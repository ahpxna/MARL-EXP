#!/usr/bin/env python3
"""A fingerprint that answers "did the EXECUTED CODE change", and a verifier
for freeze records written before this existed.

WHY THIS FILE EXISTS

`research_chains.provenance.source_fingerprint` hashes `git diff HEAD` plus the
contents of every untracked file. Research outputs are untracked, so the run's
own result JSON is inside its own fingerprint. Demonstrated on this repo:

    >>> a = source_fingerprint(root)
    >>> (root/"research/confirm_ieee_20260912/_probe.tmp").write_text("x")
    >>> b = source_fingerprint(root)
    >>> a == b
    False

Consequence: `run_freeze_and_launch_v1.py` recorded
`source_changed_during_run = source_sha_at_launch != source_sha_at_finish`,
which is therefore True for EVERY run that writes an artifact, whether or not a
single line of code moved. It is a constant dressed as a check - the same defect
class as the hard-coded `development_only=True` and the hard-coded
`evidence_class` this corpus already caught.

It also means the freeze record for the F02 dev run CANNOT be read as evidence
that the four Lean files edited during that window were the cause. That
attribution was unsupported and is retracted here.

WHAT THIS COMPUTES INSTEAD

`code_fingerprint(root)` hashes only files that can change what a Python run
does: `*.py` reachable for import, plus the declared dependency/config files.
Outputs, caches, virtualenvs, vendored third-party trees and the Lean corpus are
excluded, because none of them is loaded by a lab runner.

It is deliberately NOT a general provenance primitive. It answers one question:
between two instants, did the Python that this process could import change?
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path

# Directories whose contents never affect what a lab runner executes.
EXCLUDED_PARTS = frozenset({
    ".git", ".venv", "venv", "site-packages", "__pycache__", ".lake",
    "external_envs", "envs/external", "node_modules", ".pytest_cache",
    ".mypy_cache", ".ruff_cache", "graphify-out",
    # Outputs. These are what contaminated source_fingerprint.
    "research", "results", "outputs", "compile_logs", "work",
})

# Files outside the .py set that genuinely pin behaviour.
CONFIG_NAMES = frozenset({
    "pyproject.toml", "requirements.txt", "requirements-dev.txt",
    "setup.cfg", "setup.py", "uv.lock", "poetry.lock", "Pipfile.lock",
})


def _relevant_files(root: Path):
    """Walk with in-place pruning.

    `rglob("*")` then filtering is not viable here: this repository is 12 GB and
    252,267 files, almost all of it `lake` build output and a vendored venv, so
    the walk must never descend into an excluded directory in the first place.
    """
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDED_PARTS)
        here = Path(dirpath)
        for name in sorted(filenames):
            if name.endswith(".py") or name in CONFIG_NAMES:
                path = here / name
                out.append((path.relative_to(root), path))
    out.sort(key=lambda t: t[0].as_posix())
    return out


def code_fingerprint(root: Path | str | None = None) -> dict:
    """Digest of the importable Python plus dependency pins.

    Returns the digest AND the file count, because a digest alone cannot
    distinguish "nothing changed" from "the walk found nothing".
    """
    root = Path(root or Path(__file__).resolve().parents[1]).resolve()
    digest = hashlib.sha256()
    count = 0
    for rel, path in _relevant_files(root):
        digest.update(rel.as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
        count += 1
    if count == 0:
        raise RuntimeError(f"no Python or config files found under {root}")
    return {"code_sha": f"CODE:{digest.hexdigest()}", "file_count": count,
            "root": str(root)}


def main(argv=None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--root", default=None)
    p.add_argument("--against-freeze", default=None,
                   help="a freeze record; re-reads its source_changed_during_run "
                        "claim and reports what can and cannot be concluded")
    a = p.parse_args(argv)
    fp = code_fingerprint(a.root)
    print(json.dumps(fp, indent=2))
    if a.against_freeze:
        rec = json.loads(Path(a.against_freeze).read_text())
        print()
        print(f"freeze record       : {a.against_freeze}")
        print(f"  source_changed_during_run = {rec.get('source_changed_during_run')}")
        print(f"  runner_sha_changed        = {rec.get('runner_sha_changed_during_run')}")
        print(f"  code_changed_during_run   = {rec.get('code_changed_during_run', '(not recorded)')}")
        if "code_changed_during_run" not in rec:
            print()
            print("  This record predates code_fingerprint. Its "
                  "source_changed_during_run flag includes the run's own")
            print("  untracked output, so True there is uninformative. The only "
                  "code claim it supports is the runner hash,")
            print("  which covers ONE file and not its imports.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
