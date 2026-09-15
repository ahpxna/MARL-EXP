#!/usr/bin/env python3
"""Freeze the source and the full resolved config BEFORE a run, then launch it.

Fixes two provenance defects that `write_artifact_with_provenance` cannot fix on
its own, WITHOUT editing it (append-only: this is a new file, nothing is changed):

  1. SOURCE HASH TIMING.  `write_artifact_with_provenance` calls
     `source_fingerprint()` after `run()` returns, so the recorded hash is the
     tree as it stood when the RESULT was written, not when the code was LOADED.
     If the tree is edited while a multi-hour job runs, the artifact's
     `source_sha` does not identify the code that executed.  This script takes
     the fingerprint before launch, takes it again after, and records both.
     `source_changed_during_run` is the answer the artifact cannot give.

  2. COMPARATOR SET INVISIBLE TO `protocol_sha`.  The `protocol` dict the
     functional labs hash carries no `seeds`, no `instances`, and no variant
     tuples.  Demonstrated collision, on this repo's own numbers: the shipped
     artifact `functional_v4_ieee10seed_cellv1.json.manifest.json` records
     `protocol_sha = 8864e801adacd274486c7751e5f826f3cc67f6e7dd569ee3dd7557a2869bab1d`,
     and re-running the identical CLI today - with `C_lucb` now present in
     `DEPLOYABLE` - reproduces that same hash.  A 5-comparator panel and a
     6-comparator panel are therefore indistinguishable by provenance.  This
     script imports the runner module and records `DEPLOYABLE`/`DIAGNOSTIC`
     as they actually are at launch, hashed into `freeze_sha`.

WHAT THIS DOES NOT DO.  It does not make a run confirmatory.  A freeze record
written at launch proves the code was not edited during the run; it does not
prove the protocol was registered before the outcome was known.  That requires
the freeze file to exist, committed, BEFORE the run - which is a workflow fact
about when this script was invoked, not something any script can certify about
itself.  `admissibility_record` still labels on seeds alone; this file records
the evidence that label needs, it does not change the label.

Usage (the runner and its args are passed through verbatim):

  python3 scripts/run_freeze_and_launch_v1.py \
      --freeze-out research/<dir>/<name>.freeze.json \
      --runner scripts/run_functional_variance_stopping_lab_v4.py \
      -- --instances 100 --seeds 701 ... --out research/<dir>/<name>.json
"""
from __future__ import annotations

import argparse
import datetime as _dt
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from research_chains.provenance import (  # noqa: E402
    atomic_json, canonical_json_sha256, file_sha256, source_fingerprint,
)
sys.path.insert(0, str(Path(__file__).resolve().parent))
from code_fingerprint_v1 import code_fingerprint  # noqa: E402


def _load_module(path: Path):
    spec = importlib.util.spec_from_file_location("_frozen_runner", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load runner module: {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _runner_surface(path: Path) -> dict:
    """Everything about the runner that changes what is being compared."""
    try:
        rel = str(path.relative_to(ROOT))
    except ValueError:
        rel = str(path)
    surface = {"runner_file": rel, "runner_sha": file_sha256(path)}
    try:
        mod = _load_module(path)
    except Exception as exc:  # a runner that will not import is a launch failure
        surface["module_import_error"] = f"{type(exc).__name__}: {exc}"
        return surface
    for name in ("PROTOCOL_VERSION", "DEPLOYABLE", "DIAGNOSTIC", "VARIANTS",
                 "FROZEN_CONFIRMATORY_SEEDS"):
        if hasattr(mod, name):
            value = getattr(mod, name)
            surface[name] = list(value) if isinstance(value, tuple) else value
    return surface


def main(argv=None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--runner", required=True, help="path to the experiment script")
    p.add_argument("--freeze-out", required=True, help="where to write the freeze record")
    p.add_argument("--label", default="", help="free-text label for this launch")
    p.add_argument("--dry-run", action="store_true",
                   help="write the freeze record and print the command; do not launch")
    p.add_argument("runner_args", nargs=argparse.REMAINDER,
                   help="everything after -- is passed to the runner verbatim")
    a = p.parse_args(argv)

    runner = (ROOT / a.runner).resolve() if not Path(a.runner).is_absolute() else Path(a.runner)
    if not runner.is_file():
        raise SystemExit(f"runner not found: {runner}")
    passthrough = [x for x in a.runner_args if x != "--"]

    started = _dt.datetime.now(_dt.timezone.utc).isoformat()
    source_at_launch = source_fingerprint(ROOT)
    # source_fingerprint hashes untracked files, so a run's own output changes
    # it and `source_changed_during_run` is True for every run that writes an
    # artifact. That field distinguishes nothing. code_fingerprint hashes only
    # the importable Python and the dependency pins, so it answers the question
    # the freeze record is actually for.
    code_at_launch = code_fingerprint(ROOT)
    surface = _runner_surface(runner)

    freeze = {
        "freeze_version": "freeze_and_launch_v1",
        "label": a.label,
        "started_utc": started,
        "source_sha_at_launch": source_at_launch,
        "source_sha_note": ("includes untracked files, so it moves when the run "
                            "writes its own output; not a code-change signal"),
        "code_sha_at_launch": code_at_launch["code_sha"],
        "code_files_hashed": code_at_launch["file_count"],
        "runner_surface": surface,
        "argv": passthrough,
        "python": sys.version.split()[0],
        "cwd": str(ROOT),
    }
    freeze["freeze_sha"] = canonical_json_sha256(freeze)

    freeze_path = (ROOT / a.freeze_out) if not Path(a.freeze_out).is_absolute() else Path(a.freeze_out)
    atomic_json(freeze_path, freeze)
    print(f"[freeze] {freeze_path}")
    print(f"[freeze] source_sha_at_launch = {source_at_launch}")
    print(f"[freeze] freeze_sha           = {freeze['freeze_sha']}")
    for k in ("PROTOCOL_VERSION", "DEPLOYABLE", "DIAGNOSTIC"):
        if k in surface:
            print(f"[freeze] {k:17s} = {surface[k]}")

    cmd = [sys.executable, str(runner)] + passthrough
    print(f"[freeze] command: {' '.join(cmd)}")
    if a.dry_run:
        print("[freeze] --dry-run: not launching")
        return 0

    rc = subprocess.run(cmd, cwd=str(ROOT)).returncode

    finished = _dt.datetime.now(_dt.timezone.utc).isoformat()
    source_at_finish = source_fingerprint(ROOT)
    code_at_finish = code_fingerprint(ROOT)
    freeze.update({
        "finished_utc": finished,
        "source_sha_at_finish": source_at_finish,
        "source_changed_during_run": source_at_launch != source_at_finish,
        "code_sha_at_finish": code_at_finish["code_sha"],
        "code_changed_during_run":
            code_at_launch["code_sha"] != code_at_finish["code_sha"],
        "runner_sha_at_finish": file_sha256(runner),
        "runner_sha_changed_during_run": file_sha256(runner) != surface.get("runner_sha"),
        "exit_code": rc,
    })
    # the runner's own exit code, never a pipeline/tee exit code (gate G05)
    out_path = None
    if "--out" in passthrough:
        out_path = passthrough[passthrough.index("--out") + 1]
        target = (ROOT / out_path) if not Path(out_path).is_absolute() else Path(out_path)
        if target.is_file():
            try:
                freeze["artifact"] = str(target.relative_to(ROOT))
            except ValueError:          # --out written outside the repo (self-tests)
                freeze["artifact"] = str(target)
            freeze["artifact_sha"] = file_sha256(target)
            man = target.with_suffix(target.suffix + ".manifest.json")
            if man.is_file():
                freeze["artifact_manifest"] = json.loads(man.read_text())
    freeze["freeze_sha_final"] = canonical_json_sha256(freeze)
    atomic_json(freeze_path, freeze)

    print(f"[freeze] exit_code                 = {rc}")
    print(f"[freeze] code_changed_during_run   = {freeze['code_changed_during_run']}")
    print(f"[freeze] source_changed_during_run = {freeze['source_changed_during_run']} "
          "(includes this run's own output; not a code signal)")
    if freeze["code_changed_during_run"]:
        print("[freeze] WARNING: the importable Python changed while this job ran. The "
              "artifact's source_sha is the POST-run tree and does not identify the "
              "code that executed.")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
