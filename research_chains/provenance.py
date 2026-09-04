"""Fail-closed immutable-ish manifest helpers for new-chain development runs."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import tempfile
import subprocess
from typing import Mapping


def canonical_json_sha256(payload: Mapping) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(raw).hexdigest()


def file_sha256(path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def atomic_json(path, payload) -> None:
    path = Path(path); path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, sort_keys=True, indent=2, allow_nan=False) + "\n"
    fd, tmp = tempfile.mkstemp(prefix=f".{path.name}.", dir=str(path.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(encoded); handle.flush(); os.fsync(handle.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp): os.unlink(tmp)


def _source_tree_fingerprint(root: Path) -> str:
    """Deterministic fallback for source archives that are not Git checkouts.

    Generated research outputs, caches, compiled objects and large binary artifacts
    are deliberately excluded: the fingerprint should identify the source/config tree,
    not depend on the result file that is being written.
    """
    excluded_parts = {
        ".git", "__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache",
        "research", "results", "outputs", "compile_logs", "wandb",
    }
    source_suffixes = {
        ".py", ".md", ".txt", ".toml", ".yaml", ".yml", ".json", ".sh", ".bat",
        ".lean", ".csv", ".tsv", ".ini", ".cfg", ".lock",
    }
    digest = hashlib.sha256()
    count = 0
    for path in sorted(root.rglob("*"), key=lambda p: p.as_posix()):
        if not path.is_file():
            continue
        rel = path.relative_to(root)
        if any(part in excluded_parts for part in rel.parts):
            continue
        if path.suffix.lower() not in source_suffixes and path.name not in {"Dockerfile", "Makefile"}:
            continue
        digest.update(rel.as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
        count += 1
    if count == 0:
        raise RuntimeError("no source files found for fallback fingerprint")
    return f"TREE:{digest.hexdigest()}:{count}"


def source_fingerprint(root: Path | None = None) -> str:
    """HEAD plus dirty digest, with a deterministic source-tree fallback.

    Research artifacts are often exchanged as ZIPs without `.git`; provenance must
    remain usable in that normal workflow instead of emitting `UNAVAILABLE:*`.
    """
    root = Path(root or Path(__file__).resolve().parents[1])
    try:
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, check=True,
                              capture_output=True, text=True).stdout.strip()
        diff = subprocess.run(["git", "diff", "--binary", "HEAD"], cwd=root, check=True,
                              capture_output=True).stdout
        untracked = subprocess.run(["git", "ls-files", "--others", "--exclude-standard"], cwd=root,
                                   check=True, capture_output=True, text=True).stdout.splitlines()
        digest = hashlib.sha256(diff)
        for name in sorted(untracked):
            path = root / name
            digest.update(name.encode("utf-8"))
            if path.is_file():
                digest.update(path.read_bytes())
        dirty_sha = digest.hexdigest()
        return head if not diff and not untracked else f"{head}+dirty:{dirty_sha}"
    except (subprocess.SubprocessError, OSError):
        try:
            return _source_tree_fingerprint(root)
        except Exception as exc:
            return f"UNAVAILABLE:{type(exc).__name__}"


def write_artifact_with_provenance(path, payload, *, protocol, seed=None,
                                   evidence_class="DEVELOPMENT_EMPIRICAL", chain="UNSPECIFIED"):
    """Write result plus a non-recursive hash sidecar."""
    path = Path(path); atomic_json(path, payload)
    manifest = {
        "manifest_version": "claim_evidence_run_v1", "chain": str(chain),
        "seed": None if seed is None else int(seed), "evidence_class": str(evidence_class),
        "source_sha": source_fingerprint(), "protocol_sha": canonical_json_sha256(dict(protocol)),
        "artifact": path.name, "artifact_sha": file_sha256(path),
    }
    manifest["manifest_sha"] = canonical_json_sha256(manifest)
    atomic_json(path.with_suffix(path.suffix + ".manifest.json"), manifest)
    return manifest


def build_manifest(*, protocol_version: str, chain: str, development_only: bool, seed: int | None, source_sha: str, config: Mapping, estimand_key: str, reference_semantics: str, support_version: str, continuation_version: str, metric_availability: Mapping[str, str]):
    if not development_only:
        raise ValueError("new-chain harness is development-only until protocols are frozen")
    config_sha = canonical_json_sha256(dict(config))
    payload = {
        "protocol_version": str(protocol_version),
        "chain": str(chain),
        "development_only": True,
        "seed": None if seed is None else int(seed),
        "source_sha": str(source_sha),
        "config_sha": config_sha,
        "estimand_key": str(estimand_key),
        "reference_semantics": str(reference_semantics),
        "support_version": str(support_version),
        "continuation_version": str(continuation_version),
        "metric_availability": dict(metric_availability),
    }
    payload["manifest_fingerprint"] = canonical_json_sha256(payload)
    return payload
