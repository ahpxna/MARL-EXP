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


def source_fingerprint(root: Path | None = None) -> str:
    """HEAD plus dirty-tree digest, so an edited tree is never called plain HEAD."""
    root = Path(root or Path(__file__).resolve().parents[1])
    try:
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, check=True,
                              capture_output=True, text=True).stdout.strip()
        diff = subprocess.run(["git", "diff", "--binary", "HEAD"], cwd=root, check=True,
                              capture_output=True).stdout.encode()
        untracked = subprocess.run(["git", "ls-files", "--others", "--exclude-standard"], cwd=root,
                                   check=True, capture_output=True, text=True).stdout.splitlines()
        digest = hashlib.sha256(diff)
        for name in sorted(untracked):
            path = root / name; digest.update(name.encode())
            if path.is_file(): digest.update(path.read_bytes())
        dirty_sha = digest.hexdigest()
        return head if not diff and not untracked else f"{head}+dirty:{dirty_sha}"
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
