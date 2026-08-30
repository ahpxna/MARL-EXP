"""Fail-closed immutable-ish manifest helpers for new-chain development runs."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import tempfile
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
