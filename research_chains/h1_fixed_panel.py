"""Deterministic fixed evaluation panels for H1 functional-boundary experiments."""

from __future__ import annotations

import copy
import dataclasses
import gzip
import hashlib
import json
import os
import pickle
from pathlib import Path
from typing import Any, Mapping, Sequence

import numpy as np


PANEL_PROTOCOL_VERSION = "h1_fixed_eval_panel_v1"
_REQUIRED_STEP_FIELDS = (
    "obs_all",
    "actions",
    "rewards",
    "proxy_context_excluding",
    "proxy_context_blocks",
    "belief_summary_cache",
    "geom_snapshot",
    "behaviour_probs",
    "policy_probs",
    "h1_target_policy_probs",
    "valid_action_masks",
    "env_snapshot_before_step",
)


def _canonicalize(value: Any):
    if dataclasses.is_dataclass(value):
        return _canonicalize(dataclasses.asdict(value))
    if isinstance(value, np.ndarray):
        return {
            "__ndarray__": True,
            "dtype": str(value.dtype),
            "shape": list(value.shape),
            "data": value.tolist(),
        }
    if isinstance(value, np.generic):
        return value.item()
    if isinstance(value, Mapping):
        return {
            str(key): _canonicalize(value[key])
            for key in sorted(value, key=lambda item: str(item))
        }
    if isinstance(value, (list, tuple)):
        return [_canonicalize(item) for item in value]
    if isinstance(value, set):
        return sorted((_canonicalize(item) for item in value), key=repr)
    if isinstance(value, (str, int, float, bool)) or value is None:
        if isinstance(value, float):
            if np.isnan(value):
                return "NaN"
            if np.isposinf(value):
                return "+Inf"
            if np.isneginf(value):
                return "-Inf"
        return value
    return repr(value)


def _sha256_json(value: Any) -> str:
    payload = json.dumps(
        _canonicalize(value),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def step_fingerprint(step: Mapping[str, Any]) -> str:
    missing = [name for name in _REQUIRED_STEP_FIELDS if step.get(name) is None]
    if missing:
        raise ValueError(
            "fixed H1 panel step is missing required fields: " + ", ".join(missing)
        )
    scientific_view = {name: step[name] for name in _REQUIRED_STEP_FIELDS}
    return _sha256_json(scientific_view)


def panel_fingerprint(metadata: Mapping[str, Any], step_hashes: Sequence[str]) -> str:
    identity = {
        "protocol_version": PANEL_PROTOCOL_VERSION,
        "metadata": dict(metadata),
        "step_hashes": list(step_hashes),
    }
    return _sha256_json(identity)


def _file_sha256(path: os.PathLike[str] | str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def save_fixed_panel(
    path: os.PathLike[str] | str,
    steps: Sequence[Mapping[str, Any]],
    metadata: Mapping[str, Any],
):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    stored_steps = []
    step_hashes = []
    for index, raw_step in enumerate(steps):
        step = copy.deepcopy(dict(raw_step))
        fingerprint = step_fingerprint(step)
        step["_fixed_panel_step_index"] = int(index)
        step["_fixed_panel_step_hash"] = fingerprint
        stored_steps.append(step)
        step_hashes.append(fingerprint)

    clean_metadata = dict(metadata)
    clean_metadata.update({
        "protocol_version": PANEL_PROTOCOL_VERSION,
        "n_steps": int(len(stored_steps)),
    })
    fingerprint = panel_fingerprint(clean_metadata, step_hashes)
    for step in stored_steps:
        step["_fixed_panel_fingerprint"] = fingerprint
        step["_fixed_panel_protocol"] = PANEL_PROTOCOL_VERSION

    payload = {
        "protocol_version": PANEL_PROTOCOL_VERSION,
        "metadata": clean_metadata,
        "step_hashes": step_hashes,
        "panel_fingerprint": fingerprint,
        "steps": stored_steps,
    }

    tmp_path = path.with_name(path.name + ".tmp")
    with open(tmp_path, "wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as zipped:
            pickle.dump(payload, zipped, protocol=pickle.HIGHEST_PROTOCOL)
    os.replace(tmp_path, path)

    sidecar = {
        "protocol_version": PANEL_PROTOCOL_VERSION,
        "panel_fingerprint": fingerprint,
        "file_sha256": _file_sha256(path),
        "step_hashes": step_hashes,
        "metadata": clean_metadata,
    }
    sidecar_path = path.with_suffix(path.suffix + ".json")
    sidecar_path.write_text(json.dumps(sidecar, indent=2, sort_keys=True), encoding="utf-8")
    return sidecar


def load_fixed_panel(path: os.PathLike[str] | str):
    path = Path(path)
    with gzip.open(path, "rb") as handle:
        payload = pickle.load(handle)
    if payload.get("protocol_version") != PANEL_PROTOCOL_VERSION:
        raise ValueError("fixed H1 panel protocol version mismatch")
    steps = payload.get("steps")
    if not isinstance(steps, list) or not steps:
        raise ValueError("fixed H1 panel contains no evaluation steps")
    metadata = payload.get("metadata")
    if not isinstance(metadata, dict):
        raise ValueError("fixed H1 panel metadata is missing")

    actual_hashes = []
    for index, step in enumerate(steps):
        actual = step_fingerprint(step)
        stored = str(step.get("_fixed_panel_step_hash", ""))
        if actual != stored:
            raise ValueError(f"fixed H1 panel step hash mismatch at index {index}")
        actual_hashes.append(actual)
    if actual_hashes != list(payload.get("step_hashes", [])):
        raise ValueError("fixed H1 panel step-hash ledger mismatch")
    expected_fingerprint = panel_fingerprint(metadata, actual_hashes)
    if expected_fingerprint != payload.get("panel_fingerprint"):
        raise ValueError("fixed H1 panel fingerprint mismatch")

    sidecar_path = path.with_suffix(path.suffix + ".json")
    if sidecar_path.exists():
        sidecar = json.loads(sidecar_path.read_text(encoding="utf-8"))
        if sidecar.get("panel_fingerprint") != expected_fingerprint:
            raise ValueError("fixed H1 panel sidecar fingerprint mismatch")
        if sidecar.get("file_sha256") != _file_sha256(path):
            raise ValueError("fixed H1 panel file hash mismatch")

    return {
        "protocol_version": PANEL_PROTOCOL_VERSION,
        "metadata": metadata,
        "panel_fingerprint": expected_fingerprint,
        "step_hashes": actual_hashes,
        "steps": copy.deepcopy(steps),
    }
