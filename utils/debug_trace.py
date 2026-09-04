"""Structured debugging helpers for research runs.

The project historically writes final JSON artifacts with provenance.  This
module is deliberately lower-level: it records *how* a run got there.  The
JSONL trace is safe to keep for failed runs because every event is flushed
immediately and exception events include a traceback.
"""
from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import resource
import sys
import time
import traceback
from typing import Any, Iterator


def _jsonable(value: Any) -> Any:
    if value is None or isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, dict):
        return {str(k): _jsonable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [_jsonable(v) for v in value]
    try:
        import numpy as np
        if isinstance(value, np.generic):
            return value.item()
        if isinstance(value, np.ndarray):
            return value.tolist()
    except Exception:
        pass
    return repr(value)


def _rss_mb() -> float:
    # Linux reports KiB, macOS bytes.  The CI/research hosts used by this repo
    # are Linux, but keep a conservative platform check for local debugging.
    raw = float(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    if sys.platform == "darwin":
        return raw / (1024.0 * 1024.0)
    return raw / 1024.0


@dataclass
class DebugTrace:
    path: Path | None = None
    enabled: bool = False
    run_id: str = "run"

    def __post_init__(self) -> None:
        if self.enabled and self.path is None:
            raise ValueError("enabled DebugTrace requires a path")
        if self.path is not None:
            self.path = Path(self.path)
            self.path.parent.mkdir(parents=True, exist_ok=True)

    def event(self, name: str, **payload: Any) -> None:
        if not self.enabled:
            return
        row = {
            "ts_utc": datetime.now(timezone.utc).isoformat(),
            "run_id": self.run_id,
            "event": str(name),
            "rss_mb": _rss_mb(),
            **{str(k): _jsonable(v) for k, v in payload.items()},
        }
        with self.path.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(row, sort_keys=True, allow_nan=False) + "\n")
            handle.flush()
            os.fsync(handle.fileno())

    @contextmanager
    def timed(self, name: str, **payload: Any) -> Iterator[None]:
        start = time.perf_counter()
        self.event(f"{name}.start", **payload)
        try:
            yield
        except Exception as exc:
            self.event(
                f"{name}.error",
                elapsed_s=time.perf_counter() - start,
                error_type=type(exc).__name__,
                error=str(exc),
                traceback=traceback.format_exc(),
                **payload,
            )
            raise
        else:
            self.event(f"{name}.end", elapsed_s=time.perf_counter() - start, **payload)


def null_trace() -> DebugTrace:
    return DebugTrace(enabled=False)
