"""Long-format measurement schema for the CIG-AMF observatory.

One JSONL row == one *quantity* of one *equation* of one *chain* on one
*instance*.  Nothing is aggregated at write time.  Aggregation, pivoting and
pattern mining all happen later over the same immutable store, so a question
nobody thought of on the day of the run can still be asked afterwards.

Design rules that follow from the portfolio's own protocol:

* every row records the arithmetic mode it was produced under, so a
  floating-point row can never be mistaken for an exact falsification;
* every row carries the full instance key, so any subset can be re-derived;
* equations are declared once in ``EQUATIONS`` with their symbol list, and the
  emitter refuses unknown (equation, symbol) pairs -- a typo becomes an error
  rather than a silently orphaned column;
* ``status`` separates "measured" from "skipped/blocked/undefined" so absence
  of a number is itself data.
"""
from __future__ import annotations

import json
import os
import platform
import subprocess
import sys
import time
import uuid
from dataclasses import dataclass, field, asdict
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Sequence

SCHEMA_VERSION = "observatory_long_v1"

# ---------------------------------------------------------------- arithmetic

MODE_EXACT = "exact"
MODE_FLOAT = "float"

# ------------------------------------------------------------------- status

ST_OK = "measured"
ST_UNDEFINED = "undefined"      # quantity has no value here (e.g. 0/0 gap)
ST_SKIPPED = "skipped"          # not computed (cost, missing optional dep)
ST_BLOCKED = "blocked"          # capability absent -> fail closed, never proxied
ST_ERROR = "error"

VALID_STATUS = (ST_OK, ST_UNDEFINED, ST_SKIPPED, ST_BLOCKED, ST_ERROR)

# ------------------------------------------------------------------- roles

ROLE_INPUT = "input"        # something the generator chose
ROLE_TERM = "term"          # an intermediate term of the equation
ROLE_LHS = "lhs"
ROLE_RHS = "rhs"
ROLE_SLACK = "slack"        # rhs - lhs for an inequality
ROLE_RATIO = "ratio"        # lhs / rhs
ROLE_FLAG = "flag"          # 0/1 predicate
ROLE_DIAG = "diag"          # diagnostic, not part of the equation proper

VALID_ROLES = (ROLE_INPUT, ROLE_TERM, ROLE_LHS, ROLE_RHS, ROLE_SLACK,
               ROLE_RATIO, ROLE_FLAG, ROLE_DIAG)


@dataclass(frozen=True)
class Equation:
    """A declared equation or inequality whose every term gets recorded."""
    eq_id: str
    chain: str
    statement: str            # human-readable, ASCII-safe
    symbols: tuple            # every symbol this equation may emit
    kind: str = "inequality"  # inequality | identity | definition | predicate
    status_note: str = ""     # PROVED / OPEN / KILLED / DEMOTED as of the ledger

    def has(self, symbol: str) -> bool:
        return symbol in self.symbols


# --------------------------------------------------------------- registry

_REGISTRY: Dict[str, Equation] = {}


def declare(eq: Equation) -> Equation:
    if eq.eq_id in _REGISTRY:
        raise ValueError("duplicate equation id: " + eq.eq_id)
    _REGISTRY[eq.eq_id] = eq
    return eq


def registry() -> Mapping[str, Equation]:
    return dict(_REGISTRY)


def equation(eq_id: str) -> Equation:
    try:
        return _REGISTRY[eq_id]
    except KeyError:
        raise KeyError(
            "undeclared equation '%s'; declare it in observatory.equations "
            "before emitting rows for it" % eq_id
        )


# ------------------------------------------------------------ value coding

def _exact_str(value: Any) -> str | None:
    """Lossless textual form for exact values; ``None`` when not exact."""
    if isinstance(value, Fraction):
        return "%d/%d" % (value.numerator, value.denominator)
    if isinstance(value, int) and not isinstance(value, bool):
        return "%d/1" % value
    return None


def _float_of(value: Any) -> float | None:
    if value is None:
        return None
    if isinstance(value, bool):
        return 1.0 if value else 0.0
    if isinstance(value, Fraction):
        try:
            return float(value)
        except (OverflowError, ZeroDivisionError):
            return None
    try:
        out = float(value)
    except (TypeError, ValueError):
        return None
    if out != out or out in (float("inf"), float("-inf")):
        # NaN / +-inf are legitimate outcomes (undefined gap, infinite ratio);
        # they are preserved as JSON strings by the encoder below.
        return out
    return out


class _Enc(json.JSONEncoder):
    def default(self, o):  # pragma: no cover - defensive
        if isinstance(o, Fraction):
            return "%d/%d" % (o.numerator, o.denominator)
        if isinstance(o, (set, frozenset, tuple)):
            return list(o)
        try:
            import numpy as _np
            if isinstance(o, _np.integer):
                return int(o)
            if isinstance(o, _np.floating):
                return float(o)
            if isinstance(o, _np.ndarray):
                return o.tolist()
            if isinstance(o, _np.bool_):
                return bool(o)
        except Exception:
            pass
        return str(o)


def _json_safe_float(x: float | None):
    if x is None:
        return None
    if x != x:
        return "NaN"
    if x == float("inf"):
        return "Infinity"
    if x == float("-inf"):
        return "-Infinity"
    return x


# ---------------------------------------------------------------- emitter

def _git_rev(root: Path) -> str:
    try:
        out = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, timeout=10,
        )
        if out.returncode == 0:
            return out.stdout.strip()
    except Exception:
        pass
    return "no-git"


@dataclass
class RunContext:
    """Provenance stamped on every row of a run."""
    run_id: str = field(default_factory=lambda: uuid.uuid4().hex[:12])
    started_at: float = field(default_factory=time.time)
    profile: str = "adhoc"
    seed: int = 0
    schema_version: str = SCHEMA_VERSION
    python: str = field(default_factory=lambda: sys.version.split()[0])
    platform: str = field(default_factory=lambda: platform.platform())
    git_rev: str = ""
    notes: str = ""

    def payload(self) -> Dict[str, Any]:
        return asdict(self)


class Emitter:
    """Append-only long-format writer.

    ``emit`` is deliberately verbose at the call site: the caller must name the
    equation and the symbol.  That is what makes it possible to later ask
    "show me every recorded term of every inequality that mentions delta_square"
    without having guessed the question in advance.
    """

    def __init__(self, path, ctx: RunContext, *, autoflush: int = 2000):
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.ctx = ctx
        self._buf: list = []
        self._autoflush = int(autoflush)
        self.n_rows = 0
        self._counts: Dict[str, int] = {}
        header = {
            "record": "run_header",
            "schema_version": SCHEMA_VERSION,
            **ctx.payload(),
        }
        with self.path.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(header, cls=_Enc) + "\n")

    # -- core ------------------------------------------------------------
    def emit(
        self,
        *,
        chain: str,
        eq_id: str,
        symbol: str,
        value: Any = None,
        role: str = ROLE_TERM,
        mode: str = MODE_EXACT,
        status: str = ST_OK,
        instance: Mapping[str, Any] | None = None,
        tags: Sequence[str] = (),
        note: str = "",
    ) -> None:
        eq = equation(eq_id)
        if eq.chain != chain:
            raise ValueError(
                "equation %s belongs to chain %s, not %s" % (eq_id, eq.chain, chain)
            )
        if not eq.has(symbol):
            raise ValueError(
                "symbol '%s' is not declared for equation %s (declared: %s)"
                % (symbol, eq_id, ", ".join(eq.symbols))
            )
        if role not in VALID_ROLES:
            raise ValueError("bad role: " + str(role))
        if status not in VALID_STATUS:
            raise ValueError("bad status: " + str(status))
        if mode not in (MODE_EXACT, MODE_FLOAT):
            raise ValueError("bad mode: " + str(mode))

        exact = _exact_str(value) if mode == MODE_EXACT else None
        if mode == MODE_EXACT and exact is None and status == ST_OK and value is not None:
            # An "exact" row that is not actually a rational is a bug we want to
            # hear about immediately, because the whole falsification protocol
            # rests on that distinction.
            if isinstance(value, bool):
                exact = "1/1" if value else "0/1"
            else:
                raise TypeError(
                    "exact mode requires Fraction/int for %s.%s, got %r"
                    % (eq_id, symbol, type(value).__name__)
                )

        row = {
            "record": "q",
            "run_id": self.ctx.run_id,
            "chain": chain,
            "eq_id": eq_id,
            "symbol": symbol,
            "role": role,
            "mode": mode,
            "status": status,
            "value": _json_safe_float(_float_of(value)),
            "exact": exact,
            "instance": dict(instance or {}),
            "tags": list(tags),
            "note": note,
        }
        self._buf.append(row)
        self.n_rows += 1
        key = chain + "|" + eq_id
        self._counts[key] = self._counts.get(key, 0) + 1
        if len(self._buf) >= self._autoflush:
            self.flush()

    # -- convenience -----------------------------------------------------
    def emit_many(self, rows: Iterable[Mapping[str, Any]]) -> None:
        for r in rows:
            self.emit(**r)

    def emit_inequality(
        self,
        *,
        chain: str,
        eq_id: str,
        lhs: Any,
        rhs: Any,
        lhs_symbol: str,
        rhs_symbol: str,
        slack_symbol: str | None = None,
        ratio_symbol: str | None = None,
        holds_symbol: str | None = None,
        mode: str = MODE_EXACT,
        instance: Mapping[str, Any] | None = None,
        tags: Sequence[str] = (),
    ) -> bool:
        """Record both sides, the slack, the ratio and the verdict.

        The verdict is returned so a caller can branch, but the *numbers* are
        always written even when the inequality holds -- a satisfied bound with
        tiny slack is exactly the signal a sharpness search is looking for, and
        it is invisible if only violations are logged.
        """
        self.emit(chain=chain, eq_id=eq_id, symbol=lhs_symbol, value=lhs,
                  role=ROLE_LHS, mode=mode, instance=instance, tags=tags)
        self.emit(chain=chain, eq_id=eq_id, symbol=rhs_symbol, value=rhs,
                  role=ROLE_RHS, mode=mode, instance=instance, tags=tags)
        holds = bool(lhs <= rhs)
        if slack_symbol is not None:
            self.emit(chain=chain, eq_id=eq_id, symbol=slack_symbol,
                      value=(rhs - lhs), role=ROLE_SLACK, mode=mode,
                      instance=instance, tags=tags)
        if ratio_symbol is not None:
            if rhs == 0:
                self.emit(chain=chain, eq_id=eq_id, symbol=ratio_symbol,
                          value=None, role=ROLE_RATIO, mode=mode,
                          status=ST_UNDEFINED, instance=instance, tags=tags,
                          note="rhs is zero")
            else:
                self.emit(chain=chain, eq_id=eq_id, symbol=ratio_symbol,
                          value=(lhs / rhs), role=ROLE_RATIO, mode=mode,
                          instance=instance, tags=tags)
        if holds_symbol is not None:
            self.emit(chain=chain, eq_id=eq_id, symbol=holds_symbol,
                      value=(1 if holds else 0), role=ROLE_FLAG, mode=mode,
                      instance=instance, tags=tags)
        return holds

    # -- lifecycle -------------------------------------------------------
    def flush(self) -> None:
        if not self._buf:
            return
        with self.path.open("a", encoding="utf-8") as fh:
            for row in self._buf:
                fh.write(json.dumps(row, cls=_Enc) + "\n")
        self._buf = []

    def close(self, extra: Mapping[str, Any] | None = None) -> None:
        self.flush()
        footer = {
            "record": "run_footer",
            "run_id": self.ctx.run_id,
            "n_rows": self.n_rows,
            "finished_at": time.time(),
            "elapsed_s": time.time() - self.ctx.started_at,
            "rows_by_equation": dict(sorted(self._counts.items())),
        }
        if extra:
            footer.update(dict(extra))
        with self.path.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(footer, cls=_Enc) + "\n")

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close({"exception": None if exc is None else repr(exc)})
        return False


def make_context(profile: str, seed: int, root: Path | None = None, notes: str = "") -> RunContext:
    root = Path(root or Path(__file__).resolve().parents[1])
    return RunContext(profile=profile, seed=int(seed), git_rev=_git_rev(root), notes=notes)
