"""Finite binary active-cell LP discovery for the D6 balanced branch.

This module mirrors the *semantics* of the Lean active-cell programme but is a
numerical discovery tool, not a proof.  It fixes a binary product-reference
active cell, maximises the doubled decision gap, and records an exact LP dual
certificate over:

* binary mixed-difference rectangle constraints ``|Delta_i(x)-Delta_i(y)|<=1``;
* active residual max/min inequalities;
* response max/min inequalities;
* Top-C inequalities for the frozen selected set.

For m binary coordinates, the mixed-difference unit ball can be written with
one pair of inequalities for every pair of complement contexts.  This gives a
finite sparse LP with free F-values and, importantly, direct dual multipliers
on actual rectangle/cycle inequalities.

The implementation is intended to discover/kill the conjectural pattern
Gamma(C)=m-1 on balanced cells for m=4,6,8 before expensive Lean work.
"""
from __future__ import annotations

from dataclasses import dataclass, asdict
from functools import lru_cache
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import time
from typing import Iterable, Sequence

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

from utils.debug_trace import DebugTrace, null_trace


Array = np.ndarray
World = tuple[int, ...]


def _canonical_hash(payload: dict) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()[:20]


@dataclass(frozen=True)
class BinaryProductReference:
    probs: tuple[tuple[float, float], ...]
    key: str = "uniform"

    def __post_init__(self) -> None:
        clean = []
        for row in self.probs:
            if len(row) != 2:
                raise ValueError("binary product reference requires two probabilities per coordinate")
            row = tuple(float(x) for x in row)
            if min(row) < -1e-15 or not all(math.isfinite(x) for x in row):
                raise ValueError("reference probabilities must be finite and non-negative")
            if not math.isclose(sum(row), 1.0, rel_tol=0.0, abs_tol=1e-12):
                raise ValueError("each discovery reference row must sum to one")
            clean.append(row)
        object.__setattr__(self, "probs", tuple(clean))
        if not clean:
            raise ValueError("reference requires at least one coordinate")

    @property
    def m(self) -> int:
        return len(self.probs)

    @property
    def worlds(self) -> tuple[World, ...]:
        return tuple(itertools.product((0, 1), repeat=self.m))

    @property
    def n_worlds(self) -> int:
        return 1 << self.m

    def index(self, world: Sequence[int]) -> int:
        # itertools.product((0,1), repeat=m) is binary-count lexicographic.
        idx = 0
        for bit in world:
            idx = (idx << 1) | int(bit)
        return idx

    def joint_weight(self, world: Sequence[int]) -> float:
        out = 1.0
        for i, bit in enumerate(world):
            out *= self.probs[i][int(bit)]
        return float(out)

    @lru_cache(maxsize=None)
    def response_coeff(self, i: int, u: int) -> tuple[float, ...]:
        i, u = int(i), int(u)
        coeff = np.zeros(self.n_worlds, dtype=np.float64)
        for c in self.worlds:
            w = self.joint_weight(c)
            target = list(c)
            target[i] = u
            coeff[self.index(target)] += w
        return tuple(float(x) for x in coeff)

    def response_matrix(self) -> Array:
        out = np.empty((self.m, 2, self.n_worlds), dtype=np.float64)
        for i in range(self.m):
            for u in (0, 1):
                out[i, u] = np.asarray(self.response_coeff(i, u), dtype=np.float64)
        return out


def make_reference(
    m: int,
    mode: str,
    rng: np.random.Generator | None = None,
    *,
    random_denominator: int = 100,
) -> BinaryProductReference:
    m = int(m)
    mode = str(mode)
    if mode == "uniform":
        probs = ((0.5, 0.5),) * m
    elif mode == "point0":
        probs = ((1.0, 0.0),) * m
    elif mode == "point1":
        probs = ((0.0, 1.0),) * m
    elif mode == "random":
        rng = np.random.default_rng(0) if rng is None else rng
        den = int(random_denominator)
        if den < 4:
            raise ValueError("random_denominator must be at least 4")
        # Use rational grid probabilities so exact reconstruction is stable.
        # Keep every row away from 0/1 to exercise genuinely non-degenerate q.
        lo = max(1, int(math.ceil(0.08 * den)))
        hi = min(den - 1, int(math.floor(0.92 * den)))
        if lo > hi:
            raise ValueError("random_denominator is too small for the requested interior range")
        rows = []
        for _ in range(m):
            num = int(rng.integers(lo, hi + 1))
            p = num / den
            rows.append((p, 1.0 - p))
        probs = tuple(rows)
    else:
        raise ValueError(f"unknown reference mode: {mode}")
    return BinaryProductReference(tuple(probs), key=mode)


@dataclass(frozen=True)
class ActiveCell:
    m: int
    selected: tuple[int, ...]
    competitor: tuple[int, ...]
    selected_max: World
    selected_min: World
    competitor_max: World
    competitor_min: World
    response_max: tuple[int, ...]
    response_min: tuple[int, ...]
    reference_key: str
    reference_probs: tuple[tuple[float, float], ...]

    def __post_init__(self) -> None:
        if self.m % 2 != 0:
            raise ValueError("balanced discovery cell requires even m")
        if len(self.selected) != self.m // 2 or len(self.competitor) != self.m // 2:
            raise ValueError("selected/competitor must be balanced")
        if set(self.selected) & set(self.competitor):
            raise ValueError("selected and competitor must be disjoint")
        if set(self.selected) | set(self.competitor) != set(range(self.m)):
            raise ValueError("selected and competitor must be complements")
        if len(self.reference_probs) != self.m:
            raise ValueError("active cell must store the exact product-reference rows")
        for row in self.reference_probs:
            if len(row) != 2 or min(row) < -1e-15 or not math.isclose(sum(row), 1.0, rel_tol=0.0, abs_tol=1e-12):
                raise ValueError("invalid stored product-reference row")

    def payload(self) -> dict:
        row = asdict(self)
        for key in ("selected", "competitor", "selected_max", "selected_min", "competitor_max", "competitor_min", "response_max", "response_min"):
            row[key] = list(row[key])
        row["reference_probs"] = [list(r) for r in row["reference_probs"]]
        return row

    @property
    def signature(self) -> str:
        return _canonical_hash(self.payload())


def reference_from_cell(cell: ActiveCell) -> BinaryProductReference:
    """Reconstruct the exact reference frozen into an active cell."""
    return BinaryProductReference(tuple(tuple(float(x) for x in r) for r in cell.reference_probs), key=cell.reference_key)


@dataclass
class LPSolution:
    success: bool
    status: int
    message: str
    gamma: float | None
    target_m_minus_1: int
    violation: float | None
    primal_max_violation: float | None
    duality_gap: float | None
    stationarity_max_abs: float | None
    dual_cycle_mass: float | None
    active_cycles: list[dict]
    active_inequalities: list[dict]
    cell: ActiveCell
    F: Array | None = None
    solve_seconds: float | None = None
    topc_min_margin: float | None = None

    def to_json(self, *, include_F: bool = False) -> dict:
        row = {
            "success": bool(self.success),
            "status": int(self.status),
            "message": str(self.message),
            "gamma": None if self.gamma is None else float(self.gamma),
            "target_m_minus_1": int(self.target_m_minus_1),
            "violation": None if self.violation is None else float(self.violation),
            "primal_max_violation": None if self.primal_max_violation is None else float(self.primal_max_violation),
            "duality_gap": None if self.duality_gap is None else float(self.duality_gap),
            "stationarity_max_abs": None if self.stationarity_max_abs is None else float(self.stationarity_max_abs),
            "dual_cycle_mass": None if self.dual_cycle_mass is None else float(self.dual_cycle_mass),
            "solve_seconds": None if self.solve_seconds is None else float(self.solve_seconds),
            "topc_min_margin": None if self.topc_min_margin is None else float(self.topc_min_margin),
            "active_cycles": self.active_cycles,
            "active_inequalities": self.active_inequalities,
            "cell": self.cell.payload() | {"signature": self.cell.signature},
        }
        if include_F and self.F is not None:
            row["F"] = [float(x) for x in self.F]
        return row


def _argmax_first(values: Array) -> int:
    return int(np.flatnonzero(values >= np.max(values) - 1e-12)[0])


def _argmin_first(values: Array) -> int:
    return int(np.flatnonzero(values <= np.min(values) + 1e-12)[0])


def _retained_coeff(ref: BinaryProductReference, response: Array, selected: Iterable[int], z: World) -> Array:
    coeff = np.zeros(ref.n_worlds, dtype=np.float64)
    coeff[ref.index(z)] = 1.0
    for i in selected:
        coeff -= response[int(i), int(z[int(i)])]
    return coeff


def derive_active_cell(F: Sequence[float], ref: BinaryProductReference) -> ActiveCell:
    F = np.asarray(F, dtype=np.float64)
    if F.shape != (ref.n_worlds,):
        raise ValueError(f"F must have shape ({ref.n_worlds},)")
    response = ref.response_matrix()
    qvals = np.einsum("iun,n->iu", response, F)
    rmax = tuple(_argmax_first(qvals[i]) for i in range(ref.m))
    rmin = tuple(_argmin_first(qvals[i]) for i in range(ref.m))
    scores = np.asarray([qvals[i, rmax[i]] - qvals[i, rmin[i]] for i in range(ref.m)])
    # Stable deterministic top-d: larger score first, then smaller coordinate id.
    order = sorted(range(ref.m), key=lambda i: (-float(scores[i]), int(i)))
    selected = tuple(sorted(order[: ref.m // 2]))
    competitor = tuple(i for i in range(ref.m) if i not in set(selected))

    worlds = ref.worlds
    rs = np.asarray([_retained_coeff(ref, response, selected, z) @ F for z in worlds])
    rt = np.asarray([_retained_coeff(ref, response, competitor, z) @ F for z in worlds])
    return ActiveCell(
        m=ref.m,
        selected=selected,
        competitor=competitor,
        selected_max=worlds[_argmax_first(rs)],
        selected_min=worlds[_argmin_first(rs)],
        competitor_max=worlds[_argmax_first(rt)],
        competitor_min=worlds[_argmin_first(rt)],
        response_max=rmax,
        response_min=rmin,
        reference_key=ref.key,
        reference_probs=ref.probs,
    )


@lru_cache(maxsize=None)
def _binary_cycle_matrix(m: int) -> tuple[sparse.csr_matrix, Array, tuple[str, ...]]:
    """Direct rectangle constraints equivalent to UnitInteractionBound for binary U.

    For each coordinate i and two complement contexts p,q, let
      d_i(p)=F(i=1,p)-F(i=0,p).
    Unit interaction is exactly |d_i(p)-d_i(q)| <= 1.
    """
    m = int(m)
    n = 1 << m
    rows: list[int] = []
    cols: list[int] = []
    data: list[float] = []
    b: list[float] = []
    labels: list[str] = []
    row_id = 0

    def idx(world: Sequence[int]) -> int:
        out = 0
        for bit in world:
            out = (out << 1) | int(bit)
        return out

    for i in range(m):
        other = [j for j in range(m) if j != i]
        contexts = list(itertools.product((0, 1), repeat=m - 1))
        contrast_rows = []
        for ctx in contexts:
            w0 = [0] * m
            w1 = [0] * m
            for j, bit in zip(other, ctx):
                w0[j] = w1[j] = bit
            w0[i] = 0
            w1[i] = 1
            contrast_rows.append((idx(w1), idx(w0), ctx))
        for a in range(len(contrast_rows)):
            p1, p0, pctx = contrast_rows[a]
            for q in range(a + 1, len(contrast_rows)):
                q1, q0, qctx = contrast_rows[q]
                # + rectangle: (F1p-F0p)-(F1q-F0q) <= 1
                for c, v in ((p1, 1.0), (p0, -1.0), (q1, -1.0), (q0, 1.0)):
                    rows.append(row_id); cols.append(c); data.append(v)
                b.append(1.0)
                labels.append(f"cycle:i={i}:p={''.join(map(str,pctx))}:q={''.join(map(str,qctx))}:sign=+1")
                row_id += 1
                # - rectangle
                for c, v in ((p1, -1.0), (p0, 1.0), (q1, 1.0), (q0, -1.0)):
                    rows.append(row_id); cols.append(c); data.append(v)
                b.append(1.0)
                labels.append(f"cycle:i={i}:p={''.join(map(str,pctx))}:q={''.join(map(str,qctx))}:sign=-1")
                row_id += 1
    mat = sparse.coo_matrix((data, (rows, cols)), shape=(row_id, n), dtype=np.float64).tocsr()
    return mat, np.asarray(b, dtype=np.float64), tuple(labels)


def _active_cell_constraints(cell: ActiveCell, ref: BinaryProductReference, topc_margin: float = 0.0) -> tuple[sparse.csr_matrix, Array, tuple[str, ...], Array]:
    if cell.m != ref.m:
        raise ValueError("cell/reference dimension mismatch")
    response = ref.response_matrix()
    worlds = ref.worlds
    rows_dense: list[Array] = []
    b: list[float] = []
    labels: list[str] = []

    def add(row: Array, rhs: float, label: str) -> None:
        rows_dense.append(np.asarray(row, dtype=np.float64))
        b.append(float(rhs)); labels.append(str(label))

    rs = {z: _retained_coeff(ref, response, cell.selected, z) for z in worlds}
    rt = {z: _retained_coeff(ref, response, cell.competitor, z) for z in worlds}
    smax, smin = cell.selected_max, cell.selected_min
    tmax, tmin = cell.competitor_max, cell.competitor_min
    for z in worlds:
        if z != smax:
            add(rs[z] - rs[smax], 0.0, f"cell:selected_residual_max:z={''.join(map(str,z))}")
        if z != smin:
            add(rs[smin] - rs[z], 0.0, f"cell:selected_residual_min:z={''.join(map(str,z))}")
        if z != tmax:
            add(rt[z] - rt[tmax], 0.0, f"cell:competitor_residual_max:z={''.join(map(str,z))}")
        if z != tmin:
            add(rt[tmin] - rt[z], 0.0, f"cell:competitor_residual_min:z={''.join(map(str,z))}")

    span_coeff = []
    for i in range(ref.m):
        rmax = int(cell.response_max[i]); rmin = int(cell.response_min[i])
        for u in (0, 1):
            if u != rmax:
                add(response[i, u] - response[i, rmax], 0.0, f"cell:response_max:i={i}:u={u}")
            if u != rmin:
                add(response[i, rmin] - response[i, u], 0.0, f"cell:response_min:i={i}:u={u}")
        span_coeff.append(response[i, rmax] - response[i, rmin])

    for j in cell.selected:
        for l in cell.competitor:
            # C_l - C_j <= -margin.  margin=0 matches Lean's non-strict
            # IsTopKByScore; a positive margin is a debugging stress test for
            # whether violations are purely tie-driven.
            add(span_coeff[l] - span_coeff[j], -float(topc_margin), f"cell:topC:selected={j}:rejected={l}")

    objective = rs[smax] - rs[smin] - rt[tmax] + rt[tmin]
    matrix = sparse.csr_matrix(np.vstack(rows_dense)) if rows_dense else sparse.csr_matrix((0, ref.n_worlds))
    return matrix, np.asarray(b, dtype=np.float64), tuple(labels), objective


@lru_cache(maxsize=None)
def _binary_range_interaction_matrix(m: int) -> tuple[sparse.csr_matrix, Array, tuple[str, ...]]:
    """Compact extended formulation of the same binary interaction unit ball.

    Variables are [F(worlds), hi_i, lo_i].  Every coordinate contrast lies in
    [lo_i, hi_i] and hi_i-lo_i<=1.  This is dramatically faster for cell
    discovery at m=8; promising cells are re-solved with direct rectangle
    constraints to recover cycle dual coefficients.
    """
    m = int(m); n = 1 << m; total = n + 2 * m
    rows=[]; cols=[]; data=[]; b=[]; labels=[]; rid=0
    def idx(world):
        out=0
        for bit in world: out=(out<<1)|int(bit)
        return out
    for i in range(m):
        other=[j for j in range(m) if j!=i]
        hi=n+i; lo=n+m+i
        for ctx in itertools.product((0,1), repeat=m-1):
            w0=[0]*m; w1=[0]*m
            for j,bit in zip(other,ctx): w0[j]=w1[j]=bit
            w1[i]=1
            # delta(ctx) - hi_i <= 0
            for c,v in ((idx(w1),1.0),(idx(w0),-1.0),(hi,-1.0)):
                rows.append(rid); cols.append(c); data.append(v)
            b.append(0.0); labels.append(f"range:upper:i={i}:ctx={''.join(map(str,ctx))}"); rid+=1
            # lo_i - delta(ctx) <= 0
            for c,v in ((lo,1.0),(idx(w1),-1.0),(idx(w0),1.0)):
                rows.append(rid); cols.append(c); data.append(v)
            b.append(0.0); labels.append(f"range:lower:i={i}:ctx={''.join(map(str,ctx))}"); rid+=1
        rows += [rid, rid]; cols += [hi, lo]; data += [1.0, -1.0]
        b.append(1.0); labels.append(f"range:width:i={i}"); rid+=1
    return sparse.coo_matrix((data,(rows,cols)),shape=(rid,total),dtype=np.float64).tocsr(), np.asarray(b,float), tuple(labels)


def solve_active_cell_lp(
    cell: ActiveCell,
    ref: BinaryProductReference,
    *,
    dual_tol: float = 1e-8,
    trace: DebugTrace | None = None,
    dump_dir: Path | None = None,
    interaction_encoding: str = "pairwise",
    topc_margin: float = 0.0,
) -> LPSolution:
    trace = trace or null_trace()
    if cell.m != ref.m:
        raise ValueError("active-cell/reference dimension mismatch")
    if tuple(tuple(float(x) for x in r) for r in cell.reference_probs) != ref.probs:
        raise ValueError("active-cell/reference probability mismatch; never solve a frozen cell under a different q")
    cell_A0, cell_b, cell_labels, objective0 = _active_cell_constraints(cell, ref, topc_margin=topc_margin)
    if interaction_encoding == "pairwise":
        cycle_A, cycle_b, cycle_labels = _binary_cycle_matrix(ref.m)
        cell_A = cell_A0
        objective = objective0
        n_variables = ref.n_worlds
        direct_cycles = True
    elif interaction_encoding == "range":
        cycle_A, cycle_b, cycle_labels = _binary_range_interaction_matrix(ref.m)
        extra = 2 * ref.m
        cell_A = sparse.hstack((cell_A0, sparse.csr_matrix((cell_A0.shape[0], extra))), format="csr")
        objective = np.concatenate((objective0, np.zeros(extra, dtype=np.float64)))
        n_variables = ref.n_worlds + extra
        direct_cycles = False
    else:
        raise ValueError(f"unknown interaction_encoding {interaction_encoding}")
    A = sparse.vstack((cycle_A, cell_A), format="csr")
    b = np.concatenate((cycle_b, cell_b))
    if dump_dir is not None:
        dump_dir = Path(dump_dir); dump_dir.mkdir(parents=True, exist_ok=True)
        sparse.save_npz(dump_dir / f"A_{cell.signature}.npz", A)
        np.save(dump_dir / f"b_{cell.signature}.npy", b)
        np.save(dump_dir / f"objective_{cell.signature}.npy", objective)
        (dump_dir / f"labels_{cell.signature}.json").write_text(
            json.dumps(list(cycle_labels) + list(cell_labels), indent=2), encoding="utf-8")
        (dump_dir / f"cell_{cell.signature}.json").write_text(
            json.dumps(cell.payload(), indent=2), encoding="utf-8")

    trace.event(
        "d6.lp.matrix",
        m=ref.m,
        cell=cell.signature,
        n_variables=n_variables,
        interaction_encoding=interaction_encoding,
        topc_margin=float(topc_margin),
        n_cycle_constraints=cycle_A.shape[0],
        n_cell_constraints=cell_A.shape[0],
        nnz=int(A.nnz),
    )
    started = time.perf_counter()
    res = linprog(
        -objective,
        A_ub=A,
        b_ub=b,
        bounds=[(None, None)] * n_variables,
        method="highs",
        options={"presolve": True},
    )
    elapsed = time.perf_counter() - started
    if not res.success:
        trace.event("d6.lp.failed", m=ref.m, cell=cell.signature, status=res.status, message=res.message)
        return LPSolution(
            False, int(res.status), str(res.message), None, ref.m - 1, None,
            None, None, None, None, [], [], cell, None, elapsed,
        )

    x = np.asarray(res.x, dtype=np.float64)
    gamma = float(objective @ x)
    slack = b - A @ x
    max_violation = float(max(0.0, -float(np.min(slack))))
    marginals = np.asarray(res.ineqlin.marginals, dtype=np.float64)
    # HiGHS/SciPy minimises -objective.  For <= inequalities its reported RHS
    # marginals are -lambda; lambda>=0 is the max-LP dual coefficient.
    dual = -marginals
    dual[np.abs(dual) < dual_tol] = 0.0
    dual_obj = float(b @ dual)
    stationarity = np.asarray(A.T @ dual - objective, dtype=np.float64)
    stationarity_max = float(np.max(np.abs(stationarity))) if stationarity.size else 0.0
    duality_gap = float(abs(gamma - dual_obj))
    n_cycle = cycle_A.shape[0]
    cycle_dual = dual[:n_cycle]
    cell_dual = dual[n_cycle:]
    dual_cycle_mass = float(np.sum(cycle_dual)) if direct_cycles else None

    active_cycles = []
    if direct_cycles:
        for idx in np.flatnonzero(cycle_dual > dual_tol):
            active_cycles.append({
                "row": int(idx),
                "label": cycle_labels[int(idx)],
                "dual": float(cycle_dual[int(idx)]),
                "slack": float(slack[int(idx)]),
            })
    # Evaluate the realised Top-C margin at the optimum.
    F_only = x[:ref.n_worlds]
    response = ref.response_matrix()
    qvals = np.einsum("iun,n->iu", response, F_only)
    spans = np.asarray([qvals[i, cell.response_max[i]] - qvals[i, cell.response_min[i]] for i in range(ref.m)], dtype=np.float64)
    topc_min_margin = min((float(spans[j] - spans[l]) for j in cell.selected for l in cell.competitor), default=float("inf"))

    active_ineq = []
    for local in np.flatnonzero(cell_dual > dual_tol):
        global_idx = n_cycle + int(local)
        active_ineq.append({
            "row": int(global_idx),
            "label": cell_labels[int(local)],
            "dual": float(cell_dual[int(local)]),
            "slack": float(slack[global_idx]),
        })

    trace.event(
        "d6.lp.solved",
        m=ref.m,
        cell=cell.signature,
        gamma=gamma,
        target=ref.m - 1,
        violation=gamma - (ref.m - 1),
        dual_cycle_mass=dual_cycle_mass,
        duality_gap=duality_gap,
        stationarity_max_abs=stationarity_max,
        active_cycle_count=len(active_cycles),
        active_cell_inequality_count=len(active_ineq),
        solve_seconds=elapsed,
        topc_min_margin=topc_min_margin,
    )
    return LPSolution(
        True,
        int(res.status),
        str(res.message),
        gamma,
        ref.m - 1,
        float(gamma - (ref.m - 1)),
        max_violation,
        duality_gap,
        stationarity_max,
        dual_cycle_mass,
        active_cycles,
        active_ineq,
        cell,
        x[:ref.n_worlds],
        elapsed,
        topc_min_margin,
    )



def exact_verify_binary_solution(
    sol: LPSolution,
    ref: BinaryProductReference,
    max_denominator: int = 100000,
    *,
    required_topc_margin: float = 0.0,
) -> dict:
    """Independent rational check of a solved binary active cell.

    This is intentionally separate from SciPy's primal/dual diagnostics.  It
    rationalises the returned F, recomputes product responses, active selectors,
    Top-C, mixed-difference modulus and compression losses, and flags an exact
    m-1 violation.  It is suitable for handing a small candidate to the Lean
    worker, but the final formal counterexample must still be encoded in Lean.
    """
    if not sol.success or sol.F is None:
        return {"verified": False, "reason": "no_primal_solution"}
    if tuple(tuple(float(x) for x in r) for r in sol.cell.reference_probs) != ref.probs:
        return {"verified": False, "reason": "reference_mismatch"}
    q = tuple(tuple(Fraction(str(float(x))).limit_denominator(max_denominator) for x in row) for row in ref.probs)
    Fv = tuple(Fraction(str(float(x))).limit_denominator(max_denominator) for x in sol.F)
    worlds = ref.worlds
    index = {w: i for i, w in enumerate(worlds)}

    def f(w): return Fv[index[tuple(w)]]
    def qcomp_weight(w, skip):
        out = Fraction(1, 1)
        for j, a in enumerate(w):
            if j != skip: out *= q[j][a]
        return out
    response = []
    for i in range(ref.m):
        row=[]
        for u in (0,1):
            row.append(sum((f(w)*qcomp_weight(w,i) for w in worlds if w[i]==u), Fraction(0,1)))
        response.append(tuple(row))
    def residual(S, w):
        return f(w) - sum((response[i][w[i]] for i in S), Fraction(0,1))
    rs=[residual(sol.cell.selected,w) for w in worlds]
    rt=[residual(sol.cell.competitor,w) for w in worlds]
    loss_s=(max(rs)-min(rs))/2
    loss_t=(max(rt)-min(rt))/2
    gamma=2*(loss_s-loss_t)
    scores=[max(r)-min(r) for r in response]
    topc=all(scores[j] >= scores[l] for j in sol.cell.selected for l in sol.cell.competitor)
    response_extrema=all(
        response[i][sol.cell.response_max[i]] == max(response[i]) and
        response[i][sol.cell.response_min[i]] == min(response[i])
        for i in range(ref.m)
    )
    active_residual=(
        residual(sol.cell.selected,sol.cell.selected_max)==max(rs) and
        residual(sol.cell.selected,sol.cell.selected_min)==min(rs) and
        residual(sol.cell.competitor,sol.cell.competitor_max)==max(rt) and
        residual(sol.cell.competitor,sol.cell.competitor_min)==min(rt)
    )
    delta=Fraction(0,1)
    for i in range(ref.m):
        other=[j for j in range(ref.m) if j!=i]
        contrasts=[]
        for ctx in itertools.product((0,1), repeat=ref.m-1):
            w0=[0]*ref.m; w1=[0]*ref.m
            for j,bit in zip(other,ctx): w0[j]=w1[j]=bit
            w1[i]=1
            contrasts.append(f(tuple(w1))-f(tuple(w0)))
        if contrasts:
            delta=max(delta,max(contrasts)-min(contrasts))
    rhs=Fraction(ref.m-1,1)*delta
    margin=min((scores[j]-scores[l] for j in sol.cell.selected for l in sol.cell.competitor), default=Fraction(10**9,1))
    exact_violation=gamma-rhs
    required_margin = Fraction(str(float(required_topc_margin))).limit_denominator(max_denominator)
    margin_ok = margin >= required_margin
    verified = bool(topc and margin_ok and response_extrema and active_residual and delta <= 1)
    return {
        "verified": verified,
        "topC": bool(topc),
        "response_extrema": bool(response_extrema),
        "active_residual_extrema": bool(active_residual),
        "scores": [str(x) for x in scores],
        "topc_min_margin": str(margin),
        "required_topc_margin": str(required_margin),
        "topc_margin_ok": bool(margin_ok),
        "delta_square": str(delta),
        "loss_selected": str(loss_s),
        "loss_competitor": str(loss_t),
        "gamma_doubled_gap": str(gamma),
        "m_minus_1_rhs": str(rhs),
        "exact_violation": str(exact_violation),
        "counterexample_to_m_minus_1": bool(verified and exact_violation > 0),
        "F_rational": [str(x) for x in Fv],
        "q_rational": [[str(x) for x in row] for row in q],
    }


def discover_active_cells(
    m: int,
    *,
    seed: int = 0,
    restarts: int = 8,
    closure_steps: int = 4,
    reference_modes: Sequence[str] = ("uniform", "point0"),
    dual_tol: float = 1e-8,
    trace: DebugTrace | None = None,
    dump_dir: Path | None = None,
    search_encoding: str = "range",
    refine_top: int = 3,
    topc_margin: float = 0.0,
    random_reference_denominator: int = 100,
    mutation_trials: int = 0,
    mutation_scale: float = 0.05,
    mutation_elites: int = 4,
) -> dict:
    if int(m) % 2:
        raise ValueError("active-cell balanced discovery requires even m")
    rng = np.random.default_rng(int(seed))
    trace = trace or null_trace()
    unique: dict[tuple[str, str], LPSolution] = {}
    failures: list[dict] = []

    for mode in reference_modes:
        fixed_ref = None if mode == "random" else make_reference(m, mode, rng, random_denominator=random_reference_denominator)
        for restart in range(int(restarts)):
            # Every random-reference restart gets its own exact rational q.
            ref = fixed_ref or make_reference(m, mode, rng, random_denominator=random_reference_denominator)
            # Mix dense random worlds and a sparse interaction-rich seed.
            F = rng.normal(0.0, 1.0, size=ref.n_worlds)
            if restart % 2:
                F *= rng.choice([-1.0, 1.0], size=ref.n_worlds)
                F[rng.random(ref.n_worlds) < 0.6] = 0.0
            seen_local = set()
            last_sol = None
            for step in range(int(closure_steps)):
                cell = derive_active_cell(F, ref)
                key = (mode, cell.signature)
                if key in seen_local:
                    break
                seen_local.add(key)
                if key in unique:
                    sol = unique[key]
                else:
                    subdump = None if dump_dir is None else Path(dump_dir) / f"m{m}" / mode
                    sol = solve_active_cell_lp(cell, ref, dual_tol=dual_tol, trace=trace, dump_dir=subdump, interaction_encoding=search_encoding, topc_margin=topc_margin)
                    unique[key] = sol
                last_sol = sol
                if not sol.success or sol.F is None:
                    failures.append({"reference": mode, "cell": cell.signature, "status": sol.status, "message": sol.message})
                    break
                # Cell-closure iteration: feed the LP maximiser back through the
                # nonlinear selector map.  A tiny deterministic jitter prevents
                # tie faces from repeatedly choosing an arbitrary zero-margin cell.
                F = np.asarray(sol.F, dtype=np.float64).copy()
                F += rng.normal(0.0, 1e-9, size=F.shape)


    solved = [s for s in unique.values() if s.success and s.gamma is not None]
    solved_sorted = sorted(solved, key=lambda s: float(s.gamma), reverse=True)

    # Targeted selector-neighbour search around the strongest LP maximisers.
    # Mutating only elite cells gives substantially better information per LP solve
    # than perturbing every low-value restart.
    if int(mutation_trials) > 0 and solved_sorted:
        elites = solved_sorted[: min(int(mutation_elites), len(solved_sorted))]
        for elite in elites:
            if elite.F is None:
                continue
            ref_elite = reference_from_cell(elite.cell)
            base_F = np.asarray(elite.F, dtype=np.float64)
            for trial in range(int(mutation_trials)):
                frac = trial / max(1, int(mutation_trials) - 1)
                # Sweep tiny-to-moderate perturbations to cross selector boundaries.
                scale = float(mutation_scale) * (10.0 ** (-2.0 + 2.0 * frac))
                mutated_F = base_F + rng.normal(0.0, scale, size=base_F.shape)
                mutated_cell = derive_active_cell(mutated_F, ref_elite)
                key = (mutated_cell.reference_key, mutated_cell.signature)
                if key in unique:
                    continue
                subdump = None if dump_dir is None else Path(dump_dir) / f"m{m}" / f"{mutated_cell.reference_key}_elite_mutated"
                msol = solve_active_cell_lp(
                    mutated_cell, ref_elite, dual_tol=dual_tol, trace=trace, dump_dir=subdump,
                    interaction_encoding=search_encoding, topc_margin=topc_margin,
                )
                unique[key] = msol
                if not msol.success:
                    failures.append({"reference": mutated_cell.reference_key, "cell": mutated_cell.signature, "status": msol.status, "message": msol.message})
        solved = [s for s in unique.values() if s.success and s.gamma is not None]
        solved_sorted = sorted(solved, key=lambda s: float(s.gamma), reverse=True)
    # Re-solve the strongest cells with direct rectangle constraints so the
    # output contains genuine cycle dual multipliers even when search used the
    # compact range formulation.
    if search_encoding != "pairwise" and refine_top > 0:
        refined = []
        for coarse in solved_sorted[: int(refine_top)]:
            mode = coarse.cell.reference_key
            # Reconstruct exactly the same q frozen into the active cell, including random q.
            ref2 = reference_from_cell(coarse.cell)
            subdump = None if dump_dir is None else Path(dump_dir) / f"m{m}" / f"{mode}_refined"
            refined.append(solve_active_cell_lp(coarse.cell, ref2, dual_tol=dual_tol, trace=trace, dump_dir=subdump, interaction_encoding="pairwise", topc_margin=topc_margin))
        refined_map = {(s.cell.reference_key, s.cell.signature): s for s in refined if s.success}
        solved_sorted = [refined_map.get((s.cell.reference_key, s.cell.signature), s) for s in solved_sorted]
        solved_sorted.sort(key=lambda s: float(s.gamma), reverse=True)
    best = solved_sorted[0] if solved_sorted else None
    exact_best = None
    if best is not None:
        exact_best = exact_verify_binary_solution(
            best, reference_from_cell(best.cell), required_topc_margin=topc_margin
        )
    numerical_counterexample = bool(best is not None and float(best.gamma) > (m - 1) + 1e-7)
    exact_counterexample = bool(exact_best and exact_best.get("verified") and exact_best.get("counterexample_to_m_minus_1"))
    return {
        "protocol_version": "d6_active_cell_lp_discovery_v2",
        "development_only": True,
        "binary_actions_only": True,
        "m": int(m),
        "seed": int(seed),
        "restarts": int(restarts),
        "closure_steps": int(closure_steps),
        "reference_modes": list(map(str, reference_modes)),
        "search_encoding": str(search_encoding),
        "refine_top": int(refine_top),
        "topc_margin": float(topc_margin),
        "random_reference_denominator": int(random_reference_denominator),
        "mutation_trials": int(mutation_trials),
        "mutation_scale": float(mutation_scale),
        "mutation_elites": int(mutation_elites),
        "unique_cells": int(len(unique)),
        "solved_cells": int(len(solved)),
        "failed_cells": failures,
        "target_m_minus_1": int(m - 1),
        "max_gamma": None if best is None else float(best.gamma),
        "max_violation": None if best is None else float(best.gamma - (m - 1)),
        "pattern_match": bool(best is not None and abs(float(best.gamma) - (m - 1)) <= 1e-7),
        "numerical_counterexample_candidate": numerical_counterexample,
        "exact_counterexample_verified": exact_counterexample,
        # Backwards-compatible key now means a verified exact counterexample, not merely a floating LP excess.
        "counterexample_found": exact_counterexample,
        "best": None if best is None else (best.to_json(include_F=True) | {"exact_rational_check": exact_best}),
        "top_cells": [s.to_json(include_F=False) for s in solved_sorted[: min(10, len(solved_sorted))]],
        "scope": "development LP discovery; sampled active cells are not an exhaustive proof",
    }
