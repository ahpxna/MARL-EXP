"""Pattern mining over the long-format observatory store.

The store is deliberately unaggregated, so this module is where questions get
asked.  It answers four kinds, in increasing order of usefulness for finding a
next direction:

1. *Coverage*  -- which declared symbols never got emitted?  A silent gap in
   instrumentation looks exactly like a quantity that is always zero.
2. *Violations* -- every row where a declared inequality or predicate failed.
   These are candidate counterexamples and are printed with their full instance
   key so they can be rebuilt exactly.
3. *Tightness*  -- the smallest non-negative slack per equation.  A bound that
   is never close to tight is either loose or measured on the wrong family;
   a bound that touches zero is a sharpness witness.
4. *Discovery*  -- relations between quantities that nobody declared: pairs
   (X, Y) for which X <= Y held on every instance where both were measured,
   ranked by how much evidence supports them and how often they are tight.
   This is the part meant to generate conjectures rather than check them.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from observatory import equations  # noqa: F401
from observatory.schema import registry


# ------------------------------------------------------------------- loading

def _num(row):
    """Prefer the exact rational; fall back to the float; None when absent."""
    ex = row.get("exact")
    if ex:
        try:
            return Fraction(ex)
        except Exception:
            pass
    v = row.get("value")
    if v is None or isinstance(v, str):
        return None
    return v


def load(paths: Sequence[Path]):
    rows, headers, footers = [], [], []
    for p in paths:
        with Path(p).open(encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    r = json.loads(line)
                except json.JSONDecodeError:
                    continue
                rec = r.get("record")
                if rec == "q":
                    rows.append(r)
                elif rec == "run_header":
                    headers.append(r)
                elif rec == "run_footer":
                    footers.append(r)
    return rows, headers, footers


def _inst_key(r) -> Tuple:
    inst = r.get("instance") or {}
    return tuple(sorted((str(k), str(v)) for k, v in inst.items()))


# ------------------------------------------------------------------ analyses

def coverage(rows) -> Dict[str, Dict]:
    reg = registry()
    seen = defaultdict(set)
    for r in rows:
        seen[r["eq_id"]].add(r["symbol"])
    out = {}
    for eq_id, eq in sorted(reg.items()):
        got = seen.get(eq_id, set())
        missing = [s for s in eq.symbols if s not in got]
        out[eq_id] = {
            "chain": eq.chain,
            "declared": len(eq.symbols),
            "emitted": len(got),
            "missing": missing,
            "rows": sum(1 for r in rows if r["eq_id"] == eq_id),
            "status_note": eq.status_note,
        }
    return out


VIOLATION_SYMBOLS = ("holds", "holds_op", "holds_box", "violation", "sign_violation",
                     "nonneg_holds", "monotone_holds", "iff_holds", "implication_holds",
                     "sandwich_holds", "lp_valid", "raw_bound_holds",
                     "scaled_bound_holds", "identity_residual")


def violations(rows) -> List[Dict]:
    out = []
    for r in rows:
        # 'skipped', 'undefined' and 'blocked' are deliberately *not* failures.
        # Conflating them was the first bug this store caught in its own writer.
        if r["status"] != "measured":
            continue
        s, v = r["symbol"], r.get("value")
        if v is None:
            continue
        bad = False
        if s in ("holds", "holds_op", "holds_box", "nonneg_holds", "iff_holds",
                 "implication_holds", "sandwich_holds", "lp_valid",
                 "monotone_holds", "cover_feasible", "achieved_by_midpoint"):
            bad = (v == 0)
        elif s in ("violation", "sign_violation", "killed", "false_safe",
                   "would_have_been_silently_normalized"):
            # These are genuine failures of a declared claim.
            bad = (v != 0)
        elif s in ("exceeds_m_minus_1", "counterexample_local_ok_global_bad"):
            # Expected-and-wanted findings: the m-1 law is already falsified and
            # 'local does not imply global' is an active result.  They are
            # surfaced separately rather than as errors.
            bad = False
        elif s == "identity_residual":
            bad = (v != 0)
        if bad:
            out.append({
                "chain": r["chain"], "eq_id": r["eq_id"], "symbol": s,
                "value": v, "mode": r["mode"], "instance": r.get("instance", {}),
                "note": r.get("note", ""),
            })
    return out


def tightness(rows, top: int = 5) -> Dict[str, List[Dict]]:
    """Smallest non-negative slack per equation: the sharpness frontier."""
    by_eq = defaultdict(list)
    for r in rows:
        if r["role"] != "slack" or r["status"] != "measured":
            continue
        v = _num(r)
        if v is None or v < 0:
            continue
        by_eq[r["eq_id"]].append((v, r))
    out = {}
    for eq_id, items in by_eq.items():
        items.sort(key=lambda t: t[0])
        out[eq_id] = [{
            "slack": float(v), "slack_exact": str(v), "symbol": r["symbol"],
            "instance": r.get("instance", {}),
        } for v, r in items[:top]]
    return out


def _fact_table(rows):
    """(world_id, k) -> {'<eq>.<symbol>': numeric value}.

    Collisions keep the first value and count how many were dropped, which is
    reported: a high collision count means the join key is too coarse for that
    quantity and any correlation involving it should be read with care.
    """
    lo: Dict[Tuple, Dict[str, Fraction]] = defaultdict(dict)
    hi: Dict[Tuple, Dict[str, Fraction]] = defaultdict(dict)
    collisions = defaultdict(int)
    for r in rows:
        if r["status"] != "measured":
            continue
        v = _num(r)
        if v is None or isinstance(v, str):
            continue
        inst = r.get("instance") or {}
        wid = inst.get("world_id")
        if wid is None:
            continue
        key = (wid, str(inst.get("k", "")))
        col = r["eq_id"] + "." + r["symbol"]
        if col in lo[key]:
            collisions[col] += 1
            if v < lo[key][col]:
                lo[key][col] = v
            if v > hi[key][col]:
                hi[key][col] = v
        else:
            lo[key][col] = v
            hi[key][col] = v
    # A quantity measured several times per join key is exposed as its own
    # interval.  'max(X) <= min(Y)' is then a genuinely universal statement at
    # this granularity, instead of an accident of which row happened to be first.
    facts: Dict[Tuple, Dict[str, Fraction]] = defaultdict(dict)
    for key in lo:
        for col in lo[key]:
            facts[key][col + "|min"] = lo[key][col]
            facts[key][col + "|max"] = hi[key][col]
    return facts, dict(collisions)


def discover_inequalities(rows, *, min_support: int = 20, max_cols: int = 220,
                          min_distinct: int = 3):
    """Find (X, Y) with X <= Y on every jointly measured instance.

    Three filters separate a candidate law from an artefact, and all three are
    necessary -- without them the ranking fills up with pairs that are equal
    because both sides are identically zero:

    * *variation*  -- each side must take at least ``min_distinct`` values, so a
      constant column cannot dominate anything;
    * *distinctness* -- the two series must not be equal everywhere, which would
      make the "inequality" a definitional restatement (the exact radius and the
      modular radius are literally the same number on co-extremizable worlds);
    * *informativeness* -- the relation must be tight somewhere **and** slack
      somewhere.  A bound that is always tight is an identity; one that is never
      tight carries no information about where the truth sits.

    What survives is ranked by evidence: how many instances support it, and what
    fraction of those are tight.
    """
    facts, collisions = _fact_table(rows)
    counts = defaultdict(int)
    for d in facts.values():
        for c in d:
            counts[c] += 1
    cols = [c for c, n in sorted(counts.items(), key=lambda t: -t[1])[:max_cols]
            if n >= min_support]
    cand = []
    for i in range(len(cols)):
        for j in range(len(cols)):
            if i == j:
                continue
            a, b = cols[i], cols[j]
            # only compare an upper summary against a lower one
            if not (a.endswith("|max") and b.endswith("|min")):
                continue
            n = 0
            tight = 0
            min_slack = None
            max_slack = None
            ok = True
            va, vb = set(), set()
            identical = True
            for d in facts.values():
                if a not in d or b not in d:
                    continue
                n += 1
                va.add(d[a]); vb.add(d[b])
                if d[a] != d[b]:
                    identical = False
                sl = d[b] - d[a]
                if sl < 0:
                    ok = False
                    break
                if sl == 0:
                    tight += 1
                if min_slack is None or sl < min_slack:
                    min_slack = sl
                if max_slack is None or sl > max_slack:
                    max_slack = sl
            informative = (0 < tight < n)
            varied = len(va) >= min_distinct and len(vb) >= min_distinct
            if ok and n >= min_support and informative and varied and not identical:
                cand.append({
                    "lhs": a, "rhs": b, "support": n, "tight": tight,
                    "tight_rate": tight / n if n else 0.0,
                    "min_slack": float(min_slack) if min_slack is not None else None,
                    "max_slack": float(max_slack) if max_slack is not None else None,
                    "distinct_lhs": len(va), "distinct_rhs": len(vb),
                    "cross_chain": a.split(".")[0] != b.split(".")[0],
                    "cross_equation": a.split("|")[0].rsplit(".", 1)[0]
                                      != b.split("|")[0].rsplit(".", 1)[0],
                })
    # Rank by evidence first: a relation tight on 40% of 3000 instances is a
    # far better conjecture than one tight on 100% of 21.
    cand.sort(key=lambda c: (-(c["support"] * min(c["tight_rate"], 0.5)), -c["support"]))
    return cand, collisions


def correlations(rows, *, min_support: int = 30, top: int = 40):
    """Pearson correlation between every pair of jointly measured quantities."""
    facts, _ = _fact_table(rows)
    counts = defaultdict(int)
    for d in facts.values():
        for c in d:
            counts[c] += 1
    cols = [c for c, n in counts.items() if n >= min_support and c.endswith("|min")]
    series = {c: [] for c in cols}
    for d in facts.values():
        for c in cols:
            series[c].append(float(d[c]) if c in d else None)
    out = []
    for i in range(len(cols)):
        for j in range(i + 1, len(cols)):
            a, b = cols[i], cols[j]
            pairs = [(x, y) for x, y in zip(series[a], series[b])
                     if x is not None and y is not None
                     and math.isfinite(x) and math.isfinite(y)]
            if len(pairs) < min_support:
                continue
            xs = [p[0] for p in pairs]; ys = [p[1] for p in pairs]
            if len(set(xs)) < 3 or len(set(ys)) < 3:
                continue          # a near-constant column correlates with anything
            if xs == ys:
                continue          # the same quantity under two names
            mx = sum(xs) / len(xs); my = sum(ys) / len(ys)
            sxx = sum((x - mx) ** 2 for x in xs)
            syy = sum((y - my) ** 2 for y in ys)
            if sxx <= 0 or syy <= 0:
                continue
            sxy = sum((x - mx) * (y - my) for x, y in pairs)
            r = sxy / math.sqrt(sxx * syy)
            out.append({"a": a, "b": b, "r": r, "n": len(pairs),
                        "cross_chain": a.split(".")[0] != b.split(".")[0]})
    out.sort(key=lambda d: -abs(d["r"]))
    return out[:top]


def regime_scan(rows, group_keys=("family", "m", "arity")):
    """Holds-rate and mean slack per structural regime, per equation."""
    agg = defaultdict(lambda: {"n": 0, "holds": 0, "slack_sum": 0.0, "slack_n": 0})
    for r in rows:
        if r["status"] != "measured":
            continue
        inst = r.get("instance") or {}
        g = tuple(str(inst.get(k, "")) for k in group_keys)
        key = (r["eq_id"], g)
        if r["symbol"] in ("holds", "holds_op", "holds_box"):
            agg[key]["n"] += 1
            agg[key]["holds"] += int(bool(r.get("value")))
        if r["role"] == "slack":
            v = r.get("value")
            if isinstance(v, (int, float)) and math.isfinite(v):
                agg[key]["slack_sum"] += v
                agg[key]["slack_n"] += 1
    out = []
    for (eq_id, g), d in sorted(agg.items()):
        out.append({
            "eq_id": eq_id,
            **{k: v for k, v in zip(group_keys, g)},
            "n_holds_rows": d["n"],
            "holds_rate": (d["holds"] / d["n"]) if d["n"] else None,
            "mean_slack": (d["slack_sum"] / d["slack_n"]) if d["slack_n"] else None,
            "n_slack_rows": d["slack_n"],
        })
    return out


# -------------------------------------------------------------------- report

def report(paths: Sequence[Path], out_dir: Path, *, top: int = 25) -> Dict:
    rows, headers, footers = load(paths)
    out_dir.mkdir(parents=True, exist_ok=True)
    cov = coverage(rows)
    vio = violations(rows)
    tig = tightness(rows)
    ineq, collisions = discover_inequalities(rows)
    cors = correlations(rows)
    reg = regime_scan(rows)

    summary = {
        "n_rows": len(rows),
        "n_runs": len(headers),
        "equations_declared": len(cov),
        "equations_with_rows": sum(1 for v in cov.values() if v["rows"] > 0),
        "symbols_declared": sum(v["declared"] for v in cov.values()),
        "symbols_emitted": sum(v["emitted"] for v in cov.values()),
        "n_violations": len(vio),
        "n_candidate_inequalities": len(ineq),
        "join_key_collisions": collisions,
    }
    (out_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    (out_dir / "coverage.json").write_text(json.dumps(cov, indent=2), encoding="utf-8")
    (out_dir / "violations.json").write_text(json.dumps(vio, indent=2, default=str), encoding="utf-8")
    (out_dir / "tightness.json").write_text(json.dumps(tig, indent=2, default=str), encoding="utf-8")
    (out_dir / "candidate_inequalities.json").write_text(
        json.dumps(ineq[:400], indent=2, default=str), encoding="utf-8")
    (out_dir / "correlations.json").write_text(json.dumps(cors, indent=2), encoding="utf-8")
    (out_dir / "regime_scan.json").write_text(json.dumps(reg, indent=2, default=str), encoding="utf-8")

    _write_invariant_rows(ineq, out_dir)

    lines = ["# Observatory report", ""]
    lines.append("rows=%d  runs=%d  equations with data=%d/%d  symbols emitted=%d/%d"
                 % (summary["n_rows"], summary["n_runs"],
                    summary["equations_with_rows"], summary["equations_declared"],
                    summary["symbols_emitted"], summary["symbols_declared"]))
    lines += ["", "## Instrumentation gaps", ""]
    MINER_ONLY = {"X.cross_chain_invariant"}
    gaps = [(k, v) for k, v in cov.items() if v["missing"] and k not in MINER_ONLY]
    if not gaps:
        lines.append("None: every declared symbol was emitted at least once.")
    for k, v in sorted(gaps, key=lambda t: -len(t[1]["missing"]))[:top]:
        lines.append("- `%s` missing %d/%d: %s"
                     % (k, len(v["missing"]), v["declared"], ", ".join(v["missing"][:8])))
    lines += ["", "## Expected findings (the ledger predicts these)", ""]
    wanted = defaultdict(int)
    for r in rows:
        if r["status"] == "measured" and r.get("value"):
            if r["symbol"] in ("exceeds_m_minus_1", "counterexample_local_ok_global_bad",
                               "infeasible_maintenance", "reversal_witness",
                               "rankable_but_not_topc", "topc_but_not_coext"):
                wanted[r["eq_id"] + "." + r["symbol"]] += 1
    for k, n in sorted(wanted.items(), key=lambda t: -t[1]):
        lines.append("- `%s`: %d rows" % (k, n))
    if not wanted:
        lines.append("None fired in this store.")

    lines += ["", "## Violations (candidate counterexamples)", ""]
    if not vio:
        lines.append("None observed in this store.")
    else:
        byeq = defaultdict(int)
        for v in vio:
            byeq[v["eq_id"] + "." + v["symbol"]] += 1
        for k, n in sorted(byeq.items(), key=lambda t: -t[1])[:top]:
            lines.append("- `%s`: %d rows" % (k, n))
    lines += ["", "## Sharpest instances (smallest non-negative slack)", ""]
    flat = []
    for eq, items in tig.items():
        if items:
            flat.append((items[0]["slack"], eq, items[0]))
    for sl, eq, it in sorted(flat)[:top]:
        lines.append("- `%s` slack=%s at %s"
                     % (eq, it["slack_exact"], json.dumps(it["instance"], default=str)[:160]))
    lines += ["", "## Candidate inequalities never declared (X <= Y on all data)", ""]
    lines.append("Filtered to relations that vary on both sides, are tight somewhere "
                 "and slack somewhere, and are not definitional restatements.")
    lines.append("")
    if not ineq:
        lines.append("None survived the filters.")
    shown = 0
    for c in ineq:
        if shown >= top:
            break
        lines.append("- `%s` <= `%s`  support=%d tight=%d (%.0f%%) distinct=%d/%d%s"
                     % (c["lhs"], c["rhs"], c["support"], c["tight"],
                        100 * c["tight_rate"], c["distinct_lhs"], c["distinct_rhs"],
                        "  [cross-chain]" if c["cross_chain"] else ""))
        shown += 1
    lines += ["", "## Strongest correlations", ""]
    for c in cors[:top]:
        lines.append("- r=%+.3f n=%d  `%s` ~ `%s`%s"
                     % (c["r"], c["n"], c["a"], c["b"],
                        "  [cross-chain]" if c["cross_chain"] else ""))
    (out_dir / "REPORT.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return summary


def _write_invariant_rows(ineq, out_dir: Path, *, limit: int = 500) -> None:
    """Feed the discovered relations back into the store as X.cross_chain_invariant.

    A mined relation is a *hypothesis*, so it is written with the same schema as
    everything else and can be re-checked by the next sweep.  That is the loop
    the whole observatory exists to close: measure, mine, re-measure.
    """
    from observatory.schema import Emitter, make_context
    ctx = make_context("mined", 0, root=ROOT, notes="relations discovered by mine.py")
    path = out_dir / "mined_invariants.jsonl"
    if path.exists():
        path.unlink()
    with Emitter(path, ctx) as em:
        for i, c in enumerate(ineq[:limit]):
            inst = {"lhs": c["lhs"], "rhs": c["rhs"], "rank": i}
            em.emit(chain="CROSS", eq_id="X.cross_chain_invariant",
                    symbol="lhs_symbol", value=i, role="diag", instance=inst,
                    note=c["lhs"])
            em.emit(chain="CROSS", eq_id="X.cross_chain_invariant",
                    symbol="rhs_symbol", value=i, role="diag", instance=inst,
                    note=c["rhs"])
            em.emit(chain="CROSS", eq_id="X.cross_chain_invariant",
                    symbol="relation", value=0, role="diag", instance=inst,
                    note="lhs <= rhs")
            em.emit(chain="CROSS", eq_id="X.cross_chain_invariant",
                    symbol="support_count", value=c["support"], role="term", instance=inst)
            em.emit(chain="CROSS", eq_id="X.cross_chain_invariant",
                    symbol="violation_count", value=0, role="term", instance=inst)
            em.emit(chain="CROSS", eq_id="X.cross_chain_invariant",
                    symbol="holds", value=1, role="flag", instance=inst)
            if c["min_slack"] is not None:
                em.emit(chain="CROSS", eq_id="X.cross_chain_invariant",
                        symbol="slack", value=c["min_slack"], role="slack",
                        mode="float", instance=inst)
            em.emit(chain="CROSS", eq_id="X.cross_chain_invariant",
                    symbol="lhs_value", value=c["tight"], role="term", instance=inst,
                    note="number of tight instances")
            em.emit(chain="CROSS", eq_id="X.cross_chain_invariant",
                    symbol="rhs_value", value=c["support"] - c["tight"], role="term",
                    instance=inst, note="number of slack instances")


def main(argv=None):
    p = argparse.ArgumentParser(description="Mine the observatory store")
    p.add_argument("inputs", nargs="+")
    p.add_argument("--out", default="research/observatory/analysis")
    p.add_argument("--top", type=int, default=25)
    a = p.parse_args(argv)
    paths = []
    for i in a.inputs:
        pp = Path(i)
        paths.extend(sorted(pp.glob("*.jsonl")) if pp.is_dir() else [pp])
    s = report(paths, Path(a.out), top=a.top)
    print(json.dumps(s, indent=2)[:2000])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
