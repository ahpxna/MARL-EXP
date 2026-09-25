#!/usr/bin/env python3
"""Paper C: locate the magnitude-ratio transition of the two-magnitude family (NUMERICAL).

Question (and nothing more): `paperC_typed_frontier.json` shows that for counts (1,1,2,2) and
(2,2,2,2) the price V(0)/V_free and the free threshold change somewhere between a/b = 2 and
a/b = 3. This run locates the change on a finer ratio grid.

Model and solver: `frontier_value` of `scripts/EXP_paperC_typed_frontier.py`, which solves the
count-flow LP of `typed_flow_equivalence` (LeanPaperCTypedFlowV1) with HiGHS. Floating point, so
every value is NUMERICAL and the located transition is a conjecture for the proof stage.

SELF-CHECKS (refuse to write on failure):
* at a/b = 2 and a/b = 3, the values reproduce the stored rows of paperC_typed_frontier.json to
  1e-9 on its eta grid;
* every frontier is nonincreasing in eta;
* eta = m gives the unbanded value.

Usage:
    python -u scripts/EXP_paperC_typed_transition.py --smoke
    python -u scripts/EXP_paperC_typed_transition.py
Output (new file; refuses to overwrite): research/unified_20260919/paperC_typed_transition.json
(smoke: paperC_typed_transition_smoke.json)
"""

import hashlib
import importlib.util
import json
import pathlib
import sys
import time
from fractions import Fraction as Fr

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("typed_frontier", HERE / "EXP_paperC_typed_frontier.py")
tf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tf)

OUTDIR = pathlib.Path("research/unified_20260919")
STORED = OUTDIR / "paperC_typed_frontier.json"


def main():
    smoke = "--smoke" in sys.argv
    out = OUTDIR / ("paperC_typed_transition_smoke.json" if smoke else "paperC_typed_transition.json")
    if out.exists():
        print(f"refusing to overwrite {out}", file=sys.stderr)
        return 2
    checks = []

    def check(name, ok, detail=""):
        checks.append({"name": name, "ok": bool(ok), "detail": detail})
        print(f"  [{'OK  ' if ok else 'FAIL'}] {name}   {detail}", flush=True)
        return ok

    t0 = time.time()
    stored = json.loads(STORED.read_text())
    egrid_old = stored["eta_grid"]
    counts = [(1, 1, 2, 2), (2, 2, 2, 2)]
    # self-check 1: reproduce the stored rows at a/b = 2 and 3
    worst = 0.0
    for c in counts:
        for ab in ("2", "3"):
            row = next(r for r in stored["rows"]
                       if r["counts_+a_-a_+b_-b"] == list(c) and r["a_over_b"] == ab)
            w = [float(Fr(ab)), -float(Fr(ab)), 1.0, -1.0]
            for e, v_old in zip(egrid_old, row["values"]):
                worst = max(worst, abs(tf.frontier_value(w, list(c), e) - v_old))
    check("reproduces the stored rows at a/b = 2, 3", worst < 1e-9, f"largest gap {worst:.2e}")
    # the refined grid
    ratios = ([Fr(2), Fr(5, 2), Fr(3)] if smoke else [Fr(2) + Fr(i, 20) for i in range(0, 21)])
    egrid = [i / 40 for i in range(0, 49)]
    rows = []
    mono = True
    for c in counts:
        for ab in ratios:
            w = [float(ab), -float(ab), 1.0, -1.0]
            vals = [tf.frontier_value(w, list(c), e) for e in egrid]
            free = tf.frontier_value(w, list(c), 0.0, band=False)
            mono &= all(v2 <= v1 + 1e-9 for v1, v2 in zip(vals, vals[1:]))
            free_at = next((e for e, v in zip(egrid, vals) if abs(v - free) < 1e-9), None)
            rows.append({"a_over_b": str(ab), "counts_+a_-a_+b_-b": list(c), "m": sum(c),
                         "V0": vals[0], "Vfree": free,
                         "price_V0_over_free": (vals[0] / free) if free > 1e-12 else None,
                         "kinks_on_grid": tf.kinks(egrid, vals), "free_from_eta": free_at,
                         "values": vals})
            print(f"  c={c} a/b={str(ab):>5} price={rows[-1]['price_V0_over_free']:.4f} "
                  f"free_from={free_at} [{time.time()-t0:5.0f}s]", flush=True)
    check("every frontier is nonincreasing in eta", mono)
    w5 = [2.5, -2.5, 1.0, -1.0]
    check("eta = m gives the unbanded value",
          abs(tf.frontier_value(w5, [1, 1, 2, 2], 6.0) - tf.frontier_value(w5, [1, 1, 2, 2], 0.0, band=False)) < 1e-9)
    allok = all(c["ok"] for c in checks)
    if not allok:
        print("self-checks failed; not writing", file=sys.stderr)
        return 1
    rec = {"producer": "scripts/EXP_paperC_typed_transition.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "solver_source_sha256": hashlib.sha256((HERE / "EXP_paperC_typed_frontier.py").read_bytes()).hexdigest(),
           "model": "count flow of typed_flow_equivalence (LeanPaperCTypedFlowV1); HiGHS floats",
           "status": "NUMERICAL; the located transition is a grid conjecture, not a result",
           "eta_grid": egrid, "rows": rows, "checks": checks, "all_passed": allok,
           "wall_seconds": time.time() - t0}
    out.write_text(json.dumps(rec, indent=1))
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
