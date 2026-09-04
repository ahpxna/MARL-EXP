"""Sweep driver for the CIG-AMF observatory.

Usage
-----
    python -m observatory.run --profile quick
    python -m observatory.run --profile screening --out research/observatory

A profile fixes the world families, dimensions, arities, budgets, tolerances and
seed count.  Nothing is aggregated here: the driver's only job is to visit a
reproducible set of instances and let every chain probe write its rows.
"""
from __future__ import annotations

import argparse
import random
import sys
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from observatory import equations  # noqa: F401  (declares the registry)
from observatory.exact import Q, ZERO
from observatory.schema import Emitter, make_context
from observatory.worlds import (FAMILIES, generate_world, ternary_falsifier,
                                staircase_family, coupled_support_witness,
                                same_summary_pair, ProductReference)
from observatory.chains import (support as C_support, master as C_master,
                                structural as C_structural, d6 as C_d6,
                                functional as C_functional, query as C_query,
                                cross as C_cross)

EPS_GRID = (Q(0), Q(1, 100), Q(1, 20), Q(1, 10), Q(1, 5), Q(1, 2), Q(1))

PROFILES = {
    "smoke": dict(families=("cartesian", "strong_coupling"), ms=(3,), arities=(2,),
                  seeds=1, epsilons=EPS_GRID[:4], staircase_r=(1, 2), d6_ms=(3,),
                  query_models=6),
    "quick": dict(families=FAMILIES, ms=(3, 4), arities=(2, 3), seeds=2,
                  epsilons=EPS_GRID, staircase_r=(1, 2, 3), d6_ms=(3, 4),
                  query_models=12),
    "screening": dict(families=FAMILIES, ms=(3, 4, 5), arities=(2, 3), seeds=5,
                      epsilons=EPS_GRID, staircase_r=(1, 2, 3, 4), d6_ms=(3, 4),
                      query_models=24),
    "deep": dict(families=FAMILIES, ms=(3, 4, 5, 6), arities=(2, 3, 4), seeds=10,
                 epsilons=EPS_GRID, staircase_r=(1, 2, 3, 4, 5), d6_ms=(3, 4),
                 query_models=48),
}


def budgets_for(m: int):
    return tuple(range(0, m + 1))


def run_profile(profile: str, out_path: Path, seed: int = 20260904,
                notes: str = "") -> Path:
    cfg = PROFILES[profile]
    ctx = make_context(profile, seed, root=ROOT, notes=notes)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    with Emitter(out_path, ctx) as em:
        rng = random.Random(seed)
        pool = []
        for fam in cfg["families"]:
            for m in cfg["ms"]:
                for arity in cfg["arities"]:
                    for s in range(cfg["seeds"]):
                        w = generate_world(fam, m, arity, rng=rng)
                        pool.append(w)
                        b = budgets_for(m)
                        C_support.run(em, w, budgets=b, epsilons=cfg["epsilons"][:3], rng=rng)
                        C_master.run(em, w, budgets=b, epsilons=cfg["epsilons"], rng=rng)
                        C_structural.run(em, w, rng=rng, epsilons=(ZERO, Q(1, 10)))
                        C_functional.run(em, w, rng=rng, budgets=b)
                        C_cross.run(em, w, budgets=b, epsilons=cfg["epsilons"])
                        if w.support.is_cartesian and m in cfg["d6_ms"]:
                            C_d6.run(em, w, budgets=b, rng=rng)

        # -- named exact witnesses ------------------------------------
        for name, w in (("ternary_falsifier", ternary_falsifier()),
                        ("coupled_support", coupled_support_witness())):
            b = budgets_for(w.m)
            C_support.run(em, w, budgets=b, epsilons=(ZERO,), rng=rng)
            C_master.run(em, w, budgets=b, epsilons=cfg["epsilons"], rng=rng)
            C_cross.run(em, w, budgets=b, epsilons=cfg["epsilons"])
            if w.support.is_cartesian:
                C_d6.run(em, w, budgets=b, rng=rng)
        for r in cfg["staircase_r"]:
            w = staircase_family(r)
            C_structural.probe_staircase(em, w, r, {"family": "staircase", "r": r,
                                                    "m": w.m, "world_id": w.content_id()})
            if w.m <= 8:
                C_structural.run(em, w, rng=rng, epsilons=(ZERO,))

        # -- the same-summary twins are the Query chain's negative boundary --
        twins = []
        for scale in (Q(1), Q(1, 2), Q(2)):
            for m in cfg["ms"]:
                a, b = same_summary_pair(m, 2, residual_scale=scale)
                twins += [a, b]
                bb = budgets_for(m)
                C_cross.run(em, a, budgets=bb, epsilons=cfg["epsilons"])
                if a.support.is_cartesian and m in cfg["d6_ms"]:
                    C_d6.run(em, a, budgets=bb, rng=rng)

        qpool = [w for w in pool if w.m == max(cfg["ms"])][: cfg["query_models"]]
        C_query.run(em, twins + qpool, rng=rng)

        # -- master pieces that are not world-specific ------------------
        base_key = {"family": "synthetic", "m": 0, "arity": 0}
        C_master.probe_indispensability(em, dict(base_key))
        for i in range(6):
            C_master.probe_typed_completion(em, dict(base_key, draw=i), rng)
        for (A, B, N) in ((Q(1), Q(1), 100), (Q(1), Q(4), 100), (Q(3), Q(1), 240)):
            C_master.probe_budget_split(em, dict(base_key), A, B, N)

    print("profile=%s rows=%d elapsed=%.1fs -> %s"
          % (profile, em.n_rows, time.time() - t0, out_path))
    return out_path


def main(argv=None):
    p = argparse.ArgumentParser(description="CIG-AMF observatory sweep")
    p.add_argument("--profile", default="quick", choices=sorted(PROFILES))
    p.add_argument("--out", default="research/observatory")
    p.add_argument("--seed", type=int, default=20260904)
    p.add_argument("--notes", default="")
    a = p.parse_args(argv)
    stamp = time.strftime("%Y%m%d_%H%M%S")
    out = Path(a.out) / ("obs_%s_%s.jsonl" % (a.profile, stamp))
    run_profile(a.profile, out, a.seed, a.notes)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
