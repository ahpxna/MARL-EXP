#!/usr/bin/env python3
"""Paper A, deviation P-2: the LOCKED deployable-policy panel -- paired trajectories over (r, M).

`EXP_paperA_deployable.py` was the pilot (24 runs per cell, M = 1).  This is the locked run the
supervision plan asks for: the SAME rules, certificate and stop, imported unchanged from the
pilot's module; the configuration fixed before launch and hashed into the artifact; common
random numbers across the three rules (one seed per cell and run, shared by every rule); 200
paired trajectories per cell.

    r in {1, 2, 4},  M in {1, 4},  base world (answer A) and swapped world (answer B),
    rules: surrogate_at_estimate, geometry, uniform;  alpha = 0.05;  B = 60000.

Recorded per run: tau, answer, censored, middle share, the rounds with an estimate off by 1/16
or more, the full count vector, and wall time.  Self-checks are the pilot's (certificate sides,
the surrogate oracle's exactness, accounting, the alpha tail, and the transcribed
`oCount_le_bad` bound) plus: every rule of a pair used the same seed.

Output (new file; refuses to overwrite): research/unified_20260919/paperA_deployable_paired.json.
Smoke: `--smoke --out DIR`.
"""

import hashlib
import json
import math
import pathlib
import sys
import time

import numpy as np

sys.path.insert(0, "scripts")
import EXP_paperA_deployable as D  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "research/unified_20260919/paperA_deployable_paired.json"
CHECKS = []
CONFIG = {"r_values": [1, 2, 4], "M_values": [1.0, 4.0], "worlds": [False, True],
          "rules": ["surrogate_at_estimate", "geometry", "uniform"], "alpha": 0.05,
          "budget": 60000, "n_runs": 200, "check_every": 50,
          "geometry_refresh_every": D.REFRESH_EVERY, "seed_base": 20260926}


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""), flush=True)
    return ok


def main():
    global OUT
    smoke = "--smoke" in sys.argv
    if "--out" in sys.argv:
        d = pathlib.Path(sys.argv[sys.argv.index("--out") + 1])
        d.mkdir(parents=True, exist_ok=True)
        OUT = d / OUT.name
    if OUT.exists():
        print(f"refusing to overwrite existing {OUT}", file=sys.stderr)
        return 2
    cfg = dict(CONFIG)
    if smoke:
        cfg.update({"r_values": [1], "M_values": [1.0, 4.0], "n_runs": 2, "budget": 3000})
    cfg_sha = hashlib.sha256(json.dumps(CONFIG, sort_keys=True).encode()).hexdigest()
    t0 = time.time()
    print("Paper A, P-2: locked deployable-policy panel, paired over rules", flush=True)
    rows, ok_count, ok_thm, thm_slack, ok_pair, ok_sides = [], True, True, math.inf, True, True
    for r in cfg["r_values"]:
        HSA, HSB = D.half_spaces_A(r), D.half_spaces_B(r)
        for M in cfg["M_values"]:
            for swapped in cfg["worlds"]:
                theta, var, bcells = D.build(r, M, swapped)
                n = len(theta)
                correct = D.answer_at(theta, bcells)
                w = D.w_uniform(n)
                v_ok = D.value_at(w, var, theta, HSA if correct == "A" else HSB)
                v_bad = D.value_at(w, var, theta, HSB if correct == "A" else HSA)
                ok_sides &= (v_ok > 0.0) and (v_bad == 0.0)
                for rule in cfg["rules"]:
                    recs = []
                    for ix in range(cfg["n_runs"]):
                        seed = [cfg["seed_base"], r, int(M), int(swapped), ix]
                        rng = np.random.default_rng(seed)
                        ts = time.time()
                        t, ans, N, c, bad_w, bad_est = D.run(rng, theta, var, bcells, HSA, HSB,
                                                             rule, cfg["alpha"], cfg["budget"],
                                                             cfg["check_every"])
                        q = D.forcing_quota(int(N.sum()), n)
                        for e in range(4, n):
                            slack = 2.0 + bad_w[e] + q - N[e]
                            thm_slack = min(thm_slack, slack)
                            ok_thm &= slack >= -1e-9
                        recs.append({"seed": seed, "tau": int(t), "answer": ans,
                                     "censored": bool(c),
                                     "middle_share": float(N[4:].sum() / N.sum()),
                                     "bad_estimate_rounds": int(bad_est),
                                     "counts": [float(x) for x in N],
                                     "wall_seconds": time.time() - ts})
                    stopped = [x for x in recs if not x["censored"]]
                    row = {"r": r, "M": M, "swapped": swapped, "correct_answer": correct,
                           "rule": rule, "runs": recs, "stopped": len(stopped),
                           "stopped_wrong": sum(1 for x in stopped if x["answer"] != correct),
                           "censored": sum(1 for x in recs if x["censored"]),
                           "restricted_mean_tau": float(np.mean([x["tau"] for x in recs]))}
                    ok_count &= row["stopped"] + row["censored"] == cfg["n_runs"]
                    rows.append(row)
                    print(f"  r={r} M={M} swapped={str(swapped):5s} {rule:22s}"
                          f" E[min(tau,B)]={row['restricted_mean_tau']:8.0f}"
                          f" stopped={row['stopped']:3d} wrong={row['stopped_wrong']}"
                          f" censored={row['censored']:3d}   [{time.time() - t0:7.0f}s]", flush=True)
                seeds = {rule: [x["seed"] for x in next(rw for rw in rows if rw["r"] == r
                                                         and rw["M"] == M
                                                         and rw["swapped"] == swapped
                                                         and rw["rule"] == rule)["runs"]]
                         for rule in cfg["rules"]}
                ok_pair &= all(seeds[x] == seeds[cfg["rules"][0]] for x in cfg["rules"])
    check("both certificates sit on the right sides at every truth", ok_sides)
    check("every run is accounted for exactly once as stopped or censored", ok_count)
    check("PAIRING: within a cell, every rule used the same seed for the same run", ok_pair)
    n_stop = sum(x["stopped"] for x in rows)
    n_wrong = sum(x["stopped_wrong"] for x in rows)
    tail = D.binom_tail(n_wrong, n_stop, cfg["alpha"]) if n_stop else 1.0
    check("wrong answers among stopped runs are consistent with alpha", tail >= 1e-3,
          f"{n_wrong} wrong of {n_stop} stopped, tail {tail:.3f}")
    check("THEOREM (`oCount_le_bad`, transcribed): N_e <= 2 + bad_e + q(t) on every middle cell"
          " of every run", ok_thm, f"min slack {thm_slack:.2f}")
    out = {"producer": "scripts/EXP_paperA_deployable_paired.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "rules_module_sha256": hashlib.sha256(
               pathlib.Path("scripts/EXP_paperA_deployable.py").read_bytes()).hexdigest(),
           "config": cfg, "locked_config_sha256": cfg_sha, "smoke": smoke, "rows": rows,
           "scope": "deployable policies under one two-answer lower certificate; alpha far"
                    " above delta_0; paired (common random numbers) across rules",
           "wall_seconds": time.time() - t0,
           "checks": CHECKS, "all_passed": all(c["ok"] for c in CHECKS)}
    if not out["all_passed"]:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    OUT.write_text(json.dumps(out))
    print(f"\n{sum(c['ok'] for c in CHECKS)}/{len(CHECKS)} self-checks passed; wrote {OUT}",
          flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
