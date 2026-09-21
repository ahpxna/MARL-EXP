#!/usr/bin/env python3
"""Paper A: the alternative set's active region really changes, and the change is real.

Theorem `alt_iff_exists_region` says the alternative set is the UNION of its polyhedral
regions.  A union is only worth carrying if more than one member is ever the cheapest.  If
the region realising the minimum-energy alternative never changed, the frozen surrogate
would be right and the whole decomposition would be decoration.

This script sweeps two continuous parameters and shows the active region moving:

  SWEEP V (variance).   Family 1 of `EXP_paperA_frozen_proxy`, with variance `M` on B's
                        middle cell.  As `M` grows the cheapest alternative stops closing
                        the original gap and starts lifting the cheap cell into the maximum,
                        which is a DIFFERENT region of the union.

  SWEEP G (geometry).   Variance held fixed and B's middle cell slid continuously.  Here
                        nothing about the noise changes; the extrema themselves move, so a
                        region change here cannot be blamed on the observation model.

A parameter sweep can manufacture a fake transition in two ways, and both are checked
against rather than assumed away:

  A GRID ARTEFACT would show the value jumping at the switch.  The true minimum over a
  union of closed regions is continuous in the parameter wherever the regions are, so at a
  genuine crossing the two competing regional minima must AGREE.  The script brackets the
  switch by bisection and checks that the incoming and outgoing regions meet there to
  `1e-6` -- a jump would mean one side never really was the minimum.

  A SOLVER FLAKE would show an uncertified winner.  Every region on both sides of every
  switch carries a KKT certificate in the sense of `kkt_region_minimum`, with multipliers
  recovered by non-negative least squares.

SELF-CHECKS transcribe proved statements: the winner is always KKT-certified, the winning
region's value never exceeds the frozen region's (a union contains its member), and the
value is continuous across every located transition.
"""

import json
import sys
from itertools import product

import numpy as np

sys.path.insert(0, "scripts")
from EXP_paperA_frozen_proxy import (J_frozen, kkt_residual, region_constraints,
                                     region_lower_bound, solve_region)

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def winning_region(a, b, varA, varB):
    """Return (value, region, worst KKT residual over all regions, n_certified)."""
    nA, nB = len(a), len(b)
    theta = np.concatenate([a, b])
    Hdiag = 1.0 / np.concatenate([varA, varB])
    best, reg, worst, ncert, nreg = np.inf, None, 0.0, 0, 0
    for iM, im, jM, jm in product(range(nA), range(nA), range(nB), range(nB)):
        Amat, bvec = region_constraints(nA, nB, iM, im, jM, jm)
        nreg += 1
        res = solve_region(theta, Hdiag, Amat, bvec)
        if res is None:
            continue
        st, ng, cp = kkt_residual(theta, Hdiag, Amat, bvec, res.x)
        k = max(st, ng, cp)
        if k <= 1e-5:
            ncert += 1
            worst = max(worst, k)
        if res.fun < best - 1e-12:
            best, reg = float(res.fun), (iM, im, jM, jm)
    return best, reg, worst, ncert, nreg


def sweep(name, mk, lo, hi, npts):
    """Evaluate the winner along a parameter and return the sampled trace."""
    trace = []
    for t in np.linspace(lo, hi, npts):
        a, b, varA, varB = mk(float(t))
        val, reg, worst, ncert, nreg = winning_region(a, b, varA, varB)
        trace.append({"t": float(t), "value": val, "region": list(reg),
                      "frozen": J_frozen(a, b, varA, varB),
                      "worst_kkt": worst, "certified": ncert, "regions": nreg})
    return trace


def bisect_switch(mk, t_lo, t_hi, reg_lo, reg_hi, iters=40):
    """Bracket the parameter at which the winning region changes."""
    for _ in range(iters):
        mid = 0.5 * (t_lo + t_hi)
        a, b, varA, varB = mk(mid)
        _, reg, _, _, _ = winning_region(a, b, varA, varB)
        if list(reg) == list(reg_lo):
            t_lo = mid
        else:
            t_hi = mid
            reg_hi = reg
    return t_lo, t_hi, reg_hi


def regional_value(mk, t, reg):
    """The minimum over ONE named region at parameter `t`, or None if infeasible."""
    a, b, varA, varB = mk(t)
    theta = np.concatenate([a, b])
    Hdiag = 1.0 / np.concatenate([varA, varB])
    Amat, bvec = region_constraints(len(a), len(b), *reg)
    res = solve_region(theta, Hdiag, Amat, bvec)
    return None if res is None else float(res.fun)


def transitions(trace):
    out = []
    for i in range(1, len(trace)):
        if trace[i]["region"] != trace[i - 1]["region"]:
            out.append((i - 1, i))
    return out


def run(label, mk, lo, hi, npts, axis):
    print(f"\n  {label}")
    print("  " + "-" * 70)
    trace = sweep(label, mk, lo, hi, npts)
    prev = None
    for row in trace:
        mark = "  <-- region change" if prev and row["region"] != prev else ""
        print(f"      {axis}={row['t']:8.4f}:  J_full={row['value']:.6e}"
              f"  region={tuple(row['region'])}"
              f"  {row['certified']}/{row['regions']} certified{mark}")
        prev = row["region"]

    swaps = transitions(trace)
    located = []
    for i, j in swaps:
        t_lo, t_hi, reg_hi = bisect_switch(mk, trace[i]["t"], trace[j]["t"],
                                           trace[i]["region"], trace[j]["region"])
        tm = 0.5 * (t_lo + t_hi)
        v_in = regional_value(mk, tm, trace[i]["region"])
        v_out = regional_value(mk, tm, reg_hi)
        gap = abs(v_in - v_out) if (v_in is not None and v_out is not None) else None
        located.append({"t": tm, "from": list(trace[i]["region"]),
                        "to": list(reg_hi), "v_from": v_in, "v_to": v_out,
                        "meet_gap": gap})
        print(f"      switch at {axis} = {tm:.6f}:  {tuple(trace[i]['region'])}"
              f" -> {tuple(reg_hi)}   the two regions meet to {gap:.2e}")
    return trace, located


def main():
    print("=" * 78)
    print("Paper A: the active region of the alternative set moves, and moves genuinely")
    print("=" * 78)

    # ---------------- SWEEP V: the noise changes, the geometry does not
    def mk_var(logM):
        M = 10.0 ** logM
        return (np.array([0.0, 1.0, 0.5]), np.array([0.0, 0.75, 0.5]),
                np.array([1.0, 1.0, 1.0]), np.array([1.0, 1.0, M]))

    trV, swV = run("Sweep V: variance M on B's middle cell, geometry fixed",
                   mk_var, 0.0, 2.0, 11, "log10 M")

    # ---------------- SWEEP G: the geometry changes, the noise does not
    def mk_geo(c):
        return (np.array([0.0, 1.0, 0.5]), np.array([0.0, 0.75, c]),
                np.array([1.0, 1.0, 1.0]), np.array([1.0, 1.0, 4.0]))

    trG, swG = run("Sweep G: B's middle cell slid, variance fixed at 4",
                   mk_geo, 0.0, 1.6, 17, "c")

    print("\n  what the sweeps establish")
    print("  " + "-" * 70)
    regV = {tuple(r["region"]) for r in trV}
    regG = {tuple(r["region"]) for r in trG}
    print(f"      distinct winning regions: {len(regV)} along V, {len(regG)} along G")

    check("more than one region is ever the cheapest, so the union is not decoration",
          len(regV) > 1 or len(regG) > 1,
          f"{len(regV)} distinct along V, {len(regG)} along G")
    check("the geometry sweep alone changes the active region, so the transition is not"
          " an artefact of the observation model", len(regG) > 1,
          f"{len(swG)} switch(es) with variance held fixed")
    check("at every located transition the incoming and outgoing regions MEET, so the"
          " change is a crossing and not a jump",
          all(s["meet_gap"] is not None and s["meet_gap"] < 1e-6
              for s in swV + swG),
          f"{len(swV)+len(swG)} transitions, worst meeting gap "
          f"{max([s['meet_gap'] for s in swV+swG] or [0.0]):.2e}")
    check("every region on both sides of every switch is KKT-certified",
          all(r["certified"] == r["regions"] for r in trV + trG),
          f"{sum(r['certified'] for r in trV+trG)} certificates over "
          f"{len(trV)+len(trG)} parameter values")
    check("the union's minimum never exceeds the frozen region's, as a minimum over a"
          " superset must not",
          all(r["value"] <= r["frozen"] + 1e-9 for r in trV + trG))
    check("and it is strictly cheaper somewhere, which is what the frozen surrogate misses",
          any(r["value"] < r["frozen"] - 1e-9 for r in trV + trG),
          f"{sum(1 for r in trV+trG if r['value'] < r['frozen']-1e-9)} of "
          f"{len(trV)+len(trG)} parameter values")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperA_region_transition.py").read_bytes()).hexdigest(),"sweep_variance": trV, "switches_variance": swV,
           "sweep_geometry": trG, "switches_geometry": swG,
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperA_region_transition.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
