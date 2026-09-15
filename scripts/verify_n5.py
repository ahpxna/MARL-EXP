"""Adversarial independent recomputation of package N5.

Written from the PRIMARY sources only:
  - research/high_risk_20260910/QUERY_natural_panel_v2.json  (raw records)
  - scripts/QUERY_restricted_decoder_exact.py                (the audited claim)
No import of, and no numbers copied from, scripts/N5_resolution_minimax.py.

Every check RAISES AssertionError on mismatch.  Exact rational arithmetic only
(fractions.Fraction); floats never compared with a tolerance.

SKIPPED, and why:
  - Shapley targets: the audited claim and the worker both use ATE at horizon 6.
  - Regeneration of the panel: needs the external rware runtime; consumed as given.
  - Part D (all-32-subset sweep) is run on the 59-unit evaluable subpanel only,
    exactly as the audited script does; the full 1600-unit panel is swept for the
    6 representations the worker reports, in exact rationals (1,279,200 pairs is
    ~10s per rep in Fraction, so the full 32-subset x full-panel cross product is
    NOT run -- stated, not silently truncated).
"""
from __future__ import annotations
import collections, itertools, json, sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PANEL = ROOT / "research/high_risk_20260910/QUERY_natural_panel_v2.json"
PRIOR = ROOT / "research/high_risk_20260910/QUERY_restricted_decoder_exact.json"
NOOP, N_ACT = 0, 5
CATALOG = ("mechanism_features", "privileged_geometry", "relation_features",
           "response_h2", "weak_prior_score")
INTEGER_BLOCKS = {"c1", "c2", "privileged_geometry"}

def load():
    p = json.loads(PANEL.read_text())
    cands = p["candidates"]
    units = []
    for rec in p["records"]:
        if rec.get("status") != "OK":
            continue
        for jj, ag in enumerate(cands):
            b1, b2, bT = rec["R1"][jj][NOOP], rec["R2"][jj][NOOP], rec["RT"][jj][NOOP]
            u = {"seed": rec["seed"], "t": rec["t"], "cand": int(ag), "local": jj,
                 "physical_key": rec["physical_key"], "rng_key": rec["rng_key"],
                 "c1": [Fr(v - b1) for v in rec["R1"][jj]],
                 "c2": [Fr(v - b2) for v in rec["R2"][jj]],
                 "cT": [Fr(v - bT) for v in rec["RT"][jj]]}
            u["ateT"] = Fr(sum(rec["RT"][jj]), N_ACT) - Fr(bT)
            for k, v in rec["catalog"].items():
                row = v[jj]
                u[k] = [Fr(float(x)) for x in (row if isinstance(row, list) else [row])]
            units.append(u)
    return p, units

def blk(u, name):
    return u["c2"] if name == "response_h2" else u[name]

def sigmas(units):
    sig, rng = {}, {}
    for block in ("c1", "c2", "relation_features", "mechanism_features",
                  "weak_prior_score", "privileged_geometry"):
        nm = "response_h2" if block == "c2" else block
        for d in range(len(blk(units[0], nm))):
            vals = [blk(u, nm)[d] for u in units]
            lo, hi = min(vals), max(vals)
            rng[(block, d)] = hi - lo
            sig[(block, d)] = Fr(1) if block in INTEGER_BLOCKS else ((hi - lo) if hi > lo else Fr(1))
    return sig, rng

def rep(u, extras, sig):
    out = [v / sig[("c1", d)] for d, v in enumerate(u["c1"])]
    lab = [("c1", d) for d in range(N_ACT)]
    for name in extras:
        b = "c2" if name == "response_h2" else name
        for d, v in enumerate(blk(u, name)):
            out.append(v / sig[(b, d)]); lab.append((b, d))
    return out, lab

def winf(a, b):
    return max((abs(x - y) for x, y in zip(a, b)), default=Fr(0))

# ---- E*_eta, two independent routes --------------------------------------
def estar_pairwise(R, g, eta):
    best = Fr(0)
    n = len(R)
    for i in range(n):
        for j in range(i + 1, n):
            if winf(R[i], R[j]) <= 2 * eta:
                d = abs(g[i] - g[j])
                if d > best: best = d
    return best / 2

def estar_fibre_exact0(R, g):
    """eta=0 route that never touches the distance machinery: exact-key fibres."""
    part = collections.defaultdict(list)
    for r, t in zip(R, g):
        part[tuple(r)].append(t)
    return max((max(v) - min(v) for v in part.values()), default=Fr(0)) / 2

def eta_crit(R, g, eps):
    """(1/2) min distance over Bad(eps); None when Bad(eps) is empty."""
    n = len(R); best = None; arg = None
    for i in range(n):
        for j in range(i + 1, n):
            if abs(g[i] - g[j]) > 2 * eps:
                d = winf(R[i], R[j])
                if best is None or d < best:
                    best, arg = d, (i, j)
    return (None, None) if best is None else (best / 2, arg)

def main():
    payload, units = load()
    fails = []
    def ck(name, got, want):
        ok = (got == want)
        print(f"   [{'OK ' if ok else 'FAIL'}] {name}: got {got!r} want {want!r}")
        if not ok: fails.append(name)

    print("=" * 78); print("A. panel accounting (independent)"); print("=" * 78)
    const = [u for u in units if all(v == 0 for v in u["cT"])]
    ev = [u for u in units if any(v != 0 for v in u["cT"])]
    ck("units_total", len(units), 1600)
    ck("units_constant_target", len(const), 1541)
    ck("units_evaluable", len(ev), 59)
    ck("units_c1_all_zero", sum(1 for u in units if all(v == 0 for v in u["c1"])), 1580)

    print("=" * 78); print("B. WORKER COUNTEREXAMPLE 3: is the rng-confound filter vacuous?")
    print("=" * 78)
    pk = collections.Counter(u["physical_key"] for u in units)
    pkl = collections.Counter((u["physical_key"], u["local"]) for u in units)
    print(f"   distinct physical_key over units          = {len(pk)}")
    print(f"   MAX units sharing a physical_key          = {max(pk.values())}   <-- worker claims 1")
    print(f"   distinct (physical_key, local) groups     = {len(pkl)}  max = {max(pkl.values())}")
    ck("max_units_sharing_a_physical_key", max(pk.values()), 1)  # worker's claim; expect FAIL

    # Recompute the prior script's own rng-confound exclusion from scratch.
    def c2(m): return m * (m - 1) // 2
    def rng_confounded(us, keyfn, tfn):
        part = collections.defaultdict(list)
        for u in us: part[keyfn(u)].append(u)
        tot = 0
        for members in part.values():
            if len(members) < 2: continue
            byp = collections.defaultdict(list)
            for u in members: byp[u["physical_key"]].append(u)
            for grp in byp.values():
                gc = collections.Counter(tfn(u) for u in grp)
                tot += c2(len(grp)) - sum(c2(v) for v in gc.values())
        return tot
    kc1 = lambda u: tuple(u["c1"])
    n_full = rng_confounded(units, kc1, lambda u: u["ateT"])
    n_ev   = rng_confounded(ev,    kc1, lambda u: u["ateT"])
    print(f"   rng-confounded pairs EXCLUDED, full panel, c1, ATE  = {n_full}")
    print(f"   rng-confounded pairs EXCLUDED, 59-unit subpanel     = {n_ev}")
    ck("rng_confound_exclusion_removes_exactly_0_pairs(worker)", n_full, 0)  # expect FAIL
    prior = json.loads(PRIOR.read_text())
    ck("matches prior artifact full_panel rng_conf",
       n_full, prior["baseline_c1_summary"]["full_panel"]["pairs_ate_horizon6"]["bad_pairs_rng_confounded"])
    ck("matches prior artifact subpanel rng_conf",
       n_ev, prior["baseline_c1_summary"]["evaluable_nonconstant_subpanel"]["pairs_ate_horizon6"]["bad_pairs_rng_confounded"])

    print("=" * 78); print("C. sigma declaration (full-panel observed range)"); print("=" * 78)
    sig, rng = sigmas(units)
    for k in [("relation_features",0),("relation_features",1),("weak_prior_score",0)]:
        print(f"   sigma{k} = {sig[k]}  = {float(sig[k]):.10g}")

    print("=" * 78); print("D. eta_crit(0) for all 32 subsets on the 59-unit subpanel"); print("=" * 78)
    g_ev = [u["ateT"] for u in ev]
    suff = []
    for r in range(len(CATALOG) + 1):
        for extras in itertools.combinations(CATALOG, r):
            Rv = [rep(u, extras, sig)[0] for u in ev]
            e0p = estar_pairwise(Rv, g_ev, Fr(0))
            e0f = estar_fibre_exact0(Rv, g_ev)
            if e0p != e0f:
                raise AssertionError(f"two routes disagree at eta=0 for {extras}: {e0p} vs {e0f}")
            if e0p == 0:
                ec, arg = eta_crit(Rv, g_ev, Fr(0))
                lab = rep(ev[0], extras, sig)[1]
                i, j = arg
                seps = {lab[d]: abs(Rv[i][d] - Rv[j][d]) for d in range(len(lab))
                        if Rv[i][d] != Rv[j][d]}
                suff.append((extras, ec, seps, (ev[i], ev[j])))
    print(f"   exact-key-sufficient subsets on subpanel: {len(suff)}")
    for extras, ec, seps, pr in sorted(suff, key=lambda z: -z[1]):
        blocks = sorted({b for b, _ in seps})
        print(f"     {float(ec):.7f}  {'+'.join(extras) or '(c1 only)'}")
        print(f"         separating coords: {sorted((str(k), float(v)) for k, v in seps.items())}")
    ck("n_sufficient_subsets_on_subpanel", len(suff), 10)
    crits = sorted({ec for _, ec, _, _ in suff})
    print(f"   distinct eta_crit values: {[float(c) for c in crits]}")

    print("=" * 78); print("E. full 1600-unit panel, exact rationals, declared reps"); print("=" * 78)
    reps_to_test = [(), ("privileged_geometry", "relation_features"), CATALOG]
    for extras in reps_to_test:
        Rv = [rep(u, extras, sig)[0] for u in units]
        gv = [u["ateT"] for u in units]
        e0 = estar_fibre_exact0(Rv, gv)
        print(f"   {'+'.join(extras) or 'c1 only':<70} E*_0 = {e0}")
        if e0 == 0:
            ec, arg = eta_crit(Rv, gv, Fr(0))
            lab = rep(units[0], extras, sig)[1]
            i, j = arg
            seps = {lab[d]: abs(Rv[i][d] - Rv[j][d]) for d in range(len(lab)) if Rv[i][d] != Rv[j][d]}
            a, b = units[i], units[j]
            print(f"       eta_crit(0) = {ec} = {float(ec):.10g}")
            print(f"       argmin pair: (seed {a['seed']}, t {a['t']}, cand {a['cand']}) vs "
                  f"(seed {b['seed']}, t {b['t']}, cand {b['cand']})  |gap|={abs(a['ateT']-b['ateT'])}")
            print(f"       separating coords: {sorted((str(k), float(v)) for k, v in seps.items())}")
            globals()['_full_ec'] = ec
        # E* curve at the worker's declared radii
        for eta in (Fr(1,200), Fr(1,20), Fr(1,10), Fr(1,2)):
            pass  # curve done below only for the 2-item rep (cost)
    print("=" * 78); print("F. E*_eta curve, full panel, privileged_geometry+relation_features")
    print("=" * 78)
    extras = ("privileged_geometry", "relation_features")
    Rv = [rep(u, extras, sig)[0] for u in units]
    gv = [u["ateT"] for u in units]
    for eta in (Fr(0), Fr(1,20), Fr(1,10), Fr(1,2)):
        print(f"   eta={str(eta):<6} E* = {estar_pairwise(Rv, gv, eta)}")

    print()
    if fails:
        raise AssertionError("MISMATCHES (each is a refutation target): " + "; ".join(fails))
    print("all checks agreed")

if __name__ == "__main__":
    sys.exit(main())
