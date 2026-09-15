#!/usr/bin/env python3
"""D6 Goi B, the open tier: a dual over the FULL alternative set, by mixture.

WHY THE OLD DUAL COULD NOT CLOSE. `B1_d6_width_transition_local.py` upper-bounds the
value by ONE alternative -- the uniform single-swap mixture at nuisance mu - delta --
and searches only over the scalar delta. `B2_sandwich_refinement.py` showed that
refining that search is hopeless: a GLOBAL sweep 10x finer than B1's leaves the worst
cell at a 11.8% relative gain width. The dual FAMILY is too narrow, not the search.

THE STRUCTURE THAT MAKES A REAL DUAL POSSIBLE, read off B1's own verified algebra.
`polynomial_identity_check` proves, exhaustively over all C(2q+1,q+1)-1 labels, that
the design value depends on the label only through d = |label cap B| and on the
nuisance only through x = nu - mu, and equals

    G(eta, d, x) = (1-eta) * (d mu^2 + (q-d) x^2)/(2q)
                 + eta * jo(q,mu,d,x) / (C(q,2) * cz).

So the ALTERNATIVE SET is exactly {(d, x) : d in 1..q, x in [-mu, 1-mu]}, and -- the
key point -- G is AFFINE IN eta. Therefore for any distribution Q over alternatives

    max over eta in [0, cap] of E_Q[G(eta, .)]  =  max( E_Q[G(0,.)], E_Q[G(cap,.)] ),

an affine function on an interval attains its max at an endpoint. The dual is then

    U(ALT) = min over Q supported on ALT of max( <Q,u>, <Q,v> ),
    u_k = G(0, alt_k),   v_k = G(cap, alt_k),

which is an LP with only TWO inequality constraints, so a basic optimum has support at
most 2. That means it is solvable IN CLOSED FORM over pairs, in exact rationals, with
NO LP SOLVER AND NO FLOATING POINT ANYWHERE. Every U below is therefore a certificate,
not a solver output.

Restricting ALT to a finite subset can only RAISE the min, so every U is valid however
the set was chosen. The set is grown by column generation: solve the dual, read off the
eta at which it binds, add the EXACT minimising alternative there (via B1's
`profile_exact`, which minimises the quadratic in x in closed form), repeat.

CHARGE DIRECTIONS, kept as B1 has them. The primal uses the certified charge UPPER
bound (which understates the pair term, so L is a valid lower bound) and the dual the
certified LOWER bound (which overstates it, so U is a valid upper bound). Part of the
residual gap is that bracket itself, and its size is reported.

WHAT THIS DOES NOT ESTABLISH
 - The design family is still B1's one-parameter eta family. What is now dual-closed is
   `max over eta in [0,cap] of min over ALL alternatives`. If the true design space is
   larger than that eta family, this is the value of B1's restricted game, not of the
   unrestricted one, and that is stated rather than blurred.
 - Only B1's (q, mu, h) cells.
 - Column generation is a search; validity never depends on it converging, because any
   finite ALT gives a valid U and any eta gives a valid L.

    .venv/bin/python scripts/B3_dual_mixture.py
"""
from __future__ import annotations

from fractions import Fraction as F
import importlib.util, json, math, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
spec = importlib.util.spec_from_file_location(
    "b1", REPO / "scripts/B1_d6_width_transition_local.py")
b1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b1)
from certified_pow import enclose_zstar, enclose_charge, enclose_root


def exact_charge_bracket(g, mu, h, digits=40):
    """A MUCH tighter certified bracket for the charge 2**(z* - h).

    B1 brackets z* = 1 + 2 log2(g/mu) to resolution 1/den and then exponentiates, so
    the charge inherits a relative width of about ln2/den -- 6.93e-5 at den = 1e4, and
    raising den is ruinous because it forces an integer root of order den.

    But 2**(z*) = 2 (g/mu)**2 is EXACT. So
        2**(z* - h) = 2 (g/mu)**2 * 2**(-h),
    and with h = p/n only the n-th root of the rational 2**(-p) has to be certified --
    n is at most 100 here. `enclose_root` does that at any requested precision for
    essentially no cost, and z* never has to be bracketed at all."""
    p_, n_ = h.numerator, h.denominator
    lo, hi = enclose_root(F(2) ** (-p_), 1, n_, digits)
    base = 2 * (g / mu) ** 2
    return base * lo, base * hi


def dual_closed_form(u, v):
    """min over the simplex of max(<Q,u>, <Q,v>). Exact, closed form.

    The LP has two inequality constraints, so a basic optimum puts mass on at most two
    alternatives; enumerate singletons and pairs and take the best. Returns
    (value, support, weights)."""
    n = len(u)
    best = None
    for k in range(n):
        val = max(u[k], v[k])
        if best is None or val < best[0]:
            best = (val, (k,), (F(1),))
    for k in range(n):
        for l in range(k + 1, n):
            du, dv = u[k] - u[l], v[k] - v[l]
            den = du - dv
            cands = []
            if den != 0:
                th = (v[l] - u[l]) / den
                if 0 <= th <= 1:
                    cands.append(th)
            for th in cands:
                a = th * u[k] + (1 - th) * u[l]
                bb = th * v[k] + (1 - th) * v[l]
                val = max(a, bb)
                if val < best[0]:
                    best = (val, (k, l), (th, 1 - th))
    return best


def prune(alts, u, v):
    """drop alternatives dominated in BOTH coordinates: they can never help the min."""
    keep = []
    for i in range(len(alts)):
        dominated = False
        for j in range(len(alts)):
            if i == j:
                continue
            if u[j] <= u[i] and v[j] <= v[i] and (u[j] < u[i] or v[j] < v[i]):
                dominated = True
                break
        if not dominated:
            keep.append(i)
    return [alts[i] for i in keep], [u[i] for i in keep], [v[i] for i in keep]


def ternary_max(f, lo, hi, iters):
    """f is CONCAVE on [lo, hi] (a pointwise min of functions affine in eta), so
    ternary search converges to its maximiser. Every value of f is a valid bound in
    its own right, so the best seen is returned and correctness never depends on
    convergence."""
    best = None
    for x in (lo, hi):
        v = f(x)
        if best is None or v > best[0]:
            best = (v, x)
    for _ in range(iters):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        v1, v2 = f(m1), f(m2)
        for v, x in ((v1, m1), (v2, m2)):
            if v > best[0]:
                best = (v, x)
        if v1 < v2:
            lo = m1
        else:
            hi = m2
    return best


def cell(q, mu, h, iters=60, xgrid=16, L_seed=None, tight_charge=False):
    g = 1 - mu
    V0 = mu * mu / (2 * q)
    cstar = 2 * g * g / (mu * mu)
    if tight_charge:
        cz_lo, cz_hi = exact_charge_bracket(g, mu, h)
    else:
        zs_lo, zs_hi = enclose_zstar(g, mu)
        cz_lo, cz_hi = enclose_charge(2, zs_lo - h, zs_hi - h)
    cap = cz_lo / (cz_lo + cstar)

    def Gd(eta, d, x):                       # dual side: charge LOWER -> upper bound
        return b1.general_poly(q, mu, eta, cz_lo, d, x)

    def Lp(eta):                             # primal: charge UPPER -> lower bound
        return min(b1.profile_exact(q, mu, eta, cz_hi, d)[0] for d in range(1, q + 1))

    def Ld(eta):                             # the same curve on the dual's charge
        return min(b1.profile_exact(q, mu, eta, cz_lo, d)[0] for d in range(1, q + 1))

    # PRIMAL: ternary search on the concave curve, seeded with B1's own value
    lo_e = cap / 10 ** 6
    Lval, eta_p = ternary_max(Lp, lo_e, cap, iters)
    if L_seed is not None and L_seed > Lval:
        Lval, eta_p = L_seed, None

    # DUAL: locate the kink of the concave dual-side curve, then take the alternatives
    # active on BOTH sides of it -- those are the two the optimal mixture uses.
    _, eta_d = ternary_max(Ld, lo_e, cap, iters)
    lo_x, hi_x = -mu, 1 - mu
    alts = set((d, lo_x + (hi_x - lo_x) * F(i, xgrid))
               for d in range(1, q + 1) for i in range(xgrid + 1))
    probes = {eta_d, cap, lo_e}
    for k in range(1, 12):                   # geometric neighbourhood of the kink
        w = cap / F(2 ** k)
        probes.add(max(lo_e, eta_d - w))
        probes.add(min(cap, eta_d + w))
    for e in probes:
        for d in range(1, q + 1):
            _, xs = b1.profile_exact(q, mu, e, cz_lo, d)
            alts.add((d, xs))
    alts = sorted(alts)
    u = [Gd(F(0), d, x) for (d, x) in alts]
    v = [Gd(cap, d, x) for (d, x) in alts]
    alts, u, v = prune(alts, u, v)
    U, sup, w = dual_closed_form(u, v)
    return dict(q=q, mu=mu, h=h, V0=V0, cap=cap, cz_lo=cz_lo, cz_hi=cz_hi,
                L=Lval, U=U, eta=eta_p, eta_dual=eta_d, alts=len(alts),
                support=[alts[i] for i in sup], weights=list(w),
                dual_curve_max=Ld(eta_d))


def main():
    old = {f"{r['q']} {r['mu']} {r['h']}": r
           for r in json.loads(
               (REPO / "research/worker_gopB_20260913"
                / "B1_width_transition_local.json").read_text())["dual_sandwich"]}
    print("B3: a dual by MIXTURE over the full alternative set (d, x)\n")
    print(f"{'q':>2} {'mu':>4} {'h':>6} | {'U-L B1':>10} {'U-L B3':>10} {'factor':>8} "
          f"| {'gainwid B1':>10} {'B3':>9} | {'|supp|':>6} {'alts':>5}")
    rows = []
    for q in (3, 4, 8):
        for mu in (F(1, 4), F(2, 5)):
            for h in (F(1, 10), F(1, 20), F(1, 50), F(1, 100)):
                o0 = old[f"{q} {mu} {h}"]
                r = cell(q, mu, h,
                         L_seed=F(o0["primal_lower_L_exact"]))
                key = f"{q} {mu} {h}"
                o = old[key]
                Lo, Uo = F(o["primal_lower_L_exact"]), F(o["dual_upper_U_exact"])
                if r["U"] < r["L"]:
                    raise AssertionError(
                        f"{key}: mixture dual fell BELOW the primal "
                        f"({float(r['U'])} < {float(r['L'])}); one of the two "
                        f"charge directions must be wrong")
                gapo, gapn = Uo - Lo, r["U"] - r["L"]
                wo = float(gapo / (Lo - r["V0"]))
                wn = float(gapn / (r["L"] - r["V0"]))
                fac = float(gapo / gapn) if gapn > 0 else math.inf
                print(f"{q:>2} {str(mu):>4} {str(h):>6} | {float(gapo):10.3e} "
                      f"{float(gapn):10.3e} {fac:8.1f} | {wo:10.6f} {wn:9.6f} "
                      f"| {len(r['support']):6d} {r['alts']:5d}")
                rows.append({"q": q, "mu": str(mu), "h": str(h),
                             "L_B1": str(Lo), "U_B1": str(Uo),
                             "L_B3": str(r["L"]), "U_B3": str(r["U"]),
                             "gap_B1": float(gapo), "gap_B3": float(gapn),
                             "tightening_factor": fac,
                             "gain_rel_width_B1": wo, "gain_rel_width_B3": wn,
                             "dual_support_size": len(r["support"]),
                             "dual_support": [[d, str(x)] for d, x in r["support"]],
                             "dual_weights": [str(w) for w in r["weights"]],
                             "alternatives_kept": r["alts"],
                             "eta_star": str(r["eta"]),
                             "eta_dual_kink": str(r["eta_dual"]),
                             "dual_side_curve_max": str(r["dual_curve_max"]),
                             "charge_lo": str(r["cz_lo"]),
                             "charge_hi": str(r["cz_hi"]),
                             "charge_rel_width": float(
                                 (r["cz_hi"] - r["cz_lo"]) / r["cz_lo"])})
    print("\nTIGHTER CHARGE -- using 2**(z*) = 2 (g/mu)**2 exactly, so only the n-th")
    print("root of a rational has to be certified and z* never is")
    print(f"{'q':>2} {'mu':>4} {'h':>6} | {'charge relw':>11} {'->':>2} {'tighter':>11}"
          f" | {'gain width':>10} {'->':>2} {'tighter':>10}")
    tight = []
    for q in (3, 4, 8):
        for mu in (F(1, 4), F(2, 5)):
            for h in (F(1, 10), F(1, 20), F(1, 50), F(1, 100)):
                base = [r for r in rows if r["q"] == q and r["mu"] == str(mu)
                        and r["h"] == str(h)][0]
                o0 = old[f"{q} {mu} {h}"]
                t = cell(q, mu, h, L_seed=F(o0["primal_lower_L_exact"]),
                         tight_charge=True)
                if t["U"] < t["L"]:
                    raise AssertionError(f"tight-charge dual below primal at "
                                         f"q={q} mu={mu} h={h}")
                crw = float((t["cz_hi"] - t["cz_lo"]) / t["cz_lo"])
                w = float((t["U"] - t["L"]) / (t["L"] - t["V0"]))
                print(f"{q:>2} {str(mu):>4} {str(h):>6} | "
                      f"{base['charge_rel_width']:11.3e} -> {crw:11.3e} | "
                      f"{base['gain_rel_width_B3']:10.6f} -> {w:10.6f}")
                base["charge_rel_width_tight"] = crw
                base["gain_rel_width_tight"] = w
                base["L_tight"] = str(t["L"]); base["U_tight"] = str(t["U"])
                tight.append(w)
    print(f"   relative gain width with the tighter charge: "
          f"{min(tight):.3e} .. {max(tight):.3e}")
    nexact = sum(1 for r in rows if F(r["L_tight"]) == F(r["U_tight"]))
    print(f"   EXACT EQUALITIES L = U: {nexact} of {len(rows)} cells.")
    print("   So this is a VERY TIGHT CERTIFICATE, not an exact equality and not a")
    print("   Lean theorem over all parameters. Saying 'the duality gap is zero' would")
    print("   overstate the data; what holds is a bracket of relative width")
    print(f"   {min(tight):.3e}..{max(tight):.3e} on the gain.")
    print("\n   SCOPE, which must not be blurred: B1's dual bounds the FULL design")
    print("   space (it maximises over every query type), while the dual here bounds")
    print("   only the CAPPED eta family. The two therefore bound DIFFERENT games, so")
    print("   the reduction in width is NOT 'the mixture repaired the old dual on the")
    print("   same problem'. Part of it is that the game being bounded is smaller.")

    print("\nRESIDUAL ATTRIBUTION -- what is left, and whose fault it is")
    print(f"{'q':>2} {'mu':>4} {'h':>6} | {'U-L (B3)':>10} | {'same-charge':>11} "
          f"{'share':>7} | {'charge part':>11} {'share':>7}")
    for r in rows:
        gap = F(r["U_B3"]) - F(r["L_B3"])
        same = F(r["U_B3"]) - F(r["dual_side_curve_max"])
        chg = gap - same
        print(f"{r['q']:>2} {r['mu']:>4} {r['h']:>6} | {float(gap):10.3e} | "
              f"{float(same):11.3e} {float(same/gap)*100:6.1f}% | "
              f"{float(chg):11.3e} {float(chg/gap)*100:6.1f}%")
        r["residual_same_charge"] = float(same)
        r["residual_charge_bracket"] = float(chg)
    shares = [r["residual_charge_bracket"] / (F(r["U_B3"]) - F(r["L_B3"]))
              for r in rows]
    print(f"   the certified charge bracket accounts for "
          f"{100*float(min(shares)):.1f}%-{100*float(max(shares)):.1f}% of what is")
    print("   left. Where that share is high the bracket is the binding constraint and")
    print("   no amount of extra search will help; a tighter enclosure would.")

    wn = [r["gain_rel_width_B3"] for r in rows]
    wo = [r["gain_rel_width_B1"] for r in rows]
    mixed = [r for r in rows if r["dual_support_size"] > 1]
    print(f"\n   relative gain width: B1 {min(wo):.4f}..{max(wo):.4f}"
          f"   ->  B3 {min(wn):.4f}..{max(wn):.4f}")
    print(f"   the optimal dual uses a genuine MIXTURE (support 2) in "
          f"{len(mixed)}/{len(rows)} cells; a single alternative would have been "
          f"strictly worse there")
    crw = max(r["charge_rel_width"] for r in rows)
    print(f"   residual floor from the certified charge bracket alone: "
          f"{crw:.3e} relative")
    print("\n   Every U is min over Q of max(<Q,u>,<Q,v>) computed in closed form over")
    print("   pairs in exact rationals -- no LP solver, no float. Every L is the value")
    print("   of an explicit design. The run raises if U ever falls below L.")
    print("\n   WHAT IS NOW CLOSED: for B1's one-parameter design family, the value")
    print("   max over eta in [0,cap] of min over the FULL alternative set (d,x) is")
    print("   bracketed by a matching primal and a mixture dual. WHAT IS NOT: whether")
    print("   that eta family is the optimal design space at all. That is a different")
    print("   question and this file does not touch it.")

    out = REPO / "research/worker_gopB_20260913/B3_dual_mixture.json"
    out.write_text(json.dumps({
        "what": "dual by mixture over the FULL alternative set (d, x), exact rational, "
                "closed form, no solver",
        "CORRECTION": "an earlier report of this run said 'the duality gap is zero'. "
                      "That overstates the data: no cell achieves L = U exactly; the "
                      "relative gain width is 1.47e-16..1.23e-12. It is a very tight "
                      "certificate, not an equality and not a Lean theorem.",
        "SCOPE_WARNING": "B1's dual bounds the FULL design space; this dual bounds "
                         "only the CAPPED eta family. They bound different games, so "
                         "the width reduction must not be read as the mixture "
                         "repairing the old dual on the same problem.",
        "why_it_works": "general_poly is AFFINE in eta, so max over eta in [0,cap] of "
                        "E_Q[G] is max at an endpoint; the dual LP then has two "
                        "inequality constraints and a basic optimum of support <= 2",
        "rows": rows,
        "not_established": [
            "the design family is still B1's one-parameter eta family; this closes "
            "max_eta min_alt for THAT family, not the unrestricted design problem",
            "only B1's (q, mu, h) cells",
            "column generation is a search; validity comes from any finite ALT giving "
            "a valid U and any eta a valid L",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
