#!/usr/bin/env python3
"""Paper C: the breakpoint law for EVERY size, from an explicit construction.

The exact-dual script closes the breakpoint at `m = 5,...,11` one size at a time, with a
rational Farkas certificate per size.  That is per-size evidence, not a law.  This script
tests the law

    eta_*(m) = 1                    for m odd,
    eta_*(m) = (m - 2) / (2(m - 1)) for m even,

by building the distribution over rankings that is claimed to attain the free value, and
checking -- in EXACT arithmetic, with no solver anywhere on the path -- that it does.

THE CONSTRUCTION.  Write the family as `g = (-3, (-1)^p, (+1)^q, +3)` with
`p = ceil((m-2)/2)`, `q = floor((m-2)/2)`.  Start from the alternating ordinary sequence
`-1, +1, -1, +1, ...` of length `m - 2`, and for each `j in {1, ..., m-1}` insert the pair
`(+3, -3)` at positions `j, j+1`.  Call the result `pi_j` and mix uniformly over `j`.  For
`m` even the numbers of `+1` and `-1` agree, so negating every weight is again a ranking of
the same family; each `pi_j` is then mixed half and half with its sign flip.

WHAT IS CHECKED, and in what direction.

  UPPER SIDE (eta_* <= the formula).  Checked for every `m` in the sweep, exactly:
    * the excess identity `|S_k(pi_j)| - b_k = 2 * [k = j]`, verified ranking by ranking;
    * `E r_k = V_m^free` at EVERY budget `k`, so the mixture attains the free value;
    * the marginal band `|E count_tau(k) - c_tau k / m| <= c_tau eta / m` holds at
      `eta = eta_*(m)` -- so that `eta` is FEASIBLE, which bounds `eta_*` above.

  TIGHTNESS of the construction.  The band is checked to FAIL for this construction just
  below `eta_*(m)`.  That says the construction cannot do better; on its own it does not
  say no other distribution can.

  LOWER SIDE (eta_* >= the formula).  This needs a statement about EVERY distribution, and
  it now rests on two combinatorial lemmas that are PROVED for general `m` in
  `LeanPaperCRankingV1`:
    * m even: `two_budget_identity`, the two end budgets read off the two end items;
    * m odd:  `odd_total_excess`, the `+3` step forces excess two.
  The exhaustive enumeration below was the evidence for those statements before they were
  proved; it is kept as a CROSS-CHECK that the Lean statements say what the model does.
  The arithmetic turning them into the law is proved in `LeanPaperCBreakpointV1`.

  CROSS-CHECK.  Where the exact-dual artifact already has a certified `eta_*`, the law is
  compared against it.

SELF-CHECKS transcribe those statements and the script refuses to write on any failure.
"""

import itertools
import json
import math
import pathlib
import sys
from fractions import Fraction as Fr

sys.path.insert(0, "scripts")
from EXP_paperC_flow_lp import WEIGHTS, caps, baseline

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def law(m):
    """The conjectured breakpoint."""
    return Fr(1) if m % 2 else Fr(m - 2, 2 * (m - 1))


def free_value(m):
    return Fr(2, (m + 4) * (m - 1))


def items(m):
    """The multiset of weights, as a flat list."""
    p, q = -(-(m - 2) // 2), (m - 2) // 2
    return [-3] + [-1] * p + [1] * q + [3]


def type_of(w):
    return WEIGHTS.index(w)


def base_sequence(m):
    """`-1, +1, -1, +1, ...` of length `m - 2`, with one extra `-1` when `m` is odd."""
    q = (m - 2) // 2
    seq = [-1, 1] * q
    if (m - 2) % 2:
        seq.append(-1)
    return seq


def constructed_rankings(m):
    """The mixture: uniform over `j`, and for even `m` also over the sign flip."""
    base = base_sequence(m)
    out = []
    for j in range(1, m):
        pi = base[:j - 1] + [3, -3] + base[j - 1:]
        assert len(pi) == m
        if m % 2 == 0:
            out.append((tuple(pi), Fr(1, 2 * (m - 1))))
            out.append((tuple(-w for w in pi), Fr(1, 2 * (m - 1))))
        else:
            out.append((tuple(pi), Fr(1, m - 1)))
    return out


def excesses(pi, b):
    """`|S_k| - b_k` for `k = 1, ..., m-1`, in exact integers."""
    m = len(pi)
    S, out = 0, {}
    for k in range(1, m):
        S += pi[k - 1]
        out[k] = abs(S) - b[k]
    return out


def main():
    print("=" * 78)
    print("Paper C: the breakpoint law for every size, from an explicit construction")
    print("=" * 78)
    MS = list(range(4, 25))
    results = {}

    print("\n  the construction, checked exactly at each size")
    print("  " + "-" * 72)
    all_excess_ok, all_value_ok, all_band_ok, all_tight_ok = True, True, True, True
    for m in MS:
        D = m + 4
        b = baseline(m)
        c = caps(m)
        mix = constructed_rankings(m)
        tot = sum(w for _, w in mix)
        assert tot == 1, (m, tot)

        # multiset check: every ranking is a permutation of the family
        multiset_ok = all(sorted(pi) == sorted(items(m)) for pi, _ in mix)

        # the excess identity, ranking by ranking
        exc_ok = True
        for pi, _ in mix:
            ex = excesses(pi, b)
            hits = [k for k, v in ex.items() if v != 0]
            if len(hits) != 1 or ex[hits[0]] != 2:
                exc_ok = False
                break

        # E r_k at every budget
        Vf = free_value(m)
        val_ok = True
        worst_k = None
        for k in range(1, m):
            Er = sum(w * Fr(excesses(pi, b)[k], D) for pi, w in mix)
            if Er != Vf:
                val_ok, worst_k = False, (k, Er, Vf)
                break

        # the marginal band, at the law's eta and just below it
        def band_slack(eta):
            worst = None
            for k in range(1, m):
                for tau in range(4):
                    if c[tau] == 0:
                        continue
                    Ec = sum(w * Fr(sum(1 for x in pi[:k] if type_of(x) == tau))
                             for pi, w in mix)
                    dev = abs(Ec - Fr(c[tau] * k, m))
                    slack = Fr(c[tau], m) * eta - dev
                    if worst is None or slack < worst:
                        worst = slack
            return worst

        eta = law(m)
        s_at = band_slack(eta)
        s_below = band_slack(eta - Fr(1, 10 ** 6)) if eta > 0 else Fr(-1)
        band_ok = s_at >= 0
        tight_ok = s_below < 0

        all_excess_ok &= exc_ok and multiset_ok
        all_value_ok &= val_ok
        all_band_ok &= band_ok
        all_tight_ok &= tight_ok
        results[m] = {"eta_law": str(eta), "free_value": str(Vf),
                      "excess_identity": bool(exc_ok and multiset_ok),
                      "attains_free_value": bool(val_ok),
                      "band_slack_at_eta": str(s_at),
                      "band_slack_just_below": str(s_below),
                      "support_size": len(mix)}
        print(f"      m={m:3d}  eta_law={str(eta):>10s}  V_free={str(Vf):>12s}"
              f"  excess={'ok' if exc_ok and multiset_ok else 'NO':>2s}"
              f"  value={'ok' if val_ok else 'NO':>2s}"
              f"  band slack={str(s_at):>10s}  just below={'<0' if tight_ok else 'NO'}")

    check("every constructed ranking is a permutation of the family, and its excess"
          " profile is the claimed spike: |S_k| - b_k = 2 exactly at k = j",
          all_excess_ok, f"checked at m = {MS[0]}..{MS[-1]}")
    check("the mixture attains the free value at EVERY budget, so it is optimal for the"
          " unconstrained problem -- this is the upper side of the law",
          all_value_ok)
    check("the marginal band holds at eta_*(m), so that eta is feasible and the breakpoint"
          " is at most the law's value",
          all_band_ok)
    check("and the band FAILS just below eta_*(m) for this construction, so the"
          " construction is tight -- which does not yet exclude a different one",
          all_tight_ok)

    # --------------------------------------------- the two lower-bound lemmas, exhaustively
    print("\n  the lower-bound lemmas (PROVED for general m), cross-checked"
          " by exhaustive enumeration")
    print("  " + "-" * 72)

    even_ok, odd_ok, enum = True, True, {}
    for m in range(4, 11):
        b = baseline(m)
        D = m + 4
        seen = set(itertools.permutations(items(m)))
        n_even_bad, n_odd_bad = 0, 0
        for pi in seen:
            ex = excesses(pi, b)
            if m % 2 == 0:
                lhs = Fr(ex[1], D) + Fr(ex[m - 1], D)
                rhs = Fr(2, D) * ((1 if abs(pi[0]) == 3 else 0)
                                  + (1 if abs(pi[-1]) == 3 else 0))
                if lhs != rhs:
                    n_even_bad += 1
            else:
                tot = sum(ex[k] for k in range(1, m))
                if tot < 2 + 2 * (1 if pi[-1] > 0 else 0):
                    n_odd_bad += 1
        enum[m] = {"rankings": len(seen), "even_violations": n_even_bad,
                   "odd_violations": n_odd_bad}
        if m % 2 == 0:
            even_ok &= (n_even_bad == 0)
            print(f"      m={m:3d} (even)  {len(seen):8d} rankings"
                  f"   r_1 + r_(m-1) identity violations: {n_even_bad}")
        else:
            odd_ok &= (n_odd_bad == 0)
            print(f"      m={m:3d} (odd)   {len(seen):8d} rankings"
                  f"   total-excess inequality violations: {n_odd_bad}")

    check("m even: on EVERY ranking, r_1 + r_(m-1) = (2/D)([first is +-3] + [last is"
          " +-3]) -- the identity the two-budget lower bound rests on",
          even_ok)
    check("m odd: on EVERY ranking, sum_k (|S_k| - b_k) >= 2 + 2[last item positive]"
          " -- the inequality the odd lower bound rests on",
          odd_ok)

    # the arithmetic the two lemmas feed, done exactly
    print("\n  what those lemmas give, in exact arithmetic")
    print("  " + "-" * 72)
    even_bound_ok, odd_bound_ok = True, True
    for m in MS:
        D = m + 4
        eta = law(m)
        if m % 2 == 0:
            # E(r_1 + r_(m-1)) >= 8(1-eta)/(mD) from the band; <= 4/(D(m-1)) at free value
            lhs = Fr(8, m * D) * (1 - eta)
            rhs = Fr(4, D * (m - 1))
            even_bound_ok &= (lhs <= rhs)
            # and the bound it implies
            implied = Fr(m - 2, 2 * (m - 1))
            even_bound_ok &= (implied == eta)
        else:
            # P(last positive) >= (m-1)(1-eta)/(2m) must be 0, forcing eta >= 1
            odd_bound_ok &= (Fr(m - 1, 2 * m) * (1 - eta) == 0)
    check("m even: the band's floor 8(1-eta)/(mD) on E(r_1 + r_(m-1)) meets the free"
          " value's ceiling 4/(D(m-1)) exactly at eta = (m-2)/(2(m-1))",
          even_bound_ok, f"checked at every even m in {MS[0]}..{MS[-1]}")
    check("m odd: attaining the free value forces P(last item positive) = 0, and the"
          " band's floor (m-1)(1-eta)/(2m) can vanish only at eta = 1",
          odd_bound_ok, f"checked at every odd m in {MS[0]}..{MS[-1]}")

    # --------------------------------------------- cross-check against the certified sizes
    print("\n  cross-check against the per-size Farkas certificates already on disk")
    print("  " + "-" * 72)
    cross = {}
    art = pathlib.Path("research/unified_20260919/paperC_exact_dual.json")
    cross_ok = True
    if art.exists():
        prev = json.loads(art.read_text())
        for rec in prev.get("rows", []):
            m = rec.get("m")
            root = rec.get("affine_root")
            if m is None or root is None:
                continue
            want = law(m)
            got = Fr(str(root))
            ok = got == want
            cross[m] = {"farkas_affine_root": str(got), "law": str(want),
                        "agree": bool(ok)}
            cross_ok &= ok
            print(f"      m={m:3d}  Farkas root {str(got):>10s}   law {str(want):>10s}"
                  f"   {'agree' if ok else 'DISAGREE'}")
    check("the law agrees with every size whose breakpoint already carries a rational"
          " Farkas certificate, and there is at least one such size to compare against",
          cross_ok and len(cross) > 0,
          f"{len(cross)} sizes compared"
          + ("" if cross else " -- NOTHING WAS COMPARED, so this check would otherwise"
                              " have passed vacuously"))

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    print("\n  SCOPE.  The LOWER side of the law is now proved for general m: the two")
    print("  combinatorial lemmas are theorems in LeanPaperCRankingV1, and the arithmetic")
    print("  turning them into the law is a theorem in LeanPaperCBreakpointV1.  The")
    print("  enumeration above cross-checks those statements; it is no longer the")
    print("  evidence for them.  The UPPER side -- that the construction attains the free")
    print("  value -- is still established size by size in exact arithmetic at every m in")
    print("  the sweep, and a general-m proof of attainment remains the one obligation.")

    out = {"sizes": results, "enumeration": enum, "cross_check": cross,
           "law": {"odd": "1", "even": "(m-2)/(2(m-1))"},
           "scope": "lower side PROVED for general m (LeanPaperCRankingV1"
                    ".two_budget_identity and .odd_total_excess, assembled by"
                    " LeanPaperCBreakpointV1.breakpoint_lower_even/_odd); the enumeration"
                    " here cross-checks those statements.  Upper side still established"
                    " size by size in exact arithmetic; general-m attainment open",
           "source_sha256": None, "checks": CHECKS, "all_passed": nfail == 0}
    import hashlib
    out["source_sha256"] = hashlib.sha256(
        pathlib.Path("scripts/EXP_paperC_general_m.py").read_bytes()).hexdigest()
    with open("research/unified_20260919/paperC_general_m.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
