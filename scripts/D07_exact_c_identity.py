#!/usr/bin/env python3
"""D07 probe A: the identity  c = a - b = (1-t)^(2q)  in the D6 reference instance.

Definitions transcribed LITERALLY from the Lean source (no paraphrase):

  LeanD6ReferenceResponseJoinV1.lean:63
    tailFactor t B = (1-t)^B.card + (B.card:R) * t * (1-t)^(B.card - 1)     -- NAT sub
  LeanD6ReferenceResponseJoinV1.lean:68
    gateMass t A j = (1-t)^A.card * tailFactor t (others A j)
  LeanD6ReferenceCenteredCompensatedV1.lean:70
    slopeBval t A j = (((others A j).card:R) - 1) * t
                        * (1-t)^(A.card + (others A j).card - 1)            -- NAT sub
  LeanD6ReferenceEndpointWorldsV1.lean:35-37
    a = gateMass, b = slopeBval, c = a - b

Cardinalities in the D6 instance (verified against LeanD6ThresholdConstructionV1.lean:454-455
and LeanD6ReferencePhaseWitnessV1.lean:witness_cards):
    ground   I (2q+1)                     (Fintype.card = 2q+2)
    positiveGround = univ.erase j         card = 2q+1
    worlds  = positiveGround.powersetCard (q+1)
    so  A.card = q+1 = k   and  (others A j).card = (univ \\ A).erase j |.card = q.

This probe does TWO independent exact checks:
  (1) polynomial-identity check: a(t) - b(t) - (1-t)^(2q) is the ZERO polynomial,
      verified coefficient-by-coefficient in exact integer arithmetic, for each q
      in a range.  (This is a proof for each individual q, not a sample.)
  (2) exact Fraction point evaluation at many (q, t) using the literal Lean
      expressions including the natural-number subtractions.
Optionally a sympy symbolic check in q as well, if sympy is importable.

Run:  python3 scripts/D07_exact_c_identity.py
"""
from fractions import Fraction

# ---------- exact univariate polynomials over Z, dense coefficient lists ----------

def pmul(u, v):
    out = [0] * (len(u) + len(v) - 1)
    for i, a in enumerate(u):
        if a:
            for j, b in enumerate(v):
                out[i + j] += a * b
    return out

def padd(u, v):
    n = max(len(u), len(v))
    return [(u[i] if i < len(u) else 0) + (v[i] if i < len(v) else 0) for i in range(n)]

def pscale(u, s):
    return [s * a for a in u]

def ppow(u, n):
    out = [1]
    for _ in range(n):
        out = pmul(out, u)
    return out

def is_zero(u):
    return all(a == 0 for a in u)

ONE_MINUS_T = [1, -1]   # 1 - t
T = [0, 1]              # t

# ---------- literal Lean definitions, as polynomials in t ----------

def tailFactor_poly(cardB):
    """(1-t)^|B| + |B| * t * (1-t)^(|B|-1) with NATURAL subtraction on |B|-1."""
    nat_sub = cardB - 1 if cardB >= 1 else 0
    return padd(ppow(ONE_MINUS_T, cardB),
                pscale(pmul(T, ppow(ONE_MINUS_T, nat_sub)), cardB))

def gateMass_poly(cardA, cardB):
    return pmul(ppow(ONE_MINUS_T, cardA), tailFactor_poly(cardB))

def slopeBval_poly(cardA, cardB):
    """((|B|:R) - 1) * t * (1-t)^(|A|+|B|-1); the -1 on the coefficient is REAL
    subtraction, the -1 in the exponent is NATURAL subtraction."""
    nat_sub = cardA + cardB - 1 if cardA + cardB >= 1 else 0
    return pscale(pmul(T, ppow(ONE_MINUS_T, nat_sub)), cardB - 1)

# ---------- literal Lean definitions, as exact Fractions ----------

def tailFactor_val(t, cardB):
    nat_sub = cardB - 1 if cardB >= 1 else 0
    return (1 - t) ** cardB + Fraction(cardB) * t * (1 - t) ** nat_sub

def gateMass_val(t, cardA, cardB):
    return (1 - t) ** cardA * tailFactor_val(t, cardB)

def slopeBval_val(t, cardA, cardB):
    nat_sub = cardA + cardB - 1 if cardA + cardB >= 1 else 0
    return (Fraction(cardB) - 1) * t * (1 - t) ** nat_sub


def main():
    print("=" * 78)
    print("D07 probe A : c = a - b = (1-t)^(2q)  in the D6 reference instance")
    print("cards: |A| = q+1 = k, |others A j| = q")
    print("=" * 78)

    # ---- check (1): polynomial identity in t, exact integers, per q ----
    QMAX = 60
    fails = []
    for q in range(0, QMAX + 1):
        cardA, cardB = q + 1, q
        a = gateMass_poly(cardA, cardB)
        b = slopeBval_poly(cardA, cardB)
        c = padd(a, pscale(b, -1))
        target = ppow(ONE_MINUS_T, 2 * q)
        diff = padd(c, pscale(target, -1))
        if not is_zero(diff):
            fails.append((q, diff))
    print(f"\n[1] polynomial identity  a(t)-b(t)-(1-t)^(2q) == 0  in Z[t]")
    print(f"    q = 0 .. {QMAX}  ({QMAX+1} values, each an EXACT coefficient-wise check)")
    print(f"    failures: {len(fails)}")
    for q, d in fails[:5]:
        print(f"      q={q}: residual poly {d}")

    # also record the *shape* of the cancellation for the write-up
    q = 5
    a = gateMass_poly(q + 1, q)
    b = slopeBval_poly(q + 1, q)
    print(f"    example q=5: a = {a}")
    print(f"                 b = {b}")
    print(f"                 a-b = {padd(a, pscale(b,-1))} = (1-t)^10 = {ppow(ONE_MINUS_T,10)}")

    # ---- check (2): exact Fraction evaluation on a (q,t) grid ----
    ts = [Fraction(0), Fraction(1, 25), Fraction(1, 17), Fraction(1, 8), Fraction(1, 4),
          Fraction(1, 3), Fraction(1, 2), Fraction(2, 3), Fraction(3, 4), Fraction(7, 8),
          Fraction(1), Fraction(37818, 1000000), Fraction(-1, 5), Fraction(6, 5)]
    n2 = 0
    bad2 = []
    for q in range(0, 41):
        for t in ts:
            a = gateMass_val(t, q + 1, q)
            b = slopeBval_val(t, q + 1, q)
            if a - b != (1 - t) ** (2 * q):
                bad2.append((q, t, a - b - (1 - t) ** (2 * q)))
            n2 += 1
    print(f"\n[2] exact Fraction point check, q=0..40 x {len(ts)} values of t "
          f"(incl. t outside [0,1]): {n2} cells, failures: {len(bad2)}")
    for z in bad2[:5]:
        print("      ", z)

    # ---- cross-check against the compiled Lean witness numbers ----
    t = Fraction(1, 25)
    q = 8
    a = gateMass_val(t, q + 1, q)
    b = slopeBval_val(t, q + 1, q)
    a_lean = Fraction(32, 25) * Fraction(24, 25) ** 16     # gateMass_witness
    b_lean = Fraction(7, 25) * Fraction(24, 25) ** 16      # slopeBval_witness
    print(f"\n[3] cross-check vs the PROVED Lean witness (q=8, t=1/25):")
    print(f"    a matches gateMass_witness  : {a == a_lean}")
    print(f"    b matches slopeBval_witness : {b == b_lean}")
    print(f"    c = a-b == (1-t)^16         : {a - b == Fraction(24,25)**16}")

    # ---- optional sympy symbolic-in-q check ----
    try:
        import sympy as sp
        tt, qq = sp.symbols('t q', positive=True)
        a_s = (1 - tt) ** (qq + 1) * ((1 - tt) ** qq + qq * tt * (1 - tt) ** (qq - 1))
        b_s = (qq - 1) * tt * (1 - tt) ** (2 * qq)
        expr = sp.simplify(sp.expand(a_s - b_s - (1 - tt) ** (2 * qq)))
        # sympy leaves a common factor (1-t)^(2q-1) un-collected; pull it out.
        # sympy leaves (1-t)^(2q-1) un-collected; substitute u = 1-t (u>0 symbolic)
        # so that u^(2q) = u * u^(2q-1) is applied, then the bracket collapses to 0.
        uu = sp.symbols('u', positive=True)
        expr_u = expr.subs(tt, 1 - uu)
        expr_u = sp.simplify(sp.powsimp(sp.expand(expr_u / uu ** (2 * qq - 1))))
        print(f"\n[4] sympy symbolic-in-q residual (raw)        : {expr}")
        print(f"    same, u = 1-t, divided by u^(2q-1)        : {expr_u}")
        print(f"    -> identity holds symbolically for all q  : {sp.simplify(expr_u) == 0}")
    except Exception as ex:                                    # pragma: no cover
        print(f"\n[4] sympy unavailable ({ex}); skipped. Checks [1]-[3] are exact and "
              f"sufficient for every q in range.")

    ok = not fails and not bad2
    print("\nVERDICT:", "IDENTITY CONFIRMED (exact)" if ok else "IDENTITY REFUTED")


if __name__ == "__main__":
    main()
