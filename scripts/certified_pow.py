#!/usr/bin/env python3
"""Certified rational enclosures of irrational powers, by integer comparison only.

Every bound returned here is CHECKED with exact rational arithmetic before it is
handed back. A float is used only to seed the search; it never appears in a
certificate. This replaces the pattern

    c = Fraction(2 ** z).limit_denominator(10**12) * (1 - 1e-9)

which certifies nothing: rounding a float to a rational and nudging it does not
prove the result brackets the real number.

    c_lo <= base**(num/den) <= c_hi      certified by      c_lo**den <= base**num
                                                           base**num <= c_hi**den

and for `z* = 1 + 2 log2(g/mu)`,

    z_lo <= z* <= z_hi                   certified by      2**a <= (g/mu)**(2b)
                                                           for z_lo - 1 = a/b, etc.

Run directly for the self-tests.
"""
from fractions import Fraction as F
from functools import lru_cache
import math


def _pow_rat(x: F, n: int) -> F:
    return x ** n if n >= 0 else F(1) / (x ** (-n))


@lru_cache(maxsize=None)
def enclose_root(base: F, num: int, den: int, seed_digits: int = 20):
    """Rationals (lo, hi) with lo <= base**(num/den) <= hi, certified exactly.

    `den > 0`, `base > 0`. Certification: lo**den <= base**num <= hi**den.
    """
    if den <= 0 or base <= 0:
        raise ValueError("need den > 0 and base > 0")
    target = _pow_rat(base, num)
    approx = math.exp((num / den) * math.log(float(base)))
    seed = F(approx).limit_denominator(10 ** seed_digits)
    lo, step = seed, F(1, 10 ** seed_digits)
    while lo <= 0 or lo ** den > target:
        lo -= step
        step *= 2
        if lo <= 0:
            lo = target / (2 ** den) if target > 0 else F(1, 10 ** 30)
            break
    hi, step = seed, F(1, 10 ** seed_digits)
    while hi ** den < target:
        hi += step
        step *= 2
    if not (lo ** den <= target <= hi ** den):
        raise AssertionError("enclosure not certified")
    if lo <= 0:
        raise AssertionError("lower bound is not positive")
    return lo, hi


@lru_cache(maxsize=None)
def enclose_zstar(g: F, mu: F, den: int = 10 ** 4):
    """Rationals (z_lo, z_hi) with z_lo <= 1 + 2 log2(g/mu) <= z_hi.

    `z - 1 = a/den` satisfies `z <= z*`  iff  `2**(a/den) <= (g/mu)**2`
    iff  `2**a <= (g/mu)**(2*den)`, an exact comparison of rationals.
    """
    if g <= 0 or mu <= 0:
        raise ValueError("need g, mu > 0")
    ratio2 = (g / mu) ** 2
    zs = 1 + 2 * math.log(float(g) / float(mu), 2)
    a0 = int(math.floor((zs - 1) * den))
    rhs = ratio2 ** den

    def ok(a):
        return _pow_rat(F(2), a) <= rhs

    # O(1) scan: the float seed is within a couple of ticks of the true value
    a = None
    for cand in range(a0 - 3, a0 + 4):
        if ok(cand) and not ok(cand + 1):
            a = cand
            break
    if a is None:
        raise AssertionError("the float seed was not close enough to bracket z*")
    z_lo = 1 + F(a, den)
    z_hi = 1 + F(a + 1, den)
    # certify both ends
    if not (_pow_rat(F(2), a) <= rhs and rhs <= _pow_rat(F(2), a + 1)):
        raise AssertionError("z* enclosure not certified")
    return z_lo, z_hi


@lru_cache(maxsize=None)
def enclose_charge(r: int, z_lo: F, z_hi: F, seed_digits: int = 20):
    """Rationals (c_lo, c_hi) with c_lo <= r**z <= c_hi for EVERY z in [z_lo, z_hi].

    For r >= 1 the map z -> r**z is increasing, so the endpoints suffice; for
    r = 1 it is constant. Each endpoint is certified by `enclose_root`.
    """
    if r < 1:
        raise ValueError("width must be at least 1")
    if r == 1:
        return F(1), F(1)
    lo, _ = enclose_root(F(r), z_lo.numerator, z_lo.denominator, seed_digits)
    _, hi = enclose_root(F(r), z_hi.numerator, z_hi.denominator, seed_digits)
    if lo > hi:
        raise AssertionError("charge enclosure is inverted")
    return lo, hi


def _selftest():
    for base, num, den in ((F(2), 3, 4), (F(3), -5, 7), (F(5, 2), 11, 3),
                           (F(7), 1, 12), (F(1, 3), 4, 5)):
        lo, hi = enclose_root(base, num, den)
        true = math.exp((num / den) * math.log(float(base)))
        assert float(lo) <= true * (1 + 1e-12) and true <= float(hi) * (1 + 1e-12), \
            (base, num, den, float(lo), true, float(hi))
        assert lo ** den <= _pow_rat(base, num) <= hi ** den
    print("enclose_root: 5 cases, every enclosure certified by integer comparison")

    for g, mu in ((F(3, 4), F(1, 4)), (F(3, 5), F(2, 5)), (F(7, 8), F(1, 8))):
        zl, zh = enclose_zstar(g, mu)
        true = 1 + 2 * math.log(float(g) / float(mu), 2)
        assert float(zl) <= true <= float(zh), (g, mu, float(zl), true, float(zh))
        assert zh - zl <= F(1, 10 ** 4)
        print(f"  z*({g},{mu}) in [{float(zl):.9f}, {float(zh):.9f}], "
              f"width {float(zh-zl):.1e}")

    for r in (2, 3, 4, 5):
        zl, zh = enclose_zstar(F(3, 4), F(1, 4))
        cl, ch = enclose_charge(r, zl, zh)
        true = r ** (1 + 2 * math.log(3.0, 2))
        assert float(cl) <= true <= float(ch), (r, float(cl), true, float(ch))
    print("enclose_charge: r in {2,3,4,5}, every charge bracketed")

    # the pattern this replaces does NOT bracket: show it on one case
    z = 1 + 2 * math.log(3.0, 2)
    bad = F(2 ** z).limit_denominator(10 ** 12) * (1 + F(1, 10 ** 9))
    exact_lo, exact_hi = enclose_charge(2, *enclose_zstar(F(3, 4), F(1, 4)))
    print(f"the old pattern gives {float(bad):.12f}; the certified bracket is "
          f"[{float(exact_lo):.12f}, {float(exact_hi):.12f}]")
    print("  the old value is a rounded float times a nudge -- it proves nothing "
          "about the real number, whichever side it happens to land on")


if __name__ == "__main__":
    _selftest()
