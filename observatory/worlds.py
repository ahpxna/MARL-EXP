"""Exact finite worlds: the shared substrate every chain is measured on.

A world is (support, additive primitives, baseline, interaction residual).
Everything the six chains argue about is a functional of that tuple:

    F(a) = b + sum_j f_j(a_j) + R(a)          on a in Omega

Support geometry lives in ``Omega``; interaction lives in ``R``; the response
primitives live in ``f``.  Keeping the three separable in the generator is what
lets a probe answer "was this an interaction failure or a support failure?",
which is precisely the distinction the Support report insists on.

All values are exact rationals.  Generators take an explicit ``rng`` and record
their parameters, so any world in the store can be rebuilt bit-for-bit.
"""
from __future__ import annotations

import itertools
import random
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Dict, Iterable, Mapping, Sequence, Tuple

import hashlib

from .exact import Q, ZERO, ONE, HALF, osc, half_osc, q

Action = Tuple[int, ...]


# ------------------------------------------------------------------ support

@dataclass(frozen=True)
class Support:
    """A feasible joint-action set, possibly a strict subset of the product."""
    action_sizes: Tuple[int, ...]
    omega: Tuple[Action, ...]

    def __post_init__(self):
        if not self.action_sizes:
            raise ValueError("a support needs at least one relation")
        if not self.omega:
            raise ValueError("omega must be non-empty")
        n_full = 1
        for n in self.action_sizes:
            n_full *= int(n)
        oset = frozenset(self.omega)
        if len(oset) != len(self.omega):
            raise ValueError("omega contains duplicate actions")
        for a in self.omega:
            if len(a) != len(self.action_sizes):
                raise ValueError("omega action has the wrong arity")
            for j, x in enumerate(a):
                if not 0 <= int(x) < self.action_sizes[j]:
                    raise ValueError("omega contains actions outside the product")
        object.__setattr__(self, "_omega_set", oset)
        object.__setattr__(self, "_n_full", n_full)
        object.__setattr__(self, "_proj", None)

    def contains(self, a) -> bool:
        return tuple(a) in self._omega_set

    @property
    def m(self) -> int:
        return len(self.action_sizes)

    def full_product(self):
        return itertools.product(*[range(n) for n in self.action_sizes])

    @property
    def n_full(self) -> int:
        return self._n_full

    @property
    def is_cartesian(self) -> bool:
        return len(self.omega) == self._n_full

    def projection(self, j: int) -> Tuple[int, ...]:
        """Actions of relation j that occur somewhere in Omega (memoized)."""
        cache = self._proj
        if cache is None:
            cache = tuple(
                tuple(sorted({a[i] for a in self.omega}))
                for i in range(len(self.action_sizes))
            )
            object.__setattr__(self, "_proj", cache)
        return cache[int(j)]

    def density(self) -> Q:
        return Q(len(self.omega), self.n_full)

    @staticmethod
    def cartesian(action_sizes: Sequence[int]) -> "Support":
        sizes = tuple(int(n) for n in action_sizes)
        return Support(sizes, tuple(itertools.product(*[range(n) for n in sizes])))

    def restricted(self, keep) -> "Support":
        omega = tuple(a for a in self.omega if keep(a))
        return Support(self.action_sizes, omega)


# -------------------------------------------------------------------- world

@dataclass(frozen=True)
class World:
    support: Support
    primitives: Tuple[Tuple[Q, ...], ...]        # f_j indexed by action id
    baseline: Q = ZERO
    residual: Mapping[Action, Q] = field(default_factory=dict)
    meta: Mapping[str, object] = field(default_factory=dict)

    def __post_init__(self):
        if len(self.primitives) != self.support.m:
            raise ValueError("one primitive vector per relation is required")
        for j, (vals, n) in enumerate(zip(self.primitives, self.support.action_sizes)):
            if len(vals) != n:
                raise ValueError("primitive %d has wrong arity" % j)

    # -- values ---------------------------------------------------------
    @property
    def m(self) -> int:
        return self.support.m

    def additive(self, a: Action) -> Q:
        return self.baseline + sum(self.primitives[j][a[j]] for j in range(self.m))

    def resid(self, a: Action) -> Q:
        return self.residual.get(tuple(a), ZERO)

    def value(self, a: Action) -> Q:
        return self.additive(a) + self.resid(a)

    def values_on_support(self) -> Tuple[Q, ...]:
        return tuple(self.value(a) for a in self.support.omega)

    # -- spans ----------------------------------------------------------
    def component_span(self, j: int, support: Support | None = None) -> Q:
        sup = support or self.support
        idx = sup.projection(int(j))
        vals = [self.primitives[int(j)][i] for i in idx]
        return osc(vals)

    def component_spans(self, support: Support | None = None) -> Tuple[Q, ...]:
        return tuple(self.component_span(j, support) for j in range(self.m))

    # -- support-aware compression -------------------------------------
    def omitted_sum(self, retained: Iterable[int], a: Action) -> Q:
        keep = set(int(j) for j in retained)
        return sum(self.primitives[j][a[j]] for j in range(self.m) if j not in keep)

    def additive_radius(self, retained: Iterable[int], support: Support | None = None) -> Q:
        """r_Omega(S) = (1/2) osc_{a in Omega} sum_{j not in S} f_j(a_j)."""
        sup = support or self.support
        return half_osc([self.omitted_sum(retained, a) for a in sup.omega])

    def true_compression_loss(self, retained: Iterable[int], support: Support | None = None) -> Q:
        """L_F(S): best scalar residual once the retained primitives are kept."""
        sup = support or self.support
        return half_osc([self.omitted_sum(retained, a) + self.resid(a) for a in sup.omega])

    def residual_supnorm(self) -> Q:
        vals = [abs(self.resid(a)) for a in self.support.omega]
        return max(vals) if vals else ZERO

    def is_additive(self) -> bool:
        return all(self.resid(a) == 0 for a in self.support.omega)

    # -- identity -------------------------------------------------------
    def content_id(self) -> str:
        """Deterministic content hash of the exact world.

        Two worlds with the same primitives, support, baseline and residual get
        the same id; anything else gets a different one.  Every emitted row
        carries this, which is what makes a downstream join between two
        quantities of the same instance actually correct.  Without it, rows from
        distinct worlds that happen to share (family, m, arity, |Omega|) are
        indistinguishable and any pivot silently mixes them.
        """
        h = hashlib.blake2b(digest_size=8)
        h.update(repr(self.support.action_sizes).encode())
        h.update(repr(sorted(self.support.omega)).encode())
        h.update(("%d/%d" % (self.baseline.numerator, self.baseline.denominator)).encode())
        for vals in self.primitives:
            h.update(b"|")
            for v in vals:
                h.update(("%d/%d;" % (v.numerator, v.denominator)).encode())
        h.update(b"#")
        for a in sorted(self.residual):
            v = self.residual[a]
            h.update(("%s=%d/%d;" % (a, v.numerator, v.denominator)).encode())
        return h.hexdigest()

    # -- interaction ----------------------------------------------------
    def _value_map(self):
        cache = getattr(self, "_vmap", None)
        if cache is None:
            cache = {a: self.value(a) for a in self.support.omega}
            object.__setattr__(self, "_vmap", cache)
        return cache

    def mixed_difference(self, i: int, x: Action, c: Action) -> Q:
        """Delta_i F(x,c) = F(x) - F(x with i<-c_i) - F(c with i<-x_i) + F(c)."""
        i = int(i)
        x = tuple(x); c = tuple(c)
        xc = list(x); xc[i] = c[i]
        cx = list(c); cx[i] = x[i]
        xc = tuple(xc); cx = tuple(cx)
        vm = self._value_map()
        try:
            return vm[x] - vm[xc] - vm[cx] + vm[c]
        except KeyError:
            raise KeyError("mixed difference needs all four corners in Omega")

    def delta_square(self) -> Q:
        """delta_box = sup over coordinates and corner pairs of |Delta_i F|.

        Defined only when Omega is Cartesian, which is exactly the D6
        applicability assumption; callers must check ``support.is_cartesian``
        and fail closed otherwise rather than projecting the input.
        """
        if not self.support.is_cartesian:
            raise ValueError("delta_square requires full Cartesian support")
        cached = getattr(self, "_delta", None)
        if cached is not None:
            return cached
        vm = self._value_map()
        omega = self.support.omega
        best = ZERO
        for i in range(self.m):
            for x in omega:
                xi = x[i]
                for c in omega:
                    ci = c[i]
                    if xi == ci:
                        continue
                    xc = x[:i] + (ci,) + x[i + 1:]
                    cx = c[:i] + (xi,) + c[i + 1:]
                    v = vm[x] - vm[xc] - vm[cx] + vm[c]
                    if v < 0:
                        v = -v
                    if v > best:
                        best = v
        object.__setattr__(self, "_delta", best)
        return best


# --------------------------------------------------------- product reference

@dataclass(frozen=True)
class ProductReference:
    """q(a) = prod_j q_j(a_j) with each q_j a nonnegative normalized weight."""
    weights: Tuple[Tuple[Q, ...], ...]

    def __post_init__(self):
        for j, w in enumerate(self.weights):
            if any(x < 0 for x in w):
                raise ValueError("reference weights must be nonnegative (coord %d)" % j)
            if sum(w) != ONE:
                raise ValueError("reference weights must sum to one (coord %d)" % j)

    def prob(self, a: Action) -> Q:
        out = ONE
        for j, i in enumerate(a):
            out *= self.weights[j][i]
        return out

    def is_point_mass(self) -> bool:
        return all(any(x == ONE for x in w) for w in self.weights)

    @staticmethod
    def point_mass(action_sizes: Sequence[int], at: Sequence[int] | None = None) -> "ProductReference":
        at = tuple(at or [0] * len(action_sizes))
        rows = []
        for n, i in zip(action_sizes, at):
            rows.append(tuple(ONE if k == i else ZERO for k in range(int(n))))
        return ProductReference(tuple(rows))

    @staticmethod
    def uniform(action_sizes: Sequence[int]) -> "ProductReference":
        return ProductReference(tuple(
            tuple(Q(1, int(n)) for _ in range(int(n))) for n in action_sizes
        ))

    @staticmethod
    def skewed(action_sizes: Sequence[int], mass: Q = Q(9, 10)) -> "ProductReference":
        rows = []
        for n in action_sizes:
            n = int(n)
            if n == 1:
                rows.append((ONE,))
                continue
            rest = (ONE - mass) / Q(n - 1)
            rows.append(tuple(mass if k == 0 else rest for k in range(n)))
        return ProductReference(tuple(rows))


# ------------------------------------------------------------- generators

def _rand_q(rng: random.Random, lo: int, hi: int, den: int) -> Q:
    return Q(rng.randint(int(lo), int(hi)), int(den))


FAMILIES = (
    "cartesian",
    "coextremizable",
    "weak_coupling",
    "moderate_coupling",
    "strong_coupling",
    "cancellation",
    "nonnested",
    "support_uncertainty",
    "random_sparse",
    "interaction_light",
    "interaction_heavy",
)


def generate_world(
    family: str,
    m: int,
    arity: int = 2,
    *,
    rng: random.Random,
    den: int = 4,
    span: int = 8,
) -> World:
    """Generate one exact world in a named structural family.

    Families differ in *why* they are hard, not merely in random seed:
    ``coextremizable`` admits simultaneous component extrema (Top-C is exact),
    the ``*_coupling`` family removes joint actions so component extrema cannot
    co-occur, ``cancellation`` builds components that cancel on the feasible
    set, ``nonnested`` targets budget optima that are not inclusion-ordered,
    and the ``interaction_*`` families keep support Cartesian but add residual.
    """
    sizes = tuple([int(arity)] * int(m))
    full = Support.cartesian(sizes)
    prim = tuple(
        tuple(_rand_q(rng, -span, span, den) for _ in range(int(arity)))
        for _ in range(int(m))
    )
    residual: Dict[Action, Q] = {}
    support = full
    meta: Dict[str, object] = {"family": family, "arity": int(arity)}

    if family == "cartesian":
        pass

    elif family == "coextremizable":
        # force each component to attain max at action 0 and min at last action
        prim = tuple(
            tuple(sorted(vals, reverse=True)) for vals in prim
        )

    elif family in ("weak_coupling", "moderate_coupling", "strong_coupling"):
        drop = {"weak_coupling": Q(1, 8), "moderate_coupling": Q(1, 3),
                "strong_coupling": Q(1, 2)}[family]
        keep = []
        for a in full.omega:
            if rng.random() >= float(drop):
                keep.append(a)
        if len(keep) < 2:
            keep = list(full.omega)[:2]
        support = Support(sizes, tuple(keep))
        meta["dropped_fraction"] = str(drop)

    elif family == "cancellation":
        # pair components so their sum is constant on a large slice of Omega
        prim = list(prim)
        for j in range(0, int(m) - 1, 2):
            prim[j + 1] = tuple(-v for v in prim[j])
        prim = tuple(prim)

    elif family == "nonnested":
        # make one small-span component indispensable only at larger budgets
        prim = list(prim)
        prim[0] = tuple(Q(k * span, den) for k in range(int(arity)))
        if int(m) >= 3:
            prim[1] = tuple(Q(k * span, den * 2) for k in range(int(arity)))
            prim[2] = tuple(Q(k * span, den * 2) for k in range(int(arity)))
        prim = tuple(prim)
        keep = [a for a in full.omega if not (a[0] == 0 and all(x == 0 for x in a[1:]))]
        support = Support(sizes, tuple(keep) if len(keep) >= 2 else full.omega)

    elif family == "support_uncertainty":
        keep = [a for a in full.omega if rng.random() > 0.25]
        if len(keep) < 2:
            keep = list(full.omega)[:2]
        support = Support(sizes, tuple(keep))
        meta["bracketed"] = True

    elif family == "random_sparse":
        n_keep = max(2, int(len(full.omega) * 0.3))
        keep = rng.sample(list(full.omega), n_keep)
        support = Support(sizes, tuple(sorted(keep)))

    elif family in ("interaction_light", "interaction_heavy"):
        scale = 1 if family == "interaction_light" else 4
        for a in full.omega:
            if rng.random() < 0.5:
                residual[a] = _rand_q(rng, -scale, scale, den)

    else:
        raise ValueError("unknown world family: " + str(family))

    return World(support, prim, ZERO, residual, meta)


# --------------------------------------------------- named exact witnesses

def ternary_falsifier() -> World:
    """The 4-Sep normalized ternary counterexample to the universal m-1 law.

    m = 4, U = {0,1,2}, point-mass reference at the all-zero action, selected
    S = {0,2}, competitor T = {1,3}.  All four response spans equal 1 and the
    unit mixed-difference bound holds, yet 2[L_F(S) - L_F(T)] = 4 > 3 = m-1.

    Reproduced here as a *target* for the probe rather than as an assertion:
    the probe recomputes every term and records whether the violation is still
    observed, so a future change to the definitions shows up as data.
    """
    m, arity = 4, 3
    sizes = tuple([arity] * m)
    full = Support.cartesian(sizes)
    # staircase-like components with unit spans
    prim = tuple(
        tuple(Q(0) if k == 0 else Q(1) if k == 1 else Q(1) for k in range(arity))
        for _ in range(m)
    )
    residual: Dict[Action, Q] = {}
    for a in full.omega:
        nz = sum(1 for x in a if x != 0)
        if nz >= 2:
            residual[a] = Q(-(nz - 1), 2)
    return World(full, prim, ZERO, residual, {"family": "ternary_falsifier", "arity": arity})


def staircase_family(r: int) -> World:
    """The 4-Sep Structural staircase F_r inside the actual supportOsc class.

    Ground set I_r = {0..r-1} x {+,-} so m = 2r.  Anchor action bottom has every
    component zero; at support coordinate i the positive component is
    f_{(j,+)}(i) = 1{j = i} and the negative staircase component is
    f_{(t,-)}(i) = -1{i <= t}.
    """
    r = int(r)
    if r < 1:
        raise ValueError("staircase parameter must be positive")
    m = 2 * r
    # one "action" per support coordinate, plus the anchor
    n_actions = r + 1          # 0..r-1 are coordinates, r is the anchor
    sizes = tuple([n_actions] * m)
    # Omega is the diagonal: every relation reads the same support coordinate.
    omega = tuple(tuple([i] * m) for i in range(n_actions))
    support = Support(sizes, omega)
    prim = []
    for j in range(r):                       # positive basis components
        prim.append(tuple(
            ONE if (i < r and i == j) else ZERO for i in range(n_actions)
        ))
    for t in range(r):                       # negative staircase components
        prim.append(tuple(
            -ONE if (i < r and i <= t) else ZERO for i in range(n_actions)
        ))
    return World(support, tuple(prim), ZERO, {},
                 {"family": "staircase", "r": r, "anchor_action": r})


def coupled_support_witness() -> World:
    """The P8/P10 witness: component spans 10 > 9 > 8, yet keeping the largest
    span is far from optimal because joint feasibility forbids co-extremization.
    """
    sizes = (2, 2, 2)
    full = Support.cartesian(sizes)
    # forbid the two corners that would let all three extrema co-occur
    omega = tuple(a for a in full.omega if a not in {(0, 0, 0), (1, 1, 1)})
    support = Support(sizes, omega)
    prim = ((Q(0), Q(10)), (Q(0), Q(9)), (Q(0), Q(8)))
    return World(support, prim, ZERO, {}, {"family": "coupled_support_witness"})


def support_compression_pair():
    """The exact two-world support-compression witness with Q*_eps = 1.

    Omega_small = {0,1} and Omega_large = {0,1,2} differ only at cell 2, and the
    zero-regret decisions reverse across that single membership bit.
    """
    sizes = (1,)
    # single relation with three actions; encode via arity 3 and one relation
    sizes = (3,)
    small = Support(sizes, ((0,), (1,)))
    large = Support(sizes, ((0,), (1,), (2,)))
    prim = ((Q(0), Q(1), Q(9)),)
    w_small = World(small, prim, ZERO, {}, {"family": "support_pair", "which": "small"})
    w_large = World(large, prim, ZERO, {}, {"family": "support_pair", "which": "large"})
    return w_small, w_large


def same_summary_pair(m: int = 3, arity: int = 2, *, residual_scale: Q = ONE):
    """Two worlds with *identical* component spans but different removal value.

    Component spans read only the additive primitives, so putting all the
    difference in the interaction residual produces exactly the Query chain's
    negative boundary: the pairwise response summary is the same, while the
    removal / synergy targets differ.  This is the witness that makes the
    quantitative error floor measurable instead of vacuous.
    """
    sizes = tuple([int(arity)] * int(m))
    full = Support.cartesian(sizes)
    prim = tuple(tuple(Q(k) for k in range(int(arity))) for _ in range(int(m)))
    r1: Dict[Action, Q] = {}
    r2: Dict[Action, Q] = {}
    for idx, a in enumerate(full.omega):
        if sum(a) >= 2:
            r1[a] = residual_scale
            r2[a] = -residual_scale
    w1 = World(full, prim, ZERO, r1, {"family": "same_summary", "arity": int(arity), "twin": "A"})
    w2 = World(full, prim, ZERO, r2, {"family": "same_summary", "arity": int(arity), "twin": "B"})
    return w1, w2
