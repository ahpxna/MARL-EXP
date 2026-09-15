# D6 good-allocation sets, step 1: the blind threshold is strictly positive.

`scripts/D1_blind_allocation_threshold.py`. The assignment's first step is to
decide whether learning `A` is needed at all before measuring what it costs.

## Result

    q   mu     Gamma        V_blind      zeta_blind
    3   0.25   0.24231410   0.15000000   0.380969
    3   0.50   0.10769515   0.06666667   0.380969
    3   0.75   0.09375000   0.06786243   0.276134
    4   0.25   0.24171286   0.15050551   0.377338
    4   0.50   0.10742794   0.06689134   0.377338
    4   0.75   0.07031250   0.05555556   0.209877

**`zeta_blind > 0` in every cell measured.** (The `0.21`-`0.38` range is these
six cells only; the wider sweep reaches `0.17065` at `q=4, mu=0.65`.) No single allocation serves every world at the
optimal rate, so the cost of learning `A` in order to choose an allocation is not
zero, and steps 2–4 of the package (the packing number `L_zeta` and the
information lower bound) are worth doing.

The threshold is also the useful positive statement: for tolerance
`zeta >= zeta_blind` — about `0.38` at `q=3`, `mu <= 1/2` — the intersection
`∩_A W_zeta(A, mu)` is non-empty and **no discovery is needed at all**.

## Two structural facts worth following

* `zeta_blind` agrees TO SOLVER TOLERANCE at `mu = 0.25` and `mu = 0.5` (0.380969 at `q=3`,
  0.377338 at `q=4`) and then drops at `mu = 0.75`. The blind penalty is
  `mu`-independent over a region and only moves near the top. That is a candidate
  phase boundary in `mu`, and it is cheap to locate by bisection.
* It barely moves from `q=3` to `q=4` (0.380969 → 0.377338 at `mu <= 1/2`). If
  that persists, the blind penalty is an `O(1)` fraction rather than something
  growing with `q`, which would bound how much the discovery term can matter.

Neither is a law yet: two values of `q` and three of `mu`.

## The blind design itself is a single class

The optimal permutation-invariant allocation is not a spread-out mixture. Its
support:

    q=3 mu=0.25   ('g', 3, False) : 0.02857                      (one class)
    q=3 mu=0.50   ('g', 3, False) : 0.02857                      (one class)
    q=3 mu=0.75   ('g', 3, False) : 0.00160   ('s','coord') : 0.13487
    q=4 mu=0.25   ('g', 4, False) : 0.00794                      (one class)
    q=4 mu=0.50   ('g', 4, False) : 0.00794                      (one class)
    q=4 mu=0.75   ('g', 4, False) : 0.00039   ('s','coord') : 0.10569

For `mu <= 1/2` the whole blind mass sits on **one** class: joint queries of width
`q` with `h = false`, uniformly over every such subset. No scalars at all. At
`mu = 0.75` scalars take over and the joint class keeps only a sliver — which is
the same place `zeta_blind` drops. So the `mu`-region where `zeta_blind` is
constant is exactly the region where the blind design is the pure uniform
width-`q` joint design, and the drop at `mu = 0.75` is a change of support.

That is a falsifiable structural claim and the cheapest next check: bisect `mu`
between `0.5` and `0.75` and find where the scalar class enters. If the support
change and the `zeta_blind` kink coincide, that boundary is the object to name.

## Method, and why it is cheap

The problem is invariant under permutations of the non-special coordinates,
acting on both `w` and `A`. `V_A(w)` is an infimum of linear functionals of `w`,
hence concave, and `V_A(sigma w) = V_{sigma^{-1}A}(w)`. So for any `w`, its group
average `wbar` satisfies

    V_A(wbar) >= avg_sigma V_A(sigma w) = avg_sigma V_{sigma^{-1}A}(w) >= min_{A'} V_{A'}(w),

so the max-min is attained at a permutation-invariant allocation — and for such
an allocation `V_A` is the SAME number for every `A`. Hence
`V_blind = max over invariant w of V_{A_0,mu}(w)`, a maximisation over eight
class masses instead of over all worlds.

`Gamma` and `V_blind` are computed by the **same** cutting-plane loop on the
**same** alternative set, differing only in whether `w` is confined to the
invariant subspace, so the ratio does not compare two solvers. The unrestricted
branch reproduces the published solver's `Gamma` to 1e-7 in all six cells, which
is the correctness check on the evaluator.

One thing that had to be right: under the invariant restriction the normalisation
is `eqrow . m = 1` rather than `sum m = 1`, so the dual bound is the maximum of
the dual-weighted row PER UNIT of that constraint. With the raw maximum the
cutting plane does not converge.

## WHAT THIS DOES NOT ESTABLISH

- **Floating-point LP**, duality gap below `2e-8`. Not an exact rational
  certificate. The clean-looking values (`V_blind = 0.15` at `mu=0.25`,
  `1/15` at `mu=0.5`, `q=3`) are suggestive, not certified.
- `eps = 0`, `shell = 0`: the exact-identification game. Nothing here covers the
  approximate-answer game.
- `zeta_blind` is about achieving the OPTIMAL RATE with one allocation. It says
  nothing yet about `L_zeta` (how many worlds one allocation can serve below the
  threshold), nor about the information lower bound, nor about any algorithm.
- The symmetry reduction is an argument, not a Lean theorem, and the concavity of
  `V_A` in `w` is used without proof here (it is an infimum of linear functionals,
  the same fact already proved in the Functional modules, but not transported).
- Two values of `q` and three of `mu`. No law in `q` or `mu` is claimed.
