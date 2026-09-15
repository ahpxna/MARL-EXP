# Query weak leakage: the achievable order is decided by the measurement class.

`scripts/Q2_weak_leakage_order.py`, exact rational arithmetic on the cube.
Worlds: the certified raw-indistinguishable pair `A = {0,1,3}`, `B = {0,2,3}` at
`k = 3`, `t0 = 1/8` — 32 levels over 64 cube points, histograms equal exactly.

## The criterion, reduced to two finite linear/quadratic conditions

For `Y_h = F_A(X) + h g(X) + Z`, grouping the cube by baseline level and using
that shifted Gaussian derivatives at distinct levels are independent:

    order r >= 2  <=>  S_A(v) = S_B(v) for every level v,   S_W(v) = sum_{F_W=v} p g
    order r  = 2  <=>  additionally T_A(v) != T_B(v) somewhere, T_W(v) = sum_{F_W=v} p g^2

No density is integrated. The first condition is a LINEAR system in `g`; the
second is a quadratic check on its kernel. Both exact.

## The structural fact that decides everything

The permutation `pi = (1 2)` maps `A` to `B`, fixes the product reference and the
target set. Verified exactly on all 64 cube points: `F_B(x) = F_A(pi x)` and
`p(pi x) = p(x)`. Hence

    S_B^g = S_A^{g o pi}   and   T_B^g = T_A^{g^2 o pi},

and the same holds for every power of `g`. So a **pi-symmetric `g` separates the
two worlds at NO order at all**, however large `h` gets. Those are the useless
solutions of the first-order system, and the probe asserts on any pi-symmetric
`g` that separates at second order (none does).

That turns the question into: does the kernel of the first-order system contain
anything BEYOND the pi-symmetric functions?

## Result

    class                      dim   rank   kernel   pi-symmetric   breaking pi   order
    linear                       7      1        6              6             0    r = 1
    quadratic                   22      4       18             16             2    r = 2
    all functions on the cube    64     12       52             44             8    r = 2

* **Linear perturbations: the kernel is EXACTLY the pi-symmetric subspace.** Every
  linear `g` either fails the first-order condition — so it separates at `r = 1`,
  `KL = Theta(h^2)` — or is pi-symmetric and never separates at all. **There is no
  weak-leakage regime in the linear class.** This is the risk the assignment
  flagged ("if the admissible class gives only trivial solutions, drop `r = 2`"),
  and it materialises with a precise reason: the first-order condition collapses
  onto the transport symmetry.
* **Quadratic perturbations admit `r = 2`.** An explicit non-pi-symmetric `g` kills
  the first order and leaves second-order gap `2401/131072`, so
  `KL = Theta(h^4)`. Allowing all functions on the cube adds more such directions
  but does not improve the order.

So the exponent is not a free parameter to tune for a nicer rate: **it is fixed by
which perturbations are physically available.** That is a sharper statement than
"context helps", and it is falsifiable — enlarge or shrink the class and the
order moves.

## Consequence for the break-even, stated with the right exponents

If a context `X_S` separates the two worlds already at `h = 0`, then on this pair

    linear class     : N_raw = Theta(h^{-2} log(1/delta)),  N_context = O(log(1/delta))
    quadratic class  : N_raw = Theta(h^{-4} log(1/delta)),  N_context = O(log(1/delta))

with break-even at `c_ctx h^2 ~ 1` and `c_ctx h^4 ~ 1` respectively. The value of
keeping context is an order of magnitude more sensitive to `h` in the quadratic
class.

## WHAT THIS DOES NOT ESTABLISH

- **`KL = Theta(h^{2r})` is the reading of the expansion, not a proved bound.** No
  density is integrated, no remainder is bounded, and integrability of the
  expansion is not checked. The two `N_raw` rates above inherit that status: they
  are the consequence one expects, not a theorem.
- `N_context = O(log(1/delta))` is asserted from the `h = 0` separation, not
  proved here; the bounded-statistic route (`1{X_S=u} cos(tY)`) and its
  concentration bound are NOT implemented.
- One pair of worlds, one configuration (`k = 3`, `t0 = 1/8`). Nothing is claimed
  for other pairs, other `k`, or other measurement classes. In particular the
  conjectured `b_dec ~ k`, `b_id ~ 2k` is untouched.
- Nothing is formalised in Lean. The transport identity is verified pointwise on
  64 points, not proved as a theorem about `centeredWorld` — which is the same
  obligation still open from `LeanQueryInterventionFloorV1`.
- Singularity structure and slow mixture rates have a deep existing literature
  (Ho–Nguyen); the `h^4` phenomenon must not be advertised as new. What is
  specific here is the CIG measurement, the actual decision loss, and the fact
  that the order is pinned by the transport symmetry of the admissible class.
