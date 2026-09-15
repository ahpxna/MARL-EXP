# F05: the full-extrema alternative is not the pair-flip calculation

**Date:** 2026-09-12 · **Evidence class: NUMERICAL EVIDENCE.** Nothing below is
proved. This is the step that decides whether the F05 region decomposition is
correct and whether the phenomenon it exists for is real, before any Lean.

Script: `scripts/f05_full_extrema_alternative_probe_v1.py`
Data: `research/high_risk_20260910/f05_full_extrema_probe_v1.json`

## Model, taken from the runner and not invented

From `run_functional_variance_stopping_lab_v4.py`: capacity is `np.ptp`, i.e.
`c_r = max_a t[r,a] - min_a t[r,a]`, and the answer is the Top-k of `c`. With
known independent cell variances and positive weights,
`KL = (1/2) sum w (dt)^2 / s2`.

## What `LeanFunctionalPairFlipCostV1` actually is

`energy v w x y = x^2/(2v) + y^2/(2w)`, `pair_flip_lower` giving
`gap^2/(2(v+w))`. Read against the model above, `v` and `w` are the effective
variances of the two capacities **with hi/lo pinned**:
`v_r = s2[r,hi]/w[r,hi] + s2[r,lo]/w[r,lo]`.

So the existing theorem is the fixed-extrema relaxation. It is correct as stated
about two free scalars; the question is whether the real problem reduces to it.

## Result 1 — the region decomposition checks out

For each relation, fixing an ordered pair `(hi, lo)` makes `c_r` linear, so the
alternative constraint is linear and the region is a polyhedron; minimising the
positive-definite cost over it is a convex QP. The regions cover everything,
since every point has some argmax and argmin.

Tested against an independent penalty search over the raw alternative set, with
no regions: **8 of 8 problems agree**, largest discrepancy `5.2e-7`.

That is support for the decomposition, not a proof that the regions cover the
set. The covering argument is what F05 has to formalise.

## Result 2 — the minimiser really does move the extrema

Extrema changed in **3 of 4** hand-built cases. The mechanism is concrete and
constructible in both directions:

- **Cheaper route via a middle cell.** If the out-relation's max and min are
  expensive (small `s2`) but a middle cell is cheap (`s2 = 100`), pushing that
  middle cell past the max is a longer move at a far lower price. Case B:
  the optimum moves the argmin from action 0 to action 1.
- **Kink on shrinking.** Lowering the in-relation's max below its runner-up
  makes the runner-up the new max, so further shrinking must move two cells.
  Case C: argmax moves from action 2 to action 1.

## Result 3 — the fixed-extrema value is a bound in NEITHER direction

| case | gap | pair-flip (fixed extrema) | true min | ratio | extrema |
|---|---:|---:|---:|---:|---|
| A uniform variances | 0.20 | 0.00500000 | 0.00500000 | 1.000 | unchanged |
| B cheap middle out | 0.20 | 0.00500000 | 0.00174757 | **0.349** | changed |
| C close runner-up in | 0.60 | 0.04500000 | 0.04911429 | **1.091** | changed |
| D both | 0.60 | 0.04500000 | 0.00507937 | **0.113** | changed |

Both directions occur, and neither is small:

- **B, D — the true minimum is cheaper.** The two-scalar model priced at the
  original extrema over-prices the move, because a different pair of cells is a
  cheaper route. In D it is off by a factor of 8.9.
- **C — the true minimum is dearer.** The two-scalar model under-prices, because
  it lets capacity shrink at a constant price past the point where the kink
  makes it more expensive.

So `gap^2/(2(v+w))` with `v, w` read off the original extrema is neither an upper
nor a lower bound on the KL to the full alternative set. It coincides with it
only when the extrema do not move (case A).

**Consequence for the sample-complexity direction.** The characteristic quantity
is a min over the alternative; a smaller min means a closer alternative and MORE
samples. Cases B and D have a true min below the fixed-extrema value, so a
complexity built on the pair-flip number would **understate** the samples needed
there. Case C goes the other way. The error is not conservative.

## Result 4 — closed boundary vs strict reversal behave as the corpus says

`c_out >= c_in` (closed) attains its minimum at a tie. `c_out >= c_in + eta`
gives a larger value that decreases toward the closed one. Measured in case A:
`0.00500000` closed, `0.00505012` at `eta = 1e-3`. The existing
`pair_flip_attained` docstring already makes this distinction for two scalars;
it survives the full-extrema problem.

One honest artefact: in case C the reported extrema labels differ between the
closed and strict runs. At a tie the argmax is ambiguous, so the label is not
well defined on the boundary. The VALUES are what the comparison rests on.

## What this does NOT establish

- `R = 2`, `K = 3`, `k = 1`, uniform weights only. Not general `R, K, k`.
- Numerical. SLSQP per region plus a penalty cross-check; no proof, no
  certified global optimality.
- The covering claim is supported by agreement on 8 problems, not proved.
- Ties in the ANSWER (several correct Top-k sets) are untouched; only ties in
  the extrema appear here.
- **Incidence on the real panel is still open.** These are constructed
  witnesses. Whether the effect occurs in worlds the generator actually draws
  (`R=5, K=6, k=2`, per-action sigma in `[.15,.85]`) is a separate measurement,
  in `scripts/f05_generator_incidence_probe_v1.py`. Existence does not imply it
  matters for the panel, and this document does not claim it does.

## What F05 should now prove

1. The alternative set is the union over `(hi, lo)` selections of the closed
   polyhedra above — a covering statement, which is the part the numerics only
   support.
2. On each region the problem is a convex QP, so the min over the alternative is
   the min of finitely many QP values.
3. The fixed-extrema value is recovered exactly as the single region that keeps
   the original extrema — which makes `pair_flip_lower` a special case rather
   than a bound, and states its scope honestly.
