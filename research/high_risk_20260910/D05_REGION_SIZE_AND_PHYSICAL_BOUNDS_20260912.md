# D05: physical slope bound, and the size at which the Region is non-empty
Date: 2026-09-12. Append-only artifact. Supersedes nothing.

## 1. What is now proved (pending the axiom audit)

New module `work/p13_conjectures/LeanD6ReferencePhysicalBoundsV1.lean`:

* `bernoulli_tail_le_one` : `(1-t)^m * (1 + m*t) <= 1` on `[0,1]`, by induction on
  `m` only. No derivative, no analysis, no `native_decide`.
* `tail_quarter` : `(m*t) * ((1-t)^m)^2 <= 1/4`, from the identity
  `4*y*z^2 = (z*(1+y))^2 - z^2*(1-y)^2` with `y = m*t`, `z = (1-t)^m`.
* `slopeBval_le_quarter` : in the `2q+1` instance (`|A| = q+1`, `|others A j| = q`)
  the reference slope `b = (q-1)*t*(1-t)^(2q)` satisfies `b <= 1/4`.
* `hp_from_physical` : hence `rho >= 1` gives `rho - 2*b >= 1/2` outright.
* `physicalRegion` : a `Region` constructor taking only physical parameters.

EFFECT: the field `hp : 1/2 <= rho - 2*slopeBval t T j` is no longer an input
anywhere downstream. It was never a modelling choice.

EVIDENCE CLASS: these are Lean statements awaiting `#print axioms`. Until the
axiom audit prints `[propext, Classical.choice, Quot.sound]` for each, they are
COMPILED-PENDING, not PROVED.

## 2. What is NOT removed

The field `strong : 1 <= (q-1) * slopeBval t T j` remains an assumption. It is
not implied by anything in this module. `slopeBval <= 1/4` forces `q >= 5`
before `strong` can hold at all; that necessary condition is proved as
`strong_needs_size`. The TRUE threshold is larger and is NOT proved.

## 3. Size at which the Region is non-empty — NUMERICAL EVIDENCE

Method: `t*(1-t)^(2q)` is maximised at `t = 1/(2q+1)`; the full region was then
scanned on a 2e5-point grid in `t` on `(0,1)`, requiring simultaneously
`strong`, `c = a - b > 0`, and existence of `rho in [1,2]` with
`min(a,2b) <= (q+1)*(2a-rho)`, where `a = gateMass`, `b = slopeBval`.

| q | max (q-1)*b | region |
|---|---|---|
| 2..7 | 0.082 .. 0.914 | **EMPTY** — no admissible `t` at all |
| 8 | 1.093 | first witness: `t = 0.037818`, `a = 0.6825`, `b = 0.1429`, `rho in [1, 1.3333]` |
| 9 | 1.273 | `rho in [1, 1.5081]` |
| 10 | 1.454 | `rho in [1, 1.6037]` |
| 12 | 1.817 | `rho in [1, 1.7127]` |

CONSEQUENCE THAT MUST BE STATED WHEN CITING D05: every theorem quantified over
`Region q j T` is **VACUOUS for q <= 7**. The smallest size at which the region is
inhabited is `q = 8`, i.e. `k = q+1 = 9` retained coordinates on
`I (2q+1) = Fin (2q+2) = 18` coordinates. A size scan does NOT decide
publishability; this is a statement about the region only.

EVIDENCE CLASS: NUMERICAL EVIDENCE (floating-point grid scan). The emptiness for
`q <= 7` is evidence, not a theorem. Do not write "holds for all q", and do not
write "the region is non-empty" without the size qualifier.

## 4. Not addressed here

* `(k-2)*b >= 1` is still carried as `strong`; only its `q >= 5` consequence is proved.
* No claim is made that the algebraic threshold is the actual minimax threshold.
