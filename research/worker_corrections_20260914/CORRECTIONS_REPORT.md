# Three corrections the supervisor flagged — closed 2026-09-14

All three were real. None of them was fixed by narrowing a claim; each one changed
code or a reported number.

---

## 1. `check_symmetric_reduction` certified nothing (scripts/N7_functional_extrema_crossover.py)

**The finding.** The check was one-sided: `(Gamma_full - Gamma_sym)/Gamma_sym < 1e-5`.
Replacing the full-dimensional solver with a function that always returns `0` left
all nine cases passing. Confirmed: the stub passes.

**Root cause, exactly.** `gamma_full` initialised `best = 0.0` and only ever raised
it inside `if r.success:`. With no converged start it returned `0.0` silently, which
is indistinguishable from the stub.

**What changed.**

* `gamma_full` now **raises** `RuntimeError` when no start converges, and records
  why each start was discarded.
* It **checks feasibility of the returned allocation** — bounds and `sum w = 1` —
  rather than trusting `r.success`, and rejects a start whose reported objective is
  not the objective recomputed at the point it returned.
* The comparison is now **two-sided**. A referee that falls short of the symmetric
  optimum is not searching the simplex and so cannot testify that nothing outside
  the symmetric face does better; that now fails too.
* A **negative control**, `check_referee_rejects_stub`, swaps in the zero-returning
  stub and asserts the check now FAILS. It runs on every invocation.

**The two-sided test immediately caught a second defect, in my own referee.** J is
concave but NONSMOOTH (a minimum over ordered pairs), and minimising the nonsmooth
objective directly made SLSQP stall: at `n = 8, rho = 0.9` it fell **1.67e-2 short**
of the symmetric optimum while reporting success on 9 of 10 starts. The old
one-sided test would never have seen this. `gamma_full` was rewritten in
**epigraph form** — maximise `t` subject to `t <= f_ab(w)` for every ordered pair
plus `sum w = 1`, a smooth concave program with `(2+n)(1+n)` constraints. It now
reaches the symmetric optimum to 1.35e-14.

**The mathematics no longer rests on SLSQP.** `check_concavity_and_symmetry_averaging`
verifies the two hypotheses of the real argument, over 1200 random allocations:

  (i) J is INVARIANT under the instance's symmetry group G = (permutations of the n
      middle cells) x (swap of the two incumbent cells) x (swap of the two outsider
      endpoints) — worst deviation **0.00e+00**;
  (ii) J is CONCAVE on the simplex, being a minimum over ordered pairs of
      `A*B/(A+B)*(1-D)^2` with each harmonic half concave and `(A,B) -> AB/(A+B)`
      concave and nondecreasing — worst chord defect **0.00e+00**.

Then for any `w`, the group average `wbar` is G-invariant, i.e. of the symmetric
form `(p/2, p/2, q/2, q/2, u/n, ..., u/n)`, and by (ii) then (i)

    J(wbar) >= (1/|G|) sum_g J(g.w) = J(w),

so the supremum over the symmetric face equals the supremum over the whole simplex.
Checked directly as well: worst drop under averaging **0.00e+00**. The SLSQP referee
is now labelled in the source as a cross-check only.

Current run: gain over symmetric 1.23e-06, shortfall 1.35e-14, stub rejected `True`.

---

## 2. The crossover note misreported the error at c = 0.5, n = 4096

**Confirmed, and the supervisor's recomputation is the right one.** The note said
"already 9e-6 relative at n = 4096". Recomputed:

    n*Gamma_n = 0.0073595502     limit = 0.0073529412
    absolute residual = 6.61e-06     RELATIVE error = 8.99e-04

The line reported an ABSOLUTE residual as a relative one — and it did not even get
that right (6.61e-6, not 9e-6). Corrected in place in
`research/high_risk_20260910/N7_FUNCTIONAL_CROSSOVER_20260913.md`, with the other
columns recorded so the retraction cannot be read narrowly: c=0.5 at n=1024 is
1.76e-03; c=1.0 is 1.15e-02 (n=1024) and 5.99e-03 (n=4096); c=2.0 is 5.53e-02 and
2.94e-02.

CORRECTION TO THIS CORRECTION (supervisor caught it): an earlier version of this
line said the relative error falls "roughly like 1/n". That is wrong, and I had
the numbers in front of me when I wrote it. From n=1024 to n=4096 — a factor FOUR
in n — c=0.5 goes 1.7586e-03 -> 8.9882e-04 (ratio 1.96), c=1.0 goes 1.1529e-02 ->
5.9858e-03 (ratio 1.93), c=2.0 goes 5.5346e-02 -> 2.9360e-02 (ratio 1.89). A
factor of about 2 per factor of 4 in n is `n^(-1/2)`, NOT `1/n`. And two points
per curve cannot establish a rate at all. What the data supports is only that the
residual decreases, with a slope consistent with n^(-1/2) over the range measured.

This does not disturb the limit conjecture.

---

## 3. Both solver imports pointed outside the repo

* `scripts/R2_below_half_threshold.py:32` imported the solver from
  `/Users/phanan/Documents/ChatGPT/CIG-AMF/work/distinct_completion_20260913/`.
* `research/worker_distinct_completion_20260913/width_cost_game.py:7` pointed at
  `research/distinct_research_20260913`, which does not exist in this repo.

So the in-repo copy was unloadable and the runner depended on an outside checkout.
Both are now repointed to in-repo artifacts:

* the runner resolves `SOLVER` and `GAME` from `Path(__file__).resolve().parents[1]`;
* `width_cost_game.py` resolves the game at
  `research/worker_distinct_research_acceptance_20260913/approximate_game.py`, and
  raises `FileNotFoundError` naming the path if it is missing, instead of failing
  obscurely inside `importlib`.

**Verified end to end, not merely import-tested.** `.venv/bin/python
scripts/R2_below_half_threshold.py` runs to completion from the repo alone, exit 0,
**all 16 cells matched the threshold prediction** — below `z*(mu)` the optimum
exceeds the scalar value with a non-scalar allocation, above it the optimum equals
`mu^2/(2q)` with a scalar-only allocation.

Dependency hashes recorded in
`research/worker_distinct_completion_20260913/DEPENDENCY_HASHES.json`. Note the
in-repo `width_cost_game.py` now differs from the outside copy by the repointed
import header only; the solver body is unchanged, so the previously reported
numbers are not invalidated.

    scripts/N7_functional_extrema_crossover.py
      5eb7152975d1fdccb56218da181123ea886de076e239975f03281301dbf1c8ea
    scripts/R2_below_half_threshold.py
      8fc257d45a66967b44f9107f548e552149fdc3d4b36ec87b933eb5257d244e8b
    research/worker_distinct_completion_20260913/width_cost_game.py
      de6d8b7c74dfd39d63fd08071ea14029f5d462c7596a59bb3ec5f43407a40a16
    research/worker_distinct_research_acceptance_20260913/approximate_game.py
      8ab8e9db8abb67e1229a8a1c72f5e3e0e5d3ad0e0e699ff37562c3a19b3538d0
    research/high_risk_20260910/N7_FUNCTIONAL_CROSSOVER_20260913.md
      566b2213474832d803a79a0fe3d5e4cbf17959ae1aa51d6d48e35966d1e88a26

---

## What these corrections do NOT establish

- The symmetry reduction is now proved by concavity + group averaging, with both
  hypotheses verified numerically over 1200 allocations. That is an argument plus a
  numerical check of its hypotheses — it is **not** a Lean receipt. Formalising it
  is the second deliverable of Gói A.
- The epigraph referee agreeing with the symmetric optimum is evidence, not a
  certificate of global optimality: it is a local solver on a concave program, which
  is strong, but no dual certificate is emitted.
- Correcting the c = 0.5 figure changes nothing about whether the two limit laws
  hold. Neither has a matching lower bound.
