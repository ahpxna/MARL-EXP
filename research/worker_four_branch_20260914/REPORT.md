# Four-branch batch: Structural, Support, MASTER, D6. All four touched.

Three new modules, **15 clean audits, 0 nonstandard, 0 failures**; every receipt
`lean_exit=0`, source hash unchanged, `.olean` strictly newer.

    LeanStructuralSortedPrefixV1      9 audits   the quantifier upgrade
    LeanMasterAnchorCertificateV1     4 audits   anchor profile + dual certificate
    LeanSupportMinimaxCountingV1      2 audits   the active-law count

## 1. Structural — the quantifier is closed. PROVED.

`work/p13_conjectures/LeanStructuralSortedPrefixV1.lean`, **9 audits, 0
nonstandard, accepted**.

`excess_le_two_thirds` took `hmass : modularSpan T f ≤ modularSpan S f` as a
hypothesis, supplied per budget, so on its own it gave `∀k ∃π_k`. The new module
gives

    ∃ ONE nested chain S_0 ⊆ S_1 ⊆ ... , ∀k ∀T, |T| = k →
        supportOsc (S k)ᶜ f ≤ supportOsc Tᶜ f + (2/3) modularSpan univ f

with **no `hmass` anywhere**. `one_prefix_chain`.

**Not by sorting.** The chain is built by repeatedly deleting a minimum-span
element from `univ`. The content is `spanMaximal_erase`: if `S` is span-maximal
among sets of its cardinality and `x` has minimal span in `S`, then `S.erase x`
is span-maximal among sets one smaller. Exchange step — for a competitor `T` one
smaller, `S \ T` is non-empty (cardinality), so pick `z` there; `T ∪ {z}` has the
full cardinality, hence `mass T + span z ≤ mass S`, and `span z ≥ span x` because
`x` was minimal, so `mass T ≤ mass S − span x = mass (S.erase x)`. Induction from
`univ` gives `chain_card`, `chain_subset`, `chain_maximal`; reindexing by
`k = card − j` feeds the maximality straight into `excess_le_two_thirds`.

**Not established.** The constant is `2/3`, inherited unchanged; with the previous
batch's exact signed witness at `1/2`, what is open is the constant in
`[1/2, 2/3]`. The statement is unnormalised (dividing by `modularSpan univ f`
needs it non-zero, not assumed). The chain uses `Finset.exists_min_image`, so it
is classical and no complexity claim is made. This says nothing about the
fractional-execution question, where the obstruction is preserving a given path's
marginals, not finding a good ranking.

## 2. Support — all three claims verified exactly; the counting core partly formalised.

`scripts/U1_support_minimax_check.py`, exact `Fraction` throughout.

* **U2 posterior.** With a uniform prior over `b`-subsets and seen-tip set `S`,
  `Pr(j ∈ W | data) = (b−s)/(m−s)` for every unseen `j`, and a seen tip is
  certainly unsafe. Verified for **every** `S` and `j` at `(m,b) = (5,2), (6,3),
  (7,3), (7,4)`.
* **U3 passive.** The uniform-unseen policy's risk equals `E[L_N/(a+L_N)]`
  **exactly**: `127/640` at `(5,2,p=1/4,N=3)`, `11/36` at `(6,3,1/6,4)`,
  `7541/28672` at `(7,3,1/8,5)`. Computed two independent ways — by transcript
  enumeration with inclusion–exclusion, and from the occupancy law — and they
  agree as rationals.
* **U5 active.** `C(b,k+1)/C(a+b,k+1)` is **the Bayes optimum over ALL
  deterministic adaptive query trees of depth `k`** — enumerated by memoised
  recursion over (asked set, answers), not assumed. Confirmed in 11 cells:
  `2/5, 1/10, 0` at `(5,2)`; `1/2, 1/5, 1/20, 0` at `(6,3)`; `3/7, 1/7, 1/35, 0`
  at `(7,3)`.

Lean: `LeanSupportMinimaxCountingV1` (**2 audits, 0 nonstandard, accepted**) carries the count behind the randomised
upper bound of the active law (`active_error_card`, `active_total_card`): the
all-unsafe draws are exactly the `(k+1)`-subsets of `W`.

**Not established.** No probability space appears in the Lean file — these are
cardinalities, and reading them as a posterior or an error probability is the
step the wrapper must make. `R_N^* = E[L_N/(a+L_N)]` is NOT proved: the occupancy
law, the Bayes lower bound and the policy's risk are all outside it, exactly as
`LeanSupportPassiveAnswerMultiplicityV1` says about itself. The posterior
counting identity is verified on every `S, j` for `m ≤ 7` but is NOT formalised —
the bijection `W ↦ W \ S` plus the `choose` absorption identity did not match the
spellings this Mathlib ships, and it is recorded as open rather than left as a
broken proof. Equal tip masses are assumed; with unequal masses the posterior is
not uniform and none of it transfers.

## 3. MASTER — the anchor profile and a certificate that proves its own soundness.

`work/p13_conjectures/LeanMasterAnchorCertificateV1.lean`, **4 audits, 0
nonstandard, accepted**.

* `anchor_profile` — with the physical anchor `Y0 = b + N(0,sig0)` at exposure
  `x0`, profiling the unknown common offset gives
  `D_u − M_u²/(2(K + x0/sig0))`, attained at `t = M_u/(K + x0/sig0)`. **The anchor
  enters only by adding `x0/sig0` to the curvature** — which is precisely why a
  threshold in `c0` can exist at all.
* `dual_bound` — for ANY prior `lam` on alternatives and ANY shifts `z_u`, every
  budget-feasible `(w, x0)` obeys
  `min_u I_u(w,x0) ≤ max{ max_e H_e/c_e , H_0/c_0 }`. Two steps, no optimisation:
  the infimum is at most the `lam`-average, each averaged term is at most its
  value at the chosen shift, and the budget turns a linear functional into that
  maximum. **This is `sound` proved rather than assumed**: the bound holds
  whatever produced `lam` and `z`, so a solver's output is only a candidate and
  this theorem is what makes it a certificate.
* `no_anchor_needed` — if a certificate already caps the anchor-free value at
  `V0` and `c0 V0 ≥ H_0`, buying exposure cannot help at that price.

**Not established, and this is the half that is missing.** The CONVERSE is not
proved: `c0 V0 < H_0` only makes this certificate unusable, it does not show the
anchor must be bought. That needs an explicit allocation with `x0 > 0` of value
`> V0` plus a matching dual. Both sides of the threshold were the target; one
side is delivered. `D_u, M_u, K` are taken as given reals, not derived from the
compensated world's actual query means, so the link to the real instrument is an
interface, not a theorem. No algorithm, transcript, stopping rule or running cost.

## 4. D6 — the blind phase boundary, in closed form, confirmed out of sample.

`scripts/D3_blind_phase_boundary.py`.

With `m = 2q+1`, `K_q = q(q²+1)/(2(2q+1))`, `B_q = (q+1)/(2(2q+1))`,
`c_q = B_q/K_q = (q+1)/(q(q²+1))`, the joint-only branch is optimal until
`z = mu/(1−mu)` solves the QUADRATIC

    z² + c_q z + (q/2) c_q²  =  ((q+1)/2)(1 − c_q/2).

So the boundary is a closed-form root, not a bisection. Solved exactly and then
handed to the SAME blind LP as `D1` — which never sees the prediction:

    q=3   c_q = 2/15    mu* = 0.563593    scalar absent below, present above   CONFIRMED
    q=4   c_q = 5/68    mu* = 0.601909    CONFIRMED
    q=5   c_q = 3/65    mu* = 0.627903    CONFIRMED

at three distances each (0.05, 0.02, 0.005). `q=5` is **out of sample**: the
earlier sweep covered only `q=3,4`, and the earlier sweep's own support-change
intervals — `(0.55, 0.60)` at `q=3` and `(0.60, 0.625)` at `q=4` — both contain
the predicted root.

`zeta_blind` is CONSTANT TO SOLVER TOLERANCE below `mu*` (`0.380969`, `0.377338`, `0.388113`
for `q = 3,4,5`) and falls immediately above. CORRECTED WORDING: a float LP on a
grid cannot show a ratio is EXACTLY constant on an interval; what the data
supports is that every measured point below `mu*` agrees to within the solver's
tolerance, and that the first point above it does not. Note the value is not
monotone in `q`.

**Not established.** The two-curve reduction itself — that the ordinary scalar
and the width-`q` off-query dominate every other class after group averaging — is
the HYPOTHESIS this boundary is derived from. The agreement above is evidence for
it, not a proof, and "the solver only found two classes" is not an argument. `eps
= 0`, `shell = 0`, float LP with gap below 2e-8. Nothing here is `L_zeta`, the
information lower bound, or any algorithm.

---

## Three readings corrected, as flagged

1. The Functional report said `n Gamma_n = ...`; the script computes the value
   **at the proposed allocation**. It is `n J(w_candidate)` until a matching upper
   bound over every allocation exists. The heterogeneous upper bound is proved
   only for `Splus` (the `H_n^+` side), so the two ends are still different
   quantities.
2. `V_blind < Gamma` rules out one fixed allocation being oracle-optimal
   simultaneously in every world. It does **not** prove a separately-payable
   discovery cost: deployment itself supplies information.
3. `d05_phase_closure_manifest_20260912.json` records the MOST RECENT call only.
   `all_accepted=true` there is not a statement about the corpus.
