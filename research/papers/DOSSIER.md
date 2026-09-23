# Writing dossier — everything needed to draft the three final papers

Companion files: **`PROOFS.md`** (the central arguments in readable mathematics, no Lean
required), **`CLAIMS.md`** (claim → theorem → remaining hypotheses → evidence, one row
per headline) and **`ROADMAP.md`** (every named deliverable with a status: LEAN /
LEAN-COND / NUM / OPEN, and exactly what remains). This file is the superset: state of the corpus, exact statements, every
measured number with its provenance, the open list, and what was retracted.

---

## 0. Corpus state

```
modules = 29      audited_theorems = 562      failed = 0
sorry = 0         native_decide = 0
axioms  ⊆ {propext, Classical.choice, Quot.sound}
VERIFY PASS
```

Reproduce with `work/p13_conjectures/verify_all.sh`. Acceptance is deliberately stricter
than "no errors": **`sorryAx` is counted separately**, because an error anywhere in a module
makes Lean insert `sorryAx` into that module's downstream theorems, so a clean error count
alone does not establish the theorems are proved. The script also checks no source is newer
than its own log, so a stale `.olean` cannot masquerade as a verified result.

| Module | Thms | Subject |
|---|---|---|
| `LeanPaperClosuresV1` | 5 | closure lemmas |
| `LeanPaperAAlternativesV1` / `…UnionV1` | 7 / 8 | alternative sets |
| `LeanPaperAModelBridgeV1` | 18 | centred response, Gaussian KL = squared gap |
| `LeanPaperAOracleCertificateV1` | 5 | oracle certificates |
| `LeanPaperARepairV1` | 9 | repair criterion |
| `LeanPaperASeparationV1` | 85 | separation after allocation, 8-cell model |
| `LeanPaperARPairV1` | 23 | r-pair family, pigeonhole, four-square |
| `LeanPaperARGamesV1` | 12 | the two games as `⨆_w ⨅_λ`; `theta0_centered` |
| `LeanPaperAHomogV1` | 5 | homogeneity ⟹ leakage bound |
| `LeanPaperAFrozenV1` | 10 | the **actual** frozen-linear surrogate's game |
| `LeanPaperA7OracleSelectV1` | 14 | answer selection |
| `LeanPaperA7TrackingV1` | 9 | tracking |
| `LeanPaperA7ConfidenceV1` | 14 | Ville, finite horizon |
| `LeanPaperA7StreamV1` | 35 | Gaussian-prior mixture = the code's `Q_t` |
| `LeanPaperA7TailV1` | 33 | window accumulation → tail → limsup |
| `LeanPaperA7EtaV1` | 7 | rate at `Γ−η`; certificate vs algorithm |
| `LeanPaperA2ChainV1` | 7 | cumulative-exploration law |
| `LeanPaperBAttainmentV1` | 5 | attainment, exact constant |
| `LeanPaperBHellingerV1` | 3 | Hellinger from moment contrast |
| `LeanPaperBTranscriptKLV1` | 4 | chain rule, **finite alphabet** |
| `LeanPaperBRatesV1` | 75 | envelope chain; `log(1/δ)` side |
| `LeanPaperBGeometryV1` | 11 | safe order 1 vs identification order `m−1` |
| `LeanPaperBTestV1` | 11 | LRT error derived, per world; decoder total |
| `LeanPaperBCrossoverV1` | 8 | crossover parity cancellation |
| `LeanPaperCFrontierV1` | 9 | frontier |
| `LeanPaperCRankingV1` | 67 | (O1) at every `m`, both parities |
| `LeanPaperCBreakpointV1` | 54 | (O2) both parities; `hsec`'s three steps |
| `LeanPaperCFinalV1` | 9 | `hsec` discharged at the actual graph; strict gap |

---

## 1. Paper A — information needed for a decision, not for a prediction

**One sentence.** A frozen-linear surrogate cannot approximate the information complexity of
compression: the separation is `Θ((rM)^{-1})`, it survives after the allocation has been
optimised, and it exists at *uniform* variance — so it is not a conditioning artefact but a
consequence of how many alternatives the surrogate declines to look at.

**Do not** headline "we use Sticky Track-and-Stop", "we use martingales", or "we formalised
N theorems". **Nor "adaptive beats uniform"**: that is neither new nor what the panel
establishes.

**Where the contribution has to sit**, as a chain, and each link is load-bearing:

> real compression → real alternative geometry → the optimal *proxy* is still seriously
> wrong → the cost of learning changes → an algorithm attains the *correct* benchmark.

Three results carry it, and the paper should be ordered by them:

1. **Separation after the allocation is optimised**, on one class of worlds under one
   observation law: `Γ_true/Γ_frozen = Θ((rM)^{-1})`. The case `M=1, r→∞` matters most —
   it shows the failure is not bought by inflating a variance.
2. **The consequence for the design or learner the proxy selects.** Two different game
   values do *not* by themselves show the proxy policy needs more samples. What has to be
   proved is that starving the cells that matter destroys information about the *true*
   compression — the starvation lemmas, and then a sequential-cost separation.
3. **Attainability of the true benchmark**, with confidence, selection, tracking and
   stopping all inside one model. The machinery may be inherited; the contribution is that
   it reaches the complexity the new geometry defines.

Main theorems: (1) and (2). The learner panel is **Results**, with the scope stated in the
table below — it is evidence for the implementation side of (3) and for nothing else.

### Central results

**A-i. The two games, defined and bracketed.** At the concrete centred world `θ₀`,

$$\Gamma_{\rm true}=\sup_{w\ \rm alloc}\ \inf_{\lambda:\,\mathrm{range}_A\lambda<\mathrm{range}_B\lambda}\mathcal E(w,\lambda),
\qquad
\Gamma_{\rm frozen}=\sup_{w}\ \inf_{\lambda\in\Lambda_{\rm frozen}}\mathcal E(w,\lambda),$$

with `Λ_frozen = {λ : (λ₁−λ₀) − (λ₂−λ₃) ≤ 0}` the surrogate's own single linear contrast.
Proved: `Γ_true ≤ 1/(8Mr)`, `Γ_true ≥ 1/(128(4+2rM))`, `1/32 ≤ Γ_frozen ≤ 1`, hence

$$\frac{1}{128(4+2rM)}\;\le\;\frac{\Gamma_{\rm true}}{\Gamma_{\rm frozen}}\;\le\;\frac{16}{Mr}.$$

No value is assumed. The two constants are not matched — report an order, never a constant.

**A-ii. The sets are provably different.** `proxyAlt_ne_frozenAlt`: arm `A` at `(0,1)`, arm
`B`'s frozen maximum at `−2`, middles `0` has true `B`-range `2>1` but frozen contrast
`3>0`. We prove the *values* agree in order; we never assume the sets agree.

**A-iii. Every proxy optimum starves the pairs**, and by homogeneity an `ε`-optimal design
leaks at most `ε/(Γ_proxy−ε)` off the anchors. This is the bridge from static starvation to
a policy's exploration cost.

**A-iv. Cumulative-exploration law.** `N_mov(t) ≤ C_r + 2√t + ε̄t`; Jensen inverts at
`a = 1/2` (giving `Ω(log²(1/α))`) while `ε̄t ≤ 2√t`, i.e. `t ≤ (2/ε̄)²`.

**A-v. Rate at `Γ−η`,** with the threshold's extra terms carried inside an arbitrary budget
`b`, and `1/(Γ−η) → 1/Γ`.

### Measured numbers

| Quantity | Value | Artifact |
|---|---|---|
| `Γ_comp` | `2.3256e-2` | `paperA7_learner.json` |
| Oracle bracket, as shipped | `8.0377e-3` | timing probe |
| … + running-min upper bracket | `8.0377e-3` | timing probe |
| … + damped cutting-plane step | `1.9022e-4` | timing probe |
| … + regional dual to tolerance | **`5.043e-7`** | timing probe |
| Repair witness at `M=256` | `0.402%` of floored proxy optimum, `4.15%` of bracketed true optimum | `paperA_repair_barrier.json` |
| `(64/M)·Γ_proxy/Γ_true` at `M=1,4,16,64,256` | `66.2, 18.4, 6.43, 3.42, 2.58` — **vacuous at every `M`** | same |
| Mean queries, corrected policy, **common random numbers**, 12 runs/cell | see the per-`α` table below | `paperA7_learner.json` |
| Learner slope in `log(1/α)` | `49.6 ± 12.8` against a drift-corrected prediction of `47.9` | `paperA7_alpha_slope.json` |

**The panel, per `α`.** `M=16`, one world, 12 runs per cell, all 144 runs correct, none
censored. `α` enters the algorithm only at the stopping test, so the seed is free of `α` and
the four levels share one path; `τ` is monotone in `α` on all 36 paths, checked.

| `α` | learner | oracle (diagnostic) | uniform | `t` | `p` (Holm) |
|---|---|---|---|---|---|
| 0.10 | 1316.7 ± 88.6 | 1104.2 ± 72.9 | 1620.8 ± 92.4 | 2.38 | 0.079 |
| 0.05 | 1366.7 ± 86.9 | 1183.3 ± 89.9 | 1650.0 ± 91.5 | 2.25 | 0.079 |
| 0.02 | 1416.7 ± 102.7 | 1212.5 ± 93.0 | 1725.0 ± 78.0 | 2.39 | 0.079 |
| 0.01 | 1429.2 ± 102.3 | 1283.3 ± 84.0 | 1762.5 ± 82.1 | 2.54 | 0.076 |

**Three things to state plainly.**
*The learner is below uniform at every `α` by 19–23%, and no cell is significant after the
Holm correction* at `n=12`. Report it that way, not pooled. An earlier independently-seeded
panel put one cell at `t=4.67`; under common random numbers that vanished, which is what an
unlucky draw looks like.
*The slope is a heuristic diagnostic; the levels are not testable at all.* The threshold
carries a penalty of `19.6`–`19.8` against `log(1/α) ≤ 4.61`, so no level compares with
`log(1/α)/Γ`. Differencing along `α` cancels the penalty's constant part, and its measured
drift of `+0.113` per unit is removed too: `49.6 ± 12.8` against `47.9`. **But differencing
does not remove the threshold overshoot `O_α` nor the finite-time information residual
`R_τ`** — `Γ·Eτ = log(1/α) + E b_τ + E O_α − E R_τ` — and neither is bounded anywhere in
this corpus. Either can move the slope in either direction. So this is consistent with the
rate theorem and establishes nothing on its own; it is **not** an upper bound on `1/Γ`.
*The oracle arm is a diagnostic and not a lower bound on stopping time.* It maximises the
asymptotic information rate; at finite `α` a learner can stop earlier on a path with nothing
wrong.
*Repair is undetermined, not negative.* In true units the certificate ceiling is vacuous at
every `M` tested, and at `M=256` none of the 43 sampled designs is certified, so
`Γ_cert = sup_{Cert(w)} J_true(w)` is not estimated at all.

### Numerical repairs that changed a reported number

Two faults in `EXP_paperB_uniform_hellinger.py`, both of which moved a headline figure.

1. **`H²` was formed as `1 − affinity`.** The quantity is of order `h^{2r}` — about `1e-8`
   at `r=3, h=0.05` — while the affinity sits within `1e-8` of one, so the subtraction
   discards roughly half the double-precision mantissa *before* quadrature error counts. It
   is now `½∫(p−q)²/(√p+√q)²`, which has no cancellation.
2. **The "canonical" seed was not the canonical probe.** It was a flat vector over every
   coefficient, spreading the same mass over the head coordinates `z₁,z₂,z₃`. The
   construction's attaining probe is the tail average `(1/r)Σ_{ℓ≥4} z_ℓ` alone. It is now
   recovered from the basis by least squares, with the residual checked (`6.1e-16`) and
   written to the artifact as `canonical_tail_seed_residual`.

**Effect.** The fitted identification order at `r=3` moves from `8.13` to **`5.80`** against
the claimed `2r = 6`; `r=2` is unchanged at `3.79` against `4`. The earlier `8.13` was an
implementation artefact and must not be cited. **This is better evidence, not a proof:** the
ascent still fails to improve on its best seed at every `h`, so the value remains a *lower*
bound on the supremum over the query class.

### Methodology repairs, second round — each changed what a number means

1. **`find_N` selected on noise.** It returned the first ladder point whose *observed* error
   cleared the target. A point chosen for having a low observed error has a low observed
   error partly because it was chosen — the winner's curse. The ladder is now a **pilot**;
   the candidate is re-run on independent repetitions, and what must clear the target is the
   **worst world's Clopper–Pearson upper bound**. A candidate that fails is counted and the
   search continues. Measured effect: at `r=2, h=0.4` the decision budget moves from
   `N* = 94` (which does not confirm) to `N* = 170` — a factor of `1.8`.
2. **Error was pooled over a random truth.** The truth was drawn uniformly and the mistakes
   summed, which estimates the *average* error under a uniform prior — not a worst-case
   guarantee, and not something a minimax statement may be built from. Both worlds are now
   run with the same repetitions and reported **separately**, with the worst as the
   headline and the pooled average kept as a separate field.
3. **Cells with few repetitions were reported by their rate alone.** The moment panel has
   68 cells with 16–240 repetitions, seven of them at 16. A cell observing `0/16` has an
   observed rate of zero and a binomial upper bound near `0.17`; the worst bound across the
   panel is **`0.910`**. Every cell now carries its repetition count *and* its upper bound.
4. **The separation figure could be misread as the centred theorem.** Its artifact is the
   `r`-pair/frozen-proxy family, whose surrogate constant is `Γ_proxy = 1/512`; the centred
   construction's is `Γ_frozen = 9/512`. The figure is kept as the *other* family and its
   caption now says so explicitly. The two are not relabelled into each other.

### Retracted this session — say so, do not silently edit

1. **"A positive bracket gap forces the learner to be slower."** False. A bracket of width
   `ε` gives `0 ≤ Γ−J(w) ≤ ε`, not `≥ ε`. Only the *certifiable* bound degrades.
2. **"The 8.0e-3 plateau is the duality gap, hence structural."** False. It was the cutting
   plane's oscillation plus a loose dual tolerance; three method changes took it to
   `5.043e-7`.
3. **"Flatness in both axes identifies the residual as round-off."** Over-claimed. Flatness
   rules out the iteration budget and the dual solve; a weight floor and a subtracted
   correction remain candidates and no check separates them.
4. **"`Λ_proxy` is the frozen surrogate's set by inspection."** False, with the explicit
   counterexample above.
5. **"The oracle arm is an unattainable lower envelope on stopping time."** False, and it
   was in the script's own docstring. The oracle allocation maximises the *asymptotic
   information rate*; that is not a lower bound on the stopping time at any finite `α`. A
   learner that stops before the oracle on a path is therefore not evidence of a bug, and
   the wording is removed from `EXP_paperA7_learner.py` rather than left standing.
6. **"The threshold penalty explains why `τ` is non-monotone in `α`."** Wrong inference.
   `α` reaches `run` at exactly one place, the threshold inside `stop_certificate`;
   selection, allocation and tracking never see it. The panel drew a fresh segment of one
   stream for each `(α, arm, run)` cell, so the four `α` sat on **independent paths** and
   the reversals are between-run variation. What the penalty (`18.5`–`19.7` against
   `log(1/α) ≤ 4.61`) does explain is why the `α` signal is small next to that variation —
   i.e. why the panel cannot resolve the rate — not why the means reverse. The panel now
   runs under **common random numbers** (`seed = [BASE_SEED, arm, run]`, free of `α`) and a
   self-check asserts pathwise monotonicity in `α` and that the larger-`α` selection trace
   is a prefix of the smallest-`α` one.
7. **"`5.043e-7` shows the oracle bracket error goes to zero."** Not established by this
   implementation. `4/255` refreshes finished above their requested tolerance, the schedule
   is floored at `1e-6`, and the iteration budget is capped at `80`. The stopping rule is
   unaffected — it uses the weak-duality lower bound from `regional_lower_bound`, never a
   bracket — so a loose refresh cannot make a stop unsound; but `ε_t → 0`, which the A2
   accumulation step needs, cannot be read off this run. `all_passed = True` does not cover
   that conclusion.

---

## 2. Paper B — the query class decides the exponent

**One sentence.** On one world and one observation model, deciding safely and identifying
the world have different sample-complexity exponents, and which exponent you get is decided
by the query class.

**Billing.** The `h^{-2r}` law and the `h⁶ + η²h⁴` crossover are **supporting results**, not
the headline: the phenomenon behind them (low moments carrying nothing, signal at high
order, a coupling lowering the protective order) is established in the masking and
side-channel literature. The kept question is whether safe-answer *geometry* sets the
exponent.

### Central results

**B-i. Per-pair test bound, derived.** The LRT is exhibited; its error is computed exactly
as `½Σ_t min(P,Q)`; affinity tensorises; hence each world's own error is `≤ δ/K` once
`N ≥ log(K/δ)/H²`, and `≤ δ` in total over `K` pairs. With `H² ≥ c₀h^{2r}` the size is
`O(h^{−2r}log(K/δ))` — the same `h`-exponent as the lower bound. The `δ`-dependence matches
only up to a constant.

**B-ii. The two orders.** `s_safe = 1`, `s_id = m−1` (the latter as an `iff`), on the real
`selectedRadius` geometry; safe sets overlap pairwise but have empty total intersection; the
order-0 class is an obstruction, which is the hypothesis the `log(1/δ)` lower bound consumes.

**B-iii. Crossover mechanism.** Three exact moments; the cross term vanishes by parity
(`A` odd, `B` even, `p₀` even); the quadratic form splits into `η²h⁴ + h⁶`.

**B-iv. Refutation.** The degree-≤(r−1) class does **not** support the `2r` law: `g =
(z₄z₅+z₆)/2` at `r=3` has `E[χg²] = ½`.

### Measured numbers

| Quantity | Value | Note |
|---|---|---|
| Identify order, linear class | `3.79` (`r=2`), `5.80` (`r=3`) | claimed `2r = 4, 6` |
| Decide order | `1.91` | claimed `2` |
| Out-of-sample ratio, coarse-fitted `C_r` | `1.089` (`r=2`), `0.126` (`r=3`) | **upper-envelope test only** |
| Search-limited `h` values | `0/6` (`r=2`), **`4/6` (`r=3`)** | ascent never beat its best seed |
| Degree-capped refutation order | `3.937` | `< 6`, so the law fails there |
| Crossover orders, `η = 0 → 1.6` | `5.93, 5.63, 5.14, 4.50, 4.11, 3.98, 3.95` | monotone |
| Normalised cross term | `6.60e-15` | on the model's own baseline `p₀ = ½[f(y−1)+f(y+1)]` |

**Read the `r=3` order correctly.** Two thirds of its `h` values are search-limited — 39
starts, all converged, canonical probe `(z₄+z₅+z₆)/3` seeded, and the ascent still never
improves on its best seed. So `5.80` is **not** evidence for an `h⁶` optimum law. A ratio
of `0.126` means the measured order *exceeds* `2r`, so the upper envelope holds with room;
it is not a two-sided approximation and must not be reported as one.

### Retracted this session

1. **"within a factor of two"** for the out-of-sample check — it tested only the upper side.
2. **`p₀ = f`** in the crossover parity block — the baseline must be the mixture over the
   `z₁` channel, `½[f(y−1)+f(y+1)]`. Parity still gives `6.6e-15`, but on the right density.
3. **`7.12` and `C₃ = 6.85e-2`** in the manuscript — numbers from the refuted degree-capped
   run, now `5.80` and `8.2961e-4` on the linear class.

---

## 3. Paper C — the exact price of marginal constraints

**One sentence.** The exact parity-dependent breakpoint of the price of marginal constraints
on signed-prefix compression, with a computable optimal reduction from `m!` rankings to
`O(m²)` flow variables.

$$V_m(\eta)=V_{\rm free}\iff \eta\ge\eta_*(m)=\begin{cases}1,&m\text{ odd}\\[2pt]\dfrac{m-2}{2(m-1)},&m\text{ even.}\end{cases}$$

### Central results

**C-i. `hsec` discharged** at the actual count-state graph — the section is built, not
assumed, so the flow-to-ranking reduction is a reduction. Full proof in `PROOFS.md §C1`.

**C-ii. (O1)** — the constrained value *reaches* the free value at `η_*(m)` — at every `m`,
both parities, by an explicit insertion mixture.

**C-iii. (O2)** — it strictly exceeds below — at every `m`, both parities, **no window**,
with a margin uniform over the band-feasible set. *Conditional on* the per-ranking counting
inequality and the band bound, which are hypotheses.

**C-iv. Stability** with the normaliser moving, and a robustness floor
`V_unif/V_free ≥ 1/(4ε + 4/(m−1))` for `‖u‖₁ ≤ ε ≤ ¼`.

### Measured numbers

| Quantity | Value |
|---|---|
| Permutation LP vs flow LP, 12 configurations | max discrepancy `1.67e-16` |
| Perturbation cases | 160 grouped + 60 per-item |
| Adversarial family, `m=7` | keeps **`43.47%`** of the price at `ε=0.8`, **`30.05%`** at `ε=1.6` |
| Structured families (shrink-anchors, uniform-shift) | never lose half at any `ε ≤ 1.6`; uniform shift at `m=6` *raises* the price to `2.5×` |
| Rows inside the floor's proved domain (`ε ≤ ¼`, odd `m`) | `8` of `21` |

**Retracted this session.** "No family loses half the price at any `ε ≤ 1.6`" — false, it
read only the two structured families. And the floor was labelled on `9/21` rows outside its
proved domain (`ε > ¼`) and on `7` even-`m` rows where the substituted values are the odd-`m`
ones; those now carry `floor_in_domain: false` and are excluded from the assertion.

**Also corrected.** `breakpoint_strict_below` originally quantified over the whole simplex,
where the hypothesis is *unsatisfiable* whenever `V_free` is the attained free optimum — so
it was vacuous exactly where it was wanted. It is now on a closed band-feasible subset, with
a satisfiability witness.

**Language to fix.** `ρ = p − q` is an integer, so "open region in `(a,ρ)`" has no content
without a stated topology; and letting `a` range while keeping blocks of equal weights is
still a symmetric family, so it does not answer arbitrary perturbation in `ℝ^m`.

---

## 4. Provenance

`scripts/AUDIT_provenance.py` resolves each artifact to its producing script and compares
the recorded `source_sha256` against the file on disk.

```
34 artifacts: 28 current, 2 stale, 0 without a hash, 4 superseded, 0 unresolvable
```

Artifacts predating the hash convention are reported `NO-HASH` rather than silently
accepted; there are now none.

**Three generations of the learner panel exist and none may be mixed with another.**
(1) *Pre-damping*: a different allocation policy — before the running-min bracket, the
damped step, the dual tolerance, the witness-feasibility check and the selection slack.
(2) *Corrected policy, independent seeds*: the right policy, but each `(α, arm, run)` cell
drew a fresh segment of one stream, so the four `α` sat on independent paths; its cell means
were not even monotone in `α`, and one cell's significance did not survive coupling.
(3) *Corrected policy, common random numbers* — the current artifact: seed
`[BASE_SEED, arm, run]`, free of `α`. Each generation **replaces** the last; none is
averaged with another, and a smoke run never substitutes for the full comparison. The
current artifact's `source_sha256` matches `EXP_paperA7_learner.py` on disk, and
`paperA7_alpha_slope.json` records that file's hash as its dependency.

---

## 4b. Where each paper actually stands — supervisor audit, 2026-09-21

Recorded verbatim in substance, because it is the standard the drafts will be held to, and
because two of its three verdicts are less favourable than the corpus's own summaries.

| Paper | Real progress | Missing for the current headline | Verdict |
|---|---|---|---|
| **A** | alternative regions; model bridge; the centred construction; the frozen game exactly; starvation; a learner that runs | join the construction and the **whole alternative class** to the observation model; the true game on the *same* construction; the chain learner → confidence → information → expected stopping | **not merely "left to write"** |
| **B** | moment vanishing; Gaussian envelope; safe-set geometry; testing on a finite alphabet; the crossover mechanism | geometry and observation order still live in **two constructions that are not joined**; continuous/randomised transcript; upper bound and decoder on one observation model | **central research obligation remains** |
| **C** | construction attains the breakpoint at every size; flow → ranking for real; the counting inequality; stability | join the real band constraints to the lower side; complete the flow ⇄ ranking equivalence; fix the robustness reading | **closest to done** |

**A1/A2 — both games on one model, and the separation closed on both sides.** Done this
session. Both infima are restricted to the same `Θ₀` (`frozenValueC₀`, `trueValueC₀`), and
the direction is stated where it matters: restricting an infimum **raises** it, so the
unrestricted bounds do not transfer for free — they transfer because the witnesses
`lamStar` and `pairShift` are themselves centred. The true game is proved **on `thetaC`
itself** on both sides, so nothing pairs an old construction's bound with the new
`Γ_frozen = 9/512`:

> `Γ_frozen = 9/512` exactly, `9/(128(4+2rM)) ≤ Γ_true ≤ 1/(8Mr)`, hence
> **`4/(4+2rM) ≤ Γ_true/Γ_frozen ≤ 64/(9rM)`** — `centred_separation`.

The lower bound uses the variance-proportional design `w_e = σ_e²/(4+2rM)`, at which the
energy is the plain squared distance; reversing the decision forces a contrast of `3/4`
across four cells, and Cauchy–Schwarz gives `9/64`. The same `g = 3/4` sets
`Γ_frozen = g²/32`, so one number drives both sides. Strict alternatives inside `Θ₀` are
exhibited (`pairShiftC_strict_alt`), so the closed set is not carrying the argument.

**Still owed on A1**, and it is an *instantiation*, not new mathematics: the response map
`F_λ(a,b) = λ_A(a)+λ_B(b)` with its marginals, and `energy = ` Gaussian KL for every
`λ ∈ Θ₀` rather than at the witness. The general forms are already proved —
`loss_eq_half_range` ("the loss is half the range of a linear form"), `residual_eq_inner`,
`selectedRadius_eq_compressionLoss` in `LeanPaperAModelBridgeV1` — what is missing is
choosing `q`, `φ`, `K`, `T` so they land on this construction.

**A2 — the sample-cost claim needs the policy link, or must be dropped.** Static starvation
is not `Ω(log²(1/α))`. What is needed is, on the actual policy,
`E N_middle(τ) ≤ C_r + C'_r·E√τ + E∑_{t<τ} ε_t`, then the transportation lower bound.
**And the `ε_t` in that bound is the error of the *surrogate* oracle — not the true oracle's
bracket gap measured in the A7 panel.** Those are different quantities and the corpus has
so far measured only the second. Until this is closed, Paper A may claim a separation of the
*information game* and of the *design*, and may **not** claim a separation of sample cost.

**A3 — A7 is not joined end to end.** `rate_limsup_eta` still takes the expected stopping
bound as a hypothesis, and the window lemmas still take an accumulation condition not
discharged from the learner. Two joins remain: the code's continuous Gaussian mixture →
supermartingale and coverage (the finite-mixture supermartingale and the Gaussian integral
exist; the transfer through the continuous prior does not); and selection + tracking +
oracle → `Z_t/t ≥ Γ − error` → `Pr(τ>t)` → `Eτ`. The implementation has a tolerance floor,
so an exact-`1/Γ` theorem must be stated apart from the finite-arithmetic guarantee.

**B — three joins, not formalisation.** (1) One family only, with `F_θ`, support, loss and
observation law, from which safe sets *and* observation-order classes are derived —
`IndistAt` is currently defined on the **world index**, and `EXP_paperB_obstruction_law.py`
uses four `(u,v)` worlds whose safe sets are equal within `u` and disjoint across it, which
is *not* the intersecting family the geometry theorem is about. (2) The per-query bound
carried to a **continuous transcript with a randomised policy** — `LeanPaperBTranscriptKLV1`
states finite alphabet, deterministic policy, fixed horizon. (3) A decoder built on the same
Gaussian model with the **sample budget accounted** — `decoder_total_error` adds per-test
errors and does not build the decoder or share the data law. The target is *one* theorem
about a safe decision, not three adjacent ones about geometry, moments and testing.

**C — one mathematical join and a scope fix.** Derive `hband` from the marginal constraints
of the real ranking distribution (**partly done this session**: `LeanPaperCBandV1` derives it
from the per-item band and exhibits its satisfiability), substitute the concrete quantities
into (O2), and move from expectation-over-budget to max and infimum; then O1 + monotonicity
gives `V_m(η) = V_m^free ⟺ η ≥ η_*(m)` on the stated parameter range. Flow → ranking is
closed; ranking → flow is only described in prose and needs conservation, band and objective
preservation written out. Solving all of `V_m(η)` and finding the sharp collapse scale are
**not** required to submit — but then the title and abstract must stay inside the exact
marginal price and the breakpoint.

---

## 5. The open list, in the order it should be attacked

1. **A, observation model.** Centring (`theta0_centered`) puts the world in the class where
   energy *is* the Gaussian KL. What remains is carrying the alternatives through the actual
   response map: they are still defined by ranges and by the frozen contrast.
2. **A, the learner.** Attach the rate bounds to the implemented algorithm; instantiate the
   per-step confidence guarantee at its own confidence set; separate certificate error from
   allocation error. **Selection never narrows**: across every stored trace the kept set is
   `['A','B']` and the chosen candidate is `A` — even on the relabelled world whose correct
   answer is `B`, where stopping still returns `B` because it tests both. So there is
   evidence that *stopping* is correct and none that *selection* learns the optimal answer.
3. **B, the transcript.** Per-query bound → continuous adaptive randomised transcript. The
   chain rule is proved only for a finite alphabet. This is the one open middle link.
4. **B, the partition.** Derive `∼_s` from the query model's moments instead of positing it
   on the world index; only then are the two orders sample complexities.
5. **C, the instantiation.** Mostly closed: the counting inequality was already
   instantiated (`hineq_for_breakpoint`), and the band bound is now derived from the
   *per-item* band rather than assumed (`LeanPaperCBandV1`, row C9) — summing the band's
   lower side over mutually exclusive (item, position) indicators and exchanging the sums.
   What is still a hypothesis is the even side's identity `r₁+r_m = (2/D)·big`.
6. **C, robustness.** Locate the collapse scale, or prove the price is more robust than the
   Lipschitz bound predicts. An adversarial search gives an *upper* bound on the worst case,
   so failing to find a worse perturbation is not evidence of robustness.

---

## 6. Nearest prior art

- Multiple-answer asymptotic optimality: **Degenne–Koolen, "Pure Exploration with Multiple
  Correct Answers", 2019, arXiv:1902.03475** — lower bound *and* an algorithm attaining the
  asymptotic complexity for multiple correct answers. So "adaptive attains the complexity"
  is **not** the contribution here; the contribution must be the geometry that changes what
  the complexity *is*.
- **"When is a proxy sufficient for a decision?" is itself an existing question.** Schutte
  et al., *Sufficient Decision Proxies for Decision-Focused Learning*, IJCAI 2026
  (`https://www.ijcai.org/proceedings/2026/260`) — supervisor-supplied, not independently
  fetched here; verify the citation before it goes into a bibliography. Paper A must state
  explicitly how the frozen-linear surrogate result differs from a sufficiency criterion for
  decision proxies.
- Finite-confidence analysis of Sticky Track-and-Stop: Poiani–Bernasconi–Celli.
- Answer-wise acceptance sets, decomposition into convex alternatives: Wang–You 2026
  (**Qiaoqiao Wang, Wei You, "Ranking-and-Selection with Multiple Correct Answers and
  Non-Answerable Estimates"**). It leaves threshold calibration problem-dependent; do not
  describe it as having solved all parts of this model.
- Decision-focused acquisition: Javdani et al. 2014. Moment–information: Rioul–Cheng–Guilley
  2021.
- Ranking under exposure/marginal constraints: Singh–Joachims 2018; Singh–Kempe–Joachims 2021.
- Data informativeness: **Omar Bennouna et al., "Data Informativeness in Linear Optimization
  under Uncertainty"** (arXiv:2602.15365).

Nothing found reproduces the three specific theorems intact; that is not the same as "nobody
has done this", and should not be written as such.

---

## 7. Process notes worth keeping

Five failures this session, each now guarded:

1. A module reported "merged clean" that in fact carried `sorryAx` — the verifier now fails
   on `sorryAx` separately from the error count.
2. Shell waiter loops (`until grep -q … sleep`) that could never exit — three multi-hour
   phantom tasks.
3. Editing `verify_all.sh` **while bash was executing it** — bash reads incrementally, so
   the run died at `done` although every module had compiled clean.
4. Declaring a measured plateau "structural" without varying the method.
5. Launching a long run without `python -u`, leaving a 0-byte log and no way to tell
   progress from a hang for 90 minutes.
