# Writing dossier — everything needed to draft the three final papers

Companion files: **`PROOFS.md`** (the central arguments in readable mathematics, no Lean
required) and **`CLAIMS.md`** (claim → theorem → remaining hypotheses → evidence, one row
per headline). This file is the superset: state of the corpus, exact statements, every
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
N theorems".

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
| Mean queries, **pre-damping** policy, 48 runs/arm | learner `1740.6`, uniform `1616.7`, oracle `1156.3` | `paperA7_learner.json` |

**Two things to state plainly.**
*The learner does not beat uniform* on the measured panel. An oracle allocation maximises
the asymptotic information rate, which is not the same as minimising a finite-`α` stopping
time; the gap is the cost of learning the allocation and of the oracle calls, and is not
explained away.
*Repair is undetermined, not negative.* In true units the certificate ceiling is vacuous at
every `M` tested, and at `M=256` none of the 43 sampled designs is certified, so
`Γ_cert = sup_{Cert(w)} J_true(w)` is not estimated at all.

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
| Identify order, linear class | `3.79` (`r=2`), `8.13` (`r=3`) | claimed `2r = 4, 6` |
| Decide order | `1.91` | claimed `2` |
| Out-of-sample ratio, coarse-fitted `C_r` | `1.089` (`r=2`), `0.126` (`r=3`) | **upper-envelope test only** |
| Search-limited `h` values | `0/6` (`r=2`), **`4/6` (`r=3`)** | ascent never beat its best seed |
| Degree-capped refutation order | `3.937` | `< 6`, so the law fails there |
| Crossover orders, `η = 0 → 1.6` | `5.93, 5.63, 5.14, 4.50, 4.11, 3.98, 3.95` | monotone |
| Normalised cross term | `6.60e-15` | on the model's own baseline `p₀ = ½[f(y−1)+f(y+1)]` |

**Read the `r=3` order correctly.** Two thirds of its `h` values are search-limited — 39
starts, all converged, canonical probe `(z₄+z₅+z₆)/3` seeded, and the ascent still never
improves on its best seed. So `8.13` is **not** evidence for an `h⁶` optimum law. A ratio
of `0.126` means the measured order *exceeds* `2r`, so the upper envelope holds with room;
it is not a two-sided approximation and must not be reported as one.

### Retracted this session

1. **"within a factor of two"** for the out-of-sample check — it tested only the upper side.
2. **`p₀ = f`** in the crossover parity block — the baseline must be the mixture over the
   `z₁` channel, `½[f(y−1)+f(y+1)]`. Parity still gives `6.6e-15`, but on the right density.
3. **`7.12` and `C₃ = 6.85e-2`** in the manuscript — numbers from the refuted degree-capped
   run, now `8.13` and `8.2961e-4` on the linear class.

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

Both stale entries are the two being regenerated (`paperA7_learner`,
`paperB_uniform_hellinger`). Artifacts predating the hash convention are reported `NO-HASH`
rather than silently accepted; there are now none.

**Policy generations must not be mixed.** `paperA7_learner.json` carries
`policy_generation: pre-damping`, `superseded_by`, and `do_not_combine`. Its 144 runs were
produced by a different allocation policy (before the running-min bracket, the damped step,
the dual tolerance, the witness-feasibility check and the selection slack). The
corrected-policy run **replaces** those figures; it is never averaged with them, and a smoke
run does not substitute for the full comparison.

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
5. **C, the instantiation.** Prove the counting inequality and the band bound for the
   concrete family, removing the conditionality of (O2).
6. **C, robustness.** Locate the collapse scale, or prove the price is more robust than the
   Lipschitz bound predicts. An adversarial search gives an *upper* bound on the worst case,
   so failing to find a worse perturbation is not evidence of robustness.

---

## 6. Nearest prior art

- Multiple-answer asymptotic optimality: Degenne–Koolen 2019.
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
