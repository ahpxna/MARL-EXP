import «LeanPaperAFamilyLowerV1»
import «LeanPaperAFrontierV1»

/-!
# Paper A: how much surrogate value must be given up to make the true decision

`LeanPaperAFrontierV1` answers a design question.  Giving up a fraction `beta` of the
surrogate's value buys back `Theta(beta / (rM))` of true information.  This module answers
the operational question: how much surrogate value must a learner give up in order to make
the true decision `delta`-correctly at all?

Throughout, the surrogate value of a design is the frozen game `J_fr(w) = frozenValueC₀ M w`
at the true world, with optimum `Gamma_fr = 9/512` (`frozenGameC₀_eq`).  Its **relative
sacrifice** is

    sacrifice(w) = 1 - J_fr(w) / Gamma_fr        (`sacrifice`, `sacrifice_eq_relative`).

It is a diagnostic of a design and never enters a learner.

* `pair_demand`: every finite-horizon policy that is `delta`-correct against the strict
  alternatives queries each of the `r` middle pairs at least `8 M D` times in expectation at
  the truth, where `D = (1 - delta) log(1/delta) - log 2`.  The proof uses one change of
  measure per pair, at the strict shift `1/2 + d`, and lets `d -> 0`.
* `middle_demand`: in total, at least `8 r M D` expected queries go to middle cells.
* `middle_le_sacrifice`: a middle query is paid for in surrogate value.  For every
  allocation, the middle mass is at most the relative sacrifice.
* **`sacrifice_cost_law`**: the average design `wbar` (expected counts over their total `N`)
  satisfies

      N * sacrifice(wbar)  >=  8 r M D.

  This is the answer.  What must be given up is a **budget**, `8 r M log(1/delta)` query-units
  of surrogate value to first order, not a fraction.  A learner may spread it thinly over a
  long run (small `sacrifice`, large `N`) or pay it quickly, but it cannot avoid it.
* `exchange_strict`: pointwise, `J_true(w) <= sacrifice(w) / (8 r M)` on the STRICT game (the
  one the decision defines), so the design frontier holds on the operational game.
  `strict_frontier` gives both sides there.
* **`forcing_law`** (Jensen): if a learner's middle count obeys `Mid <= phi(T) + B` pathwise,
  for a concave continuous `phi`, then `phi(E T) >= 8 r M D - E B`.  **`power_forcing_law`**:
  for `phi(t) = c t^a` with `0 < a <= 1`,

      E T  >=  ((8 r M D - b) / c)^(1/a).

  At `a = 1/2` this is the `log^2(1/delta)` cost of square-root forcing, now for every
  learner of that shape rather than one constructed learner.
* `upper_constant`: `1 / Gamma_true <= 128 (4 + 2 r M) / 9`.  With `sacrifice <= 1`
  (`sacrifice_le_one`), the ideal learner of `LeanPaperA7IdealFamilyV1` (rate
  `1/actualKLGame`) pays at most `(128 (4 + 2rM)/9 + o(1)) log(1/delta)`.  The budget is
  therefore `Theta(r M log(1/delta))`; the constants differ by at most `32/9` as `rM -> oo`.

Scope.  Every statement is about Paper A's centred family (`thetaC r`, `famChan`), with the
strict alternatives the compression decision defines.  All policies are randomised,
adaptive and of finite horizon.  The dummy query is free and carries no information.
-/

namespace CIGAMF.P13.PaperASacrifice

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy
open CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperAActualDecisionBridge CIGAMF.P13.PaperAStrict
open CIGAMF.P13.PaperACentred CIGAMF.P13.PaperARPair CIGAMF.P13.PaperAGaussianKL
open CIGAMF.P13.PaperAFamilyLower CIGAMF.P13.PaperAFrontier

variable {r : ℕ}

/-! ## 0. The two scalar objects -/

/-- The demand of a `delta`-correct answer: `(1 - delta) log(1/delta) - log 2`. -/
noncomputable def demand (δ : ℝ) : ℝ := (1 - δ) * Real.log (1 / δ) - Real.log 2

/-- The relative surrogate sacrifice of a design: `1 - J_fr / Gamma_fr`. -/
noncomputable def sacrifice (M : ℝ) (w : Cell r → ℝ) : ℝ := 1 - (512 / 9) * frozenValueC₀ M w

theorem sacrifice_eq_relative (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) :
    sacrifice M w = 1 - frozenValueC₀ M w / frozenGameC₀ r M := by
  rw [frozenGameC₀_eq r M hM]
  unfold sacrifice
  ring

theorem frozenValueC₀_nonneg' (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ frozenValueC₀ M w :=
  le_ciInf (fun lam => energyC_nonneg M hM _ _ hw)

theorem sacrifice_le_one (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    sacrifice M w ≤ 1 := by
  have := frozenValueC₀_nonneg' M hM w hw
  unfold sacrifice
  linarith

/-- **A middle query is paid for in surrogate value.**  The middle mass of an allocation is
at most its relative sacrifice. -/
theorem middle_le_sacrifice (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w) :
    ∑ p : Fin r × Bool, w (Sum.inr p) ≤ sacrifice M w := by
  have h := near_optimal_starvation₀ M hM w hw (9 / 512 - frozenValueC₀ M w) (by linarith)
  unfold sacrifice
  linarith

theorem sacrifice_nonneg (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w) :
    0 ≤ sacrifice M w :=
  le_trans (Finset.sum_nonneg fun p _ => hw.1 _) (middle_le_sacrifice M hM w hw)

/-! ## 1. A limit in the shift margin -/

/-- If `D <= P (1/2 + d)^2 / (2M)` for every `d > 0`, then `8 M D <= P`. -/
theorem limit_shift (D P M : ℝ) (hM : 0 < M) (hP : 0 ≤ P)
    (h : ∀ d : ℝ, 0 < d → D ≤ P * (1 / 2 + d) ^ 2 / (2 * M)) : 8 * M * D ≤ P := by
  have key : D ≤ P / (8 * M) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    set d := min 1 (M * ε / (P + 1)) with hd
    have hd0 : 0 < d := lt_min one_pos (by positivity)
    have hd1 : d ≤ 1 := min_le_left _ _
    have hd2 : d ≤ M * ε / (P + 1) := min_le_right _ _
    have h1 := h d hd0
    have hsplit : P * (1 / 2 + d) ^ 2 / (2 * M) = P / (8 * M) + P * (d + d ^ 2) / (2 * M) := by
      field_simp
      ring
    have h2 : P * (d + d ^ 2) / (2 * M) ≤ P * d / M := by
      rw [div_le_div_iff₀ (by positivity) hM]
      nlinarith [mul_nonneg (mul_nonneg hP hM.le) (mul_nonneg hd0.le (sub_nonneg.2 hd1))]
    have h3 : P * d / M ≤ ε := by
      rw [div_le_iff₀ hM]
      have h4 : P * d ≤ P * (M * ε / (P + 1)) := mul_le_mul_of_nonneg_left hd2 hP
      have h5 : P * (M * ε / (P + 1)) ≤ ε * M := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith [mul_pos hM hε]
      linarith
    linarith
  rw [le_div_iff₀ (by positivity)] at key
  linarith

/-! ## 2. The demand on each middle pair, for every policy -/

/-- The expected number of queries of real cell `e` at the truth, as a real number. -/
noncomputable def expCnt (M : ℝ) (hM : 0 < M) (π : Policy (Cell r ⊕ Unit)) (n : ℕ) :
    Cell r → ℝ :=
  fun e => (∫⁻ ω, cntQ (Sum.inl e) n ω ∂hist (famChan M hM) π (lift (thetaC r)) n).toReal

theorem expCnt_nonneg (M : ℝ) (hM : 0 < M) (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (e : Cell r) :
    0 ≤ expCnt M hM π n e := ENNReal.toReal_nonneg

/-- One change of measure at the strict shift of pair `j` by `1/2 + d`. -/
theorem demand_le_shift [NeZero r] (M : ℝ) (hM : 0 < M)
    (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist (famChan M hM) π (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π (lift lam) n).real S ≤ δ)
    (hD : 0 ≤ demand δ) (j : Fin r) (d : ℝ) (hd : 0 < d) :
    demand δ ≤ pairWeight (expCnt M hM π n) j * (1 / 2 + d) ^ 2 / (2 * M) := by
  classical
  have hKL := gaussianKLIdentification_holds r M hM
  have hθc := thetaC_mem_centred r
  have hmem : pairShift (thetaC r) j (1 / 2 + d) ∈ TrueAltStrict r :=
    ⟨(pairShiftC_strict_alt j d hd).1, pairShiftC_mem_centred j (1 / 2 + d)⟩
  have hk : ∀ e, klq (famChan M hM) (lift (thetaC r)) (lift (pairShift (thetaC r) j (1 / 2 + d)))
      (Sum.inl e) = klDiv (observationLaw (familyVariance r M hM) (thetaC r) e)
        (observationLaw (familyVariance r M hM) (pairShift (thetaC r) j (1 / 2 + d)) e) := by
    intro e
    unfold klq
    rw [obsLaw_fam_real M hM _ hθc, obsLaw_fam_real M hM _ hmem.2]
  have hfin : ∀ q, klq (famChan M hM) (lift (thetaC r))
      (lift (pairShift (thetaC r) j (1 / 2 + d))) q ≠ ⊤ := by
    intro q
    cases q with
    | inl e => rw [hk e]; exact (hKL _ _ hθc hmem.2 e).1
    | inr u =>
        have : (Sum.inr u : Cell r ⊕ Unit) = (famChan (r := r) M hM).dummy := rfl
        rw [this, klq_dummy]; exact ENNReal.zero_ne_top
  have hc := change_of_measure (famChan M hM) π (lift (thetaC r))
    (lift (pairShift (thetaC r) j (1 / 2 + d))) n S hS δ hδ hδ1 hθ (hl _ hmem)
  have hre := real_of_change _ hD _ _
    (fun q => lintegral_cntQ_ne_top (famChan M hM) π (lift (thetaC r)) q n) hfin hc
  rw [Fintype.sum_sum_type] at hre
  have hdum : ∑ u : Unit, (∫⁻ ω, cntQ (Sum.inr u) n ω
      ∂hist (famChan M hM) π (lift (thetaC r)) n).toReal
      * (klq (famChan M hM) (lift (thetaC r)) (lift (pairShift (thetaC r) j (1 / 2 + d)))
          (Sum.inr u)).toReal = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    have : (Sum.inr u : Cell r ⊕ Unit) = (famChan (r := r) M hM).dummy := rfl
    rw [this, klq_dummy]
    simp
  have hreal : ∑ e : Cell r, (∫⁻ ω, cntQ (Sum.inl e) n ω
      ∂hist (famChan M hM) π (lift (thetaC r)) n).toReal
      * (klq (famChan M hM) (lift (thetaC r)) (lift (pairShift (thetaC r) j (1 / 2 + d)))
          (Sum.inl e)).toReal
      = energy (expCnt M hM π n) (pairVar M) (thetaC r) (pairShift (thetaC r) j (1 / 2 + d)) := by
    rw [energy_eq_sum_gaussKL]
    refine Finset.sum_congr rfl fun e _ => ?_
    obtain ⟨-, h2⟩ := hKL _ _ hθc hmem.2 e
    rw [hk e, h2]
    rfl
  have henergy : energy (expCnt M hM π n) (pairVar M) (thetaC r)
      (pairShift (thetaC r) j (1 / 2 + d))
      = pairWeight (expCnt M hM π n) j * (1 / 2 + d) ^ 2 / (2 * M) :=
    pair_shift_energy _ (pairVar M) (thetaC r) _ j M (1 / 2 + d) hM
      (pairVarC_pair M (j, true)) (pairVarC_pair M (j, false))
      (pairShift_true (thetaC r) j (1 / 2 + d)) (pairShift_false (thetaC r) j (1 / 2 + d))
      (fun e h1 h2 => pairShift_rest (thetaC r) j (1 / 2 + d) e h1 h2)
  linarith

/-- **Every middle pair must be queried `8 M D` times in expectation.** -/
theorem pair_demand [NeZero r] (M : ℝ) (hM : 0 < M)
    (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist (famChan M hM) π (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π (lift lam) n).real S ≤ δ)
    (hD : 0 ≤ demand δ) (j : Fin r) :
    8 * M * demand δ ≤ pairWeight (expCnt M hM π n) j :=
  limit_shift _ _ M hM (pairWeight_nonneg _ (expCnt_nonneg M hM π n) j)
    (fun d hd => demand_le_shift M hM π n S hS δ hδ hδ1 hθ hl hD j d hd)

/-- **In total, `8 r M D` expected queries must go to middle cells.** -/
theorem middle_demand [NeZero r] (M : ℝ) (hM : 0 < M)
    (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist (famChan M hM) π (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π (lift lam) n).real S ≤ δ)
    (hD : 0 ≤ demand δ) :
    8 * (r : ℝ) * M * demand δ ≤ ∑ p : Fin r × Bool, expCnt M hM π n (Sum.inr p) := by
  rw [middle_eq_sum_pairWeight]
  have hconst : ∑ _j : Fin r, 8 * M * demand δ = 8 * (r : ℝ) * M * demand δ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [← hconst]
  exact Finset.sum_le_sum fun j _ => pair_demand M hM π n S hS δ hδ hδ1 hθ hl hD j

/-! ## 3. The sacrifice–cost law -/

/-- **The sacrifice–cost law.**  For every finite-horizon policy that is `delta`-correct
against the strict alternatives, the expected number of real queries `N` and the relative
surrogate sacrifice of the average design `wbar = expCnt / N` satisfy
`N * sacrifice(wbar) >= 8 r M D`. -/
theorem sacrifice_cost_law [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r)
    (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist (famChan M hM) π (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π (lift lam) n).real S ≤ δ)
    (hD : 0 < demand δ) :
    0 < ∑ e, expCnt M hM π n e
      ∧ IsAlloc (fun e => expCnt M hM π n e / ∑ e', expCnt M hM π n e')
      ∧ 8 * (r : ℝ) * M * demand δ
          ≤ (∑ e, expCnt M hM π n e)
            * sacrifice M (fun e => expCnt M hM π n e / ∑ e', expCnt M hM π n e') := by
  classical
  set c := expCnt M hM π n with hc
  set N := ∑ e, c e with hN
  have hmid := middle_demand M hM π n S hS δ hδ hδ1 hθ hl hD.le
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmidpos : 0 < ∑ p : Fin r × Bool, c (Sum.inr p) := by
    have : 0 < 8 * (r : ℝ) * M * demand δ := by positivity
    linarith
  have hsplit : N = (∑ i : Fin 4, c (Sum.inl i)) + ∑ p : Fin r × Bool, c (Sum.inr p) :=
    Fintype.sum_sum_type _
  have hA : 0 ≤ ∑ i : Fin 4, c (Sum.inl i) :=
    Finset.sum_nonneg fun i _ => expCnt_nonneg M hM π n _
  have hNpos : 0 < N := by linarith
  have halloc : IsAlloc (fun e => c e / N) := by
    refine ⟨fun e => div_nonneg (expCnt_nonneg M hM π n e) hNpos.le, ?_⟩
    rw [← Finset.sum_div, div_self hNpos.ne']
  refine ⟨hNpos, halloc, ?_⟩
  have hml := middle_le_sacrifice M hM (fun e => c e / N) halloc
  have hmideq : ∑ p : Fin r × Bool, c (Sum.inr p) / N
      = (∑ p : Fin r × Bool, c (Sum.inr p)) / N := (Finset.sum_div _ _ _).symm
  rw [hmideq, div_le_iff₀ hNpos] at hml
  linarith

/-! ## 4. The exchange on the operational (strict) game, and its frontier -/

/-- **Pointwise exchange on the strict game.**  `J_true(w) <= sacrifice(w) / (8 r M)`. -/
theorem exchange_strict [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (w : Cell r → ℝ)
    (hw : IsAlloc w) :
    trueValueStrict M w ≤ sacrifice M w / (8 * M * (r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨j, hj⟩ := exists_light_pair_le r hr (pairWeight w) (sacrifice M w)
    (by rw [← middle_eq_sum_pairWeight]; exact middle_le_sacrifice M hM w hw)
  have hlim := limit_shift (trueValueStrict M w) (pairWeight w j) M hM
    (pairWeight_nonneg w hw.1 j) (fun d hd => trueValueStrict_le_shift M hM w hw.1 j d hd)
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ hrR] at hj
  nlinarith

/-- **The frontier on the strict game, both sides.** -/
theorem strict_frontier [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∃ w : Cell r → ℝ, IsAlloc w ∧ sacrifice M w ≤ β
        ∧ 9 * β / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueValueStrict M w)
      ∧ (∀ w : Cell r → ℝ, IsAlloc w → sacrifice M w ≤ β →
          trueValueStrict M w ≤ β / (8 * M * (r : ℝ))) := by
  refine ⟨?_, fun w hw hs => ?_⟩
  · obtain ⟨w, hw, hfr, htr⟩ := frontier_lower M hM r hr β hβ0 hβ1
    refine ⟨w, hw, ?_, le_trans htr (trueValueC₀_le_trueValueStrict M hM w hw.1)⟩
    unfold sacrifice
    linarith
  · have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    exact (exchange_strict M hM hr w hw).trans
      (div_le_div_of_nonneg_right hs (by positivity))

/-! ## 5. Forcing schedules: Jensen -/

/-- The total number of real queries of a history. -/
noncomputable def totReal (n : ℕ) (ω : Hist (Cell r ⊕ Unit) n) : ℝ :=
  ∑ e : Cell r, (cntQ (Sum.inl e) n ω).toReal

/-- The number of middle queries of a history. -/
noncomputable def midReal (n : ℕ) (ω : Hist (Cell r ⊕ Unit) n) : ℝ :=
  ∑ p : Fin r × Bool, (cntQ (Sum.inl (Sum.inr p)) n ω).toReal

theorem cntQ_lt_top (q : Cell r ⊕ Unit) (n : ℕ) (ω : Hist (Cell r ⊕ Unit) n) :
    cntQ q n ω < ⊤ :=
  lt_of_le_of_lt (cntQ_le q n ω) (ENNReal.natCast_lt_top n)

theorem cntQ_toReal_le (q : Cell r ⊕ Unit) (n : ℕ) (ω : Hist (Cell r ⊕ Unit) n) :
    (cntQ q n ω).toReal ≤ n := by
  have h := cntQ_le q n ω
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top n) h
  simpa using this

theorem measurable_cnt_toReal (q : Cell r ⊕ Unit) (n : ℕ) :
    Measurable fun ω : Hist (Cell r ⊕ Unit) n => (cntQ q n ω).toReal :=
  (measurable_cntQ q n).ennreal_toReal

theorem integrable_cnt_toReal (μ : Measure (Hist (Cell r ⊕ Unit) n)) [IsProbabilityMeasure μ]
    (q : Cell r ⊕ Unit) :
    Integrable (fun ω => (cntQ q n ω).toReal) μ := by
  refine Integrable.of_bound (measurable_cnt_toReal q n).aestronglyMeasurable (n : ℝ) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact cntQ_toReal_le q n ω

theorem integral_cnt_toReal (μ : Measure (Hist (Cell r ⊕ Unit) n)) [IsProbabilityMeasure μ]
    (q : Cell r ⊕ Unit) :
    ∫ ω, (cntQ q n ω).toReal ∂μ = (∫⁻ ω, cntQ q n ω ∂μ).toReal :=
  integral_toReal (measurable_cntQ q n).aemeasurable
    (Filter.Eventually.of_forall fun ω => cntQ_lt_top q n ω)

theorem integral_midReal (M : ℝ) (hM : 0 < M) (π : Policy (Cell r ⊕ Unit)) (n : ℕ) :
    ∫ ω, midReal n ω ∂hist (famChan M hM) π (lift (thetaC r)) n
      = ∑ p : Fin r × Bool, expCnt M hM π n (Sum.inr p) := by
  have := hist_prob (famChan M hM) π (lift (thetaC r)) n
  unfold midReal
  rw [integral_finsetSum _ fun p _ => integrable_cnt_toReal _ _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_cnt_toReal]
  rfl

theorem integrable_totReal (μ : Measure (Hist (Cell r ⊕ Unit) n)) [IsProbabilityMeasure μ] :
    Integrable (totReal n) μ := by
  unfold totReal
  exact integrable_finsetSum _ fun e _ => integrable_cnt_toReal μ _

theorem totReal_nonneg (n : ℕ) (ω : Hist (Cell r ⊕ Unit) n) : 0 ≤ totReal n ω :=
  Finset.sum_nonneg fun e _ => ENNReal.toReal_nonneg

theorem totReal_le (n : ℕ) (ω : Hist (Cell r ⊕ Unit) n) :
    totReal n ω ≤ Fintype.card (Cell r) * n := by
  unfold totReal
  calc ∑ e : Cell r, (cntQ (Sum.inl e) n ω).toReal ≤ ∑ _e : Cell r, (n : ℝ) :=
        Finset.sum_le_sum fun e _ => cntQ_toReal_le _ n ω
    _ = Fintype.card (Cell r) * n := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem measurable_totReal (n : ℕ) : Measurable (totReal (r := r) n) := by
  unfold totReal
  exact Finset.measurable_sum _ fun e _ => measurable_cnt_toReal _ n

/-- **The forcing law.**  If a policy's middle count satisfies `Mid <= phi(T) + B` on every
history, for a continuous `phi` concave on `[0, oo)` and an integrable `B` with `E B <= b`,
then `8 r M D - b <= phi(E T)`, where `T` is the number of real queries. -/
theorem forcing_law [NeZero r] (M : ℝ) (hM : 0 < M)
    (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist (famChan M hM) π (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π (lift lam) n).real S ≤ δ)
    (hD : 0 ≤ demand δ)
    (φ : ℝ → ℝ) (hφc : Continuous φ) (hφ : ConcaveOn ℝ (Set.Ici 0) φ)
    (B : Hist (Cell r ⊕ Unit) n → ℝ)
    (hB : Integrable B (hist (famChan M hM) π (lift (thetaC r)) n)) (b : ℝ)
    (hb : ∫ ω, B ω ∂hist (famChan M hM) π (lift (thetaC r)) n ≤ b)
    (hpath : ∀ ω, midReal n ω ≤ φ (totReal n ω) + B ω) :
    8 * (r : ℝ) * M * demand δ - b
      ≤ φ (∫ ω, totReal n ω ∂hist (famChan M hM) π (lift (thetaC r)) n) := by
  set μ := hist (famChan M hM) π (lift (thetaC r)) n with hμ
  have := hist_prob (famChan M hM) π (lift (thetaC r)) n
  have hmid := middle_demand M hM π n S hS δ hδ hδ1 hθ hl hD
  rw [← integral_midReal] at hmid
  -- `phi ∘ T` is bounded and measurable
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Fintype.card (Cell r) * n)).exists_bound_of_continuousOn
    hφc.continuousOn
  have hφT : Integrable (fun ω => φ (totReal n ω)) μ := by
    refine Integrable.of_bound (hφc.measurable.comp (measurable_totReal n)).aestronglyMeasurable
      K (Filter.Eventually.of_forall fun ω => ?_)
    exact hK _ ⟨totReal_nonneg n ω, totReal_le n ω⟩
  have hjensen : ∫ ω, φ (totReal n ω) ∂μ ≤ φ (∫ ω, totReal n ω ∂μ) :=
    hφ.le_map_integral hφc.continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun ω => totReal_nonneg n ω) (integrable_totReal μ) hφT
  have hmidint : Integrable (midReal n) μ := by
    unfold midReal
    exact integrable_finsetSum _ fun p _ => integrable_cnt_toReal μ _
  have hmono : ∫ ω, midReal n ω ∂μ ≤ ∫ ω, (φ (totReal n ω) + B ω) ∂μ :=
    integral_mono hmidint (hφT.add hB) hpath
  rw [integral_add hφT hB] at hmono
  linarith

/-- **Power forcing.**  If the middle count is at most `c T^a + B` with `0 < a <= 1`, then
`E T >= ((8 r M D - b) / c)^(1/a)`.  At `a = 1/2` this is the `log^2(1/delta)` law of
square-root forcing, for every learner of that shape. -/
theorem power_forcing_law [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r)
    (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist (famChan M hM) π (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π (lift lam) n).real S ≤ δ)
    (hD : 0 ≤ demand δ) (c a : ℝ) (hc : 0 < c) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (B : Hist (Cell r ⊕ Unit) n → ℝ)
    (hB : Integrable B (hist (famChan M hM) π (lift (thetaC r)) n)) (b : ℝ)
    (hb : ∫ ω, B ω ∂hist (famChan M hM) π (lift (thetaC r)) n ≤ b)
    (hgap : b ≤ 8 * (r : ℝ) * M * demand δ)
    (hpath : ∀ ω, midReal n ω ≤ c * totReal n ω ^ a + B ω) :
    ((8 * (r : ℝ) * M * demand δ - b) / c) ^ (1 / a)
      ≤ ∫ ω, totReal n ω ∂hist (famChan M hM) π (lift (thetaC r)) n := by
  have := hist_prob (famChan M hM) π (lift (thetaC r)) n
  have hφc : Continuous fun t : ℝ => c * t ^ a :=
    continuous_const.mul (Real.continuous_rpow_const ha0.le)
  have hφ : ConcaveOn ℝ (Set.Ici 0) fun t : ℝ => c * t ^ a :=
    (Real.concaveOn_rpow ha0.le ha1).smul hc.le
  have h := forcing_law M hM π n S hS δ hδ hδ1 hθ hl hD (fun t => c * t ^ a) hφc hφ B hB b hb
    hpath
  set ET := ∫ ω, totReal n ω ∂hist (famChan M hM) π (lift (thetaC r)) n with hET
  have hET0 : 0 ≤ ET := integral_nonneg fun ω => totReal_nonneg n ω
  have hbase : 0 ≤ (8 * (r : ℝ) * M * demand δ - b) / c := div_nonneg (by linarith) hc.le
  have hle : (8 * (r : ℝ) * M * demand δ - b) / c ≤ ET ^ a := by
    rw [div_le_iff₀ hc]
    linarith
  calc ((8 * (r : ℝ) * M * demand δ - b) / c) ^ (1 / a) ≤ (ET ^ a) ^ (1 / a) :=
        Real.rpow_le_rpow hbase hle (by positivity)
    _ = ET := by
        rw [one_div, Real.rpow_rpow_inv hET0 ha0.ne']

/-! ## 6. The upper constant -/

/-- **The ideal learner's constant.**  `1 / Gamma_true <= 128 (4 + 2 r M) / 9`, so a learner
at the true game's rate pays at most `(128 (4 + 2rM)/9 + o(1)) log(1/delta)` queries, and at
most that much sacrifice (`sacrifice_le_one`). -/
theorem upper_constant [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) :
    1 / actualKLGame r M hM ≤ 128 * (4 + 2 * (r : ℝ) * M) / 9 := by
  have hKL := gaussianKLIdentification_holds r M hM
  have hb := (strict_game_bounds M hM hr).1
  rw [← actualKLGame_eq M hM hKL] at hb
  have hpos : (0 : ℝ) < 9 / (128 * (4 + 2 * (r : ℝ) * M)) := by positivity
  calc 1 / actualKLGame r M hM ≤ 1 / (9 / (128 * (4 + 2 * (r : ℝ) * M))) :=
        one_div_le_one_div_of_le hpos hb
    _ = 128 * (4 + 2 * (r : ℝ) * M) / 9 := by field_simp

/-- The lower and upper constants differ by at most `(128 (4 + 2rM)/9) / (8 r M)`, which
tends to `32/9` as `r M -> oo`. -/
theorem constant_gap (r M : ℝ) (hr : 0 < r) (hM : 0 < M) :
    (128 * (4 + 2 * r * M) / 9) / (8 * r * M) = 32 / 9 + 64 / (9 * r * M) := by
  field_simp
  ring

/-! ## Audit -/

#print axioms sacrifice_eq_relative
#print axioms sacrifice_le_one
#print axioms middle_le_sacrifice
#print axioms limit_shift
#print axioms demand_le_shift
#print axioms pair_demand
#print axioms middle_demand
#print axioms sacrifice_cost_law
#print axioms exchange_strict
#print axioms strict_frontier
#print axioms forcing_law
#print axioms power_forcing_law
#print axioms upper_constant
#print axioms constant_gap

end CIGAMF.P13.PaperASacrifice
