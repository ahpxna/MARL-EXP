import «LeanPaperBHellingerTestV1»
import «LeanPaperAFamilyLowerV1»
import «LeanPaperAGaussianKLV1»

/-!
# The private-query channel: the upper side of any law in `t*` must pay the number of queries

Worlds `0, 1, …, k`.
* Query `0` is the dummy.
* Query `j ≥ 1` returns `N(h, 1)` in world `j` and `N(0, 1)` in every other world.

So world `0` is pure noise, and only query `j` separates world `j` from world `0`. The task is
identification, with singleton safe sets.

* `klq_pq_le`: every query carries at most `h^2/2` nats between any two worlds, so the
  obstruction value of this problem is at most `h^2/2`.
* `private_query_lower`: every finite-horizon policy that identifies the world with
  probability `1 - δ` spends, at world `0`,
  `E_0[#queries] · h^2/2 ≥ k ((1-δ) log(1/δ) - log 2)`.

The cost is `(|W| - 1)` times what the obstruction value alone predicts. The factor is the
number of informative queries, and no law stated through `t*` alone can remove it. Section 3
shows the hypotheses are satisfiable: the Hellinger tournament identifies the world, and its
output events are measurable (`measurableSet_decode_eq`, proved for every channel).
-/

namespace CIGAMF.P13.PaperBPrivateQuery

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperALowerKL
open CIGAMF.P13.PaperAFamilyLower CIGAMF.P13.PaperAGaussianKL CIGAMF.P13.PaperAStrict
open CIGAMF.P13.PaperBObstructionLaw CIGAMF.P13.PaperBHellingerTest CIGAMF.P13.PaperBSafe
open CIGAMF.P13.PaperBSchedule

/-! ## 1. Measurability of the tournament's output, on every channel -/

section Measurable

variable {W A Ω : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
  [MeasurableSpace Ω]

theorem measurableSet_survivors_eq (R : Finset (W × W)) (beat : W → W → Set Ω)
    (hb : ∀ u v, MeasurableSet (beat u v)) (F : Finset W) :
    MeasurableSet {ω | survivors R beat ω = F} := by
  classical
  have hset : {ω | survivors R beat ω = F}
      = ⋂ w : W, {ω | (∀ v, (w, v) ∈ R → ω ∈ beat w v) ↔ w ∈ F} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, survivors, Finset.ext_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hall : ∀ w, MeasurableSet {ω | ∀ v, (w, v) ∈ R → ω ∈ beat w v} := by
    intro w
    have : {ω | ∀ v, (w, v) ∈ R → ω ∈ beat w v} = ⋂ v : W, ⋂ (_ : (w, v) ∈ R), beat w v := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hb w v
  rw [hset]
  refine MeasurableSet.iInter fun w => ?_
  by_cases hw : w ∈ F
  · simp only [hw, iff_true]
    exact hall w
  · simp only [hw, iff_false]
    exact (hall w).compl

open Classical in
/-- The decoder as a function of the survivor set. -/
noncomputable def decF (safe : W → Finset A) (a0 : A) (F : Finset W) : A :=
  if h : ∃ a, ∀ u ∈ F, a ∈ safe u then Classical.choose h else a0

theorem decode_eq_decF (safe : W → Finset A) (R : Finset (W × W)) (beat : W → W → Set Ω)
    (a0 : A) (ω : Ω) : decode safe R beat a0 ω = decF safe a0 (survivors R beat ω) := rfl

/-- **The tournament's output events are measurable** whenever its tests are. -/
theorem measurableSet_decode_eq (safe : W → Finset A) (R : Finset (W × W))
    (beat : W → W → Set Ω) (hb : ∀ u v, MeasurableSet (beat u v)) (a0 a : A) :
    MeasurableSet {ω | decode safe R beat a0 ω = a} := by
  classical
  have hset : {ω | decode safe R beat a0 ω = a}
      = ⋃ F ∈ (Finset.univ.filter fun F : Finset W => decF safe a0 F = a),
          {ω | survivors R beat ω = F} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      decode_eq_decF, exists_prop]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨F, hF, rfl⟩; exact hF
  rw [hset]
  exact Finset.measurableSet_biUnion _ fun F _ => measurableSet_survivors_eq R beat hb F

theorem measurableSet_decode_mem (safe : W → Finset A) (R : Finset (W × W))
    (beat : W → W → Set Ω) (hb : ∀ u v, MeasurableSet (beat u v)) (a0 : A) (S : Finset A) :
    MeasurableSet {ω | decode safe R beat a0 ω ∈ S} := by
  have : {ω | decode safe R beat a0 ω ∈ S} = ⋃ a ∈ S, {ω | decode safe R beat a0 ω = a} := by
    ext ω; simp
  rw [this]
  exact Finset.measurableSet_biUnion _ fun a _ => measurableSet_decode_eq safe R beat hb a0 a

end Measurable

section BeatMeas

variable {W Q : Type*} [Fintype W] [DecidableEq W]
  [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] [Fintype Q]

theorem measurable_lik (C : Channel W Q) (t : ℝ≥0) (n : ℕ) (x u v : W) :
    Measurable (lik C t n x u v) := by
  unfold lik
  exact Finset.measurable_prod _ fun i _ =>
    (C.meas x _).comp (measurable_snd.comp (measurable_pi_apply i))

theorem measurableSet_beatH (C : Channel W Q) (t : ℝ≥0) (n : ℕ) (u v : W) :
    MeasurableSet (beatH C t n u v) := by
  unfold beatH
  split_ifs
  · exact measurableSet_le (measurable_lik C t n v u v) (measurable_lik C t n u u v)
  · exact measurableSet_lt (measurable_lik C t n v u v) (measurable_lik C t n u u v)

end BeatMeas

/-! ## 2. The channel and the lower bound -/

section Channel

variable (k : ℕ)

/-- The mean of query `q` in world `j`: `h` exactly when `q = j ≠ 0`. -/
def pmean (h : ℝ) (j q : Fin (k + 1)) : ℝ := if q ≠ 0 ∧ q = j then h else 0

/-- **The private-query channel.** -/
noncomputable def pqChan (h : ℝ) : Channel (Fin (k + 1)) (Fin (k + 1)) where
  dens j q y := gaussianPDFReal (pmean k h j q) 1 y
  dummy := 0
  meas j q := measurable_gaussianPDFReal _ _
  pos j q y := gaussianPDFReal_pos _ _ _ one_ne_zero
  mass j q := lintegral_gaussianPDFReal_eq_one _ one_ne_zero
  dummy_same j j' y := by simp [pmean]

theorem obsLawC_pq (h : ℝ) (j q : Fin (k + 1)) :
    obsLawC (pqChan k h) j q = gaussianReal (pmean k h j q) 1 := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  rfl

theorem klq_pq (h : ℝ) (a b q : Fin (k + 1)) :
    klq (pqChan k h) a b q = ENNReal.ofReal ((pmean k h a q - pmean k h b q) ^ 2 / 2) := by
  unfold klq
  rw [obsLawC_pq, obsLawC_pq]
  have hne := klDiv_gaussianReal_ne_top (pmean k h a q) (pmean k h b q) 1 one_ne_zero
  rw [← ENNReal.ofReal_toReal hne, toReal_klDiv_gaussianReal _ _ _ one_ne_zero]
  unfold gaussKL
  norm_num

/-- **Every query carries at most `h^2/2` nats between any two worlds.** -/
theorem klq_pq_le (h : ℝ) (a b q : Fin (k + 1)) :
    klq (pqChan k h) a b q ≤ ENNReal.ofReal (h ^ 2 / 2) := by
  rw [klq_pq]
  apply ENNReal.ofReal_le_ofReal
  unfold pmean
  split_ifs <;> nlinarith [sq_nonneg h]

theorem klq_pq_zero_off (h : ℝ) (j q : Fin (k + 1)) (hq : q ≠ j) :
    klq (pqChan k h) 0 j q = 0 := by
  rw [klq_pq]
  unfold pmean
  have h1 : ¬ (q ≠ 0 ∧ q = 0) := fun h => h.1 h.2
  have h2 : ¬ (q ≠ 0 ∧ q = j) := fun h => hq h.2
  simp [h1, h2]

theorem klq_pq_zero_on (h : ℝ) (j : Fin (k + 1)) (hj : j ≠ 0) :
    klq (pqChan k h) 0 j j = ENNReal.ofReal (h ^ 2 / 2) := by
  rw [klq_pq]
  unfold pmean
  simp [hj]

theorem costN_eq_sum {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
    [DecidableEq Q] [Fintype Q] (C : Channel W Q) (pol : Policy Q) (w : W) (n : ℕ) :
    costN C pol w n
      = ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C pol w n) * (if q = C.dummy then 0 else 1) := by
  unfold costN
  simp_rw [tauN_eq_sum_cnt]
  rw [lintegral_finsetSum _ (fun q _ => (measurable_cntQ q n).mul_const _)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [lintegral_mul_const _ (measurable_cntQ q n)]

/-- **The lower bound at the noise world.**  Every finite-horizon policy that identifies the
world with probability `1 - δ` spends, at world `0`,
`E_0[#queries] · h^2/2 ≥ k ((1-δ) log(1/δ) - log 2)`. -/
theorem private_query_lower (h : ℝ) (pol : Policy (Fin (k + 1))) (n : ℕ)
    (out : Hist (Fin (k + 1)) n → Fin (k + 1)) (hmeas : ∀ j, MeasurableSet {ω | out ω = j})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : ∀ j, 1 - δ ≤ (hist (pqChan k h) pol j n).real {ω | out ω = j}) :
    (k : ℝ≥0∞) * ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2)
      ≤ costN (pqChan k h) pol 0 n * ENNReal.ofReal (h ^ 2 / 2) := by
  classical
  set D := ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2) with hDdef
  set c := ENNReal.ofReal (h ^ 2 / 2) with hc
  have hper : ∀ j : Fin (k + 1), j ≠ 0 →
      D ≤ (∫⁻ ω, cntQ j n ω ∂hist (pqChan k h) pol 0 n) * c := by
    intro j hj
    haveI := hist_prob (pqChan k h) pol j n
    have hS := hmeas 0
    have hl : (hist (pqChan k h) pol j n).real {ω | out ω = 0} ≤ δ := by
      have hsub : {ω | out ω = 0} ⊆ {ω | out ω = j}ᶜ := by
        intro ω hω hj'
        exact hj ((Set.mem_setOf_eq ▸ hj').symm.trans hω)
      have := measureReal_mono hsub (measure_ne_top (hist (pqChan k h) pol j n) _)
      rw [measureReal_compl (hmeas j), probReal_univ] at this
      linarith [hcorr j]
    have hcm := change_of_measure (pqChan k h) pol 0 j n {ω | out ω = 0} hS δ hδ hδ1
      (hcorr 0) hl
    rw [Finset.sum_eq_single j] at hcm
    · rwa [klq_pq_zero_on k h j hj] at hcm
    · intro q _ hq
      rw [klq_pq_zero_off k h j q hq, mul_zero]
    · intro hj'; exact absurd (Finset.mem_univ j) hj'
  have hcard : ((Finset.univ.erase (0 : Fin (k + 1))).card : ℝ≥0∞) = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    simp
  calc (k : ℝ≥0∞) * D = ∑ _j ∈ Finset.univ.erase (0 : Fin (k + 1)), D := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ ∑ j ∈ Finset.univ.erase (0 : Fin (k + 1)),
          (∫⁻ ω, cntQ j n ω ∂hist (pqChan k h) pol 0 n) * c :=
        Finset.sum_le_sum fun j hj => hper j (Finset.ne_of_mem_erase hj)
    _ = costN (pqChan k h) pol 0 n * c := by
        rw [costN_eq_sum, Finset.sum_mul]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (k + 1)))]
        have h0 : (0 : Fin (k + 1)) = (pqChan k h).dummy := rfl
        simp only [← h0, if_true, mul_zero, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [if_neg (Finset.ne_of_mem_erase hj), mul_one]

end Channel

/-! ## 3. The hypotheses are satisfiable -/

section Satisfiable

variable (k : ℕ)

theorem gauss_prod_gen (a b y : ℝ) :
    gaussianPDFReal a 1 y * gaussianPDFReal b 1 y
      = (Real.exp (-(a - b) ^ 2 / 8) * gaussianPDFReal ((a + b) / 2) 1 y) ^ 2 := by
  simp only [gaussianPDFReal, NNReal.coe_one]
  have e : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [← Real.exp_nat_mul]; norm_num
  calc (√(2 * π * 1))⁻¹ * rexp (-(y - a) ^ 2 / (2 * 1))
        * ((√(2 * π * 1))⁻¹ * rexp (-(y - b) ^ 2 / (2 * 1)))
      = (√(2 * π * 1))⁻¹ ^ 2 * rexp (-(y - a) ^ 2 / (2 * 1) + -(y - b) ^ 2 / (2 * 1)) := by
        rw [Real.exp_add]; ring
    _ = (√(2 * π * 1))⁻¹ ^ 2
          * rexp (2 * (-(a - b) ^ 2 / 8 + -(y - (a + b) / 2) ^ 2 / (2 * 1))) := by
        congr 2; ring
    _ = (rexp (-(a - b) ^ 2 / 8)
          * ((√(2 * π * 1))⁻¹ * rexp (-(y - (a + b) / 2) ^ 2 / (2 * 1)))) ^ 2 := by
        rw [← e, Real.exp_add]; ring

theorem bc_pq (h : ℝ) (a b q : Fin (k + 1)) :
    bc (pqChan k h) a b q
      = ENNReal.ofReal (Real.exp (-(pmean k h a q - pmean k h b q) ^ 2 / 8)) := by
  unfold bc
  have hpt : ∀ y, ENNReal.ofReal (Real.sqrt ((pqChan k h).dens a q y * (pqChan k h).dens b q y))
      = ENNReal.ofReal (Real.exp (-(pmean k h a q - pmean k h b q) ^ 2 / 8))
        * ENNReal.ofReal (gaussianPDFReal ((pmean k h a q + pmean k h b q) / 2) 1 y) := by
    intro y
    show ENNReal.ofReal (Real.sqrt (gaussianPDFReal (pmean k h a q) 1 y
      * gaussianPDFReal (pmean k h b q) 1 y)) = _
    rw [gauss_prod_gen, Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le
      (gaussianPDFReal_nonneg _ _ _)), ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (measurable_gaussianPDFReal _ 1).ennreal_ofReal,
    lintegral_gaussianPDFReal_eq_one _ one_ne_zero, mul_one]

/-- The Hellinger information of a separating query. -/
theorem helNN_pq (h : ℝ) (a b q : Fin (k + 1))
    (hsep : (pmean k h a q - pmean k h b q) ^ 2 = h ^ 2) :
    (helNN (pqChan k h) a b q : ℝ) = 1 - Real.exp (-h ^ 2 / 8) := by
  show hel (pqChan k h) a b q = _
  unfold hel
  rw [bc_pq, ENNReal.toReal_ofReal (Real.exp_pos _).le, hsep]

/-- Some query separates any two distinct worlds by `h`. -/
theorem pq_sep (h : ℝ) (a b : Fin (k + 1)) (hab : a ≠ b) :
    ∃ q, (pmean k h a q - pmean k h b q) ^ 2 = h ^ 2 := by
  by_cases ha : a = 0
  · subst ha
    refine ⟨b, ?_⟩
    have hb : b ≠ 0 := fun h => hab h.symm
    unfold pmean
    simp [hb]
  · refine ⟨a, ?_⟩
    unfold pmean
    simp [ha, hab]

/-- **Identification is resolved** at `t = 1 - e^{-h^2/8} > 0` for `h ≠ 0`. -/
theorem pq_resolves (h : ℝ) :
    Resolves (kH (pqChan k h)) (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1))))
      ⟨1 - Real.exp (-h ^ 2 / 8), by
        have : Real.exp (-h ^ 2 / 8) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg h])
        linarith⟩ := by
  intro H hH
  obtain ⟨u, hu⟩ : H.Nonempty := by
    obtain ⟨w, hw, _⟩ := hH 0
    exact ⟨w, hw⟩
  obtain ⟨v, hv, hvu⟩ := hH u
  have hne : u ≠ v := fun h => hvu (by simp [h])
  refine ⟨u, hu, v, hv, hne, ?_⟩
  obtain ⟨q, hq⟩ := pq_sep k h u v hne
  have hle : helNN (pqChan k h) u v q ≤ kH (pqChan k h) u v :=
    Finset.le_sup (f := helNN (pqChan k h) u v) (Finset.mem_univ q)
  refine le_trans (le_of_eq ?_) hle
  apply Subtype.ext
  exact (helNN_pq k h u v q hq).symm

/-- **The lower bound is not vacuous.**  For `h ≠ 0` and every `δ ∈ (0, 1]`, the Hellinger
tournament is a finite-horizon policy with measurable output that identifies the world with
probability `≥ 1 - δ` at every world. -/
theorem private_query_satisfiable (h : ℝ) (hh : h ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (pol : Policy (Fin (k + 1))) (n : ℕ) (out : Hist (Fin (k + 1)) n → Fin (k + 1)),
      (∀ j, MeasurableSet {ω | out ω = j})
        ∧ ∀ j, 1 - δ ≤ (hist (pqChan k h) pol j n).real {ω | out ω = j} := by
  classical
  have hpos : 0 < 1 - Real.exp (-h ^ 2 / 8) := by
    have : Real.exp (-h ^ 2 / 8) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < h ^ 2 := by positivity
      linarith)
    linarith
  set t : ℝ≥0 := ⟨1 - Real.exp (-h ^ 2 / 8), hpos.le⟩ with ht
  have htpos : 0 < t := by
    show (0 : ℝ) < 1 - Real.exp (-h ^ 2 / 8); exact hpos
  set m : ℕ := ⌈Real.log ((Fintype.card (Fin (k + 1)) : ℝ) / δ) / t⌉₊ with hm
  have hn : Real.log ((Fintype.card (Fin (k + 1)) : ℝ) / δ) / t ≤ m := Nat.le_ceil _
  obtain ⟨herr, -⟩ := hellinger_tournament (pqChan k h)
    (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1)))) t htpos (pq_resolves k h) 0 δ hδ m hn
  refine ⟨schedPolicy (tSched (pqChan k h) t m), Fintype.card (Fin (k + 1) × Fin (k + 1)) * m,
    decode (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1))))
      (pairSet (kH (pqChan k h)) t) (beatH (pqChan k h) t m) 0, ?_, ?_⟩
  · intro j
    exact measurableSet_decode_eq _ _ _ (measurableSet_beatH (pqChan k h) t m) 0 j
  · intro j
    haveI := hist_prob (pqChan k h) (schedPolicy (tSched (pqChan k h) t m)) j
      (Fintype.card (Fin (k + 1) × Fin (k + 1)) * m)
    have hmj := measurableSet_decode_eq (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1))))
      (pairSet (kH (pqChan k h)) t) (beatH (pqChan k h) t m)
      (measurableSet_beatH (pqChan k h) t m) 0 j
    have he := herr j
    have hset : {ω | decode (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1))))
        (pairSet (kH (pqChan k h)) t) (beatH (pqChan k h) t m) 0 ω ∉ ({j} : Finset (Fin (k + 1)))}
        = {ω | decode (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1))))
            (pairSet (kH (pqChan k h)) t) (beatH (pqChan k h) t m) 0 ω = j}ᶜ := by
      ext ω; simp
    rw [hset] at he
    have hreal : (hist (pqChan k h) (schedPolicy (tSched (pqChan k h) t m)) j
        (Fintype.card (Fin (k + 1) × Fin (k + 1)) * m)).real
          {ω | decode (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1))))
            (pairSet (kH (pqChan k h)) t) (beatH (pqChan k h) t m) 0 ω = j}ᶜ ≤ δ := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hδ.le he
    rw [measureReal_compl hmj, probReal_univ] at hreal
    linarith

end Satisfiable

#print axioms measurableSet_decode_eq
#print axioms measurableSet_beatH
#print axioms klq_pq_le
#print axioms private_query_lower
#print axioms bc_pq
#print axioms pq_resolves
#print axioms private_query_satisfiable

end CIGAMF.P13.PaperBPrivateQuery
