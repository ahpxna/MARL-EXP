import «LeanPaperALowerKLV1»
import «LeanPaperA7OracleSelectV1»

/-!
# Paper A: from the change of measure to `E[count] >= demand / Gamma`

`LeanPaperALowerKLV1.change_of_measure` gives, for EVERY alternative `lambda` at which the
answer is wrong, `demand <= sum_q E[N_q] KL_q(theta ‖ lambda)`.  This module turns the family
of those inequalities into the rate inequality:

* `count_lower_bound` -- if `D <= sum_q n_q k_q(lambda)` for every `lambda` in a nonempty set,
  and every allocation `w` has value `inf_lambda sum_q w_q k_q(lambda) <= Gamma`, then
  `D / Gamma <= sum_q n_q`.  The average design `n / sum n` is an allocation, so its value is at
  most the game;
* `real_of_change` -- the `ENNReal` statement of the change of measure, in real numbers, when
  the per-query divergences are finite;
* `expected_count_lower` -- both together on the adaptive protocol: every finite-horizon
  randomised policy whose answer event has the two probabilities spends, in expectation, at
  least `((1 - delta) log(1/delta) - log 2) / Gamma` queries.
-/

namespace CIGAMF.P13.PaperALowerGame

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperALowerKL
open CIGAMF.P13.PaperA7OracleSelect

/-- **The counting lower bound.** -/
theorem count_lower_bound {Q L : Type*} [Fintype Q] (Alt : Set L) (hne : Alt.Nonempty)
    (n : Q → ℝ) (hn : ∀ q, 0 ≤ n q) (k : L → Q → ℝ) (hk : ∀ l q, 0 ≤ k l q) (D : ℝ)
    (hD : 0 < D) (h : ∀ l ∈ Alt, D ≤ ∑ q, n q * k l q) (Γ : ℝ) (hΓ0 : 0 < Γ)
    (hΓ : ∀ w : Q → ℝ, IsAlloc w → sInf ((fun l => ∑ q, w q * k l q) '' Alt) ≤ Γ) :
    D / Γ ≤ ∑ q, n q := by
  set T := ∑ q, n q with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun q _ => hn q
  rcases hT0.eq_or_lt with hT0' | hTpos
  · -- no query at all: the demand cannot be met
    exfalso
    obtain ⟨l, hl⟩ := hne
    have hzero : ∀ q, n q = 0 := by
      intro q
      have := Finset.single_le_sum (f := n) (fun q _ => hn q) (Finset.mem_univ q)
      linarith [hn q]
    have := h l hl
    simp [hzero] at this
    linarith
  · -- the average design is an allocation
    set w : Q → ℝ := fun q => n q / T with hw
    have halloc : IsAlloc w := by
      refine ⟨fun q => div_nonneg (hn q) hTpos.le, ?_⟩
      rw [hw]; simp only
      rw [← Finset.sum_div, ← hT, div_self hTpos.ne']
    have hval : D / T ≤ sInf ((fun l => ∑ q, w q * k l q) '' Alt) := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨l, hl, rfl⟩
      have heq : ∑ q, w q * k l q = (∑ q, n q * k l q) / T := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hw]; ring
      show D / T ≤ ∑ q, w q * k l q
      rw [heq]
      exact div_le_div_of_nonneg_right (h l hl) hTpos.le
    have hDT : D / T ≤ Γ := le_trans hval (hΓ w halloc)
    rw [div_le_iff₀ hTpos] at hDT
    rw [div_le_iff₀ hΓ0]
    linarith

/-- The change of measure in real numbers. -/
theorem real_of_change {Q : Type*} [Fintype Q] (D : ℝ) (hD : 0 ≤ D) (n k : Q → ℝ≥0∞)
    (hn : ∀ q, n q ≠ ⊤) (hk : ∀ q, k q ≠ ⊤)
    (h : ENNReal.ofReal D ≤ ∑ q, n q * k q) :
    D ≤ ∑ q, (n q).toReal * (k q).toReal := by
  have hfin : ∑ q, n q * k q ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun q _ => ENNReal.mul_ne_top (hn q) (hk q)
  have := (ENNReal.ofReal_le_iff_le_toReal hfin).mp h
  rw [ENNReal.toReal_sum fun q _ => ENNReal.mul_ne_top (hn q) (hk q)] at this
  simpa [ENNReal.toReal_mul] using this

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- A history has at most `n` rounds of any query. -/
theorem cntQ_le (q : Q) (n : ℕ) (ω : Hist Q n) : cntQ q n ω ≤ n := by
  unfold cntQ
  calc ∑ i : Fin n, (if (ω i).1 = q then (1 : ℝ≥0∞) else 0) ≤ ∑ _i : Fin n, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> simp
    _ = n := by simp

theorem lintegral_cntQ_ne_top (C : Channel W Q) (π : Policy Q) (w : W) (q : Q) (n : ℕ) :
    ∫⁻ ω, cntQ q n ω ∂hist C π w n ≠ ⊤ := by
  haveI := hist_prob C π w n
  refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) ?_
  calc ∫⁻ ω, cntQ q n ω ∂hist C π w n ≤ ∫⁻ _ω, (n : ℝ≥0∞) ∂hist C π w n :=
        lintegral_mono fun ω => cntQ_le q n ω
    _ = n := by simp

/-- **Every finite-horizon policy's expected counts carry `demand / Gamma`.** -/
theorem expected_count_lower [Fintype Q] (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ)
    (Alt : Set W) (hne : Alt.Nonempty) (S : Set (Hist Q n)) (hS : MeasurableSet S)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist C π θ n).real S) (hl : ∀ l ∈ Alt, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ Alt, ∀ q, klq C θ l q ≠ ⊤)
    (hD : 0 < (1 - δ) * Real.log (1 / δ) - Real.log 2)
    (Γ : ℝ) (hΓ0 : 0 < Γ)
    (hΓ : ∀ w : Q → ℝ, IsAlloc w →
      sInf ((fun l => ∑ q, w q * (klq C θ l q).toReal) '' Alt) ≤ Γ) :
    ((1 - δ) * Real.log (1 / δ) - Real.log 2) / Γ
      ≤ ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n).toReal := by
  refine count_lower_bound Alt hne (fun q => (∫⁻ ω, cntQ q n ω ∂hist C π θ n).toReal)
    (fun q => ENNReal.toReal_nonneg) (fun l q => (klq C θ l q).toReal)
    (fun l q => ENNReal.toReal_nonneg) _ hD (fun l hlA => ?_) Γ hΓ0 hΓ
  exact real_of_change _ hD.le _ _ (fun q => lintegral_cntQ_ne_top C π θ q n) (hfin l hlA)
    (change_of_measure C π θ l n S hS δ hδ hδ1 hθ (hl l hlA))

#print axioms count_lower_bound
#print axioms real_of_change
#print axioms expected_count_lower

end CIGAMF.P13.PaperALowerGame
