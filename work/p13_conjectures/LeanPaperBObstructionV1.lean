import Mathlib

/-!
# Paper B: the lower bound's divergence demand, from one output event

The adaptive lower bound needs, for a correct algorithm, a pair of worlds whose transcript
laws are FAR apart.  The distance is read off one event of the output.  If the output event
`E` has probability at least `p` in the first world and at most `delta` in the second, then

    klDiv P Q  >=  p log(1/delta) - log 2.                                  (event_klDiv_ge)

The proof is Donsker-Varadhan for the two-valued function `f = log(1/delta) 1_E`, obtained
from Mathlib's tilted-measure identity (`integral_llr_tilted_right`) and Gibbs' inequality
for the tilted law -- no binary-entropy computation and no case `Q E = 0` to special-case:
if `P` is not absolutely continuous the divergence is `∞`, and otherwise the bound holds
as stated.  `Q E` enters only through `E_Q e^f = 1 + (1/delta - 1) Q E <= 2`.

Two consequences, in the shape the minimax interface consumes:

* `safe_pair_exists` -- the SAFE task does not get a fixed pair.  At a world `w0` a
  `delta`-correct answer avoids `w0` with probability `>= 1 - delta`, so by pigeonhole some
  `v != w0` receives probability `>= (1 - delta)/(m - 1)`, while in world `v` that answer is
  unsafe and has probability `<= delta`.  The pair is chosen from the algorithm's own output
  distribution, as the blueprint requires.
* `demand_of_small_delta` -- for `delta <= min (1/2) (2^(-4(m-1)))` the demand is at least
  `log(1/delta)/(4(m-1))`: deliberately conservative, uniform in `delta` on that interval.
-/

namespace CIGAMF.P13.PaperBObstruction

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Donsker-Varadhan for one function**: `∫ llr P Q dP >= E_P f - log E_Q exp f`. -/
theorem integral_llr_ge_dv (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hint : Integrable (llr P Q) P) (f : Ω → ℝ) (hfP : Integrable f P)
    (hfQ : Integrable (fun x => exp (f x)) Q) :
    ∫ x, f x ∂P - log (∫ x, exp (f x) ∂Q) ≤ ∫ x, llr P Q x ∂P := by
  haveI : IsProbabilityMeasure (Q.tilted f) := isProbabilityMeasure_tilted hfQ
  have hac : P ≪ Q.tilted f := hPQ.trans (absolutelyContinuous_tilted hfQ)
  have hint' := integrable_llr_tilted_right hPQ hfP hint hfQ
  have hgibbs := integral_llr_add_sub_measure_univ_nonneg hac hint'
  simp only [probReal_univ, add_sub_cancel_right] at hgibbs
  rw [integral_llr_tilted_right hPQ hfP hfQ hint] at hgibbs
  linarith

/-- **The event bound.**  An event of probability `p` under `P` and at most `delta` under
`Q` forces `klDiv P Q >= p log(1/delta) - log 2`. -/
theorem event_klDiv_ge (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set Ω) (hE : MeasurableSet E) (δ : ℝ) (hδ : 0 < δ) (hQE : Q.real E ≤ δ) :
    ENNReal.ofReal (P.real E * log (1 / δ) - log 2) ≤ klDiv P Q := by
  by_cases hPQ : P ≪ Q
  swap; · simp [hPQ]
  by_cases hint : Integrable (llr P Q) P
  swap; · simp [hint]
  rw [klDiv_of_ac_of_integrable hPQ hint]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [probReal_univ, add_sub_cancel_right]
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · -- then log(1/delta) <= 0 and the claimed bound is at most -log 2 <= 0 <= ∫ llr
    have hlog : log (1 / δ) ≤ 0 := by
      rw [one_div, log_inv]; exact neg_nonpos.mpr (log_nonneg hδ1)
    have hgibbs := integral_llr_add_sub_measure_univ_nonneg hPQ hint
    simp only [probReal_univ, add_sub_cancel_right] at hgibbs
    have hPE : 0 ≤ P.real E := measureReal_nonneg
    nlinarith [log_pos (by norm_num : (1 : ℝ) < 2), mul_nonpos_of_nonneg_of_nonpos hPE hlog]
  · set t := log (1 / δ) with ht
    have htpos : 0 < t := by rw [ht]; exact log_pos (by rw [lt_div_iff₀ hδ]; linarith)
    set f : Ω → ℝ := E.indicator (fun _ => t) with hf
    have hfm : Measurable f := measurable_const.indicator hE
    have hfb : ∀ x, |f x| ≤ t := by
      intro x
      by_cases hx : x ∈ E
      · simp [hf, hx, abs_of_pos htpos]
      · simp [hf, hx, htpos.le]
    have hfP : Integrable f P :=
      Integrable.of_bound hfm.aestronglyMeasurable t (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hfb x)
    have hexp : ∀ x, exp (f x) = 1 + E.indicator (fun _ => exp t - 1) x := by
      intro x
      by_cases hx : x ∈ E
      · simp [hf, hx]
      · simp [hf, hx]
    have hfQ : Integrable (fun x => exp (f x)) Q := by
      simp_rw [hexp]
      exact (integrable_const 1).add ((integrable_const _).indicator hE)
    have hdv := integral_llr_ge_dv P Q hPQ hint f hfP hfQ
    have hEf : ∫ x, f x ∂P = t * P.real E := by
      rw [hf, integral_indicator_const _ hE, smul_eq_mul, mul_comm]
    have hEexp : ∫ x, exp (f x) ∂Q = 1 + (exp t - 1) * Q.real E := by
      simp_rw [hexp]
      rw [integral_add (integrable_const 1) ((integrable_const _).indicator hE),
        integral_const, integral_indicator_const _ hE]
      simp [mul_comm]
    have hexpt : exp t = 1 / δ := by rw [ht, exp_log (by positivity)]
    have hle2 : 1 + (exp t - 1) * Q.real E ≤ 2 := by
      rw [hexpt]
      have hQnn : 0 ≤ Q.real E := measureReal_nonneg
      have h1 : (1 / δ - 1) * Q.real E ≤ (1 / δ) * δ := by
        have hd : 0 ≤ 1 / δ - 1 := by rw [sub_nonneg, le_div_iff₀ hδ]; linarith
        calc (1 / δ - 1) * Q.real E ≤ (1 / δ) * Q.real E :=
              mul_le_mul_of_nonneg_right (by linarith) hQnn
          _ ≤ (1 / δ) * δ := mul_le_mul_of_nonneg_left hQE (by positivity)
      have h2 : (1 / δ) * δ = 1 := by field_simp
      linarith
    have hpos : 0 < 1 + (exp t - 1) * Q.real E := by
      have : 0 ≤ (exp t - 1) * Q.real E :=
        mul_nonneg (by linarith [add_one_le_exp t]) measureReal_nonneg
      linarith
    have hlog2 : log (1 + (exp t - 1) * Q.real E) ≤ log 2 := log_le_log hpos hle2
    rw [hEf, hEexp] at hdv
    nlinarith [hdv, hlog2]

/-! ## The safe task's pair, chosen from the output -/

/-- **Pigeonhole on the output.**  If the answer avoids `w0` with probability at least
`1 - delta`, some other answer `v` receives at least `(1 - delta)/(m - 1)`. -/
theorem safe_pair_exists {m : ℕ} (hm : 2 ≤ m) (P : Measure Ω) [IsProbabilityMeasure P]
    (ans : Ω → Fin m) (hans : Measurable ans) (w0 : Fin m) (δ : ℝ)
    (hw0 : P.real {ω | ans ω = w0} ≤ δ) :
    ∃ v : Fin m, v ≠ w0 ∧ (1 - δ) / ((m : ℝ) - 1) ≤ P.real {ω | ans ω = v} := by
  classical
  by_contra hcon
  push Not at hcon
  have hmeas : ∀ v, MeasurableSet {ω | ans ω = v} := fun v => hans (measurableSet_singleton v)
  have htot : ∑ v, P.real {ω | ans ω = v} = 1 := by
    have hU : (⋃ v, {ω | ans ω = v}) = Set.univ := by ext ω; simp
    have hdisj : Pairwise (Function.onFun Disjoint fun v => {ω | ans ω = v}) := by
      intro a b hab
      exact Set.disjoint_left.mpr fun ω ha hb => hab (ha.symm.trans hb)
    have := measureReal_iUnion_fintype (μ := P) hdisj hmeas
    rw [hU, probReal_univ] at this
    exact this.symm
  have hsplit : ∑ v, P.real {ω | ans ω = v}
      = P.real {ω | ans ω = w0} + ∑ v ∈ Finset.univ.erase w0, P.real {ω | ans ω = v} := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w0)]
  have hrest : ∑ v ∈ Finset.univ.erase w0, P.real {ω | ans ω = v}
      < ∑ _v ∈ Finset.univ.erase w0, (1 - δ) / ((m : ℝ) - 1) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨⟨if w0.val = 0 then 1 else 0, by split_ifs <;> omega⟩, by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]
        split_ifs with h <;> omega⟩
    · intro v hv
      exact hcon v (Finset.ne_of_mem_erase hv)
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ w0), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hrest
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
  rw [hcast, mul_div_cancel₀ _ hm1] at hrest
  linarith

/-! ## From the event bound to the rate's demand -/

/-- **The demand, uniformly in `delta` on an explicit interval.**  For `m >= 2` and
`delta <= min (1/2) (2^(-4(m-1)))`, `((1-delta)/(m-1)) log(1/delta) - log 2 >=
log(1/delta) / (4(m-1))`. -/
theorem demand_of_small_delta (m : ℕ) (hm : 2 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hδm : δ ≤ (2 : ℝ) ^ (-(4 * ((m : ℝ) - 1)))) :
    log (1 / δ) / (4 * ((m : ℝ) - 1))
      ≤ (1 - δ) / ((m : ℝ) - 1) * log (1 / δ) - log 2 := by
  have hm1 : 0 < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hL : 4 * ((m : ℝ) - 1) * log 2 ≤ log (1 / δ) := by
    have h := log_le_log hδ hδm
    rw [Real.log_rpow (by norm_num)] at h
    rw [one_div, log_inv]
    linarith
  have hLnn : 0 ≤ log (1 / δ) := le_trans (by positivity) hL
  have hhalf : (1 / 2) * log (1 / δ) ≤ (1 - δ) * log (1 / δ) :=
    mul_le_mul_of_nonneg_right (by linarith) hLnn
  have key : log (1 / δ) / (4 * ((m : ℝ) - 1)) + log 2
      ≤ (1 / 2) * log (1 / δ) / ((m : ℝ) - 1) := by
    rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) hm1]
    nlinarith [hL, hLnn]
  have hstep : (1 / 2) * log (1 / δ) / ((m : ℝ) - 1) ≤ (1 - δ) / ((m : ℝ) - 1) * log (1 / δ) := by
    have hre : (1 - δ) / ((m : ℝ) - 1) * log (1 / δ) = (1 - δ) * log (1 / δ) / ((m : ℝ) - 1) := by
      ring
    rw [hre]
    exact div_le_div_of_nonneg_right hhalf hm1.le
  linarith

#print axioms integral_llr_ge_dv
#print axioms event_klDiv_ge
#print axioms safe_pair_exists
#print axioms demand_of_small_delta

end CIGAMF.P13.PaperBObstruction
