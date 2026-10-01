import «LeanSupportMultiTipGeometryV1»

/-! # Support: the normalized tolerance threshold of the multi-tip family.

`radius_formula` already gives the UNNORMALIZED radius,
`selectedRadius (components W) {j} = ((m-1)/2) * 1{j ∈ W}`. A tolerance `eps` is
only meaningful against the instance's own scale, so this file computes that
scale from `components` itself — not from an abstract radius table — and reads
off the exact threshold.

With `b = |W| >= 2` unsafe decisions and `a = m - b` safe ones:

* `osc_component` — component `j` of the geometry oscillates by `m-1` when
  `j ∈ W` and by `1` when `j ∉ W`. (Component `j` takes the value `0` at the
  anchor, `1` at every tip other than `j`, and `2-m` at tip `j`.)
* `modular_span_eq` — hence the normaliser is
      B_W = (sum_j osc) / 2 = (b(m-1) + a)/2.
* `normalized_radius_eq` — the normalized radius of a WRONG decision is exactly
      gamma = (m-1) / (b(m-1) + a),
  and of a safe decision exactly `0`.
* `no_query_needed` — if `eps >= gamma` then EVERY singleton decision is within
  tolerance, so no query is needed at all; and `query_needed_below` — if
  `eps < gamma` then a decision is within tolerance iff it is genuinely safe, so
  reaching the tolerance is exactly the problem of finding a safe decision.

That is an exact phase transition in `eps` for this family, at a point that
depends on `a` and `b`, not a constant.

## WHAT THIS DOES NOT ESTABLISH

- `b >= 2` is assumed throughout. At `b = 1` the component `j ∈ W` loses its
  value `1` (there is no other tip) and the oscillation is `m-2`, so the formula
  changes; that case is excluded, not covered.
- This is the normalisation and the threshold only. The active and passive
  minimax laws are NOT proved here, and neither is
  `V_active(k) = gamma * C(b,k+1)/C(a+b,k+1)` or
  `V_passive(N) = gamma * E[L_N/(a+L_N)]`. Those need the minimax theorems that
  `LeanSupportPassiveAnswerMultiplicityV1` explicitly does not contain; this file
  supplies only the `gamma` that both of them must be multiplied by, so that the
  two branches are finally quoted in the SAME unit.
- Equal tip probabilities are irrelevant here (no probability appears), but they
  are essential to those minimax laws, and dropping them changes the posterior —
  so this normalisation does not transfer to the unequal-mass family for free.
- Nothing here concerns noisy queries or an adaptive procedure.
-/

namespace CIGAMF.P13.SupportNormalizedTolerance
open Finset
open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportUnboundedObstruction
open CIGAMF.P13.SupportMultiTipGeometry
noncomputable section
variable {m : ℕ}

theorem component_value (W : Finset (Fin m)) (j : Fin m) (x : Points W) :
    components W j x = if h : x.isSome then
        (if j = ((x.get h).val) then 2-(m:ℝ) else 1) else 0 := by
  cases x with
  | none => simp [components, point]
  | some w =>
      simp only [components, point, Option.isSome_some, dif_pos, Option.get_some]
      unfold tip
      by_cases h : j = w.val
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring

/-- Every component oscillates by `m-1` on an unsafe decision and by `1` on a
safe one, provided at least two tips are present. -/
theorem osc_component (hm : 2 ≤ m) (W : Finset (Fin m)) (hb : 2 ≤ W.card)
    (j : Fin m) : osc (components W j) = if j ∈ W then (m:ℝ)-1 else 1 := by
  classical
  have hm' : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  -- a tip different from `j` always exists
  obtain ⟨w0, hw0, hw0j⟩ : ∃ w0 ∈ W, w0 ≠ j := by
    by_contra hc
    push_neg at hc
    have : W ⊆ {j} := fun x hx => by simp [hc x hx]
    have := Finset.card_le_card this
    simp at this; omega
  have hval : ∀ x : Points W, components W j x = 0 ∨ components W j x = 1
      ∨ components W j x = 2-(m:ℝ) := by
    intro x
    cases x with
    | none => left; simp [components, point]
    | some w =>
        simp only [components, point]
        unfold tip
        by_cases h : j = w.val
        · right; right; rw [if_pos h]; ring
        · right; left; rw [if_neg h]; ring
  have hone : components W j (some ⟨w0, hw0⟩) = 1 := by
    simp only [components, point]; unfold tip
    rw [if_neg (fun h => hw0j h.symm)]; ring
  have hmax : maxVal (components W j) = 1 := by
    refine le_antisymm (maxVal_le _ (fun x => ?_)) (hone ▸ le_maxVal _ _)
    rcases hval x with h | h | h <;> rw [h] <;> linarith
  by_cases hj : j ∈ W
  · have hlow : components W j (some ⟨j, hj⟩) = 2-(m:ℝ) := by
      simp only [components, point]; unfold tip; rw [if_pos rfl]; ring
    have hmin : minVal (components W j) = 2-(m:ℝ) := by
      have hle2 : minVal (components W j) ≤ 2-(m:ℝ) := by
        have h := minVal_le (components W j) (some ⟨j, hj⟩)
        rwa [hlow] at h
      refine le_antisymm hle2 (le_minVal _ (fun x => ?_))
      rcases hval x with h | h | h <;> rw [h] <;> linarith
    unfold osc; rw [hmax, hmin, if_pos hj]; ring
  · have hzero : components W j (none : Points W) = 0 := by simp [components, point]
    have hmin : minVal (components W j) = 0 := by
      have hle0 : minVal (components W j) ≤ 0 := by
        have h := minVal_le (components W j) (none : Points W)
        rwa [hzero] at h
      refine le_antisymm hle0 (le_minVal _ (fun x => ?_))
      cases x with
      | none => simp [components, point]
      | some w =>
          simp only [components, point]; unfold tip
          rw [if_neg (fun h => hj (by rw [h]; exact w.property))]; ring_nf; norm_num
    unfold osc; rw [hmax, hmin, if_neg hj]; ring

/-- The instance's own scale: `B_W = (b(m-1) + a)/2` with `b = |W|`, `a = m-b`. -/
theorem modular_span_eq (hm : 2 ≤ m) (W : Finset (Fin m)) (hb : 2 ≤ W.card) :
    (∑ j : Fin m, osc (components W j))
      = (W.card : ℝ)*((m:ℝ)-1) + ((m:ℝ) - W.card) := by
  classical
  have h1 : (univ.filter (fun j : Fin m => j ∈ W)) = W := by ext j; simp
  have hle : W.card ≤ m := by
    simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ W)
  have h2 : (univ.filter (fun j : Fin m => ¬ j ∈ W)).card = m - W.card := by
    have hcompl : (univ.filter (fun j : Fin m => ¬ j ∈ W)) = Wᶜ := by ext j; simp
    rw [hcompl, Finset.card_compl, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun j _ => osc_component hm W hb j), Finset.sum_ite,
    Finset.sum_const, Finset.sum_const, h1, h2, nsmul_eq_mul, nsmul_eq_mul]
  have hcast : ((m - W.card : ℕ) : ℝ) = (m:ℝ) - W.card := by
    push_cast [Nat.cast_sub hle]; ring
  rw [hcast]; ring

/-- The normalized radius of a wrong decision: the exact tolerance threshold. -/
theorem normalized_radius_eq (hm : 2 ≤ m) (W : Finset (Fin m)) (hb : 2 ≤ W.card)
    (j : Fin m) :
    selectedRadius (components W) {j} / ((∑ i : Fin m, osc (components W i))/2)
      = if j ∈ W then ((m:ℝ)-1)/((W.card:ℝ)*((m:ℝ)-1) + ((m:ℝ) - W.card)) else 0 := by
  have hm' : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hb' : (2:ℝ) ≤ (W.card:ℝ) := by exact_mod_cast hb
  have hle : W.card ≤ m := by
    simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ W)
  have hle' : (W.card:ℝ) ≤ (m:ℝ) := by exact_mod_cast hle
  have hden : (0:ℝ) < (W.card:ℝ)*((m:ℝ)-1) + ((m:ℝ) - W.card) := by nlinarith
  rw [radius_formula hm W j, modular_span_eq hm W hb]
  by_cases hj : j ∈ W
  · rw [if_pos hj, if_pos hj]
    field_simp
  · rw [if_neg hj, if_neg hj]
    simp

/-- Above the threshold no query is needed: every singleton decision already
meets the tolerance. -/
theorem no_query_needed (hm : 2 ≤ m) (W : Finset (Fin m)) (hb : 2 ≤ W.card)
    (eps : ℝ)
    (hEps : ((m:ℝ)-1)/((W.card:ℝ)*((m:ℝ)-1) + ((m:ℝ) - W.card)) ≤ eps)
    (j : Fin m) :
    selectedRadius (components W) {j} / ((∑ i : Fin m, osc (components W i))/2) ≤ eps := by
  have hm' : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hb' : (2:ℝ) ≤ (W.card:ℝ) := by exact_mod_cast hb
  have hle : W.card ≤ m := by
    simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ W)
  have hle' : (W.card:ℝ) ≤ (m:ℝ) := by exact_mod_cast hle
  have hden : (0:ℝ) < (W.card:ℝ)*((m:ℝ)-1) + ((m:ℝ) - W.card) := by nlinarith
  rw [normalized_radius_eq hm W hb j]
  by_cases hj : j ∈ W
  · rw [if_pos hj]; exact hEps
  · rw [if_neg hj]
    refine le_trans (div_nonneg (by linarith) hden.le) hEps

/-- Below the threshold the tolerance problem IS the problem of finding a safe
decision: a decision meets the tolerance exactly when it is genuinely safe. -/
theorem query_needed_below (hm : 2 ≤ m) (W : Finset (Fin m)) (hb : 2 ≤ W.card)
    (eps : ℝ) (hEps0 : 0 ≤ eps)
    (hEps : eps < ((m:ℝ)-1)/((W.card:ℝ)*((m:ℝ)-1) + ((m:ℝ) - W.card)))
    (j : Fin m) :
    selectedRadius (components W) {j} / ((∑ i : Fin m, osc (components W i))/2) ≤ eps
      ↔ j ∉ W := by
  rw [normalized_radius_eq hm W hb j]
  by_cases hj : j ∈ W
  · rw [if_pos hj]
    simp only [hj, not_true_eq_false, iff_false, not_le]
    exact hEps
  · rw [if_neg hj]
    simp [hj, hEps0]

#print axioms component_value
#print axioms osc_component
#print axioms modular_span_eq
#print axioms normalized_radius_eq
#print axioms no_query_needed
#print axioms query_needed_below

end
end CIGAMF.P13.SupportNormalizedTolerance
