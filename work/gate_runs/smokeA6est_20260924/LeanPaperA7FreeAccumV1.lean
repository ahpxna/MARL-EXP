import «LeanPaperA7AccumulationV1»
import «LeanPaperA7TrackingV1»

/-!
# Paper A7: information accumulation without a box on the alternatives

`LeanPaperA7AccumulationV1.accumulation_window` transfers the average target's information to
the counts' design through the ALLOCATION modulus `J_lipschitz_in_allocation`, which needs a
box on the alternatives.  The paper's alternative set is unbounded, so here the transfer is
MULTIPLICATIVE and box-free:

* `Jval_scale_le` -- if `w >= c w'` coordinatewise (`c >= 0`), then `J(w) >= c J(w')`:
  the penalty is linear in the design and every term is nonnegative;
* `mult_of_additive` -- an additive tracking discrepancy `sum_e |N_e/t - avg_e| <= c/t` and a
  floor `avg_e >= m0 > 0` give `N_e/t >= (1 - c/(t m0)) avg_e`;
* `avgTarget_floor` -- with forcing `rho_s >= 1/sqrt(s+1)` toward the uniform design, the
  average target is at least `1/(K sqrt t)`, so the factor is `1 - cK/sqrt t -> 1`;
* `accumulation_window_free` -- on a window of good rounds,
  `J(N/t, theta) >= (1 - eps) (1/t) sum_{[n,t)} (1 - rho_s)(Gamma - eta_s)`.
-/

namespace CIGAMF.P13.PaperA7FreeAccum

open Finset
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7Accumulation
open CIGAMF.P13.PaperA7Tracking

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The design's information scales down at most linearly.** -/
theorem Jval_scale_le (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w w' μ : E → ℝ)
    (hw' : ∀ e, 0 ≤ w' e) (c : ℝ) (hc : 0 ≤ c) (hle : ∀ e, c * w' e ≤ w e) :
    c * Jval Alt w' μ ≤ Jval Alt w μ := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨ν, hν, rfl⟩
  have h1 : Jval Alt w' μ ≤ pen w' μ ν := csInf_le (Jval_bddBelow Alt w' μ hw') ⟨ν, hν, rfl⟩
  have h2 : c * pen w' μ ν ≤ pen w μ ν := by
    unfold pen
    rw [mul_div_assoc', mul_sum]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    refine sum_le_sum fun e _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hle e) (sq_nonneg _)
  calc c * Jval Alt w' μ ≤ c * pen w' μ ν := mul_le_mul_of_nonneg_left h1 hc
    _ ≤ pen w μ ν := h2

/-- **Additive tracking with a floor is multiplicative tracking.** -/
theorem mult_of_additive (N avg : E → ℝ) (t c m0 : ℝ) (ht : 0 < t) (hm0 : 0 < m0)
    (hc : 0 ≤ c) (havg : ∀ e, m0 ≤ avg e) (htrack : ∑ e, |N e / t - avg e| ≤ c / t) :
    ∀ e, (1 - c / (t * m0)) * avg e ≤ N e / t := by
  intro e
  have h1 : |N e / t - avg e| ≤ c / t :=
    le_trans (single_le_sum (f := fun e => |N e / t - avg e|) (fun e _ => abs_nonneg _)
      (mem_univ e)) htrack
  have h2 : avg e - c / t ≤ N e / t := by
    have := (abs_le.mp h1).1
    linarith
  have h3 : c / t ≤ c / (t * m0) * avg e := by
    have hq : c / t = c / (t * m0) * m0 := by field_simp
    rw [hq]
    exact mul_le_mul_of_nonneg_left (havg e) (by positivity)
  nlinarith

/-- **The forcing floor of the average target.** -/
theorem avgTarget_floor [Nonempty E] (w : ℕ → E → ℝ) (hw : ∀ s e, 0 ≤ w s e) (ρ : ℕ → ℝ)
    (hρ1 : ∀ s, ρ s ≤ 1) (hρf : ∀ s : ℕ, 1 / Real.sqrt ((s : ℝ) + 1) ≤ ρ s)
    (u : E → ℝ) (hu : ∀ e, u e = 1 / (Fintype.card E : ℝ)) (t : ℕ) (ht : 0 < t) (e : E) :
    1 / ((Fintype.card E : ℝ) * Real.sqrt t) ≤ avgTarget w ρ u t e := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hterm : ∀ s ∈ range t, (1 / (t : ℝ)) * (1 / Real.sqrt ((s : ℝ) + 1)
      * (1 / (Fintype.card E : ℝ))) ≤ (1 / (t : ℝ)) * target w ρ u s e := by
    intro s _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    unfold target
    rw [hu]
    have h0 : 0 ≤ (1 - ρ s) * w s e := mul_nonneg (by linarith [hρ1 s]) (hw s e)
    have : 1 / Real.sqrt ((s : ℝ) + 1) * (1 / (Fintype.card E : ℝ))
        ≤ ρ s * (1 / (Fintype.card E : ℝ)) :=
      mul_le_mul_of_nonneg_right (hρf s) (by positivity)
    linarith
  have hsum := sum_le_sum hterm
  have hS := sum_inv_sqrt_ge t
  unfold avgTarget
  refine le_trans ?_ hsum
  rw [← mul_sum, ← sum_mul]
  have hsqrt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htR
  have hts : (t : ℝ) = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt htR.le).symm
  calc 1 / ((Fintype.card E : ℝ) * Real.sqrt t)
      = 1 / (t : ℝ) * (Real.sqrt t * (1 / (Fintype.card E : ℝ))) := by
        rw [show (1 : ℝ) / t = 1 / (Real.sqrt t * Real.sqrt t) by rw [← hts]]
        field_simp
    _ ≤ 1 / (t : ℝ) * ((∑ s ∈ range t, 1 / Real.sqrt ((s : ℝ) + 1))
          * (1 / (Fintype.card E : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (by positivity)

/-- **Information accumulation on a window, box-free.** -/
theorem accumulation_window_free (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (θ : E → ℝ)
    (Γ : ℝ) (n t : ℕ) (hnt : n ≤ t) (ht : 0 < t)
    (w : ℕ → E → ℝ) (hw : ∀ s, IsAlloc (w s))
    (ρ : ℕ → ℝ) (hρ : ∀ s, 0 ≤ ρ s ∧ ρ s ≤ 1) (u : E → ℝ) (hu : IsAlloc u)
    (η : ℕ → ℝ) (hgood : ∀ s, n ≤ s → s < t → Γ - η s ≤ Jval Alt (w s) θ)
    (N : E → ℝ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (htrack : ∀ e, (1 - ε) * avgTarget w ρ u t e ≤ N e / t) :
    (1 - ε) * ((1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s))
      ≤ Jval Alt (fun e => N e / t) θ := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have htarget_nn : ∀ s e, 0 ≤ target w ρ u s e := by
    intro s e
    exact add_nonneg (mul_nonneg (by linarith [(hρ s).2]) ((hw s).1 e))
      (mul_nonneg (hρ s).1 (hu.1 e))
  have hround : ∀ s ∈ range t,
      (if n ≤ s then (1 - ρ s) * (Γ - η s) else 0) ≤ Jval Alt (target w ρ u s) θ := by
    intro s hs
    have hst : s < t := mem_range.mp hs
    split_ifs with hns
    · exact le_trans (mul_le_mul_of_nonneg_left (hgood s hns hst) (by linarith [(hρ s).2]))
        (forced_mixture Alt hne (w s) u θ (hw s).1 hu.1 (ρ s) (hρ s).1 (hρ s).2)
    · exact Jval_nonneg Alt hne _ θ (htarget_nn s)
  have hconc := J_concave_finite (range t) Alt hne (target w ρ u) (fun _ => 1 / (t : ℝ)) θ
    htarget_nn (fun _ _ => by positivity)
    (fun e => sum_nonneg fun s _ => mul_nonneg (by positivity) (htarget_nn s e))
  have hsum : ∑ s ∈ range t, (1 / (t : ℝ)) * (if n ≤ s then (1 - ρ s) * (Γ - η s) else 0)
      ≤ ∑ s ∈ range t, (1 / (t : ℝ)) * Jval Alt (target w ρ u s) θ :=
    sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hround s hs) (by positivity)
  have hIco : ∑ s ∈ range t, (1 / (t : ℝ)) * (if n ≤ s then (1 - ρ s) * (Γ - η s) else 0)
      = (1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s) := by
    rw [← mul_sum, ← sum_filter]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext s
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  have havg_nn : ∀ e, 0 ≤ avgTarget w ρ u t e :=
    fun e => sum_nonneg fun s _ => mul_nonneg (by positivity) (htarget_nn s e)
  have hacc : (1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s)
      ≤ Jval Alt (avgTarget w ρ u t) θ := by
    have : Jval Alt (avgTarget w ρ u t) θ
        = Jval Alt (fun e => ∑ s ∈ range t, (1 / (t : ℝ)) * target w ρ u s e) θ := rfl
    linarith
  have hscale := Jval_scale_le Alt hne (fun e => N e / t) (avgTarget w ρ u t) θ havg_nn
    (1 - ε) (by linarith) htrack
  calc (1 - ε) * ((1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s))
      ≤ (1 - ε) * Jval Alt (avgTarget w ρ u t) θ :=
        mul_le_mul_of_nonneg_left hacc (by linarith)
    _ ≤ Jval Alt (fun e => N e / t) θ := hscale

#print axioms Jval_scale_le
#print axioms mult_of_additive
#print axioms avgTarget_floor
#print axioms accumulation_window_free

end CIGAMF.P13.PaperA7FreeAccum
