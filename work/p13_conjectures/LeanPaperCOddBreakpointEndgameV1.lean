import «LeanPaperCEndgameV1»

/-!
DRAFT ENDGAME — not compiled. This does not repeat the circular-window calculation.
It takes the existing odd_total_excess inequality to the ALL-PERMUTATIONS optimum,
with a UNIFORM gap below eta=1. Thus no per-size bisection, rational certificate,
compactness argument, or invalid 'pointwise strict implies infimum strict' is needed.

The upper direction still needs the previously assigned insertion/relabelled law.
OddEndpointData names precisely that remaining input; this file does NOT assert an
instance. Once supplied, odd_breakpoint_iff closes the general odd threshold.
-/
namespace CIGAMF.P13.PaperCOddBreakpointEndgame
open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndgame

variable {m : ℕ}

noncomputable def plusItem (m : ℕ) (hm : 3 ≤ m) : Fin m := ⟨m-1,by omega⟩

lemma plusItem_weight (m : ℕ) (hm : 3 ≤ m) : gFamily m (plusItem m hm)=3 := by
  simp [plusItem,gFamily,gN,show m-1 ≠ 0 from by omega]

lemma ranked_odd (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2=1) (σ : Perm m) :
    IsOddFamily (rankOf (gFamily m) σ) := by
  have hf : IsOddFamily (gFamily m) := by
    convert gFamily_isOddFamily (m-2) (by omega) (by omega) using 1 <;>
      simp [Nat.sub_add_cancel (by omega : 2 ≤ m)]
  refine ⟨fun i => gFamily_weights m (σ i),?_⟩
  change (∑ i,gFamily m (σ i)) = -1
  rw [Equiv.sum_comp σ]
  exact hf.total

/-- An ACTUAL labelled +3 item is enough; no positivity-set counting assumption is used. -/
lemma odd_rank_total (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2=1) (σ : Perm m) :
    2+2*(if plusItem m hm=σ ⟨m-1,by omega⟩ then (1:ℝ) else 0)
      ≤ totalExcess (rankOf (gFamily m) σ) := by
  classical
  let j := σ.symm (plusItem m hm)
  have hj3 : rankOf (gFamily m) σ ⟨j.val,j.isLt⟩=3 := by
    simpa [rankOf,j] using plusItem_weight m hm
  have h := odd_total_excess (by omega) hmo _ (ranked_odd m hm hmo σ)
    j.val j.isLt hj3
  have hi : (if plusItem m hm=σ ⟨m-1,by omega⟩ then (1:ℝ) else 0)
      ≤ (if 0 < rankOf (gFamily m) σ ⟨m-1,by omega⟩ then (1:ℝ) else 0) := by
    by_cases hp : plusItem m hm=σ ⟨m-1,by omega⟩
    · have hpos : 0 < rankOf (gFamily m) σ ⟨m-1,by omega⟩ := by
        change 0 < gFamily m (σ ⟨m-1,by omega⟩)
        rw [← hp,plusItem_weight]; norm_num
      simp [hp,hpos]
    · simp only [if_neg hp]; split_ifs <;> norm_num
  linarith

lemma budgets_eq_Ico (m : ℕ) : budgets m=Ico 1 m := by
  ext k; simp [budgets]; omega

lemma total_eq_sum_regret (m : ℕ) (hm : 3 ≤ m) (σ : Perm m) :
    totalExcess (rankOf (gFamily m) σ) =
      denom m * ∑ k ∈ budgets m,regret (gFamily m) σ (denom m) k := by
  rw [budgets_eq_Ico]
  unfold totalExcess
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  simp [regret,denom,show (m:ℝ)+4 ≠ 0 from by positivity]

/-- Summing across all budgets controls their maximum. No chosen construction in this step. -/
lemma objective_ge_mean_total (m : ℕ) (hm : 3 ≤ m) (P : Perm m → ℝ) (c : ℝ)
    (hc : c≤∑ σ,P σ*totalExcess (rankOf (gFamily m) σ)) :
    c/(denom m*((m:ℝ)-1)) ≤ objective m (by omega) P := by
  classical
  have hD : 0 < denom m := by unfold denom; positivity
  have hm1 : 0 < (m:ℝ)-1 := by have : (3:ℝ) ≤ m := by exact_mod_cast hm; linarith
  have heq : (∑ σ,P σ*totalExcess (rankOf (gFamily m) σ)) =
      denom m * ∑ k ∈ budgets m,∑ σ,P σ*regret (gFamily m) σ (denom m) k := by
    simp_rw [total_eq_sum_regret m hm, mul_sum]
    rw [sum_comm]
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [mul_sum]
    apply sum_congr rfl
    intro σ hσ
    ring
  have hmax : (∑ k ∈ budgets m,∑ σ,P σ*regret (gFamily m) σ (denom m) k)
      ≤ ((m:ℝ)-1)*objective m (by omega) P := by
    calc _ ≤ ∑ _k ∈ budgets m,objective m (by omega) P := by
            apply sum_le_sum; intro k hk; exact le_sup' _ hk
      _ = _ := by simp [budgets,Nat.cast_sub (by omega : 1 ≤ m)]; ring
  rw [heq] at hc
  rw [div_le_iff₀ (mul_pos hD hm1)]
  nlinarith [mul_le_mul_of_nonneg_left hmax hD.le]

lemma odd_mean_total (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2=1)
    (P : Perm m → ℝ) (hP : ∀ σ,0 ≤ P σ) (hP1 : ∑ σ,P σ=1) :
    2+2*(∑ σ,P σ*(if plusItem m hm=σ ⟨m-1,by omega⟩ then (1:ℝ) else 0))
      ≤ ∑ σ,P σ*totalExcess (rankOf (gFamily m) σ) := by
  have h := sum_le_sum (fun σ (_ : σ ∈ (univ : Finset (Perm m))) =>
    mul_le_mul_of_nonneg_left (odd_rank_total m hm hmo σ) (hP σ))
  convert h using 1
  simp only [mul_add,sum_add_distrib,← sum_mul,← mul_sum,hP1]
  ring

lemma last_plus_mass (m : ℕ) (hm : 3 ≤ m) (η : ℝ)
    (P : Perm m → ℝ) (hP : P ∈ FeasibleAt id η) :
    (1-η)/(m:ℝ) ≤
      ∑ σ,P σ*(if plusItem m hm=σ ⟨m-1,by omega⟩ then (1:ℝ) else 0) := by
  apply endpoint_last_lower (by omega) P id (plusItem m hm) (m:ℝ) η
    (by positivity) hP.2.1
  have h := (abs_le.mp (hP.2.2 (m-1) (by omega) (plusItem m hm))).2
  rw [Nat.cast_sub (by omega : 1 ≤ m)] at h
  norm_num at h
  linarith

/-- The uniform lower gap already lives on each concrete feasible law. -/
theorem odd_law_gap (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2=1) (η : ℝ)
    (P : Perm m → ℝ) (hP : P ∈ FeasibleAt id η) :
    freeValue m+2*(1-η)/((m:ℝ)*denom m*((m:ℝ)-1))
      ≤ objective m (by omega) P := by
  have hc := odd_mean_total m hm hmo P hP.1 hP.2.1
  have hmass := last_plus_mass m hm η P hP
  have hmean : 2+2*((1-η)/(m:ℝ)) ≤
      ∑ σ,P σ*totalExcess (rankOf (gFamily m) σ) := by linarith
  have h := objective_ge_mean_total m hm P _ hmean
  convert h using 1
  unfold freeValue denom
  field_simp
  ring

/-- A positive gap survives the infimum over the ENTIRE feasible game. -/
theorem odd_value_gap (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2=1) (η : ℝ) (hη : 0 ≤ η) :
    freeValue m+2*(1-η)/((m:ℝ)*denom m*((m:ℝ)-1)) ≤ value m (by omega) η := by
  exact value_lower m hm η _ hη (fun P hP => odd_law_gap m hm hmo η P hP)

lemma odd_free_lower (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2=1)
    (P : Perm m → ℝ) (hP : ∀ σ,0 ≤ P σ) (hP1 : ∑ σ,P σ=1) :
    freeValue m ≤ objective m (by omega) P := by
  have hi : 0≤∑ σ,P σ*(if plusItem m hm=σ ⟨m-1,by omega⟩ then (1:ℝ) else 0) := by
    apply sum_nonneg; intro σ hσ
    exact mul_nonneg (hP σ) (by split_ifs <;> norm_num)
  have h := odd_mean_total m hm hmo P hP hP1
  exact objective_ge_mean_total m hm P 2 (by linarith)

/-- OPEN input from the assigned insertion + uniform-within-type relabelling join.
Supply actual item marginals at ALL k, not only type counts or endpoints. m=3 has no +1
items; skip its empty type rather than dividing by its zero multiplicity. -/
structure OddEndpointData (m : ℕ) (hm : 3 ≤ m) where
  endpoint : Perm m → ℝ
  endpoint_band : endpoint ∈ FeasibleAt id 1
  endpoint_value : objective m (by omega) endpoint ≤ freeValue m

/-- The general odd breakpoint. Lower direction is unconditional; the remaining upstream
obligation is exactly an actual endpoint witness. No family of Farkas certificates needed. -/
theorem odd_breakpoint_iff (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2=1)
    (E : OddEndpointData m hm) (η : ℝ) (hη : 0 ≤ η) :
    value m (by omega) η=freeValue m ↔ 1 ≤ η := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  constructor
  · intro heq
    by_contra hη1
    have hpos : 0 < 2*(1-η)/((m:ℝ)*denom m*((m:ℝ)-1)) := by
      have : η < 1 := lt_of_not_ge hη1
      unfold denom; positivity
    have h := odd_value_gap m hm hmo η hη
    rw [heq] at h
    linarith
  · intro hη1
    apply le_antisymm
    · have hPf := feasible_mono (id : Perm m → _) 1 η (by omega) hη1 E.endpoint_band
      exact (value_le_witness m hm η _ hPf).trans E.endpoint_value
    · exact value_lower m hm η _ hη
        (fun P hP => odd_free_lower m hm hmo P hP.1 hP.2.1)

/-- Discharges the target left explicit by CEndgame once all endpoint laws are supplied. -/
theorem odd_finish (E : ∀ s : ℕ, OddEndpointData (2*s+3) (by omega)) :
    OddBreakpointFinish := by
  intro s η hη
  exact odd_breakpoint_iff (2*s+3) (by omega) (by omega) (E s) η hη

#print axioms odd_rank_total
#print axioms odd_value_gap
#print axioms odd_free_lower
#print axioms odd_breakpoint_iff
#print axioms odd_finish
end CIGAMF.P13.PaperCOddBreakpointEndgame
