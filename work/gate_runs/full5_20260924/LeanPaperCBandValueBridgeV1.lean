import «LeanPaperCLawPushV1»

/-!
# Quantitative even-band obstruction on the actual ranking objective

Unlike the conditional endpoint-equality theorem, this bound takes only membership in
FeasibleAt. A UNIFORM positive gap survives passage to the infimum over all rankings.
This proves the obstruction side, not existence of a law attaining the breakpoint.
-/
namespace CIGAMF.P13.PaperCBandValueBridge
open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCBand
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCLawPush
variable {R : Type*} [Fintype R]

/-- Endpoint mass gives a quantitative lower bound at each band-feasible ranking law. -/
theorem maxRegret_ge_band (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 0)
    (P : R → ℝ) (perm : R → Equiv.Perm (Fin (n + 2))) (D η : ℝ) (hD : 0 < D)
    (hP : P ∈ FeasibleAt perm η)
    (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (h1 : 1 ∈ budgets) (h2 : n + 2 - 1 ∈ budgets) :
    4 * (1 - η) / (((n : ℝ) + 2) * D)
      ≤ maxRegret P (gFamily (n + 2)) perm D budgets hne := by
  classical
  have hmpos : 0 < n + 2 := by omega
  have hmR : 0 < (n : ℝ) + 2 := by positivity
  let big : R → ℝ := fun x =>
    heavy (rankOf (gFamily (n + 2)) (perm x) ⟨0, hmpos⟩)
      + heavy (rankOf (gFamily (n + 2)) (perm x) ⟨n + 2 - 1, by omega⟩)
  have hf : ∀ i ∈ heavySet (gFamily (n + 2)),
      (1 - η) / ((n : ℝ) + 2) ≤
        ∑ x, P x * (if i = perm x ⟨0, hmpos⟩ then (1 : ℝ) else 0) := by
    intro i _
    apply endpoint_first_lower hmpos P perm i ((n : ℝ) + 2) η hmR
    have h := (abs_le.mp (hP.2.2 1 (by omega) i)).1
    norm_num at h
    rw [one_div]
    linarith
  have hl : ∀ i ∈ heavySet (gFamily (n + 2)),
      (1 - η) / ((n : ℝ) + 2) ≤
        ∑ x, P x * (if i = perm x ⟨n + 2 - 1, by omega⟩ then (1 : ℝ) else 0) := by
    intro i _
    apply endpoint_last_lower hmpos P perm i ((n : ℝ) + 2) η hmR hP.2.1
    have h := (abs_le.mp (hP.2.2 (n + 2 - 1) (by omega) i)).2
    have hc : ((n + 2 - 1 : ℕ) : ℝ) = (n : ℝ) + 2 - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n + 2)]; push_cast; ring
    rw [hc] at h
    norm_num at h
    rw [show n + 2 - 1 = n + 1 from by omega]
    linarith [h]
  have hb : 4 * (1 - η) / ((n : ℝ) + 2) ≤ ∑ x, P x * big x :=
    hband_even_of_endpoint_band P
      (fun i x => if i = perm x ⟨0, hmpos⟩ then 1 else 0)
      (fun i x => if i = perm x ⟨n + 2 - 1, by omega⟩ then 1 else 0)
      big (heavySet (gFamily (n + 2))) ((n : ℝ) + 2) η hmR
      (by rw [gFamily_heavy_card n hn]; norm_num)
      (fun x => big_eq_sum_endpoints (gFamily (n + 2)) hmpos (perm x)) hf hl
  have hid := hid_on_regret (by omega : 1 < n + 2) (by omega : (n + 2) % 2 = 0)
    (gFamily (n + 2)) (gFamily_isEvenFamily n hn hpar) perm D (ne_of_gt hD)
  have heq : (∑ x, P x * (regret (gFamily (n + 2)) (perm x) D 1
      + regret (gFamily (n + 2)) (perm x) D (n + 2 - 1))) / 2
      = (∑ x, P x * big x) / D := by
    simp_rw [hid]
    change (∑ x, P x * (2 / D * big x)) / 2 = _
    rw [show (∑ x, P x * (2 / D * big x)) = (2 / D) * ∑ x, P x * big x by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring]
    ring
  have havg := avg_two_le_maxRegret P (gFamily (n + 2)) perm D budgets hne h1 h2
  rw [heq] at havg
  have hdiv : (4 * (1 - η) / ((n : ℝ) + 2)) / D ≤ (∑ x, P x * big x) / D := by
    have hDinv : (0 : ℝ) ≤ 1 / D := by positivity
    rw [div_eq_mul_one_div (4 * (1 - η) / ((n : ℝ) + 2)) D,
      div_eq_mul_one_div (∑ x, P x * big x) D]
    exact mul_le_mul_of_nonneg_right hb hDinv
  calc 4 * (1 - η) / (((n : ℝ) + 2) * D)
      = (4 * (1 - η) / ((n : ℝ) + 2)) / D := by rw [div_div]
    _ ≤ (∑ x, P x * big x) / D := hdiv
    _ ≤ _ := havg

/-- The quantitative bound survives the infimum; the global feasible set is inhabited. -/
theorem Vm_allPerm_ge_band (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 0)
    (D η : ℝ) (hD : 0 < D) (hη : 0 ≤ η)
    (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (h1 : 1 ∈ budgets) (h2 : n + 2 - 1 ∈ budgets) :
    4 * (1 - η) / (((n : ℝ) + 2) * D)
      ≤ Vm (gFamily (n + 2)) id D η budgets hne := by
  letI : NeZero (n + 2) := ⟨by omega⟩
  apply le_csInf ((allPerm_feasible_nonempty (n + 2) η hη).image _)
  rintro v ⟨P, hP, rfl⟩
  exact maxRegret_ge_band n hn hpar P id D η hD hP budgets hne h1 h2

/-- Uniform gap above the free benchmark, not a strict inequality lost under an infimum. -/
theorem Vm_allPerm_gap (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 0)
    (D η : ℝ) (hD : 0 < D) (hη : 0 ≤ η)
    (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (h1 : 1 ∈ budgets) (h2 : n + 2 - 1 ∈ budgets) :
    2 / (D * ((n : ℝ) + 1))
      + 4 / (((n : ℝ) + 2) * D) * ((n : ℝ) / (2 * ((n : ℝ) + 1)) - η)
      ≤ Vm (gFamily (n + 2)) id D η budgets hne := by
  have heq : 2 / (D * ((n : ℝ) + 1))
      + 4 / (((n : ℝ) + 2) * D) * ((n : ℝ) / (2 * ((n : ℝ) + 1)) - η)
      = 4 * (1 - η) / (((n : ℝ) + 2) * D) := by
    have h1n : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2n : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    <;> ring
  rw [heq]
  exact Vm_allPerm_ge_band n hn hpar D η hD hη budgets hne h1 h2

#print axioms maxRegret_ge_band
#print axioms Vm_allPerm_ge_band
#print axioms Vm_allPerm_gap
end CIGAMF.P13.PaperCBandValueBridge
