import «LeanD6ReferenceLegalCountMinimumV1»
import «LeanD6ReferencePhaseValueV1»

/-! D05: actual fixed-world optimum and regret in the sufficient phase domain.
The strong domain (k-2)b >= 1 is explicit, not silently removed by D04.
Both legal attaining decisions are constructed. The next step is averaging
this actual regret over the endpoint prior, not assuming an ansatz is WLOG.
-/
namespace CIGAMF.P13.D6ReferencePhaseRegretBridge
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceRetainedOscillation CIGAMF.P13.D6ReferenceFullCountLoss
open CIGAMF.P13.D6ReferenceLegalCountMinimum
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

def correction (a b : ℝ) (u v : ℕ) : ℝ :=
  if u=0 ∧ v=0 then min a (2*b) else if u=0 ∧ v=1 then b else 0

def variableCost (a b rho : ℝ) (u v : ℕ) : ℝ :=
  (rho-2*b)*(v:ℝ)-(2*a-rho)*(u:ℝ)-correction a b u v

def commonConstant (a b : ℝ) (k : ℕ) : ℝ := a*(1+(k:ℝ))+b*((k:ℝ)-1)

theorem minimum_branch_dominates (a b : ℝ) (k u v : ℕ) (hk : 3 ≤ k)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) (hu : u ≤ k) (hv : v ≤ k-1)
    (huv : u+v ≤ k) (hstrong : 1 ≤ ((k:ℝ)-2)*b) :
    (1-a)-a*((k:ℝ)-(u:ℝ))-b*(((k-1:ℕ):ℝ)-(v:ℝ)) ≤
      if v < k-1 then -b else 0 := by
  have huc : (u:ℝ) ≤ k := by exact_mod_cast hu
  have huv' : (u:ℝ)+(v:ℝ) ≤ k := by exact_mod_cast huv
  have hkn : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  rw [hkn]
  have hprod : 0 ≤ (a-b)*((k:ℝ)-(u:ℝ)) := mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr huc)
  have htail : 0 ≤ b*((k:ℝ)-(u:ℝ)-(v:ℝ)) := mul_nonneg hb (by linarith)
  split_ifs <;> nlinarith

/-- The full D04 count loss specializes to a common constant plus variable cost. -/
theorem count_loss_phase (a b rho : ℝ) (k u v : ℕ) (hk : 3 ≤ k)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) (hu : u ≤ k) (hv : v ≤ k-1)
    (huv : u+v ≤ k) (hstrong : 1 ≤ ((k:ℝ)-2)*b) :
    countLoss a b rho k (k-1) u v = (commonConstant a b k+variableCost a b rho u v)/2 := by
  have hl := minimum_branch_dominates a b k u v hk ha hb hba hu hv huv hstrong
  unfold countLoss
  rw [min_eq_left hl]
  unfold upperCount commonConstant variableCost correction
  rw [Nat.cast_sub (by omega : 1 ≤ k),Nat.cast_one]
  ring

/-- A pointwise lower bound on EVERY feasible count pair. -/
theorem variable_lower (a b rho : ℝ) (h u v : ℕ)
    (hb : 0 ≤ b) (hba : b ≤ a) (hp : 0 ≤ rho-2*b) (hu : u ≤ h) :
    -max (min a (2*b)) ((2*a-rho)*(h:ℝ)) ≤ variableCost a b rho u v := by
  have he : b ≤ min a (2*b) := le_min hba (by linarith)
  have hmaxe := le_max_left (min a (2*b)) ((2*a-rho)*(h:ℝ))
  have hmaxr := le_max_right (min a (2*b)) ((2*a-rho)*(h:ℝ))
  have hu' : (u:ℝ) ≤ h := by exact_mod_cast hu
  have hun : (0:ℝ) ≤ u := Nat.cast_nonneg _
  have hvn : (0:ℝ) ≤ v := Nat.cast_nonneg _
  unfold variableCost correction
  split_ifs with h0 h1
  · rcases h0 with ⟨rfl,rfl⟩
    simp only [Nat.cast_zero,mul_zero,sub_self,zero_sub]
    linarith
  · rcases h1 with ⟨rfl,rfl⟩
    simp only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
    linarith
  · simp only [sub_zero]
    by_cases hr : 0 ≤ 2*a-rho
    · have hru := mul_le_mul_of_nonneg_left hu' hr
      have hpv := mul_nonneg hp hvn
      linarith
    · have hru := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hr) hun
      have hpv := mul_nonneg hp hvn
      linarith

theorem variable_zero (a b rho : ℝ) : variableCost a b rho 0 0 = -min a (2*b) := by
  simp [variableCost,correction]

theorem variable_all_A (a b rho : ℝ) (h : ℕ) (hh : 1 ≤ h) :
    variableCost a b rho h 0 = -(2*a-rho)*(h:ℝ) := by
  simp [variableCost,correction,show h ≠ 0 by omega]
  ring

def actualLoss (A T S : Finset (I n)) (j : I n) (rho t : ℝ) : ℝ :=
  productCompressionLoss (centeredWorld A T j rho t)
    (productResponse (bern t) (centeredWorld A T j rho t)) S

theorem actual_phase_loss (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A T S : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjT : j ∉ T)
    (k : ℕ) (hk : 3 ≤ k) (hAc : A.card=k) (hBc : (others A j).card=k-1) (hTc : T.card=k)
    (rho : ℝ) (hr : 1 ≤ rho) (hstrong : 1 ≤ ((k:ℝ)-2)*slopeBval t A j) :
    actualLoss A T S j rho t =
      (commonConstant (gateMass t A j) (slopeBval t A j) k+
        variableCost (gateMass t A j) (slopeBval t A j) rho
          ((T \ S) ∩ A).card ((T \ S) ∩ others A j).card)/2 := by
  have hB2 : 2 ≤ (others A j).card := by omega
  have ha := gateMass_bounds t ht0 ht1 A j (by omega)
  have hb := slopeBval_nonneg t ht0 ht1 A j hB2
  have hba := slope_order t ht1 A j hB2
  have hu : ((T \ S) ∩ A).card ≤ k := hAc ▸ Finset.card_le_card Finset.inter_subset_right
  have hv : ((T \ S) ∩ others A j).card ≤ k-1 := hBc ▸ Finset.card_le_card Finset.inter_subset_right
  have hsum : ((T \ S) ∩ A).card+((T \ S) ∩ others A j).card=(T \ S).card := by
    exact_mod_cast card_split A (T \ S) j (fun h => hjT (Finset.mem_sdiff.mp h).1)
  have hd : (T \ S).card ≤ k := hTc ▸ Finset.card_le_card Finset.sdiff_subset
  unfold actualLoss
  rw [actual_full_count_loss t ht0 ht1 A T S j hjA hjT hB2 rho hr,hAc,hBc]
  exact count_loss_phase _ _ rho k _ _ hk ha.1 hb hba hu hv (by omega) hstrong

/-- Actual fixed-budget optimum, with empty-D and all-A-overlap witnesses. -/
theorem actual_optimum (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A T : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjT : j ∉ T)
    (k : ℕ) (hk : 3 ≤ k) (hAc : A.card=k) (hBc : (others A j).card=k-1) (hTc : T.card=k)
    (hroom : 2*T.card ≤ Fintype.card (I n)) (hh : 1 ≤ (T ∩ A).card)
    (rho : ℝ) (hr : 1 ≤ rho) (hp : 0 ≤ rho-2*slopeBval t A j)
    (hstrong : 1 ≤ ((k:ℝ)-2)*slopeBval t A j) :
    legalMinimum A T j rho t =
      (commonConstant (gateMass t A j) (slopeBval t A j) k-
        max (min (gateMass t A j) (2*slopeBval t A j))
          ((2*gateMass t A j-rho)*((T ∩ A).card:ℝ)))/2 := by
  have hB2 : 2 ≤ (others A j).card := by omega
  have hb := slopeBval_nonneg t ht0 ht1 A j hB2
  have hba := slope_order t ht1 A j hB2
  apply le_antisymm
  · have h0 := minVal_le (fun S : {S : Finset (I n) // S.card=T.card} =>
      actualLoss A T S.val j rho t) ⟨T,rfl⟩
    rw [actual_phase_loss t ht0 ht1 A T T j hjA hjT k hk hAc hBc hTc rho hr hstrong] at h0
    simp only [Finset.sdiff_self,Finset.empty_inter,Finset.card_empty,variable_zero] at h0
    obtain ⟨S,hSc,hSA,hSB⟩ := every_count_legal A T j hroom (T ∩ A).card 0 (le_refl _) (Nat.zero_le _)
    have h1 := minVal_le (fun S : {S : Finset (I n) // S.card=T.card} =>
      actualLoss A T S.val j rho t) ⟨S,hSc⟩
    rw [actual_phase_loss t ht0 ht1 A T S j hjA hjT k hk hAc hBc hTc rho hr hstrong,
      hSA,hSB,variable_all_A _ _ rho _ hh] at h1
    rcases le_total (min (gateMass t A j) (2*slopeBval t A j))
        ((2*gateMass t A j-rho)*((T ∩ A).card:ℝ)) with h | h
    · rw [max_eq_right h]
      change legalMinimum A T j rho t ≤ _ at h1
      linarith
    · rw [max_eq_left h]
      exact h0
  · apply le_minVal
    intro S
    change _ ≤ actualLoss A T S.val j rho t
    rw [actual_phase_loss t ht0 ht1 A T S.val j hjA hjT k hk hAc hBc hTc rho hr hstrong]
    have hl := variable_lower (gateMass t A j) (slopeBval t A j) rho (T ∩ A).card
      ((T \ S.val) ∩ A).card ((T \ S.val) ∩ others A j).card hb hba hp (omitted_count_le T S.val A)
    linarith

/-- Every legal or randomized decision can now be compared against an actual optimum. -/
theorem actual_regret (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A T S : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjT : j ∉ T)
    (k : ℕ) (hk : 3 ≤ k) (hAc : A.card=k) (hBc : (others A j).card=k-1) (hTc : T.card=k)
    (hroom : 2*T.card ≤ Fintype.card (I n)) (hh : 1 ≤ (T ∩ A).card)
    (rho : ℝ) (hr : 1 ≤ rho) (hp : 0 ≤ rho-2*slopeBval t A j)
    (hstrong : 1 ≤ ((k:ℝ)-2)*slopeBval t A j) :
    actualLoss A T S j rho t-legalMinimum A T j rho t =
      (variableCost (gateMass t A j) (slopeBval t A j) rho
        ((T \ S) ∩ A).card ((T \ S) ∩ others A j).card+
       max (min (gateMass t A j) (2*slopeBval t A j))
         ((2*gateMass t A j-rho)*((T ∩ A).card:ℝ)))/2 := by
  rw [actual_phase_loss t ht0 ht1 A T S j hjA hjT k hk hAc hBc hTc rho hr hstrong,
    actual_optimum t ht0 ht1 A T j hjA hjT k hk hAc hBc hTc hroom hh rho hr hp hstrong]
  ring

#print axioms minimum_branch_dominates
#print axioms count_loss_phase
#print axioms variable_lower
#print axioms actual_phase_loss
#print axioms actual_optimum
#print axioms actual_regret
end
end CIGAMF.P13.D6ReferencePhaseRegretBridge
