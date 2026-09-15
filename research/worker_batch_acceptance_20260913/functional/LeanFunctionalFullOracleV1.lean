import «LeanFunctionalIntervalOracleV1»

/-! Exact full-extrema oracle for two free relations with three actions.
The joint infimum ranges over interval position, width, and every ordered
expansion pair. It does not freeze the original extrema. -/
namespace CIGAMF.P13.FunctionalFullOracle
open scoped BigOperators
open Finset
open CIGAMF.P13.FunctionalExtremaSeparation CIGAMF.P13.FunctionalIntervalOracle
noncomputable section

def shiftedPair (theta : Row) (a b : Fin 3) (x y : ℝ) : Row :=
  fun i => if i=a then theta i+x else if i=b then theta i+y else theta i

lemma shifted_pair_energy (p theta : Row) (a b : Fin 3) (hab : a ≠ b) (x y : ℝ) :
    rowEnergy p theta (shiftedPair theta a b x y)=pairEnergy (p a) (p b) x y := by
  fin_cases a <;> fin_cases b <;>
    simp_all [shiftedPair,rowEnergy,pairEnergy,Fin.sum_univ_succ]
  <;> ring

lemma two_cell_weighted (p theta v : Row) (hp : ∀ a,0 ≤ p a)
    (a b : Fin 3) (hab : a ≠ b) :
    pairEnergy (p a) (p b) (v a-theta a) (v b-theta b) ≤ rowEnergy p theta v := by
  have h := sum_le_sum_of_subset_of_nonneg (s:={a,b}) (t:=univ) (by simp)
    (f:=fun i => p i*(v i-theta i)^2) (fun i _ _ => mul_nonneg (hp i) (sq_nonneg _))
  simp only [sum_pair hab] at h
  unfold pairEnergy rowEnergy
  linarith

def candidateValue (pi pj ti tj : Row) (ell z : ℝ) (a b : Fin 3) :=
  rowEnergy pi ti (fun i => project ell z (ti i))+
    openingCost (pj a) (pj b) (z-(tj a-tj b))

def oracleValues (pi pj ti tj : Row) : Set ℝ :=
  {v | ∃ ell z : ℝ,∃ a b : Fin 3,0 ≤ z ∧ a ≠ b ∧ v=candidateValue pi pj ti tj ell z a b}

def oracle (pi pj ti tj : Row) := sInf (oracleValues pi pj ti tj)

lemma oracle_nonempty (pi pj ti tj : Row) : (oracleValues pi pj ti tj).Nonempty :=
  ⟨candidateValue pi pj ti tj 0 0 0 1,0,0,0,1,le_rfl,by decide,rfl⟩

lemma candidate_nonneg (pi pj ti tj : Row) (hi : ∀ a,0 ≤ pi a) (hj : ∀ a,0 < pj a)
    (ell z : ℝ) (a b : Fin 3) : 0 ≤ candidateValue pi pj ti tj ell z a b := by
  unfold candidateValue
  apply add_nonneg (rowEnergy_nonneg _ _ _ hi)
  unfold openingCost
  have ha := hj a
  have hb := hj b
  positivity

/-- Every oracle candidate gives a concrete feasible full-extrema alternative. -/
theorem candidate_attainable (pi pj ti tj : Row) (hi : ∀ a,0 ≤ pi a) (hj : ∀ a,0 < pj a)
    (ell z : ℝ) (hz : 0 ≤ z) (a b : Fin 3) (hab : a ≠ b) :
    ∃ vi vj,capacity vi ≤ capacity vj ∧
      fullEnergy pi pj ti tj vi vj=candidateValue pi pj ti tj ell z a b := by
  let gap := z-(tj a-tj b)
  let x := max 0 gap*pj b/(pj a+pj b)
  let y := -(max 0 gap)*pj a/(pj a+pj b)
  let vi := fun i => project ell z (ti i)
  let vj := shiftedPair tj a b x y
  have hcost := pair_open_attained (pj a) (pj b) gap (hj a) (hj b)
  change gap ≤ x-y ∧ pairEnergy (pj a) (pj b) x y=openingCost (pj a) (pj b) gap at hcost
  have hva : vj a=tj a+x := by simp [vj,shiftedPair]
  have hvb : vj b=tj b+y := by simp [vj,shiftedPair,Ne.symm hab]
  have hupper : capacity vi ≤ z := (range_le_iff_interval vi z).mpr ⟨ell,fun i => project_mem ell z (ti i) hz⟩
  have hlower : z ≤ capacity vj := by
    apply le_trans _ (pair_le_capacity vj a b)
    rw [hva,hvb]
    dsimp [gap] at hcost
    linarith [hcost.1]
  refine ⟨vi,vj,hupper.trans hlower,?_⟩
  unfold fullEnergy candidateValue
  rw [shifted_pair_energy pj tj a b hab x y,hcost.2]

/-- For every full alternative, one oracle candidate costs no more. -/
theorem alternative_dominates_candidate (pi pj ti tj : Row)
    (hi : ∀ a,0 ≤ pi a) (hj : ∀ a,0 < pj a) (vi vj : Row)
    (halt : capacity vi ≤ capacity vj) :
    ∃ ell z : ℝ,∃ a b : Fin 3,0 ≤ z ∧ a ≠ b ∧
      candidateValue pi pj ti tj ell z a b ≤ fullEnergy pi pj ti tj vi vj := by
  let z := capacity vi
  have hz : 0 ≤ z := capacity_nonneg vi
  obtain ⟨ell,hinterval⟩ := (range_le_iff_interval vi z).mp le_rfl
  obtain ⟨a,b,hab,hpair⟩ := (range_ge_iff_pair vj z hz).mp halt
  have hs := (shrink_projection pi ti vi ell z hz hi hinterval).2
  have hg : z-(tj a-tj b) ≤ (vj a-tj a)-(vj b-tj b) := by linarith
  have he := (pair_open_lower (pj a) (pj b) _ _ _ (hj a) (hj b) hg).trans
    (two_cell_weighted pj tj vj (fun a => (hj a).le) a b hab)
  exact ⟨ell,z,a,b,hz,hab,add_le_add hs he⟩

/-- Equality of true alternative cost and the unrestricted-extrema oracle. -/
theorem full_oracle_equality (pi pj ti tj : Row) (hi : ∀ a,0 < pi a) (hj : ∀ a,0 < pj a) :
    fullCost pi pj ti tj=oracle pi pj ti tj := by
  have hb : BddBelow (costs pi pj ti tj) := by
    refine ⟨0,?_⟩
    rintro v ⟨vi,vj,_,rfl⟩
    exact add_nonneg (rowEnergy_nonneg _ _ _ (fun a => (hi a).le)) (rowEnergy_nonneg _ _ _ (fun a => (hj a).le))
  have ho : BddBelow (oracleValues pi pj ti tj) := by
    refine ⟨0,?_⟩
    rintro v ⟨ell,z,a,b,_,_,rfl⟩
    exact candidate_nonneg pi pj ti tj (fun a => (hi a).le) hj ell z a b
  apply le_antisymm
  · apply le_csInf (oracle_nonempty pi pj ti tj)
    rintro v ⟨ell,z,a,b,hz,hab,rfl⟩
    obtain ⟨vi,vj,hvalid,hcost⟩ := candidate_attainable pi pj ti tj (fun a => (hi a).le) hj ell z hz a b hab
    exact csInf_le hb ⟨vi,vj,hvalid,hcost.symm⟩
  · apply le_csInf (costs_nonempty pi pj ti tj)
    rintro v ⟨vi,vj,hvalid,rfl⟩
    obtain ⟨ell,z,a,b,hz,hab,hcost⟩ := alternative_dominates_candidate pi pj ti tj (fun a => (hi a).le) hj vi vj hvalid
    exact (csInf_le ho ⟨ell,z,a,b,hz,hab,rfl⟩).trans hcost

#print axioms shifted_pair_energy
#print axioms candidate_attainable
#print axioms alternative_dominates_candidate
#print axioms full_oracle_equality
end
end CIGAMF.P13.FunctionalFullOracle
