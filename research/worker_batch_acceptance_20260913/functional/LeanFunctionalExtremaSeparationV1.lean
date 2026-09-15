import «LeanFunctionalPairFlipCostV1»

/-! Free response tables, known variances, positive precisions. Alternatives
include ties. These statements do not assume realizability by one shared F. -/
namespace CIGAMF.P13.FunctionalExtremaSeparation
open scoped BigOperators
open Finset
noncomputable section
abbrev Row := Fin 3 → ℝ

def high (v : Row) := max (v 0) (max (v 1) (v 2))
def low (v : Row) := min (v 0) (min (v 1) (v 2))
def capacity (v : Row) := high v-low v

def rowEnergy (p theta v : Row) := (∑ a,p a*(v a-theta a)^2)/2

def fullEnergy (pi pj ti tj vi vj : Row) := rowEnergy pi ti vi+rowEnergy pj tj vj

def costs (pi pj ti tj : Row) : Set ℝ :=
  {c | ∃ vi vj,capacity vi ≤ capacity vj ∧ c=fullEnergy pi pj ti tj vi vj}

def fullCost (pi pj ti tj : Row) := sInf (costs pi pj ti tj)

def middleI : Row := ![0,1,1/2]
def runnerI : Row := ![0,1,3/4]
def originalJ : Row := ![0,1/2,1/4]
def ones : Row := ![1,1,1]
def cheapMiddle (eta : ℝ) : Row := ![1,1,eta]
def cheapMaximum (eta : ℝ) : Row := ![1,eta,1]
def middleWitness : Row := ![0,1/2,1]

def scalarMiddle : ℝ := (1/2)^2/(2*(2+2))
def scalarRunner (eta : ℝ) := eta/(8*(1+3*eta))

lemma high_mem (v : Row) : ∃ a,high v=v a := by
  unfold high
  rcases le_total (v 0) (max (v 1) (v 2)) with h | h
  · rw [max_eq_right h]
    rcases le_total (v 1) (v 2) with hh | hh
    · exact ⟨2,max_eq_right hh⟩
    · exact ⟨1,max_eq_left hh⟩
  · exact ⟨0,max_eq_left h⟩

lemma low_mem (v : Row) : ∃ a,low v=v a := by
  unfold low
  rcases le_total (v 0) (min (v 1) (v 2)) with h | h
  · exact ⟨0,min_eq_left h⟩
  · rw [min_eq_right h]
    rcases le_total (v 1) (v 2) with hh | hh
    · exact ⟨1,min_eq_left hh⟩
    · exact ⟨2,min_eq_right hh⟩

lemma le_high (v : Row) (a : Fin 3) : v a ≤ high v := by
  fin_cases a <;> simp [high,le_max_iff]

lemma low_le (v : Row) (a : Fin 3) : low v ≤ v a := by
  fin_cases a <;> simp [low,min_le_iff]

lemma pair_le_capacity (v : Row) (a b : Fin 3) : v a-v b ≤ capacity v := by
  unfold capacity
  linarith [le_high v a,low_le v b]

lemma capacity_nonneg (v : Row) : 0 ≤ capacity v := by
  simpa using pair_le_capacity v 0 0

lemma rowEnergy_nonneg (p theta v : Row) (hp : ∀ a,0 ≤ p a) : 0 ≤ rowEnergy p theta v := by
  unfold rowEnergy
  exact div_nonneg (sum_nonneg (fun a _ => mul_nonneg (hp a) (sq_nonneg _))) (by norm_num)

lemma costs_nonempty (pi pj ti tj : Row) : (costs pi pj ti tj).Nonempty :=
  ⟨fullEnergy pi pj ti tj (fun _ => 0) (fun _ => 0),_,_,le_rfl,rfl⟩

lemma fullCost_nonneg (pi pj ti tj : Row) (hi : ∀ a,0 ≤ pi a) (hj : ∀ a,0 ≤ pj a) :
    0 ≤ fullCost pi pj ti tj := by
  apply le_csInf (costs_nonempty pi pj ti tj)
  rintro c ⟨vi,vj,_,rfl⟩
  exact add_nonneg (rowEnergy_nonneg _ _ _ hi) (rowEnergy_nonneg _ _ _ hj)

theorem cheap_middle_feasible : capacity middleI=1 ∧ capacity originalJ=1/2 ∧
    capacity middleI ≤ capacity middleWitness := by norm_num [capacity,high,low,middleI,originalJ,middleWitness,Matrix.cons_val_two]

theorem cheap_middle_cost (eta : ℝ) :
    fullEnergy ones (cheapMiddle eta) middleI originalJ middleI middleWitness=9*eta/32 := by
  norm_num [fullEnergy,rowEnergy,ones,cheapMiddle,middleI,originalJ,middleWitness,Fin.sum_univ_succ]
  ring

theorem cheap_middle_bound (eta : ℝ) (he : 0 < eta) :
    0 ≤ fullCost ones (cheapMiddle eta) middleI originalJ / scalarMiddle ∧
      fullCost ones (cheapMiddle eta) middleI originalJ / scalarMiddle ≤ 9*eta := by
  have hi : ∀ a,0 ≤ ones a := by intro a;fin_cases a <;> norm_num [ones]
  have hj : ∀ a,0 ≤ cheapMiddle eta a := by intro a;fin_cases a <;> simp [cheapMiddle];linarith
  have hn := fullCost_nonneg ones (cheapMiddle eta) middleI originalJ hi hj
  have hu : fullCost ones (cheapMiddle eta) middleI originalJ ≤ 9*eta/32 := by
    have hb : BddBelow (costs ones (cheapMiddle eta) middleI originalJ) := by
      refine ⟨0,?_⟩
      rintro c ⟨vi,vj,_,rfl⟩
      exact add_nonneg (rowEnergy_nonneg _ _ _ hi) (rowEnergy_nonneg _ _ _ hj)
    exact csInf_le hb ⟨middleI,middleWitness,cheap_middle_feasible.2.2,(cheap_middle_cost eta).symm⟩
  norm_num [scalarMiddle] at *
  constructor <;> linarith

lemma two_cell_energy (theta v : Row) (a b : Fin 3) (hab : a ≠ b) :
    ((v a-theta a)^2+(v b-theta b)^2)/2 ≤ rowEnergy ones theta v := by
  have h := sum_le_sum_of_subset_of_nonneg (s:={a,b}) (t:=univ) (by simp)
    (f:=fun i => (v i-theta i)^2) (fun i _ _ => sq_nonneg _)
  simp only [sum_pair hab] at h
  have he : rowEnergy ones theta v=(∑ i,(v i-theta i)^2)/2 := by
    unfold rowEnergy
    congr 1
    apply sum_congr rfl
    intro i _
    fin_cases i <;> simp [ones]
  rw [he]
  linarith

lemma runner_two_cell (eta : ℝ) (he : 0 ≤ eta) (v : Row) :
    ((v 0)^2+(v 2-3/4)^2)/2 ≤ rowEnergy (cheapMaximum eta) runnerI v := by
  simp [rowEnergy,cheapMaximum,runnerI,Fin.sum_univ_succ]
  nlinarith [mul_nonneg he (sq_nonneg (v 1-1))]

/-- Every alternative, not just one optimizer, pays a fixed positive energy. -/
theorem runner_up_uniform_lower (eta : ℝ) (he : 0 ≤ eta) (vi vj : Row)
    (halt : capacity vi ≤ capacity vj) :
    (1:ℝ)/128 ≤ fullEnergy (cheapMaximum eta) ones runnerI originalJ vi vj := by
  let z := capacity vj
  let u := max 0 (3/4-z)
  let v := max 0 (z-1/2)
  have hu : 0 ≤ u := le_max_left _ _
  have hv : 0 ≤ v := le_max_left _ _
  have huv : 1/4 ≤ u+v := by dsimp [u,v];linarith [le_max_right 0 (3/4-z),le_max_right 0 (z-1/2)]
  have hi : u^2/4 ≤ rowEnergy (cheapMaximum eta) runnerI vi := by
    have hp := pair_le_capacity vi 2 0
    have hc := runner_two_cell eta he vi
    by_cases hz : 3/4 ≤ z
    · have hu0 : u=0 := max_eq_left (by linarith)
      rw [hu0]
      have hn : 0 ≤ rowEnergy (cheapMaximum eta) runnerI vi := by
        apply rowEnergy_nonneg
        intro a;fin_cases a <;> simp [cheapMaximum,he]
      nlinarith
    · have hue : u=3/4-z := max_eq_right (by linarith)
      rw [hue]
      have hcross : 3/4-z ≤ vi 0-(vi 2-3/4) := by dsimp [z] at *;linarith
      nlinarith [sq_nonneg (vi 0+(vi 2-3/4))]
  have hj : v^2/4 ≤ rowEnergy ones originalJ vj := by
    by_cases hz : z ≤ 1/2
    · have hv0 : v=0 := max_eq_left (by linarith)
      rw [hv0]
      have hn : 0 ≤ rowEnergy ones originalJ vj := by
        apply rowEnergy_nonneg
        intro a;fin_cases a <;> norm_num [ones]
      nlinarith
    · obtain ⟨a,ha⟩ := high_mem vj
      obtain ⟨b,hb⟩ := low_mem vj
      have hab : a ≠ b := by
        intro h
        have hz0 : z=0 := by simp [z,capacity,ha,hb,h]
        linarith
      have hc := two_cell_energy originalJ vj a b hab
      have hg : originalJ a-originalJ b ≤ 1/2 := by fin_cases a <;> fin_cases b <;> norm_num [originalJ]
      have heq : z=vj a-vj b := by simp [z,capacity,ha,hb]
      have hve : v=z-1/2 := max_eq_right (by linarith)
      rw [hve]
      have hcross : z-1/2 ≤ (vj a-originalJ a)-(vj b-originalJ b) := by linarith
      nlinarith [sq_nonneg ((vj a-originalJ a)+(vj b-originalJ b))]
  unfold fullEnergy
  nlinarith [sq_nonneg (u-v)]

theorem runner_up_full_lower (eta : ℝ) (he : 0 < eta) :
    (1:ℝ)/128 ≤ fullCost (cheapMaximum eta) ones runnerI originalJ := by
  apply le_csInf (costs_nonempty _ _ _ _)
  rintro c ⟨vi,vj,halt,rfl⟩
  exact runner_up_uniform_lower eta he.le vi vj halt

/-- The scalar formula really is the old-extrema effective-variance proxy. -/
theorem scalar_runner_formula (eta : ℝ) (he : 0 < eta) :
    (1/2)^2/(2*((1+1/eta)+2))=scalarRunner eta := by
  unfold scalarRunner
  have he0 := ne_of_gt he
  have hd : 1+3*eta ≠ 0 := by positivity
  field_simp
  <;> ring

theorem runner_ratio_lower (eta : ℝ) (he : 0 < eta) :
    (1+3*eta)/(16*eta) ≤ fullCost (cheapMaximum eta) ones runnerI originalJ/scalarRunner eta := by
  have hs : 0 < scalarRunner eta := by unfold scalarRunner;positivity
  have h := div_le_div_of_nonneg_right (runner_up_full_lower eta he) hs.le
  have hid : (1/128:ℝ)/scalarRunner eta=(1+3*eta)/(16*eta) := by
    unfold scalarRunner
    field_simp
    <;> ring
  rwa [hid] at h

/-- No positive uniform multiplicative lower comparison exists. -/
theorem no_uniform_lower (c : ℝ) (hc : 0 < c) :
    ∃ eta : ℝ,0 < eta ∧ eta ≤ 1 ∧
      fullCost ones (cheapMiddle eta) middleI originalJ < c*scalarMiddle := by
  let eta := min 1 (c/18)
  have he : 0 < eta := lt_min (by norm_num) (by positivity)
  have hbound := (cheap_middle_bound eta he).2
  have heta : eta ≤ c/18 := min_le_right _ _
  have hs : scalarMiddle=(1:ℝ)/32 := by norm_num [scalarMiddle]
  refine ⟨eta,he,min_le_left _ _,?_⟩
  norm_num [scalarMiddle] at hbound ⊢
  nlinarith

/-- No finite positive uniform multiplicative upper comparison exists. -/
theorem no_uniform_upper (c : ℝ) (hc : 0 < c) :
    ∃ eta : ℝ,0 < eta ∧ eta ≤ 1 ∧
      c*scalarRunner eta < fullCost (cheapMaximum eta) ones runnerI originalJ := by
  let eta := 1/(256*(c+1))
  have hd : 0 < 256*(c+1) := by positivity
  have he : 0 < eta := by dsimp [eta];positivity
  have heta : eta ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hid : eta*(256*(c+1))=1 := by dsimp [eta];field_simp
  have hscalar : scalarRunner eta ≤ eta/8 := by
    unfold scalarRunner
    apply div_le_div_of_nonneg_left he.le (by norm_num)
    nlinarith
  refine ⟨eta,he,heta,?_⟩
  have hf := runner_up_full_lower eta he
  have hx := mul_le_mul_of_nonneg_left hscalar hc.le
  nlinarith

#print axioms scalar_runner_formula
#print axioms runner_ratio_lower
#print axioms no_uniform_lower
#print axioms no_uniform_upper
#print axioms cheap_middle_feasible
#print axioms cheap_middle_cost
#print axioms cheap_middle_bound
#print axioms runner_up_uniform_lower
#print axioms runner_up_full_lower
end
end CIGAMF.P13.FunctionalExtremaSeparation
