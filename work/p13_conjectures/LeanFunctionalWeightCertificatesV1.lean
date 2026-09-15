import «LeanFunctionalFullOracleV1»

/-! Allocation concavity and approximate-oracle gap certificates for the
same two-by-three free-table alternative set. No optimizer advantage is assumed. -/
namespace CIGAMF.P13.FunctionalWeightCertificates
open Finset
open scoped BigOperators
open CIGAMF.P13.FunctionalExtremaSeparation
noncomputable section

abbrev Table := Fin 2 → Row

def gradient (theta lambda : Table) (r : Fin 2) (a : Fin 3) := (lambda r a-theta r a)^2/2
def energy (p theta lambda : Table) := ∑ r,∑ a,p r a*gradient theta lambda r a
def legal (lambda : Table) : Prop := capacity (lambda 0) ≤ capacity (lambda 1)
def values (p theta : Table) : Set ℝ := {v | ∃ lambda,legal lambda ∧ v=energy p theta lambda}
def information (p theta : Table) := sInf (values p theta)
def Nonneg (p : Table) : Prop := ∀ r a,0 ≤ p r a

def dot (p g : Table) := ∑ r,∑ a,p r a*g r a

lemma energy_nonneg (p theta lambda : Table) (hp : Nonneg p) : 0 ≤ energy p theta lambda := by
  unfold energy gradient
  apply sum_nonneg
  intro r _
  apply sum_nonneg
  intro a _
  exact mul_nonneg (hp r a) (by positivity)

lemma values_nonempty (p theta : Table) : (values p theta).Nonempty :=
  ⟨energy p theta (fun _ _ => 0),(fun _ _ => 0),le_rfl,rfl⟩
lemma values_bdd (p theta : Table) (hp : Nonneg p) : BddBelow (values p theta) := by
  refine ⟨0,?_⟩
  rintro v ⟨lambda,_,rfl⟩
  exact energy_nonneg p theta lambda hp
lemma information_le (p theta lambda : Table) (hp : Nonneg p) (hl : legal lambda) :
    information p theta ≤ energy p theta lambda := csInf_le (values_bdd p theta hp) ⟨lambda,hl,rfl⟩

lemma energy_two_rows (p theta lambda : Table) :
    energy p theta lambda=fullEnergy (p 0) (p 1) (theta 0) (theta 1) (lambda 0) (lambda 1) := by
  simp only [energy,Fin.sum_univ_two,fullEnergy,rowEnergy,gradient]
  simp only [mul_div_assoc,sum_div]

/-- Connect the allocation value to the previously checked full-extrema cost. -/
theorem information_eq_fullCost (p theta : Table) :
    information p theta=fullCost (p 0) (p 1) (theta 0) (theta 1) := by
  unfold information fullCost
  congr 1
  ext v
  constructor
  · rintro ⟨lambda,hl,hv⟩
    exact ⟨lambda 0,lambda 1,hl,by simpa only [energy_two_rows] using hv⟩
  · rintro ⟨vi,vj,hl,hv⟩
    refine ⟨![vi,vj],hl,?_⟩
    simpa only [energy_two_rows,Matrix.cons_val_zero,Matrix.cons_val_one] using hv

/-- The infimum of linear information functions is concave on nonnegative
precisions. All alternatives in the same full-extrema set are retained. -/
theorem information_concave (p q theta : Table) (hp : Nonneg p) (hq : Nonneg q)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t*information p theta+(1-t)*information q theta ≤
      information (fun r a => t*p r a+(1-t)*q r a) theta := by
  apply le_csInf (values_nonempty _ _)
  rintro v ⟨lambda,hl,rfl⟩
  have he : energy (fun r a => t*p r a+(1-t)*q r a) theta lambda=
      t*energy p theta lambda+(1-t)*energy q theta lambda := by
    unfold energy
    simp only [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro a _
    ring
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left (information_le p theta lambda hp hl) ht0)
    (mul_le_mul_of_nonneg_left (information_le q theta lambda hq hl) (by linarith))

/-- A feasible eps-optimal oracle alternative gives an eps-supergradient. -/
theorem approximate_supergradient (p q theta lambda : Table) (hq : Nonneg q)
    (hl : legal lambda) (eps : ℝ) (heps : energy p theta lambda ≤ information p theta+eps) :
    information q theta ≤ information p theta+eps+
      dot (fun r a => q r a-p r a) (gradient theta lambda) := by
  have he : energy q theta lambda=energy p theta lambda+
      dot (fun r a => q r a-p r a) (gradient theta lambda) := by
    unfold energy dot
    simp only [← sum_add_distrib]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro a _
    ring
  calc
    information q theta ≤ energy q theta lambda := information_le q theta lambda hq hl
    _ = _ := he
    _ ≤ _ := by linarith

/-- A coordinatewise gradient cap yields a global simplex allocation gap.
The cap is checkable from the returned alternative, not an assumed optimum. -/
theorem simplex_gap_certificate (p q theta lambda : Table) (hq : Nonneg q)
    (hqsum : ∑ r,∑ a,q r a=1) (hl : legal lambda) (eps M : ℝ)
    (heps : energy p theta lambda ≤ information p theta+eps)
    (hM : ∀ r a,gradient theta lambda r a ≤ M) :
    information q theta ≤ information p theta+eps+M-energy p theta lambda := by
  have hg : dot q (gradient theta lambda) ≤ M := by
    calc
      _ ≤ ∑ r,∑ a,q r a*M := by
        apply sum_le_sum
        intro r _
        apply sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hM r a) (hq r a)
      _ = M := by simp only [← sum_mul,hqsum,one_mul]
  have hd : dot (fun r a => q r a-p r a) (gradient theta lambda)=
      dot q (gradient theta lambda)-energy p theta lambda := by
    unfold dot energy
    simp only [sub_mul,sum_sub_distrib]
  have h := approximate_supergradient p q theta lambda hq hl eps heps
  rw [hd] at h
  linarith

#print axioms information_eq_fullCost
#print axioms information_concave
#print axioms approximate_supergradient
#print axioms simplex_gap_certificate
end
end CIGAMF.P13.FunctionalWeightCertificates
