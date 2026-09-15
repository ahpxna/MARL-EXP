import «LeanD6MovingNuisanceRegretV1»
import «LeanD6GaussianOverlapV1»

/-! Allocation loss uses the infimum over actual same-cardinality alternative
worlds and all legal nuisance margins. Benchmark rates are explicit arguments;
this module does not silently assume the unproved phase-III oracle formula. -/
namespace CIGAMF.P13.D6AllocationRiskBridge
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationMargin CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.P13.D6MovingNuisanceRegret CIGAMF.P13.D6GaussianOverlap
noncomputable section
variable {n : ℕ}

def Admissible (A A' : Finset (I n)) (j : I n) (nu : ℝ) : Prop :=
  A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1

def valueSet (A : Finset (I n)) (j : I n) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : Set ℝ :=
  {v | ∃ A' nu, Admissible A A' j nu ∧ v=∑ e ∈ E,w e*information A A' j mu nu e}

def allocationValue (A : Finset (I n)) (j : I n) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : ℝ :=
  sInf (valueSet A j mu E w)

def benchmarkRegret (A : Finset (I n)) (j : I n) (mu G : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : ℝ :=
  max 0 (G-allocationValue A j mu E w)

lemma information_nonnegative (A A' : Finset (I n)) (j : I n) (mu nu : ℝ)
    (e : Measurement n) : 0 ≤ information A A' j mu nu e := by
  rw [information_eq_mean]
  positivity

lemma valueSet_bounded_below (A : Finset (I n)) (j : I n) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hw : ∀ e ∈ E,0 ≤ w e) : BddBelow (valueSet A j mu E w) := by
  refine ⟨0,?_⟩
  rintro v ⟨A',nu,h,hv⟩
  rw [hv]
  exact sum_nonneg (fun e he => mul_nonneg (hw e he) (information_nonnegative A A' j mu nu e))

theorem allocationValue_le_actual (A A' : Finset (I n)) (j : I n) (mu nu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hw : ∀ e ∈ E,0 ≤ w e) (ha : Admissible A A' j nu) :
    allocationValue A j mu E w ≤ ∑ e ∈ E,w e*information A A' j mu nu e := by
  exact csInf_le (valueSet_bounded_below A j mu E w hw) ⟨A',nu,ha,rfl⟩

/-- Actual infimum regrets inherit the dimension-free separation. -/
theorem actual_regret_separation (A : Finset (I n)) (j : I n) (q lam eps : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (heps : 0 ≤ eps) (hlo : eps ≤ 1-lam*(1+root q (scale q)))
    (hup : eps ≤ lam*(1+root q (scale q)))
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hn : ∑ e ∈ E,w e=1)
    (Gminus Gplus : ℝ) :
    Gminus+Gplus-2*rate q lam-eps^2 ≤
      benchmarkRegret A j ((1-lam)-eps) Gminus E w+
      benchmarkRegret A j ((1-lam)+eps) Gplus E w := by
  obtain ⟨A',nu,hne,hcard,hj',hnum,hnuplus,hbound⟩ :=
    moving_adversary_two_margin A j q lam eps hq hI hj hA hB heps hlo hup E w hl hw hn
  have hm := allocationValue_le_actual A A' j ((1-lam)-eps) (nu-eps) E w hw
    ⟨hne,hcard,hj',hnum,by linarith⟩
  have hp := allocationValue_le_actual A A' j ((1-lam)+eps) (nu+eps) E w hw
    ⟨hne,hcard,hj',by linarith,hnuplus⟩
  have hrm := le_max_right (0 : ℝ) (Gminus-allocationValue A j ((1-lam)-eps) E w)
  have hrp := le_max_right (0 : ℝ) (Gplus-allocationValue A j ((1-lam)+eps) E w)
  unfold benchmarkRegret
  linarith

/-- Exact Gaussian experiment risk for measurable/integrable allocation rules.
Connecting a general adaptive record to this scalar sufficient statistic is
still a separate theorem, and is not an assumption hidden in the conclusion. -/
theorem gaussian_allocation_risk_lower
    (A : Finset (I n)) (j : I n) (q lam eps a : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (heps : 0 ≤ eps) (hlo : eps ≤ 1-lam*(1+root q (scale q)))
    (hup : eps ≤ lam*(1+root q (scale q))) (ha : 0 ≤ a)
    (E : Finset (Measurement n)) (w : ℝ → Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ x e, e ∈ E → 0 ≤ w x e)
    (hn : ∀ x, ∑ e ∈ E,w x e=1) (Gminus Gplus : ℝ)
    (him : Integrable (fun x => gaussianPDFReal (-a) 1 x*
      benchmarkRegret A j ((1-lam)-eps) Gminus E (w x)))
    (hip : Integrable (fun x => gaussianPDFReal a 1 x*
      benchmarkRegret A j ((1-lam)+eps) Gplus E (w x))) :
    (Gminus+Gplus-2*rate q lam-eps^2)*standardTail a ≤
      max (∫ x, gaussianPDFReal (-a) 1 x*benchmarkRegret A j ((1-lam)-eps) Gminus E (w x))
        (∫ x, gaussianPDFReal a 1 x*benchmarkRegret A j ((1-lam)+eps) Gplus E (w x)) := by
  apply gaussian_max_risk_lower a ha _ _ _ him hip
  · intro x; exact le_max_left _ _
  · intro x; exact le_max_left _ _
  · intro x
    exact actual_regret_separation A j q lam eps hq hI hj hA hB heps hlo hup E (w x) hl
      (hw x) (hn x) Gminus Gplus

#print axioms allocationValue_le_actual
#print axioms actual_regret_separation
#print axioms gaussian_allocation_risk_lower
end
end CIGAMF.P13.D6AllocationRiskBridge
