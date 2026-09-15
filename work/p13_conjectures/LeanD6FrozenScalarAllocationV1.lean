import «LeanD6PhaseThreeSharpV1»

/-! Exact value of a scalar-B / B-on allocation whose weight is frozen while
mu changes. Covers all actual hidden alternatives, not only nearest swaps.
The displayed guard and nuisance constraints are explicit algebraic checks. -/
namespace CIGAMF.P13.D6FrozenScalarAllocation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationPrimalBridge
open CIGAMF.P13.D6AllocationPhaseThreeCore CIGAMF.P13.D6PhaseThreePrimal
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6ExpandedAllocation CIGAMF.P13.D6AllocationSharp
noncomputable section
variable {n : ℕ}

def p (q w : ℝ) := (1-w)/q
def beta (q w : ℝ) := (1-w)*(q-1)*w/(q*coefficient q w)
def delta (q w mu : ℝ) := w*(q-2)*(1-mu)/coefficient q w
def value (q w mu : ℝ) := (p q w*mu^2+beta q w*(1-mu)^2)/2

theorem frozen_completed_square (q w mu u : ℝ) (hq : q ≠ 0)
    (hc : coefficient q w ≠ 0) :
    mixedLoss q mu w 1 u=2*value q w mu+
      coefficient q w*(u-((1-mu)+delta q w mu))^2 := by
  unfold mixedLoss value p beta delta
  field_simp [hq,hc]
  unfold coefficient
  field_simp [hq]
  <;> ring

theorem frozen_all_distances_lower (q w mu d u : ℝ) (hq : 3 ≤ q)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < coefficient q w)
    (hd : d=1 ∨ 2 ≤ d) (hdq : d ≤ q)
    (guard : beta q w*(1-mu)^2 ≤ p q w*mu^2) :
    2*value q w mu ≤ mixedLoss q mu w d u := by
  rcases hd with hd | hd
  · rw [hd,frozen_completed_square q w mu u (by linarith) (ne_of_gt hc)]
    exact le_add_of_nonneg_right (mul_nonneg hc.le (sq_nonneg _))
  · have hp : 0 < q := by linarith
    have h1 : 0 ≤ (1-w)*(q-d)*(u-(1-mu))^2 := by positivity
    have h2 : 0 ≤ w*((1-mu)*(q-d-1)+(1-mu)*d-(q-d-1)*u)^2 := by positivity
    have h3 : 0 ≤ (1-w)*(d-2)*mu^2 := by positivity
    have hb : 2*value q w mu ≤ 2*(1-w)*mu^2/q := by
      calc
        2*value q w mu = p q w*mu^2+beta q w*(1-mu)^2 := by unfold value; ring
        _ ≤ 2*p q w*mu^2 := by linarith only [guard]
        _ = 2*(1-w)*mu^2/q := by unfold p; ring
    apply hb.trans
    unfold mixedLoss
    apply (div_le_iff₀ hp).mpr
    have he : ((1-w)*(d*mu^2+(q-d)*(u-(1-mu))^2)/q+
        w*((1-mu)*(q-1)-(q-d-1)*u)^2)*q=
        (1-w)*d*mu^2+(1-w)*(q-d)*(u-(1-mu))^2+
          q*w*((1-mu)*(q-1)-(q-d-1)*u)^2 := by
      field_simp [ne_of_gt hp]
      <;> ring
    rw [he]
    have h4 : 0 ≤ q*w*((1-mu)*(q-1)-(q-d-1)*u)^2 := by positivity
    nlinarith

/-- A literal one-swap world has distance exactly one. -/
lemma swapped_distance_one (A : Finset (I n)) (j a b : I n)
    (ha : a ∈ A) (hb : b ∈ others A j) : (A \ swapped A a b).card=1 := by
  have hbA := (others_not_mem A j b hb).1
  have hab : a ≠ b := by intro h; subst b; exact hbA ha
  have he : A \ swapped A a b={a} := by
    ext i
    by_cases hi : i=a
    · subst i
      simp [swapped,ha,hab]
    · by_cases hia : i ∈ A <;> simp [swapped,hi,hia]
  rw [he,card_singleton]

/-- The frozen design's actual infimum is a quadratic in mu. No optimality
claim is needed for the frozen allocation away from its design margin. -/
theorem frozen_actual_value (A : Finset (I n)) (j : I n) (q w mu : ℝ)
    (hq : 3 ≤ q) (hw : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < coefficient q w)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (guard : beta q w*(1-mu)^2 ≤ p q w*mu^2)
    (hnu0 : 0 ≤ mu-delta q w mu) (hnu1 : mu-delta q w mu ≤ 1) :
    allocationValue A j mu (queries A j) (weights A j q w)=value q w mu := by
  have ha0 : A.Nonempty := card_pos.mp (by exact_mod_cast (show (0:ℝ)<A.card by linarith))
  have hb0 : (others A j).Nonempty := card_pos.mp
    (by exact_mod_cast (show (0:ℝ)<(others A j).card by linarith))
  obtain ⟨a,ha⟩ := ha0
  obtain ⟨b,hb⟩ := hb0
  have had : Admissible A (swapped A a b) j (mu-delta q w mu) :=
    ⟨swapped_ne A j a b hb,swapped_card A j a b ha hb,
      swapped_j_not A j a b hj hb,hnu0,hnu1⟩
  have hp := distribution A j q w (by linarith) hw hw1 hB
  have he := actual_phase_information A (swapped A a b) j q w mu (mu-delta q w mu)
    hj had.2.2.1 had.2.1 hB
  rw [swapped_distance_one A j a b ha hb,Nat.cast_one,
    frozen_completed_square q w mu (1-(mu-delta q w mu)) (by linarith) (ne_of_gt hc)] at he
  have hu : 1-(mu-delta q w mu)-((1-mu)+delta q w mu)=0 := by ring
  rw [hu,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,add_zero] at he
  have hev : (∑ e ∈ queries A j,weights A j q w e*information A (swapped A a b) j mu
      (mu-delta q w mu) e)=value q w mu := by linarith
  apply le_antisymm
  · exact (allocationValue_le_actual A (swapped A a b) j mu (mu-delta q w mu) _ _
      (fun e _ => hp.2.1 e) had).trans_eq hev
  · apply le_csInf (s := valueSet A j mu (queries A j) (weights A j q w))
      ⟨_,swapped A a b,mu-delta q w mu,had,rfl⟩
    rintro v ⟨A',nu,h,rfl⟩
    have hd := alternative_distance_bounds A A' j q h.2.2.1 h.2.1 h.1 hB
    have hdN : 1 ≤ (A \ A').card := by exact_mod_cast hd.1
    have hcase : ((A \ A').card:ℝ)=1 ∨ 2 ≤ ((A \ A').card:ℝ) := by
      rcases Nat.eq_or_lt_of_le hdN with h | h
      · left; exact_mod_cast h.symm
      · right; exact_mod_cast h
    have hlow := frozen_all_distances_lower q w mu (A \ A').card (1-nu) hq hw hw1 hc hcase hd.2 guard
    rw [← actual_phase_information A A' j q w mu nu hj h.2.2.1 h.2.1 hB] at hlow
    linarith

/-- Exact local expansion, with a known nonnegative quadratic remainder when
0 <= w <= 1. Connecting this quadratic to the oracle derivative is separate. -/
theorem frozen_local_expansion (q w mu eps : ℝ) :
    value q w (mu+eps)=value q w mu+
      (p q w*mu-beta q w*(1-mu))*eps+(p q w+beta q w)*eps^2/2 := by
  unfold value
  ring

#print axioms frozen_completed_square
#print axioms frozen_all_distances_lower
#print axioms frozen_actual_value
#print axioms frozen_local_expansion
end
end CIGAMF.P13.D6FrozenScalarAllocation
