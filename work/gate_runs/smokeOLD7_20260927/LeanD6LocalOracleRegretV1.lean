import «LeanD6PhaseThreeSharpV1»

/-! Regret relative to the actual supremum over every finite legal allocation,
not an externally supplied benchmark. Phase II and III rates are proved equal
to this supremum before substituting them into the local lower bound. -/
namespace CIGAMF.P13.D6LocalOracleRegret
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationMargin CIGAMF.P13.D6AllocationMarginSharp
open CIGAMF.P13.D6AllocationDistribution
open CIGAMF.P13.D6AllocationRiskBridge
open CIGAMF.P13.D6AllocationPhaseThreeFeasible
open CIGAMF.P13.D6AllocationMarginRegion CIGAMF.P13.D6ExpandedAllocation
noncomputable section
variable {n : ℕ}

def Feasible (j : I n) (q : ℝ) (E : Finset (Measurement n)) (w : Measurement n → ℝ) : Prop :=
  (∀ e ∈ E,Legal j q e) ∧ (∀ e ∈ E,0 ≤ w e) ∧ (∑ e ∈ E,w e)=1

def gameValues (A : Finset (I n)) (j : I n) (q mu : ℝ) : Set ℝ :=
  {v | ∃ E w,Feasible j q E w ∧ v=allocationValue A j mu E w}

def oracleValue (A : Finset (I n)) (j : I n) (q mu : ℝ) := sSup (gameValues A j q mu)

def oracleRegret (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) :=
  max 0 (oracleValue A j q mu-allocationValue A j mu E w)

theorem oracle_eq_of_attainment (A : Finset (I n)) (j : I n) (q mu g : ℝ)
    (attains : ∃ E w,Feasible j q E w ∧ allocationValue A j mu E w=g)
    (upper : ∀ E w,Feasible j q E w → allocationValue A j mu E w ≤ g) :
    oracleValue A j q mu=g := by
  obtain ⟨E,w,hf,he⟩ := attains
  have hm : g ∈ gameValues A j q mu := ⟨E,w,hf,he.symm⟩
  have hb : BddAbove (gameValues A j q mu) := by
    refine ⟨g,?_⟩
    rintro v ⟨E',w',hf',rfl⟩
    exact upper E' w' hf'
  apply le_antisymm
  · apply csSup_le ⟨g,hm⟩
    rintro v ⟨E',w',hf',rfl⟩
    exact upper E' w' hf'
  · exact le_csSup hb hm

theorem phase_two_allocation_value (A : Finset (I n)) (j : I n) (q lam : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    allocationValue A j (1-lam) (primalQueries A j) (primalWeight A j q)=rate q lam := by
  have hp := primal_distribution A j q hq hj hA hB
  obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,hu⟩ :=
    arbitrary_margin_allocation_upper A j q lam hq hI hj hA hB _ _ hp.1
      (fun e _ => hp.2.1 e) hp.2.2
  have ha : Admissible A A' j nu := ⟨hne,hcard,hj',hnu,hnu1⟩
  apply le_antisymm
  · exact le_trans (allocationValue_le_actual A A' j (1-lam) nu _ _
      (fun e _ => hp.2.1 e) ha) hu
  · apply le_csInf (s := valueSet A j (1-lam) (primalQueries A j) (primalWeight A j q))
      ⟨_,A',nu,ha,rfl⟩
    rintro v ⟨A'',nu',h,rfl⟩
    exact margin_distribution_lower A A'' j q lam nu' hq hI.1 hj h.2.2.1 h.2.1 h.1 hA hB

theorem phase_two_oracle (A : Finset (I n)) (j : I n) (q lam : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    oracleValue A j q (1-lam)=rate q lam := by
  have hp := primal_distribution A j q hq hj hA hB
  apply oracle_eq_of_attainment A j q (1-lam) (rate q lam)
  · exact ⟨_,_,⟨hp.1,(fun e _ => hp.2.1 e),hp.2.2⟩,
      phase_two_allocation_value A j q lam hq hI hj hA hB⟩
  · rintro E w ⟨hl,hw,hn⟩
    obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,hu⟩ :=
      arbitrary_margin_allocation_upper A j q lam hq hI hj hA hB E w hl hw hn
    exact le_trans (allocationValue_le_actual A A' j (1-lam) nu E w hw
      ⟨hne,hcard,hj',hnu,hnu1⟩) hu

theorem phase_three_oracle (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    oracleValue A j q mu=D6PhaseThreeSharp.rate q mu := by
  have hm := phase_mass_bounds q mu hq hlo hup
  have hp := D6PhaseThreePrimal.distribution A j q (D6AllocationPhaseThreeParameters.mass q mu)
    (by linarith) hm.1 (by linarith [hm.2]) hB
  apply oracle_eq_of_attainment A j q mu (D6PhaseThreeSharp.rate q mu)
  · exact ⟨_,_,⟨hp.1,(fun e _ => hp.2.1 e),hp.2.2⟩,
      D6PhaseThreeSharp.optimal_allocation_value A j q mu hq hlo hup hj hA hB⟩
  · rintro E w ⟨hl,hw,hn⟩
    exact D6PhaseThreeSharp.every_allocation_value_le A j q mu hq hlo hup hj hA hB E w hl hw hn

/-- Both losses use the actual oracle value. The two rates on the left are
certified optima on their respective phases, over every actual legal query. -/
theorem local_oracle_regret_separation (A : Finset (I n)) (j : I n) (q lam eps : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hminus : Interior q (lam+eps))
    (hpluslo : marginMax q ≤ (1-lam)+eps) (hplushi : (1-lam)+eps ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (heps : 0 ≤ eps) (hlo : eps ≤ 1-lam*(1+root q (scale q)))
    (hup : eps ≤ lam*(1+root q (scale q)))
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) (hf : Feasible j q E w) :
    rate q (lam+eps)+D6PhaseThreeSharp.rate q ((1-lam)+eps)-2*rate q lam-eps^2 ≤
      oracleRegret A j q ((1-lam)-eps) E w+oracleRegret A j q ((1-lam)+eps) E w := by
  have hm := phase_two_oracle A j q (lam+eps) hq hminus hj hA hB
  have hp := phase_three_oracle A j q ((1-lam)+eps) hq hpluslo hplushi hj hA hB
  have he : 1-(lam+eps)=(1-lam)-eps := by ring
  rw [he] at hm
  unfold oracleRegret
  rw [hm,hp]
  exact actual_regret_separation A j q lam eps hq hI hj hA hB heps hlo hup E w hf.1 hf.2.1 hf.2.2 _ _

#print axioms oracle_eq_of_attainment
#print axioms phase_two_allocation_value
#print axioms phase_two_oracle
#print axioms phase_three_oracle
#print axioms local_oracle_regret_separation
end
end CIGAMF.P13.D6LocalOracleRegret
