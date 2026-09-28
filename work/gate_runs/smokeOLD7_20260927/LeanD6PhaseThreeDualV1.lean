import «LeanD6AllocationPhaseThreeFeasibleV1»
import «LeanD6AllocationMarginSharpV1»

/-! A dual certificate over every actual legal scalar and joint query in phase
III. The same adjacent adversary is selected after the whole allocation. -/
namespace CIGAMF.P13.D6PhaseThreeDual
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationPrimalBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.P13.D6AllocationMargin CIGAMF.P13.D6AllocationMarginSharp
open CIGAMF.P13.D6AllocationPhaseThreeCore
open CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible
open CIGAMF.P13.D6AllocationMarginRegion
noncomputable section
variable {n : ℕ}

theorem endpoint_order (q z : ℝ) (hq : 3 ≤ q) (hz : 0 ≤ z)
    (hu : z ≤ root q (scale q)) :
    q*(1+z)^2 ≤ (q+1)*(1-(q-2)*z)^2 := by
  have hc := scale_properties q hq
  have hd : 0 < q-2+scale q := by linarith [hc.1]
  have hl := (le_div_iff₀ hd).mp hu
  have hleft : 0 ≤ scale q*(1+z) := mul_nonneg (by linarith [hc.1]) (by linarith)
  have hlinear : scale q*(1+z) ≤ 1-(q-2)*z := by linarith
  have hs := (sq_le_sq₀ hleft (le_trans hleft hlinear)).mpr hlinear
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ q+1 by linarith)
  have he := congrArg (fun t : ℝ => t*(1+z)^2) hc.2.2
  nlinarith [hm,he]

theorem joint_envelope (q z s t : ℝ) (hq : 3 ≤ q) (hz : 0 ≤ z)
    (hu : z ≤ root q (scale q)) (hsmall : 4*q*z ≤ 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ q) :
    dual q z 0 s t ≤ q*(q+1)*(1-(q-2)*z)^2 ∧
    dual q z 1 s t ≤ q*(q+1)*(1-(q-2)*z)^2 := by
  have ho := mul_le_mul_of_nonneg_left (endpoint_order q z hq hz hu)
    (show 0 ≤ q by linarith)
  have hA0 : dual q z 0 q 0 ≤ q*(q+1)*(1-(q-2)*z)^2 := by
    have he : dual q z 0 q 0=q^2*(1+z)^2 := by unfold dual; ring
    rw [he]
    nlinarith [ho]
  have hA1 : dual q z 1 q 0 ≤ q*(q+1)*(1-(q-2)*z)^2 := by
    have hp := mul_nonneg (show 0 ≤ q by linarith)
      (show 0 ≤ (q-1)*z^2+2*q*z from add_nonneg
        (mul_nonneg (by linarith) (sq_nonneg z)) (mul_nonneg (by linarith) hz))
    have he : dual q z 0 q 0-dual q z 1 q 0=q*((q-1)*z^2+2*q*z) := by unfold dual; ring
    linarith
  have hB1 : dual q z 1 0 q=q*(q+1)*(1-(q-2)*z)^2 := by unfold dual; ring
  have hB0 : dual q z 0 0 q ≤ q*(q+1)*(1-(q-2)*z)^2 := by
    have hp := mul_nonneg (show 0 ≤ q*(q+1)*z by positivity)
      (show 0 ≤ 2-(2*q-3)*z by nlinarith)
    have he : dual q z 1 0 q-dual q z 0 0 q=q*(q+1)*z*(2-(2*q-3)*z) := by unfold dual; ring
    linarith
  exact ⟨dual_envelope q z 0 s t _ hq hz hsmall (by norm_num) (by norm_num)
    hs ht hst hA0 hB0,
    dual_envelope q z 1 s t _ hq hz hsmall (by norm_num) (by norm_num)
      hs ht hst hA1 hB1.le⟩

theorem phase_nuisance (q mu : ℝ) (hq : 3 ≤ q)
    (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q) :
    0 < 1-mu ∧ 0 ≤ mu-shift q mu ∧ mu-shift q mu ≤ 1 ∧
      0 ≤ shift q mu/(1-mu) ∧ shift q mu/(1-mu) ≤ root q (scale q) ∧
      4*q*(shift q mu/(1-mu)) ≤ 1 := by
  have hb := phase_shift_bounds q mu hq hlo hup
  have hd : 0 < 1+Real.sqrt q := by positivity
  have hhigh : marginHigh q < 1 := (div_lt_one hd).mpr (by linarith)
  have hl : 0 < 1-mu := by linarith
  have hs : shift q mu ≤ mu := by nlinarith [hb.2.2.1,hb.2.2.2]
  refine ⟨hl,by linarith,by linarith [hb.2.1,hb.2.2.1],
    div_nonneg hb.2.2.1 hl.le,?_,?_⟩
  · apply (div_le_iff₀ hl).mpr
    have he := shift_le_boundary_tilt q mu hq (by linarith [hb.1]) hb.2.1 hlo
    simpa [tilt,mul_comm] using he
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hl).mpr
    simpa using hb.2.2.2

theorem actual_joint_bound (A G : Finset (I n)) (j : I n) (h : Bool) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (hsize : (G.card : ℝ) ≤ q) :
    2*(∑ a ∈ A,∑ b ∈ others A j,
      queryKL A (swapped A a b) G j h mu (mu-shift q mu)) ≤
        q*(q+1)*gammaTwice q mu (shift q mu) := by
  let z := shift q mu/(1-mu)
  have hn := phase_nuisance q mu hq hlo hup
  have hmu : 1-(1-mu)=mu := by ring
  have hnu : 1-(1-mu)*(1+z)=mu-shift q mu := by
    dsimp [z]
    field_simp [ne_of_gt hn.1]
    <;> ring
  have he : (∑ a ∈ A,∑ b ∈ others A j,
      queryKL A (swapped A a b) G j h mu (mu-shift q mu)) =
      4*(1-mu)^2*(∑ a ∈ A,∑ b ∈ others A j,
        queryKL A (swapped A a b) G j h (1/2) (1-(1+z)/2)) := by
    rw [mul_sum]
    apply sum_congr rfl; intro a ha
    rw [mul_sum]
    apply sum_congr rfl; intro b hb
    have hh := joint_homogeneity A (swapped A a b) G j h hj
      (swapped_j_not A j a b hj hb) hjG hG (1-mu) (1+z)
    simpa only [hmu,hnu] using hh
  rw [he]
  have he' := actual_dual_sum A G j h q z hj hA hB hjG hG
  have hcnt : ((G ∩ A).card : ℝ)+(G ∩ others A j).card ≤ q := by
    have hh : ((G ∩ A).card : ℝ)+(G ∩ others A j).card=G.card := by
      exact_mod_cast query_count_partition A G j hjG
    linarith
  have heq : 2*(4*(1-mu)^2*(∑ a ∈ A,∑ b ∈ others A j,
        queryKL A (swapped A a b) G j h (1/2) (1-(1+z)/2))) =
      (1-mu)^2*dual q z (bit h) (G ∩ A).card (G ∩ others A j).card := by
    nlinarith [congrArg (fun t : ℝ => (1-mu)^2*t) he']
  rw [heq]
  have hb := joint_envelope q z (G ∩ A).card (G ∩ others A j).card hq
    hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2 (by positivity) (by positivity) hcnt
  have hb' : dual q z (bit h) (G ∩ A).card (G ∩ others A j).card ≤
      q*(q+1)*(1-(q-2)*z)^2 := by
    cases h <;> simp only [bit_false,bit_true] <;> first | exact hb.1 | exact hb.2
  have hm := mul_le_mul_of_nonneg_left hb' (sq_nonneg (1-mu))
  have hbal := balance q mu hq (by linarith [(phase_shift_bounds q mu hq hlo hup).1])
    (phase_shift_bounds q mu hq hlo hup).2.1
  have hzid : (1-mu)^2*(1-(q-2)*z)^2=((1-mu)-(q-2)*shift q mu)^2 := by
    dsimp [z]
    field_simp [ne_of_gt hn.1]
    <;> ring
  have htarget : (1-mu)^2*(q*(q+1)*(1-(q-2)*z)^2) =
      q*(q+1)*gammaTwice q mu (shift q mu) := by
    calc
      _ = (q+1)*(q*((1-mu)-(q-2)*shift q mu)^2) := by rw [← hzid]; ring
      _ = _ := by rw [hbal]; unfold gammaTwice; field_simp [show q ≠ 0 by linarith]
  exact htarget ▸ hm

theorem actual_scalar_bound (A : Finset (I n)) (j i : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    2*(∑ a ∈ A,∑ b ∈ others A j,
      scalarKL A (swapped A a b) j i mu (mu-shift q mu)) ≤
        q*(q+1)*gammaTwice q mu (shift q mu) := by
  let z := shift q mu/(1-mu)
  have hn := phase_nuisance q mu hq hlo hup
  have hb := phase_shift_bounds q mu hq hlo hup
  have hmu : 1-(1-mu)=mu := by ring
  have hnu : 1-(1-mu)*(1+z)=mu-shift q mu := by
    dsimp [z]
    field_simp [ne_of_gt hn.1]
    <;> ring
  have hz : (1-mu)^2*z^2=(shift q mu)^2 := by
    dsimp [z]
    field_simp [ne_of_gt hn.1]
    <;> ring
  have he := actual_scalar_margin_sum A j i hj (1-mu) z
  rw [hmu,hnu,hA,hB] at he
  have he2 : (1-mu)^2*z^2=(shift q mu)^2 := hz
  simp only [mul_assoc] at he
  have he3 : (1-mu)^2*(z*z)=shift q mu*shift q mu := by nlinarith [hz]
  have ht : q*(q+1)*gammaTwice q mu (shift q mu) =
      (q+1)*(mu^2+(q-1)*(shift q mu)^2) := by
    unfold gammaTwice; field_simp [show q ≠ 0 by linarith]
  rw [ht,he]
  have hs : (mu-shift q mu)^2 ≤ mu^2 := by
    apply (sq_le_sq₀ hn.2.1 (by linarith [hb.1])).mpr
    linarith [hb.2.2.1]
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ q by linarith)
  have hsmall : shift q mu ≤ mu := by linarith [hn.2.1]
  have hshift : (shift q mu)^2 ≤ mu^2 :=
    (sq_le_sq₀ hb.2.2.1 (by linarith [hb.1])).mpr hsmall
  split_ifs
  · nlinarith [mul_nonneg (show 0 ≤ q^2-1 by nlinarith) (sq_nonneg (shift q mu))]
  · nlinarith [congrArg (fun t : ℝ => (q+1)*q*t) hz,
      mul_nonneg (show 0 ≤ q+1 by linarith) (sub_nonneg.mpr hshift)]
  · nlinarith [congrArg (fun t : ℝ => (q+1)*(q-1)*t) hz]

theorem measurement_bound (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (e : Measurement n) (he : Legal j q e) :
    2*(∑ a ∈ A,∑ b ∈ others A j,
      information A (swapped A a b) j mu (mu-shift q mu) e) ≤
        q*(q+1)*gammaTwice q mu (shift q mu) := by
  cases e with
  | inl i => exact actual_scalar_bound A j i q mu hq hlo hup hj hA hB
  | inr p => exact actual_joint_bound A p.1 j p.2 q mu hq hlo hup hj hA hB he.1 he.2.2 he.2.1

theorem allocation_upper (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hlegal : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hnorm : ∑ e ∈ E,w e=1) :
    ∃ a ∈ A,∃ b ∈ others A j,
      (∑ e ∈ E,w e*information A (swapped A a b) j mu (mu-shift q mu) e) ≤
        gammaTwice q mu (shift q mu)/2 := by
  let L := fun a b => ∑ e ∈ E,w e*information A (swapped A a b) j mu (mu-shift q mu) e
  have he : (∑ a ∈ A,∑ b ∈ others A j,L a b) =
      ∑ e ∈ E,w e*(∑ a ∈ A,∑ b ∈ others A j,
        information A (swapped A a b) j mu (mu-shift q mu) e) := by
    dsimp [L]; simp_rw [mul_sum]
    calc
      _ = ∑ a ∈ A,∑ e ∈ E,∑ b ∈ others A j,
          w e*information A (swapped A a b) j mu (mu-shift q mu) e := by
        apply sum_congr rfl; intro a ha; exact sum_comm
      _ = _ := sum_comm
  have hb : 2*(∑ a ∈ A,∑ b ∈ others A j,L a b) ≤
      q*(q+1)*gammaTwice q mu (shift q mu) := by
    rw [he,mul_sum]
    calc
      _ ≤ ∑ e ∈ E,w e*(q*(q+1)*gammaTwice q mu (shift q mu)) := by
        apply sum_le_sum; intro e he
        have hh := mul_le_mul_of_nonneg_left
          (measurement_bound A j q mu hq hlo hup hj hA hB e (hlegal e he)) (hw e he)
        nlinarith
      _ = _ := by rw [← sum_mul,hnorm,one_mul]
  have hAnon : A.Nonempty := card_pos.mp (by exact_mod_cast (show (0:ℝ) < A.card by linarith))
  have hBnon : (others A j).Nonempty := card_pos.mp
    (by exact_mod_cast (show (0:ℝ) < (others A j).card by linarith))
  have hs : (∑ a ∈ A,∑ b ∈ others A j,L a b) ≤
      ∑ _a ∈ A,∑ _b ∈ others A j,gammaTwice q mu (shift q mu)/2 := by
    simp only [sum_const,nsmul_eq_mul,hA,hB]
    linarith [hb]
  obtain ⟨a,ha,hal⟩ := exists_le_of_sum_le hAnon hs
  obtain ⟨b,hb,hbl⟩ := exists_le_of_sum_le hBnon hal
  exact ⟨a,ha,b,hb,hbl⟩

#print axioms endpoint_order
#print axioms joint_envelope
#print axioms phase_nuisance
#print axioms actual_joint_bound
#print axioms actual_scalar_bound
#print axioms measurement_bound
#print axioms allocation_upper
end
end CIGAMF.P13.D6PhaseThreeDual
