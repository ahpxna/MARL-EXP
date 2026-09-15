import «LeanD6AllocationPhaseThreeFeasibleV1»
import «LeanD6AllocationMarginV1»

/-! All-query dual for phase III. An adjacent-world mixture uses nuisance
nu = mu - shift. The same mixture bounds every legal measurement. -/
namespace CIGAMF.P13.D6AllocationPhaseThreeDual
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6ExpandedAllocation CIGAMF.P13.D6AllocationMargin
open CIGAMF.P13.D6AllocationPhaseThreeCore CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMarginRegion
noncomputable section
variable {n : ℕ}

/-- Below the old tilt, the anchored B endpoint dominates the A endpoint. -/
theorem endpoint_order (q z : ℝ) (hq : 3 ≤ q) (hz : 0 ≤ z) (hzz : z ≤ tilt q) :
    q*(1+z)^2 ≤ (q+1)*(1-(q-2)*z)^2 := by
  have hc := scale_properties q hq
  have ht := root_properties q _ hq hc.1 hc.2.1 hc.2.2
  change 0 < tilt q ∧ 4*q*tilt q ≤ 1 ∧
    (q+1)*(1-(q-2)*tilt q)^2=q*(1+tilt q)^2 at ht
  have hleft : (1+z)^2 ≤ (1+tilt q)^2 := by nlinarith
  have htpos : 0 ≤ 1-(q-2)*tilt q := by nlinarith [ht.1,ht.2.1]
  have horder : 1-(q-2)*tilt q ≤ 1-(q-2)*z := by nlinarith
  have hright : (1-(q-2)*tilt q)^2 ≤ (1-(q-2)*z)^2 :=
    (sq_le_sq₀ htpos (le_trans htpos horder)).mpr horder
  have h1 := mul_le_mul_of_nonneg_left hleft (show 0 ≤ q by linarith)
  have h2 := mul_le_mul_of_nonneg_left hright (show 0 ≤ q+1 by linarith)
  linarith [ht.2.2]

/-- The existing continuous count envelope now has a phase-III endpoint. -/
theorem joint_envelope (q z s t : ℝ) (h : Bool) (hq : 3 ≤ q)
    (hz : 0 ≤ z) (hsmall : 4*q*z ≤ 1) (hzz : z ≤ tilt q)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ q) :
    dual q z (bit h) s t ≤ q*(q+1)*(1-(q-2)*z)^2 := by
  have he := endpoint_order q z hq hz hzz
  have hA : dual q z 0 q 0 ≤ q*(q+1)*(1-(q-2)*z)^2 := by
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ q by linarith)
    unfold dual
    nlinarith
  have hAon : dual q z 1 q 0 ≤ dual q z 0 q 0 := by
    have hqm : 0 ≤ q-1 := by linarith
    have hh : 0 ≤ q*z*(2*q+(q-1)*z) := by positivity
    unfold dual
    nlinarith
  have hBoff : dual q z 0 0 q ≤ dual q z 1 0 q := by
    have hh : 0 ≤ q*(q+1)*z*(2-(2*q-3)*z) := by
      apply mul_nonneg (by positivity)
      nlinarith
    unfold dual
    nlinarith
  have hBon : dual q z 1 0 q=q*(q+1)*(1-(q-2)*z)^2 := by unfold dual; ring
  cases h with
  | false =>
    exact dual_envelope q z 0 s t _ hq hz hsmall (by norm_num) (by norm_num)
      hs ht hst hA (by linarith [hBoff,hBon])
  | true =>
    exact dual_envelope q z 1 s t _ hq hz hsmall (by norm_num) (by norm_num)
      hs ht hst (le_trans hAon hA) hBon.le

theorem phase_nuisance_bounds (q mu : ℝ) (hq : 3 ≤ q)
    (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q) :
    0 < 1-mu ∧ 0 ≤ mu-shift q mu ∧ mu-shift q mu ≤ 1 ∧
      0 ≤ shift q mu/(1-mu) ∧ 4*q*(shift q mu/(1-mu)) ≤ 1 ∧
      shift q mu/(1-mu) ≤ tilt q := by
  obtain ⟨hm,hm1,hd,hsmall⟩ := phase_shift_bounds q mu hq hlo hup
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hhigh : marginHigh q < 1 := (div_lt_one (by linarith : 0 < 1+Real.sqrt q)).mpr (by linarith)
  have hl : 0 < 1-mu := by linarith
  have hdmu : shift q mu ≤ mu := by nlinarith
  refine ⟨hl,by linarith,by linarith,div_nonneg hd hl.le,?_,?_⟩
  · rw [← mul_div_assoc]
    exact (div_le_one hl).mpr hsmall
  · exact (div_le_iff₀ hl).mpr (by
      nlinarith [shift_le_boundary_tilt q mu hq (by linarith) hm1 hlo])

/-- Actual joint-world information is bounded for every legal group size,
not just the two groups that receive primal mass. -/
theorem actual_joint_bound (A G : Finset (I n)) (j : I n) (h : Bool) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (hsize : (G.card : ℝ) ≤ q) :
    2*(∑ a ∈ A, ∑ b ∈ others A j,
      queryKL A (swapped A a b) G j h mu (mu-shift q mu)) ≤
        (q+1)*(mu^2+(q-1)*(shift q mu)^2) := by
  let lam := 1-mu
  let z := shift q mu/lam
  have hp := phase_nuisance_bounds q mu hq hlo hup
  have ht : 1-lam*(1+z)=mu-shift q mu := by
    dsimp [z,lam]
    field_simp [ne_of_gt hp.1]
    ring
  have hmu : 1-lam=mu := by dsimp [lam]; ring
  have he : (∑ a ∈ A, ∑ b ∈ others A j,
      queryKL A (swapped A a b) G j h mu (mu-shift q mu)) =
      4*lam^2*(∑ a ∈ A, ∑ b ∈ others A j,
        queryKL A (swapped A a b) G j h (1/2) (1-(1+z)/2)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [mul_sum]
    apply sum_congr rfl
    intro b hb
    rw [← ht,← hmu]
    exact joint_homogeneity A (swapped A a b) G j h hj
      (swapped_j_not A j a b hj hb) hjG hG lam (1+z)
  have hcnt : ((G ∩ A).card : ℝ)+(G ∩ others A j).card ≤ q := by
    have he : ((G ∩ A).card : ℝ)+(G ∩ others A j).card=G.card :=
      by exact_mod_cast query_count_partition A G j hjG
    linarith
  have hb := joint_envelope q z (G ∩ A).card (G ∩ others A j).card h hq
    hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2 (by positivity) (by positivity) hcnt
  have hs := actual_dual_sum A G j h q z hj hA hB hjG hG
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg lam)
  have hid : lam^2*(q*(q+1)*(1-(q-2)*z)^2)=
      (q+1)*(q*((1-mu)-(q-2)*shift q mu)^2) := by
    dsimp [lam,z]
    field_simp [ne_of_gt hp.1]
  have hm := phase_shift_bounds q mu hq hlo hup
  rw [balance q mu hq (by linarith [hm.1]) hm.2.1] at hid
  rw [he]
  nlinarith [hmul,hs,hid]

theorem actual_scalar_bound (A : Finset (I n)) (j i : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    2*(∑ a ∈ A, ∑ b ∈ others A j,
      scalarKL A (swapped A a b) j i mu (mu-shift q mu)) ≤
        (q+1)*(mu^2+(q-1)*(shift q mu)^2) := by
  have hp := phase_nuisance_bounds q mu hq hlo hup
  have hm := phase_shift_bounds q mu hq hlo hup
  have ht : 1-(1-mu)*(1+shift q mu/(1-mu))=mu-shift q mu := by
    field_simp [ne_of_gt hp.1]
    ring
  have he := actual_scalar_margin_sum A j i hj (1-mu) (shift q mu/(1-mu))
  have hsq : (1-mu)^2*(shift q mu/(1-mu))^2=(shift q mu)^2 := by
    field_simp [ne_of_gt hp.1]
  rw [ht,show 1-(1-mu)=mu by ring,hA,hB] at he
  have hs : (mu-shift q mu)^2 ≤ mu^2 := by
    nlinarith only [hp.2.1,hm.2.2.1]
  have hd : (shift q mu)^2 ≤ mu^2 := by
    nlinarith only [hp.2.1,hm.2.2.1,hm.1]
  have hnon : 0 ≤ (q-1)*(shift q mu)^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  rw [he]
  split_ifs
  · calc
      _ ≤ q*mu^2 := mul_le_mul_of_nonneg_left hs (by linarith)
      _ ≤ (q+1)*mu^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnon) (by linarith)
  · rw [mul_assoc ((q+1)*q),hsq]
    calc
      _ = (q+1)*((shift q mu)^2+(q-1)*(shift q mu)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hd (le_refl _)) (by linarith)
  · rw [mul_assoc (q-1),hsq]


theorem measurement_bound (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (e : Measurement n) (he : Legal j q e) :
    2*(∑ a ∈ A, ∑ b ∈ others A j,
      information A (swapped A a b) j mu (mu-shift q mu) e) ≤
        (q+1)*(mu^2+(q-1)*(shift q mu)^2) := by
  cases e with
  | inl i => exact actual_scalar_bound A j i q mu hq hlo hup hj hA hB
  | inr p => exact actual_joint_bound A p.1 j p.2 q mu hq hlo hup hj hA hB he.1 he.2.2 he.2.1

#print axioms endpoint_order
#print axioms joint_envelope
#print axioms phase_nuisance_bounds
#print axioms actual_joint_bound
#print axioms actual_scalar_bound
#print axioms measurement_bound
end
end CIGAMF.P13.D6AllocationPhaseThreeDual
