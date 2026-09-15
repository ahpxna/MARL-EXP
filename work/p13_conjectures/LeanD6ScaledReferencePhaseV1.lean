import «LeanD6ScaledReferenceCoefficientsV1»
import «LeanD6ReferencePhysicalCertificateV1»

/-! Scaled physical reference coefficients and the clamped phase value.
The physical minimax theorem is used with its original strong restriction. -/
namespace CIGAMF.P13.D6ScaledReferencePhase
open Filter Finset
open scoped Topology
open CIGAMF.P13.D6ScaledReferenceCoefficients CIGAMF.P13.D6ReferencePhaseValue
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceFullCountLoss
noncomputable section

def value (tau rho : ℝ) (k : ℕ) :=
  phaseValueFull k (rho-2*b tau k) (c tau k) (e tau k) (2*a tau k-rho)
def limitValue (tau rho : ℝ) :=
  max 0 (limitThreshold tau-rho)*(rho-2*tau*limitC tau)/(4*limitC tau)

lemma normalized_value (k p c e r : ℝ) (hk : 1 < k) :
    phaseValueFull k p c e r/k = max 0 (r-e/k)*(p+max 0 (e-r)/(k-1))/(4*c) := by
  have hk0 : k ≠ 0 := by linarith
  have hk1 : k-1 ≠ 0 := by linarith
  have hmax : max 0 (k*r-e)/k=max 0 (r-e/k) := by
    rw [← max_div_div_right (by linarith : 0 ≤ k),zero_div]
    congr 1
    field_simp
  unfold phaseValueFull
  rw [show max 0 (k*r-e)*(p*(k-1)+max 0 (e-r))/(4*(c*(k-1)))/k=
      (max 0 (k*r-e)/k)*(p+max 0 (e-r)/(k-1))/(4*c) by field_simp <;> ring,hmax]

set_option backward.isDefEq.respectTransparency false in
/-- The inactive branch remains zero in the limit. -/
theorem value_tendsto (tau rho : ℝ) :
    Tendsto (fun k : ℕ => value tau rho k/(k:ℝ)) atTop (𝓝 (limitValue tau rho)) := by
  have hthr := (threshold_tendsto tau).sub_const rho
  have hmax := (show Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0) from tendsto_const_nhds).max hthr
  have hp := (show Tendsto (fun _ : ℕ => rho) atTop (𝓝 rho) from tendsto_const_nhds).sub ((b_tendsto tau).const_mul 2)
  have hnum := (show Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0) from tendsto_const_nhds).max
    ((e_tendsto tau).sub (((a_tendsto tau).const_mul 2).sub_const rho))
  have hden : Tendsto (fun k : ℕ => (k:ℝ)-1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1) tendsto_natCast_atTop_atTop
  have hz := hnum.div_atTop hden
  have h := (hmax.mul (hp.add hz)).div ((c_tendsto tau).const_mul 4)
    (by dsimp [limitC];positivity)
  have hh : Tendsto (fun k : ℕ => max 0 (threshold tau k-rho)*
      (rho-2*b tau k+max 0 (e tau k-(2*a tau k-rho))/((k:ℝ)-1))/(4*c tau k))
      atTop (𝓝 (limitValue tau rho)) := by
    convert h using 1 <;> (try simp only [Pi.div_apply,limitValue,mul_assoc,add_zero]) <;> rfl
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with k hk
  rw [value,normalized_value _ _ _ _ _ (by exact_mod_cast (show 1<k by omega))]
  congr 3
  unfold threshold
  ring

/-- Actual physical coefficients equal the scaled formulas at k=q+1. -/
theorem physical_coefficients (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (T : Finset (I (2*q+1))) (hT : T ∈ worlds q j) (tau : ℝ) :
    gateMass (tau/(q+1:ℕ)) T j=a tau (q+1) ∧
    slopeBval (tau/(q+1:ℕ)) T j=b tau (q+1) := by
  have hp := world_parameters q j hq hT
  have hTc := hp.2.1
  have hBc : (others T j).card=q := by
    change (Tᶜ.erase j).card=q
    rw [card_erase_of_mem (by simp [hp.1]),hp.2.2.1,hTc]
    omega
  have hb : slopeBval (tau/(q+1:ℕ)) T j=b tau (q+1) := by
    unfold slopeBval b c
    rw [hTc,hBc]
    simp only [Nat.cast_add,Nat.cast_one,show q+1+q-1=2*(q+1)-2 by omega]
    ring
  have hg := slope_gap (tau/(q+1:ℕ)) T j (by omega)
  rw [hTc,hBc,show q+1+q-1=2*(q+1)-2 by omega,hb] at hg
  refine ⟨?_,hb⟩
  dsimp [a,b,c] at *
  linarith

#print axioms normalized_value
#print axioms value_tendsto
#print axioms physical_coefficients
end
end CIGAMF.P13.D6ScaledReferencePhase
