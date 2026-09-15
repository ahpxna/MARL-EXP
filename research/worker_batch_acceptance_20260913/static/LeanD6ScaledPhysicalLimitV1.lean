import «LeanD6ScaledReferencePhaseV1»

/-! The scaled formula is eventually the value of the actual physical game.
The strong restriction is discharged by an eventual theorem, never removed. -/
namespace CIGAMF.P13.D6ScaledPhysicalLimit
open Filter Finset
open scoped Topology
open CIGAMF.P13.D6ScaledReferenceCoefficients CIGAMF.P13.D6ScaledReferencePhase
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceEndpointWorlds CIGAMF.P13.D6ReferencePhysicalBounds
open CIGAMF.P13.D6ReferencePhysicalCertificate CIGAMF.P13.D6ReferencePhaseValue
noncomputable section

/-- The value certificate quantifies over all reference worlds of this size. -/
def ScaledCertified (tau rho : ℝ) (q : ℕ) : Prop :=
  ∀ (j : I (2*q+1)) (T : Finset (I (2*q+1))), T ∈ worlds q j →
    ∃ M : Region q j T, M.t=tau/(q+1:ℕ) ∧ M.rho=rho ∧
      CertifiedValue M (value tau rho (q+1))

theorem physical_scaled_certificate (tau rho : ℝ) (q : ℕ) (hq : 2 ≤ q)
    (ht : 0 ≤ tau) (htq : tau ≤ (q+1:ℕ)) (hr : 1 ≤ rho) (hr2 : rho ≤ 2)
    (hs : 1 ≤ (((q+1:ℕ):ℝ)-2)*b tau (q+1)) :
    ScaledCertified tau rho q := by
  intro j T hT
  have hab := physical_coefficients q hq j T hT tau
  have hqpos : (0:ℝ) < (q+1:ℕ) := by positivity
  have ht0 : 0 ≤ tau/(q+1:ℕ) := div_nonneg ht hqpos.le
  have ht1 : tau/(q+1:ℕ) ≤ 1 := (div_le_one hqpos).mpr htq
  have strong : 1 ≤ ((q:ℝ)-1)*CIGAMF.P13.D6ReferenceCenteredCompensated.slopeBval (tau/(q+1:ℕ)) T j := by
    rw [hab.2]
    convert hs using 1 <;> push_cast <;> ring
  let M := physicalRegion q j T (tau/(q+1:ℕ)) rho hq hT ht0 ht1 hr hr2 strong
  have ha : M.a=a tau (q+1) := hab.1
  have hb : M.b=b tau (q+1) := hab.2
  have hc : M.c=c tau (q+1) := by
    change M.a-M.b=c tau (q+1)
    rw [ha,hb]
    unfold a b
    ring
  have hv : phaseValueFull ((q:ℝ)+1) M.p M.c M.e M.r=value tau rho (q+1) := by
    dsimp only [Region.p,Region.e,Region.r,value]
    rw [ha,hb,hc]
    simp only [Nat.cast_add,Nat.cast_one,e]
    rfl
  refine ⟨M,rfl,rfl,?_⟩
  rw [← hv]
  exact (region_certified_threshold M).1

/-- For positive tau, every sufficiently large size is in the retained domain. -/
theorem scaled_certified_eventually (tau rho : ℝ) (ht : 0 < tau)
    (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    ∀ᶠ q : ℕ in atTop, ScaledCertified tau rho q := by
  have hs := (tendsto_add_atTop_nat 1).eventually (strong_eventually tau ht)
  have hq : ∀ᶠ q : ℕ in atTop, tau ≤ (q:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop).eventually (eventually_ge_atTop tau)
  filter_upwards [hs,hq,eventually_ge_atTop (2:ℕ)] with q hs hq hq2
  apply physical_scaled_certificate tau rho q hq2 ht.le _ hr hr2 hs
  exact hq.trans (by norm_cast;omega)

/-- Both the actual-game status and its normalized clamped limit. -/
theorem physical_value_limit_clamped (tau rho : ℝ) (ht : 0 < tau)
    (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    (∀ᶠ q : ℕ in atTop, ScaledCertified tau rho q) ∧
    Tendsto (fun q : ℕ => value tau rho (q+1)/(q+1:ℕ)) atTop (𝓝 (limitValue tau rho)) :=
  ⟨scaled_certified_eventually tau rho ht hr hr2,
    (value_tendsto tau rho).comp (tendsto_add_atTop_nat 1)⟩

#print axioms physical_scaled_certificate
#print axioms scaled_certified_eventually
#print axioms physical_value_limit_clamped
end
end CIGAMF.P13.D6ScaledPhysicalLimit
