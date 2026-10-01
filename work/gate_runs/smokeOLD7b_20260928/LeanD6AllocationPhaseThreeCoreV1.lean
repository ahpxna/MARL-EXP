import «LeanD6AllocationMarginRegionV1»

/-! Algebraic core of the scalar-B / B-on phase. Conditions are explicit
balance and stationarity equations, not assumed optimality. Endpoint formulas
and their feasibility are still to be connected separately. All-distance
bounds cover distance one and every real distance >=2 up to q. -/
namespace CIGAMF.P13.D6AllocationPhaseThreeCore
noncomputable section

def mixedLoss (q mu w d u : ℝ) : ℝ :=
  (1-w)*(d*mu^2+(q-d)*(u-(1-mu))^2)/q+
    w*((1-mu)*(q-1)-(q-d-1)*u)^2

def gammaTwice (q mu shift : ℝ) : ℝ := (mu^2+(q-1)*shift^2)/q

def coefficient (q w : ℝ) : ℝ := (1-w)*(q-1)/q+w*(q-2)^2

/-- Exact identity isolating the only two equations required for nearest
alternative optimality. -/
theorem square_remainder (q mu w shift u : ℝ) (hq : q ≠ 0) :
    q*(mixedLoss q mu w 1 u-gammaTwice q mu shift-
      coefficient q w*(u-((1-mu)+shift))^2) =
      w*(q*((1-mu)-(q-2)*shift)^2-mu^2-(q-1)*shift^2)+
      2*(u-((1-mu)+shift))*((1-w)*(q-1)*shift-w*q*(q-2)*((1-mu)-(q-2)*shift)) := by
  unfold mixedLoss gammaTwice coefficient
  field_simp [hq]
  <;> ring

theorem nearest_completed_square (q mu w shift u : ℝ) (hq : 0 < q)
    (balance : q*((1-mu)-(q-2)*shift)^2=mu^2+(q-1)*shift^2)
    (stationarity : (1-w)*(q-1)*shift=w*q*(q-2)*((1-mu)-(q-2)*shift)) :
    mixedLoss q mu w 1 u=gammaTwice q mu shift+
      coefficient q w*(u-((1-mu)+shift))^2 := by
  have he := square_remainder q mu w shift u (ne_of_gt hq)
  rw [stationarity,sub_self,mul_zero,add_zero,balance] at he
  have hzero : q*(mixedLoss q mu w 1 u-gammaTwice q mu shift-
      coefficient q w*(u-((1-mu)+shift))^2)=0 := by nlinarith [he]
  have hz := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hq)
  linarith

theorem distant_lower (q mu w shift d u : ℝ) (hq : 3 ≤ q)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hd : 2 ≤ d) (hdq : d ≤ q)
    (guard : (q-1)*shift^2 ≤ (1-2*w)*mu^2) :
    gammaTwice q mu shift ≤ mixedLoss q mu w d u := by
  have hp : 0 < q := by linarith
  have hterm : 0 ≤ (1-w)*(q-d)*(u-(1-mu))^2 := by positivity
  have hterm2 : 0 ≤ q*w*((1-mu)*(q-1)-(q-d-1)*u)^2 := by positivity
  have hdterm : 0 ≤ (1-w)*(d-2)*mu^2 := by positivity
  unfold gammaTwice mixedLoss
  apply (div_le_iff₀ hp).mpr
  have he : ((1-w)*(d*mu^2+(q-d)*(u-(1-mu))^2)/q+
      w*((1-mu)*(q-1)-(q-d-1)*u)^2)*q =
      (1-w)*d*mu^2+(1-w)*(q-d)*(u-(1-mu))^2+
        q*w*((1-mu)*(q-1)-(q-d-1)*u)^2 := by
    field_simp [ne_of_gt hp]
    <;> ring
  rw [he]
  nlinarith

/-- Once feasibility, balance and stationarity are proved for the explicit
phase formula, every integer alternative distance is covered. -/
theorem all_distances_lower (q mu w shift d u : ℝ) (hq : 3 ≤ q)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hd : d=1 ∨ 2 ≤ d) (hdq : d ≤ q)
    (balance : q*((1-mu)-(q-2)*shift)^2=mu^2+(q-1)*shift^2)
    (stationarity : (1-w)*(q-1)*shift=w*q*(q-2)*((1-mu)-(q-2)*shift))
    (guard : (q-1)*shift^2 ≤ (1-2*w)*mu^2) :
    gammaTwice q mu shift ≤ mixedLoss q mu w d u := by
  rcases hd with he | he
  · subst d
    rw [nearest_completed_square q mu w shift u (by linarith) balance stationarity]
    have hc : 0 ≤ coefficient q w := by unfold coefficient; positivity
    exact le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg _))
  · exact distant_lower q mu w shift d u hq hw hw1 he hdq guard

#print axioms square_remainder
#print axioms nearest_completed_square
#print axioms distant_lower
#print axioms all_distances_lower
end
end CIGAMF.P13.D6AllocationPhaseThreeCore
