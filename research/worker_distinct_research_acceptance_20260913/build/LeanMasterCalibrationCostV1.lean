import «LeanMasterUnknownCalibrationV1»

namespace CIGAMF.P13.MasterCalibrationCost
open CIGAMF.P13.MasterUnknownCalibration
noncomputable section

/-- r,v are square roots of positive channel costs; s,t are noise standard deviations. -/
def info (s t g x y : ℝ) : ℝ := x*y*g^2/(2*(s^2*y+t^2*x))

theorem cost_information_upper (s t r v g x y : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hr : 0 < r) (hv : 0 < v) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hb : r^2*x+v^2*y=1) : info s t g x y ≤ g^2/(2*(s*r+t*v)^2) := by
  by_cases hx0 : x=0
  · simp [info,hx0]; positivity
  by_cases hy0 : y=0
  · simp [info,hy0]; positivity
  have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hden : 0 < s^2*y+t^2*x := by positivity
  have hH : 0 < s*r+t*v := by positivity
  have hid : (s^2*y+t^2*x)-x*y*(s*r+t*v)^2 = (s*v*y-t*r*x)^2 := by
    nlinarith [congrArg (fun z : ℝ => (s^2*y+t^2*x)*z) hb]
  unfold info
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg (sq_nonneg g) (sq_nonneg (s*v*y-t*r*x))]

theorem cost_information_attained (s t r v g : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hr : 0 < r) (hv : 0 < v) :
    let x := (s/r)/(s*r+t*v)
    let y := (t/v)/(s*r+t*v)
    0 < x ∧ 0 < y ∧ r^2*x+v^2*y=1 ∧
      info s t g x y = g^2/(2*(s*r+t*v)^2) := by
  obtain ⟨hx,hy,hb,hi⟩ := optimal_cost_allocation s t r v hs ht hr hv
  refine ⟨hx,hy,hb,?_⟩
  dsimp [info]
  have hd : s*r+t*v ≠ 0 := ne_of_gt (by positivity)
  field_simp
  <;> ring

/-- Profiling two actual Gaussian channels (0,g) with unit common-offset direction. -/
theorem profiled_two_channel (s t g x y : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hx : 0 < x) (hy : 0 < y) :
    ∃ u, (∀ z, info s t g x y ≤ ((x/s^2)*z^2+(y/t^2)*(g-z)^2)/2) ∧
      ((x/s^2)*u^2+(y/t^2)*(g-u)^2)/2 = info s t g x y := by
  let a := x/s^2
  let b := y/t^2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a+b ≠ 0 := ne_of_gt (by positivity)
  have he : a*b*g^2/(2*(a+b))=info s t g x y := by
    dsimp [a,b,info]
    field_simp
    <;> ring
  refine ⟨b*g/(a+b),?_,?_⟩
  · intro z
    change info s t g x y ≤ (a*z^2+b*(g-z)^2)/2
    rw [control_channels a b g z hab,he]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  · change (a*(b*g/(a+b))^2+b*(g-b*g/(a+b))^2)/2 = _
    rw [control_channels a b g _ hab,he]
    simp

#print axioms cost_information_upper
#print axioms cost_information_attained
#print axioms profiled_two_channel
end
end CIGAMF.P13.MasterCalibrationCost
