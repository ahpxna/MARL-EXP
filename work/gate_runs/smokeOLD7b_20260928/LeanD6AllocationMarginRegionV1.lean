import «LeanD6AllocationMarginV1»

/-! Exact closed endpoints of the true-margin region for the actual D6
allocation theorem. The square root below is a positive expression for the
scalar-B dual constraint. No additional assumption about optimality is used. -/
namespace CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6ExpandedAllocation CIGAMF.P13.D6AllocationMargin
noncomputable section

def tilt (q : ℝ) : ℝ := root q (scale q)
def gain (q : ℝ) : ℝ := 1+tilt q
def radius (q : ℝ) : ℝ :=
  Real.sqrt ((q^2+2*q^2*tilt q+(tilt q)^2)/(q+1))
def lower (q : ℝ) : ℝ := 1/(1+radius q)
def upper (q : ℝ) : ℝ := 1/gain q
def marginMin (q : ℝ) : ℝ := (1-scale q)/(q-1)
def marginMax (q : ℝ) : ℝ := radius q/(1+radius q)

theorem tilt_pos (q : ℝ) (hq : 3 ≤ q) : 0 < tilt q := by
  have hc := scale_properties q hq
  exact (root_properties q _ hq hc.1 hc.2.1 hc.2.2).1

theorem gain_pos (q : ℝ) (hq : 3 ≤ q) : 0 < gain q := by
  have hz := tilt_pos q hq
  unfold gain
  linarith

theorem radius_pos (q : ℝ) (hq : 3 ≤ q) : 0 < radius q := by
  have hz := tilt_pos q hq
  have hp : 0 < q := by linarith
  unfold radius
  apply Real.sqrt_pos.2
  positivity

/-- This identity also gives R²=q²T²/(q+1)-(q-1)z². -/
theorem radius_balance (q : ℝ) (hq : 3 ≤ q) :
    (q+1)*(radius q)^2=q^2*(gain q)^2-(q^2-1)*(tilt q)^2 := by
  have hz := tilt_pos q hq
  have hp : 0 < q := by linarith
  have hk : q+1 ≠ 0 := by linarith
  have hr : (radius q)^2=(q^2+2*q^2*tilt q+(tilt q)^2)/(q+1) := by
    exact Real.sq_sqrt (by positivity)
  have he := (eq_div_iff hk).mp hr
  unfold gain
  nlinarith [he]

theorem radius_sq_le (q : ℝ) (hq : 3 ≤ q) :
    (radius q)^2 ≤ q*(gain q)^2 := by
  have he := radius_balance q hq
  have hk : 0 < q+1 := by linarith
  have hp : 0 ≤ q*(gain q)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hz : 0 ≤ (q^2-1)*(tilt q)^2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  apply le_of_mul_le_mul_left (a := q+1) ?_ hk
  nlinarith [hp,hz]

/-- Within the feasible nuisance range, satisfying the scalar-B bound implies
satisfying scalar A. Thus B is the active scalar constraint at the endpoint. -/
theorem scalar_B_implies_A (q lam : ℝ) (hq : 3 ≤ q) (hlam : 0 ≤ lam)
    (hu : lam*gain q ≤ 1)
    (hB : (q+1)*((1-lam)^2+(q-1)*lam^2*(tilt q)^2) ≤
      q^2*lam^2*(gain q)^2) :
    (1-lam*gain q)^2 ≤ q*lam^2*(gain q)^2 := by
  have hz := (tilt_pos q hq).le
  have hk : 0 < q+1 := by linarith
  have hlz := mul_nonneg hlam hz
  have hlu : lam ≤ 1 := by dsimp [gain] at hu; nlinarith
  have hnon : 0 ≤ 1-lam*gain q := by linarith
  have hdiff : 1-lam*gain q ≤ 1-lam := by dsimp [gain]; nlinarith
  have hs : (1-lam*gain q)^2 ≤ (1-lam)^2 := by nlinarith
  have he := congrArg (fun x : ℝ => lam^2*x) (radius_balance q hq)
  have hBs : (1-lam)^2 ≤ lam^2*(radius q)^2 := by
    apply le_of_mul_le_mul_left (a := q+1) ?_ hk
    nlinarith [he]
  have hr := mul_le_mul_of_nonneg_left (radius_sq_le q hq) (sq_nonneg lam)
  nlinarith [hr]

/-- Closed, exact interval in lambda=1-mu, with no missing scalar constraint. -/
theorem interior_iff (q lam : ℝ) (hq : 3 ≤ q) :
    Interior q lam ↔ lower q ≤ lam ∧ lam ≤ upper q := by
  have hz := tilt_pos q hq
  have ht := gain_pos q hq
  have hr := radius_pos q hq
  have hd : 0 < 1+radius q := by linarith
  have hk : 0 < q+1 := by linarith
  constructor
  · rintro ⟨hl,hl1,hu,hA,hB⟩
    have he := congrArg (fun x : ℝ => lam^2*x) (radius_balance q hq)
    have hBs : (1-lam)^2 ≤ (lam*radius q)^2 := by
      apply le_of_mul_le_mul_left (a := q+1) ?_ hk
      dsimp [gain,tilt] at he
      nlinarith [he]
    have hprod : 0 ≤ lam*radius q := mul_nonneg hl.le hr.le
    have hline : 1 ≤ lam*(1+radius q) := by nlinarith [hBs]
    refine ⟨(div_le_iff₀ hd).mpr hline, ?_⟩
    exact (le_div_iff₀ ht).mpr (by simpa [gain,tilt] using hu)
  · rintro ⟨hlo,hup⟩
    have hl : 0 < lam := lt_of_lt_of_le (div_pos (by norm_num) hd) hlo
    have hu : lam*gain q ≤ 1 := (le_div_iff₀ ht).mp hup
    have hlz := mul_nonneg hl.le hz.le
    have hl1 : lam ≤ 1 := by dsimp [gain] at hu; nlinarith
    have hline : 1 ≤ lam*(1+radius q) := (div_le_iff₀ hd).mp hlo
    have hprod : 0 ≤ lam*radius q := mul_nonneg hl.le hr.le
    have hBs : (1-lam)^2 ≤ (lam*radius q)^2 := by nlinarith
    have he := congrArg (fun x : ℝ => lam^2*x) (radius_balance q hq)
    have hB : (q+1)*((1-lam)^2+(q-1)*lam^2*(tilt q)^2) ≤
        q^2*lam^2*(gain q)^2 := by
      have hm := mul_le_mul_of_nonneg_left hBs hk.le
      nlinarith [he,hm]
    have hA := scalar_B_implies_A q lam hq hl.le hu hB
    exact ⟨hl,hl1,by simpa [gain,tilt] using hu,
      by simpa [gain,tilt] using hA,by simpa [gain,tilt] using hB⟩

/-- The lower endpoint in the true margin has a particularly simple form. -/
theorem marginMin_eq (q : ℝ) (hq : 3 ≤ q) : marginMin q=1-upper q := by
  have hc := scale_properties q hq
  have hd : q-2+scale q ≠ 0 := by linarith [hc.1]
  have hq1 : q-1 ≠ 0 := by linarith
  have ht : gain q=(q-1)/(q-2+scale q) := by
    unfold gain tilt root
    field_simp [hd]
    ring
  unfold marginMin upper
  rw [ht]
  field_simp [hd,hq1]
  ring

theorem marginMax_eq (q : ℝ) (hq : 3 ≤ q) : marginMax q=1-lower q := by
  have hr := radius_pos q hq
  have hd : 1+radius q ≠ 0 := by linarith
  unfold marginMax lower
  field_simp [hd]
  ring

/-- Exact true-margin endpoints for every width m=2(q+1)>=8. -/
theorem interior_iff_margin (q mu : ℝ) (hq : 3 ≤ q) :
    Interior q (1-mu) ↔ marginMin q ≤ mu ∧ mu ≤ marginMax q := by
  rw [interior_iff q (1-mu) hq,marginMin_eq q hq,marginMax_eq q hq]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

#print axioms radius_balance
#print axioms scalar_B_implies_A
#print axioms interior_iff
#print axioms marginMin_eq
#print axioms interior_iff_margin
end
end CIGAMF.P13.D6AllocationMarginRegion
