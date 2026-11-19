import Mathlib

/-!
# Two-share extrapolation and the global component a within-run switchback cannot see (city track, W22-E, 17/10/2026)

Companion of PROTOCOL_CITY_WAVE22_20261017 Amendment W22-E (ledger C-261); extends `LeanCityOwnerTestV1`.

## WHAT IS PROVED
* `two_share_exact` — if the treated and control fleet means are affine in the treated share, `T p = t0 + t1 p`, `C p = c0 + c1 p`, then the
  two-share extrapolation from any shares `p1 < p2`,
  `(T p2 + (1 - p2) (T p2 - T p1) / (p2 - p1)) - (C p1 - p1 (C p2 - C p1) / (p2 - p1))`, equals the global effect `T 1 - C 0` exactly.
* `naive_bias_affine` — under the same model the naive contrast at share p, `T p - C p`, misses the global effect by `-(1 - p) t1 - p c1`.
* `two_share_error_bound` — if `T` and `C` are within `ε` of affine functions at `p1`, `p2` and at the end points `1`, `0` (with
  `0 ≤ p1 < p2 ≤ 1`), the extrapolation error is at most `ε (4 + 2 (1 - p2 + p1) / (p2 - p1))`.
* `switchback_misses_global` — with window response `μ + τl Z + γ G` (own assignment `Z`, network treated share `G`), a within-run
  switchback at share `g` measures `τl`, the global effect is `τl + γ`, and twice the run mean over the no-SPaT baseline at `g = 1/2`
  recovers `τl + γ`.
* `hyps_satisfiable` — shares (0.3, 0.7) with an affine instance; the bound's hypotheses with ε = 0.

## WHAT THIS DOES NOT ESTABLISH
That the simulator's means are affine in the share (W22-B post hoc, then W22-E on two fresh families and a fresh driver world, show the
extrapolation recovering the global effect within its interval), or that real windows follow the additive local + global model.  Variances
and the pairing of the two shares on the same simulated days are not treated.
-/

namespace CIGAMF.P13.CityOwnerTestV2

/-- The two-share extrapolation of `T 1 - C 0` from shares `p1 < p2`. -/
noncomputable def twoShare (T C : ℝ → ℝ) (p1 p2 : ℝ) : ℝ :=
  (T p2 + (1 - p2) * (T p2 - T p1) / (p2 - p1)) - (C p1 - p1 * (C p2 - C p1) / (p2 - p1))

theorem two_share_exact (t0 t1 c0 c1 : ℝ) {p1 p2 : ℝ} (h : p1 < p2) :
    twoShare (fun p => t0 + t1 * p) (fun p => c0 + c1 * p) p1 p2 = (t0 + t1 * 1) - (c0 + c1 * 0) := by
  have hne : p2 - p1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  unfold twoShare; field_simp; ring

theorem naive_bias_affine (t0 t1 c0 c1 p : ℝ) :
    ((t0 + t1 * p) - (c0 + c1 * p)) - ((t0 + t1 * 1) - (c0 + c1 * 0)) = -(1 - p) * t1 - p * c1 := by ring

theorem two_share_error_bound {T C : ℝ → ℝ} {t0 t1 c0 c1 ε p1 p2 : ℝ} (h : p1 < p2) (hp1 : 0 ≤ p1) (hp2 : p2 ≤ 1)
    (hT1 : |T p1 - (t0 + t1 * p1)| ≤ ε) (hT2 : |T p2 - (t0 + t1 * p2)| ≤ ε) (hC1 : |C p1 - (c0 + c1 * p1)| ≤ ε)
    (hC2 : |C p2 - (c0 + c1 * p2)| ≤ ε) (hTe : |T 1 - (t0 + t1 * 1)| ≤ ε) (hCe : |C 0 - (c0 + c1 * 0)| ≤ ε) :
    |twoShare T C p1 p2 - (T 1 - C 0)| ≤ ε * (4 + 2 * (1 - p2 + p1) / (p2 - p1)) := by
  have hd : 0 < p2 - p1 := sub_pos.mpr h
  have hne : p2 - p1 ≠ 0 := hd.ne'
  have key : twoShare T C p1 p2 - (T 1 - C 0)
      = (T p2 - (t0 + t1 * p2)) + (1 - p2) * ((T p2 - (t0 + t1 * p2)) - (T p1 - (t0 + t1 * p1))) / (p2 - p1)
        - (C p1 - (c0 + c1 * p1)) + p1 * ((C p2 - (c0 + c1 * p2)) - (C p1 - (c0 + c1 * p1))) / (p2 - p1)
        - (T 1 - (t0 + t1 * 1)) + (C 0 - (c0 + c1 * 0)) := by
    unfold twoShare; field_simp; ring
  rw [key]
  generalize T p1 - (t0 + t1 * p1) = a at *
  generalize T p2 - (t0 + t1 * p2) = b at *
  generalize C p1 - (c0 + c1 * p1) = c at *
  generalize C p2 - (c0 + c1 * p2) = d at *
  generalize T 1 - (t0 + t1 * 1) = e at *
  generalize C 0 - (c0 + c1 * 0) = f at *
  have hba : |b - a| ≤ 2 * ε := by
    calc |b - a| ≤ |b| + |a| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have hdc : |d - c| ≤ 2 * ε := by
    calc |d - c| ≤ |d| + |c| := abs_sub _ _
      _ ≤ 2 * ε := by linarith
  have h1 : |(1 - p2) * (b - a) / (p2 - p1)| ≤ (1 - p2) * (2 * ε) / (p2 - p1) := by
    rw [abs_div, abs_of_pos hd, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hba (by linarith)) hd.le
  have h2 : |p1 * (d - c) / (p2 - p1)| ≤ p1 * (2 * ε) / (p2 - p1) := by
    rw [abs_div, abs_of_pos hd, abs_mul, abs_of_nonneg hp1]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdc hp1) hd.le
  have tri : |b + (1 - p2) * (b - a) / (p2 - p1) - c + p1 * (d - c) / (p2 - p1) - e + f|
      ≤ |b| + |(1 - p2) * (b - a) / (p2 - p1)| + |c| + |p1 * (d - c) / (p2 - p1)| + |e| + |f| := by
    have s1 := abs_add_le (b + (1 - p2) * (b - a) / (p2 - p1) - c + p1 * (d - c) / (p2 - p1) - e) f
    have s2 := abs_sub (b + (1 - p2) * (b - a) / (p2 - p1) - c + p1 * (d - c) / (p2 - p1)) e
    have s3 := abs_add_le (b + (1 - p2) * (b - a) / (p2 - p1) - c) (p1 * (d - c) / (p2 - p1))
    have s4 := abs_sub (b + (1 - p2) * (b - a) / (p2 - p1)) c
    have s5 := abs_add_le b ((1 - p2) * (b - a) / (p2 - p1))
    linarith
  have hsum : ε + (1 - p2) * (2 * ε) / (p2 - p1) + ε + p1 * (2 * ε) / (p2 - p1) + ε + ε
      = ε * (4 + 2 * (1 - p2 + p1) / (p2 - p1)) := by
    field_simp; ring
  linarith [tri, h1, h2]

/-- Window response: own assignment `Z`, network treated share `G`. -/
def resp (μ τl γ Z G : ℝ) : ℝ := μ + τl * Z + γ * G

theorem switchback_misses_global (μ τl γ g : ℝ) :
    resp μ τl γ 1 g - resp μ τl γ 0 g = τl ∧
    resp μ τl γ 1 1 - resp μ τl γ 0 0 = τl + γ ∧
    2 * ((1 / 2 : ℝ) * resp μ τl γ 1 (1 / 2) + (1 / 2) * resp μ τl γ 0 (1 / 2) - resp μ τl γ 0 0) = τl + γ := by
  unfold resp; refine ⟨by ring, by ring, by ring⟩

theorem hyps_satisfiable :
    (3 / 10 : ℝ) < 7 / 10 ∧
    twoShare (fun p => 1 + 2 * p) (fun p => 3 + 4 * p) (3 / 10) (7 / 10) = (1 + 2 * 1) - (3 + 4 * 0) ∧
    |(fun p : ℝ => 1 + 2 * p) (3 / 10) - (1 + 2 * (3 / 10))| ≤ (0 : ℝ) := by
  refine ⟨by norm_num, two_share_exact 1 2 3 4 (by norm_num), by norm_num⟩

end CIGAMF.P13.CityOwnerTestV2

#print axioms CIGAMF.P13.CityOwnerTestV2.two_share_exact
#print axioms CIGAMF.P13.CityOwnerTestV2.naive_bias_affine
#print axioms CIGAMF.P13.CityOwnerTestV2.two_share_error_bound
#print axioms CIGAMF.P13.CityOwnerTestV2.switchback_misses_global
#print axioms CIGAMF.P13.CityOwnerTestV2.hyps_satisfiable
