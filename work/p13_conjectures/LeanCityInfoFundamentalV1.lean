import Mathlib

/-!
# The information fundamental diagram: vehicle-carried information is stale at BOTH ends of demand

Direction: research/papers/audits/CITY_TWO_POPULATION_NOVELTY_20261002.md (idea 3, "the cars are the channel"); measurement
protocol research/city_sim/PROTOCOL_CITY_Q3_INFO_FUNDAMENTAL_20261002.md.  A light that hears about its upstream neighbour only
through vehicles that travelled the link holds a copy whose mean age is the travel time plus the wait for the next carrier:
A = L/u + c/q.  Under Greenshields (u = u_f (1 − ρ), q = ρ k_j u) this is

    A(ρ) = (a ρ + b) / (ρ (1 − ρ)),   a = L / u_f,  b = c / (k_j u_f),  ρ ∈ (0, 1) the density relative to jam.

## WHAT IS PROVED (a, b > 0)
* `age_identity` — A(ρ) − m* = (√m* ρ − √b)² / (ρ (1 − ρ)) with m* = (√(a + b) + √b)².
* `age_ge_min` — A(ρ) ≥ m* for every ρ ∈ (0, 1); `age_at_min` — equality at ρ* = √b / (√b + √(a + b)) ∈ (0, 1).
* `age_ge_low`, `age_ge_high` — A(ρ) ≥ b / ρ and A(ρ) ≥ a / (1 − ρ).
* `exit_both_ends` — for every training ceiling M > 0: A(ρ) > M whenever ρ < b / M (too few carriers) or ρ > 1 − a / M (carriers
  too slow).  A learned receiver trained on ages ≤ M therefore meets out-of-range ages at low AND at high demand.
* `witness` — a = 3, b = 1: m* = 9 at ρ* = 1/3; A(1/10) = 130/9 and A(9/10) = 370/9 both exceed 9 (hypotheses satisfiable).

## WHAT THIS DOES NOT ESTABLISH
- That SUMO's links follow Greenshields or a Poisson carrier stream (the protocol measures A against L/u + 1/q directly).
- Anything about a learned light's performance; that is the Q8 experiment.
-/

namespace CIGAMF.P13.CityInfoFundamentalV1

noncomputable section

/-- Mean age of vehicle-carried information at relative density ρ. -/
def age (a b ρ : ℝ) : ℝ := (a * ρ + b) / (ρ * (1 - ρ))

/-- The minimal mean age. -/
def mstar (a b : ℝ) : ℝ := (Real.sqrt (a + b) + Real.sqrt b) ^ 2

/-- The density that attains it. -/
def rhostar (a b : ℝ) : ℝ := Real.sqrt b / (Real.sqrt b + Real.sqrt (a + b))

theorem num_identity (a b ρ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * ρ + b - mstar a b * (ρ * (1 - ρ)) = (Real.sqrt (mstar a b) * ρ - Real.sqrt b) ^ 2 := by
  have hs : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt (by linarith)
  have ht : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hm : Real.sqrt (mstar a b) = Real.sqrt (a + b) + Real.sqrt b := by
    unfold mstar; rw [Real.sqrt_sq (by positivity)]
  rw [hm]; unfold mstar
  linear_combination (-ρ) * hs + (ρ - 1) * ht

theorem age_identity (a b ρ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 < ρ) (h1 : ρ < 1) :
    age a b ρ - mstar a b = (Real.sqrt (mstar a b) * ρ - Real.sqrt b) ^ 2 / (ρ * (1 - ρ)) := by
  have hd : ρ * (1 - ρ) ≠ 0 := (mul_pos h0 (by linarith)).ne'
  rw [← num_identity a b ρ ha hb, eq_div_iff hd]; unfold age
  rw [sub_mul, div_mul_cancel₀ _ hd]

theorem age_ge_min (a b ρ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 < ρ) (h1 : ρ < 1) : mstar a b ≤ age a b ρ := by
  have hd : 0 < ρ * (1 - ρ) := mul_pos h0 (by linarith)
  have := age_identity a b ρ ha hb h0 h1
  have hnn : 0 ≤ (Real.sqrt (mstar a b) * ρ - Real.sqrt b) ^ 2 / (ρ * (1 - ρ)) := div_nonneg (sq_nonneg _) hd.le
  linarith

theorem rhostar_mem (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < rhostar a b ∧ rhostar a b < 1 := by
  have h1 : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have h2 : 0 < Real.sqrt (a + b) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨div_pos h1 (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

theorem age_at_min (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : age a b (rhostar a b) = mstar a b := by
  obtain ⟨h0, h1⟩ := rhostar_mem a b ha hb
  have hid := age_identity a b (rhostar a b) ha.le hb.le h0 h1
  have hm : Real.sqrt (mstar a b) = Real.sqrt (a + b) + Real.sqrt b := by
    unfold mstar; rw [Real.sqrt_sq (by positivity)]
  have hz : Real.sqrt (mstar a b) * rhostar a b - Real.sqrt b = 0 := by
    rw [hm]; unfold rhostar
    have h1' : 0 < Real.sqrt b + Real.sqrt (a + b) := by
      have := Real.sqrt_pos.mpr hb; have := Real.sqrt_nonneg (a + b); linarith
    field_simp; ring
  rw [hz] at hid; simp at hid; linarith

theorem age_ge_low (a b ρ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 < ρ) (h1 : ρ < 1) : b / ρ ≤ age a b ρ := by
  unfold age
  rw [div_le_div_iff₀ h0 (mul_pos h0 (by linarith))]
  nlinarith [mul_nonneg ha (sq_nonneg ρ), mul_nonneg hb h0.le, mul_nonneg (mul_nonneg ha h0.le) h0.le]

theorem age_ge_high (a b ρ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h0 : 0 < ρ) (h1 : ρ < 1) : a / (1 - ρ) ≤ age a b ρ := by
  have h1' : 0 < 1 - ρ := by linarith
  unfold age
  rw [div_le_div_iff₀ h1' (mul_pos h0 h1')]
  nlinarith [mul_nonneg hb h1'.le]

theorem exit_both_ends (a b M ρ : ℝ) (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (h0 : 0 < ρ) (h1 : ρ < 1)
    (hρ : ρ < b / M ∨ 1 - a / M < ρ) : M < age a b ρ := by
  rcases hρ with hl | hh
  · have hlow := age_ge_low a b ρ ha.le hb.le h0 h1
    have : M < b / ρ := by
      rw [lt_div_iff₀ h0]; rw [lt_div_iff₀ hM] at hl; linarith
    linarith
  · have hhigh := age_ge_high a b ρ ha.le hb.le h0 h1
    have h1' : 0 < 1 - ρ := by linarith
    have : M < a / (1 - ρ) := by
      rw [lt_div_iff₀ h1']
      have : 1 - ρ < a / M := by linarith
      rw [lt_div_iff₀ hM] at this; linarith
    linarith

theorem witness : mstar 3 1 = 9 ∧ rhostar 3 1 = 1 / 3 ∧ age 3 1 (1 / 10) = 130 / 9 ∧ age 3 1 (9 / 10) = 370 / 9 ∧
    9 < age 3 1 (1 / 10) ∧ 9 < age 3 1 (9 / 10) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h1 : Real.sqrt 1 = 1 := Real.sqrt_one
  have e : (3 : ℝ) + 1 = 4 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold mstar; rw [e, h4, h1]; norm_num
  · unfold rhostar; rw [e, h4, h1]; norm_num
  · unfold age; norm_num
  · unfold age; norm_num
  · unfold age; norm_num
  · unfold age; norm_num

end

end CIGAMF.P13.CityInfoFundamentalV1

#print axioms CIGAMF.P13.CityInfoFundamentalV1.age_identity
#print axioms CIGAMF.P13.CityInfoFundamentalV1.age_ge_min
#print axioms CIGAMF.P13.CityInfoFundamentalV1.age_at_min
#print axioms CIGAMF.P13.CityInfoFundamentalV1.exit_both_ends
#print axioms CIGAMF.P13.CityInfoFundamentalV1.witness
