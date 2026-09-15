import «LeanUniformSubsetMomentsV1»
import Mathlib

/-! A sharp algebraic variance lower bound for nonadaptive linear off-query
statistics whose mean is invariant across all q-subsets. Independent unit
Gaussian noises have variance sum(lambda^2); no adaptive optimality is claimed. -/
namespace CIGAMF.P13.D6BlindLinearVariance
open scoped BigOperators
open Finset
open CIGAMF.P13.UniformSubsetMoments
noncomputable section
variable {I T : Type*} [DecidableEq I] [Fintype T]

def coefficient (G : T → Finset I) (w : T → ℝ) (B : Finset I) : ℝ :=
  ∑ t, w t * ((G t ∩ B).card : ℝ)

lemma coefficient_as_sum (G : T → Finset I) (w : T → ℝ) (B : Finset I) :
    coefficient G w B = ∑ i ∈ B, ∑ t, w t * hit (G t) i := by
  have he (t : T) : ((G t ∩ B).card : ℝ) = ∑ i ∈ B, hit (G t) i := by
    have hf : B.filter (fun i => i ∈ G t) = G t ∩ B := by ext i; simp [and_comm]
    simpa only [hit, Finset.sum_boole] using (congrArg (fun S : Finset I => (S.card:ℝ)) hf).symm
  simp only [coefficient,he,mul_sum]
  rw [sum_comm]

/-- Hidden-label invariance forces the averaged slope; this is derived from
actual subset counts rather than assumed as a moment identity. -/
theorem invariant_slope_identity (U : Finset I) (q : ℕ) (hq : 2 ≤ q)
    (hqU : q ≤ U.card) (G : T → Finset I) (w : T → ℝ)
    (hG : ∀ t, G t ⊆ U) (a : ℝ)
    (ha : ∀ B ∈ U.powersetCard q, coefficient G w B = a) :
    (U.card : ℝ) * a = (q : ℝ) * (∑ t, w t * (G t).card) := by
  have hc : (0:ℝ) < (U.powersetCard q).card := by
    exact_mod_cast card_pos.mpr (powersetCard_nonempty.mpr hqU)
  have hn : (0:ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  have havg : avg U q (coefficient G w) = a := by
    unfold avg
    rw [sum_congr rfl ha]
    simp only [sum_const,nsmul_eq_mul]
    exact mul_div_cancel_left₀ a (ne_of_gt hc)
  have hmoment := average_weighted U q hq hqU (fun i => ∑ t, w t * hit (G t) i)
  have hin (t : T) : (∑ i ∈ U, hit (G t) i) = ((G t).card:ℝ) := by
    have hf : U.filter (fun i => i ∈ G t) = G t := by
      ext i; simp only [mem_filter]; exact ⟨fun h => h.2,fun h => ⟨hG t h,h⟩⟩
    simpa only [hit, Finset.sum_boole] using congrArg (fun S : Finset I => (S.card:ℝ)) hf
  simp_rw [← coefficient_as_sum G w] at hmoment
  rw [havg] at hmoment
  have hU : coefficient G w U = ∑ t, w t * (G t).card := by
    unfold coefficient
    simp_rw [inter_eq_left.mpr (hG _)]
  rw [hU] at hmoment
  have hh := congrArg (fun x : ℝ => (U.card:ℝ)*x) hmoment
  field_simp at hh
  nlinarith [hh]

/-- With unit independent noises this bounds the variance of the unbiased
linear estimator by |U|^2/(q^4 N), allowing signed coefficients. -/
theorem invariant_variance_lower (U : Finset I) (q : ℕ) (hq : 2 ≤ q)
    (hqU : q ≤ U.card) (G : T → Finset I) (w : T → ℝ)
    (hG : ∀ t, G t ⊆ U) (hsize : ∀ t, (G t).card ≤ q)
    (a : ℝ) (ha0 : a ≠ 0)
    (ha : ∀ B ∈ U.powersetCard q, coefficient G w B = a) :
    (U.card:ℝ)^2 ≤ (q:ℝ)^4 * Fintype.card T * ((∑ t, (w t)^2) / a^2) := by
  have hid := invariant_slope_identity U q hq hqU G w hG a ha
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset T) w (fun t => ((G t).card:ℝ))
  have hs : (∑ t, (((G t).card:ℝ))^2) ≤ (Fintype.card T:ℝ)*(q:ℝ)^2 := by
    calc
      _ ≤ ∑ _t : T, (q:ℝ)^2 := by
        apply sum_le_sum
        intro t _
        have hc : ((G t).card:ℝ) ≤ q := by exact_mod_cast hsize t
        have hc0 : (0:ℝ) ≤ (G t).card := Nat.cast_nonneg _
        nlinarith
      _ = _ := by simp
  have hw : 0 ≤ ∑ t, (w t)^2 := sum_nonneg (fun t _ => sq_nonneg _)
  have hbound := le_trans hcs (mul_le_mul_of_nonneg_left hs hw)
  have hmul := mul_le_mul_of_nonneg_left hbound (sq_nonneg (q:ℝ))
  have he : ((U.card:ℝ)*a)^2 = ((q:ℝ)*(∑ t, w t*(G t).card))^2 := congrArg (fun x : ℝ => x^2) hid
  have hfinal : (U.card:ℝ)^2*a^2 ≤ (q:ℝ)^4*Fintype.card T*(∑ t,(w t)^2) := by
    nlinarith only [hmul,he]
  have ha2 : 0 < a^2 := sq_pos_of_ne_zero ha0
  calc
    (U.card:ℝ)^2 ≤ ((q:ℝ)^4 * Fintype.card T * (∑ t, (w t)^2)) / a^2 :=
      (le_div_iff₀ ha2).2 hfinal
    _ = (q:ℝ)^4 * Fintype.card T * ((∑ t, (w t)^2) / a^2) := by ring

theorem cyclic_penalty_lt_nine (q : ℝ) (hq : 1 < q) :
    (2 + 1/q)^2 < 9 := by
  have hq0 : 0 < q := by linarith
  have h1 : 1/q < 1 := (div_lt_one hq0).mpr hq
  have h0 : 0 < 1/q := one_div_pos.mpr hq0
  nlinarith

#print axioms invariant_slope_identity
#print axioms invariant_variance_lower
#print axioms cyclic_penalty_lt_nine
end
end CIGAMF.P13.D6BlindLinearVariance
