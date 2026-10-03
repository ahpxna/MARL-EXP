import Mathlib
import LeanMarlMismatchW1V1

/-!
# Training on a mixture of channels bounds the worst-case mismatch: why the mixture receiver covers the feasible set

Ledger L-256 (E4, PROTOCOL_E3_MIXED_CHANNEL): one receiver trained on the balanced mixture of iid / K = 1 / 2 / 3 is never
below compiled silence (MX1), loses nothing at iid (MX2), and has the best worst case of the three receivers; a specialist
keeps a ≈ 1-point premium at its own corner (MX3 failed).  On top of `LeanMarlMismatchW1V1` (W1 on the ages, the Lipschitz
value bound) this file proves the distance part of that picture for N training regimes p_1 … p_N with pairwise W1 ≤ D:

## WHAT IS PROVED
* `cum_wsum`, `w1_wsum_le` — W1 to a fixed histogram is convex under any finite weighted mixture.
* `w1_self`, `w1_comm` — W1(p, p) = 0 and symmetry.
* `mixture_minimax` — the uniform mixture is within ((N − 1)/N)·D of EVERY regime, whereas a specialist trained on one
  regime is at distance up to D from another (the diameter): the mixture's worst case is strictly better when D > 0, and it
  pays at most ((N − 1)/N)·D at a specialist's own corner (the specialist premium is bounded, not zero).
* `mixture_value_gap` — with an L-Lipschitz age response and normalised histograms, the value under any regime differs from
  the value under the mixture by at most L ((N − 1)/N) D.
* `mixture_witness` — two regimes δ₀, δ₁ (D = 1): the mixture is at W1 = 1/2 = ((2 − 1)/2)·1 from both (attained), the
  specialist δ₀ at 1 from δ₁.

## WHAT THIS DOES NOT ESTABLISH
- That a receiver trained on the mixture HAS the mixture's age response (it may also learn regime-conditional behaviour,
  hypothesis H-RID, untested); the measured E4 gains (L-256) are empirical.
-/

namespace CIGAMF.P13.MarlMixtureV1

open Finset CIGAMF.P13.MarlMismatchW1V1

theorem cum_wsum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (p : ι → ℕ → ℝ) (a : ℕ) :
    cum (fun b => ∑ k ∈ s, w k * p k b) a = ∑ k ∈ s, w k * cum (p k) a := by
  unfold cum; simp_rw [mul_sum]; exact sum_comm

theorem w1_wsum_le {ι : Type*} (n : ℕ) (s : Finset ι) (w : ι → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k) (hsum : ∑ k ∈ s, w k = 1)
    (p : ι → ℕ → ℝ) (q : ℕ → ℝ) :
    w1 n (fun b => ∑ k ∈ s, w k * p k b) q ≤ ∑ k ∈ s, w k * w1 n (p k) q := by
  have key : ∀ a, |cum (fun b => ∑ k ∈ s, w k * p k b) a - cum q a| ≤ ∑ k ∈ s, w k * |cum (p k) a - cum q a| := by
    intro a
    rw [cum_wsum]
    have e : ∑ k ∈ s, w k * cum (p k) a - cum q a = ∑ k ∈ s, w k * (cum (p k) a - cum q a) := by
      simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hsum, one_mul]
    rw [e]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun k hk => ?_))
    rw [abs_mul, abs_of_nonneg (hw k hk)]
  unfold w1
  calc ∑ a ∈ range n, |cum (fun b => ∑ k ∈ s, w k * p k b) a - cum q a|
      ≤ ∑ a ∈ range n, ∑ k ∈ s, w k * |cum (p k) a - cum q a| := sum_le_sum fun a _ => key a
    _ = ∑ k ∈ s, w k * ∑ a ∈ range n, |cum (p k) a - cum q a| := by rw [sum_comm]; simp_rw [mul_sum]

theorem w1_self (n : ℕ) (p : ℕ → ℝ) : w1 n p p = 0 := by simp [w1]

theorem w1_comm (n : ℕ) (p q : ℕ → ℝ) : w1 n p q = w1 n q p := by
  unfold w1; exact sum_congr rfl fun a _ => abs_sub_comm _ _

/-- The uniform mixture of `N` regimes. -/
noncomputable def mix {N : ℕ} (p : Fin N → ℕ → ℝ) : ℕ → ℝ := fun b => ∑ k, (1 / N : ℝ) * p k b

theorem mixture_minimax {N : ℕ} (hN : 0 < N) (p : Fin N → ℕ → ℝ) (n : ℕ) (D : ℝ) (hD : ∀ k j, w1 n (p k) (p j) ≤ D)
    (j : Fin N) : w1 n (mix p) (p j) ≤ ((N - 1) / N : ℝ) * D := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsum : ∑ _k : Fin N, (1 / N : ℝ) = 1 := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have h := w1_wsum_le n univ (fun _ => (1 / N : ℝ)) (fun _ _ => by positivity) hsum p (p j)
  have hcard : ((univ.erase j).card : ℝ) = (N : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne'), Nat.cast_one]
  have hrest : ∑ k ∈ univ.erase j, w1 n (p k) (p j) ≤ ((N : ℝ) - 1) * D := by
    calc ∑ k ∈ univ.erase j, w1 n (p k) (p j) ≤ ∑ _k ∈ univ.erase j, D := sum_le_sum fun k _ => hD k j
      _ = ((N : ℝ) - 1) * D := by rw [sum_const, nsmul_eq_mul, hcard]
  calc w1 n (mix p) (p j) ≤ ∑ k, (1 / N : ℝ) * w1 n (p k) (p j) := h
    _ = (1 / N : ℝ) * ∑ k ∈ univ.erase j, w1 n (p k) (p j) := by
        rw [← mul_sum, ← add_sum_erase _ _ (mem_univ j), w1_self, zero_add]
    _ ≤ (1 / N : ℝ) * (((N : ℝ) - 1) * D) := by gcongr
    _ = ((N - 1) / N : ℝ) * D := by field_simp

theorem mixture_value_gap {N : ℕ} (hN : 0 < N) (p : Fin N → ℕ → ℝ) (n : ℕ) (D L : ℝ) (hD : ∀ k j, w1 n (p k) (p j) ≤ D)
    (hL : 0 ≤ L) (hmass : ∀ k, ∑ a ∈ range (n + 1), p k a = 1) (g : ℕ → ℝ) (hg : ∀ a, a < n → |g a - g (a + 1)| ≤ L)
    (j : Fin N) :
    |∑ a ∈ range (n + 1), (p j a - mix p a) * g a| ≤ L * (((N - 1) / N : ℝ) * D) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hm : ∑ a ∈ range (n + 1), mix p a = 1 := by
    unfold mix; rw [sum_comm]; simp_rw [← mul_sum, hmass]
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hb := lipschitz_w1_bound (p j) (mix p) g n L hg (by rw [hmass j, hm])
  rw [w1_comm] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (mixture_minimax hN p n D hD j) hL)

/-- Witness: δ₀ and δ₁ on the ages {0, 1}. -/
def delta (i : ℕ) : ℕ → ℝ := fun a => if a = i then 1 else 0
def twoRegimes : Fin 2 → ℕ → ℝ := fun k => delta k

theorem mixture_witness :
    w1 1 (twoRegimes 0) (twoRegimes 1) = 1 ∧ w1 1 (mix twoRegimes) (twoRegimes 0) = 1 / 2 ∧
    w1 1 (mix twoRegimes) (twoRegimes 1) = 1 / 2 ∧ ((2 - 1) / 2 : ℝ) * 1 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, by norm_num⟩ <;>
    norm_num [w1, cum, mix, twoRegimes, delta, Fin.sum_univ_two, abs_of_nonneg, abs_of_nonpos]

end CIGAMF.P13.MarlMixtureV1

#print axioms CIGAMF.P13.MarlMixtureV1.w1_wsum_le
#print axioms CIGAMF.P13.MarlMixtureV1.mixture_minimax
#print axioms CIGAMF.P13.MarlMixtureV1.mixture_value_gap
#print axioms CIGAMF.P13.MarlMixtureV1.mixture_witness
