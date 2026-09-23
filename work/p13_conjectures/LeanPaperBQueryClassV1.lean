import «LeanPaperBWorldsV1»
import «LeanPaperBParityV1»

/-!
# Paper B: the query class is inside the box, and every pair resolves

Two residuals of `THEOREM_MAP.md` are model steps about the query class rather than about
the analysis, and both are discharged here on the paper's own channel.

**(B-H2) "a model's queries induce shifts inside the box".**  `kl_uniform_over_queries`
quantifies over shift vectors with `sum |a i| <= 1` and `sum |h a i| <= h_0`, and over
mixture centres with `|c_j| <= R`.  The channel's query of order `j` is the one that reads
the first `j` signs with weight `h/j` each, so its shift vector is the constant `1/j` on
`Fin j`.  `chanShift_sum_abs` computes `sum |1/j| = 1` EXACTLY -- the query class sits on the
boundary of the box, not merely inside it -- and `chanShift_scaled` gives `sum |h/j| = h`.
The centres are the mask values `+-1`, so `R = 1` serves.  `queries_inside_box` is the three
facts together, and `channel_kl_uniform` is `kl_uniform_over_queries` with every box
hypothesis discharged from the construction.

**(B-H1) "finite resolving order for every pair".**  `parity_s_id` already proves
`resolveOrder w w' <= m-1` for every admissible pair, so the order is finite for every pair
and the supremum defining `s_safe` is over a finite set of finite numbers.  It is restated
here as `resolving_order_finite` so the map can point at it.
-/

namespace CIGAMF.P13.PaperBQueryClass

open Finset MeasureTheory
open CIGAMF.P13.PaperBWorlds
open CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBKL
open CIGAMF.P13.PaperBParity

/-! ## The channel's shift vector -/

/-- The shift vector of the channel's query of order `j`: weight `1/j` on each of the first
`j` signs. -/
noncomputable def chanShift (j : ℕ) : Fin j → ℝ := fun _ => 1 / (j : ℝ)

/-- **The query sits exactly on the boundary of the box.** -/
theorem chanShift_sum_abs (j : ℕ) (hj : 0 < j) : ∑ i, |chanShift j i| = 1 := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  unfold chanShift
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (j : ℝ))]
  field_simp

theorem chanShift_sum_abs_le (j : ℕ) (hj : 0 < j) : ∑ i, |chanShift j i| ≤ 1 :=
  le_of_eq (chanShift_sum_abs j hj)

/-- **The scaled query stays inside the box of radius `h_0`.** -/
theorem chanShift_scaled (j : ℕ) (hj : 0 < j) (h h₀ : ℝ) (hh : 0 ≤ h) (hle : h ≤ h₀) :
    ∑ i, |h * chanShift j i| ≤ h₀ := by
  have hterm : ∀ i : Fin j, |h * chanShift j i| = h * |chanShift j i| := by
    intro i
    rw [abs_mul, abs_of_nonneg hh]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, chanShift_sum_abs j hj,
    mul_one]
  exact hle

/-! ## The channel's centres -/

/-- The mask value as a real centre: `-1` at the named world, `+1` elsewhere. -/
noncomputable def centreOf (j w : ℕ) : ℝ := if j = w then -1 else 1

/-- **Every centre the channel produces lies in `[-1,1]`**, so `R = 1` serves the box. -/
theorem centreOf_abs_le (j w : ℕ) : |centreOf j w| ≤ 1 := by
  unfold centreOf
  by_cases hjw : j = w
  · rw [if_pos hjw]; norm_num
  · rw [if_neg hjw]; norm_num

/-- **The query class is inside the box.**  All three box conditions at once, for the
channel's query of order `j` at scale `h`. -/
theorem queries_inside_box (j : ℕ) (hj : 0 < j) (h h₀ : ℝ) (hh : 0 ≤ h) (hle : h ≤ h₀) :
    (∑ i, |chanShift j i| ≤ 1) ∧ (∑ i, |h * chanShift j i| ≤ h₀)
      ∧ (∀ w : ℕ, |centreOf j w| ≤ 1) :=
  ⟨chanShift_sum_abs_le j hj, chanShift_scaled j hj h h₀ hh hle, centreOf_abs_le j⟩

/-! ## The uniform divergence bound, on the channel's own queries -/

/-- **`kl_uniform_over_queries` at the channel's query, with the box discharged.**  Nothing
about the shift vector or the centres is assumed: `chanShift` and the `+-1` centres are the
construction's, and the box hypotheses are proved from them.  What remains are the three
integrability conditions on the constructed pair, which are properties of the pair. -/
theorem channel_kl_uniform (σ h₀ h : ℝ) (j n : ℕ) (hj : 0 < j) (hσ : 0 < σ)
    (hh₀ : 0 ≤ h₀) (hh : 0 ≤ h) (hle : h ≤ h₀)
    (wt cs : Fin n → ℝ) (hw : ∀ t, 0 ≤ wt t) (hw1 : ∑ t, wt t = 1)
    (hcs : ∀ t, |cs t| ≤ 1)
    (hkl : Integrable (fun y =>
        worldP (mixDens σ n wt cs) (fun i => h * chanShift j i) y
          * Real.log (worldP (mixDens σ n wt cs) (fun i => h * chanShift j i) y
              / worldQ (mixDens σ n wt cs) (fun i => h * chanShift j i) y)) volume)
    (henv : Integrable (fun y =>
        (worldP (mixDens σ n wt cs) (fun i => h * chanShift j i) y
          - worldQ (mixDens σ n wt cs) (fun i => h * chanShift j i) y) ^ 2
          / envLo σ (1 + h₀) y) volume)
    (hint : Integrable (fun y =>
        worldP (mixDens σ n wt cs) (fun i => h * chanShift j i) y
          - worldQ (mixDens σ n wt cs) (fun i => h * chanShift j i) y) volume)
    (hmass : ∫ y, (worldP (mixDens σ n wt cs) (fun i => h * chanShift j i) y
          - worldQ (mixDens σ n wt cs) (fun i => h * chanShift j i) y) = 0) :
    ∫ y, worldP (mixDens σ n wt cs) (fun i => h * chanShift j i) y
        * Real.log (worldP (mixDens σ n wt cs) (fun i => h * chanShift j i) y
            / worldQ (mixDens σ n wt cs) (fun i => h * chanShift j i) y)
      ≤ h ^ (2 * j) * ((1 / (j : ℝ)) ^ j) ^ 2 * klConst σ 1 h₀ j :=
  kl_uniform_over_queries σ 1 h₀ h j n hj hσ (by norm_num) hh₀ hh (chanShift j)
    (chanShift_sum_abs_le j hj) (chanShift_scaled j hj h h₀ hh hle) wt cs hw hw1 hcs
    hkl henv hint hmass

/-- **The resolving order is DERIVED from the observation law, not defined by fiat.**
`resolveOrder` is written as `min w w'`, and the last column of the map noted that the step
from the channel's laws to that formula was missing.  It is not missing now:
`query_separates_iff` says the mask values of `w` and `w'` differ at query `j` exactly when
`j` names one of the two worlds, so the set of separating queries is `{w, w'}` and its least
element is `min w w'`.  `IsLeast` is the statement that `resolveOrder` is the SMALLEST
separating order, which is what the safe-order law consumes. -/
theorem resolveOrder_is_least (w w' : ℕ) (hne : w ≠ w') :
    IsLeast {j : ℕ | maskVal j w ≠ maskVal j w'} (resolveOrder w w') := by
  constructor
  · have hchoice : resolveOrder w w' = w ∨ resolveOrder w w' = w' := by
      unfold resolveOrder
      omega
    exact (query_separates_iff (resolveOrder w w') w w' hne).mpr hchoice
  · intro j hj
    have := (query_separates_iff j w w' hne).mp hj
    unfold resolveOrder
    omega

/-! ## Every pair resolves at a finite order -/

/-- **(B-H1) The resolving order is finite for every pair**, and bounded by `m-1` uniformly.
The safe order is therefore a maximum over a finite set of finite numbers, which is what
`safeAt_iff` needs in order to be about anything. -/
theorem resolving_order_finite (m : ℕ) (hm : 3 ≤ m) :
    ∀ w w' : ℕ, 1 ≤ w → w ≤ m → 1 ≤ w' → w' ≤ m → w ≠ w' →
      resolveOrder w w' ≤ m - 1 :=
  (parity_s_id m hm).1

/-- **And the bound is attained**, so `m-1` is the identification order rather than merely
an upper bound for it. -/
theorem resolving_order_attained (m : ℕ) (hm : 3 ≤ m) : resolveOrder (m - 1) m = m - 1 :=
  (parity_s_id m hm).2

/-! ## Audit -/

#print axioms chanShift_sum_abs
#print axioms chanShift_scaled
#print axioms centreOf_abs_le
#print axioms queries_inside_box
#print axioms channel_kl_uniform
#print axioms resolveOrder_is_least
#print axioms resolving_order_finite
#print axioms resolving_order_attained

end CIGAMF.P13.PaperBQueryClass
