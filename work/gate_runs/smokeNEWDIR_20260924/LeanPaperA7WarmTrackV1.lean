import «LeanPaperA7TrackingV1»
import «LeanPaperA7AccumulationV1»

/-!
# Paper A7: the tracking of the ACTUAL learner, warm start included

`scripts/EXP_paperA7_learner.py` (function `run`) does not start its counts at zero: it draws
ONE sample of every cell first (`N = 1` for all `K` cells, total time `t = K`), keeps the
cumulative quota `W` starting at `0`, and then, at total time `t >= K`,

    rho = 1 / sqrt(t + 1);   w = (1 - rho) w_cur + rho u;   W += w;   e_t = argmax(W - N);
    N[e_t] += 1;   t += 1.

`LeanPaperA7TrackingV1.Tracking` is the start-at-zero recursion, so it may NOT be applied to
these counts directly.  `WarmRun` records the code's recursion as it is; `WarmRun.shifted` is
the start-at-zero tracker for `N - 1` (the greedy rule is unchanged by a uniform shift), and all
bounds are transferred back:

* `N_sum`: `sum_e N_e(k) = k + K` -- the design `N(k) / (k + K)` is an allocation;
* `discrepancy`: `-(K - 1) <= N_e(k) - 1 - W_e(k) <= 1`;
* `warm_htrack`: with the warm rounds read as rounds of target `u` (`rho_s = 1`, `s < K`) and
  round `K + k` as the code's target, the counts' design is within `2(K-1) / (K + k)` of the
  average target in `l1` -- exactly the tracking input `htrack` of
  `LeanPaperA7AccumulationV1.accumulation_window`, at the TOTAL time `K + k`;
* `warm_count_ge`: under the code's forcing `rho = 1/sqrt(t+1)`,
  `N_e(k) >= sqrt(K + k) / K - (K - 1)` -- the count growth the confidence radius needs.
-/

namespace CIGAMF.P13.PaperA7WarmTrack

open Finset
open CIGAMF.P13.PaperA7Tracking CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7Accumulation

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-- The learner's sampling recursion after its warm start (post-warm step `k`). -/
structure WarmRun (E : Type*) [Fintype E] [DecidableEq E] where
  /-- the target added to the quota at post-warm step `k + 1` -/
  v : ℕ → E → ℝ
  /-- the counts after `k` post-warm steps, INCLUDING the warm sample -/
  N : ℕ → E → ℝ
  pick : ℕ → E
  vnn : ∀ s e, 0 ≤ v s e
  vsum : ∀ s, ∑ e, v s e = 1
  N0 : ∀ e, N 0 e = 1
  Nstep : ∀ t e, N (t + 1) e = N t e + (if e = pick (t + 1) then 1 else 0)
  /-- `argmax (W - N)` after `W += w`, as in the code -/
  greedy : ∀ t e, W v (t + 1) e - N t e ≤ W v (t + 1) (pick (t + 1)) - N t (pick (t + 1))

namespace WarmRun

variable (R : WarmRun E)

/-- The start-at-zero tracker of the post-warm counts `N - 1`. -/
def shifted : Tracking E where
  v := R.v
  N t e := R.N t e - 1
  pick := R.pick
  vnn := R.vnn
  vsum := R.vsum
  N0 e := by rw [R.N0]; ring
  Nstep t e := by rw [R.Nstep]; ring
  greedy t e := by have := R.greedy t e; linarith

theorem N_sum (t : ℕ) : ∑ e, R.N t e = t + Fintype.card E := by
  have h := (R.shifted).N_sum t
  have : ∑ e, (R.shifted).N t e = ∑ e, R.N t e - Fintype.card E := by
    show ∑ e, (R.N t e - 1) = _
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  linarith

theorem discrepancy (t : ℕ) (e : E) :
    -((Fintype.card E : ℝ) - 1) ≤ R.N t e - 1 - W R.v t e ∧ R.N t e - 1 - W R.v t e ≤ 1 :=
  ⟨(R.shifted).discrepancy_ge_neg t e, (R.shifted).discrepancy_le_one t e⟩

end WarmRun

/-- A family bounded above by one and summing to zero has `l1` norm at most `2 (K - 1)`. -/
theorem l1_of_le_one (D : E → ℝ) (hle : ∀ e, D e ≤ 1) (hsum : ∑ e, D e = 0) :
    ∑ e, |D e| ≤ 2 * ((Fintype.card E : ℝ) - 1) := by
  obtain ⟨e0, he0⟩ : ∃ e0, D e0 ≤ 0 := by
    by_contra h
    push Not at h
    have := Finset.sum_pos (fun e _ => h e) Finset.univ_nonempty
    linarith
  have habs : ∀ e, |D e| = 2 * max (D e) 0 - D e := by
    intro e
    rcases le_total 0 (D e) with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_nonpos h, max_eq_right h]; ring
  have hmax : ∑ e, max (D e) 0 ≤ (Fintype.card E : ℝ) - 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0), max_eq_right he0, zero_add]
    calc ∑ e ∈ univ.erase e0, max (D e) 0 ≤ ∑ _e ∈ univ.erase e0, (1 : ℝ) :=
          sum_le_sum fun e _ => max_le (hle e) zero_le_one
      _ = (Fintype.card E : ℝ) - 1 := by
          rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul, mul_one,
            Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  calc ∑ e, |D e| = ∑ e, (2 * max (D e) 0 - D e) := sum_congr rfl fun e _ => habs e
    _ = 2 * ∑ e, max (D e) 0 - ∑ e, D e := by rw [sum_sub_distrib, mul_sum]
    _ ≤ 2 * ((Fintype.card E : ℝ) - 1) := by rw [hsum]; linarith

/-- The average target over the total time `K + k` is `(1 + W_e(k)) / (K + k)`. -/
theorem avgTarget_warm (R : WarmRun E) (w : ℕ → E → ℝ) (ρ : ℕ → ℝ) (u : E → ℝ)
    (hu : ∀ e, u e = 1 / Fintype.card E)
    (hwarm : ∀ s, s < Fintype.card E → ρ s = 1)
    (hpost : ∀ k e, target w ρ u (Fintype.card E + k) e = R.v (k + 1) e) (k : ℕ) (e : E) :
    avgTarget w ρ u (Fintype.card E + k) e
      = (1 + W R.v k e) / ((Fintype.card E + k : ℕ) : ℝ) := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  unfold avgTarget
  rw [← Finset.mul_sum, Finset.sum_range_add]
  have hwarmsum : ∑ s ∈ range (Fintype.card E), target w ρ u s e = 1 := by
    have : ∀ s ∈ range (Fintype.card E), target w ρ u s e = 1 / Fintype.card E := by
      intro s hs
      unfold target
      rw [hwarm s (mem_range.mp hs), hu]
      ring
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
    field_simp
  have hpostsum : ∑ j ∈ range k, target w ρ u (Fintype.card E + j) e = W R.v k e := by
    unfold W
    exact sum_congr rfl fun j _ => hpost j e
  rw [hwarmsum, hpostsum]
  ring

/-- **The tracking input of the accumulation theorem, for the actual learner.** -/
theorem warm_htrack (R : WarmRun E) (w : ℕ → E → ℝ) (ρ : ℕ → ℝ) (u : E → ℝ)
    (hu : ∀ e, u e = 1 / Fintype.card E)
    (hwarm : ∀ s, s < Fintype.card E → ρ s = 1)
    (hpost : ∀ k e, target w ρ u (Fintype.card E + k) e = R.v (k + 1) e) (k : ℕ) :
    ∑ e, |R.N k e / ((Fintype.card E + k : ℕ) : ℝ) - avgTarget w ρ u (Fintype.card E + k) e|
      ≤ 2 * ((Fintype.card E : ℝ) - 1) / ((Fintype.card E + k : ℕ) : ℝ) := by
  have hT : (0 : ℝ) < ((Fintype.card E + k : ℕ) : ℝ) := by
    have : 0 < Fintype.card E + k := Nat.add_pos_left Fintype.card_pos k
    exact_mod_cast this
  set D : E → ℝ := fun e => R.N k e - 1 - W R.v k e with hD
  have hW : ∑ e, W R.v k e = (k : ℝ) := (R.shifted).W_sum k
  have hsumD : ∑ e, D e = 0 := by
    rw [hD]
    simp only
    rw [sum_sub_distrib, sum_sub_distrib, R.N_sum, hW, sum_const, card_univ,
      nsmul_eq_mul, mul_one]
    ring
  have hl1 := l1_of_le_one D (fun e => (R.discrepancy k e).2) hsumD
  have hterm : ∀ e, |R.N k e / ((Fintype.card E + k : ℕ) : ℝ)
      - avgTarget w ρ u (Fintype.card E + k) e| = |D e| / ((Fintype.card E + k : ℕ) : ℝ) := by
    intro e
    rw [avgTarget_warm R w ρ u hu hwarm hpost k e, ← sub_div, abs_div, abs_of_pos hT]
    congr 2
    rw [hD]
    ring
  rw [sum_congr rfl fun e _ => hterm e, ← sum_div]
  exact div_le_div_of_nonneg_right hl1 hT.le

/-- `sum_{j < k} 1/sqrt(K + j + 1) >= sqrt(K + k) - K`. -/
theorem sum_inv_sqrt_shift_ge (K k : ℕ) :
    Real.sqrt ((K + k : ℕ) : ℝ) - K ≤ ∑ j ∈ range k, 1 / Real.sqrt ((K + j : ℕ) + 1) := by
  have htot := sum_inv_sqrt_ge (K + k)
  rw [Finset.sum_range_add] at htot
  have hhead : ∑ s ∈ range K, 1 / Real.sqrt ((s : ℝ) + 1) ≤ K := by
    calc ∑ s ∈ range K, 1 / Real.sqrt ((s : ℝ) + 1) ≤ ∑ _s ∈ range K, (1 : ℝ) := by
          refine sum_le_sum fun s _ => ?_
          rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
          exact Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
      _ = K := by simp
  have htail : ∑ x ∈ range k, 1 / Real.sqrt (((K + x : ℕ) : ℝ) + 1)
      = ∑ j ∈ range k, 1 / Real.sqrt ((K + j : ℕ) + 1) := rfl
  push_cast at htot htail ⊢
  linarith

/-- **Forced exploration of the actual learner.**  If the code's target at post-warm step
`k + 1` puts at least `rho_(K+k) / K = 1 / (K sqrt(K + k + 1))` on every cell, then every
count grows like `sqrt` of the total time. -/
theorem warm_count_ge (R : WarmRun E) (e : E)
    (hfloor : ∀ j : ℕ,
      1 / ((Fintype.card E : ℝ) * Real.sqrt ((Fintype.card E + j : ℕ) + 1)) ≤ R.v (j + 1) e)
    (k : ℕ) :
    Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) / Fintype.card E - ((Fintype.card E : ℝ) - 1)
      ≤ R.N k e := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hW : (Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) - Fintype.card E) / Fintype.card E
      ≤ W R.v k e := by
    unfold W
    calc (Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) - Fintype.card E) / Fintype.card E
        ≤ (∑ j ∈ range k, 1 / Real.sqrt ((Fintype.card E + j : ℕ) + 1)) / Fintype.card E :=
          div_le_div_of_nonneg_right (sum_inv_sqrt_shift_ge _ k) hK.le
      _ = ∑ j ∈ range k, 1 / ((Fintype.card E : ℝ) * Real.sqrt ((Fintype.card E + j : ℕ) + 1)) := by
          rw [sum_div]
          refine sum_congr rfl fun j _ => ?_
          rw [div_div, mul_comm]
      _ ≤ ∑ j ∈ range k, R.v (j + 1) e := sum_le_sum fun j _ => hfloor j
  have hd := (R.discrepancy k e).1
  have : (Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) - Fintype.card E) / Fintype.card E
      = Real.sqrt ((Fintype.card E + k : ℕ) : ℝ) / Fintype.card E - 1 := by
    field_simp
  linarith

/-- The code's forcing gives that floor: `(1 - rho) w + rho u >= rho / K` for an allocation
`w`, with `rho = 1/sqrt(t+1)` at total time `t = K + k`. -/
theorem code_target_floor (w u : E → ℝ) (hw : ∀ e, 0 ≤ w e) (hu : ∀ e, u e = 1 / Fintype.card E)
    (t : ℕ) (e : E) :
    1 / ((Fintype.card E : ℝ) * Real.sqrt (t + 1))
      ≤ (1 - 1 / Real.sqrt (t + 1)) * w e + 1 / Real.sqrt (t + 1) * u e := by
  have hs : 1 ≤ Real.sqrt ((t : ℝ) + 1) := Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)])
  have hρ : 1 / Real.sqrt ((t : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hs
  have h1 : 0 ≤ (1 - 1 / Real.sqrt ((t : ℝ) + 1)) * w e := mul_nonneg (by linarith) (hw e)
  rw [hu]
  have : 1 / ((Fintype.card E : ℝ) * Real.sqrt (t + 1)) = 1 / Real.sqrt (t + 1) * (1 / Fintype.card E) := by
    rw [one_div_mul_one_div, mul_comm]
  linarith

#print axioms WarmRun.N_sum
#print axioms WarmRun.discrepancy
#print axioms l1_of_le_one
#print axioms warm_htrack
#print axioms warm_count_ge
#print axioms code_target_floor

end CIGAMF.P13.PaperA7WarmTrack
