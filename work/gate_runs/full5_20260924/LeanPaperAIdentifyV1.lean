import «LeanPaperA7TrackingV1»

/-!
# Paper A: the learner's arrays ARE the model's, proved

`THEOREM_MAP.md` recorded as still assumed "the identification of the code's `q_t, N_e, S_e`
with the model's".  The experiment `EXP_paperA7_learner.py` keeps three accumulators and
updates them in a loop:

    W += w ;  e_t = argmax(W - N) ;  Ysum[e_t] += sampler(e_t) ;  N[e_t] += 1

while `LeanPaperA7TrackingV1` states its results about a `Tracking` structure whose `W` is a
SUM over steps, whose `N` obeys a one-step recursion, and whose `pick` satisfies a greedy
inequality.  An accumulator and a sum are not the same object, and until they are shown to
agree the theorems are about the model only.

This module closes that.  `CodeState` is the loop's own state -- the allocation it forms and
the observations the sampler returns -- and `Wcode`, `Ncode`, `Scode` are its three
accumulators written as the recursions the code performs.  Then

* `Wcode_eq_W` -- the accumulator equals the model's sum, at every step;
* `toTracking` -- the loop's state IS a `Tracking`, so every theorem of the tracking module
  applies to the arrays the code holds, with no translation;
* `Ncode_eq_visits`, `Scode_eq_sum_visits` -- the count array counts the visits and the sum
  array sums the observations at them, which is what `mu_hat = Ysum / N` means;
* `mixed_allocation_floor` -- the code's mixing rule `w = (1-1/sqrt t) w_cur + (1/sqrt t) u`
  meets the model's forced-exploration floor, with a factor of two to spare;
* `code_count_growth` -- hence `N_e(t) >= sqrt t/(2|E|) - (|E|-1)` holds of the ARRAY the
  code prints, not of a model of it.
-/

namespace CIGAMF.P13.PaperAIdentify

open scoped BigOperators
open CIGAMF.P13.PaperA7Tracking

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-! ## The loop's own state -/

/-- What the learner's loop holds: the allocation it forms at each iteration and the
observation the sampler returns.  The true world is not a field, matching the code, where
`theta` is not in scope inside `run`. -/
structure CodeState (E : Type*) [Fintype E] [DecidableEq E] where
  /-- the mixed allocation formed at iteration `s` -/
  w : ℕ → E → ℝ
  /-- the observation the sampler returns at iteration `s` for query `e` -/
  obs : ℕ → E → ℝ
  wnn : ∀ s e, 0 ≤ w s e
  wsum : ∀ s, ∑ e, w s e = 1

namespace CodeState

variable (R : CodeState E) (pick : ℕ → E)

/-- The code's `W` accumulator: `W += w` once per iteration. -/
noncomputable def Wcode : ℕ → E → ℝ
  | 0, _ => 0
  | (t + 1), e => Wcode t e + R.w (t + 1) e

/-- The code's `N` accumulator: `N[e_t] += 1`. -/
noncomputable def Ncode : ℕ → E → ℝ
  | 0, _ => 0
  | (t + 1), e => Ncode t e + (if e = pick (t + 1) then 1 else 0)

/-- The code's `Ysum` accumulator: `Ysum[e_t] += sampler(e_t)`. -/
noncomputable def Scode : ℕ → E → ℝ
  | 0, _ => 0
  | (t + 1), e => Scode t e + (if e = pick (t + 1) then R.obs (t + 1) e else 0)

/-- **The accumulator is the model's sum.** -/
theorem Wcode_eq_W (t : ℕ) (e : E) : Wcode R t e = W R.w t e := by
  induction t with
  | zero => simp [Wcode, W]
  | succ t ih =>
      show Wcode R t e + R.w (t + 1) e = W R.w (t + 1) e
      rw [ih, W, W, Finset.sum_range_succ]

/-- **The loop's state is a `Tracking`.**  Every field is the code's own update rule; the
greedy field is `e_t = argmax(W - N)` with the code's index convention, `W` already
incremented and `N` not yet. -/
noncomputable def toTracking
    (hpick : ∀ t e, W R.w (t + 1) e - Ncode pick t e
      ≤ W R.w (t + 1) (pick (t + 1)) - Ncode pick t (pick (t + 1))) :
    Tracking E where
  v := R.w
  N := Ncode pick
  pick := pick
  vnn := R.wnn
  vsum := R.wsum
  N0 := fun _ => rfl
  Nstep := fun _ _ => rfl
  greedy := hpick

/-! ## What the arrays count and sum -/

/-- **The count array counts the visits**: one unit for each step at which the greedy rule
picked this query. -/
theorem Ncode_eq_visits (t : ℕ) (e : E) :
    Ncode pick t e
      = ∑ s ∈ Finset.range t, (if e = pick (s + 1) then (1 : ℝ) else 0) := by
  classical
  induction t with
  | zero => simp [Ncode]
  | succ t ih =>
      show Ncode pick t e + (if e = pick (t + 1) then (1:ℝ) else 0) = _
      rw [ih, Finset.sum_range_succ]

/-- **The sum array sums the observations at the visits**, which is what the code's
`mu_hat = Ysum / max(N,1)` divides. -/
theorem Scode_eq_sum_visits (t : ℕ) (e : E) :
    Scode R pick t e
      = ∑ s ∈ Finset.range t, (if e = pick (s + 1) then R.obs (s + 1) e else 0) := by
  classical
  induction t with
  | zero => simp [Scode]
  | succ t ih =>
      show Scode R pick t e + (if e = pick (t + 1) then R.obs (t + 1) e else 0) = _
      rw [ih, Finset.sum_range_succ]

/-! ## The mixing rule meets the model's floor -/

/-- **The code's forced exploration is the model's, with a factor of two to spare.**  The
loop sets `rho = 1/sqrt t` and mixes the uniform allocation in at that weight, so every
query's share is at least `1/(|E| sqrt t)`, and the model asks only for `1/(2|E| sqrt t)`. -/
theorem mixed_allocation_floor (wcur : ℕ → E → ℝ) (hwcur : ∀ s e, 0 ≤ wcur s e)
    (hmix : ∀ s e, R.w s e
      = (1 - 1 / Real.sqrt s) * wcur s e + (1 / Real.sqrt s) * (1 / (Fintype.card E : ℝ)))
    (s : ℕ) (hs : 1 ≤ s) (e : E) :
    1 / (2 * (Fintype.card E : ℝ) * Real.sqrt s) ≤ R.w s e := by
  have hcard : (0 : ℝ) < (Fintype.card E : ℝ) := by
    have : 0 < Fintype.card E := Fintype.card_pos
    exact_mod_cast this
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsq : (1 : ℝ) ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hs1
  have hsqpos : (0 : ℝ) < Real.sqrt s := by linarith
  have hrho : 1 / Real.sqrt s ≤ 1 := by
    rw [div_le_one hsqpos]
    exact hsq
  have hrhopos : (0 : ℝ) < 1 / Real.sqrt s := by positivity
  have hfirst : 0 ≤ (1 - 1 / Real.sqrt s) * wcur s e :=
    mul_nonneg (by linarith) (hwcur s e)
  have hhalf : 1 / (2 * (Fintype.card E : ℝ) * Real.sqrt s)
      ≤ (1 / Real.sqrt s) * (1 / (Fintype.card E : ℝ)) := by
    rw [div_mul_div_comm, one_mul]
    apply div_le_div_of_nonneg_left one_pos.le (by positivity)
    nlinarith
  rw [hmix s e]
  linarith

/-- **The growth rate, of the code's own array.**  `forced_exploration_sqrt_growth` applied
through the identification: the numbers the experiment prints obey the bound. -/
theorem code_count_growth (wcur : ℕ → E → ℝ) (hwcur : ∀ s e, 0 ≤ wcur s e)
    (hmix : ∀ s e, R.w s e
      = (1 - 1 / Real.sqrt s) * wcur s e + (1 / Real.sqrt s) * (1 / (Fintype.card E : ℝ)))
    (hpick : ∀ t e, W R.w (t + 1) e - Ncode pick t e
      ≤ W R.w (t + 1) (pick (t + 1)) - Ncode pick t (pick (t + 1)))
    (t : ℕ) (e : E) :
    Real.sqrt t / (2 * (Fintype.card E : ℝ)) - ((Fintype.card E : ℝ) - 1)
      ≤ Ncode pick t e :=
  forced_exploration_sqrt_growth (toTracking R pick hpick) t e
    (fun s hs => mixed_allocation_floor R wcur hwcur hmix s hs e)

/-- **The tracking invariant, of the code's own array.**  The discrepancy between the
accumulator and the count never exceeds one. -/
theorem code_discrepancy_le_one
    (hpick : ∀ t e, W R.w (t + 1) e - Ncode pick t e
      ≤ W R.w (t + 1) (pick (t + 1)) - Ncode pick t (pick (t + 1)))
    (t : ℕ) (e : E) : Ncode pick t e - Wcode R t e ≤ 1 := by
  rw [Wcode_eq_W]
  exact Tracking.discrepancy_le_one (toTracking R pick hpick) t e

end CodeState

/-! ## Audit -/

#print axioms CodeState.Wcode_eq_W
#print axioms CodeState.Ncode_eq_visits
#print axioms CodeState.Scode_eq_sum_visits
#print axioms CodeState.mixed_allocation_floor
#print axioms CodeState.code_count_growth
#print axioms CodeState.code_discrepancy_le_one

end CIGAMF.P13.PaperAIdentify
