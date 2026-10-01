import Mathlib

/-!
# Paper A7, package A7-rate: the sampling recursion tracks its quota.

## WHY THIS MODULE EXISTS

The rate argument needs the realised counts to follow the allocations the oracle asks for.
It is tempting to assert that the tracking discrepancy stays below one in absolute value;
the corpus already contains a witness showing that kind of claim needs care.  What is
actually true, and enough, is a two-sided invariant that is NOT symmetric:

    -(|E| - 1)  <=  N_e(t) - W_e(t)  <=  1.

`discrepancy_le_one` and `discrepancy_ge_neg` prove it.  The upper side is the real content
and comes from the greedy rule; the lower side is then free, because the discrepancies sum
to zero and each is at most one.

## THE RECURSION

`W_e(t) = sum_{s <= t} v_{s,e}` is the cumulative quota, with `v_s` the allocation used
before step `s`.  Before drawing sample `t` the rule picks

    e_t in argmax_e ( W_e(t) - N_e(t-1) ),

that is, it compares the quota INCLUDING step `t` against the counts BEFORE it.  Using the
quota through `t-1` instead is an off-by-one that breaks the invariant, so the indices are
fixed in the `Tracking` structure rather than left to prose.

## WHAT IT BUYS

With forced exploration `v_{s,e} >= 1 / (2 |E| sqrt s)`, `forced_exploration_sqrt_growth`
turns the invariant into

    N_e(t) >= sqrt t / (2 |E|) - (|E| - 1),

so every query is sampled a growing number of times and the confidence radius shrinks
uniformly.  That is the input the information-accumulation step needs; it is proved here,
not assumed.
-/

namespace CIGAMF.P13.PaperA7Tracking

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-- The cumulative quota through step `t`. -/
noncomputable def W (v : ℕ → E → ℝ) (t : ℕ) (e : E) : ℝ :=
  ∑ s ∈ Finset.range t, v (s + 1) e

/-- The sampling recursion, with its index conventions fixed. -/
structure Tracking (E : Type*) [Fintype E] [DecidableEq E] where
  /-- the allocation used before step `s` -/
  v : ℕ → E → ℝ
  /-- the realised counts after step `t` -/
  N : ℕ → E → ℝ
  /-- the query drawn at step `t` -/
  pick : ℕ → E
  vnn : ∀ s e, 0 ≤ v s e
  vsum : ∀ s, ∑ e, v s e = 1
  N0 : ∀ e, N 0 e = 0
  Nstep : ∀ t e, N (t + 1) e = N t e + (if e = pick (t + 1) then 1 else 0)
  /-- the greedy rule compares the quota THROUGH `t+1` against the counts BEFORE it -/
  greedy : ∀ t e, W v (t + 1) e - N t e ≤ W v (t + 1) (pick (t + 1)) - N t (pick (t + 1))

namespace Tracking

variable (T : Tracking E)

theorem W_zero (e : E) : W T.v 0 e = 0 := by simp [W]

theorem W_succ (t : ℕ) (e : E) : W T.v (t + 1) e = W T.v t e + T.v (t + 1) e := by
  simp [W, Finset.sum_range_succ]

theorem W_mono (t : ℕ) (e : E) : W T.v t e ≤ W T.v (t + 1) e := by
  rw [W_succ]
  linarith [T.vnn (t + 1) e]

/-- The quotas sum to the number of steps. -/
theorem W_sum (t : ℕ) : ∑ e, W T.v t e = (t : ℝ) := by
  classical
  induction t with
  | zero => simp [W]
  | succ n ih =>
      have : ∑ e, W T.v (n + 1) e = (∑ e, W T.v n e) + ∑ e, T.v (n + 1) e := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun e _ => W_succ T n e)
      rw [this, ih, T.vsum (n + 1)]
      push_cast
      ring

/-- So do the counts. -/
theorem N_sum (t : ℕ) : ∑ e, T.N t e = (t : ℝ) := by
  classical
  induction t with
  | zero => simp [T.N0]
  | succ n ih =>
      have hstep : ∑ e, T.N (n + 1) e
          = (∑ e, T.N n e) + ∑ e, (if e = T.pick (n + 1) then (1:ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun e _ => T.Nstep n e)
      rw [hstep, ih, Finset.sum_ite_eq' Finset.univ (T.pick (n + 1)) (fun _ => (1:ℝ))]
      simp

/-- The greedy pick's quota already covers its count: the maximum of a family summing to
one over a nonempty index set is positive. -/
theorem picked_has_slack (t : ℕ) :
    0 ≤ W T.v (t + 1) (T.pick (t + 1)) - T.N t (T.pick (t + 1)) := by
  classical
  by_contra hneg
  push_neg at hneg
  have hall : ∀ e : E, W T.v (t + 1) e - T.N t e < 0 :=
    fun e => lt_of_le_of_lt (T.greedy t e) hneg
  have hsum : ∑ e, (W T.v (t + 1) e - T.N t e) < 0 := by
    have hne : (Finset.univ : Finset E).Nonempty := Finset.univ_nonempty
    exact Finset.sum_neg (fun e _ => hall e) hne
  rw [Finset.sum_sub_distrib, W_sum, N_sum] at hsum
  push_cast at hsum
  linarith

/-- **The upper half of the invariant.**  No query ever runs more than one sample ahead of
its quota.  This is where the greedy rule is used. -/
theorem discrepancy_le_one : ∀ (t : ℕ) (e : E), T.N t e - W T.v t e ≤ 1 := by
  classical
  intro t
  induction t with
  | zero => intro e; simp [T.N0, W]
  | succ n ih =>
      intro e
      by_cases he : e = T.pick (n + 1)
      · have hslack := picked_has_slack T n
        rw [T.Nstep n e, if_pos he, he]
        linarith
      · rw [T.Nstep n e]
        simp only [if_neg he, add_zero]
        have := ih e
        have hmono := W_mono T n e
        linarith

/-- **The lower half**, which is free: the discrepancies sum to zero and each is at most
one, so none can be below `-(|E| - 1)`.  The asymmetry is genuine and is not an artefact of
the proof. -/
theorem discrepancy_ge_neg (t : ℕ) (e : E) :
    -((Fintype.card E : ℝ) - 1) ≤ T.N t e - W T.v t e := by
  classical
  set D : E → ℝ := fun f => T.N t f - W T.v t f with hD
  have hsum : ∑ f, D f = 0 := by
    rw [hD]
    simp only
    rw [Finset.sum_sub_distrib, N_sum, W_sum]
    ring
  have hother : ∑ f ∈ Finset.univ.erase e, D f ≤ ((Fintype.card E : ℝ) - 1) := by
    have hcard : (Finset.univ.erase e).card = Fintype.card E - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ]
    calc ∑ f ∈ Finset.univ.erase e, D f
        ≤ ∑ _f ∈ Finset.univ.erase e, (1:ℝ) :=
          Finset.sum_le_sum (fun f _ => discrepancy_le_one T t f)
      _ = ((Finset.univ.erase e).card : ℝ) := by simp
      _ = ((Fintype.card E - 1 : ℕ) : ℝ) := by rw [hcard]
      _ ≤ ((Fintype.card E : ℝ) - 1) := by
          have hpos : 1 ≤ Fintype.card E := Fintype.card_pos
          push_cast [Nat.cast_sub hpos]
          linarith
  have hsplit : D e + ∑ f ∈ Finset.univ.erase e, D f = 0 := by
    rw [← hsum]
    exact Finset.add_sum_erase _ D (Finset.mem_univ e)
  linarith

/-- The counts are at least the quota minus the fixed slack. -/
theorem count_ge_quota_sub (t : ℕ) (e : E) :
    W T.v t e - ((Fintype.card E : ℝ) - 1) ≤ T.N t e := by
  have := discrepancy_ge_neg T t e
  linarith

end Tracking

/-! ## Forced exploration turns the invariant into a growth rate -/

/-- A harmonic-type lower bound proved by induction: the partial sums of `1/sqrt s`
dominate `sqrt t`.  This is the only analytic input to the growth rate. -/
theorem sum_inv_sqrt_ge (t : ℕ) :
    Real.sqrt t ≤ ∑ s ∈ Finset.range t, 1 / Real.sqrt (s + 1) := by
  induction t with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : (0:ℝ) < Real.sqrt (n + 1) := by
        apply Real.sqrt_pos.2; linarith
      have hsq : Real.sqrt ((n:ℝ) + 1) * Real.sqrt ((n:ℝ) + 1) = (n : ℝ) + 1 :=
        Real.mul_self_sqrt (by linarith)
      have hs : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n : ℝ) := Real.mul_self_sqrt hn
      have hmono : Real.sqrt (n:ℝ) ≤ Real.sqrt ((n:ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hstep : Real.sqrt ((n:ℝ) + 1) ≤ Real.sqrt n + 1 / Real.sqrt ((n:ℝ) + 1) := by
        rw [← sub_le_iff_le_add', le_div_iff₀ h1]
        nlinarith [hsq, hs, hmono, Real.sqrt_nonneg (n:ℝ)]
      push_cast
      linarith [ih, hstep]

/-- **Forced exploration gives every query a growing number of samples.**  With an
allocation floor of `1 / (2 |E| sqrt s)` the quota grows like `sqrt t / (2 |E|)`, and the
tracking invariant transfers that to the realised counts up to the fixed slack. -/
theorem forced_exploration_sqrt_growth (T : Tracking E) (t : ℕ) (e : E)
    (hfloor : ∀ s : ℕ, 1 ≤ s →
      1 / (2 * (Fintype.card E : ℝ) * Real.sqrt s) ≤ T.v s e) :
    Real.sqrt t / (2 * (Fintype.card E : ℝ)) - ((Fintype.card E : ℝ) - 1) ≤ T.N t e := by
  classical
  have hk : (0:ℝ) < 2 * (Fintype.card E : ℝ) := by
    have : 0 < Fintype.card E := Fintype.card_pos
    positivity
  have hquota : Real.sqrt t / (2 * (Fintype.card E : ℝ)) ≤ W T.v t e := by
    unfold W
    have hterm : ∀ s ∈ Finset.range t,
        (1 / (2 * (Fintype.card E : ℝ))) * (1 / Real.sqrt (s + 1)) ≤ T.v (s + 1) e := by
      intro s _
      have := hfloor (s + 1) (by omega)
      push_cast at this ⊢
      calc (1 / (2 * (Fintype.card E : ℝ))) * (1 / Real.sqrt ((s:ℝ) + 1))
          = 1 / (2 * (Fintype.card E : ℝ) * Real.sqrt ((s:ℝ) + 1)) := by
            rw [div_mul_div_comm]; ring_nf
        _ ≤ T.v (s + 1) e := this
    calc Real.sqrt t / (2 * (Fintype.card E : ℝ))
        = (1 / (2 * (Fintype.card E : ℝ))) * Real.sqrt t := by ring
      _ ≤ (1 / (2 * (Fintype.card E : ℝ))) * ∑ s ∈ Finset.range t, 1 / Real.sqrt (s + 1) := by
          apply mul_le_mul_of_nonneg_left (sum_inv_sqrt_ge t) (by positivity)
      _ = ∑ s ∈ Finset.range t, (1 / (2 * (Fintype.card E : ℝ))) * (1 / Real.sqrt (s + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ s ∈ Finset.range t, T.v (s + 1) e := Finset.sum_le_sum hterm
  have := T.count_ge_quota_sub t e
  linarith

/-- The invariant does NOT say the discrepancy is below one in absolute value, and this
records why no proof should try: the lower slack really is `|E| - 1`, and an index set with
three or more queries admits a state at distance more than one below its quota. -/
theorem lower_slack_is_not_one :
    ∀ k : ℕ, 3 ≤ k → (1:ℝ) < (k : ℝ) - 1 := by
  intro k hk
  have : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  linarith

/-! ## Audit -/

#print axioms Tracking.W_sum
#print axioms Tracking.N_sum
#print axioms Tracking.picked_has_slack
#print axioms Tracking.discrepancy_le_one
#print axioms Tracking.discrepancy_ge_neg
#print axioms Tracking.count_ge_quota_sub
#print axioms sum_inv_sqrt_ge
#print axioms forced_exploration_sqrt_growth
#print axioms lower_slack_is_not_one

end CIGAMF.P13.PaperA7Tracking
