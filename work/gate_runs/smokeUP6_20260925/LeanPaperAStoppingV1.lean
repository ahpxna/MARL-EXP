import Mathlib

/-!
# Paper A7: the stopping time, allowed to be infinite

`LeanAdaptiveExpectedStoppingV1` proves the layer-cake identity for an `Nat`-valued stopping
time, and `fixed_level_gives_no_summable_tail` records that a constant error level gives no
summable tail.  Neither is re-proved here.

What neither supplies is the step before them.  A stopping time DEFINED as
`tau : Omega -> Nat` has termination built into its type: there is no value for a path on
which the rule never fires, so "the algorithm terminates" cannot be a theorem about it.  The
hitting time has to be allowed the value infinity first, and finiteness has to be DERIVED.

This file supplies that, and one thing more.  The panel reports a RESTRICTED mean
`E[min(tau, B)]` on runs that did not stop, and it matters that this is a different quantity
from `E[tau]`: on a path that never fires, the restricted quantity records the budget `B`
while the stopping time is infinite.  Substituting `B` for infinity and calling the result an
expected stopping time is the error the separation below names.
-/

namespace CIGAMF.P13.PaperAStopping


variable {p : ℕ → Prop} [DecidablePred p]

open Classical in
/-- **The hitting time, allowed to be infinite.**  No finiteness is built into the type. -/
noncomputable def hitTime (p : ℕ → Prop) [DecidablePred p] : ℕ∞ :=
  if h : ∃ n, p n then ((Nat.find h : ℕ) : ℕ∞) else ⊤

theorem hitTime_eq_top_iff : hitTime p = ⊤ ↔ ∀ n, ¬ p n := by
  unfold hitTime
  by_cases h : ∃ n, p n
  · rw [dif_pos h]
    constructor
    · intro hc
      exact absurd hc (by exact_mod_cast ENat.coe_ne_top _)
    · intro hall
      obtain ⟨n, hn⟩ := h
      exact absurd hn (hall n)
  · rw [dif_neg h]
    push_neg at h
    exact ⟨fun _ => h, fun _ => rfl⟩

theorem hitTime_lt_top_iff : hitTime p < ⊤ ↔ ∃ n, p n := by
  rw [lt_top_iff_ne_top, Ne, hitTime_eq_top_iff]
  push_neg
  rfl

/-- **Termination is a theorem about the path, not a fact about the type.** -/
theorem hitTime_finite_of_fires (h : ∃ n, p n) : hitTime p ≠ ⊤ := by
  rw [Ne, hitTime_eq_top_iff]
  push_neg
  exact h

/-- Its value, when it is finite. -/
theorem hitTime_eq_find (h : ∃ n, p n) : hitTime p = ((Nat.find h : ℕ) : ℕ∞) := by
  unfold hitTime
  rw [dif_pos h]

/-- **The tail event, pathwise**: the hitting time exceeds `t` exactly when nothing has
fired by `t`.  This is the event a summable bound has to bound. -/
theorem lt_hitTime_iff (t : ℕ) : (t : ℕ∞) < hitTime p ↔ ∀ n ≤ t, ¬ p n := by
  unfold hitTime
  by_cases h : ∃ n, p n
  · rw [dif_pos h]
    constructor
    · intro hlt n hn hpn
      have : Nat.find h ≤ n := Nat.find_le hpn
      have hlt' : t < Nat.find h := by exact_mod_cast hlt
      omega
    · intro hall
      have : t < Nat.find h := by
        by_contra hc
        push_neg at hc
        exact hall (Nat.find h) hc (Nat.find_spec h)
      exact_mod_cast this
  · rw [dif_neg h]
    push_neg at h
    exact ⟨fun _ n _ => h n, fun _ => by exact lt_of_le_of_ne le_top (by simp)⟩

/-! ## The restricted quantity is not the stopping time -/

open Classical in
/-- What a censored run contributes to a restricted mean. -/
noncomputable def truncAt (B : ℕ) (p : ℕ → Prop) [DecidablePred p] : ℕ :=
  if h : ∃ n, p n then min (Nat.find h) B else B

/-- **On a path that never fires the two disagree completely**: the restricted quantity
records the budget, the stopping time is infinite.  Reporting the first as the second is the
substitution this states cannot be made. -/
theorem trunc_ne_hitTime_of_never (B : ℕ) (h : ∀ n, ¬ p n) :
    hitTime p = ⊤ ∧ truncAt B p = B := by
  refine ⟨hitTime_eq_top_iff.mpr h, ?_⟩
  unfold truncAt
  rw [dif_neg (by push_neg; exact h)]

/-- **And they agree exactly when the rule fires within the budget.** -/
theorem trunc_eq_hitTime_iff (B : ℕ) (h : ∃ n, p n) :
    (truncAt B p : ℕ∞) = hitTime p ↔ Nat.find h ≤ B := by
  rw [hitTime_eq_find h]
  unfold truncAt
  rw [dif_pos h]
  constructor
  · intro hc
    have : min (Nat.find h) B = Nat.find h := by exact_mod_cast hc
    omega
  · intro hle
    have : min (Nat.find h) B = Nat.find h := min_eq_left hle
    rw [this]

/-! ## Audit -/

#print axioms hitTime_eq_top_iff
#print axioms hitTime_lt_top_iff
#print axioms hitTime_finite_of_fires
#print axioms lt_hitTime_iff
#print axioms trunc_ne_hitTime_of_never
#print axioms trunc_eq_hitTime_iff

end CIGAMF.P13.PaperAStopping
