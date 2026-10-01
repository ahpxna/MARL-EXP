import Mathlib

/-!
# Paper B: the safe-observation order

A world is decided safely when the observer can name an answer that is safe in every world
it cannot yet tell apart.  `Together sep s H` says the observer at order `s` cannot separate
any pair inside `H`; `Unsafe safe H` says `H` admits no common safe answer.  `SafeAt sep
safe s` is then the law: at order `s`, no set the observer still holds together is unsafe.

`safeAt_iff` restates it contrapositively -- every unsafe set contains a pair the observer
separates by order `s` -- which is the form the downstream modules consume.

`sep` is DATA here: nothing in this module says it is the order at which the observer's own
queries begin to separate a pair.  `LeanPaperBSepDerivedV1` removes that, by reading `sep`
off a separation predicate and proving the table is then determined.
-/

namespace CIGAMF.P13.PaperBSafe

open Finset

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

/-- `H` admits no answer safe in all of its worlds. -/
def Unsafe (safe : W → Finset A) (H : Finset W) : Prop :=
  ∀ a : A, ∃ w ∈ H, a ∉ safe w

/-- At order `s` the observer separates no pair inside `H`. -/
def Together (sep : W → W → ℕ) (s : ℕ) (H : Finset W) : Prop :=
  ∀ w ∈ H, ∀ w' ∈ H, s < sep w w'

/-- **The safe-order law.**  Order `s` suffices when no set the observer still holds
together is unsafe. -/
def SafeAt (sep : W → W → ℕ) (safe : W → Finset A) (s : ℕ) : Prop :=
  ∀ H : Finset W, Together sep s H → ¬ Unsafe safe H

/-- **The law, contrapositively.**  Order `s` suffices exactly when every unsafe set
contains a pair separated by order `s`.  This is the form that is checkable: it quantifies
over obstructions rather than over everything the observer might hold together. -/
theorem safeAt_iff (sep : W → W → ℕ) (safe : W → Finset A) (s : ℕ) :
    SafeAt sep safe s ↔
      ∀ H : Finset W, Unsafe safe H → ∃ w ∈ H, ∃ w' ∈ H, sep w w' ≤ s := by
  constructor
  · intro hs H hH
    by_contra hcon
    push_neg at hcon
    exact hs H (fun w hw w' hw' => hcon w hw w' hw') hH
  · intro hs H htog hH
    obtain ⟨w, hw, w', hw', hle⟩ := hs H hH
    exact absurd (htog w hw w' hw') (by omega)

/-- **A wider order is still safe.**  Separating more pairs cannot create an obstruction. -/
theorem safeAt_mono (sep : W → W → ℕ) (safe : W → Finset A) {s s' : ℕ} (hss : s ≤ s')
    (h : SafeAt sep safe s) : SafeAt sep safe s' := by
  rw [safeAt_iff] at h ⊢
  intro H hH
  obtain ⟨w, hw, w', hw', hle⟩ := h H hH
  exact ⟨w, hw, w', hw', le_trans hle hss⟩

/-- **A set held together at a wider order is held together at a narrower one.** -/
theorem together_mono (sep : W → W → ℕ) {s s' : ℕ} (hss : s ≤ s') (H : Finset W)
    (h : Together sep s' H) : Together sep s H :=
  fun w hw w' hw' => lt_of_le_of_lt hss (h w hw w' hw')

/-- **A common safe answer makes a set safe**, which is the only way `Unsafe` fails. -/
theorem not_unsafe_iff (safe : W → Finset A) (H : Finset W) :
    ¬ Unsafe safe H ↔ ∃ a : A, ∀ w ∈ H, a ∈ safe w := by
  unfold Unsafe
  push_neg
  rfl

/-! ## Audit -/

#print axioms safeAt_iff
#print axioms safeAt_mono
#print axioms together_mono
#print axioms not_unsafe_iff

end CIGAMF.P13.PaperBSafe
