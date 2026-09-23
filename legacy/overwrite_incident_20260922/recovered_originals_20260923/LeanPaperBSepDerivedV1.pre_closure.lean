import «LeanPaperBSafeOrderV1»
import «LeanPaperBQueryClassV1»

/-!
# Paper B: the separation order is read off the query model

`LeanPaperBSafeOrderV1` states the safe-order law in terms of a function
`sep : W -> W -> Nat`, and `Together sep s H` is `s < sep` on every pair of `H`.  The last
column of `THEOREM_MAP.md` recorded the honest objection: `sep` is DATA there.  Nothing says
it is the order at which the observer's own queries begin to separate the pair, so
`SafeAt` was a statement about a table rather than about a query model, and the orders it
produces were not sample complexities of anything.

This module removes that.  Fix a separation predicate

    Sep : Nat -> W -> W -> Prop,      "some admissible query of order j separates the pair",

and say that `sep` is READ OFF it when `sep w w'` is the LEAST such order.  Then

* `together_iff_no_separating_query` -- `Together sep s H` holds exactly when no admissible
  query of order at most `s` separates any pair inside `H`.  So the hypothesis of the law is
  a statement about queries, not about the table.
* `safeAt_iff_query` -- the law itself, restated over the query model.
* `sep_symm_of_least`, `sep_unique` -- `sep` is determined by `Sep`, so there is no freedom
  left in the table.

On the paper's own channel the hypothesis is discharged rather than assumed:
`resolveOrder_is_least` proves `IsLeast {j | maskVal j w /= maskVal j w'} (resolveOrder w w')`,
so `channel_sep_is_read_off` instantiates everything above at `resolveOrder`.

WHAT IS STILL NOT HERE.  `Sep` is a predicate on orders, and the passage from "the
characteristic functions differ at order `j`" to "a test on `N` samples distinguishes the
pair" is the sample-complexity step, which lives in `LeanPaperBHoeffdingV1` for the channel
and is open for an arbitrary family.
-/

namespace CIGAMF.P13.PaperBSepDerived

open Finset
open CIGAMF.P13.PaperBSafe
open CIGAMF.P13.PaperBParity
open CIGAMF.P13.PaperBQueryClass

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

/-- `sep` is read off the query model when each entry is the least order at which some
admissible query separates the pair. -/
def ReadsOff (Sep : ℕ → W → W → Prop) (sep : W → W → ℕ) : Prop :=
  ∀ w w' : W, IsLeast {j : ℕ | Sep j w w'} (sep w w')

/-- **The table is determined.**  Two functions read off the same query model agree, so
nothing downstream depends on a choice. -/
theorem sep_unique (Sep : ℕ → W → W → Prop) (sep sep' : W → W → ℕ)
    (h : ReadsOff Sep sep) (h' : ReadsOff Sep sep') : sep = sep' := by
  funext w w'
  exact IsLeast.unique (h w w') (h' w w')

/-- **`sep` is symmetric when the query model is.** -/
theorem sep_symm_of_least (Sep : ℕ → W → W → Prop) (sep : W → W → ℕ)
    (h : ReadsOff Sep sep) (hsymm : ∀ j w w', Sep j w w' ↔ Sep j w' w) (w w' : W) :
    sep w w' = sep w' w := by
  refine IsLeast.unique (h w w') ?_
  obtain ⟨hmem, hlb⟩ := h w' w
  refine ⟨(hsymm _ _ _).mpr hmem, fun j hj => hlb ((hsymm _ _ _).mp hj)⟩

/-- **The law's hypothesis, in the query model's own words.**  `Together` says exactly that
no admissible query of order at most `s` separates any pair of `H`. -/
theorem together_iff_no_separating_query (Sep : ℕ → W → W → Prop) (sep : W → W → ℕ)
    (h : ReadsOff Sep sep) (s : ℕ) (H : Finset W) :
    Together sep s H ↔ ∀ w ∈ H, ∀ w' ∈ H, ∀ j ≤ s, ¬ Sep j w w' := by
  constructor
  · intro htog w hw w' hw' j hj hsep
    have hle : sep w w' ≤ j := (h w w').2 hsep
    have := htog w hw w' hw'
    omega
  · intro hno w hw w' hw'
    by_contra hcon
    push_neg at hcon
    exact hno w hw w' hw' (sep w w') hcon (h w w').1

/-- **The safe-order law, over the query model.**  Order `s` suffices exactly when every
unsafe set contains a pair that some admissible query of order at most `s` separates. -/
theorem safeAt_iff_query (Sep : ℕ → W → W → Prop) (sep : W → W → ℕ)
    (h : ReadsOff Sep sep) (safe : W → Finset A) (s : ℕ) :
    SafeAt sep safe s ↔
      ∀ H : Finset W, Unsafe safe H → ∃ w ∈ H, ∃ w' ∈ H, ∃ j ≤ s, Sep j w w' := by
  rw [safeAt_iff]
  constructor
  · intro hs H hH
    obtain ⟨w, hw, w', hw', hle⟩ := hs H hH
    exact ⟨w, hw, w', hw', sep w w', hle, (h w w').1⟩
  · intro hs H hH
    obtain ⟨w, hw, w', hw', j, hj, hsep⟩ := hs H hH
    exact ⟨w, hw, w', hw', le_trans ((h w w').2 hsep) hj⟩

/-! ## The channel's own table is read off its own law -/

/-- The channel's separation predicate: query `j` separates the pair when its mask values
differ there. -/
def maskSep (j w w' : ℕ) : Prop := maskVal j w ≠ maskVal j w'

/-- **On the parity channel the table is not data.**  `resolveOrder` is the least order at
which an admissible query separates the pair, so every statement above applies to it with no
hypothesis left over. -/
theorem channel_sep_is_read_off :
    ∀ w w' : ℕ, w ≠ w' → IsLeast {j : ℕ | maskSep j w w'} (resolveOrder w w') :=
  fun w w' hne => resolveOrder_is_least w w' hne

/-- **And it is symmetric**, as a separation order must be. -/
theorem channel_sep_symm (w w' : ℕ) : resolveOrder w w' = resolveOrder w' w := by
  unfold resolveOrder
  omega

/-! ## Audit -/

#print axioms sep_unique
#print axioms sep_symm_of_least
#print axioms together_iff_no_separating_query
#print axioms safeAt_iff_query
#print axioms channel_sep_is_read_off
#print axioms channel_sep_symm

end CIGAMF.P13.PaperBSepDerived
