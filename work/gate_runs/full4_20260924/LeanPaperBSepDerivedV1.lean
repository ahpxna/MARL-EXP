import «LeanPaperBSafeOrderV1»
import «LeanPaperBQueryClassV1»

/-!
# Paper B: the separation order is read off the query model

`LeanPaperBSafeOrderV1` states the safe-order law in terms of a function
`sep : W -> W -> Nat`, and `Together sep s H` is `s < sep` on every DISTINCT pair of `H`.  The last
column of `THEOREM_MAP.md` recorded the honest objection: `sep` is DATA there.  Nothing says
it is the order at which the observer's own queries begin to separate the pair, so
`SafeAt` was a statement about a table rather than about a query model, and the orders it
produces were not sample complexities of anything.

This module removes that.  Fix a separation predicate

    Sep : Nat -> W -> W -> Prop,      "some admissible query of order j separates the pair",

and say that `sep` is READ OFF it when `sep w w'` is the LEAST such order for distinct worlds. Diagonal entries are unused; a world never separates from itself. Then

* `together_iff_no_separating_query` -- `Together sep s H` holds exactly when no admissible
  query of order at most `s` separates any pair inside `H`.  So the hypothesis of the law is
  a statement about queries, not about the table.
* `safeAt_iff_query` -- the law itself, restated over the query model.
* `sep_symm_of_least`, `sep_unique` -- `sep` is determined by `Sep`, so there is no freedom
  left in the table.

On the paper's own channel the hypothesis is discharged rather than assumed:
`resolveOrder_is_least` proves `IsLeast {j | maskVal j w /= maskVal j w'} (resolveOrder w w')`,
so `channel_sep_is_read_off` supplies `ReadsOff` itself. `channel_finite_readsOff` and
`channel_safeAt_iff_query` instantiate the finite-world law without an impossible diagonal premise.

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

/-- Least separating order for DISTINCT worlds; self-pairs have no such order. -/
def ReadsOff (Sep : ℕ → W → W → Prop) (sep : W → W → ℕ) : Prop :=
  ∀ w w' : W, w ≠ w' → IsLeast {j : ℕ | Sep j w w'} (sep w w')

/-- The query model determines exactly the off-diagonal entries. -/
theorem sep_unique (Sep : ℕ → W → W → Prop) (sep sep' : W → W → ℕ)
    (h : ReadsOff Sep sep) (h' : ReadsOff Sep sep') :
    ∀ w w', w ≠ w' → sep w w' = sep' w w' := by
  intro w w' hne
  exact IsLeast.unique (h w w' hne) (h' w w' hne)

/-- Full equality also needs a common convention for the unused diagonal. -/
theorem sep_unique_of_diagonal (Sep : ℕ → W → W → Prop) (sep sep' : W → W → ℕ)
    (h : ReadsOff Sep sep) (h' : ReadsOff Sep sep')
    (hd : ∀ w, sep w w = sep' w w) : sep = sep' := by
  funext w w'
  by_cases he : w = w'
  · subst w'; exact hd w
  · exact sep_unique Sep sep sep' h h' w w' he

theorem sep_symm_of_least (Sep : ℕ → W → W → Prop) (sep : W → W → ℕ)
    (h : ReadsOff Sep sep) (hsymm : ∀ j w w', Sep j w w' ↔ Sep j w' w) (w w' : W) :
    sep w w' = sep w' w := by
  by_cases he : w = w'
  · subst w'; rfl
  refine IsLeast.unique (h w w' he) ?_
  obtain ⟨hmem, hlb⟩ := h w' w (Ne.symm he)
  exact ⟨(hsymm _ _ _).mpr hmem, fun j hj => hlb ((hsymm _ _ _).mp hj)⟩

/-- No query up to order `s` separates a distinct pair in the unresolved set. -/
theorem together_iff_no_separating_query (Sep : ℕ → W → W → Prop) (sep : W → W → ℕ)
    (h : ReadsOff Sep sep) (s : ℕ) (H : Finset W) :
    Together sep s H ↔ ∀ w ∈ H, ∀ w' ∈ H, w ≠ w' → ∀ j ≤ s, ¬ Sep j w w' := by
  constructor
  · intro htog w hw w' hw' hne j hj hsep
    have hle : sep w w' ≤ j := (h w w' hne).2 hsep
    have := htog w hw w' hw' hne
    omega
  · intro hno w hw w' hw' hne
    by_contra hcon
    have hle : sep w w' ≤ s := by omega
    exact hno w hw w' hw' hne (sep w w') hle (h w w' hne).1

/-- Every unsafe set must contain a physically separable, distinct pair. -/
theorem safeAt_iff_query (Sep : ℕ → W → W → Prop) (sep : W → W → ℕ)
    (h : ReadsOff Sep sep) (safe : W → Finset A) (s : ℕ) :
    SafeAt sep safe s ↔
      ∀ H : Finset W, Unsafe safe H →
        ∃ w ∈ H, ∃ w' ∈ H, w ≠ w' ∧ ∃ j ≤ s, Sep j w w' := by
  rw [safeAt_iff]
  constructor
  · intro hs H hH
    obtain ⟨w, hw, w', hw', hne, hle⟩ := hs H hH
    exact ⟨w, hw, w', hw', hne, sep w w', hle, (h w w' hne).1⟩
  · intro hs H hH
    obtain ⟨w, hw, w', hw', hne, j, hj, hsep⟩ := hs H hH
    exact ⟨w, hw, w', hw', hne, le_trans ((h w w' hne).2 hsep) hj⟩

/-! ## The channel's own table is read off its own law -/

/-- The channel's separation predicate: query `j` separates the pair when its mask values
differ there. -/
def maskSep (j w w' : ℕ) : Prop := maskVal j w ≠ maskVal j w'

/-- **On the parity channel the table is not data.**  `resolveOrder` is the least order at
which an admissible query separates the pair, so every statement above applies to it with no
hypothesis left over. -/
theorem channel_sep_is_read_off :
    ReadsOff maskSep resolveOrder :=
  fun w w' hne => resolveOrder_is_least w w' hne

/-- Actual finite-channel instantiation; all off-diagonal least-order premises are proved. -/
theorem channel_finite_readsOff (m : ℕ) :
    ReadsOff (fun j (w w' : Fin m) => maskSep j w.val w'.val)
      (fun w w' => resolveOrder w.val w'.val) := by
  intro w w' hne
  exact channel_sep_is_read_off w.val w'.val (fun h => hne (Fin.ext h))

/-- The safe-order criterion over the actual finite channel, with no `ReadsOff` input. -/
theorem channel_safeAt_iff_query (m : ℕ) (safe : Fin m → Finset A) (s : ℕ) :
    SafeAt (fun (w w' : Fin m) => resolveOrder w.val w'.val) safe s ↔
      ∀ H : Finset (Fin m), Unsafe safe H →
        ∃ w ∈ H, ∃ w' ∈ H, w ≠ w' ∧ ∃ j ≤ s, maskSep j w.val w'.val :=
  safeAt_iff_query _ _ (channel_finite_readsOff m) safe s

/-- **And it is symmetric**, as a separation order must be. -/
theorem channel_sep_symm (w w' : ℕ) : resolveOrder w w' = resolveOrder w' w := by
  unfold resolveOrder
  omega

/-! ## Audit -/

#print axioms sep_unique
#print axioms sep_unique_of_diagonal
#print axioms sep_symm_of_least
#print axioms together_iff_no_separating_query
#print axioms safeAt_iff_query
#print axioms channel_sep_is_read_off
#print axioms channel_sep_symm
#print axioms channel_finite_readsOff
#print axioms channel_safeAt_iff_query

end CIGAMF.P13.PaperBSepDerived
