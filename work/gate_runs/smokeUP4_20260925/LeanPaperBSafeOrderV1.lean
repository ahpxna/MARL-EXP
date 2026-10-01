import Mathlib

/-!
# Paper B: the safe-observation order

A world is decided safely when the observer can name an answer that is safe in every world
it cannot yet tell apart.  `Together sep s H` says the observer at order `s` separates no
pair inside `H`; `Unsafe safe H` says `H` admits no common safe answer.  `SafeAt sep safe s`
is then the law: at order `s`, no set the observer still holds together is unsafe.

`Together` quantifies over DISTINCT pairs.  A world cannot be separated from itself, so
including the diagonal would demand `s < sep w w`, which no finite table satisfies at every
order; `Together` would then fail on every non-empty set and `SafeAt s` would hold vacuously
at every `s`.  The same restriction is why `ReadsOff` in `LeanPaperBSepDerivedV1` asks for a
least separating order only off the diagonal: that is the only place a query model supplies
one.

`safeAt_iff` restates the law contrapositively -- every unsafe set contains a distinct pair
the observer separates by order `s` -- which is the form the downstream modules consume.

`sep` is DATA here: nothing in this module says it is the order at which the observer's own
queries begin to separate a pair.  `LeanPaperBSepDerivedV1` removes that, by reading `sep`
off a separation predicate and proving the table is then determined.

The second half instantiates the law at the overlapping geometry `safe w = everything but
w`: every two safe sets meet, the total intersection is empty, the whole world set is the
ONLY unsafe set, and the law collapses to a statement about the minimum of `sep` over all
distinct pairs.
-/

namespace CIGAMF.P13.PaperBSafe

open Finset

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

/-- `H` admits no answer safe in all of its worlds. -/
def Unsafe (safe : W → Finset A) (H : Finset W) : Prop :=
  ∀ a : A, ∃ w ∈ H, a ∉ safe w

/-- At order `s` the observer separates no DISTINCT pair inside `H`. -/
def Together (sep : W → W → ℕ) (s : ℕ) (H : Finset W) : Prop :=
  ∀ w ∈ H, ∀ w' ∈ H, w ≠ w' → s < sep w w'

/-- **The safe-order law.**  Order `s` suffices when no set the observer still holds
together is unsafe. -/
def SafeAt (sep : W → W → ℕ) (safe : W → Finset A) (s : ℕ) : Prop :=
  ∀ H : Finset W, Together sep s H → ¬ Unsafe safe H

/-- **The law, contrapositively.**  Order `s` suffices exactly when every unsafe set
contains a distinct pair separated by order `s`.  This is the form that is checkable: it
quantifies over obstructions rather than over everything the observer might hold together. -/
theorem safeAt_iff (sep : W → W → ℕ) (safe : W → Finset A) (s : ℕ) :
    SafeAt sep safe s ↔
      ∀ H : Finset W, Unsafe safe H → ∃ w ∈ H, ∃ w' ∈ H, w ≠ w' ∧ sep w w' ≤ s := by
  constructor
  · intro hs H hH
    by_contra hcon
    push_neg at hcon
    exact hs H (fun w hw w' hw' hne => hcon w hw w' hw' hne) hH
  · intro hs H htog hH
    obtain ⟨w, hw, w', hw', hne, hle⟩ := hs H hH
    exact absurd (htog w hw w' hw' hne) (by omega)

/-- **Unsafeness is upward closed.**  Adding worlds cannot create a common safe answer. -/
theorem unsafe_mono (safe : W → Finset A) {K H : Finset W} (hKH : K ⊆ H)
    (hK : Unsafe safe K) : Unsafe safe H := by
  intro a
  obtain ⟨w, hw, ha⟩ := hK a
  exact ⟨w, hKH hw, ha⟩

/-- **A wider order is still safe.**  Separating more pairs cannot create an obstruction. -/
theorem safeAt_mono (sep : W → W → ℕ) (safe : W → Finset A) {s s' : ℕ} (hss : s ≤ s')
    (h : SafeAt sep safe s) : SafeAt sep safe s' := by
  rw [safeAt_iff] at h ⊢
  intro H hH
  obtain ⟨w, hw, w', hw', hne, hle⟩ := h H hH
  exact ⟨w, hw, w', hw', hne, le_trans hle hss⟩

/-- **No obstruction means order zero suffices.**  The law does not silently report a
positive requirement when some answer is safe everywhere. -/
theorem safeAt_zero_of_no_unsafe (sep : W → W → ℕ) (safe : W → Finset A)
    (h : ∀ H : Finset W, ¬ Unsafe safe H) : SafeAt sep safe 0 := by
  rw [safeAt_iff]
  intro H hH
  exact absurd hH (h H)

/-- A singleton is held together at every order because it has no distinct pair.
It is safe only if that world itself admits a safe answer. -/
theorem together_singleton (sep : W → W → ℕ) (s : ℕ) (w : W) :
    Together sep s {w} := by
  intro x hx y hy hne
  rw [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hne

/-! ## The overlapping geometry: every world's safe answers are all the others -/

/-- The overlapping family: an answer is safe in every world but the one it names. -/
def coSafe (w : W) : Finset W := Finset.univ.erase w

/-- **Every two safe sets meet**, as soon as there are three worlds. -/
theorem coSafe_pairwise_inter_nonempty (hcard : 3 ≤ Fintype.card W) (w w' : W) :
    ((coSafe w) ∩ (coSafe w') : Finset W).Nonempty := by
  classical
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty] at hcon
  have hsub : (Finset.univ : Finset W) ⊆ {w, w'} := by
    intro a _
    by_contra ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    push_neg at ha
    have : a ∈ (coSafe w) ∩ (coSafe w') := by
      simp only [coSafe, Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨ha.1, ha.2⟩
    rw [hcon] at this
    exact absurd this (Finset.notMem_empty a)
  have h1 : Fintype.card W ≤ 2 := by
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    exact le_trans this (Finset.card_insert_le _ _ |>.trans (by simp))
  omega

/-- Original existential API, now derived from the intersection form. -/
theorem coSafe_pairwise_meet (hcard : 3 ≤ Fintype.card W) (w w' : W) :
    ∃ a : W, a ∈ coSafe w ∧ a ∈ coSafe w' := by
  obtain ⟨a, ha⟩ := coSafe_pairwise_inter_nonempty hcard w w'
  exact ⟨a, Finset.mem_inter.mp ha⟩

/-- **The whole world set is unsafe**: no answer is safe everywhere, because each answer is
excluded by the world it names. -/
theorem coSafe_univ_unsafe : Unsafe (coSafe : W → Finset W) Finset.univ := by
  intro a
  exact ⟨a, Finset.mem_univ a, by simp [coSafe]⟩

/-- **And it is the only one**: any set missing a world is safe, with that world's own name
as the common answer. -/
theorem coSafe_proper_safe (H : Finset W) (hH : H ≠ Finset.univ) :
    ¬ Unsafe (coSafe : W → Finset W) H := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : W, a ∉ H := by
    by_contra hcon
    push_neg at hcon
    exact hH (Finset.eq_univ_of_forall hcon)
  intro hu
  obtain ⟨w, hw, hna⟩ := hu a
  exact hna (by
    simp only [coSafe, Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun h => ha (h ▸ hw))

/-- **The law at the overlapping geometry.**  With exactly one obstruction -- the whole world
set -- the order needed is the smallest separating order over ALL distinct pairs. -/
theorem coSafe_safeAt_iff (sep : W → W → ℕ) (s : ℕ) :
    SafeAt sep (coSafe : W → Finset W) s ↔ ∃ w w' : W, w ≠ w' ∧ sep w w' ≤ s := by
  classical
  rw [safeAt_iff]
  constructor
  · intro h
    obtain ⟨w, _, w', _, hne, hle⟩ := h Finset.univ coSafe_univ_unsafe
    exact ⟨w, w', hne, hle⟩
  · rintro ⟨w, w', hne, hle⟩ H hH
    by_cases hu : H = Finset.univ
    · subst hu
      exact ⟨w, Finset.mem_univ w, w', Finset.mem_univ w', hne, hle⟩
    · exact absurd hH (coSafe_proper_safe H hu)

/-- Regression: a hidden two-world disagreement cannot become safe merely because the
unused diagonal of the table is zero. The old definition incorrectly proved `SafeAt 0`. -/
theorem diagonal_zero_does_not_certify :
    ¬ SafeAt (fun (w w' : Fin 2) => if w = w' then 0 else 10)
      (coSafe : Fin 2 → Finset (Fin 2)) 0 := by
  rw [coSafe_safeAt_iff]
  rintro ⟨w, w', hne, hle⟩
  rw [if_neg hne] at hle
  omega

/-! ## Audit -/

#print axioms safeAt_iff
#print axioms unsafe_mono
#print axioms safeAt_mono
#print axioms safeAt_zero_of_no_unsafe
#print axioms together_singleton
#print axioms diagonal_zero_does_not_certify
#print axioms coSafe_pairwise_meet
#print axioms coSafe_univ_unsafe
#print axioms coSafe_proper_safe
#print axioms coSafe_safeAt_iff

end CIGAMF.P13.PaperBSafe
