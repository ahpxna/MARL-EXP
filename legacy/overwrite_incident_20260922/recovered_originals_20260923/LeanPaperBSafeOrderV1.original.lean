import Mathlib

/-!
# Paper B: the safe-observation order, as a law about obstructions

This is the geometry–query link stated as a theorem rather than assumed: **how deep an
observer must resolve worlds before every class it can still confuse admits one answer that
is safe for all of them.**

THE OBJECTS.  A finite set of worlds; for each world a finite set of answers that are safe
at it; and a *resolving order* `sep θ λ` — the first order at which some admissible query
tells `θ` from `λ`.  A set of worlds is **together at level `s`** when no pair in it is
resolved by order `s`, i.e. it is still inside one class for an order-`s` observer; and it
is **unsafe** when its worlds share no safe answer.

    SafeAt s   :=   every set that is together at level `s` has a common safe answer.

THE LAW.

    SafeAt s   <->   every unsafe set contains a pair resolved by order `s`,

which is `s_safe = max over unsafe H of min over pairs in H of sep`.

WHY "ALL UNSAFE SETS" AND NOT "MINIMAL" ONES.  Unsafety is upward closed — a superset of an
unsafe set shares no answer either — and enlarging a set can only lower the minimum over its
pairs.  So the maximum is attained on minimal unsafe sets anyway, and stating the law over
*all* unsafe sets avoids having to define minimality at all.  The minimal-obstruction
reading is recovered as a corollary, which is the form to quote in prose.

WHAT THIS IS NOT.  `sep` is an input here.  Deriving it from the densities of an actual
observation model — the coefficient of `h^k` in the expansion, uniformly over the admissible
query class — is Paper B's central obligation and is NOT done in this file.  The law below
says what follows from a resolving-order table; it does not say the model has one.
-/

namespace CIGAMF.P13.PaperBSafe

open Finset

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

/-- A set of worlds no order-`s` observer can split apart. -/
def Together (sep : W → W → ℕ) (s : ℕ) (H : Finset W) : Prop :=
  ∀ θ ∈ H, ∀ lam ∈ H, s < sep θ lam

/-- A set of worlds with no answer safe at all of them. -/
def Unsafe (safe : W → Finset A) (H : Finset W) : Prop :=
  ∀ a : A, ∃ θ ∈ H, a ∉ safe θ

/-- Order `s` suffices for safe decisions: every class an order-`s` observer can still
confuse admits an answer safe across it. -/
def SafeAt (sep : W → W → ℕ) (safe : W → Finset A) (s : ℕ) : Prop :=
  ∀ H : Finset W, Together sep s H → ¬ Unsafe safe H

/-- **The law.**  Order `s` suffices exactly when every unsafe set already contains a pair
the observer resolves by order `s`. -/
theorem safeAt_iff (sep : W → W → ℕ) (safe : W → Finset A) (s : ℕ) :
    SafeAt sep safe s ↔
      ∀ H : Finset W, Unsafe safe H → ∃ θ ∈ H, ∃ lam ∈ H, sep θ lam ≤ s := by
  constructor
  · intro hs H hH
    by_contra hcon
    push_neg at hcon
    exact hs H (fun θ hθ lam hlam => hcon θ hθ lam hlam) hH
  · intro h H htog hH
    obtain ⟨θ, hθ, lam, hlam, hle⟩ := h H hH
    exact absurd (htog θ hθ lam hlam) (by omega)

/-- **Unsafety is upward closed**, which is why the law may quantify over all unsafe sets. -/
theorem unsafe_mono (safe : W → Finset A) {H K : Finset W} (hHK : H ⊆ K)
    (h : Unsafe safe H) : Unsafe safe K := by
  intro a
  obtain ⟨θ, hθ, ha⟩ := h a
  exact ⟨θ, hHK hθ, ha⟩

/-- **Monotone in the order**: resolving more can only help. -/
theorem safeAt_mono (sep : W → W → ℕ) (safe : W → Finset A) {s t : ℕ} (hst : s ≤ t)
    (h : SafeAt sep safe s) : SafeAt sep safe t := by
  rw [safeAt_iff] at h ⊢
  intro H hH
  obtain ⟨θ, hθ, lam, hlam, hle⟩ := h H hH
  exact ⟨θ, hθ, lam, hlam, le_trans hle hst⟩

/-- **When no set is unsafe, order zero suffices** --- there is a globally safe answer and
the decision costs no observation at all.  One of the two edge cases the law has to name. -/
theorem safeAt_zero_of_no_unsafe (sep : W → W → ℕ) (safe : W → Finset A)
    (h : ∀ H : Finset W, ¬ Unsafe safe H) : SafeAt sep safe 0 :=
  fun H _ hH => h H hH

/-! ## The overlapping-safe-sets construction, geometry half

With `m >= 3` worlds and `safe w = everything except w`, every pair of safe sets meets, the
total intersection is empty, and **the only unsafe set is the whole world set**.  The law
then reads `SafeAt s <-> min over ALL pairs of sep <= s`, the simplest case it has.

This is the GEOMETRY half of that construction.  The other half --- that a query at order
`j` resolves world `j` from the rest, so that `sep` is the table the separation needs --- is
a statement about densities and is not proved here.
-/

/-- The safe sets of the construction: every answer but the world's own index. -/
def coSafe [DecidableEq W] (w : W) : Finset W := Finset.univ.erase w

theorem coSafe_pairwise_meet [DecidableEq W] (hcard : 3 ≤ Fintype.card W) (u v : W) :
    ∃ a : W, a ∈ coSafe u ∧ a ∈ coSafe v := by
  classical
  have h : ((Finset.univ : Finset W).erase u).erase v ≠ ∅ := by
    intro hempty
    have hle := Finset.card_erase_le (s := (Finset.univ : Finset W).erase u) (a := v)
    have h1 : ((Finset.univ : Finset W).erase u).card + 1 ≥ Fintype.card W := by
      have := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset W)) (a := u)
      simp [Finset.card_univ] at this ⊢
      omega
    have h2 : (((Finset.univ : Finset W).erase u).erase v).card = 0 := by
      rw [hempty]; rfl
    have h3 := Finset.pred_card_le_card_erase
      (s := (Finset.univ : Finset W).erase u) (a := v)
    rw [h2] at h3
    simp [Finset.card_univ] at h1 h3 ⊢
    omega
  obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty h
  refine ⟨a, ?_, ?_⟩
  · exact Finset.mem_of_mem_erase ha
  · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, Finset.mem_univ a⟩

/-- **The whole world set is unsafe**: no answer is safe at every world, since the answer's
own world excludes it. -/
theorem coSafe_univ_unsafe [DecidableEq W] : Unsafe (A := W) coSafe Finset.univ := by
  intro a
  exact ⟨a, Finset.mem_univ a, by simp [coSafe]⟩

/-- **And nothing smaller is**: a proper subset always has a common safe answer, namely any
world outside it.  So the construction has exactly one unsafe set. -/
theorem coSafe_proper_safe [DecidableEq W] (H : Finset W) (hne : H ≠ Finset.univ) :
    ¬ Unsafe (A := W) coSafe H := by
  classical
  intro hU
  obtain ⟨a, ha⟩ : ∃ a : W, a ∉ H := by
    by_contra hcon
    push_neg at hcon
    exact hne (Finset.eq_univ_of_forall hcon)
  obtain ⟨θ, hθ, hmem⟩ := hU a
  exact hmem (Finset.mem_erase.mpr ⟨fun h => ha (h ▸ hθ), Finset.mem_univ a⟩)

/-- **The law, at this construction.**  Exactly one obstruction, so the safe order is the
minimum resolving order over ALL pairs --- the simplest instance the general law has. -/
theorem coSafe_safeAt_iff [DecidableEq W] (sep : W → W → ℕ) (s : ℕ) :
    SafeAt sep (A := W) coSafe s ↔
      ∃ θ : W, ∃ lam : W, sep θ lam ≤ s := by
  rw [safeAt_iff]
  constructor
  · intro h
    obtain ⟨θ, -, lam, -, hle⟩ := h Finset.univ coSafe_univ_unsafe
    exact ⟨θ, lam, hle⟩
  · rintro ⟨θ, lam, hle⟩ H hH
    by_cases hu : H = Finset.univ
    · exact ⟨θ, hu ▸ Finset.mem_univ θ, lam, hu ▸ Finset.mem_univ lam, hle⟩
    · exact absurd hH (coSafe_proper_safe H hu)

/-! ## Audit -/

#print axioms safeAt_iff
#print axioms unsafe_mono
#print axioms safeAt_mono
#print axioms safeAt_zero_of_no_unsafe
#print axioms coSafe_pairwise_meet
#print axioms coSafe_univ_unsafe
#print axioms coSafe_proper_safe
#print axioms coSafe_safeAt_iff

end CIGAMF.P13.PaperBSafe
