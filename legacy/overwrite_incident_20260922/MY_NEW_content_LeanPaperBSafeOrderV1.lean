import Mathlib

/-!
# Paper B: the safe-observation order, as a law about obstructions

Paper B's central quantity is

    s_safe = max over unsafe H of  min over distinct θ, λ in H of r(θ, λ),

where `H` is a set of worlds with NO answer safe for all of them, and `r(θ, λ)` is the
earliest density order at which some admissible query separates that pair.  The manuscript
states it as a maximum over MINIMAL unsafe obstructions, which is the form with the
scientific reading -- but minimality is an awkward thing to carry through a formalisation,
and it is not needed.

`sSafe_eq_sSafeMin` proves the two agree.  The argument is two monotonicities: unsafeness is
upward closed, so every unsafe set contains a minimal one; and `phi` is ANTITONE, because a
larger set has more pairs to take a minimum over.  So the larger family's maximum is attained
on the smaller one, and neither form is stronger.

Two edge cases the supervisor named are handled rather than assumed away.  When no unsafe set
exists -- some answer is safe everywhere -- `sSafe` is `⊥`, i.e. zero decision cost
(`sSafe_eq_bot_of_no_obstruction`).  When a pair is separated at no finite order, `r` takes
the value `⊤`, which is why the codomain is `ℕ∞` and not `ℕ`.

This is the combinatorial half only.  It says nothing about observation laws: supplying the
table of resolving orders `r` from actual densities is a separate obligation, and the law
above does not discharge it.
-/

namespace CIGAMF.P13.PaperBSafeOrder

open Finset

variable {Θ Ans : Type*} [Fintype Θ] [DecidableEq Θ] [DecidableEq Ans]

/-! ## Obstructions -/

/-- A set of worlds is unsafe when no single answer is safe for all of them. -/
def IsUnsafe (A : Θ → Finset Ans) (H : Finset Θ) : Prop :=
  ¬ ∃ a : Ans, ∀ θ ∈ H, a ∈ A θ

/-- A minimal obstruction: unsafe, with every proper subset safe. -/
def MinimalUnsafe (A : Θ → Finset Ans) (H : Finset Θ) : Prop :=
  IsUnsafe A H ∧ ∀ K ⊂ H, ¬ IsUnsafe A K

/-- **Unsafeness is upward closed.**  Adding worlds cannot create a common safe answer. -/
theorem unsafe_mono (A : Θ → Finset Ans) {K H : Finset Θ} (hKH : K ⊆ H)
    (hK : IsUnsafe A K) : IsUnsafe A H := by
  intro ⟨a, ha⟩
  exact hK ⟨a, fun θ hθ => ha θ (hKH hθ)⟩

/-- **Every obstruction contains a minimal one.** -/
theorem exists_minimal_unsafe (A : Θ → Finset Ans) :
    ∀ H : Finset Θ, IsUnsafe A H → ∃ K ⊆ H, MinimalUnsafe A K := by
  classical
  intro H
  induction H using Finset.strongInduction with
  | _ H ih =>
      intro h
      by_cases hmin : ∀ K ⊂ H, ¬ IsUnsafe A K
      · exact ⟨H, subset_rfl, h, hmin⟩
      · push_neg at hmin
        obtain ⟨K, hKH, hK⟩ := hmin
        obtain ⟨L, hLK, hL⟩ := ih K hKH hK
        exact ⟨L, hLK.trans hKH.subset, hL⟩

/-! ## The order of an obstruction -/

/-- The earliest order at which some pair inside `H` is separated.  `⊤` when `H` has fewer
than two worlds, or when no pair is separated at any finite order. -/
noncomputable def phi (r : Θ → Θ → ℕ∞) (H : Finset Θ) : ℕ∞ :=
  H.offDiag.inf (fun p => r p.1 p.2)

/-- **`phi` is antitone**: a bigger obstruction takes a minimum over more pairs. -/
theorem phi_antitone (r : Θ → Θ → ℕ∞) {K H : Finset Θ} (hKH : K ⊆ H) :
    phi r H ≤ phi r K :=
  Finset.inf_mono (Finset.offDiag_mono hKH)

/-! ## The law -/

open scoped Classical in
/-- The observation order needed to decide safely. -/
noncomputable def sSafe (A : Θ → Finset Ans) (r : Θ → Θ → ℕ∞) : ℕ∞ :=
  ((Finset.univ : Finset (Finset Θ)).filter (fun H => IsUnsafe A H)).sup (phi r)

open scoped Classical in
/-- The same, read off the minimal obstructions only. -/
noncomputable def sSafeMin (A : Θ → Finset Ans) (r : Θ → Θ → ℕ∞) : ℕ∞ :=
  ((Finset.univ : Finset (Finset Θ)).filter (fun H => MinimalUnsafe A H)).sup (phi r)

/-- **The two readings agree.**  Quantifying over all obstructions is no weaker than
quantifying over the minimal ones, so the formalisation may take the easy form and the
manuscript may keep the meaningful one. -/
theorem sSafe_eq_sSafeMin (A : Θ → Finset Ans) (r : Θ → Θ → ℕ∞) :
    sSafe A r = sSafeMin A r := by
  classical
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le (fun H hH => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
    obtain ⟨K, hKH, hK⟩ := exists_minimal_unsafe A H hH
    refine le_trans (phi_antitone r hKH) ?_
    refine Finset.le_sup ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hK
  · refine Finset.sup_le (fun H hH => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
    refine Finset.le_sup ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH.1

/-- **No obstruction means no decision cost.**  If some answer is safe in every world, the
order is `⊥`; the law does not silently report a positive requirement. -/
theorem sSafe_eq_bot_of_no_obstruction (A : Θ → Finset Ans) (r : Θ → Θ → ℕ∞)
    (h : ∀ H : Finset Θ, ¬ IsUnsafe A H) : sSafe A r = ⊥ := by
  classical
  unfold sSafe
  have hempty : ((Finset.univ : Finset (Finset Θ)).filter
      (fun H => IsUnsafe A H)) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr (fun H _ => h H)
  rw [hempty, Finset.sup_empty]

/-- **A single obstruction fixes the order.**  When exactly one set obstructs, the law reads
off that set's own pairwise minimum -- the shape the `m`-world family instantiates. -/
theorem sSafe_of_unique_obstruction (A : Θ → Finset Ans) (r : Θ → Θ → ℕ∞)
    (H₀ : Finset Θ) (hH₀ : MinimalUnsafe A H₀)
    (huniq : ∀ H : Finset Θ, MinimalUnsafe A H → H = H₀) :
    sSafeMin A r = phi r H₀ := by
  classical
  unfold sSafeMin
  refine le_antisymm (Finset.sup_le (fun H hH => ?_)) (Finset.le_sup ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
    rw [huniq H hH]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH₀

/-! ## Audit -/

#print axioms unsafe_mono
#print axioms exists_minimal_unsafe
#print axioms phi_antitone
#print axioms sSafe_eq_sSafeMin
#print axioms sSafe_eq_bot_of_no_obstruction
#print axioms sSafe_of_unique_obstruction

end CIGAMF.P13.PaperBSafeOrder
