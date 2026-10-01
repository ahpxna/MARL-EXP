import «LeanPaperBDecisionOrderV1»

/-!
# Paper B: query design is exactly a hitting-set problem

`LeanPaperBDecisionOrderV1.dec_hitting` reduces "does the sub-menu `M` reach decision order
`≤ s`?" to a hitting condition on the obstructions. This module proves the converse
embedding: **every hitting-set instance is a query-design instance**, with the same feasible
solutions. So minimum-cost query design at a target order contains minimum-cost hitting set,
which is NP-hard (Karp 1972). The greedy rule inherits the `H_n` approximation of set cover
(Johnson 1974, Chvátal 1979); these two facts are cited, not formalised.

**The instance.** Queries `Q`, sets `F₁, …, F_r ⊆ Q`.
* Worlds are `Fin r × Bool`: a pair of twins `(i, false)`, `(i, true)` per set.
* Each world's only safe answer is itself.
* Twins are separated at order `1` by the queries of `F_i` and at order `2` by the others.
* Worlds of different pairs are separated at order `0` by every query.
* The size is linear: `2r` worlds, `2r` answers, the same queries.

**What is proved.**
* `hitting_embeds`: a nonempty menu `M` has decision order `≤ 1` if and only if it meets every
  `F_i`.
* `order_zero_fails`: no menu reaches order `0` when `r ≥ 1`. So the decision order of `M` is
  `1` when `M` hits and `2` when it misses (`order_two`).
* `id_iff_hitting`: on this instance the identification order is the same. The hardness is
  already present when the decision and identification designs coincide.
-/

namespace CIGAMF.P13.PaperBQueryDesign

open Finset CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBDecisionOrder

variable {Q : Type*} [Fintype Q] [Nonempty Q] [DecidableEq Q] {r : ℕ}

/-- Each world's only safe answer is itself. -/
def hsSafe (w : Fin r × Bool) : Finset (Fin r × Bool) := {w}

/-- The per-query orders of the hitting-set instance. -/
def hsSq (F : Fin r → Finset Q) (q : Q) (u v : Fin r × Bool) : ℕ :=
  if u.1 ≠ v.1 then 0 else if u.2 = v.2 then 0 else if q ∈ F u.1 then 1 else 2

/-- The twins of set `i`. -/
def twins (i : Fin r) : Finset (Fin r × Bool) := {(i, false), (i, true)}

theorem twins_unsafe (i : Fin r) : Unsafe hsSafe (twins i) := by
  intro a
  by_cases ha : a = (i, false)
  · exact ⟨(i, true), by simp [twins], by simp [hsSafe, ha]⟩
  · exact ⟨(i, false), by simp [twins], by simpa [hsSafe] using ha⟩

theorem twins_pair (i : Fin r) (u v : Fin r × Bool) (hu : u ∈ twins i) (hv : v ∈ twins i)
    (huv : u ≠ v) : u.1 = i ∧ v.1 = i ∧ u.2 ≠ v.2 := by
  simp only [twins, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

/-- **Hitting sets are query designs.** -/
theorem hitting_embeds [NeZero r] (F : Fin r → Finset Q) (M : Finset Q) (hM : M.Nonempty) :
    DecLE (hsSq F) hsSafe M hM 1 ↔ ∀ i, ∃ q ∈ M, q ∈ F i := by
  rw [dec_hitting]
  constructor
  · intro h i
    obtain ⟨q, hq, u, hu, v, hv, huv, hle⟩ := h (twins i) (twins_unsafe i)
    obtain ⟨hu1, hv1, h2⟩ := twins_pair i u v hu hv huv
    refine ⟨q, hq, ?_⟩
    by_contra hqF
    unfold hsSq at hle
    rw [if_neg (by rw [hu1, hv1]; exact not_not.mpr rfl), if_neg h2, hu1, if_neg hqF] at hle
    omega
  · intro h H hH
    obtain ⟨u, hu, -⟩ := hH ((0 : Fin r), false)
    obtain ⟨v, hv, huv⟩ := hH u
    have hne : u ≠ v := by
      rintro rfl; exact huv (by simp [hsSafe])
    by_cases h1 : u.1 = v.1
    · obtain ⟨q, hq, hqF⟩ := h u.1
      have h2 : u.2 ≠ v.2 := fun h2 => hne (Prod.ext h1 h2)
      refine ⟨q, hq, u, hu, v, hv, hne, ?_⟩
      unfold hsSq
      rw [if_neg (not_not.mpr h1), if_neg h2, if_pos hqF]
    · obtain ⟨q, hq⟩ := hM
      refine ⟨q, hq, u, hu, v, hv, hne, ?_⟩
      unfold hsSq
      rw [if_pos h1]
      omega

/-- **Order `0` is out of reach.** -/
theorem order_zero_fails (F : Fin r → Finset Q) (M : Finset Q) (hM : M.Nonempty) (i : Fin r) :
    ¬ DecLE (hsSq F) hsSafe M hM 0 := by
  intro h
  rw [dec_hitting] at h
  obtain ⟨q, -, u, hu, v, hv, huv, hle⟩ := h (twins i) (twins_unsafe i)
  obtain ⟨hu1, hv1, h2⟩ := twins_pair i u v hu hv huv
  unfold hsSq at hle
  rw [if_neg (by rw [hu1, hv1]; exact not_not.mpr rfl), if_neg h2] at hle
  split_ifs at hle <;> omega

/-- **A menu that misses a set has order `2` exactly**: it fails order `1` and reaches `2`. -/
theorem order_two [NeZero r] (F : Fin r → Finset Q) (M : Finset Q) (hM : M.Nonempty)
    (i : Fin r) (hmiss : ∀ q ∈ M, q ∉ F i) :
    ¬ DecLE (hsSq F) hsSafe M hM 1 ∧ DecLE (hsSq F) hsSafe M hM 2 := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨q, hq, hqF⟩ := (hitting_embeds F M hM).mp h i
    exact hmiss q hq hqF
  · rw [dec_hitting]
    intro H hH
    obtain ⟨u, hu, -⟩ := hH ((0 : Fin r), false)
    obtain ⟨v, hv, huv⟩ := hH u
    have hne : u ≠ v := by
      rintro rfl; exact huv (by simp [hsSafe])
    obtain ⟨q, hq⟩ := hM
    refine ⟨q, hq, u, hu, v, hv, hne, ?_⟩
    unfold hsSq
    split_ifs <;> omega

/-- **Identification is the same condition here.** -/
theorem id_iff_hitting [NeZero r] (F : Fin r → Finset Q) (M : Finset Q) (hM : M.Nonempty) :
    IdLE (hsSq F) M hM 1 ↔ ∀ i, ∃ q ∈ M, q ∈ F i := by
  constructor
  · intro h
    exact (hitting_embeds F M hM).mp (id_implies_dec (hsSq F) hsSafe M hM 1
      (fun w => ⟨w, by simp [hsSafe]⟩) h)
  · intro h u v huv
    unfold sepM
    by_cases h1 : u.1 = v.1
    · obtain ⟨q, hq, hqF⟩ := h u.1
      have h2 : u.2 ≠ v.2 := fun h2 => huv (Prod.ext h1 h2)
      refine (Finset.inf'_le _ hq).trans ?_
      unfold hsSq
      rw [if_neg (not_not.mpr h1), if_neg h2, if_pos hqF]
    · obtain ⟨q, hq⟩ := hM
      refine (Finset.inf'_le _ hq).trans ?_
      unfold hsSq
      rw [if_pos h1]
      omega

#print axioms twins_unsafe
#print axioms hitting_embeds
#print axioms order_zero_fails
#print axioms order_two
#print axioms id_iff_hitting

end CIGAMF.P13.PaperBQueryDesign
