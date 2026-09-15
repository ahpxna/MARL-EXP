import «LeanStructuralRecourseUniformNestingV1»

/-! # Structural: ONE ranking that works at EVERY budget.

`excess_le_two_thirds` compares a set `S` with a competitor `T` of the same
cardinality, but only under the hypothesis `modularSpan T f ≤ modularSpan S f`.
That hypothesis is supplied per budget, so on its own the module gives

    forall k, exists S_k, forall T, ...

which is NOT what an executable ranking needs. This file upgrades the quantifier
to

    exists ONE nested chain, forall k, forall T, ...

## How

Not by sorting. A chain is built by repeatedly deleting a MINIMUM-span element:

* `spanMaximal_univ` — `univ` is span-maximal among sets of its cardinality.
* `spanMaximal_erase` — deleting a minimum-span element of a span-maximal set
  leaves a span-maximal set. The proof is the exchange step: for a competitor `T`
  of cardinality one less, `S \ T` is non-empty, so pick `z` there; then
  `T ∪ {z}` has the full cardinality, hence
  `mass T + span z ≤ mass S`, and `span z ≥ span x` because `x` was minimal in
  `S`, so `mass T ≤ mass S - span x = mass (S.erase x)`.
* `chain` — iterate that deletion from `univ`; `chain_card`, `chain_subset`,
  `chain_maximal` follow by induction.
* `one_prefix_chain` — reindex by `k = card - j` and feed the maximality into
  `excess_le_two_thirds`. The result carries no `hmass`.

## WHAT THIS DOES NOT ESTABLISH

- The constant is `2/3`, inherited unchanged. The sharp universal nesting
  threshold is NOT determined here; the previous batch's exact signed witness
  puts it at least `1/2`, so what is open is the constant in `[1/2, 2/3]`.
- `2/3 * modularSpan univ f` is the UNNORMALISED form. Dividing by
  `modularSpan univ f` needs it non-zero, which is not assumed here.
- This is about the existence of a good chain. It says nothing about computing
  one from an approximate oracle, and nothing about the fractional-execution
  question (`V_avg` versus `V_path`), where the obstruction is preserving a given
  path's marginals rather than finding a good ranking.
- The chain is built with `Finset.exists_min_image`, so it is classical; no
  complexity claim is made.
-/

namespace CIGAMF.P13.StructuralSortedPrefix
open Finset
open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.StructuralRecourseUniformNesting
noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]

/-- `S` carries at least as much span mass as every set of its own cardinality. -/
def SpanMaximal (f : ι → Ω → ℝ) (S : Finset ι) : Prop :=
  ∀ T : Finset ι, T.card = S.card → modularSpan T f ≤ modularSpan S f

theorem spanMaximal_univ (f : ι → Ω → ℝ) : SpanMaximal f univ := by
  intro T hT
  have hTu : T = univ := by
    apply Finset.eq_univ_of_card
    rw [hT, Finset.card_univ]
  rw [hTu]

/-- Deleting a minimum-span element of a span-maximal set leaves one. -/
theorem spanMaximal_erase (f : ι → Ω → ℝ) (S : Finset ι) (hS : SpanMaximal f S)
    (x : ι) (hx : x ∈ S) (hmin : ∀ y ∈ S, componentSpan f x ≤ componentSpan f y) :
    SpanMaximal f (S.erase x) := by
  classical
  intro T hT
  have hcard : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
  have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hTlt : T.card < S.card := by rw [hT, hcard]; omega
  -- some element of `S` is outside `T`
  obtain ⟨z, hzS, hzT⟩ : ∃ z ∈ S, z ∉ T := by
    by_contra hc
    push_neg at hc
    exact absurd (Finset.card_le_card hc) (by omega)
  have hins : (insert z T).card = S.card := by
    rw [Finset.card_insert_of_notMem hzT, hT, hcard]; omega
  have hmass := hS (insert z T) hins
  have hsum : modularSpan (insert z T) f = componentSpan f z + modularSpan T f := by
    unfold modularSpan; exact Finset.sum_insert hzT
  have herase : modularSpan (S.erase x) f = modularSpan S f - componentSpan f x := by
    unfold modularSpan; exact Finset.sum_erase_eq_sub hx
  have hxz := hmin z hzS
  rw [herase]
  rw [hsum] at hmass
  linarith

/-- One deletion step: remove a minimum-span element. -/
def step (f : ι → Ω → ℝ) (S : Finset ι) : Finset ι :=
  if h : S.Nonempty then S.erase (Finset.exists_min_image S (componentSpan f) h).choose
  else S

theorem step_subset (f : ι → Ω → ℝ) (S : Finset ι) : step f S ⊆ S := by
  unfold step
  split
  · exact Finset.erase_subset _ _
  · exact subset_rfl

theorem step_card (f : ι → Ω → ℝ) (S : Finset ι) : (step f S).card = S.card - 1 := by
  unfold step
  split
  · rename_i h
    exact Finset.card_erase_of_mem (Finset.exists_min_image S (componentSpan f) h).choose_spec.1
  · rename_i h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h]; simp

theorem step_maximal (f : ι → Ω → ℝ) (S : Finset ι) (hS : SpanMaximal f S) :
    SpanMaximal f (step f S) := by
  unfold step
  split
  · rename_i h
    obtain ⟨hmem, hmin⟩ := (Finset.exists_min_image S (componentSpan f) h).choose_spec
    exact spanMaximal_erase f S hS _ hmem hmin
  · exact hS

/-- The chain: delete `j` minimum-span elements from `univ`. -/
def chain (f : ι → Ω → ℝ) : ℕ → Finset ι
  | 0 => univ
  | (j+1) => step f (chain f j)

theorem chain_subset (f : ι → Ω → ℝ) (j : ℕ) : chain f (j+1) ⊆ chain f j :=
  step_subset f _

theorem chain_card (f : ι → Ω → ℝ) (j : ℕ) :
    (chain f j).card = Fintype.card ι - j := by
  induction j with
  | zero => simp [chain, Finset.card_univ]
  | succ j ih => rw [chain, step_card, ih]; omega

theorem chain_maximal (f : ι → Ω → ℝ) (j : ℕ) : SpanMaximal f (chain f j) := by
  induction j with
  | zero => exact spanMaximal_univ f
  | succ j ih => exact step_maximal f _ ih

/-- ONE nested chain that beats every competitor at EVERY budget, with no span-mass
hypothesis left anywhere. -/
theorem one_prefix_chain (f : ι → Ω → ℝ) :
    ∃ S : ℕ → Finset ι,
      (∀ k, k < Fintype.card ι → S k ⊆ S (k+1)) ∧
      (∀ k, k ≤ Fintype.card ι → (S k).card = k) ∧
      (∀ k, k ≤ Fintype.card ι → ∀ T : Finset ι, T.card = k →
        supportOsc (S k)ᶜ f ≤ supportOsc Tᶜ f + 2/3 * modularSpan univ f) := by
  classical
  set N := Fintype.card ι with hN
  refine ⟨fun k => chain f (N - k), ?_, ?_, ?_⟩
  · intro k hk
    show chain f (N - k) ⊆ chain f (N - (k+1))
    have hstep : N - k = (N - (k+1)) + 1 := by omega
    rw [hstep]
    exact chain_subset f _
  · intro k hk
    rw [chain_card, ← hN]; omega
  · intro k hk T hT
    have hcard : (chain f (N - k)).card = k := by rw [chain_card, ← hN]; omega
    have hmass : modularSpan T f ≤ modularSpan (chain f (N - k)) f :=
      chain_maximal f (N - k) T (by rw [hcard, hT])
    exact excess_le_two_thirds f _ T hmass

#print axioms spanMaximal_univ
#print axioms spanMaximal_erase
#print axioms step_subset
#print axioms step_card
#print axioms step_maximal
#print axioms chain_subset
#print axioms chain_card
#print axioms chain_maximal
#print axioms one_prefix_chain

end
end CIGAMF.P13.StructuralSortedPrefix
