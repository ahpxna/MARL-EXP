import Mathlib

/-! N3: consistency and counterworld completion for a nonadaptive transcript.
The interval hitting-set construction is a separate obligation. -/
namespace CIGAMF.P13.SupportNonadaptiveCompletion
open scoped BigOperators
open Finset
noncomputable section
variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]

theorem hitting_set_card_lower (H : Finset X) (W : I → Finset X) (L : ℕ)
    (hcover : ∀ i, ∃ x ∈ H,x ∈ W i)
    (hfreq : ∀ x ∈ H, (univ.filter (fun i => x ∈ W i)).card ≤ L) :
    Fintype.card I ≤ H.card*L := by
  have hu : (univ : Finset I) ⊆ H.biUnion (fun x => univ.filter (fun i => x ∈ W i)) := by
    intro i _
    obtain ⟨x,hx,hi⟩ := hcover i
    exact mem_biUnion.mpr ⟨x,hx,by simp [hi]⟩
  have hc := (card_le_card hu).trans (card_biUnion_le)
  have hs := sum_le_sum (fun x (hx : x ∈ H) => hfreq x hx)
  simpa using hc.trans hs

theorem enough_unknown_for_completion (Q Y : Finset X) (W : I → Finset X) (s L : ℕ)
    (hlarge : s*L < Fintype.card I)
    (hcover : ∀ i, ∃ x ∈ Y ∪ Qᶜ,x ∈ W i)
    (hfreq : ∀ x ∈ Y ∪ Qᶜ, (univ.filter (fun i => x ∈ W i)).card ≤ L) :
    s < (Y ∪ Qᶜ).card := by
  have hc := hitting_set_card_lower (Y ∪ Qᶜ) W L hcover hfreq
  by_contra h
  have hh : (Y ∪ Qᶜ).card ≤ s := by omega
  have hp := Nat.mul_le_mul_right L hh
  omega

lemma intersection_of_completion (Q Y Z : Finset X) (hYQ : Y ⊆ Q)
    (hYZ : Y ⊆ Z) (hZA : Z ⊆ Y ∪ Qᶜ) : Z ∩ Q=Y := by
  ext x
  constructor
  · intro h
    rcases mem_union.mp (hZA (mem_inter.mp h).1) with hy | hn
    · exact hy
    · exact False.elim ((mem_compl.mp hn) (mem_inter.mp h).2)
  · intro h; exact mem_inter.mpr ⟨hYZ h,hYQ h⟩

theorem transcript_consistent (Q Y : Finset X) (s : ℕ) (hYQ : Y ⊆ Q)
    (hsmall : Y.card ≤ s) (hroom : s ≤ (Y ∪ Qᶜ).card) :
    ∃ Z : Finset X,Z.card=s ∧ Z ∩ Q=Y := by
  obtain ⟨Z,hYZ,hZA,hZ⟩ := exists_subsuperset_card_eq (subset_union_left : Y ⊆ Y ∪ Qᶜ) hsmall hroom
  exact ⟨Z,hZ,intersection_of_completion Q Y Z hYQ hYZ hZA⟩

theorem each_window_defeated (Q Y : Finset X) (W : I → Finset X) (s : ℕ)
    (hYQ : Y ⊆ Q) (hsmall : Y.card<s) (hroom : s ≤ (Y ∪ Qᶜ).card)
    (hhit : ∀ i, W i ⊆ Q → (W i ∩ Y).Nonempty) (i : I) :
    ∃ Z : Finset X,Z.card=s ∧ Z ∩ Q=Y ∧ (Z ∩ W i).Nonempty := by
  by_cases hY : (W i ∩ Y).Nonempty
  · obtain ⟨x,hx⟩ := hY
    obtain ⟨Z,hYZ,hZA,hZ⟩ := exists_subsuperset_card_eq
      (subset_union_left : Y ⊆ Y ∪ Qᶜ) hsmall.le hroom
    exact ⟨Z,hZ,intersection_of_completion Q Y Z hYQ hYZ hZA,
      x,mem_inter.mpr ⟨hYZ (mem_inter.mp hx).2,(mem_inter.mp hx).1⟩⟩
  · have hnot : ¬ W i ⊆ Q := fun h => hY (hhit i h)
    obtain ⟨x,hx,hxQ⟩ := not_subset.mp hnot
    have hxA : x ∈ Y ∪ Qᶜ := mem_union_right _ (mem_compl.mpr hxQ)
    have hsub : insert x Y ⊆ Y ∪ Qᶜ := insert_subset hxA subset_union_left
    have hc : (insert x Y).card ≤ s := (card_insert_le x Y).trans (by omega)
    obtain ⟨Z,hreq,hZA,hZ⟩ := exists_subsuperset_card_eq hsub hc hroom
    have hYZ : Y ⊆ Z := (subset_insert x Y).trans hreq
    exact ⟨Z,hZ,intersection_of_completion Q Y Z hYQ hYZ hZA,
      x,mem_inter.mpr ⟨hreq (mem_insert_self x Y),hx⟩⟩

#print axioms hitting_set_card_lower
#print axioms enough_unknown_for_completion
#print axioms transcript_consistent
#print axioms each_window_defeated
end
end CIGAMF.P13.SupportNonadaptiveCompletion
