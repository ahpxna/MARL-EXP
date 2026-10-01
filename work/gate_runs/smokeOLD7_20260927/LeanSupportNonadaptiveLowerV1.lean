import «LeanSupportCyclicWindowV1»

namespace CIGAMF.P13.SupportNonadaptiveLower
open Finset
open CIGAMF.P13.SupportCyclicWindow CIGAMF.P13.SupportNonadaptiveCompletion
noncomputable section
variable {m : ℕ} [NeZero m]

theorem cyclic_hitting (L : ℕ) (hL : 0<L) (Q : Finset (ZMod m)) (hQ : Q.card< m) :
    ∃ Y : Finset (ZMod m),Y ⊆ Q ∧ Y.card*L ≤ Q.card ∧
      ∀ a,window L a ⊆ Q → (Y ∩ window L a).Nonempty := by
  have hex : ∃ c : ZMod m,c ∉ Q := by
    by_contra h
    push_neg at h
    have he : Q=univ := eq_univ_of_forall h
    rw [he,card_univ,ZMod.card] at hQ
    omega
  obtain ⟨c,hc⟩ := hex
  let Q' := Q.image (fun x => x-c)
  have hzero : 0 ∉ Q' := by
    intro h
    obtain ⟨x,hx,he⟩ := mem_image.mp h
    have hx0 : x=c := sub_eq_zero.mp he
    subst x
    exact hc hx
  obtain ⟨Y,hY,hcard,hhit⟩ := zero_cut_hitting L hL Q' hzero
  let Z := Y.image (fun x => x+c)
  have hZQ : Z ⊆ Q := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
    obtain ⟨x,hx,he⟩ := mem_image.mp (hY hy)
    rw [← he,sub_add_cancel]
    exact hx
  have hQc : Q'.card=Q.card := card_image_of_injective Q (fun x y h =>
    add_right_cancel (show x + -c = y + -c by simpa only [sub_eq_add_neg] using h))
  have hZc : Z.card=Y.card := card_image_of_injective Y (fun x y h => add_right_cancel h)
  refine ⟨Z,hZQ,?_,?_⟩
  · rw [hZc]
    simpa only [hQc] using hcard
  intro a ha
  have htran : window L (a-c) ⊆ Q' := by
    rw [← translate_window L a c]
    exact image_subset_image ha
  obtain ⟨x,hx⟩ := hhit (a-c) htran
  refine ⟨x+c,mem_inter.mpr ⟨mem_image.mpr ⟨x,(mem_inter.mp hx).1,rfl⟩,?_⟩⟩
  have hh := (mem_window L (a-c) x).mp (mem_inter.mp hx).2
  rw [mem_window]
  convert hh using 1 <;> congr 1 <;> ring

def Sufficient (s L : ℕ) (Q : Finset (ZMod m)) : Prop :=
  ∀ W : Finset (ZMod m),W.card=s → ∃ a : ZMod m,
    ∀ V : Finset (ZMod m),V.card=s → V ∩ Q=W ∩ Q → Disjoint (window L a) V

theorem nonadaptive_lower (s L : ℕ) (hL : 0<L) (hlarge : s*L< m)
    (Q : Finset (ZMod m)) (hQ : Q.card<s*L) : ¬ Sufficient s L Q := by
  obtain ⟨Y,hY,hcard,hhit⟩ := cyclic_hitting L hL Q (hQ.trans hlarge)
  have hsmall : Y.card<s := by
    by_contra h
    have hh : s ≤ Y.card := by omega
    have hp := Nat.mul_le_mul_right L hh
    omega
  have hcover : ∀ a : ZMod m,∃ x ∈ Y ∪ Qᶜ,x ∈ window L a := by
    intro a
    by_cases ha : window L a ⊆ Q
    · obtain ⟨x,hx⟩ := hhit a ha
      exact ⟨x,mem_union_left _ (mem_inter.mp hx).1,(mem_inter.mp hx).2⟩
    · obtain ⟨x,hx,hxQ⟩ := not_subset.mp ha
      exact ⟨x,mem_union_right _ (mem_compl.mpr hxQ),hx⟩
  have hroom : s ≤ (Y ∪ Qᶜ).card := (enough_unknown_for_completion Q Y (window L) s L
    (by simpa [ZMod.card] using hlarge) hcover (fun x _ => incidence_bound L x)).le
  obtain ⟨W,hW,hWQ⟩ := transcript_consistent Q Y s hY hsmall.le hroom
  intro hs
  obtain ⟨a,ha⟩ := hs W hW
  have hhit' : ∀ a,window L a ⊆ Q → (window L a ∩ Y).Nonempty := by
    intro a h; simpa [inter_comm] using hhit a h
  obtain ⟨V,hV,hVQ,x,hx⟩ := each_window_defeated Q Y (window L) s hY hsmall hroom hhit' a
  have hd := ha V hV (hVQ.trans hWQ.symm)
  exact disjoint_left.mp hd (mem_inter.mp hx).2 (mem_inter.mp hx).1

#print axioms cyclic_hitting
#print axioms nonadaptive_lower
end
end CIGAMF.P13.SupportNonadaptiveLower
