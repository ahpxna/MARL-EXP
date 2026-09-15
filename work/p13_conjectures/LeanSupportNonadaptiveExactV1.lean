import «LeanSupportNonadaptiveLowerV1»

namespace CIGAMF.P13.SupportNonadaptiveExact
open Finset
open CIGAMF.P13.SupportIntervalHitting CIGAMF.P13.SupportCyclicWindow
open CIGAMF.P13.SupportNonadaptiveCompletion CIGAMF.P13.SupportNonadaptiveLower
noncomputable section
variable {m : ℕ} [NeZero m]

theorem safe_window_exists (s L : ℕ) (hlarge : s*L< m)
    (W : Finset (ZMod m)) (hW : W.card=s) : ∃ a,Disjoint (window L a) W := by
  by_contra h
  push_neg at h
  have hit : ∀ a : ZMod m,∃ x ∈ W,x ∈ window L a := by
    intro a
    obtain ⟨x,hxW,hx⟩ := not_disjoint_iff.mp (h a)
    exact ⟨x,hx,hxW⟩
  have hc := hitting_set_card_lower W (window L) L hit (fun x _ => incidence_bound L x)
  rw [ZMod.card,hW] at hc
  omega

def blockQueries (s L : ℕ) : Finset (ZMod m) := (range (s*L)).image (fun (v : ℕ) => (v : ZMod m))

lemma block_mem (s L : ℕ) (hlarge : s*L< m) (i : Fin s) (x : ZMod m) :
    x ∈ window L ((i.val*L : ℕ) : ZMod m) ↔ i.val*L ≤ x.val ∧ x.val<(i.val+1)*L := by
  have hi : (i.val+1)*L ≤ s*L := Nat.mul_le_mul_right L (by omega)
  have hiv : i.val*L< m := by nlinarith
  have he : ((i.val*L : ℕ) : ZMod m).val=i.val*L := ZMod.val_natCast_of_lt hiv
  have hnw : ((i.val*L : ℕ) : ZMod m).val+L ≤ m := by rw [he]; nlinarith
  simpa only [interval_mem,he,Nat.add_mul,Nat.one_mul] using
    (nonwrapping_mem L ((i.val*L : ℕ) : ZMod m) x hnw)

lemma block_subset (s L : ℕ) (hlarge : s*L< m) (i : Fin s) :
    window L ((i.val*L : ℕ) : ZMod m) ⊆ blockQueries s L := by
  intro x hx
  have hi := (block_mem s L hlarge i x).mp hx
  have hle := Nat.mul_le_mul_right L (show i.val+1 ≤ s by omega)
  exact mem_image.mpr ⟨x.val,mem_range.mpr (hi.2.trans_le hle),ZMod.natCast_zmod_val x⟩

lemma blocks_disjoint (s L : ℕ) (hlarge : s*L< m) (i j : Fin s) (hij : i ≠ j) :
    Disjoint (window L ((i.val*L : ℕ) : ZMod m)) (window L ((j.val*L : ℕ) : ZMod m)) := by
  apply disjoint_left.mpr
  intro x hi hj
  have hi' := (block_mem s L hlarge i x).mp hi
  have hj' := (block_mem s L hlarge j x).mp hj
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := Nat.mul_le_mul_right L (show i.val+1 ≤ j.val by omega)
    omega
  · have hh := Nat.mul_le_mul_right L (show j.val+1 ≤ i.val by omega)
    omega

lemma all_blocks_hit_identifies (s L : ℕ) (hlarge : s*L< m)
    (W : Finset (ZMod m)) (hW : W.card=s)
    (hit : ∀ i : Fin s,(W ∩ window L ((i.val*L : ℕ) : ZMod m)).Nonempty) : W ⊆ blockQueries s L := by
  choose f hf using hit
  have hsub : ∀ i,f i ∈ W ∩ blockQueries s L := by
    intro i
    exact mem_inter.mpr ⟨(mem_inter.mp (hf i)).1,block_subset s L hlarge i (mem_inter.mp (hf i)).2⟩
  have hinj : Function.Injective f := by
    intro i j h
    by_contra hne
    have hd := blocks_disjoint s L hlarge i j hne
    exact disjoint_left.mp hd (mem_inter.mp (hf i)).2 (by rw [h]; exact (mem_inter.mp (hf j)).2)
  have hc := Fintype.card_le_of_injective (fun i => (⟨f i,hsub i⟩ : ↥(W ∩ blockQueries s L)))
    (fun i j h => hinj (congrArg Subtype.val h))
  have he : W ∩ blockQueries s L=W := eq_of_subset_of_card_le inter_subset_left
    (by simpa only [Fintype.card_coe,Fintype.card_fin,hW] using hc)
  exact inter_eq_left.mp he

theorem nonadaptive_upper (s L : ℕ) (hlarge : s*L< m) :
    Sufficient s L (blockQueries s L : Finset (ZMod m)) := by
  intro W hW
  by_cases hit : ∀ i : Fin s,(W ∩ window L ((i.val*L : ℕ) : ZMod m)).Nonempty
  · have hWQ := all_blocks_hit_identifies s L hlarge W hW hit
    obtain ⟨a,ha⟩ := safe_window_exists s L hlarge W hW
    refine ⟨a,?_⟩
    intro V hV hreply
    have hWV : W ⊆ V := by
      rw [inter_eq_left.mpr hWQ] at hreply
      rw [← hreply]
      exact inter_subset_left
    have heq : W=V := eq_of_subset_of_card_le hWV (by omega)
    simpa [← heq] using ha
  · push_neg at hit
    obtain ⟨i,hi⟩ := hit
    refine ⟨((i.val*L : ℕ) : ZMod m),?_⟩
    intro V hV hreply
    apply disjoint_left.mpr
    intro x hxwin hxV
    have hxQ := block_subset s L hlarge i hxwin
    have hxR : x ∈ W ∩ blockQueries s L := hreply ▸ mem_inter.mpr ⟨hxV,hxQ⟩
    have hem : x ∈ W ∩ window L ((i.val*L : ℕ) : ZMod m) := mem_inter.mpr ⟨(mem_inter.mp hxR).1,hxwin⟩
    rw [hi] at hem
    simpa using hem

def depths (s L : ℕ) : Set ℕ := {d | ∃ Q : Finset (ZMod m),Q.card=d ∧ Sufficient s L Q}

theorem nonadaptive_exact (s L : ℕ) (hL : 0<L) (hlarge : s*L< m) :
    IsLeast (depths (m:=m) s L) (s*L) := by
  have hcard : (blockQueries s L : Finset (ZMod m)).card=s*L := by
    unfold blockQueries
    rw [card_image_iff.mpr,card_range]
    intro x hx y hy he
    have hxlt : x< m := (mem_range.mp hx).trans hlarge
    have hylt : y< m := (mem_range.mp hy).trans hlarge
    have hv := congrArg ZMod.val he
    simpa [ZMod.val_natCast_of_lt hxlt,ZMod.val_natCast_of_lt hylt] using hv
  refine ⟨⟨blockQueries s L,hcard,nonadaptive_upper s L hlarge⟩,?_⟩
  rintro d ⟨Q,rfl,hQ⟩
  by_contra h
  exact nonadaptive_lower s L hL hlarge Q (by omega) hQ

#print axioms safe_window_exists
#print axioms blocks_disjoint
#print axioms all_blocks_hit_identifies
#print axioms nonadaptive_upper
#print axioms nonadaptive_exact
end
end CIGAMF.P13.SupportNonadaptiveExact
