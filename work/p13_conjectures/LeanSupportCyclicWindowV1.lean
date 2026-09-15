import «LeanSupportIntervalHittingV1»
import «LeanSupportNonadaptiveCompletionV1»

namespace CIGAMF.P13.SupportCyclicWindow
open Finset
open CIGAMF.P13.SupportIntervalHitting
noncomputable section
variable {m : ℕ} [NeZero m]

def window (L : ℕ) (a : ZMod m) : Finset (ZMod m) :=
  univ.filter (fun x => (x-a).val<L)

lemma mem_window (L : ℕ) (a x : ZMod m) : x ∈ window L a ↔ (x-a).val<L := by simp [window]

lemma val_sub_wrap (a x : ZMod m) (h : x.val<a.val) :
    (x-a).val=m-(a.val-x.val) := by
  have hn : a-x ≠ 0 := by
    intro he
    have heq := sub_eq_zero.mp he
    have hh := congrArg ZMod.val heq
    omega
  rw [show x-a=-(a-x) by ring,ZMod.neg_val (a-x),if_neg hn,ZMod.val_sub h.le]

lemma no_wrap (L : ℕ) (hL : 0<L) (a : ZMod m) (h : 0 ∉ window L a) :
    a.val+L ≤ m := by
  have hh : L ≤ (-a).val := by simpa [window] using h
  by_cases ha : a=0
  · subst a; simp at hh; omega
  · rw [ZMod.neg_val a,if_neg ha] at hh
    have hv := ZMod.val_lt a
    omega

lemma nonwrapping_mem (L : ℕ) (a x : ZMod m) (ha : a.val+L ≤ m) :
    x ∈ window L a ↔ x.val ∈ interval a.val L := by
  rw [mem_window,interval_mem]
  by_cases hax : a.val ≤ x.val
  · rw [ZMod.val_sub hax]; omega
  · have hxa : x.val<a.val := by omega
    rw [val_sub_wrap a x hxa]
    have hv := ZMod.val_lt a
    omega

theorem incidence_bound (L : ℕ) (x : ZMod m) :
    (univ.filter (fun a => x ∈ window L a)).card ≤ L := by
  let T := univ.filter (fun a => x ∈ window L a)
  let f : T → Fin L := fun a => ⟨(x-a.val).val,(mem_window L a.val x).mp (mem_filter.mp a.property).2⟩
  have hf : Function.Injective f := by
    intro a b h
    have hv : (x-a.val).val=(x-b.val).val := congrArg Fin.val h
    have he : x-a.val=x-b.val := ZMod.val_injective m hv
    apply Subtype.ext
    exact sub_right_injective he
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fin] using hc

theorem translate_window (L : ℕ) (a c : ZMod m) :
    (window L a).image (fun x => x-c)=window L (a-c) := by
  ext x
  constructor
  · rintro hx
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    simpa [window,sub_sub_sub_cancel_right] using hz
  · intro hx
    refine mem_image.mpr ⟨x+c,?_,by ring⟩
    have he : x+c-a=x-(a-c) := by ring
    simpa [window,he] using hx

theorem zero_cut_hitting (L : ℕ) (hL : 0<L) (Q : Finset (ZMod m)) (hzero : 0 ∉ Q) :
    ∃ Y : Finset (ZMod m),Y ⊆ Q ∧ Y.card*L ≤ Q.card ∧
      ∀ a,window L a ⊆ Q → (Y ∩ window L a).Nonempty := by
  let Qn := Q.image ZMod.val
  let A := univ.filter (fun a => window L a ⊆ Q)
  let S := A.image ZMod.val
  have hSQ : ∀ a ∈ S,interval a L ⊆ Qn := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    have haw : window L a ⊆ Q := (mem_filter.mp ha).2
    have hnw := no_wrap L hL a (fun h => hzero (haw h))
    intro z hz
    have hzlt : z< m := by have h := (interval_mem _ _ _).mp hz; omega
    have hval : (z : ZMod m).val=z := ZMod.val_natCast_of_lt hzlt
    have hmem : (z : ZMod m) ∈ window L a := (nonwrapping_mem L a _ hnw).mpr (by simpa [hval] using hz)
    exact mem_image.mpr ⟨(z : ZMod m),haw hmem,hval⟩
  obtain ⟨Yn,hYn,hcard,hhit⟩ := greedy_hitting L hL S Qn hSQ
  let Y := Yn.image (fun (z : ℕ) => (z : ZMod m))
  have hY : Y ⊆ Q := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    obtain ⟨w,hw,he⟩ := mem_image.mp (hYn hv)
    rw [← he,ZMod.natCast_zmod_val]
    exact hw
  have hQcard : Qn.card=Q.card := card_image_of_injective Q (ZMod.val_injective m)
  refine ⟨Y,hY,?_,?_⟩
  · have hc : Y.card ≤ Yn.card := card_image_le
    have hm := Nat.mul_le_mul_right L hc
    omega
  · intro a ha
    have haS : a.val ∈ S := mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,ha⟩,rfl⟩
    obtain ⟨v,hv⟩ := hhit a.val haS
    have hi := (mem_inter.mp hv).2
    have hnw := no_wrap L hL a (fun h => hzero (ha h))
    have hvlt : v< m := by have h := (interval_mem _ _ _).mp hi; omega
    refine ⟨(v : ZMod m),mem_inter.mpr ⟨mem_image.mpr ⟨v,(mem_inter.mp hv).1,rfl⟩,?_⟩⟩
    apply (nonwrapping_mem L a _ hnw).mpr
    simpa [ZMod.val_natCast_of_lt hvlt] using hi

#print axioms no_wrap
#print axioms nonwrapping_mem
#print axioms incidence_bound
#print axioms translate_window
#print axioms zero_cut_hitting
end
end CIGAMF.P13.SupportCyclicWindow
