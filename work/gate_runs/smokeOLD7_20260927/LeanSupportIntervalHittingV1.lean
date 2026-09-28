import Mathlib

/-! Greedy interval hitting with a cardinality certificate. Equal-length
integer intervals contained in Q need at most floor(card Q / L) hitting points. -/
namespace CIGAMF.P13.SupportIntervalHitting
open Finset
noncomputable section

def interval (a L : ℕ) : Finset ℕ := Ico a (a+L)

lemma interval_card (a L : ℕ) : (interval a L).card=L := by simp [interval]

lemma interval_mem (a L x : ℕ) : x ∈ interval a L ↔ a ≤ x ∧ x<a+L := by simp [interval]

theorem greedy_hitting (L : ℕ) (hL : 0 < L) (S Q : Finset ℕ)
    (hQ : ∀ a ∈ S,interval a L ⊆ Q) :
    ∃ Y : Finset ℕ,Y ⊆ Q ∧ Y.card*L ≤ Q.card ∧
      ∀ a ∈ S,(Y ∩ interval a L).Nonempty := by
  classical
  induction S using Finset.strongInductionOn generalizing Q
  rename_i S ih
  by_cases hn : S.Nonempty
  · let a := S.min' hn
    have ha : a ∈ S := min'_mem S hn
    have hamin : ∀ b ∈ S,a ≤ b := fun b hb => min'_le S b hb
    let x := a+L-1
    have hx : x ∈ interval a L := (interval_mem _ _ _).mpr (by dsimp [x]; omega)
    let T := S.filter (fun b => x < b)
    have hTS : T ⊂ S := by
      apply ssubset_iff_subset_ne.mpr
      refine ⟨filter_subset _ _,?_⟩
      intro he
      have : a ∈ T := he.symm ▸ ha
      have hh := (mem_filter.mp this).2
      dsimp [x] at hh
      omega
    have hdis : ∀ b ∈ T,Disjoint (interval b L) (interval a L) := by
      intro b hb
      apply disjoint_left.mpr
      intro z hzb hza
      have hb' := (mem_filter.mp hb).2
      have hz1 := (interval_mem _ _ _).mp hzb
      have hz2 := (interval_mem _ _ _).mp hza
      dsimp [x] at hb'
      omega
    have hTQ : ∀ b ∈ T,interval b L ⊆ Q \ interval a L := by
      intro b hb z hz
      exact mem_sdiff.mpr ⟨hQ b (mem_filter.mp hb).1 hz,
        fun hz' => disjoint_left.mp (hdis b hb) hz hz'⟩
    obtain ⟨Y,hY,hcard,hhit⟩ := ih T hTS (Q \ interval a L) hTQ
    have hxQ : x ∈ Q := hQ a ha hx
    have hxY : x ∉ Y := by
      intro hh
      exact (mem_sdiff.mp (hY hh)).2 hx
    refine ⟨insert x Y,insert_subset hxQ (hY.trans sdiff_subset),?_,?_⟩
    · rw [card_insert_of_notMem hxY]
      have hc := card_sdiff_add_card_eq_card (hQ a ha)
      rw [interval_card] at hc
      nlinarith
    · intro b hb
      by_cases hxb : x < b
      · obtain ⟨z,hz⟩ := hhit b (mem_filter.mpr ⟨hb,hxb⟩)
        exact ⟨z,mem_inter.mpr ⟨mem_insert_of_mem (mem_inter.mp hz).1,(mem_inter.mp hz).2⟩⟩
      · refine ⟨x,mem_inter.mpr ⟨mem_insert_self _ _,?_⟩⟩
        apply (interval_mem _ _ _).mpr
        have hab := hamin b hb
        dsimp [x] at *
        omega
  · refine ⟨∅,empty_subset _,by simp,?_⟩
    intro a ha
    exact False.elim (hn ⟨a,ha⟩)

#print axioms interval_card
#print axioms greedy_hitting
end
end CIGAMF.P13.SupportIntervalHitting
