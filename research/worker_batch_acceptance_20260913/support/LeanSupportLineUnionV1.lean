import «LeanSupportPrivateWindowV1»

/-! Corrected all-private union bound for equally long windows on a line.
This concerns geometric unions, not decision-tree optimality. -/
namespace CIGAMF.P13.SupportLineUnion
open scoped BigOperators
open Finset
open CIGAMF.P13.SupportPrivateWindow

def windows (x : ℕ → ℕ) (L n : ℕ) : Finset ℕ := (range n).biUnion (fun i => Ico (x i) (x i+L))
def AllPrivate (x : ℕ → ℕ) (L n : ℕ) : Prop :=
  ∀ i < n,∃ p ∈ Ico (x i) (x i+L),∀ j < n,j ≠ i → p ∉ Ico (x j) (x j+L)

lemma union_step (x : ℕ → ℕ) (L n : ℕ) :
    windows x L (n+1)=windows x L n ∪ Ico (x n) (x n+L) := by
  ext p
  simp [windows,Finset.mem_range,Nat.lt_add_one_iff,Nat.le_iff_lt_or_eq,or_and_right,exists_or]

lemma last_intersection (x : ℕ → ℕ) (hx : Monotone x) (L n : ℕ) (hn : 0 < n) :
    windows x L n ∩ Ico (x n) (x n+L)=Ico (x n) (x (n-1)+L) := by
  ext p
  simp only [Finset.mem_inter,Finset.mem_Ico,windows,Finset.mem_biUnion,Finset.mem_range]
  constructor
  · rintro ⟨⟨i,hi,hpi⟩,hpn⟩
    have hh := hx (show i ≤ n-1 by omega)
    exact ⟨hpn.1,by omega⟩
  · intro hp
    have hh := hx (show n-1 ≤ n by omega)
    refine ⟨⟨n-1,by omega,?_,hp.2⟩,hp.1,?_⟩ <;> omega

lemma card_step (x : ℕ → ℕ) (hx : Monotone x) (L n : ℕ) (hn : 0 < n) :
    (windows x L (n+1)).card=(windows x L n).card+min (x n-x (n-1)) L := by
  have hc := card_union_add_card_inter (windows x L n) (Ico (x n) (x n+L))
  rw [← union_step,last_intersection x hx L n hn] at hc
  simp only [Nat.card_Ico,Nat.add_sub_cancel_left] at hc
  have hh := hx (show n-1 ≤ n by omega)
  omega

/-- Exact cardinality for an ordered family; overlaps and large gaps included. -/
theorem union_cardinality (x : ℕ → ℕ) (hx : Monotone x) (L n : ℕ) :
    (windows x L (n+1)).card=L+∑ i ∈ range n,min (x (i+1)-x i) L := by
  induction n with
  | zero => simp [windows]
  | succ n ih =>
    rw [card_step x hx L (n+1) (by omega),ih,sum_range_succ]
    simp only [Nat.add_sub_cancel]
    omega

lemma all_private_gap (x : ℕ → ℕ) (hx : StrictMono x) (L n i : ℕ)
    (hp : AllPrivate x L n) (hi : i+2 < n) :
    L+1 ≤ (x (i+1)-x i)+(x (i+2)-x (i+1)) := by
  obtain ⟨p,hpwin,hprivate⟩ := hp (i+1) (by omega)
  have hleft := hprivate i (by omega) (by omega)
  have hright := hprivate (i+2) hi (by omega)
  have h01 := hx (show i < i+1 by omega)
  have h12 := hx (show i+1 < i+2 by omega)
  simp only [Finset.mem_Ico,not_and,not_lt] at *
  have hl := hleft (by omega)
  have hr : p < x (i+2) := by by_contra h;have := hright (by omega);omega
  omega

/-- Odd all-private families satisfy the corrected parity lower bound. -/
theorem odd_all_private_union (x : ℕ → ℕ) (hx : StrictMono x) (L h : ℕ) (hL : 0 < L)
    (hp : AllPrivate x L (2*h+1)) :
    h*(L+1)+L ≤ (windows x L (2*h+1)).card := by
  rw [union_cardinality x hx.monotone L (2*h)]
  apply odd_union_cost
  intro i hi
  apply clipped_pair_gap
  · have := hx (show 2*i < 2*i+1 by omega);omega
  · have := hx (show 2*i+1 < 2*i+1+1 by omega);omega
  · omega
  · have hh := all_private_gap x hx L (2*h+1) (2*i) hp (by omega)
    simpa only [Nat.add_assoc] using hh

/-- Even all-private families, with the final strictly positive gap retained. -/
theorem even_all_private_union (x : ℕ → ℕ) (hx : StrictMono x) (L h : ℕ)
    (hL : 0 < L) (hh : 0 < h) (hp : AllPrivate x L (2*h)) :
    h*(L+1) ≤ (windows x L (2*h)).card := by
  have heq : 2*h=2*(h-1)+1+1 := by omega
  rw [heq,union_cardinality x hx.monotone L (2*(h-1)+1),sum_range_succ]
  have hsum : (h-1)*(L+1) ≤ ∑ i ∈ range (2*(h-1)),min (x (i+1)-x i) L := by
    apply paired_gap_sum
    intro i hi
    apply clipped_pair_gap
    · have := hx (show 2*i < 2*i+1 by omega);omega
    · have := hx (show 2*i+1 < 2*i+1+1 by omega);omega
    · omega
    · have ht := all_private_gap x hx L (2*h) (2*i) hp (by omega)
      simpa only [Nat.add_assoc] using ht
  have hlast : 1 ≤ min (x (2*(h-1)+1)-x (2*(h-1))) L := by
    have := hx (show 2*(h-1) < 2*(h-1)+1 by omega)
    omega
  have hhprod : h*(L+1)=(h-1)*(L+1)+(L+1) := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  omega

/-- General corrected line lemma; every window, not just s-1, is private. -/
theorem line_private_union_lower (x : ℕ → ℕ) (hx : StrictMono x) (L s : ℕ)
    (hL : 0 < L) (hs : 0 < s) (hp : AllPrivate x L s) :
    (s/2)*(L+1)+(s%2)*L ≤ (windows x L s).card := by
  have hmod : s%2=0 ∨ s%2=1 := by omega
  rcases hmod with he | ho
  · have hseq : s=2*(s/2) := by omega
    have h := even_all_private_union x hx L (s/2) hL (by omega) (by simpa only [← hseq] using hp)
    rw [← hseq] at h
    simpa only [he,zero_mul,add_zero] using h
  · have hseq : s=2*(s/2)+1 := by omega
    have h := odd_all_private_union x hx L (s/2) hL (by simpa only [← hseq] using hp)
    rw [← hseq] at h
    simpa only [ho,one_mul] using h

#print axioms union_cardinality
#print axioms all_private_gap
#print axioms odd_all_private_union
#print axioms even_all_private_union
#print axioms line_private_union_lower
end CIGAMF.P13.SupportLineUnion
