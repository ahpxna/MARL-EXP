import Mathlib

/-! A refutation of the s-1-private helper and the local geometric inequality
needed by the corrected all-private route. No decision-depth claim is made. -/
namespace CIGAMF.P13.SupportPrivateWindow
open scoped BigOperators
open Finset

def W0 : Finset ℕ := {0,1,2}
def W1 : Finset ℕ := {2,3,4}
def W2 : Finset ℕ := {1,2,3}

theorem old_helper_counterexample :
    W0.card=3 ∧ W1.card=3 ∧ W2.card=3 ∧
    0 ∈ W0 ∧ 0 ∉ W1 ∧ 0 ∉ W2 ∧
    4 ∈ W1 ∧ 4 ∉ W0 ∧ 4 ∉ W2 ∧
    (W0 ∪ W1 ∪ W2).card=5 ∧
    (W0 ∪ W1 ∪ W2).card < (3/2)*(3+1)+(3%2)*3 := by decide

/-- A private point in the middle interval forces the two adjacent gaps
jointly to exceed the window length. Intervals are half-open integer windows. -/
theorem private_middle_gap (a b c L p : ℤ) (hab : a < b) (hbc : b < c)
    (hp : p ∈ Finset.Ico b (b+L))
    (hpa : p ∉ Finset.Ico a (a+L)) (hpc : p ∉ Finset.Ico c (c+L)) :
    L+1 ≤ (b-a)+(c-b) := by
  simp only [Finset.mem_Ico,not_and,not_lt] at *
  have hleft := hpa (by omega)
  have hright : p < c := by by_contra h;have := hpc (by omega);omega
  omega

/-- Truncating each positive gap at L preserves the paired lower bound. -/
theorem clipped_pair_gap (d e L : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hL : 1 ≤ L) (hpair : L+1 ≤ d+e) :
    L+1 ≤ min d L+min e L := by omega

/-- Summing disjoint gap pairs gives the parity term. These are explicit local
geometric premises; connecting them to a whole cyclic union is still separate. -/
theorem paired_gap_sum (h L : ℕ) (g : ℕ → ℕ)
    (hp : ∀ i < h,L+1 ≤ g (2*i)+g (2*i+1)) :
    h*(L+1) ≤ ∑ i ∈ range (2*h),g i := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hh := ih (fun i hi => hp i (by omega))
    have hl := hp h (by omega)
    rw [show 2*(h+1)=2*h+1+1 by omega,sum_range_succ,sum_range_succ]
    nlinarith

/-- Odd interval count: the first window and paired gaps have the stated size. -/
theorem odd_union_cost (h L : ℕ) (g : ℕ → ℕ)
    (hp : ∀ i < h,L+1 ≤ g (2*i)+g (2*i+1)) :
    h*(L+1)+L ≤ L+∑ i ∈ range (2*h),g i := by
  have := paired_gap_sum h L g hp
  omega

#print axioms old_helper_counterexample
#print axioms private_middle_gap
#print axioms clipped_pair_gap
#print axioms paired_gap_sum
#print axioms odd_union_cost
end CIGAMF.P13.SupportPrivateWindow
