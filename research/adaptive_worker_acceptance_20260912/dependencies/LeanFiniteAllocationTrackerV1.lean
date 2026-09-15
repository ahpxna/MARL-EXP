import Mathlib

/-! Explicit deterministic rounding for a sequence of simplex allocations.
At each step sample a query that is below its updated cumulative target.
The discrepancy is bounded by the number of available queries. -/
namespace CIGAMF.P13.FiniteAllocationTracker
open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]

def target (w : ℕ → T → ℝ) (N : ℕ) (i : T) := ∑ t ∈ range N,w t i

def pick (c : T → ℕ) (v : T → ℝ) : T :=
  if h : ∃ i,(c i:ℝ)<v i then Classical.choose h else Classical.choice (inferInstance : Nonempty T)

def counts (w : ℕ → T → ℝ) : ℕ → T → ℕ
  | 0 => fun _ => 0
  | N+1 => fun i => counts w N i + if i=pick (counts w N) (target w (N+1)) then 1 else 0

def query (w : ℕ → T → ℝ) (N : ℕ) := pick (counts w N) (target w (N+1))

lemma counts_succ (w : ℕ → T → ℝ) (N : ℕ) (i : T) :
    counts w (N+1) i=counts w N i+if i=query w N then 1 else 0 := rfl

lemma counts_total (w : ℕ → T → ℝ) (N : ℕ) : (∑ i,counts w N i)=N := by
  induction N with
  | zero => simp [counts]
  | succ N ih => simp only [counts,sum_add_distrib,ih];simp

lemma target_total (w : ℕ → T → ℝ) (hw : ∀ t,∑ i,w t i=1) (N : ℕ) :
    (∑ i,target w N i)=(N:ℝ) := by
  simp only [target]
  rw [sum_comm]
  simp [hw]

lemma pick_below (w : ℕ → T → ℝ) (hw : ∀ t,∑ i,w t i=1) (N : ℕ) :
    (counts w N (query w N):ℝ) < target w (N+1) (query w N) := by
  have hex : ∃ i,(counts w N i:ℝ)<target w (N+1) i := by
    by_contra hn
    push Not at hn
    have hle := sum_le_sum (fun i (_ : i ∈ univ) => hn i)
    have hc : (∑ i,(counts w N i:ℝ))=(N:ℝ) := by exact_mod_cast counts_total w N
    rw [target_total w hw (N+1),hc] at hle
    push_cast at hle
    linarith
  unfold query pick
  rw [dif_pos hex]
  exact Classical.choose_spec hex

lemma upper_discrepancy (w : ℕ → T → ℝ) (hw0 : ∀ t i,0 ≤ w t i)
    (hw : ∀ t,∑ i,w t i=1) (N : ℕ) (i : T) :
    (counts w N i:ℝ)-target w N i ≤ 1 := by
  induction N with
  | zero => simp [counts,target]
  | succ N ih =>
    have ht : target w (N+1) i=target w N i+w N i := by simp [target,sum_range_succ]
    by_cases hi : i=query w N
    · have hp := pick_below w hw N
      rw [← hi] at hp
      rw [counts_succ,if_pos hi]
      push_cast
      linarith
    · rw [counts_succ,if_neg hi,add_zero]
      rw [ht]
      linarith [hw0 N i]

theorem discrepancy_bound (w : ℕ → T → ℝ) (hw0 : ∀ t i,0 ≤ w t i)
    (hw : ∀ t,∑ i,w t i=1) (N : ℕ) (i : T) :
    |(counts w N i:ℝ)-target w N i| ≤ (Fintype.card T:ℝ) := by
  have hup := upper_discrepancy w hw0 hw N i
  have htotal : (∑ j,((counts w N j:ℝ)-target w N j))=0 := by
    rw [sum_sub_distrib,target_total w hw]
    have hc : (∑ j,(counts w N j:ℝ))=(N:ℝ) := by exact_mod_cast counts_total w N
    rw [hc];ring
  have hrest : (∑ j ∈ univ.erase i,((counts w N j:ℝ)-target w N j)) ≤ (Fintype.card T:ℝ) := by
    calc
      _ ≤ ∑ _j ∈ univ.erase i,(1:ℝ) := sum_le_sum (fun j _ => upper_discrepancy w hw0 hw N j)
      _ = ((univ.erase i).card:ℝ) := by simp
      _ ≤ (Fintype.card T:ℝ) := by exact_mod_cast (card_le_card (erase_subset (a:=i) (s:=univ)))
  have he := sum_erase_add univ (fun j => (counts w N j:ℝ)-target w N j) (mem_univ i)
  rw [htotal] at he
  have hcard : (1:ℝ) ≤ Fintype.card T := by exact_mod_cast Fintype.card_pos
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The counts are exactly those of the emitted query sequence, so the bound
is about a realized schedule, not an arbitrary vector satisfying constraints. -/
theorem counts_eq_occurrences (w : ℕ → T → ℝ) (N : ℕ) (i : T) :
    counts w N i=((range N).filter (fun t => query w t=i)).card := by
  induction N with
  | zero => simp [counts]
  | succ N ih =>
    rw [counts_succ,ih,range_add_one,filter_insert]
    by_cases hi : query w N=i
    · simp [hi,Ne.symm,show N ∉ (range N).filter (fun t => query w t=i) by simp]
    · have hh : i ≠ query w N := Ne.symm hi
      simp only [hi,hh,↓reduceIte,add_zero]

#print axioms counts_total
#print axioms pick_below
#print axioms discrepancy_bound
#print axioms counts_eq_occurrences
end
end CIGAMF.P13.FiniteAllocationTracker
