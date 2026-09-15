import «LeanFiniteTrackerCausalityV1»

/-! A finite, data-only optimization rule. The candidate set consists of all
integer simplex allocations with denominator H. Maximizers are selected by the
same fixed finite comparison-pattern rule as the tracker. The theorem quantifies
its approximation error; no near-optimality premise is supplied by a caller.
This is exact-real finite optimization, not a bit-complexity claim. -/
namespace CIGAMF.P13.FiniteGridSolver
open scoped BigOperators
open Finset MeasureTheory
open CIGAMF.P13.FiniteAllocationTracker CIGAMF.P13.FiniteTrackerCausality
noncomputable section
variable {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]

abbrev Grid (T : Type*) [Fintype T] (H : ℕ) :=
  {c : T → Fin (H+1) // ∑ i,(c i).val=H}

def weight {H : ℕ} (g : Grid T H) (i : T) : ℝ := ((g.val i).val:ℝ)/(H:ℝ)

lemma grid_nonempty (H : ℕ) : Nonempty (Grid T H) := by
  let i0 : T := Classical.choice (inferInstance : Nonempty T)
  let c : T → Fin (H+1) := fun i => ⟨if i=i0 then H else 0,by split_ifs <;> omega⟩
  exact ⟨⟨c,by simp [c]⟩⟩

lemma weight_nonneg {H : ℕ} (g : Grid T H) (i : T) : 0 ≤ weight g i := by
  unfold weight
  positivity

lemma weight_total {H : ℕ} (hH : 0 < H) (g : Grid T H) : ∑ i,weight g i=1 := by
  unfold weight
  rw [← sum_div]
  have h : (∑ i,((g.val i).val:ℝ))=(H:ℝ) := by exact_mod_cast g.property
  rw [h,div_self (by exact_mod_cast Nat.ne_of_gt hH)]

/-- Tracker counts give a constructive witness in the grid for any simplex. -/
theorem grid_dense (H : ℕ) (hH : 0 < H) (v : T → ℝ)
    (hv0 : ∀ i,0 ≤ v i) (hv : ∑ i,v i=1) :
    ∃ g : Grid T H, ∑ i,|v i-weight g i| ≤ (Fintype.card T:ℝ)^2/(H:ℝ) := by
  let w : ℕ → T → ℝ := fun _ => v
  have hb (i : T) : counts w H i ≤ H := by
    have h := single_le_sum (fun j (_ : j ∈ univ) => Nat.zero_le (counts w H j)) (mem_univ i)
    rwa [counts_total] at h
  let g : Grid T H := ⟨fun i => ⟨counts w H i,by have := hb i;omega⟩,counts_total w H⟩
  refine ⟨g,?_⟩
  have hHr : (0:ℝ)<H := by exact_mod_cast hH
  have he (i : T) : |v i-weight g i| ≤ (Fintype.card T:ℝ)/(H:ℝ) := by
    have h := discrepancy_bound w (fun _ => hv0) (fun _ => hv) H i
    have ht : target w H i=(H:ℝ)*v i := by simp [target,w]
    rw [ht] at h
    have hdiv := div_le_div_of_nonneg_right h hHr.le
    have hid : |v i-weight g i|=|(counts w H i:ℝ)-(H:ℝ)*v i|/(H:ℝ) := by
      change |v i-(counts w H i:ℝ)/(H:ℝ)|= _
      have heq : (counts w H i:ℝ)/(H:ℝ)-v i = ((counts w H i:ℝ)-(H:ℝ)*v i)/(H:ℝ) := by
        field_simp
      rw [abs_sub_comm,heq,abs_div,abs_of_pos hHr]
    rw [hid]
    exact hdiv
  calc
    _ ≤ ∑ _i : T,(Fintype.card T:ℝ)/(H:ℝ) := sum_le_sum (fun i _ => he i)
    _ = _ := by simp [pow_two];ring

/-- A fixed choice among the finite maximizer set. It depends only on pairwise
comparisons, never on unknown true parameters or future observations. -/
def argmax (s : T → ℝ) : T :=
  pick (fun _ => 0) (fun i => if ∀ j,s j ≤ s i then 1 else 0)

lemma argmax_spec (s : T → ℝ) (i : T) : s i ≤ s (argmax s) := by
  obtain ⟨a,ha,hmax⟩ := exists_max_image univ s univ_nonempty
  have hex : ∃ a : T,(0:ℝ)<(if ∀ j,s j ≤ s a then 1 else 0) :=
    ⟨a,by rw [if_pos (fun j => hmax j (mem_univ j))];norm_num⟩
  have hp : (0:ℝ)<(if ∀ j,s j ≤ s (argmax s) then 1 else 0) := by
    unfold argmax pick
    simp only [Nat.cast_zero]
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  split_ifs at hp with hm
  · exact hm i
  · norm_num at hp

lemma argmax_measurable [MeasurableSpace T] [MeasurableSingletonClass T]
    {Ω : Type*} [MeasurableSpace Ω] (s : Ω → T → ℝ)
    (hs : ∀ i,Measurable (fun x => s x i)) :
    Measurable (fun x => argmax (s x)) := by
  apply pick_measurable _ _ (fun _ => measurable_const)
  intro i
  apply Measurable.ite _ measurable_const measurable_const
  convert MeasurableSet.iInter (fun j => measurableSet_le (hs j) (hs i)) using 1
  ext x
  simp

def solve (H : ℕ) (f : (T → ℝ) → ℝ) : Grid T H :=
  letI := grid_nonempty (T:=T) H
  argmax (fun g : Grid T H => f (weight g))

lemma solve_max (H : ℕ) (f : (T → ℝ) → ℝ) (g : Grid T H) :
    f (weight g) ≤ f (weight (solve H f)) := by
  letI := grid_nonempty (T:=T) H
  exact argmax_spec (fun g : Grid T H => f (weight g)) g

/-- Uniform grid error for a simplex objective with a proved L1 modulus C. -/
theorem solve_error (H : ℕ) (hH : 0 < H) (f : (T → ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ v u : T → ℝ,(∀ i,0 ≤ v i) → (∀ i,0 ≤ u i) →
      f v ≤ f u+C*(∑ i,|v i-u i|))
    (v : T → ℝ) (hv0 : ∀ i,0 ≤ v i) (hv : ∑ i,v i=1) :
    f v ≤ f (weight (solve H f))+C*(Fintype.card T:ℝ)^2/(H:ℝ) := by
  obtain ⟨g,hg⟩ := grid_dense H hH v hv0 hv
  have h1 := hf v (weight g) hv0 (weight_nonneg g)
  have h2 := mul_le_mul_of_nonneg_left hg hC
  have h3 := solve_max H f g
  rw [← mul_div_assoc] at h2
  linarith

/-- Measurability is a consequence of finitely many measurable score evaluations. -/
theorem solve_measurable {Ω : Type*} [MeasurableSpace Ω]
    (H : ℕ) (f : Ω → (T → ℝ) → ℝ)
    (hf : ∀ g : Grid T H,Measurable (fun x => f x (weight g))) :
    Measurable (fun x => solve H (f x)) := by
  letI := grid_nonempty (T:=T) H
  exact argmax_measurable _ hf

#print axioms grid_dense
#print axioms weight_total
#print axioms argmax_spec
#print axioms argmax_measurable
#print axioms solve_error
#print axioms solve_measurable
end
end CIGAMF.P13.FiniteGridSolver
