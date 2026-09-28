import «LeanFiniteAllocationTrackerV1»

/-! Causality and measurability of the existing tracker. Classical choice in
`pick` is a fixed function of a finite comparison pattern; it cannot inspect
future targets. Step N uses targets through N and counts through N-1. -/
namespace CIGAMF.P13.FiniteTrackerCausality
open scoped BigOperators
open Finset MeasureTheory
open CIGAMF.P13.FiniteAllocationTracker
noncomputable section
variable {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]

lemma target_prefix (w v : ℕ → T → ℝ) (N : ℕ)
    (h : ∀ t < N,w t=v t) : target w N=target v N := by
  funext i
  exact sum_congr rfl (fun t ht => congrFun (h t (mem_range.mp ht)) i)

lemma counts_prefix (w v : ℕ → T → ℝ) (N : ℕ)
    (h : ∀ t < N,w t=v t) : counts w N=counts v N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hc := ih (fun t ht => h t (by omega))
    have ht := target_prefix w v (N+1) h
    funext i
    simp only [counts]
    rw [hc,ht]

/-- Same observed targets imply the same next query, including tie-breaking. -/
theorem query_prefix (w v : ℕ → T → ℝ) (N : ℕ)
    (h : ∀ t ≤ N,w t=v t) : query w N=query v N := by
  unfold query
  rw [counts_prefix w v N (fun t ht => h t (by omega)),
    target_prefix w v (N+1) (fun t ht => h t (by omega))]

variable [MeasurableSpace T] [MeasurableSingletonClass T]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Choice is from a fixed finite bit pattern, so no measurable-selection
axiom is needed even though the old tracker is noncomputable. -/
lemma pick_measurable (c : Ω → T → ℕ) (v : Ω → T → ℝ)
    (hc : ∀ i,Measurable (fun x => c x i))
    (hv : ∀ i,Measurable (fun x => v x i)) :
    Measurable (fun x => pick (c x) (v x)) := by
  let pattern : Ω → T → Bool := fun x i => if (c x i:ℝ)<v x i then true else false
  let choosePattern : (T → Bool) → T := fun b =>
    if h : ∃ i,b i=true then Classical.choose h else Classical.choice (inferInstance : Nonempty T)
  have hm : Measurable pattern := by
    apply measurable_pi_lambda
    intro i
    exact Measurable.ite (measurableSet_lt ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (hc i)) (hv i)) measurable_const measurable_const
  have he : (fun x => pick (c x) (v x))=choosePattern ∘ pattern := by
    funext x
    simp [Function.comp_def,choosePattern,pattern,pick]

  rw [he]
  exact (measurable_of_finite choosePattern).comp hm

lemma target_measurable (w : ℕ → Ω → T → ℝ) (N : ℕ)
    (hw : ∀ t < N,∀ i,Measurable (fun x => w t x i)) (i : T) :
    Measurable (fun x => target (fun t => w t x) N i) := by
  exact Finset.measurable_sum _ (fun t ht => hw t (mem_range.mp ht) i)

lemma counts_measurable (w : ℕ → Ω → T → ℝ) (N : ℕ)
    (hw : ∀ t < N,∀ i,Measurable (fun x => w t x i)) (i : T) :
    Measurable (fun x => counts (fun t => w t x) N i) := by
  induction N generalizing i with
  | zero => exact measurable_const
  | succ N ih =>
    have hc : ∀ i,Measurable (fun x => counts (fun t => w t x) N i) :=
      fun i => ih (fun t ht => hw t (by omega)) i
    have hp := pick_measurable (fun x => counts (fun t => w t x) N)
      (fun x => target (fun t => w t x) (N+1)) hc (target_measurable w (N+1) hw)
    exact (hc i).add (Measurable.ite (measurableSet_eq_fun measurable_const hp)
      measurable_const measurable_const)

/-- Only targets available at time N are needed to prove next-query measurability. -/
theorem query_measurable (w : ℕ → Ω → T → ℝ) (N : ℕ)
    (hw : ∀ t ≤ N,∀ i,Measurable (fun x => w t x i)) :
    Measurable (fun x => query (fun t => w t x) N) :=
  pick_measurable _ _ (counts_measurable w N (fun t ht => hw t (by omega)))
    (target_measurable w (N+1) (fun t ht => hw t (by omega)))

/-- Filtration version: a target available after N observations yields a query
for observation N+1 measurable in F_N. -/
theorem query_adapted {m : MeasurableSpace Ω} (F : Filtration ℕ m)
    (w : ℕ → Ω → T → ℝ)
    (hw : ∀ t i,Measurable[F t] (fun x => w t x i)) (N : ℕ) :
    Measurable[F N] (fun x => query (fun t => w t x) N) := by
  apply @query_measurable T _ _ _ _ _ Ω (F N) w N
  intro t ht i
  exact (hw t i).mono (F.mono ht) le_rfl

#print axioms query_prefix
#print axioms pick_measurable
#print axioms counts_measurable
#print axioms query_measurable
#print axioms query_adapted
end
end CIGAMF.P13.FiniteTrackerCausality
