import «LeanFiniteAllocationTrackerV1»

/-! The constructive tracker is measurable and uses targets only up to the
current time. This is the missing probabilistic interface of its pathwise
rounding theorem. The target at time N must itself be chosen from past data. -/
namespace CIGAMF.P13.FiniteAllocationTrackerMeasurable
open scoped BigOperators
open Finset MeasureTheory
open CIGAMF.P13.FiniteAllocationTracker
noncomputable section
attribute [local instance] Classical.propDecidable
variable {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
variable {Ω : Type*} [MeasurableSpace Ω]

private def chooseMask (mask : T → Bool) : T :=
  if h : ∃ i,mask i=true then Classical.choose h else Classical.choice (inferInstance : Nonempty T)

lemma pick_eq_mask (c : T → ℕ) (v : T → ℝ) :
    pick c v=chooseMask (fun i => decide ((c i:ℝ)<v i)) := by
  simp [pick,chooseMask]

/-- A finite Boolean deficiency mask makes the arbitrary finite chooser
measurable without assuming continuity of the chooser. -/
theorem measurable_pick [MeasurableSpace T] [MeasurableSingletonClass T]
    (c : Ω → T → ℕ) (v : Ω → T → ℝ)
    (hc : ∀ i,Measurable (fun x => c x i)) (hv : ∀ i,Measurable (fun x => v x i)) :
    Measurable (fun x => pick (c x) (v x)) := by
  simp_rw [pick_eq_mask]
  have hm : Measurable (fun x i => decide ((c x i:ℝ)<v x i)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_to_bool
    change MeasurableSet {x | decide ((c x i:ℝ)<v x i)=true}
    simp only [decide_eq_true_eq]
    exact measurableSet_lt ((measurable_of_countable (f:=fun n : ℕ => (n:ℝ))).comp (hc i)) (hv i)
  exact (measurable_of_countable (f:=chooseMask)).comp hm

/-- Counts and the next query are random variables whenever targets are. -/
theorem counts_measurable [MeasurableSpace T] [MeasurableSingletonClass T]
    (w : Ω → ℕ → T → ℝ) (hw : ∀ t i,Measurable (fun x => w x t i)) :
    ∀ N i,Measurable (fun x => counts (w x) N i) := by
  intro N
  induction N with
  | zero => intro i; simpa [counts] using (measurable_const : Measurable (fun _ : Ω => (0:ℕ)))
  | succ N ih =>
    have ht : ∀ i,Measurable (fun x => target (w x) (N+1) i) := by
      intro i
      unfold target
      exact Finset.measurable_sum _ (fun t _ => hw t i)
    have hp := measurable_pick (fun x => counts (w x) N) (fun x => target (w x) (N+1)) ih ht
    intro i
    simp only [counts]
    exact (ih i).add (Measurable.ite (measurableSet_eq_fun measurable_const hp) measurable_const measurable_const)

theorem query_measurable [MeasurableSpace T] [MeasurableSingletonClass T]
    (w : Ω → ℕ → T → ℝ) (hw : ∀ t i,Measurable (fun x => w x t i)) (N : ℕ) :
    Measurable (fun x => query (w x) N) := by
  apply measurable_pick
  · exact counts_measurable w hw N
  · intro i
    unfold target
    exact Finset.measurable_sum _ (fun t _ => hw t i)

/-- Equal target histories imply equal next queries. No future targets are read. -/
theorem counts_causal (w v : ℕ → T → ℝ) (N : ℕ)
    (h : ∀ t,t < N → w t=v t) : counts w N=counts v N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hc := ih (fun t ht => h t (by omega))
    have ht : target w (N+1)=target v (N+1) := by
      funext i
      exact sum_congr rfl (fun t hm => congrFun (h t (mem_range.mp hm)) i)
    funext i
    simp only [counts,hc,ht]

theorem query_causal (w v : ℕ → T → ℝ) (N : ℕ)
    (h : ∀ t,t ≤ N → w t=v t) : query w N=query v N := by
  have hc := counts_causal w v N (fun t ht => h t (by omega))
  have ht : target w (N+1)=target v (N+1) := by
    funext i
    exact sum_congr rfl (fun t hm => congrFun (h t (by have := mem_range.mp hm;omega)) i)
  simp only [query,hc,ht]

#print axioms measurable_pick
#print axioms counts_measurable
#print axioms query_measurable
#print axioms query_causal
end
end CIGAMF.P13.FiniteAllocationTrackerMeasurable
