import «LeanPaperCBreakpointV1»

/-!
# Paper C: the path-decomposition debt, discharged at the count states

`PathDecompositionDebt` says every unit flow is induced by a ranking law of the same
objective.  `pathDecomposition_discharged` PROVES it -- given a section `sec` that realises
each positive-mass trajectory as an outcome, and its compatibility `hsec`.  Those two were
the remaining input, and `PROOFS.md` recorded them as the blocker for E1--E3.

They are supplied here, at the state space the reduction actually uses.

* The outcome space is the type sequence itself, `Omega = Fin m -> Fin d`, and the layer map
  is the count state `layerState`, which is exactly the flow's own state.
* `hsec_count_states` already proves the hard half: a trajectory of positive mass that
  starts empty IS the layer map of an explicit type sequence.  `secOf` chooses that
  sequence, and `hsec_secOf` is the compatibility.
* The relabelling group is taken trivial here.  That is the honest choice: this module
  discharges the DEBT, which is about the existence of a ranking law with the same
  occupancies and objective; the uniform relabelling inside each weight type is a separate
  step, proved separately in `LeanPaperCBreakpointV1` and used by `LeanPaperCUniformV1`.

`pathDecomposition_at_count_states` is the composition, and it takes only two conditions on
the flow: that it is supported on legal steps, and that its trajectories start empty.  Both
are properties of the layered flow the LP produces, not of the conclusion.
-/

namespace CIGAMF.P13.PaperCPath

open Finset
open CIGAMF.P13.PaperCBreakpoint

/-- A trivial group, used as the relabelling group when no relabelling is wanted. -/
def NoRelabel : Type := Unit

instance : Group NoRelabel where
  mul := fun _ _ => ()
  one := ()
  inv := fun _ => ()
  mul_assoc := fun _ _ _ => rfl
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl
  inv_mul_cancel := fun _ => rfl

instance : Fintype NoRelabel := Unit.fintype

instance trivAction (α : Type*) : MulAction NoRelabel α where
  smul := fun _ x => x
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

variable {d m : ℕ}

/-! ## The section -/

open scoped Classical in
/-- The section: for a trajectory of positive mass that starts empty, the type sequence
`hsec_count_states` produces; anywhere else, an arbitrary sequence. -/
noncomputable def secOf [NeZero d] (F : LayeredFlow (CState d m))
    (hF : ∀ k v w, ¬ StepC v w → F.f k v w = 0)
    (hstart : ∀ t : Fin (m + 1) → CState d m, F.trajLaw m t ≠ 0 → ∀ τ, ((t 0) τ : ℕ) = 0)
    (t : Fin (m + 1) → CState d m) : Fin m → Fin d :=
  if ht : F.trajLaw m t ≠ 0 then
    Classical.choose (hsec_count_states F hF t ht (hstart t ht))
  else fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩

/-- The layer map at the count states: the state after `i` items is their type count. -/
noncomputable def layerAt (i : Fin (m + 1)) (s : Fin m → Fin d) : CState d m :=
  layerState s (i : ℕ) (by omega)

open scoped Classical in
/-- **`hsec`, proved.**  On every trajectory of positive mass the section reproduces the
trajectory, layer by layer. -/
theorem hsec_secOf [NeZero d] (F : LayeredFlow (CState d m))
    (hF : ∀ k v w, ¬ StepC v w → F.f k v w = 0)
    (hstart : ∀ t : Fin (m + 1) → CState d m, F.trajLaw m t ≠ 0 → ∀ τ, ((t 0) τ : ℕ) = 0)
    (t : Fin (m + 1) → CState d m) (ht : F.trajLaw m t ≠ 0) (i : Fin (m + 1)) :
    layerAt i (secOf F hF hstart t) = t i := by
  have hspec := Classical.choose_spec (hsec_count_states F hF t ht (hstart t ht))
  unfold secOf layerAt
  rw [dif_pos ht]
  have h := hspec (i : ℕ) (by omega)
  rw [h]

/-! ## The debt -/

open scoped Classical in
/-- **(E1--E3) The path-decomposition debt, discharged at the count states.**  Every unit
flow supported on legal steps whose trajectories start empty is induced by a ranking law
with the same layer occupancies and the same linear objective.  The two hypotheses are
properties of the flow; nothing about the conclusion is assumed. -/
theorem pathDecomposition_at_count_states [NeZero d] (F : LayeredFlow (CState d m))
    (hF : ∀ k v w, ¬ StepC v w → F.f k v w = 0)
    (hstart : ∀ t : Fin (m + 1) → CState d m, F.trajLaw m t ≠ 0 → ∀ τ, ((t 0) τ : ℕ) = 0)
    (c : Fin (m + 1) → CState d m → ℝ)
    (h0 : ∑ v, F.x 0 v = 1) (hcons : ∀ j, ∑ v, F.x (j + 1) v = ∑ v, F.x j v) :
    ∃ P : (Fin m → Fin d) → ℝ,
      (∀ ω, 0 ≤ P ω) ∧ (∑ ω, P ω = 1) ∧
      (∀ (i : Fin (m + 1)) (v : CState d m),
        ∑ ω, P ω * (if layerAt i ω = v then (1 : ℝ) else 0) = F.x (i : ℕ) v) ∧
      (∑ ω, P ω * (∑ i : Fin (m + 1), c i (layerAt i ω))
        = ∑ i : Fin (m + 1), ∑ v : CState d m, c i v * F.x (i : ℕ) v) := by
  classical
  refine ⟨flowRanking NoRelabel m F (secOf F hF hstart), ?_, ?_, ?_, ?_⟩
  · exact fun ω => flowRanking_nonneg NoRelabel m F (secOf F hF hstart) ω
  · exact flowRanking_sum NoRelabel m F (secOf F hF hstart) h0 hcons
  · exact fun i v => flowRanking_marginal NoRelabel m F layerAt (fun _ _ _ => rfl)
      (secOf F hF hstart) (fun t ht i => hsec_secOf F hF hstart t ht i) i v
  · exact linear_objective_from_marginals m F layerAt
      (flowRanking NoRelabel m F (secOf F hF hstart)) c
      (fun i v => flowRanking_marginal NoRelabel m F layerAt (fun _ _ _ => rfl)
        (secOf F hF hstart) (fun t ht i => hsec_secOf F hF hstart t ht i) i v)

/-! ## Audit -/

#print axioms hsec_secOf
#print axioms pathDecomposition_at_count_states

end CIGAMF.P13.PaperCPath
