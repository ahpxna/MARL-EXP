import «LeanPaperASacrificeDiluteV1»

/-!
# Paper A: the sacrifice law for policies that stop almost surely

`sacrifice_cost_law` (`LeanPaperASacrificeV1`) is stated for finite-horizon policies.  This module
extends it to every randomised adaptive policy with a measurable stopping rule that stops almost
surely at the truth, with no bound on the stopping time.

* `CorrectA S delta`: the stopping policy `S` (answer `true` = answer `A`) stops almost surely at
  `theta_C`, errs at `theta_C` with probability at most `delta` on the stopped runs at every
  horizon, and answers `A` at a strict alternative with probability at most `delta` at every
  horizon.  No uniform stopping over the alternatives is needed: an unstopped run answers `false`.
* `outT_unfired`: before the stop the truncated output is the default.
* `trunc_A`: at a horizon where at most `delta` of the truth's runs are unstopped, the truncation's
  answer event has probability `>= 1 - 2 delta` at the truth and `<= delta` at every strict
  alternative.
* `expCntSt`: the unbounded run's expected counts, the supremum over horizons (monotone).
* **`sacrifice_law_stopped`**: `N * sacrifice(wbar) >= 8 r M D(2 delta)` for the unbounded run's
  expected counts, whenever they are finite.
* `correctA_ofFinite`: a finite-horizon policy correct at level `delta` is `CorrectA`, so the
  hypotheses are satisfiable (with `sacrifice_hypotheses_satisfiable`).
-/

namespace CIGAMF.P13.PaperASacrificeStopped

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy
open CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperAActualDecisionBridge CIGAMF.P13.PaperAStrict
open CIGAMF.P13.PaperACentred CIGAMF.P13.PaperARPair CIGAMF.P13.PaperAGaussianKL
open CIGAMF.P13.PaperAFamilyLower CIGAMF.P13.PaperAFrontier CIGAMF.P13.PaperASacrifice
open CIGAMF.P13.PaperBStoppedLaw

variable {r : ℕ}

/-- The truncated answer: `true` means answer `A`. -/
noncomputable def ansT (S : SPolicy (Cell r ⊕ Unit) Bool) (n : ℕ) : Hist (Cell r ⊕ Unit) n → Bool :=
  outT S S.out false n

theorem measurableSet_ansT (S : SPolicy (Cell r ⊕ Unit) Bool) (n : ℕ) :
    MeasurableSet {x | ansT S n x = true} :=
  measurable_outT S S.out S.out_meas false n (measurableSet_singleton true)

/-- **Before the stop the truncated output is the default.** -/
theorem outT_unfired {Q A : Type*} [MeasurableSpace Q] [MeasurableSpace A] (S : SPolicy Q A)
    (f : ∀ n, Hist Q n → A) (a0 : A) :
    ∀ n (x : Hist Q n), ¬ fired S n x → outT S f a0 n x = a0
  | 0, x, hx => by
      classical
      show (if x ∈ S.stop 0 then f 0 x else a0) = a0
      rw [if_neg]
      intro hs
      exact hx ⟨0, le_rfl, by rw [hRestr_self]; exact hs⟩
  | n + 1, x, hx => by
      classical
      show (if fired S n (hRestr n (Nat.le_succ n) x) then
          outT S f a0 n (hRestr n (Nat.le_succ n) x)
        else if x ∈ S.stop (n + 1) then f (n + 1) x else a0) = a0
      have h1 : ¬ fired S n (hRestr n (Nat.le_succ n) x) := by
        rintro ⟨j, hj, hs⟩
        exact hx ⟨j, hj.trans (Nat.le_succ n), by rwa [hRestr_hRestr] at hs⟩
      have h2 : x ∉ S.stop (n + 1) := fun hs => hx ⟨n + 1, le_rfl, by rw [hRestr_self]; exact hs⟩
      rw [if_neg h1, if_neg h2]

/-- **Correctness of a stopping policy for the compression decision.** -/
def CorrectA (M : ℝ) (hM : 0 < M) (δ : ℝ) (S : SPolicy (Cell r ⊕ Unit) Bool) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ n, hist (famChan M hM) (stoppedPol S (famChan M hM).dummy)
      (lift (thetaC r)) n {x | ¬ fired S n x} ≤ ENNReal.ofReal ε)
  ∧ (∀ n, hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n
      {x | fired S n x ∧ ansT S n x ≠ true} ≤ ENNReal.ofReal δ)
  ∧ ∀ n, ∀ lam ∈ TrueAltStrict r, hist (famChan M hM) (stoppedPol S (famChan M hM).dummy)
      (lift lam) n {x | fired S n x ∧ ansT S n x = true} ≤ ENNReal.ofReal δ

/-- **The truncation is correct at level `2 delta`.** -/
theorem trunc_A (M : ℝ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ) (S : SPolicy (Cell r ⊕ Unit) Bool)
    (hS : CorrectA M hM δ S) :
    ∃ n, 1 - 2 * δ ≤ (hist (famChan M hM) (stoppedPol S (famChan M hM).dummy)
        (lift (thetaC r)) n).real {x | ansT S n x = true}
      ∧ ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) (stoppedPol S (famChan M hM).dummy)
        (lift lam) n).real {x | ansT S n x = true} ≤ 2 * δ := by
  obtain ⟨n, hn⟩ := hS.1 δ hδ
  refine ⟨n, ?_, fun lam hlam => ?_⟩
  · haveI := hist_prob (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n
    refine good_of_bad _ _ (measurableSet_ansT S n) (2 * δ) (by linarith) ?_
    set μ := hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n
    have hsub : {x | ansT S n x = true}ᶜ
        ⊆ {x | fired S n x ∧ ansT S n x ≠ true} ∪ {x | ¬ fired S n x} := by
      intro x hx
      by_cases hf : fired S n x
      · exact Or.inl ⟨hf, hx⟩
      · exact Or.inr hf
    calc μ {x | ansT S n x = true}ᶜ
        ≤ μ ({x | fired S n x ∧ ansT S n x ≠ true} ∪ {x | ¬ fired S n x}) := measure_mono hsub
      _ ≤ μ {x | fired S n x ∧ ansT S n x ≠ true} + μ {x | ¬ fired S n x} := measure_union_le _ _
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := add_le_add (hS.2.1 n) hn
      _ = ENNReal.ofReal (2 * δ) := by rw [← ENNReal.ofReal_add hδ.le hδ.le]; ring_nf
  · haveI := hist_prob (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift lam) n
    have hsub : {x | ansT S n x = true} ⊆ {x | fired S n x ∧ ansT S n x = true} := by
      intro x hx
      by_cases hf : fired S n x
      · exact ⟨hf, hx⟩
      · exfalso
        have := outT_unfired S S.out false n x hf
        simp only [Set.mem_setOf_eq, ansT] at hx
        rw [this] at hx
        exact Bool.false_ne_true hx
    have h1 := (measure_mono hsub).trans (hS.2.2 n lam hlam)
    have h2 : (hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift lam) n).real
        {x | ansT S n x = true} ≤ δ := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hδ.le h1
    linarith

/-- The unbounded run's expected counts, as the supremum over horizons. -/
noncomputable def expCntSt (M : ℝ) (hM : 0 < M) (S : SPolicy (Cell r ⊕ Unit) Bool) (e : Cell r) :
    ℝ≥0∞ :=
  ⨆ n, ∫⁻ ω, cntQ (Sum.inl e) n ω
    ∂hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n

theorem expCnt_le_St (M : ℝ) (hM : 0 < M) (S : SPolicy (Cell r ⊕ Unit) Bool) (n : ℕ) (e : Cell r)
    (hfin : expCntSt M hM S e ≠ ⊤) :
    expCnt M hM (stoppedPol S (famChan M hM).dummy) n e ≤ (expCntSt M hM S e).toReal := by
  unfold expCnt
  exact ENNReal.toReal_mono hfin (le_iSup (fun k => ∫⁻ ω, cntQ (Sum.inl e) k ω
    ∂hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) k) n)

/-- **The sacrifice law for policies that stop almost surely.**  For the unbounded run's expected
counts `N_e` (finite), `N = sum N_e` and `wbar = N_./N`: `N * sacrifice(wbar) >= 8 r M D(2 delta)`. -/
theorem sacrifice_law_stopped [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ)
    (h2δ : 2 * δ ≤ 1) (S : SPolicy (Cell r ⊕ Unit) Bool) (hS : CorrectA M hM δ S)
    (hD : 0 < demand (2 * δ)) (hfin : ∀ e, expCntSt M hM S e ≠ ⊤) :
    0 < ∑ e, (expCntSt M hM S e).toReal
      ∧ IsAlloc (fun e => (expCntSt M hM S e).toReal / ∑ e', (expCntSt M hM S e').toReal)
      ∧ 8 * (r : ℝ) * M * demand (2 * δ)
          ≤ (∑ e, (expCntSt M hM S e).toReal)
            * sacrifice M (fun e => (expCntSt M hM S e).toReal
                / ∑ e', (expCntSt M hM S e').toReal) := by
  classical
  obtain ⟨n, hθ, hl⟩ := trunc_A M hM δ hδ S hS
  have hmid := middle_demand M hM (stoppedPol S (famChan M hM).dummy) n _ (measurableSet_ansT S n)
    (2 * δ) (by linarith) h2δ hθ hl hD.le
  set c : Cell r → ℝ := fun e => (expCntSt M hM S e).toReal with hc
  set N := ∑ e, c e with hN
  have hmidc : 8 * (r : ℝ) * M * demand (2 * δ) ≤ ∑ p : Fin r × Bool, c (Sum.inr p) :=
    hmid.trans (Finset.sum_le_sum fun p _ => expCnt_le_St M hM S n _ (hfin _))
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmidpos : 0 < ∑ p : Fin r × Bool, c (Sum.inr p) := by
    have : 0 < 8 * (r : ℝ) * M * demand (2 * δ) := by positivity
    linarith
  have hsplit : N = (∑ i : Fin 4, c (Sum.inl i)) + ∑ p : Fin r × Bool, c (Sum.inr p) :=
    Fintype.sum_sum_type _
  have hA : 0 ≤ ∑ i : Fin 4, c (Sum.inl i) :=
    Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  have hNpos : 0 < N := by linarith
  have halloc : IsAlloc (fun e => c e / N) := by
    refine ⟨fun e => div_nonneg ENNReal.toReal_nonneg hNpos.le, ?_⟩
    rw [← Finset.sum_div, div_self hNpos.ne']
  refine ⟨hNpos, halloc, ?_⟩
  have hml := middle_le_sacrifice M hM (fun e => c e / N) halloc
  have hmideq : ∑ p : Fin r × Bool, c (Sum.inr p) / N
      = (∑ p : Fin r × Bool, c (Sum.inr p)) / N := (Finset.sum_div _ _ _).symm
  rw [hmideq, div_le_iff₀ hNpos] at hml
  linarith

/-- **A correct finite-horizon policy is `CorrectA`.**  With the answer read at its horizon, the
embedded stopping policy stops at the horizon and keeps the finite-horizon error bounds. -/
theorem correctA_ofFinite (M : ℝ) (hM : 0 < M) (δ : ℝ) (π : Policy (Cell r ⊕ Unit)) (N : ℕ)
    (f : Hist (Cell r ⊕ Unit) N → Bool) (hf : Measurable f)
    (hθ : hist (famChan M hM) π (lift (thetaC r)) N {x | f x ≠ true} ≤ ENNReal.ofReal δ)
    (hl : ∀ lam ∈ TrueAltStrict r, hist (famChan M hM) π (lift lam) N {x | f x = true}
      ≤ ENNReal.ofReal δ) :
    CorrectA M hM δ (ofFinite π N f hf) := by
  have key : ∀ (w : Cell r ⊕ Unit → ℝ) (n : ℕ) (P : Bool → Prop),
      N ≤ n → hist (famChan M hM) (stoppedPol (ofFinite π N f hf) (famChan M hM).dummy) w n
          {x | fired (ofFinite π N f hf) n x ∧ P (ansT (ofFinite π N f hf) n x)}
        ≤ hist (famChan M hM) π w N {x | P (f x)} := by
    intro w n P hn
    have hsub : {x | fired (ofFinite π N f hf) n x ∧ P (ansT (ofFinite π N f hf) n x)}
        ⊆ (hRestr N hn) ⁻¹' {y | P (f y)} := by
      intro x hx
      have := hx.2
      unfold ansT at this
      rw [outT_ofFinite π N f hf false n hn x] at this
      exact this
    refine (measure_mono hsub).trans ?_
    refine (Measure.le_map_apply (measurable_hRestr N hn).aemeasurable _).trans ?_
    obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
    rw [hist_map_restr (famChan M hM) _ w N k,
      hist_congr (famChan M hM) _ _ w N fun j hj => step_ofFinite_lt π N f hf _ j hj]
  have early : ∀ (w : Cell r ⊕ Unit → ℝ) (n : ℕ) (P : Bool → Prop), n < N →
      hist (famChan M hM) (stoppedPol (ofFinite π N f hf) (famChan M hM).dummy) w n
          {x | fired (ofFinite π N f hf) n x ∧ P (ansT (ofFinite π N f hf) n x)} = 0 := by
    intro w n P hn
    have : {x | fired (ofFinite π N f hf) n x ∧ P (ansT (ofFinite π N f hf) n x)} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hfx
      exact absurd ((fired_ofFinite π N f hf n x).mp hfx) (by omega)
    rw [this, measure_empty]
  refine ⟨fun ε _ => ⟨N, ?_⟩, fun n => ?_, fun n lam hlam => ?_⟩
  · have : {x : Hist (Cell r ⊕ Unit) N | ¬ fired (ofFinite π N f hf) N x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact (fired_ofFinite π N f hf N x).mpr le_rfl
    rw [this, measure_empty]
    exact zero_le
  · rcases lt_or_ge n N with hn | hn
    · rw [early _ n (fun b => b ≠ true) hn]; exact zero_le
    · exact (key _ n (fun b => b ≠ true) hn).trans hθ
  · rcases lt_or_ge n N with hn | hn
    · rw [early _ n (fun b => b = true) hn]; exact zero_le
    · exact (key _ n (fun b => b = true) hn).trans (hl lam hlam)

#print axioms outT_unfired
#print axioms trunc_A
#print axioms sacrifice_law_stopped
#print axioms correctA_ofFinite

end CIGAMF.P13.PaperASacrificeStopped
