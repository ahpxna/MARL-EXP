import Mathlib

/-!
# Paper B: the change of measure on a filtration, for a continuous alphabet

`LeanPaperBTranscriptKLV1` proves the transcript chain rule by summing over every
length-`n` list of observations.  That argument needs a FINITE observation alphabet, and it
says so: the Gaussian observation of the construction has a continuous one.  Replacing the
sum by an integral is not a formality --- the object that carries the argument is the
likelihood ratio on the filtration,

    L_t = dP|_{F_t} / dQ|_{F_t},

and the facts used are that it reproduces `P` against every `F_t`-measurable integrand
(`change_of_measure`), that it is consistent across `t` (`setIntegral_L_succ`), that this
consistency IS the tower property (`condExp_L`), and that the divergence telescopes along
it (`kl_eq_sum_increments`).  None of these needs the alphabet to be finite.

The filtration formulation also makes visible what the list formulation hid: the policy
never appears.  `L_t` is defined from the two measures and the filtration alone, so a
policy that reads the whole past is already covered --- it is part of `F_t`.

The hypothesis `hdens` is the definition of `L`, stated as an equality of trimmed measures
rather than as a pointwise Radon-Nikodym derivative, and with the density in `NNReal`,, because that is the form the integral
lemmas consume.  `L 0 = 1` says the two worlds agree before any observation.
-/

namespace CIGAMF.P13.PaperBChange

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- **The change of measure.**  Against any `F_t`-measurable integrand, `P` is `Q` weighted
by `L t`.  This is the only place `hdens` is used; everything below goes through it. -/
theorem change_of_measure (F : Filtration ℕ m0) (P Q : Measure Ω) (L : ℕ → Ω → ℝ)
    (hLmeas : ∀ t, StronglyMeasurable[F t] (L t)) (hLnn : ∀ t ω, 0 ≤ L t ω)
    (hdens : ∀ t, P.trim (F.le t)
      = (Q.trim (F.le t)).withDensity (fun ω => ((L t ω).toNNReal : ENNReal)))
    (t : ℕ) (f : Ω → ℝ) (hf : StronglyMeasurable[F t] f) :
    ∫ ω, f ω ∂P = ∫ ω, L t ω * f ω ∂Q := by
  have hmeas := (hLmeas t).measurable.real_toNNReal
  have h2 := @integral_withDensity_eq_integral_smul Ω ℝ (F t) (Q.trim (F.le t)) _ _
    (fun ω => (L t ω).toNNReal) hmeas f
  rw [← hdens t] at h2
  have hcoe : ∀ ω, (((L t ω).toNNReal : NNReal) : ℝ) = L t ω :=
    fun ω => Real.coe_toNNReal _ (hLnn t ω)
  simp only [NNReal.smul_def, hcoe, smul_eq_mul] at h2
  have hmul : StronglyMeasurable[F t] (fun ω => L t ω * f ω) := (hLmeas t).mul hf
  rw [integral_trim (F.le t) hf, h2, ← integral_trim (F.le t) hmul]

/-- **Consistency across one step.**  On an `F_t` set the two ratios integrate to the same
thing, because both reproduce `P` there. -/
theorem setIntegral_L_succ (F : Filtration ℕ m0) (P Q : Measure Ω) (L : ℕ → Ω → ℝ)
    (hLmeas : ∀ t, StronglyMeasurable[F t] (L t)) (hLnn : ∀ t ω, 0 ≤ L t ω)
    (hdens : ∀ t, P.trim (F.le t)
      = (Q.trim (F.le t)).withDensity (fun ω => ((L t ω).toNNReal : ENNReal)))
    (t : ℕ) (A : Set Ω) (hA : MeasurableSet[F t] A) :
    ∫ ω in A, L (t + 1) ω ∂Q = ∫ ω in A, L t ω ∂Q := by
  classical
  have hA0 : MeasurableSet A := F.le t A hA
  have hA1 : MeasurableSet[F (t + 1)] A := (F.mono (Nat.le_succ t)) A hA
  have hind : StronglyMeasurable[F t] (Set.indicator A (fun _ => (1 : ℝ))) :=
    (stronglyMeasurable_const).indicator hA
  have hind1 : StronglyMeasurable[F (t + 1)] (Set.indicator A (fun _ => (1 : ℝ))) :=
    (stronglyMeasurable_const).indicator hA1
  have e0 := change_of_measure F P Q L hLmeas hLnn hdens t _ hind
  have e1 := change_of_measure F P Q L hLmeas hLnn hdens (t + 1) _ hind1
  have hrw : ∀ (s : ℕ),
      ∫ ω, L s ω * Set.indicator A (fun _ => (1 : ℝ)) ω ∂Q = ∫ ω in A, L s ω ∂Q := by
    intro s
    have : ∀ ω, L s ω * Set.indicator A (fun _ => (1 : ℝ)) ω
        = Set.indicator A (L s) ω := by
      intro ω
      by_cases hω : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
    rw [funext this, integral_indicator hA0]
  rw [hrw] at e0 e1
  rw [← e1, ← e0]

/-- **The tower property.**  Consistency is exactly the statement that `L t` is the
conditional expectation of `L (t+1)` given the past. -/
theorem condExp_L (F : Filtration ℕ m0) (P Q : Measure Ω) [SigmaFinite (Q.trim (F.le 0))]
    (L : ℕ → Ω → ℝ)
    (hLmeas : ∀ t, StronglyMeasurable[F t] (L t)) (hLnn : ∀ t ω, 0 ≤ L t ω)
    (hdens : ∀ t, P.trim (F.le t)
      = (Q.trim (F.le t)).withDensity (fun ω => ((L t ω).toNNReal : ENNReal)))
    (hLint : ∀ t, Integrable (L t) Q) (t : ℕ) :
    L t =ᵐ[Q] Q[L (t + 1) | F t] := by
  have : SigmaFinite (Q.trim (F.le t)) := by
    have hle : F 0 ≤ F t := F.mono (Nat.zero_le t)
    exact sigmaFiniteTrim_mono (F.le t) hle
  refine ae_eq_condExp_of_forall_setIntegral_eq (F.le t) (hLint (t + 1))
    (fun s hs _ => ((hLint t).integrableOn)) (fun s hs _ => ?_)
    ((hLmeas t).aestronglyMeasurable)
  exact (setIntegral_L_succ F P Q L hLmeas hLnn hdens t s hs).symm

/-! ## The divergence along the filtration -/

/-- The divergence carried by the first `n` observations. -/
noncomputable def klAt (P : Measure Ω) (L : ℕ → Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, Real.log (L n ω) ∂P

/-- One step's contribution. -/
noncomputable def klIncr (P : Measure Ω) (L : ℕ → Ω → ℝ) (t : ℕ) : ℝ :=
  ∫ ω, Real.log (L (t + 1) ω / L t ω) ∂P

/-- **The divergence telescopes along the filtration.**  `KL = E_P log L_N` splits into the
`N` per-step contributions; with `L 0 = 1` there is no boundary term. -/
theorem kl_eq_sum_increments (P : Measure Ω) (L : ℕ → Ω → ℝ)
    (hLpos : ∀ t ω, 0 < L t ω) (hL0 : ∀ ω, L 0 ω = 1)
    (hint : ∀ t, Integrable (fun ω => Real.log (L t ω)) P) (n : ℕ) :
    klAt P L n = ∑ t ∈ Finset.range n, klIncr P L t := by
  induction n with
  | zero => simp [klAt, hL0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold klAt klIncr
    have hsplit : ∀ ω, Real.log (L (k + 1) ω / L k ω)
        = Real.log (L (k + 1) ω) - Real.log (L k ω) :=
      fun ω => Real.log_div (ne_of_gt (hLpos (k + 1) ω)) (ne_of_gt (hLpos k ω))
    rw [funext hsplit, integral_sub (hint (k + 1)) (hint k)]
    ring

/-- **The horizon bound, on a continuous alphabet.**  If no single observation contributes
more than `B`, the first `n` contribute at most `n B`, whatever the policy --- the policy is
inside the filtration and never appears. -/
theorem kl_le_horizon (P : Measure Ω) (L : ℕ → Ω → ℝ)
    (hLpos : ∀ t ω, 0 < L t ω) (hL0 : ∀ ω, L 0 ω = 1)
    (hint : ∀ t, Integrable (fun ω => Real.log (L t ω)) P)
    (B : ℝ) (hB : ∀ t, klIncr P L t ≤ B) (n : ℕ) :
    klAt P L n ≤ (n : ℝ) * B := by
  rw [kl_eq_sum_increments P L hLpos hL0 hint n]
  have h := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range n) => hB t)
  rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h

/-- **The likelihood ratio at time zero is forced.**  If `P` and `Q` agree on `F 0` and both
are probability measures, the ratio starts at one, which is the hypothesis `hL0` above.  It
is recorded so the telescoping is not resting on an arbitrary normalisation. -/
theorem L_zero_of_trivial (F : Filtration ℕ m0) (P Q : Measure Ω) [IsProbabilityMeasure P]
    (L : ℕ → Ω → ℝ)
    (hLmeas : ∀ t, StronglyMeasurable[F t] (L t)) (hLnn : ∀ t ω, 0 ≤ L t ω)
    (hdens : ∀ t, P.trim (F.le t)
      = (Q.trim (F.le t)).withDensity (fun ω => ((L t ω).toNNReal : ENNReal)))
    :
    ∫ ω, L 0 ω ∂Q = 1 := by
  have h := change_of_measure F P Q L hLmeas hLnn hdens 0 (fun _ => (1 : ℝ))
    stronglyMeasurable_const
  simpa using h.symm

/-! ## Audit -/

#print axioms change_of_measure
#print axioms setIntegral_L_succ
#print axioms condExp_L
#print axioms kl_eq_sum_increments
#print axioms kl_le_horizon
#print axioms L_zero_of_trivial

end CIGAMF.P13.PaperBChange
