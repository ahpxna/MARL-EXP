import «LeanPaperBKernelV1»
import «LeanPaperBChiSqV1»

/-!
# Paper B: the adaptive protocol, and the transcript divergence it pays for

A concrete adaptive protocol, on continuous observations, with a randomised policy that is
the SAME kernel in every world:

* a round records `(query, observation)` in `Q × ℝ`; a history of length `n` is
  `Fin n → Q × ℝ`;
* the policy at round `n` is a Markov kernel from the history to the next query -- it may use
  every past observation and its own randomisation, and nothing else: the hidden world is not
  an argument;
* in world `w` the observation of query `q` has density `dens w q` (a `Channel`);
* one query, `dummy`, has the SAME law in every world.  A policy that has stopped keeps
  issuing `dummy`, so a stopped policy is the killed process of the B blueprint, and its cost
  is the number of NON-dummy queries, `tauN`.

The history law is built by recursion, `H(n+1) = ((H n ⊗ₘ policy n) ⊗ₘ obs w n).map snoc`,
not assumed.  `transcript_kl_le` is the adaptive lower bound's information side:

    klDiv (H_theta N) (H_lambda N)  <=  Cmax * E_theta[tauN N],

whenever every non-dummy query's chi-square between the two worlds is at most `Cmax`.  The
proof composes `round_kl_eq` (the policy term cancels), `klDiv_compProd_le_of_pointwise` (the
round's conditional divergence is an average of per-query chi-squares, zero on `dummy`) and a
cost recursion; nothing is taken as a hypothesis about the transcript itself.
-/

namespace CIGAMF.P13.PaperBProtocol

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBKernel CIGAMF.P13.PaperBChiSq

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- A history of length `n`. -/
abbrev Hist (Q : Type*) (n : ℕ) := Fin n → Q × ℝ

/-- **The observation channel**: a density per world and query, and a dummy query that no
world distinguishes. -/
structure Channel (W Q : Type*) where
  dens : W → Q → ℝ → ℝ
  dummy : Q
  meas : ∀ w q, Measurable (dens w q)
  pos : ∀ w q y, 0 < dens w q y
  mass : ∀ w q, ∫⁻ y, ENNReal.ofReal (dens w q y) = 1
  dummy_same : ∀ w w' y, dens w dummy y = dens w' dummy y

/-- **A randomised adaptive policy**: one Markov kernel per round, from the history. -/
structure Policy (Q : Type*) [MeasurableSpace Q] where
  step : ∀ n, Kernel (Hist Q n) Q
  markov : ∀ n, IsMarkovKernel (step n)

/-! ## 1. The kernels and the recursion -/

noncomputable def obsDens (C : Channel W Q) (w : W) (n : ℕ) :
    Hist Q n × Q → ℝ → ℝ≥0∞ :=
  fun x y => ENNReal.ofReal (C.dens w x.2 y)

theorem measurable_obsDens (C : Channel W Q) (w : W) (n : ℕ) :
    Measurable (Function.uncurry (obsDens C w n)) := by
  have h : Measurable fun p : Q × ℝ => ENNReal.ofReal (C.dens w p.1 p.2) := by
    exact measurable_from_prod_countable_right fun q =>
      ENNReal.measurable_ofReal.comp (C.meas w q)
  exact h.comp ((measurable_fst.snd).prodMk measurable_snd)

/-- The observation kernel of world `w` at round `n`. -/
noncomputable def obsKernel (C : Channel W Q) (w : W) (n : ℕ) : Kernel (Hist Q n × Q) ℝ :=
  densKernel volume (obsDens C w n)

theorem obsKernel_markov (C : Channel W Q) (w : W) (n : ℕ) :
    IsMarkovKernel (obsKernel C w n) := by
  haveI : IsSFiniteKernel (obsKernel C w n) :=
    densKernel_sfinite volume _ (fun x y => ENNReal.ofReal_ne_top)
  refine ⟨fun x => ⟨?_⟩⟩
  unfold obsKernel densKernel
  rw [Kernel.withDensity_apply _ (measurable_obsDens C w n), Kernel.const_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact C.mass w x.2

/-- Appending a round to a history. -/
def snocMap (n : ℕ) : (Hist Q n × Q) × ℝ → Hist Q (n + 1) :=
  fun p => Fin.snoc (α := fun _ => Q × ℝ) p.1.1 (p.1.2, p.2)

theorem measurable_snocMap (n : ℕ) : Measurable (snocMap (Q := Q) n) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  refine Fin.lastCases (motive := fun i => Measurable fun p => snocMap (Q := Q) n p i) ?_
    (fun j => ?_) i
  · simp only [snocMap, Fin.snoc_last]
    exact (measurable_fst.snd).prodMk measurable_snd
  · simp only [snocMap, Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst.fst

/-- **The history law of policy `pi` in world `w`**, round by round. -/
noncomputable def hist (C : Channel W Q) (π : Policy Q) (w : W) : ∀ n, Measure (Hist Q n)
  | 0 => Measure.dirac (fun i => i.elim0)
  | n + 1 =>
      haveI := π.markov n
      haveI := obsKernel_markov C w n
      (((hist C π w n) ⊗ₘ π.step n) ⊗ₘ obsKernel C w n).map (snocMap n)

theorem hist_prob (C : Channel W Q) (π : Policy Q) (w : W) :
    ∀ n, IsProbabilityMeasure (hist C π w n)
  | 0 => by unfold hist; infer_instance
  | n + 1 => by
      haveI := hist_prob C π w n
      haveI := π.markov n
      haveI := obsKernel_markov C w n
      unfold hist
      exact (Measure.isProbabilityMeasure_map_iff (measurable_snocMap n).aemeasurable).mpr
        inferInstance

/-! ## 2. The cost: non-dummy queries -/

/-- The number of non-dummy queries in a history. -/
noncomputable def tauN (dummy : Q) (n : ℕ) (ω : Hist Q n) : ℕ :=
  ∑ i : Fin n, if (ω i).1 = dummy then 0 else 1

theorem tauN_snoc (dummy : Q) (n : ℕ) (p : (Hist Q n × Q) × ℝ) :
    tauN dummy (n + 1) (snocMap n p) = tauN dummy n p.1.1 + if p.1.2 = dummy then 0 else 1 := by
  unfold tauN snocMap
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem measurable_tauN (dummy : Q) (n : ℕ) : Measurable (tauN (Q := Q) dummy n) := by
  unfold tauN
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_singleton dummy)

/-- The expected cost of the first `n` rounds. -/
noncomputable def costN (C : Channel W Q) (π : Policy Q) (w : W) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (tauN C.dummy n ω : ℝ≥0∞) ∂hist C π w n

/-- Integrating out a Markov kernel leaves a function of the first coordinate alone. -/
theorem lintegral_compProd_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] {f : α → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ z, f z.1 ∂(μ ⊗ₘ κ) = ∫⁻ x, f x ∂μ := by
  rw [Measure.lintegral_compProd (f := fun z => f z.1) (hf.comp measurable_fst)]
  simp

theorem measurable_tauN_ennreal (dummy : Q) (n : ℕ) :
    Measurable fun ω : Hist Q n => (tauN dummy n ω : ℝ≥0∞) :=
  (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ≥0∞))).comp (measurable_tauN dummy n)

theorem measurableSet_active (dummy : Q) (n : ℕ) :
    MeasurableSet {x : Hist Q n × Q | x.2 ≠ dummy} :=
  (measurable_snd (measurableSet_singleton dummy)).compl

/-- **The cost recursion**: round `n` costs the mass of histories that query non-dummy. -/
theorem costN_succ (C : Channel W Q) (π : Policy Q) (w : W) (n : ℕ) :
    costN C π w (n + 1) = costN C π w n
      + ((hist C π w n) ⊗ₘ π.step n) {x | x.2 ≠ C.dummy} := by
  haveI := hist_prob C π w n
  haveI := π.markov n
  haveI := obsKernel_markov C w n
  have hind : ∀ x : Hist Q n × Q, ((if x.2 = C.dummy then 0 else 1 : ℕ) : ℝ≥0∞)
      = {x : Hist Q n × Q | x.2 ≠ C.dummy}.indicator 1 x := by
    intro x
    by_cases hx : x.2 = C.dummy
    · simp [hx]
    · simp [hx]
  have hmf : Measurable fun x : Hist Q n × Q =>
      (tauN C.dummy n x.1 : ℝ≥0∞) + ((if x.2 = C.dummy then 0 else 1 : ℕ) : ℝ≥0∞) := by
    refine ((measurable_tauN_ennreal C.dummy n).comp measurable_fst).add ?_
    simp_rw [hind]
    exact measurable_one.indicator (measurableSet_active C.dummy n)
  unfold costN
  simp only [hist]
  rw [lintegral_map (measurable_tauN_ennreal C.dummy (n + 1)) (measurable_snocMap n)]
  simp_rw [tauN_snoc, Nat.cast_add]
  rw [lintegral_compProd_fst _ _ hmf,
    lintegral_add_left (f := fun x : Hist Q n × Q => (tauN C.dummy n x.1 : ℝ≥0∞))
      ((measurable_tauN_ennreal C.dummy n).comp measurable_fst),
    lintegral_compProd_fst _ _ (measurable_tauN_ennreal C.dummy n)]
  congr 1
  simp_rw [hind]
  exact lintegral_indicator_one (measurableSet_active C.dummy n)

/-! ## 3. The information: per-query chi-squares, zero on the dummy -/

/-- The chi-square of query `q` between two worlds' observation laws. -/
noncomputable def chi (C : Channel W Q) (θ l : W) (q : Q) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal ((C.dens θ q y - C.dens l q y) ^ 2 / C.dens l q y)

theorem chi_dummy (C : Channel W Q) (θ l : W) : chi C θ l C.dummy = 0 := by
  unfold chi
  simp [C.dummy_same θ l]

/-- **One round of the killed protocol costs at most its active mass times `Cmax`.** -/
theorem kl_succ (C : Channel W Q) (π : Policy Q) (θ l : W) (n : ℕ) :
    klDiv (hist C π θ (n + 1)) (hist C π l (n + 1))
      ≤ klDiv (hist C π θ n) (hist C π l n)
        + ∫⁻ x, chi C θ l x.2 ∂((hist C π θ n) ⊗ₘ π.step n) := by
  haveI := hist_prob C π θ n
  haveI := hist_prob C π l n
  haveI := π.markov n
  haveI := obsKernel_markov C θ n
  haveI := obsKernel_markov C l n
  simp only [hist]
  calc klDiv ((((hist C π θ n) ⊗ₘ π.step n) ⊗ₘ obsKernel C θ n).map (snocMap n))
        ((((hist C π l n) ⊗ₘ π.step n) ⊗ₘ obsKernel C l n).map (snocMap n))
      ≤ klDiv (((hist C π θ n) ⊗ₘ π.step n) ⊗ₘ obsKernel C θ n)
          (((hist C π l n) ⊗ₘ π.step n) ⊗ₘ obsKernel C l n) :=
        klDiv_map_le _ _ (measurable_snocMap n)
    _ = klDiv (hist C π θ n) (hist C π l n)
          + klDiv (((hist C π θ n) ⊗ₘ π.step n) ⊗ₘ obsKernel C θ n)
              (((hist C π θ n) ⊗ₘ π.step n) ⊗ₘ obsKernel C l n) :=
        round_kl_eq _ _ _ _ _
    _ ≤ klDiv (hist C π θ n) (hist C π l n)
          + ∫⁻ x, chi C θ l x.2 ∂((hist C π θ n) ⊗ₘ π.step n) := by
        refine add_le_add le_rfl ?_
        refine klDiv_compProd_le_of_pointwise _ volume (obsDens C θ n) (obsDens C l n)
          (measurable_obsDens C θ n) (measurable_obsDens C l n)
          (fun _ _ => ENNReal.ofReal_ne_top)
          (fun x y => (ENNReal.ofReal_pos.mpr (C.pos l x.2 y)).ne')
          (fun _ _ => ENNReal.ofReal_ne_top)
          (fun x => C.mass θ x.2) (fun x => C.mass l x.2) (fun x => chi C θ l x.2) ?_
        intro x
        refine le_of_eq (lintegral_congr fun y => ?_)
        simp only [obsDens]
        rw [ENNReal.toReal_ofReal (C.pos θ x.2 y).le, ENNReal.toReal_ofReal (C.pos l x.2 y).le]

/-- **The transcript divergence is at most `Cmax` times the expected number of non-dummy
queries**, for every randomised adaptive policy and every horizon. -/
theorem transcript_kl_le (C : Channel W Q) (π : Policy Q) (θ l : W) (Cmax : ℝ≥0∞)
    (hchi : ∀ q, q ≠ C.dummy → chi C θ l q ≤ Cmax) :
    ∀ n, klDiv (hist C π θ n) (hist C π l n) ≤ Cmax * costN C π θ n
  | 0 => by
      haveI := hist_prob C π l 0
      have : hist C π θ 0 = hist C π l 0 := rfl
      rw [this, klDiv_self]
      exact bot_le
  | n + 1 => by
      haveI := hist_prob C π θ n
      haveI := π.markov n
      have hround : ∫⁻ x, chi C θ l x.2 ∂((hist C π θ n) ⊗ₘ π.step n)
          ≤ Cmax * ((hist C π θ n) ⊗ₘ π.step n) {x | x.2 ≠ C.dummy} := by
        rw [← lintegral_indicator_one (measurableSet_active C.dummy n),
          ← lintegral_const_mul _ (measurable_one.indicator (measurableSet_active C.dummy n))]
        refine lintegral_mono fun x => ?_
        by_cases hx : x.2 = C.dummy
        · rw [hx, chi_dummy]
          exact bot_le
        · have hmem : x ∈ {x : Hist Q n × Q | x.2 ≠ C.dummy} := hx
          rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
          exact hchi x.2 hx
      calc klDiv (hist C π θ (n + 1)) (hist C π l (n + 1))
          ≤ klDiv (hist C π θ n) (hist C π l n)
              + ∫⁻ x, chi C θ l x.2 ∂((hist C π θ n) ⊗ₘ π.step n) := kl_succ C π θ l n
        _ ≤ Cmax * costN C π θ n
              + Cmax * ((hist C π θ n) ⊗ₘ π.step n) {x | x.2 ≠ C.dummy} :=
            add_le_add (transcript_kl_le C π θ l Cmax hchi n) hround
        _ = Cmax * costN C π θ (n + 1) := by rw [costN_succ, mul_add]

#print axioms measurable_snocMap
#print axioms hist_prob
#print axioms costN_succ
#print axioms kl_succ
#print axioms transcript_kl_le

end CIGAMF.P13.PaperBProtocol
