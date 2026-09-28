import Mathlib
import «LeanPaperBPrivateQueryV1»
import «LeanMarlEstimatedRevisionV1»

/-!
# T2 of MARL_FINAL_SCOPE_20260927: what it costs to LEARN an acceptable revision

The frontier (`LeanMarlSubsetFrontierV1`, `LeanMarlEstimatedRevisionV1`) says a good repair
exists and bounds its value.  It says nothing about how much calibration is needed to FIND
one.  This module answers that on one explicitly stated model class, with a lower bound and a
constructive upper bound on the SAME query access.

## The model

* Messages `Fin m`; the prepared priority commits the prefix `P`, `|P| = k`; `R` legal
  replacements; reachable family `F_R(P) = {S : |S| = k, |S \ P| ≤ R}` (`Reach`).
* First-order gains `g` are known.  The unknown is the interaction.  A world is a mean vector
  `μ` over broadcast sets; the value of broadcasting `S` is `val g μ S = Σ_S g + μ(S)`.
* The class: the null world `μ = 0` (no interaction) and, for every reachable `T ≠ P`, the
  needle world `needle β T` (interaction `β` on `T` only).  Every needle world satisfies the
  local-interaction hypothesis with `δ = |β|` (`needle_local`), so every lower bound here is a
  lower bound for the local-interaction class of the frontier theorems.
* Query access (`rChan P`): one calibration rollout broadcasts ANY set `S` and observes its
  excess `μ(S)` with unit Gaussian noise (paired against the known first-order part).
  Broadcasting `P` is the free dummy: its excess is `0` in every world.  Singleton and
  first-order "importance" rollouts are queries of this channel like any other.
* Output: a reachable set.  It is acceptable in world `μ` (`Acc`) when it is within `ε` of
  every reachable set.

`defc g P S = σ_g(P \ S) − σ_g(S \ P)` is the first-order deficit.  The ambiguous repairs are

    Amb = {T ∈ F_R(P), T ≠ P : ε < defc T < β − ε}.

## WHAT IS PROVED

* `per_repair_lower` — every protocol that is acceptable with probability `1 − α` at the null
  world and at the needle world of `T ∈ Amb` spends, at the null world, at least
  `((1 − α) log(1/α) − log 2)/(β²/2)` expected rollouts ON `T` ITSELF.  Rollouts on any
  other set count for nothing toward `T`.
* `calibration_lower` — summing: `|Amb| · ((1−α)log(1/α) − log 2) ≤ E_0[#rollouts] · β²/2`.
* `zero_allocation_impossible` — the A-role statement, as a theorem: a protocol that never
  broadcasts some ambiguous repair (for instance one that calibrates only singleton
  importances) cannot be acceptable once `(1−α)log(1/α) > log 2`.
* `calibration_upper` — the matching construction on the same channel.  When every reachable
  `T ≠ P` has first-order deficit above `ε` (`hSep`), block likelihood-ratio tests on the
  ambiguous repairs only, `⌈8 log(|Amb|/α)/β²⌉` rollouts each, are acceptable with probability
  `1 − α` at EVERY world of the class, and cost `|Amb| · ⌈8 log(|Amb|/α)/β²⌉` rollouts.
  Lower and upper agree up to the factor `log |Amb|`.
* `amb_empty_R0`, `amb_mono`, `amb_empty_of_margin` — no rights, no calibration; more rights,
  more ambiguity; a first-order cut margin `γ ≥ β − ε` empties `Amb` (the calibration
  analogue of `subset_zero_price`: the certificate that makes revision unnecessary also makes
  calibration unnecessary).
* `amb_card_ge_gap` — on the uniform-gap instance (`g = γ·1_P`, `ε < γ`, `γR < β − ε`)
  `|Amb| ≥ C(k,R)·C(m−k,R)`.  READ WITH CARE: the class (needles within reach `R`) and the
  target (within `ε` of the best set in `F_R`) both change with `R`, so this compares
  DIFFERENT problems.  It is NOT a theorem that more rights need more data on a fixed
  problem; with a fixed world class and an absolute target, extra rights can always be
  left unused.
* `geometric_floor` — in a needle world beyond reach (`|T \ P| > R`) every legal output loses
  at least `β − defc T`, whatever the data.  With `calibration_lower` this is the two-cost law
  on one model: rights bound the floor, data bound which rights are usable.
* `calibration_satisfiable` — the lower bound's hypotheses are met by the constructed protocol
  on a concrete instance with `|Amb| ≥ 4` and a strictly positive bound.

## WHAT THIS DOES NOT ESTABLISH

- The class is the needle class: one interaction on one set.  For richer interaction
  structure (pairwise interactions shared across repairs) the counting changes; that bound is
  not proved here.
- Gains `g` are known.  Estimated gains enter through `LeanMarlEstimatedRevisionV1`; the joint
  learning of gains and interactions is not treated.
- The upper bound needs `hSep` (no reachable near-tie with `P` at first order); near-ties are
  acceptable at the null world and the lower bound says nothing about them.
- `log |Amb|` separates the bounds.  No claim of exact constants.
- Nothing here is about traffic.  Whether learned traffic values look like this class is an
  empirical question (E2 of the scope).
-/

namespace CIGAMF.P13.MarlRepairCalibration

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperALowerKL
open CIGAMF.P13.PaperBHellingerTest CIGAMF.P13.PaperBSchedule CIGAMF.P13.PaperABridge
open CIGAMF.P13.PaperAFamilyLower CIGAMF.P13.PaperAGaussianKL CIGAMF.P13.PaperBPrivateQuery
open CIGAMF.P13.PaperAStrict
open CIGAMF.P13.MarlSubsetFrontier CIGAMF.P13.MarlEstimatedRevision

variable {m : ℕ}

/-! ## 1. The model -/

/-- Number of broadcast sets. -/
abbrev NQ (m : ℕ) : ℕ := Fintype.card (Finset (Fin m))

/-- A broadcast set as a query index. -/
noncomputable def code (S : Finset (Fin m)) : Fin (NQ m) := Fintype.equivFin (Finset (Fin m)) S

theorem code_inj {S T : Finset (Fin m)} (h : code S = code T) : S = T :=
  (Fintype.equivFin (Finset (Fin m))).injective h

/-- **The calibration channel.**  Query `code S` broadcasts `S` in a paired rollout and observes
the excess of its value over the known first-order part, with unit Gaussian noise; the
prefix `P` is the dummy. -/
noncomputable def rChan (P : Finset (Fin m)) : Channel (Fin (NQ m) → ℝ) (Fin (NQ m)) :=
  gChan (code P) (fun _ => (1 : ℝ)) (fun _ => one_pos)

theorem rChan_dummy (P : Finset (Fin m)) : (rChan P).dummy = code P := rfl

/-- The null world. -/
def null0 : Fin (NQ m) → ℝ := fun _ => 0

/-- The needle world at `T`: interaction `β` on `T` only. -/
noncomputable def needle (β : ℝ) (T : Finset (Fin m)) : Fin (NQ m) → ℝ :=
  fun q => if q = code T then β else 0

/-- The value of broadcasting `S` in world `μ`. -/
noncomputable def val (g : Fin m → ℝ) (μ : Fin (NQ m) → ℝ) (S : Finset (Fin m)) : ℝ :=
  S.sum g + μ (code S)

/-- The first-order deficit of `S` against `P`. -/
def defc (g : Fin m → ℝ) (P S : Finset (Fin m)) : ℝ := (P \ S).sum g - (S \ P).sum g

/-- Acceptable output in world `μ`: reachable, and within `ε` of every reachable set. -/
def Acc (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (ε : ℝ) (μ : Fin (NQ m) → ℝ)
    (S : Finset (Fin m)) : Prop :=
  Reach P k R S ∧ ∀ S', Reach P k R S' → val g μ S' ≤ val g μ S + ε

/-- The ambiguous reachable repairs. -/
noncomputable def Amb (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε : ℝ) :
    Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter fun T => Reach P k R T ∧ T ≠ P ∧ ε < defc g P T ∧ defc g P T < β - ε

theorem mem_Amb {g : Fin m → ℝ} {P : Finset (Fin m)} {k R : ℕ} {β ε : ℝ} {T : Finset (Fin m)} :
    T ∈ Amb g P k R β ε ↔ Reach P k R T ∧ T ≠ P ∧ ε < defc g P T ∧ defc g P T < β - ε := by
  unfold Amb; simp

theorem mz_null (P : Finset (Fin m)) (q : Fin (NQ m)) : mz (code P) (null0 (m := m)) q = 0 := by
  unfold mz null0; split_ifs <;> rfl

theorem mz_needle_self (P T : Finset (Fin m)) (β : ℝ) (hTP : T ≠ P) :
    mz (code P) (needle β T) (code T) = β := by
  unfold mz needle
  rw [if_neg (fun h => hTP (code_inj h)), if_pos rfl]

theorem mz_needle_off (P T S : Finset (Fin m)) (β : ℝ) (hST : S ≠ T) :
    mz (code P) (needle β T) (code S) = 0 := by
  unfold mz needle
  split_ifs with h1 h2
  · rfl
  · exact absurd (code_inj h2) hST
  · rfl

theorem val_null (g : Fin m → ℝ) (S : Finset (Fin m)) : val g null0 S = S.sum g := by
  simp [val, null0]

theorem val_needle (g : Fin m → ℝ) (β : ℝ) (T S : Finset (Fin m)) :
    val g (needle β T) S = S.sum g + if S = T then β else 0 := by
  unfold val needle
  by_cases h : S = T
  · subst h; simp
  · have : code S ≠ code T := fun e => h (code_inj e)
    simp [h, this]

theorem sum_eq_sub_defc (g : Fin m → ℝ) (P S : Finset (Fin m)) :
    S.sum g = P.sum g - defc g P S := by
  unfold defc
  have h : (S \ P).sum g - (P \ S).sum g = S.sum g - P.sum g := by
    rw [Finset.sum_sdiff_sub_sum_sdiff]
  linarith

theorem defc_nonneg (g : Fin m → ℝ) (P S : Finset (Fin m)) (hc : S.card = P.card)
    (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) : 0 ≤ defc g P S := by
  unfold defc
  have hcc : (P \ S).card = (S \ P).card := Finset.card_sdiff_comm hc.symm
  have := sum_le_of_pointwise (P \ S) (S \ P) g hcc
    (fun i hi j hj => hTop i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2)
  linarith

theorem reach_P (P : Finset (Fin m)) (k R : ℕ) (hP : P.card = k) : Reach P k R P :=
  ⟨hP, by simp⟩

/-! ## 2. Who is acceptable where -/

theorem acc_null_P (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (ε : ℝ) (hP : P.card = k)
    (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) (hε : 0 ≤ ε) : Acc g P k R ε null0 P := by
  refine ⟨reach_P P k R hP, fun S' hS' => ?_⟩
  rw [val_null, val_null, sum_eq_sub_defc g P S']
  have := defc_nonneg g P S' (hS'.1.trans hP.symm) hTop
  linarith

theorem not_acc_null (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (ε : ℝ) (hP : P.card = k)
    (T : Finset (Fin m)) (hT : ε < defc g P T) : ¬ Acc g P k R ε null0 T := by
  intro hA
  have := hA.2 P (reach_P P k R hP)
  rw [val_null, val_null, sum_eq_sub_defc g P T] at this
  linarith

theorem acc_needle_unique (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) (T : Finset (Fin m))
    (hT : T ∈ Amb g P k R β ε) (S : Finset (Fin m)) (hS : Acc g P k R ε (needle β T) S) :
    S = T := by
  obtain ⟨hTr, _, _, hTd⟩ := mem_Amb.mp hT
  by_contra hST
  have h1 := hS.2 T hTr
  rw [val_needle, val_needle, if_pos rfl, if_neg hST, sum_eq_sub_defc g P T,
    sum_eq_sub_defc g P S] at h1
  have := defc_nonneg g P S (hS.1.1.trans hP.symm) hTop
  linarith

theorem acc_needle_self (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) (hε : 0 ≤ ε) (T : Finset (Fin m))
    (hT : T ∈ Amb g P k R β ε) : Acc g P k R ε (needle β T) T := by
  obtain ⟨hTr, _, _, hTd⟩ := mem_Amb.mp hT
  refine ⟨hTr, fun S' hS' => ?_⟩
  rw [val_needle, val_needle, if_pos rfl]
  by_cases h : S' = T
  · rw [if_pos h, h]; linarith
  · rw [if_neg h, sum_eq_sub_defc g P S', sum_eq_sub_defc g P T]
    have := defc_nonneg g P S' (hS'.1.trans hP.symm) hTop
    linarith

theorem acc_needle_P (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) (hε : 0 ≤ ε) (T : Finset (Fin m))
    (hTP : T ≠ P) (hTd : β - ε ≤ defc g P T) : Acc g P k R ε (needle β T) P := by
  refine ⟨reach_P P k R hP, fun S' hS' => ?_⟩
  rw [val_needle, val_needle, if_neg (Ne.symm hTP)]
  by_cases h : S' = T
  · rw [if_pos h, h, sum_eq_sub_defc g P T]; linarith
  · rw [if_neg h, sum_eq_sub_defc g P S']
    have := defc_nonneg g P S' (hS'.1.trans hP.symm) hTop
    linarith

/-- Needle worlds satisfy the local-interaction hypothesis of the frontier with `δ = |β|`. -/
theorem needle_local (g : Fin m → ℝ) (β : ℝ) (T : Finset (Fin m)) (hT : 2 ≤ T.card) :
    LocalInteraction (val g (needle β T)) |β| := by
  have hgain : ∀ i, gain (val g (needle β T)) i = g i := by
    intro i
    unfold gain
    rw [val_needle, val_needle]
    have h1 : ({i} : Finset (Fin m)) ≠ T := by
      intro h; rw [← h, Finset.card_singleton] at hT; omega
    have h2 : (∅ : Finset (Fin m)) ≠ T := by
      intro h; rw [← h, Finset.card_empty] at hT; omega
    rw [if_neg h1, if_neg h2]; simp
  intro A i hi
  rw [hgain, val_needle, val_needle, Finset.sum_insert hi, abs_le]
  rcases abs_cases β with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
  · split_ifs <;> constructor <;> linarith

/-! ## 3. The channel's divergences and affinities -/

theorem vq_one (q : Fin (NQ m)) : vq (fun _ : Fin (NQ m) => (1 : ℝ)) q = 1 := by
  apply NNReal.eq
  show (1 : ℝ) ^ 2 = 1
  norm_num

theorem rChan_dens (P : Finset (Fin m)) (μ : Fin (NQ m) → ℝ) (q : Fin (NQ m)) (y : ℝ) :
    (rChan P).dens μ q y = gaussianPDFReal (mz (code P) μ q) 1 y := by
  show gaussianPDFReal (mz (code P) μ q) (vq (fun _ => (1 : ℝ)) q) y = _
  rw [vq_one]

theorem klq_rChan (P : Finset (Fin m)) (μ ν : Fin (NQ m) → ℝ) (q : Fin (NQ m)) :
    klq (rChan P) μ ν q = ENNReal.ofReal ((mz (code P) μ q - mz (code P) ν q) ^ 2 / 2) := by
  unfold klq rChan
  rw [obsLawC_gChan, obsLawC_gChan, vq_one]
  have hne := klDiv_gaussianReal_ne_top (mz (code P) μ q) (mz (code P) ν q) 1 one_ne_zero
  rw [← ENNReal.ofReal_toReal hne, toReal_klDiv_gaussianReal _ _ _ one_ne_zero]
  unfold gaussKL
  norm_num

theorem bc_rChan (P : Finset (Fin m)) (μ ν : Fin (NQ m) → ℝ) (q : Fin (NQ m)) :
    bc (rChan P) μ ν q
      = ENNReal.ofReal (Real.exp (-(mz (code P) μ q - mz (code P) ν q) ^ 2 / 8)) := by
  unfold bc
  have hpt : ∀ y, ENNReal.ofReal (Real.sqrt ((rChan P).dens μ q y * (rChan P).dens ν q y))
      = ENNReal.ofReal (Real.exp (-(mz (code P) μ q - mz (code P) ν q) ^ 2 / 8))
        * ENNReal.ofReal
            (gaussianPDFReal ((mz (code P) μ q + mz (code P) ν q) / 2) 1 y) := by
    intro y
    rw [rChan_dens, rChan_dens, gauss_prod_gen, Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le
      (gaussianPDFReal_nonneg _ _ _)), ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (measurable_gaussianPDFReal _ 1).ennreal_ofReal,
    lintegral_gaussianPDFReal_eq_one _ one_ne_zero, mul_one]

/-- The per-rollout affinity of a separating query. -/
noncomputable def eB (β : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(β ^ 2 / 8)))

theorem eB_le_one (β : ℝ) : eB β ≤ 1 := by
  unfold eB
  rw [ENNReal.ofReal_le_one]
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg β])

theorem bc_sep (P : Finset (Fin m)) (μ ν : Fin (NQ m) → ℝ) (q : Fin (NQ m)) (β : ℝ)
    (h1 : mz (code P) μ q = 0) (h2 : mz (code P) ν q = β) : bc (rChan P) μ ν q = eB β := by
  rw [bc_rChan, h1, h2, eB]; congr 2; ring

theorem bc_sep' (P : Finset (Fin m)) (μ ν : Fin (NQ m) → ℝ) (q : Fin (NQ m)) (β : ℝ)
    (h1 : mz (code P) μ q = β) (h2 : mz (code P) ν q = 0) : bc (rChan P) μ ν q = eB β := by
  rw [bc_rChan, h1, h2, eB]; congr 2; ring

/-! ## 4. The lower bound -/

theorem measurableSet_out_mem (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (A : Set (Finset (Fin m))) :
    MeasurableSet {ω | out ω ∈ A} := by
  have : {ω | out ω ∈ A} = ⋃ S ∈ A, {ω | out ω = S} := by ext ω; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable A) (fun S _ => hmeas S)

/-- **Every ambiguous repair must itself be rolled out.** -/
theorem per_repair_lower (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα1 : α ≤ 1)
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)})
    (T : Finset (Fin m)) (hT : T ∈ Amb g P k R β ε)
    (hcT : 1 - α ≤ (hist (rChan P) pol (needle β T) n).real
      {ω | Acc g P k R ε (needle β T) (out ω)}) :
    ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2)
      ≤ (∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) pol null0 n) * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  obtain ⟨_, hTP, hTe, _⟩ := mem_Amb.mp hT
  haveI := hist_prob (rChan P) pol (needle β T) n
  have hE0m : MeasurableSet {ω | Acc g P k R ε null0 (out ω)} :=
    measurableSet_out_mem n out hmeas {S | Acc g P k R ε null0 S}
  have hETm : MeasurableSet {ω | Acc g P k R ε (needle β T) (out ω)} :=
    measurableSet_out_mem n out hmeas {S | Acc g P k R ε (needle β T) S}
  have hl : (hist (rChan P) pol (needle β T) n).real {ω | Acc g P k R ε null0 (out ω)} ≤ α := by
    have hsub : {ω | Acc g P k R ε null0 (out ω)}
        ⊆ {ω | Acc g P k R ε (needle β T) (out ω)}ᶜ := by
      intro ω hω hω'
      have h1 := acc_needle_unique g P k R β ε hP hTop T hT (out ω) hω'
      have h2 : Acc g P k R ε null0 (out ω) := hω
      rw [h1] at h2
      exact not_acc_null g P k R ε hP T hTe h2
    have := measureReal_mono hsub (measure_ne_top (hist (rChan P) pol (needle β T) n) _)
    rw [measureReal_compl hETm, probReal_univ] at this
    linarith
  have hcm := change_of_measure (rChan P) pol null0 (needle β T) n _ hE0m α hα hα1 h0 hl
  rw [Finset.sum_eq_single (code T)] at hcm
  · rwa [klq_rChan, mz_null, mz_needle_self P T β hTP, zero_sub, neg_sq] at hcm
  · intro q _ hq
    rw [klq_rChan, mz_null]
    have : mz (code P) (needle β T) q = 0 := by simp [mz, needle, hq]
    rw [this]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The calibration lower bound.** -/
theorem calibration_lower (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα1 : α ≤ 1)
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)})
    (hcorr : ∀ T ∈ Amb g P k R β ε, 1 - α ≤ (hist (rChan P) pol (needle β T) n).real
      {ω | Acc g P k R ε (needle β T) (out ω)}) :
    ((Amb g P k R β ε).card : ℝ≥0∞) * ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2)
      ≤ costN (rChan P) pol null0 n * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  set D := ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2) with hD
  set c := ENNReal.ofReal (β ^ 2 / 2) with hc
  set F : Fin (NQ m) → ℝ≥0∞ := fun q => ∫⁻ ω, cntQ q n ω ∂hist (rChan P) pol null0 n with hF
  have hper : ∀ T ∈ Amb g P k R β ε, D ≤ F (code T) * c := fun T hT =>
    per_repair_lower g P k R β ε α hP hTop pol n out hmeas hα hα1 h0 T hT (hcorr T hT)
  calc ((Amb g P k R β ε).card : ℝ≥0∞) * D = ∑ _T ∈ Amb g P k R β ε, D := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ T ∈ Amb g P k R β ε, F (code T) * c := Finset.sum_le_sum hper
    _ = ∑ q ∈ (Amb g P k R β ε).image code, F q * c := by
        rw [Finset.sum_image (fun S _ T _ h => code_inj h)]
    _ ≤ ∑ q ∈ Finset.univ.filter (fun q => q ≠ code P), F q * c := by
        apply Finset.sum_le_sum_of_subset
        intro q hq
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h; exact (mem_Amb.mp hT).2.1 (code_inj h)
    _ = costN (rChan P) pol null0 n * c := by
        rw [costN_eq_sum, Finset.sum_mul, rChan_dummy, Finset.sum_filter]
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases h : q = code P <;> simp [h, hF]

/-- **Zero allocation to an ambiguous repair is fatal.**  In particular a calibration that only
rolls out singleton or first-order importance queries is never acceptable on this class. -/
theorem zero_allocation_impossible (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα1 : α ≤ 1)
    (hDpos : 0 < (1 - α) * Real.log (1 / α) - Real.log 2)
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)})
    (T : Finset (Fin m)) (hT : T ∈ Amb g P k R β ε)
    (hcT : 1 - α ≤ (hist (rChan P) pol (needle β T) n).real
      {ω | Acc g P k R ε (needle β T) (out ω)}) :
    (∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) pol null0 n) ≠ 0 := by
  intro h0'
  have := per_repair_lower g P k R β ε α hP hTop pol n out hmeas hα hα1 h0 T hT hcT
  rw [h0', zero_mul, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  linarith

/-! ## 5. The constructive upper bound -/

section Upper

variable (P : Finset (Fin m)) (A : Finset (Finset (Fin m))) (β : ℝ) (n : ℕ)

/-- Enumeration of the tested repairs. -/
noncomputable def enumA (j : Fin A.card) : Finset (Fin m) := (A.equivFin.symm j : Finset (Fin m))

theorem enumA_mem (j : Fin A.card) : enumA A j ∈ A := (A.equivFin.symm j).2

theorem enumA_inj {i j : Fin A.card} (h : enumA A i = enumA A j) : i = j :=
  A.equivFin.symm.injective (Subtype.ext h)

theorem enumA_equivFin (T : Finset (Fin m)) (hT : T ∈ A) : enumA A (A.equivFin ⟨T, hT⟩) = T := by
  simp [enumA]

/-- Block `j` of rounds rolls out repair `j`, `n` times. -/
noncomputable def rsched (i : ℕ) : Fin (NQ m) :=
  if h : i / n < A.card then code (enumA A ⟨i / n, h⟩) else code P

/-- Round `i` belongs to block `j`. -/
def rblk (j : ℕ) : ℕ → Prop := fun i => i / n = j

instance (j : ℕ) : DecidablePred (rblk n j) := fun i => inferInstanceAs (Decidable (i / n = j))

theorem rsched_block (j : Fin A.card) (i : Fin (A.card * n))
    (hi : i ∈ blockSet (A.card * n) (rblk n j)) : rsched P A n i = code (enumA A j) := by
  have hij : (i : ℕ) / n = j := (Finset.mem_filter.mp hi).2
  have hlt : (i : ℕ) / n < A.card := by rw [hij]; exact j.isLt
  unfold rsched
  rw [dif_pos hlt, show (⟨(i : ℕ) / n, hlt⟩ : Fin A.card) = j from Fin.ext hij]

theorem rcard_block (j : Fin A.card) : n ≤ (blockSet (A.card * n) (rblk n j)).card := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · omega
  have hmap : ∀ t : Fin n, (j : ℕ) * n + t < A.card * n := by
    intro t
    have h1 : ((j : ℕ) + 1) * n ≤ A.card * n := Nat.mul_le_mul_right _ j.isLt
    have := t.isLt
    nlinarith
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n)))
    (t := blockSet (A.card * n) (rblk n j))
    (fun t => (⟨j * n + t, hmap t⟩ : Fin (A.card * n)))
    (by
      intro t _
      rw [Finset.mem_coe]
      unfold blockSet
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show ((j : ℕ) * n + (t : ℕ)) / n = j
      rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt t.isLt, zero_add])
    (by
      intro a _ b _ hab
      have := congrArg Fin.val hab
      simp only at this
      exact Fin.ext (by omega))
  simpa using h

/-- The block likelihood of world `μ` on block `j`. -/
noncomputable def rlik (μ : Fin (NQ m) → ℝ) (j : ℕ) (ω : Hist (Fin (NQ m)) (A.card * n)) : ℝ :=
  ∏ i ∈ blockSet (A.card * n) (rblk n j), (rChan P).dens μ (rsched P A n i) (ω i).2

/-- Test `j` fires when block `j` prefers the needle at repair `j` to the null world. -/
def rfires (j : Fin A.card) (ω : Hist (Fin (NQ m)) (A.card * n)) : Prop :=
  rlik P A n null0 j ω < rlik P A n (needle β (enumA A j)) j ω

theorem measurable_rlik (μ : Fin (NQ m) → ℝ) (j : ℕ) : Measurable (rlik P A n μ j) := by
  unfold rlik
  exact Finset.measurable_prod _ fun i _ =>
    ((rChan P).meas _ _).comp (measurable_snd.comp (measurable_pi_apply i))

theorem measurableSet_rfires (j : Fin A.card) : MeasurableSet {ω | rfires P A β n j ω} :=
  measurableSet_lt (measurable_rlik P A n _ _) (measurable_rlik P A n _ _)

theorem pow_card_le (j : Fin A.card) :
    eB β ^ (blockSet (A.card * n) (rblk n j)).card ≤ eB β ^ n := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (rcard_block A n j)
  rw [hd, pow_add]
  exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (eB_le_one β))

/-- A test fires wrongly with probability at most `e^{-nβ²/8}` in any world where its repair
carries no interaction. -/
theorem rfires_small (hA : ∀ T ∈ A, T ≠ P) (μ : Fin (NQ m) → ℝ) (j : Fin A.card)
    (hμ : mz (code P) μ (code (enumA A j)) = 0) :
    hist (rChan P) (schedPolicy (rsched P A n)) μ (A.card * n) {ω | rfires P A β n j ω}
      ≤ eB β ^ n := by
  have hTP := hA _ (enumA_mem A j)
  have hsub : {ω | rfires P A β n j ω} ⊆
      {ω | ∏ i ∈ blockSet (A.card * n) (rblk n j), (rChan P).dens μ (rsched P A n i) (ω i).2
        ≤ ∏ i ∈ blockSet (A.card * n) (rblk n j),
            (rChan P).dens (needle β (enumA A j)) (rsched P A n i) (ω i).2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    unfold rfires rlik at hω
    have heq : ∏ i ∈ blockSet (A.card * n) (rblk n j), (rChan P).dens null0 (rsched P A n i) (ω i).2
        = ∏ i ∈ blockSet (A.card * n) (rblk n j), (rChan P).dens μ (rsched P A n i) (ω i).2 := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [rsched_block P A n j i hi, rChan_dens, rChan_dens, mz_null, hμ]
    rw [← heq]; exact hω.le
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∏ i ∈ blockSet (A.card * n) (rblk n j),
          bc (rChan P) μ (needle β (enumA A j)) (rsched P A n i) :=
        block_error (rChan P) (rsched P A n) μ (needle β (enumA A j)) (A.card * n) (rblk n j)
    _ = eB β ^ (blockSet (A.card * n) (rblk n j)).card := by
        rw [Finset.prod_congr rfl fun i hi => by rw [rsched_block P A n j i hi], Finset.prod_const,
          bc_sep P μ _ _ β hμ (mz_needle_self P _ β hTP)]
    _ ≤ eB β ^ n := pow_card_le A β n j

/-- A test fails to fire at its own needle with probability at most `e^{-nβ²/8}`. -/
theorem rnofire_small (hA : ∀ T ∈ A, T ≠ P) (j : Fin A.card) :
    hist (rChan P) (schedPolicy (rsched P A n)) (needle β (enumA A j)) (A.card * n)
      {ω | ¬ rfires P A β n j ω} ≤ eB β ^ n := by
  have hTP := hA _ (enumA_mem A j)
  have hsub : {ω | ¬ rfires P A β n j ω} ⊆
      {ω | ∏ i ∈ blockSet (A.card * n) (rblk n j),
            (rChan P).dens (needle β (enumA A j)) (rsched P A n i) (ω i).2
        ≤ ∏ i ∈ blockSet (A.card * n) (rblk n j), (rChan P).dens null0 (rsched P A n i) (ω i).2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    unfold rfires rlik at hω
    exact not_lt.mp hω
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∏ i ∈ blockSet (A.card * n) (rblk n j),
          bc (rChan P) (needle β (enumA A j)) null0 (rsched P A n i) :=
        block_error (rChan P) (rsched P A n) (needle β (enumA A j)) null0 (A.card * n) (rblk n j)
    _ = eB β ^ (blockSet (A.card * n) (rblk n j)).card := by
        rw [Finset.prod_congr rfl fun i hi => by rw [rsched_block P A n j i hi], Finset.prod_const,
          bc_sep' P _ null0 _ β (mz_needle_self P _ β hTP) (mz_null P _)]
    _ ≤ eB β ^ n := pow_card_le A β n j

noncomputable instance rfires_dec (j : Fin A.card) (ω : Hist (Fin (NQ m)) (A.card * n)) :
    Decidable (rfires P A β n j ω) := Classical.dec _

/-- Decode the fired tests: the first fired repair, or the prefix if none fired. -/
noncomputable def rdec (b : Fin A.card → Bool) : Finset (Fin m) :=
  if h : (Finset.univ.filter fun j => b j = true).Nonempty then
    enumA A ((Finset.univ.filter fun j => b j = true).min' h) else P

theorem rdec_none (b : Fin A.card → Bool) (hb : ∀ j, b j = false) : rdec P A b = P := by
  unfold rdec
  rw [dif_neg]
  rintro ⟨j, hj⟩
  simp [hb j] at hj

theorem rdec_single (b : Fin A.card → Bool) (j0 : Fin A.card) (h0 : b j0 = true)
    (hb : ∀ j, j ≠ j0 → b j = false) : rdec P A b = enumA A j0 := by
  unfold rdec
  have hmem : j0 ∈ Finset.univ.filter fun j => b j = true := by simp [h0]
  have hne : (Finset.univ.filter fun j => b j = true).Nonempty := ⟨j0, hmem⟩
  rw [dif_pos hne]
  congr 1
  apply le_antisymm (Finset.min'_le _ _ hmem)
  apply Finset.le_min'
  intro y hy
  have hy' : b y = true := (Finset.mem_filter.mp hy).2
  by_cases hyj : y = j0
  · rw [hyj]
  · rw [hb y hyj] at hy'; exact absurd hy' (by simp)

/-- The protocol's output. -/
noncomputable def rout (ω : Hist (Fin (NQ m)) (A.card * n)) : Finset (Fin m) :=
  rdec P A (fun j => decide (rfires P A β n j ω))

theorem measurable_rvec :
    Measurable (fun ω : Hist (Fin (NQ m)) (A.card * n) => fun j => decide (rfires P A β n j ω)) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_to_countable'
  intro b
  cases b
  · have : (fun ω => decide (rfires P A β n j ω)) ⁻¹' {false} = {ω | rfires P A β n j ω}ᶜ := by
      ext ω; simp
    rw [this]; exact (measurableSet_rfires P A β n j).compl
  · have : (fun ω => decide (rfires P A β n j ω)) ⁻¹' {true} = {ω | rfires P A β n j ω} := by
      ext ω; simp
    rw [this]; exact measurableSet_rfires P A β n j

theorem measurableSet_rout (S : Finset (Fin m)) : MeasurableSet {ω | rout P A β n ω = S} := by
  have : {ω | rout P A β n ω = S}
      = (fun ω : Hist (Fin (NQ m)) (A.card * n) => fun j => decide (rfires P A β n j ω)) ⁻¹'
          {b | rdec P A b = S} := rfl
  rw [this]
  exact measurable_rvec P A β n (Set.toFinite _).measurableSet

theorem rout_of_none (ω : Hist (Fin (NQ m)) (A.card * n)) (h : ∀ j, ¬ rfires P A β n j ω) :
    rout P A β n ω = P :=
  rdec_none P A _ (fun j => by simp [h j])

theorem rout_of_single (ω : Hist (Fin (NQ m)) (A.card * n)) (j0 : Fin A.card)
    (h0 : rfires P A β n j0 ω) (h : ∀ j, j ≠ j0 → ¬ rfires P A β n j ω) :
    rout P A β n ω = enumA A j0 :=
  rdec_single P A _ j0 (by simp [h0]) (fun j hj => by simp [h j hj])

/-- Error at a world where no tested repair carries interaction and `P` is acceptable. -/
theorem err_zero_world (hA : ∀ T ∈ A, T ≠ P) (μ : Fin (NQ m) → ℝ)
    (hμ : ∀ j, mz (code P) μ (code (enumA A j)) = 0) (Acc' : Finset (Fin m) → Prop)
    (hPacc : Acc' P) :
    hist (rChan P) (schedPolicy (rsched P A n)) μ (A.card * n) {ω | Acc' (rout P A β n ω)}ᶜ
      ≤ (A.card : ℝ≥0∞) * eB β ^ n := by
  have hsub : {ω | Acc' (rout P A β n ω)}ᶜ ⊆ ⋃ j, {ω | rfires P A β n j ω} := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_iUnion, not_exists, Set.mem_setOf_eq] at hno
    apply hω
    show Acc' (rout P A β n ω)
    rw [rout_of_none P A β n ω hno]; exact hPacc
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ j, hist (rChan P) (schedPolicy (rsched P A n)) μ (A.card * n) {ω | rfires P A β n j ω} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin A.card, eB β ^ n :=
        Finset.sum_le_sum fun j _ => rfires_small P A β n hA μ j (hμ j)
    _ = (A.card : ℝ≥0∞) * eB β ^ n := by simp

/-- Error at the needle world of a tested repair. -/
theorem err_needle_world (hA : ∀ T ∈ A, T ≠ P) (j0 : Fin A.card) (Acc' : Finset (Fin m) → Prop)
    (hTacc : Acc' (enumA A j0)) :
    hist (rChan P) (schedPolicy (rsched P A n)) (needle β (enumA A j0)) (A.card * n)
      {ω | Acc' (rout P A β n ω)}ᶜ ≤ (A.card : ℝ≥0∞) * eB β ^ n := by
  classical
  let bad : Fin A.card → Set (Hist (Fin (NQ m)) (A.card * n)) := fun j =>
    if j = j0 then {ω | ¬ rfires P A β n j ω} else {ω | rfires P A β n j ω}
  have hsub : {ω | Acc' (rout P A β n ω)}ᶜ ⊆ ⋃ j, bad j := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_iUnion, not_exists] at hno
    apply hω
    have h0 : rfires P A β n j0 ω := by
      have := hno j0
      simp only [bad, if_pos rfl, Set.mem_setOf_eq, not_not] at this
      exact this
    have h1 : ∀ j, j ≠ j0 → ¬ rfires P A β n j ω := by
      intro j hj
      have := hno j
      simp only [bad, if_neg hj, Set.mem_setOf_eq] at this
      exact this
    show Acc' (rout P A β n ω)
    rw [rout_of_single P A β n ω j0 h0 h1]; exact hTacc
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ j, hist (rChan P) (schedPolicy (rsched P A n)) (needle β (enumA A j0)) (A.card * n)
          (bad j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin A.card, eB β ^ n := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : j = j0
        · subst hj
          simp only [bad, if_pos rfl]
          exact rnofire_small P A β n hA j
        · simp only [bad, if_neg hj]
          exact rfires_small P A β n hA _ j
            (mz_needle_off P (enumA A j0) (enumA A j) β (fun h => hj (enumA_inj A h)))
    _ = (A.card : ℝ≥0∞) * eB β ^ n := by simp

end Upper

/-- `|A| e^{-nβ²/8} ≤ α` once `n ≥ 8 log(|A|/α)/β²`. -/
theorem card_eB_le (a : ℕ) (β α : ℝ) (hβ : β ≠ 0) (hα : 0 < α) (n : ℕ)
    (hn : 8 * Real.log (a / α) / β ^ 2 ≤ n) : (a : ℝ≥0∞) * eB β ^ n ≤ ENNReal.ofReal α := by
  have hb2 : 0 < β ^ 2 := by positivity
  have hmain : (a : ℝ) * Real.exp (-(β ^ 2 / 8)) ^ n ≤ α := by
    rw [← Real.exp_nat_mul]
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp; exact hα.le
    · have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hlog : Real.log (a / α) ≤ n * (β ^ 2 / 8) := by
        have := (div_le_iff₀ hb2).mp hn
        nlinarith
      have hexp : Real.exp (n * -(β ^ 2 / 8)) ≤ α / a := by
        calc Real.exp (n * -(β ^ 2 / 8)) ≤ Real.exp (-Real.log (a / α)) :=
              Real.exp_le_exp.mpr (by nlinarith)
          _ = α / a := by rw [Real.exp_neg, Real.exp_log (div_pos ha' hα), inv_div]
      calc (a : ℝ) * Real.exp (n * -(β ^ 2 / 8)) ≤ a * (α / a) :=
            mul_le_mul_of_nonneg_left hexp ha'.le
        _ = α := by field_simp
  have : (a : ℝ≥0∞) * eB β ^ n = ENNReal.ofReal ((a : ℝ) * Real.exp (-(β ^ 2 / 8)) ^ n) := by
    unfold eB
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg a), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (Real.exp_pos _).le]
  rw [this]; exact ENNReal.ofReal_le_ofReal hmain

theorem real_ge_of_compl_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Set Ω) (hs : MeasurableSet s) (α : ℝ) (hα : 0 ≤ α) (h : μ sᶜ ≤ ENNReal.ofReal α) :
    1 - α ≤ μ.real s := by
  have h1 : μ.real sᶜ ≤ α := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hα h
  rw [measureReal_compl hs, probReal_univ] at h1
  linarith

/-- **The constructive upper bound.** -/
theorem calibration_upper (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hα : 0 < α) (hSep : ∀ T, Reach P k R T → T ≠ P → ε < defc g P T) :
    ∃ (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m)),
      (∀ S, MeasurableSet {ω | out ω = S}) ∧
      1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)} ∧
      (∀ T, Reach P k R T → T ≠ P →
        1 - α ≤ (hist (rChan P) pol (needle β T) n).real
          {ω | Acc g P k R ε (needle β T) (out ω)}) ∧
      ∀ μ, costN (rChan P) pol μ n ≤
        (((Amb g P k R β ε).card *
          ⌈8 * Real.log ((Amb g P k R β ε).card / α) / β ^ 2⌉₊ : ℕ) : ℝ≥0∞) := by
  classical
  set A := Amb g P k R β ε with hAdef
  set nn := ⌈8 * Real.log (A.card / α) / β ^ 2⌉₊ with hnn
  have hA : ∀ T ∈ A, T ≠ P := fun T hT => (mem_Amb.mp hT).2.1
  have hn : 8 * Real.log (A.card / α) / β ^ 2 ≤ nn := Nat.le_ceil _
  have hbound := card_eB_le A.card β α hβ.ne' hα nn hn
  refine ⟨schedPolicy (rsched P A nn), A.card * nn, rout P A β nn, measurableSet_rout P A β nn,
    ?_, ?_, ?_⟩
  · haveI := hist_prob (rChan P) (schedPolicy (rsched P A nn)) null0 (A.card * nn)
    refine real_ge_of_compl_le _ _ (measurableSet_out_mem _ _ (measurableSet_rout P A β nn)
      {S | Acc g P k R ε null0 S}) α hα.le ?_
    exact (err_zero_world P A β nn hA null0 (fun j => mz_null P _) _
      (acc_null_P g P k R ε hP hTop hε)).trans hbound
  · intro T hTr hTP
    haveI := hist_prob (rChan P) (schedPolicy (rsched P A nn)) (needle β T) (A.card * nn)
    refine real_ge_of_compl_le _ _ (measurableSet_out_mem _ _ (measurableSet_rout P A β nn)
      {S | Acc g P k R ε (needle β T) S}) α hα.le ?_
    by_cases hTA : T ∈ A
    · have he := enumA_equivFin A T hTA
      have herr := err_needle_world P A β nn hA (A.equivFin ⟨T, hTA⟩)
        (fun S => Acc g P k R ε (needle β T) S)
        (by rw [he]; exact acc_needle_self g P k R β ε hP hTop hε T hTA)
      rw [he] at herr
      exact herr.trans hbound
    · have hTd : β - ε ≤ defc g P T := by
        by_contra hlt
        push Not at hlt
        exact hTA (mem_Amb.mpr ⟨hTr, hTP, hSep T hTr hTP, hlt⟩)
      refine (err_zero_world P A β nn hA (needle β T) (fun j => ?_) _
        (acc_needle_P g P k R β ε hP hTop hε T hTP hTd)).trans hbound
      exact mz_needle_off P T (enumA A j) β (fun h => hTA (h ▸ enumA_mem A j))
  · intro μ
    rw [costN_sched]
    exact_mod_cast schedCost_le' (rsched P A nn) (rChan P).dummy (A.card * nn)

/-! ## 6. The geometry of the ambiguous set -/

theorem amb_empty_R0 (g : Fin m → ℝ) (P : Finset (Fin m)) (k : ℕ) (β ε : ℝ) (hP : P.card = k) :
    Amb g P k 0 β ε = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro T hT
  obtain ⟨⟨hTc, hTR⟩, hTP, _, _⟩ := mem_Amb.mp hT
  have hsub : T ⊆ P := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp (by omega))
  exact hTP (Finset.eq_of_subset_of_card_le hsub (by omega))

theorem amb_mono (g : Fin m → ℝ) (P : Finset (Fin m)) (k : ℕ) (β ε : ℝ) {R R' : ℕ}
    (hRR : R ≤ R') : Amb g P k R β ε ⊆ Amb g P k R' β ε := by
  intro T hT
  obtain ⟨⟨hTc, hTR⟩, hTP, h1, h2⟩ := mem_Amb.mp hT
  exact mem_Amb.mpr ⟨⟨hTc, hTR.trans hRR⟩, hTP, h1, h2⟩

theorem one_le_card_sdiff (P T : Finset (Fin m)) (hc : T.card = P.card) (hTP : T ≠ P) :
    1 ≤ (P \ T).card := by
  by_contra h
  push Not at h
  have h0 : P \ T = ∅ := Finset.card_eq_zero.mp (by omega)
  have hsub : P ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp h0
  exact hTP (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- **A first-order margin empties the ambiguous set.** -/
theorem amb_empty_of_margin (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε γ : ℝ)
    (hP : P.card = k) (hγ : 0 ≤ γ) (hMargin : ∀ i ∈ P, ∀ j ∉ P, γ + g j ≤ g i)
    (hγβ : β - ε ≤ γ) : Amb g P k R β ε = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro T hT
  obtain ⟨⟨hTc, _⟩, hTP, _, hTd⟩ := mem_Amb.mp hT
  have hc : (P \ T).card = (T \ P).card := Finset.card_sdiff_comm (hP.trans hTc.symm)
  have hs := surplus_ge_card_mul' (P \ T) (T \ P) g γ hc
    (fun i hi j hj => hMargin i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2)
  have h1 := one_le_card_sdiff P T (hTc.trans hP.symm) hTP
  have h1' : (1 : ℝ) ≤ ((P \ T).card : ℝ) := by exact_mod_cast h1
  unfold defc at hTd
  nlinarith

/-- Gains `γ` on the prefix and `0` outside. -/
def gapGain (P : Finset (Fin m)) (γ : ℝ) (i : Fin m) : ℝ := if i ∈ P then γ else 0

theorem defc_gap (P S : Finset (Fin m)) (γ : ℝ) :
    defc (gapGain P γ) P S = γ * (P \ S).card := by
  unfold defc gapGain
  have h1 : (P \ S).sum (fun i => if i ∈ P then γ else 0) = (P \ S).sum (fun _ => γ) :=
    Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_sdiff.mp hi).1
  have h2 : (S \ P).sum (fun i => if i ∈ P then γ else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => if_neg (Finset.mem_sdiff.mp hi).2
  rw [h1, h2, Finset.sum_const, nsmul_eq_mul]; ring

theorem gap_top (P : Finset (Fin m)) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∀ i ∈ P, ∀ j ∉ P, gapGain P γ j ≤ gapGain P γ i := by
  intro i hi j hj; unfold gapGain; rw [if_pos hi, if_neg hj]; exact hγ

theorem gap_sep (P : Finset (Fin m)) (k R : ℕ) (ε γ : ℝ) (hP : P.card = k) (hεγ : ε < γ)
    (hγ : 0 ≤ γ) : ∀ T, Reach P k R T → T ≠ P → ε < defc (gapGain P γ) P T := by
  intro T hTr hTP
  rw [defc_gap]
  have h1 := one_le_card_sdiff P T (hTr.1.trans hP.symm) hTP
  have h1' : (1 : ℝ) ≤ ((P \ T).card : ℝ) := by exact_mod_cast h1
  nlinarith

/-- On the uniform-gap instance the ambiguous set of the `R`-problem has at least
`C(k,R)·C(m−k,R)` members.  The `R`-problem's class and target depend on `R`. -/
theorem amb_card_ge_gap (P : Finset (Fin m)) (k R : ℕ) (β ε γ : ℝ) (hP : P.card = k)
    (hR1 : 1 ≤ R) (hεγ : ε < γ) (hγ : 0 ≤ γ) (hγβ : γ * R < β - ε) :
    k.choose R * (m - k).choose R ≤ (Amb (gapGain P γ) P k R β ε).card := by
  classical
  set X0 := P.powersetCard R
  set Y0 := Pᶜ.powersetCard R
  have hcard : (X0 ×ˢ Y0).card = k.choose R * (m - k).choose R := by
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_compl, Fintype.card_fin, hP]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun p => (P \ p.1) ∪ p.2) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe] at hp ⊢
    obtain ⟨hX, hY⟩ := Finset.mem_product.mp hp
    obtain ⟨hXP, hXc⟩ := Finset.mem_powersetCard.mp hX
    obtain ⟨hYP, hYc⟩ := Finset.mem_powersetCard.mp hY
    have hYout : ∀ j ∈ p.2, j ∉ P := fun j hj => Finset.mem_compl.mp (hYP hj)
    have hdis : Disjoint (P \ p.1) p.2 := by
      rw [Finset.disjoint_left]
      intro j hj hjY
      exact hYout j hjY (Finset.mem_sdiff.mp hj).1
    have hTP' : ((P \ p.1) ∪ p.2) \ P = p.2 := by
      ext j; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hj | hj, hjP⟩
        · exact absurd hj.1 hjP
        · exact hj
      · intro hj; exact ⟨Or.inr hj, hYout j hj⟩
    have hPT : P \ ((P \ p.1) ∪ p.2) = p.1 := by
      ext j; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hjP, hj⟩
        by_contra hjX
        exact hj (Or.inl ⟨hjP, hjX⟩)
      · intro hjX
        refine ⟨hXP hjX, ?_⟩
        rintro (hj | hj)
        · exact hj.2 hjX
        · exact hYout j hj (hXP hjX)
    have hTc : ((P \ p.1) ∪ p.2).card = k := by
      rw [Finset.card_union_of_disjoint hdis, Finset.card_sdiff_of_subset hXP, hXc, hYc, hP]
      have : R ≤ k := by rw [← hP, ← hXc]; exact Finset.card_le_card hXP
      omega
    have hne : (P \ p.1) ∪ p.2 ≠ P := by
      intro h
      have : p.2 = ∅ := by rw [← hTP', h, Finset.sdiff_self]
      rw [this, Finset.card_empty] at hYc
      omega
    refine mem_Amb.mpr ⟨⟨hTc, by rw [hTP', hYc]⟩, hne, ?_, ?_⟩
    · rw [defc_gap, hPT, hXc]
      have h1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
      nlinarith
    · rw [defc_gap, hPT, hXc]; exact hγβ
  · intro p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    obtain ⟨hpX, hpY⟩ := Finset.mem_product.mp hp
    obtain ⟨hqX, hqY⟩ := Finset.mem_product.mp hq
    have hpYout : ∀ j ∈ p.2, j ∉ P :=
      fun j hj => Finset.mem_compl.mp ((Finset.mem_powersetCard.mp hpY).1 hj)
    have hqYout : ∀ j ∈ q.2, j ∉ P :=
      fun j hj => Finset.mem_compl.mp ((Finset.mem_powersetCard.mp hqY).1 hj)
    have hpXP := (Finset.mem_powersetCard.mp hpX).1
    have hqXP := (Finset.mem_powersetCard.mp hqX).1
    simp only at hpq
    have hY : p.2 = q.2 := by
      have e1 : ((P \ p.1) ∪ p.2) \ P = p.2 := by
        ext j; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hj | hj, hjP⟩
          · exact absurd hj.1 hjP
          · exact hj
        · intro hj; exact ⟨Or.inr hj, hpYout j hj⟩
      have e2 : ((P \ q.1) ∪ q.2) \ P = q.2 := by
        ext j; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hj | hj, hjP⟩
          · exact absurd hj.1 hjP
          · exact hj
        · intro hj; exact ⟨Or.inr hj, hqYout j hj⟩
      rw [← e1, ← e2, hpq]
    have hX : p.1 = q.1 := by
      have e1 : P \ ((P \ p.1) ∪ p.2) = p.1 := by
        ext j; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hjP, hj⟩
          by_contra hjX
          exact hj (Or.inl ⟨hjP, hjX⟩)
        · intro hjX
          refine ⟨hpXP hjX, ?_⟩
          rintro (hj | hj)
          · exact hj.2 hjX
          · exact hpYout j hj (hpXP hjX)
      have e2 : P \ ((P \ q.1) ∪ q.2) = q.1 := by
        ext j; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hjP, hj⟩
          by_contra hjX
          exact hj (Or.inl ⟨hjP, hjX⟩)
        · intro hjX
          refine ⟨hqXP hjX, ?_⟩
          rintro (hj | hj)
          · exact hj.2 hjX
          · exact hqYout j hj (hqXP hjX)
      rw [← e1, ← e2, hpq]
    exact Prod.ext hX hY

/-- **The geometric floor.**  Beyond reach, every legal output loses `β − defc T`. -/
theorem geometric_floor (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) (T : Finset (Fin m))
    (hTR : R < (T \ P).card) (S : Finset (Fin m)) (hS : Reach P k R S) :
    β - defc g P T ≤ val g (needle β T) T - val g (needle β T) S := by
  have hST : S ≠ T := by
    intro h; rw [h] at hS; exact absurd hS.2 (by omega)
  rw [val_needle, val_needle, if_pos rfl, if_neg hST, sum_eq_sub_defc g P T,
    sum_eq_sub_defc g P S]
  have := defc_nonneg g P S (hS.1.trans hP.symm) hTop
  linarith

/-! ## 7. Satisfiability -/

theorem D_pos_hundredth : 0 < (1 - 1 / 100 : ℝ) * Real.log (1 / (1 / 100)) - Real.log 2 := by
  have h100 : (1 : ℝ) ≤ Real.log (1 / (1 / 100)) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have h2 := Real.log_two_lt_d9
  norm_num at h2 ⊢
  nlinarith

/-- **The lower bound is not vacuous.**  On four messages with a two-message prefix and one
revision, the ambiguous set has at least four repairs, the bound is strictly positive, and the
constructed protocol meets every hypothesis of `calibration_lower`. -/
theorem calibration_satisfiable :
    4 ≤ (Amb (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2)).card ∧
    0 < (1 - 1 / 100 : ℝ) * Real.log (1 / (1 / 100)) - Real.log 2 ∧
    ∃ (pol : Policy (Fin (NQ 4))) (n : ℕ) (out : Hist (Fin (NQ 4)) n → Finset (Fin 4)),
      (∀ S, MeasurableSet {ω | out ω = S}) ∧
      1 - 1 / 100 ≤ (hist (rChan {0, 1}) pol null0 n).real
        {ω | Acc (gapGain {0, 1} 1) {0, 1} 2 1 (1 / 2) null0 (out ω)} ∧
      ∀ T ∈ Amb (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2),
        1 - 1 / 100 ≤ (hist (rChan {0, 1}) pol (needle 3 T) n).real
          {ω | Acc (gapGain {0, 1} 1) {0, 1} 2 1 (1 / 2) (needle 3 T) (out ω)} := by
  have hP : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  refine ⟨?_, D_pos_hundredth, ?_⟩
  · have := amb_card_ge_gap ({0, 1} : Finset (Fin 4)) 2 1 3 (1 / 2) 1 hP le_rfl (by norm_num)
      (by norm_num) (by norm_num)
    simpa using this
  · obtain ⟨pol, n, out, hm, h0, hT, _⟩ := calibration_upper (gapGain ({0, 1} : Finset (Fin 4)) 1)
      {0, 1} 2 1 3 (1 / 2) (1 / 100) hP (gap_top _ 1 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num) (gap_sep _ 2 1 (1 / 2) 1 hP (by norm_num) (by norm_num))
    exact ⟨pol, n, out, hm, h0, fun T hTA =>
      hT T (mem_Amb.mp hTA).1 (mem_Amb.mp hTA).2.1⟩

end CIGAMF.P13.MarlRepairCalibration

#print axioms CIGAMF.P13.MarlRepairCalibration.acc_needle_unique
#print axioms CIGAMF.P13.MarlRepairCalibration.needle_local
#print axioms CIGAMF.P13.MarlRepairCalibration.klq_rChan
#print axioms CIGAMF.P13.MarlRepairCalibration.bc_rChan
#print axioms CIGAMF.P13.MarlRepairCalibration.per_repair_lower
#print axioms CIGAMF.P13.MarlRepairCalibration.calibration_lower
#print axioms CIGAMF.P13.MarlRepairCalibration.zero_allocation_impossible
#print axioms CIGAMF.P13.MarlRepairCalibration.rfires_small
#print axioms CIGAMF.P13.MarlRepairCalibration.rnofire_small
#print axioms CIGAMF.P13.MarlRepairCalibration.err_zero_world
#print axioms CIGAMF.P13.MarlRepairCalibration.err_needle_world
#print axioms CIGAMF.P13.MarlRepairCalibration.calibration_upper
#print axioms CIGAMF.P13.MarlRepairCalibration.amb_empty_R0
#print axioms CIGAMF.P13.MarlRepairCalibration.amb_mono
#print axioms CIGAMF.P13.MarlRepairCalibration.amb_empty_of_margin
#print axioms CIGAMF.P13.MarlRepairCalibration.amb_card_ge_gap
#print axioms CIGAMF.P13.MarlRepairCalibration.geometric_floor
#print axioms CIGAMF.P13.MarlRepairCalibration.calibration_satisfiable
