import Mathlib
import «LeanMarlRepairCalibrationV1»

/-!
# T2 debt: calibration when the interaction is SHARED across repairs (the pair class)

`LeanMarlRepairCalibrationV1` treats the needle class: the interaction sits on ONE broadcast
set.  In the executable task E1b the interaction sits on a PAIR `E = {a, b}` of senders, and
every broadcast set containing both earns it.  One rollout then informs every ambiguous pair it
contains, and the needle counting no longer applies.

Same channel `rChan P` (paired rollout of a set against the prefix `P`, unit Gaussian excess;
the prefix is the free dummy).  Pair world `pairW β E`: excess `β` on every set `S ⊇ E`.

## WHAT IS PROVED

* `acc_null_not_sup`, `acc_pair_sup` — at an ambiguous pair (`E ∈ AmbP`: `E ⊄ P`, every
  reachable set containing `E` has deficit `> ε`, some has deficit `< β − ε`), null-acceptable
  outputs never contain `E` and pair-acceptable outputs always do.
* `pair_one_lower` — any adaptive protocol, correct at the null world and at pair `E`, rolls
  out sets containing `E`: `D ≤ (Σ_q E_0[N_q] · [E ⊆ q]) · β²/2`, `D = (1−α)log(1/α) − log 2`.
* `pair_calibration_lower` — summed over pairs: `|AmbP| · D ≤ (Σ_q E_0[N_q] · cov q) · β²/2`,
  where `cov q` counts the ambiguous pairs inside query `q`.
* `pairs_cover_le` — a set `S` contains at most `|S \ P| · |S|` pairs not inside `P`.
* `pair_legal_lower` — if the protocol only rolls out LEGAL repairs (reachable sets, a.s. at
  the null world), `|AmbP| · D ≤ R · k · E_0[cost] · β²/2`.  Compared with the needle law
  (`calibration_lower`, one repair per query), a legal rollout informs up to `R·k` pairs.
* `pair_upper` — a legal fixed schedule (block tests on every reachable non-prefix set, decoded
  to the fired set of largest first-order value) is correct at the null world and at every
  ambiguous pair, with cost `≤ |F_R \ {P}| · ⌈8 log(|F_R \ {P}|/α)/β²⌉`.
* `pair_satisfiable` — on four messages, prefix of two, one revision: `|AmbP| ≥ 4`, the bound
  is strictly positive, and `pair_upper`'s protocol meets every hypothesis of
  `pair_legal_lower`.

## WHAT THIS DOES NOT ESTABLISH

- Tightness.  The lower bound divides by the per-query cover `R·k`; the constructed upper bound
  tests every reachable repair and does not exploit sharing.  A design matching the lower bound
  (e.g. grouping repairs by the outsider they bring in) is not constructed.
- One interacting pair per world.  Several simultaneous pairs, or interactions of higher order,
  are not treated.
- Queries outside the legal family (e.g. a simulator rolling out large sets) are allowed by
  `pair_calibration_lower` but then `cov q` can be as large as `C(|q|, 2)`; the legal bound
  needs the legality hypothesis.
-/

namespace CIGAMF.P13.MarlPairCalibration

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperBPrivateQuery
open CIGAMF.P13.PaperBSchedule CIGAMF.P13.PaperBObstruction CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperBHellingerTest CIGAMF.P13.PaperABridge CIGAMF.P13.PaperAFamilyLower
open CIGAMF.P13.PaperAGaussianKL CIGAMF.P13.PaperAStrict
open CIGAMF.P13.MarlSubsetFrontier CIGAMF.P13.MarlEstimatedRevision
open CIGAMF.P13.MarlRepairCalibration

variable {m : ℕ}

/-! ## 1. The pair worlds -/

/-- Decode a query index to its broadcast set. -/
noncomputable def decS (q : Fin (NQ m)) : Finset (Fin m) := (Fintype.equivFin (Finset (Fin m))).symm q

theorem decS_code (S : Finset (Fin m)) : decS (code S) = S := by
  simp [decS, code]

theorem code_decS (q : Fin (NQ m)) : code (decS q) = q := by
  simp [decS, code]

/-- The pair world: excess `β` on every broadcast set containing the pair `E`. -/
noncomputable def pairW (β : ℝ) (E : Finset (Fin m)) : Fin (NQ m) → ℝ := by
  classical
  exact fun q => if E ⊆ decS q then β else 0

theorem pairW_code (β : ℝ) (E S : Finset (Fin m)) :
    pairW β E (code S) = if E ⊆ S then β else 0 := by
  classical
  simp [pairW, decS_code]

theorem val_pair (g : Fin m → ℝ) (β : ℝ) (E S : Finset (Fin m)) :
    val g (pairW β E) S = S.sum g + if E ⊆ S then β else 0 := by
  unfold CIGAMF.P13.MarlRepairCalibration.val; rw [pairW_code]

/-- The ambiguous pairs. -/
noncomputable def AmbP (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε : ℝ) :
    Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter fun E => E.card = 2 ∧ ¬ E ⊆ P ∧
    (∀ S, Reach P k R S → E ⊆ S → ε < defc g P S) ∧
    (∃ T, Reach P k R T ∧ E ⊆ T ∧ defc g P T < β - ε)

theorem mem_AmbP {g : Fin m → ℝ} {P : Finset (Fin m)} {k R : ℕ} {β ε : ℝ} {E : Finset (Fin m)} :
    E ∈ AmbP g P k R β ε ↔ E.card = 2 ∧ ¬ E ⊆ P ∧
      (∀ S, Reach P k R S → E ⊆ S → ε < defc g P S) ∧
      (∃ T, Reach P k R T ∧ E ⊆ T ∧ defc g P T < β - ε) := by
  unfold AmbP; simp

theorem acc_null_not_sup (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε : ℝ)
    (hP : P.card = k) (E : Finset (Fin m)) (hE : E ∈ AmbP g P k R β ε) (S : Finset (Fin m))
    (hS : Acc g P k R ε null0 S) : ¬ E ⊆ S := by
  intro hES
  exact not_acc_null g P k R ε hP S ((mem_AmbP.mp hE).2.2.1 S hS.1 hES) hS

theorem acc_pair_sup (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) (E : Finset (Fin m))
    (hE : E ∈ AmbP g P k R β ε) (S : Finset (Fin m)) (hS : Acc g P k R ε (pairW β E) S) :
    E ⊆ S := by
  obtain ⟨_, _, _, T, hTr, hET, hTd⟩ := mem_AmbP.mp hE
  by_contra hES
  have h1 := hS.2 T hTr
  rw [val_pair, val_pair, if_pos hET, if_neg hES, sum_eq_sub_defc g P T,
    sum_eq_sub_defc g P S] at h1
  have := defc_nonneg g P S (hS.1.1.trans hP.symm) hTop
  linarith

theorem klq_pair (P E : Finset (Fin m)) (β : ℝ) (hEP : ¬ E ⊆ P) (q : Fin (NQ m)) :
    klq (rChan P) null0 (pairW β E) q
      = (if E ⊆ decS q then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  rw [klq_rChan, mz_null]
  by_cases hq : q = code P
  · have h : ¬ E ⊆ decS q := by rw [hq, decS_code]; exact hEP
    rw [if_neg h]; simp [mz, hq]
  · by_cases hE : E ⊆ decS q
    · rw [if_pos hE]; simp [mz, hq, pairW, hE]
    · rw [if_neg hE]; simp [mz, hq, pairW, hE]

/-! ## 2. The lower bound -/

/-- **Every ambiguous pair must be rolled out inside some set.** -/
theorem pair_one_lower (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα1 : α ≤ 1)
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)})
    (E : Finset (Fin m)) (hE : E ∈ AmbP g P k R β ε)
    (hcE : 1 - α ≤ (hist (rChan P) pol (pairW β E) n).real
      {ω | Acc g P k R ε (pairW β E) (out ω)}) :
    ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2)
      ≤ (∑ q, (∫⁻ ω, cntQ q n ω ∂hist (rChan P) pol null0 n)
          * (if E ⊆ decS q then (1 : ℝ≥0∞) else 0)) * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  have hEP := (mem_AmbP.mp hE).2.1
  haveI := hist_prob (rChan P) pol (pairW β E) n
  have hE0m : MeasurableSet {ω | Acc g P k R ε null0 (out ω)} :=
    measurableSet_out_mem n out hmeas {S | Acc g P k R ε null0 S}
  have hETm : MeasurableSet {ω | Acc g P k R ε (pairW β E) (out ω)} :=
    measurableSet_out_mem n out hmeas {S | Acc g P k R ε (pairW β E) S}
  have hl : (hist (rChan P) pol (pairW β E) n).real {ω | Acc g P k R ε null0 (out ω)} ≤ α := by
    have hsub : {ω | Acc g P k R ε null0 (out ω)}
        ⊆ {ω | Acc g P k R ε (pairW β E) (out ω)}ᶜ := by
      intro ω hω hω'
      exact acc_null_not_sup g P k R β ε hP E hE (out ω) hω
        (acc_pair_sup g P k R β ε hP hTop E hE (out ω) hω')
    have := measureReal_mono hsub (measure_ne_top (hist (rChan P) pol (pairW β E) n) _)
    rw [measureReal_compl hETm, probReal_univ] at this
    linarith
  have hcm := change_of_measure (rChan P) pol null0 (pairW β E) n _ hE0m α hα hα1 h0 hl
  refine hcm.trans (le_of_eq ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [klq_pair P E β hEP q, mul_assoc]

/-- The number of ambiguous pairs inside a query. -/
noncomputable def cov (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε : ℝ)
    (q : Fin (NQ m)) : ℕ := by
  classical
  exact ((AmbP g P k R β ε).filter fun E => E ⊆ decS q).card

/-- **The pair calibration law.** -/
theorem pair_calibration_lower (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα1 : α ≤ 1)
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)})
    (hcorr : ∀ E ∈ AmbP g P k R β ε, 1 - α ≤ (hist (rChan P) pol (pairW β E) n).real
      {ω | Acc g P k R ε (pairW β E) (out ω)}) :
    ((AmbP g P k R β ε).card : ℝ≥0∞) * ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2)
      ≤ (∑ q, (∫⁻ ω, cntQ q n ω ∂hist (rChan P) pol null0 n) * (cov g P k R β ε q : ℝ≥0∞))
          * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  set F : Fin (NQ m) → ℝ≥0∞ := fun q => ∫⁻ ω, cntQ q n ω ∂hist (rChan P) pol null0 n with hF
  set c := ENNReal.ofReal (β ^ 2 / 2)
  set D := ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2)
  calc ((AmbP g P k R β ε).card : ℝ≥0∞) * D = ∑ _E ∈ AmbP g P k R β ε, D := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ E ∈ AmbP g P k R β ε,
          (∑ q, F q * (if E ⊆ decS q then (1 : ℝ≥0∞) else 0)) * c :=
        Finset.sum_le_sum fun E hE =>
          pair_one_lower g P k R β ε α hP hTop pol n out hmeas hα hα1 h0 E hE (hcorr E hE)
    _ = (∑ q, F q * (cov g P k R β ε q : ℝ≥0∞)) * c := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        unfold cov
        rw [Finset.sum_boole]

/-! ## 3. How many pairs a legal rollout informs -/

theorem pairs_cover_le (P S : Finset (Fin m)) :
    (Finset.univ.filter fun E : Finset (Fin m) => E.card = 2 ∧ ¬ E ⊆ P ∧ E ⊆ S).card
      ≤ (S \ P).card * S.card := by
  classical
  have hsub : (Finset.univ.filter fun E : Finset (Fin m) => E.card = 2 ∧ ¬ E ⊆ P ∧ E ⊆ S)
      ⊆ (S \ P).biUnion fun x => (S.erase x).image fun y => ({x, y} : Finset (Fin m)) := by
    intro E hE
    obtain ⟨h2, hEP, hES⟩ := (Finset.mem_filter.mp hE).2
    obtain ⟨x, hxE, hxP⟩ := Finset.not_subset.mp hEP
    refine Finset.mem_biUnion.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hES hxE, hxP⟩, ?_⟩
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp h2
    rcases Finset.mem_insert.mp hxE with rfl | hxv
    · exact Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨huv.symm, hES (by simp)⟩, rfl⟩
    · rw [Finset.mem_singleton] at hxv
      subst hxv
      exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huv, hES (by simp)⟩,
        Finset.pair_comm _ _⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ S \ P, ((S.erase x).image fun y => ({x, y} : Finset (Fin m))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S \ P, S.card :=
        Finset.sum_le_sum fun x _ => Finset.card_image_le.trans (Finset.card_erase_le)
    _ = (S \ P).card * S.card := by rw [Finset.sum_const, smul_eq_mul]

theorem cov_le (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε : ℝ) (q : Fin (NQ m)) :
    cov g P k R β ε q ≤ (decS q \ P).card * (decS q).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (pairs_cover_le P (decS q))
  intro E hE
  obtain ⟨hEA, hEq⟩ := Finset.mem_filter.mp hE
  obtain ⟨h2, hEP, _⟩ := mem_AmbP.mp hEA
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, hEP, hEq⟩

/-- **Legal rollouts: the pair law against the cost.** -/
theorem pair_legal_lower (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα1 : α ≤ 1)
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)})
    (hcorr : ∀ E ∈ AmbP g P k R β ε, 1 - α ≤ (hist (rChan P) pol (pairW β E) n).real
      {ω | Acc g P k R ε (pairW β E) (out ω)})
    (hlegal : ∀ q, ¬ Reach P k R (decS q) → ∫⁻ ω, cntQ q n ω ∂hist (rChan P) pol null0 n = 0) :
    ((AmbP g P k R β ε).card : ℝ≥0∞) * ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2)
      ≤ ((R * k : ℕ) : ℝ≥0∞) * costN (rChan P) pol null0 n * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  set F : Fin (NQ m) → ℝ≥0∞ := fun q => ∫⁻ ω, cntQ q n ω ∂hist (rChan P) pol null0 n with hF
  refine (pair_calibration_lower g P k R β ε α hP hTop pol n out hmeas hα hα1 h0 hcorr).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ bot_le
  rw [costN_eq_sum, rChan_dummy, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  by_cases hqP : q = code P
  · have : cov g P k R β ε q = 0 := by
      unfold cov
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro E hE hEq
      rw [hqP, decS_code] at hEq
      exact (mem_AmbP.mp hE).2.1 hEq
    simp [this]
  · by_cases hr : Reach P k R (decS q)
    · have hc : cov g P k R β ε q ≤ R * k := by
        refine (cov_le g P k R β ε q).trans ?_
        rw [hr.1]
        exact Nat.mul_le_mul_right _ hr.2
      rw [if_neg hqP, mul_one, mul_comm ((R * k : ℕ) : ℝ≥0∞)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) bot_le
    · show F q * _ ≤ _
      rw [show F q = 0 from hlegal q hr, zero_mul]
      exact bot_le

/-! ## 4. A legal protocol: test every reachable repair, decode the fired pattern -/

section Upper

variable (g : Fin m → ℝ) (P : Finset (Fin m)) (A : Finset (Finset (Fin m))) (β : ℝ) (n : ℕ)

/-- A test fails to fire, in ANY world whose excess on its repair is `β`, with probability at
most `e^{-nβ²/8}`. -/
theorem rnofire_gen (hA : ∀ T ∈ A, T ≠ P) (μ : Fin (NQ m) → ℝ) (j : Fin A.card)
    (hμ : mz (code P) μ (code (enumA A j)) = β) :
    hist (rChan P) (schedPolicy (rsched P A n)) μ (A.card * n) {ω | ¬ rfires P A β n j ω}
      ≤ eB β ^ n := by
  have hTP := hA _ (enumA_mem A j)
  have hsub : {ω | ¬ rfires P A β n j ω} ⊆
      {ω | ∏ i ∈ blockSet (A.card * n) (rblk n j), (rChan P).dens μ (rsched P A n i) (ω i).2
        ≤ ∏ i ∈ blockSet (A.card * n) (rblk n j), (rChan P).dens null0 (rsched P A n i) (ω i).2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    unfold rfires rlik at hω
    have heq : ∏ i ∈ blockSet (A.card * n) (rblk n j),
          (rChan P).dens (needle β (enumA A j)) (rsched P A n i) (ω i).2
        = ∏ i ∈ blockSet (A.card * n) (rblk n j), (rChan P).dens μ (rsched P A n i) (ω i).2 := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [rsched_block P A n j i hi, rChan_dens, rChan_dens, mz_needle_self P _ β hTP, hμ]
    rw [← heq]; exact not_lt.mp hω
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∏ i ∈ blockSet (A.card * n) (rblk n j), bc (rChan P) μ null0 (rsched P A n i) :=
        block_error (rChan P) (rsched P A n) μ null0 (A.card * n) (rblk n j)
    _ = eB β ^ (blockSet (A.card * n) (rblk n j)).card := by
        rw [Finset.prod_congr rfl fun i hi => by rw [rsched_block P A n j i hi], Finset.prod_const,
          bc_sep' P μ null0 _ β hμ (mz_null P _)]
    _ ≤ eB β ^ n := pow_card_le A β n j

/-- **Error at a world whose tested excesses are all `0` or `β`**, for ANY decoder that is
right whenever every test agrees with the pattern. -/
theorem err_pattern_world (hA : ∀ T ∈ A, T ≠ P) (μ : Fin (NQ m) → ℝ) (pat : Fin A.card → Prop)
    (h1 : ∀ j, pat j → mz (code P) μ (code (enumA A j)) = β)
    (h0 : ∀ j, ¬ pat j → mz (code P) μ (code (enumA A j)) = 0)
    (out : Hist (Fin (NQ m)) (A.card * n) → Finset (Fin m)) (Acc' : Finset (Fin m) → Prop)
    (hgood : ∀ ω, (∀ j, rfires P A β n j ω ↔ pat j) → Acc' (out ω)) :
    hist (rChan P) (schedPolicy (rsched P A n)) μ (A.card * n) {ω | Acc' (out ω)}ᶜ
      ≤ (A.card : ℝ≥0∞) * eB β ^ n := by
  classical
  let bad : Fin A.card → Set (Hist (Fin (NQ m)) (A.card * n)) := fun j =>
    if pat j then {ω | ¬ rfires P A β n j ω} else {ω | rfires P A β n j ω}
  have hsub : {ω | Acc' (out ω)}ᶜ ⊆ ⋃ j, bad j := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_iUnion, not_exists] at hno
    apply hω
    refine hgood ω fun j => ?_
    have := hno j
    by_cases hj : pat j
    · simp only [bad, if_pos hj, Set.mem_setOf_eq, not_not] at this
      exact ⟨fun _ => hj, fun _ => this⟩
    · simp only [bad, if_neg hj, Set.mem_setOf_eq] at this
      exact ⟨fun h => absurd h this, fun h => absurd h hj⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ j, hist (rChan P) (schedPolicy (rsched P A n)) μ (A.card * n) (bad j) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin A.card, eB β ^ n := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : pat j
        · simp only [bad, if_pos hj]
          exact rnofire_gen P A β n hA μ j (h1 j hj)
        · simp only [bad, if_neg hj]
          exact rfires_small P A β n hA μ j (h0 j hj)
    _ = (A.card : ℝ≥0∞) * eB β ^ n := by simp

/-- Decode a fired pattern: the fired repair of largest first-order value, or `P`. -/
noncomputable def pdec (b : Fin A.card → Bool) : Finset (Fin m) := by
  classical
  exact if h : (Finset.univ.filter fun j => b j = true).Nonempty then
    enumA A (Classical.choose
      ((Finset.univ.filter fun j => b j = true).exists_max_image (fun j => (enumA A j).sum g) h))
  else P

theorem pdec_none (b : Fin A.card → Bool) (hb : ∀ j, b j = false) : pdec g P A b = P := by
  classical
  unfold pdec
  rw [dif_neg]
  rintro ⟨j, hj⟩
  simp [hb j] at hj

theorem pdec_some (b : Fin A.card → Bool) (j0 : Fin A.card) (h0 : b j0 = true) :
    ∃ j, b j = true ∧ pdec g P A b = enumA A j ∧
      ∀ j', b j' = true → (enumA A j').sum g ≤ (enumA A j).sum g := by
  classical
  have hne : (Finset.univ.filter fun j => b j = true).Nonempty := ⟨j0, by simp [h0]⟩
  have hspec := Classical.choose_spec
    ((Finset.univ.filter fun j => b j = true).exists_max_image (fun j => (enumA A j).sum g) hne)
  refine ⟨_, (Finset.mem_filter.mp hspec.1).2, ?_, fun j' hj' => hspec.2 j' (by simp [hj'])⟩
  unfold pdec
  rw [dif_pos hne]

/-- The legal protocol's output. -/
noncomputable def pout (ω : Hist (Fin (NQ m)) (A.card * n)) : Finset (Fin m) :=
  pdec g P A (fun j => decide (rfires P A β n j ω))

theorem measurableSet_pout (S : Finset (Fin m)) : MeasurableSet {ω | pout g P A β n ω = S} := by
  have : {ω | pout g P A β n ω = S}
      = (fun ω : Hist (Fin (NQ m)) (A.card * n) => fun j => decide (rfires P A β n j ω)) ⁻¹'
          {b | pdec g P A b = S} := rfl
  rw [this]
  exact measurable_rvec P A β n (Set.toFinite _).measurableSet

end Upper

/-- The reachable non-prefix sets. -/
noncomputable def RA (P : Finset (Fin m)) (k R : ℕ) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter fun S => Reach P k R S ∧ S ≠ P

theorem mem_RA {P : Finset (Fin m)} {k R : ℕ} {S : Finset (Fin m)} :
    S ∈ RA P k R ↔ Reach P k R S ∧ S ≠ P := by
  unfold RA; simp

theorem mz_pair (P E T : Finset (Fin m)) (β : ℝ) (hTP : T ≠ P) :
    mz (code P) (pairW β E) (code T) = if E ⊆ T then β else 0 := by
  unfold mz
  rw [if_neg (fun h => hTP (code_inj h)), pairW_code]

theorem lintegral_cntQ_sched' (P : Finset (Fin m)) (s : ℕ → Fin (NQ m)) (w : Fin (NQ m) → ℝ)
    (n : ℕ) (q : Fin (NQ m)) :
    ∫⁻ ω, cntQ q n ω ∂hist (rChan P) (schedPolicy s) w n
      = ∑ i : Fin n, if s i = q then (1 : ℝ≥0∞) else 0 := by
  haveI := hist_prob (rChan P) (schedPolicy s) w n
  have hae : ∀ᵐ ω ∂hist (rChan P) (schedPolicy s) w n,
      cntQ q n ω = ∑ i : Fin n, if s i = q then (1 : ℝ≥0∞) else 0 := by
    filter_upwards [hist_sched_ae (rChan P) s w n] with ω hω
    unfold cntQ
    exact Finset.sum_congr rfl fun i _ => by rw [hω i]
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]

/-- **A legal protocol for the pair class.** -/
theorem pair_upper (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hα : 0 < α) :
    ∃ (s : ℕ → Fin (NQ m)) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m)),
      (∀ S, MeasurableSet {ω | out ω = S}) ∧
      1 - α ≤ (hist (rChan P) (schedPolicy s) null0 n).real {ω | Acc g P k R ε null0 (out ω)} ∧
      (∀ E ∈ AmbP g P k R β ε,
        1 - α ≤ (hist (rChan P) (schedPolicy s) (pairW β E) n).real
          {ω | Acc g P k R ε (pairW β E) (out ω)}) ∧
      (∀ q, ¬ Reach P k R (decS q) → ∀ w,
        ∫⁻ ω, cntQ q n ω ∂hist (rChan P) (schedPolicy s) w n = 0) ∧
      ∀ μ, costN (rChan P) (schedPolicy s) μ n ≤
        (((RA P k R).card * ⌈8 * Real.log ((RA P k R).card / α) / β ^ 2⌉₊ : ℕ) : ℝ≥0∞) := by
  classical
  set A := RA P k R with hAdef
  set nn := ⌈8 * Real.log (A.card / α) / β ^ 2⌉₊ with hnn
  have hA : ∀ T ∈ A, T ≠ P := fun T hT => (mem_RA.mp hT).2
  have hn : 8 * Real.log (A.card / α) / β ^ 2 ≤ nn := Nat.le_ceil _
  have hbound := card_eB_le A.card β α hβ.ne' hα nn hn
  refine ⟨rsched P A nn, A.card * nn, pout g P A β nn, measurableSet_pout g P A β nn,
    ?_, ?_, ?_, ?_⟩
  · -- null world: no test should fire
    haveI := hist_prob (rChan P) (schedPolicy (rsched P A nn)) null0 (A.card * nn)
    refine real_ge_of_compl_le _ _ (measurableSet_out_mem _ _ (measurableSet_pout g P A β nn)
      {S | Acc g P k R ε null0 S}) α hα.le ?_
    refine (err_pattern_world P A β nn hA null0 (fun _ => False) (fun j h => h.elim)
      (fun j _ => mz_null P _) (pout g P A β nn) (fun S => Acc g P k R ε null0 S) ?_).trans hbound
    intro ω hω
    show Acc g P k R ε null0 (pdec g P A (fun j => decide (rfires P A β nn j ω)))
    rw [pdec_none g P A _ (fun j => by simp [(hω j).not.mpr id])]
    exact acc_null_P g P k R ε hP hTop hε
  · -- pair world `E`: exactly the repairs containing `E` should fire
    intro E hE
    obtain ⟨_, hEP, _, T, hTr, hET, hTd⟩ := mem_AmbP.mp hE
    haveI := hist_prob (rChan P) (schedPolicy (rsched P A nn)) (pairW β E) (A.card * nn)
    refine real_ge_of_compl_le _ _ (measurableSet_out_mem _ _ (measurableSet_pout g P A β nn)
      {S | Acc g P k R ε (pairW β E) S}) α hα.le ?_
    refine (err_pattern_world P A β nn hA (pairW β E) (fun j => E ⊆ enumA A j)
      (fun j h => by rw [mz_pair P E _ β (hA _ (enumA_mem A j)), if_pos h])
      (fun j h => by rw [mz_pair P E _ β (hA _ (enumA_mem A j)), if_neg h])
      (pout g P A β nn) (fun S => Acc g P k R ε (pairW β E) S) ?_).trans hbound
    intro ω hω
    have hTP : T ≠ P := fun h => hEP (h ▸ hET)
    have hTA : T ∈ A := mem_RA.mpr ⟨hTr, hTP⟩
    set jT := A.equivFin ⟨T, hTA⟩
    have hjT : enumA A jT = T := enumA_equivFin A T hTA
    obtain ⟨j, hj, hout, hmax⟩ := pdec_some g P A (fun j => decide (rfires P A β nn j ω)) jT
      (by simp only [decide_eq_true_eq]; exact (hω jT).mpr (by rw [hjT]; exact hET))
    have hjE : E ⊆ enumA A j := (hω j).mp (by simpa using hj)
    have hSr : Reach P k R (enumA A j) := (mem_RA.mp (enumA_mem A j)).1
    show Acc g P k R ε (pairW β E) (pdec g P A (fun j => decide (rfires P A β nn j ω)))
    rw [hout]
    refine ⟨hSr, fun S' hS' => ?_⟩
    have hmaxT : T.sum g ≤ (enumA A j).sum g := by
      have := hmax jT (by simp only [decide_eq_true_eq]; exact (hω jT).mpr (by rw [hjT]; exact hET))
      rwa [hjT] at this
    rw [val_pair, val_pair, if_pos hjE]
    by_cases hES' : E ⊆ S'
    · have hS'P : S' ≠ P := fun h => hEP (h ▸ hES')
      have hS'A : S' ∈ A := mem_RA.mpr ⟨hS', hS'P⟩
      have hj' := enumA_equivFin A S' hS'A
      have := hmax (A.equivFin ⟨S', hS'A⟩)
        (by simp only [decide_eq_true_eq]; exact (hω _).mpr (by rw [hj']; exact hES'))
      rw [hj'] at this
      rw [if_pos hES']; linarith
    · rw [if_neg hES', sum_eq_sub_defc g P S', sum_eq_sub_defc g P T] at *
      have := defc_nonneg g P S' (hS'.1.trans hP.symm) hTop
      linarith
  · -- only legal repairs are rolled out
    intro q hq w
    rw [lintegral_cntQ_sched']
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro hs
    apply hq
    unfold rsched at hs
    split_ifs at hs with h
    · rw [← hs, decS_code]; exact (mem_RA.mp (enumA_mem A _)).1
    · rw [← hs, decS_code]; exact reach_P P k R hP
  · intro μ
    rw [costN_sched]
    exact_mod_cast schedCost_le' (rsched P A nn) (rChan P).dummy (A.card * nn)

/-! ## 5. Satisfiability -/

theorem ambP_inst (E : Finset (Fin 4)) (h2 : E.card = 2) (hEP : ¬ E ⊆ {0, 1})
    (hR : Reach ({0, 1} : Finset (Fin 4)) 2 1 E) (hd : (({0, 1} : Finset (Fin 4)) \ E).card = 1) :
    E ∈ AmbP (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2) := by
  have hP : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  refine mem_AmbP.mpr ⟨h2, hEP, fun S hS hES => ?_, E, hR, subset_rfl, ?_⟩
  · exact gap_sep _ 2 1 (1 / 2) 1 hP (by norm_num) (by norm_num) S hS
      (fun h => hEP (h ▸ hES))
  · rw [defc_gap, hd]; norm_num

/-- **The pair law is not vacuous.** -/
theorem pair_satisfiable :
    4 ≤ (AmbP (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2)).card ∧
    0 < (1 - 1 / 100 : ℝ) * Real.log (1 / (1 / 100)) - Real.log 2 ∧
    ∃ (s : ℕ → Fin (NQ 4)) (n : ℕ) (out : Hist (Fin (NQ 4)) n → Finset (Fin 4)),
      (∀ S, MeasurableSet {ω | out ω = S}) ∧
      1 - 1 / 100 ≤ (hist (rChan {0, 1}) (schedPolicy s) null0 n).real
        {ω | Acc (gapGain {0, 1} 1) {0, 1} 2 1 (1 / 2) null0 (out ω)} ∧
      (∀ E ∈ AmbP (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2),
        1 - 1 / 100 ≤ (hist (rChan {0, 1}) (schedPolicy s) (pairW 3 E) n).real
          {ω | Acc (gapGain {0, 1} 1) {0, 1} 2 1 (1 / 2) (pairW 3 E) (out ω)}) ∧
      (∀ q, ¬ Reach ({0, 1} : Finset (Fin 4)) 2 1 (decS q) →
        ∫⁻ ω, cntQ q n ω ∂hist (rChan {0, 1}) (schedPolicy s) null0 n = 0) := by
  have hP : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  refine ⟨?_, D_pos_hundredth, ?_⟩
  · have hsub : ({{0, 2}, {0, 3}, {1, 2}, {1, 3}} : Finset (Finset (Fin 4)))
        ⊆ AmbP (gapGain ({0, 1} : Finset (Fin 4)) 1) {0, 1} 2 1 3 (1 / 2) := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl | rfl | rfl <;>
        exact ambP_inst _ (by decide) (by decide) ⟨by decide, by decide⟩ (by decide)
    have := Finset.card_le_card hsub
    have h4 : ({{0, 2}, {0, 3}, {1, 2}, {1, 3}} : Finset (Finset (Fin 4))).card = 4 := by decide
    omega
  · obtain ⟨s, n, out, hm, h0, hE, hleg, _⟩ := pair_upper (gapGain ({0, 1} : Finset (Fin 4)) 1)
      {0, 1} 2 1 3 (1 / 2) (1 / 100) hP (gap_top _ 1 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)
    exact ⟨s, n, out, hm, h0, hE, fun q hq => hleg q hq null0⟩

end CIGAMF.P13.MarlPairCalibration

#print axioms CIGAMF.P13.MarlPairCalibration.acc_null_not_sup
#print axioms CIGAMF.P13.MarlPairCalibration.acc_pair_sup
#print axioms CIGAMF.P13.MarlPairCalibration.pair_one_lower
#print axioms CIGAMF.P13.MarlPairCalibration.pair_calibration_lower
#print axioms CIGAMF.P13.MarlPairCalibration.pairs_cover_le
#print axioms CIGAMF.P13.MarlPairCalibration.pair_legal_lower
#print axioms CIGAMF.P13.MarlPairCalibration.rnofire_gen
#print axioms CIGAMF.P13.MarlPairCalibration.err_pattern_world
#print axioms CIGAMF.P13.MarlPairCalibration.pair_upper
#print axioms CIGAMF.P13.MarlPairCalibration.pair_satisfiable
