import «LeanPaperARepairBridgeV1»
import «LeanPaperABudgetUpperV1»
import «LeanPaperA7IdealFamilyV1»
import «LeanPaperATwoArmRateV1»

/-!
# Paper A: the frontier is the optimal budgeted rate on Gaussian cells, on one class of policies

The lower half of the repair law (`LeanPaperARepairBridgeV1.frontier_rate_lower`) is over kernel
policies of the eventual class. The upper half (`LeanPaperABudgetUpperV1`) is a stream learner.
This module puts both on the same objects.

**The channel.** For a specification `P` (cells `E`, noise `σ`), `gC P` is the Gaussian channel
on `E ⊕ Unit` with a fresh dummy.
* `klq_gC_inl`: the per-query divergence is `(θ_e - λ_e)²/(2σ_e²)`; `infoAt_gC`: the kernel
  information of a design is the stream energy `pen` of its real part, in unit-variance
  coordinates; `Jt_gC`: so the kernel game is the stream game `Jval`.
* `normalize_design`: a design with mass on the dummy can be renormalised onto the cells. Both
  games scale up and the sacrifice goes down, so the frontier is attained by designs on the
  cells.

**The learner as a kernel policy.** `fixPol` is the fixed-design tracking learner with the GLR
stop, stopped and then querying the dummy (`stoppedG`), as a kernel policy (`detPol`).
* `counts_meas`, `ae_map_counts`: a predicate of the query counts holds almost surely under
  the transcript law as soon as it holds on every stream path (the count vector takes countably
  many values, so the event is measurable).
* `fix_eventual`: the policy lies in the eventual class `EventualClass t₀` at **every** horizon,
  with one burn-in `t₀` for all `δ`. At horizon `n` its real-cell counts are the stream counts
  at `min(n, τ)` (`cnt_eq_at_min`), and after the burn-in the realised design is inside the
  budget on every path (`fix_budget_eventually`).
* `fix_correct`: at a Markov horizon it is δ-correct for the answer event of the stop.
* `fix_etot_le`: its expected informative count is at most `E τ`.

**The theorem** (`frontier_optimal`). On the kernel policies of the eventual class of `gC P`:
* every δ-correct family with a common burn-in has `liminf E|N|/log(1/δ) ≥ 1/R(b)`, with no
  positivity assumption on `E|N|` (`etot_pos_of_correct` derives it);
* for every `ε ∈ (0, R(b))` the stopped fixed-design learners form such a family with
  `limsup E|N|/log(1/δ) ≤ 1/(R(b) - ε)`.
So `1/R(b)` is the optimal budgeted rate over this class, and the learner that holds a design
inside the budget attains it.
-/

namespace CIGAMF.P13.PaperARepairGauss

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperALowerKL
open CIGAMF.P13.PaperALowerGame CIGAMF.P13.PaperASacrificeDuality CIGAMF.P13.PaperARepairLaw
open CIGAMF.P13.PaperAFamilyLower CIGAMF.P13.PaperAPolicyClasses CIGAMF.P13.PaperARepairRate
open CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperARepairBridge
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7IdealLearner
open CIGAMF.P13.PaperA7IdealStop CIGAMF.P13.PaperA7IdealStopped CIGAMF.P13.PaperA7StoppedGen
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7DirectLower CIGAMF.P13.PaperABridge
open CIGAMF.P13.PaperABridgeDummy CIGAMF.P13.PaperA6OracleLearner CIGAMF.P13.PaperABudgetUpper
open CIGAMF.P13.PaperA7IdealFamily CIGAMF.P13.PaperAStrict CIGAMF.P13.PaperAGaussianKL

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans)

/-! ## 1. The Gaussian channel of a specification -/

/-- **The Gaussian channel of `P`**, cells `E` plus a fresh dummy. -/
noncomputable def gC : Channel ((E ⊕ Unit) → ℝ) (E ⊕ Unit) :=
  gChan dummyQ (liftS P.σ) (liftS_pos P.σ P.σ_pos)

theorem gC_dummy : (gC P).dummy = (dummyQ : E ⊕ Unit) := rfl

theorem klq_gC_inl (θ l : E → ℝ) (e : E) :
    (klq (gC P) (lift θ) (lift l) (Sum.inl e)).toReal = (θ e - l e) ^ 2 / (2 * P.σ e ^ 2) := by
  unfold klq gC
  rw [obsLawC_gChan, obsLawC_gChan,
    toReal_klDiv_gaussianReal _ _ _ (vq_ne_zero (liftS P.σ) (liftS_pos P.σ P.σ_pos) _)]
  simp [gaussKL, mz, lift, dummyQ, vq, liftS]
  rfl

theorem klq_gC_ne_top (θ l : E → ℝ) (q : E ⊕ Unit) : klq (gC P) (lift θ) (lift l) q ≠ ⊤ := by
  cases q with
  | inl e =>
      unfold klq gC
      rw [obsLawC_gChan, obsLawC_gChan]
      exact klDiv_gaussianReal_ne_top _ _ _ (vq_ne_zero (liftS P.σ) (liftS_pos P.σ P.σ_pos) _)
  | inr u =>
      have : (Sum.inr u : E ⊕ Unit) = (gC P).dummy := rfl
      rw [this, klq_dummy]; exact ENNReal.zero_ne_top

/-- The real part of a design on `E ⊕ Unit`. -/
def rE (w : E ⊕ Unit → ℝ) : E → ℝ := fun e => w (Sum.inl e)

/-- The design on `E ⊕ Unit` that puts nothing on the dummy. -/
def lD (w : E → ℝ) : E ⊕ Unit → ℝ := Sum.elim w (fun _ => 0)

theorem rE_lD (w : E → ℝ) : rE (lD w) = w := rfl

theorem lD_alloc (w : E → ℝ) (hw : IsAlloc w) : IsAllocG (lD w) := by
  refine ⟨fun q => ?_, ?_⟩
  · cases q with
    | inl e => exact hw.1 e
    | inr u => simp [lD]
  · rw [Fintype.sum_sum_type]; simp [lD, hw.2]

/-- **The kernel information is the stream energy.** -/
theorem infoAt_gC (θ l : E → ℝ) (w : E ⊕ Unit → ℝ) :
    infoAt (gC P) (lift θ) (lift l) w = pen (rE w) (sc P.σ θ) (sc P.σ l) := by
  unfold infoAt pen sc rE
  rw [Fintype.sum_sum_type]
  have hd : ∑ u : Unit, w (Sum.inr u) * (klq (gC P) (lift θ) (lift l) (Sum.inr u)).toReal = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    have : (Sum.inr u : E ⊕ Unit) = (gC P).dummy := rfl
    rw [this, klq_dummy]; simp
  rw [hd, add_zero, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [klq_gC_inl]
  have := (P.σ_pos e).ne'
  field_simp

/-- **The kernel game is the stream game.** -/
theorem Jt_gC (θ : E → ℝ) (A : Set (E → ℝ)) (w : E ⊕ Unit → ℝ) :
    Jt (gC P) (lift θ) (lift '' A) w = Jval (sc P.σ '' A) (rE w) (sc P.σ θ) := by
  unfold Jt Jval
  show sInf (Set.range fun l : ↥(lift '' A) => infoAt (gC P) (lift θ) l w) = _
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨l, ⟨l', hl', rfl⟩, rfl⟩
    exact ⟨sc P.σ l', ⟨l', hl', rfl⟩, (infoAt_gC P θ l' w).symm⟩
  · rintro ⟨_, ⟨l', hl', rfl⟩, rfl⟩
    exact ⟨lift l', ⟨l', hl', rfl⟩, infoAt_gC P θ l' w⟩

/-- A game value is homogeneous in the design. -/
theorem Jval_smul (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w μ : E → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 < c) : Jval Alt (fun e => c * w e) μ = c * Jval Alt w μ := by
  apply le_antisymm
  · have h := Jval_ge_scale Alt hne (fun e => c * w e) w μ (1 / c) (by positivity)
      (fun e => mul_nonneg hc.le (hw e)) (fun e => by field_simp; rfl)
    have := mul_le_mul_of_nonneg_left h hc.le
    rw [← mul_assoc, mul_one_div_cancel hc.ne', one_mul] at this
    exact this
  · exact Jval_ge_scale Alt hne w (fun e => c * w e) μ c hc.le hw (fun e => le_rfl)

/-- **Renormalising a design onto the cells.**  If a design puts mass `p < 1` on the dummy, its
real part divided by `1 - p` is a design on the cells whose two games are those of the design
divided by `1 - p`. -/
theorem normalize_design (θ : E → ℝ) (A : Set (E → ℝ)) (hne : A.Nonempty)
    (w : E ⊕ Unit → ℝ) (hw : IsAllocG w) (hp : w (Sum.inr ()) < 1) :
    ∃ v : E → ℝ, IsAlloc v ∧ ∀ B : Set (E → ℝ), B.Nonempty →
      Jval (sc P.σ '' B) v (sc P.σ θ) = Jt (gC P) (lift θ) (lift '' B) w / (1 - w (Sum.inr ())) := by
  set p := w (Sum.inr ()) with hpdef
  have hq : 0 < 1 - p := by linarith
  refine ⟨fun e => rE w e / (1 - p), ⟨fun e => div_nonneg (hw.1 _) hq.le, ?_⟩, fun B hB => ?_⟩
  · have hs := hw.2
    rw [Fintype.sum_sum_type] at hs
    simp only [Fintype.univ_unit, Finset.sum_singleton] at hs
    rw [← Finset.sum_div, div_eq_one_iff_eq hq.ne']
    unfold rE; linarith
  · rw [Jt_gC, eq_div_iff hq.ne']
    have h := Jval_smul (sc P.σ '' B) (hB.image _) (rE w) (sc P.σ θ) (fun e => hw.1 _)
      (1 / (1 - p)) (by positivity)
    have e1 : (fun e => 1 / (1 - p) * rE w e) = fun e => rE w e / (1 - p) := by
      funext e; ring
    rw [e1] at h
    rw [h]; field_simp

/-! ## 2. Count predicates are measurable -/

theorem cntQ_nat {Q : Type*} [DecidableEq Q] (q : Q) (n : ℕ) (h : Hist Q n) :
    cntQ q n h = (((Finset.univ.filter fun i : Fin n => (h i).1 = q).card : ℕ) : ℝ≥0∞) := by
  unfold cntQ
  rw [Finset.sum_boole]

theorem counts_meas {n : ℕ} (p : (E ⊕ Unit → ℝ≥0∞) → Prop) :
    MeasurableSet {x : Hist (E ⊕ Unit) n | p (fun q => cntQ q n x)} := by
  classical
  set c : Hist (E ⊕ Unit) n → (E ⊕ Unit → ℝ≥0∞) := fun x q => cntQ q n x with hc
  have hcm : Measurable c := measurable_pi_lambda _ fun q => measurable_cntQ q n
  set S0 : Set (E ⊕ Unit → ℝ≥0∞) := Set.range fun k : E ⊕ Unit → ℕ => fun q => (k q : ℝ≥0∞)
  have hS0 : S0.Countable := Set.countable_range _
  have hsub : {N | p N} ∩ Set.range c ⊆ S0 := by
    rintro _ ⟨-, x, rfl⟩
    exact ⟨fun q => (Finset.univ.filter fun i : Fin n => (x i).1 = q).card,
      funext fun q => (cntQ_nat q n x).symm⟩
  have hmeas : MeasurableSet ({N | p N} ∩ Set.range c) := (hS0.mono hsub).measurableSet
  have heq : {x : Hist (E ⊕ Unit) n | p (fun q => cntQ q n x)} = c ⁻¹' ({N | p N} ∩ Set.range c) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_range]
    exact ⟨fun h => ⟨h, x, rfl⟩, fun h => h.1⟩
  rw [heq]
  exact hcm hmeas

/-- **A count predicate that holds on every path holds almost surely under the transcript law.** -/
theorem ae_map_counts {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (f : Ω → Hist (E ⊕ Unit) n) (hf : Measurable f) (p : (E ⊕ Unit → ℝ≥0∞) → Prop)
    (h : ∀ ω, p (fun q => cntQ q n (f ω))) :
    ∀ᵐ x ∂(μ.map f), p (fun q => cntQ q n x) := by
  rw [ae_map_iff hf.aemeasurable (counts_meas p)]
  exact Filter.Eventually.of_forall h


/-! ## 3. The fixed-design learner as a kernel policy -/

section Learner

variable (a : ℝ) (ha : 0 < a) (w : E → ℝ) (hw : IsAlloc w)

/-- The stream learner that tracks the fixed design `w`. -/
noncomputable def fixL : Learner E := oLearner (constO w hw)

/-- **The kernel policy**: the learner stopped by its GLR stop at level `δ`, then the dummy. -/
noncomputable def fixPol (δ : ℝ) : Policy (E ⊕ Unit) := detPol (stoppedG P a δ (fixL w hw) ha)

theorem hist_fixPol (δ : ℝ) (m : E → ℝ) (n : ℕ) :
    hist (gC P) (fixPol P a ha w hw δ) (lift m) n
      = streamMeasure.map (runSG P a δ (fixL w hw) ha m n) :=
  (stream_eq_hist_fresh (stoppedG P a δ (fixL w hw) ha) (liftS P.σ) (liftS_pos P.σ P.σ_pos) m
    n).symm

omit [MeasurableSingletonClass E] [Nonempty E] in
theorem sum_Nc (L : Learner E) (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    ∑ e, Nc L θ P.σ t ω e = t := by
  unfold Nc NF
  push_cast
  rw [Finset.sum_comm]
  simp

/-- The real-cell counts of the stopped policy at horizon `n`: their sum is some `m ≤ min(n, τ)`,
and they are the stream counts at `m`. -/
theorem real_counts (δ : ℝ) (θ : E → ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    ∃ m : ℕ, (m : ℕ∞) ≤ tauG P a δ (fixL w hw) θ ω ∧
      (∑ q, cntQ q n (runSG P a δ (fixL w hw) ha θ n ω) * infW (gC P) q = (m : ℝ≥0∞)) ∧
      ∀ e, cntQ (Sum.inl e) n (runSG P a δ (fixL w hw) ha θ n ω)
        = ENNReal.ofReal (Nc (fixL w hw) θ P.σ m ω e) := by
  obtain ⟨m, -, hmτ, -, hcnt⟩ := cnt_eq_at_min P a δ (fixL w hw) ha θ ω n
  refine ⟨m, hmτ, ?_, hcnt⟩
  rw [Fintype.sum_sum_type]
  have hd : ∑ u : Unit, cntQ (Sum.inr u) n (runSG P a δ (fixL w hw) ha θ n ω)
      * infW (gC P) (Sum.inr u) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    have : (Sum.inr u : E ⊕ Unit) = (gC P).dummy := rfl
    simp [infW, this]
  rw [hd, add_zero]
  have hi : ∀ e, infW (gC P) (Sum.inl e) = 1 := fun e => by
    unfold infW; rw [if_neg]; exact Sum.inl_ne_inr
  simp_rw [hi, mul_one, hcnt]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by unfold Nc; exact Nat.cast_nonneg _),
    sum_Nc P, ENNReal.ofReal_natCast]

/-- **The policy is in the eventual class at every horizon, with one burn-in.** -/
theorem fix_eventual (θ : E → ℝ) (Altf : Set (E → ℝ)) (hAf : Altf.Nonempty) (Γf b : ℝ)
    (hΓf : 0 < Γf) (hb : 1 - Jval (sc P.σ '' Altf) w (sc P.σ θ) / Γf < b) :
    ∃ t₀ : ℕ, ∀ δ n,
      EventualClass (gC P) (fixPol P a ha w hw δ) (lift θ) (lift '' Altf) Γf b n t₀ := by
  obtain ⟨T, hT⟩ := fix_budget_eventually P θ w hw Altf hAf Γf hΓf b hb
  refine ⟨max T 1, fun δ n => ?_⟩
  unfold EventualClass
  rw [hist_fixPol]
  refine ae_map_counts streamMeasure (runSG P a δ (fixL w hw) ha θ n)
    (measurable_runSG P a δ (fixL w hw) ha θ n)
    (fun N => ((max T 1 : ℕ) : ℝ≥0∞) ≤ ∑ q, N q * infW (gC P) q →
      MeetsBudget (gC P) (lift θ) (lift '' Altf) Γf b N) (fun ω => ?_)
  obtain ⟨m, -, hsum, hcnt⟩ := real_counts P a ha w hw δ θ ω n
  intro ht
  rw [hsum] at ht
  have hmT : max T 1 ≤ m := by exact_mod_cast ht
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_right T 1) hmT
  have hmpos : (0 : ℝ) < m := by linarith
  have hbud : 1 - Jval (sc P.σ '' Altf) (fun e => Nc (fixL w hw) θ P.σ m ω e / m)
      (sc P.σ θ) / Γf ≤ b := hT m (le_trans (le_max_left T 1) hmT) ω
  have hJf : (1 - b) * Γf ≤ Jval (sc P.σ '' Altf)
      (fun e => Nc (fixL w hw) θ P.σ m ω e / m) (sc P.σ θ) := by
    have : 1 - b ≤ Jval (sc P.σ '' Altf) (fun e => Nc (fixL w hw) θ P.σ m ω e / m)
        (sc P.σ θ) / Γf := by linarith
    rwa [le_div_iff₀ hΓf] at this
  intro l hl
  obtain ⟨l', hl', rfl⟩ := hl
  rw [hsum]
  -- the right side dominates the real-cell part
  have hreal : ENNReal.ofReal (∑ e, Nc (fixL w hw) θ P.σ m ω e
        * (klq (gC P) (lift θ) (lift l') (Sum.inl e)).toReal)
      ≤ ∑ q, cntQ q n (runSG P a δ (fixL w hw) ha θ n ω) * klq (gC P) (lift θ) (lift l') q := by
    rw [Fintype.sum_sum_type]
    refine le_trans ?_ le_self_add
    rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (by unfold Nc; exact Nat.cast_nonneg _)
      ENNReal.toReal_nonneg)]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [hcnt e, ENNReal.ofReal_mul (by unfold Nc; exact Nat.cast_nonneg _),
      ENNReal.ofReal_toReal (klq_gC_ne_top P θ l' _)]
  -- the real-cell part is m times the energy of the realised design
  have hen : ∑ e, Nc (fixL w hw) θ P.σ m ω e * (klq (gC P) (lift θ) (lift l') (Sum.inl e)).toReal
      = m * pen (fun e => Nc (fixL w hw) θ P.σ m ω e / m) (sc P.σ θ) (sc P.σ l') := by
    unfold pen sc
    rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [klq_gC_inl]
    have := (P.σ_pos e).ne'
    field_simp
  have hpen : Jval (sc P.σ '' Altf) (fun e => Nc (fixL w hw) θ P.σ m ω e / m) (sc P.σ θ)
      ≤ pen (fun e => Nc (fixL w hw) θ P.σ m ω e / m) (sc P.σ θ) (sc P.σ l') :=
    csInf_le (Jval_bddBelow _ _ _ fun e => div_nonneg (by unfold Nc; exact Nat.cast_nonneg _)
      hmpos.le) ⟨sc P.σ l', ⟨l', hl', rfl⟩, rfl⟩
  have hc : 0 ≤ (1 - b) * Γf ∨ (1 - b) * Γf < 0 := le_or_gt _ _
  refine le_trans ?_ hreal
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul' (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [hen]
  nlinarith

/-- **Its expected informative count is at most `E τ`.** -/
theorem fix_etot_le (δ : ℝ) (θ : E → ℝ) (n : ℕ)
    (hfin : (∫⁻ ω, (tauG P a δ (fixL w hw) θ ω).toENNReal ∂streamMeasure) ≠ ⊤) :
    etot (gC P) (fixPol P a ha w hw δ) (lift θ) n
      ≤ (∫⁻ ω, (tauG P a δ (fixL w hw) θ ω).toENNReal ∂streamMeasure).toReal := by
  have hinf : ∀ q, infW (gC P) q ≠ ⊤ := fun q => by unfold infW; split_ifs <;> simp
  have hE : etot (gC P) (fixPol P a ha w hw δ) (lift θ) n
      = (∑ q, (∫⁻ x, cntQ q n x ∂hist (gC P) (fixPol P a ha w hw δ) (lift θ) n)
          * infW (gC P) q).toReal := by
    rw [toReal_infW_sum]
  rw [hE]
  refine ENNReal.toReal_mono hfin ?_
  have hswap : ∑ q, (∫⁻ x, cntQ q n x ∂hist (gC P) (fixPol P a ha w hw δ) (lift θ) n)
        * infW (gC P) q
      = ∫⁻ x, ∑ q, cntQ q n x * infW (gC P) q ∂hist (gC P) (fixPol P a ha w hw δ) (lift θ) n := by
    rw [lintegral_finsetSum _ fun q _ => (measurable_cntQ q n).mul_const _]
    exact Finset.sum_congr rfl fun q _ => (lintegral_mul_const _ (measurable_cntQ q n)).symm
  rw [hswap, hist_fixPol, lintegral_map (Finset.measurable_sum _ fun q _ =>
    (measurable_cntQ q n).mul_const _) (measurable_runSG P a δ (fixL w hw) ha θ n)]
  refine lintegral_mono fun ω => ?_
  obtain ⟨m, hmτ, hsum, -⟩ := real_counts P a ha w hw δ θ ω n
  rw [hsum, ← ENat.toENNReal_coe]
  exact ENat.toENNReal_le.mpr hmτ

end Learner

/-! ## 4. The lower bound needs no positivity assumption -/

section Positivity

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q]

/-- **A correct policy makes informative queries.** -/
theorem etot_pos_of_correct (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ l : W)
    (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist C π θ n).real S) (hl : (hist C π l n).real S ≤ δ)
    (hfin : ∀ q, klq C θ l q ≠ ⊤) (hD : 0 < (1 - δ) * Real.log (1 / δ) - Real.log 2) :
    0 < etot C π θ n := by
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have h := event_info C π n θ l S hS δ hδ hl hfin
  by_contra hneg
  push_neg at hneg
  have hzero : ∀ q, ecnt C π θ n q * (klq C θ l q).toReal = 0 := by
    intro q
    by_cases hq : q = C.dummy
    · subst hq; rw [klq_dummy]; simp
    · have hle : ecnt C π θ n q * (if q = C.dummy then 0 else 1) ≤ etot C π θ n :=
        Finset.single_le_sum (f := fun q => ecnt C π θ n q * (if q = C.dummy then 0 else 1))
          (fun q _ => mul_nonneg (ecnt_nonneg _ _ _ _ _) (by split_ifs <;> norm_num))
          (Finset.mem_univ q)
      rw [if_neg hq, mul_one] at hle
      have : ecnt C π θ n q = 0 := le_antisymm (hle.trans hneg) (ecnt_nonneg _ _ _ _ _)
      rw [this, zero_mul]
  rw [Finset.sum_congr rfl fun q _ => hzero q, Finset.sum_const_zero] at h
  have := mul_le_mul_of_nonneg_right hθ hlog
  linarith

end Positivity


/-! ## 5. Correctness at a Markov horizon, and the optimal rate -/

section Optimal

/-- **The kernel policy is δ-correct at a Markov horizon**, with the stop run at level
`δ/|Ans|`. -/
theorem fix_correct (a : ℝ) (ha : 0 < a) (w : E → ℝ) (hw : IsAlloc w) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) (δ : ℝ) (hδ : 0 < δ)
    (hfin : (∫⁻ ω, (tauG P a (δ / Fintype.card Ans) (fixL w hw) θ ω).toENNReal
      ∂streamMeasure) ≠ ⊤) :
    ∃ n : ℕ,
      1 - δ ≤ (hist (gC P) (fixPol P a ha w hw (δ / Fintype.card Ans)) (lift θ) n).real
        (ansEv P a (δ / Fintype.card Ans) Tst n) ∧
      ∀ l ∈ lift '' P.Alt Tst,
        (hist (gC P) (fixPol P a ha w hw (δ / Fintype.card Ans)) l n).real
          (ansEv P a (δ / Fintype.card Ans) Tst n) ≤ δ := by
  set c : ℝ := (Fintype.card Ans : ℝ) with hc
  have hc1 : (1 : ℝ) ≤ c := by rw [hc]; exact_mod_cast Fintype.card_pos
  set δ' := δ / c with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ (by linarith)
  have hδ'le : δ' ≤ δ := div_le_self hδ.le hc1
  obtain ⟨n, hn⟩ := markov_horizon streamMeasure (tauG P a δ' (fixL w hw) θ)
    (measurable_tauG P a δ' (fixL w hw) ha θ) hfin δ' hδ'0
  have hS := measurableSet_ansEv P a δ' ha Tst n
  have hreal : ∀ m : E → ℝ, (hist (gC P) (fixPol P a ha w hw δ') (lift m) n).real
      (ansEv P a δ' Tst n)
      = streamMeasure.real {ω | runSG P a δ' (fixL w hw) ha m n ω ∈ ansEv P a δ' Tst n} := by
    intro m
    rw [hist_fixPol, map_measureReal_apply (measurable_runSG P a δ' (fixL w hw) ha m n) hS]
    rfl
  refine ⟨n, ?_, ?_⟩
  · rw [hreal]
    have h := ansEv_true_geG P a δ' (fixL w hw) ha hδ'0 Tst θ hwrong n
    have hcast : ((Fintype.card Ans - 1 : ℕ) : ℝ) = c - 1 := by
      rw [hc, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
    rw [hcast] at h
    have e : (c - 1) * δ' + δ' = δ := by rw [hδ']; field_simp; ring
    linarith
  · rintro _ ⟨l, hl, rfl⟩
    rw [hreal]
    have h := ansEv_alt_leG P a δ' (fixL w hw) ha hδ'0 Tst l hl n
    have h2 : streamMeasure.real {ω | runSG P a δ' (fixL w hw) ha l n ω ∈ ansEv P a δ' Tst n}
        ≤ δ' := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hδ'0.le h
    linarith

/-- The frontier of the Gaussian channel of `P`. -/
noncomputable def Rg (Tst : Ans) (θ : E → ℝ) (Altf : Set (E → ℝ)) (Γ b : ℝ) : ℝ :=
  Rfront (Jt (gC P) (lift θ) (lift '' Altf)) (Jt (gC P) (lift θ) (lift '' P.Alt Tst)) Γ b

theorem hD_of_small (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ < 1 / 8) :
    0 < (1 - δ) * Real.log (1 / δ) - Real.log 2 := by
  have h := hD_small (δ / 2) (by positivity) (by linarith)
  rwa [show 2 * (δ / 2) = δ by ring] at h

/-- **Lower half: no policy of the eventual class beats `1/R(b)`.**  Every family of kernel
policies on the Gaussian channel, δ-correct for the answer `Tst` and in the eventual class with one
burn-in, has `liminf E|N|/log(1/δ) ≥ 1/R(b)`. -/
theorem optimal_lower (Tst : Ans) (θ : E → ℝ) (Altf : Set (E → ℝ)) (hAf : Altf.Nonempty)
    (Γ : ℝ) (hΓ : 0 < Γ) (wstar : E → ℝ) (hws : IsAlloc wstar)
    (hopt : Jval (sc P.σ '' Altf) wstar (sc P.σ θ) = Γ) (b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hRb : 0 < Rg P Tst θ Altf Γ b) (t₀ : ℕ) (π : ℝ → Policy (E ⊕ Unit)) (n : ℝ → ℕ)
    (S : ∀ δ, Set (Hist (E ⊕ Unit) (n δ))) (hS : ∀ δ, MeasurableSet (S δ)) (δ0 : ℝ)
    (hδ0 : 0 < δ0)
    (hθ : ∀ δ, 0 < δ → δ < δ0 → 1 - δ ≤ (hist (gC P) (π δ) (lift θ) (n δ)).real (S δ))
    (hL : ∀ δ, 0 < δ → δ < δ0 → ∀ l ∈ lift '' P.Alt Tst,
      (hist (gC P) (π δ) l (n δ)).real (S δ) ≤ δ)
    (hE : ∀ δ, 0 < δ → δ < δ0 →
      EventualClass (gC P) (π δ) (lift θ) (lift '' Altf) Γ b (n δ) t₀) :
    LowerRate (fun δ => etot (gC P) (π δ) (lift θ) (n δ)) (Rg P Tst θ Altf Γ b) := by
  obtain ⟨l0, hl0⟩ := P.Alt_ne Tst
  obtain ⟨f0, hf0⟩ := hAf
  haveI : Nonempty ↥(lift '' P.Alt Tst) := ⟨⟨lift l0, l0, hl0, rfl⟩⟩
  haveI : Nonempty ↥(lift '' Altf) := ⟨⟨lift f0, f0, hf0, rfl⟩⟩
  have hfin : ∀ l ∈ lift '' P.Alt Tst, ∀ q, klq (gC P) (lift θ) l q ≠ ⊤ := by
    rintro _ ⟨l, -, rfl⟩ q; exact klq_gC_ne_top P θ l q
  have hfinf : ∀ l ∈ lift '' Altf, ∀ q, klq (gC P) (lift θ) l q ≠ ⊤ := by
    rintro _ ⟨l, -, rfl⟩ q; exact klq_gC_ne_top P θ l q
  have hopt' : Jt (gC P) (lift θ) (lift '' Altf) (lD wstar) = Γ := by
    rw [Jt_gC, rE_lD, hopt]
  set δ1 := min δ0 (1 / 16) with hδ1
  have hδ1pos : 0 < δ1 := lt_min hδ0 (by norm_num)
  have hδ1le : δ1 ≤ 1 := (min_le_right _ _).trans (by norm_num)
  refine frontier_rate_lower (gC P) (lift θ) (lift '' P.Alt Tst) (lift '' Altf)
    ⟨lift l0, l0, hl0, rfl⟩ hfin hfinf Γ b t₀ hΓ hb0 hb1 (lD wstar) (lD_alloc wstar hws) hopt' hRb
    π n S hS δ1 hδ1pos hδ1le (fun δ h0 h1 => hθ δ h0 (lt_of_lt_of_le h1 (min_le_left _ _)))
    (fun δ h0 h1 => hL δ h0 (lt_of_lt_of_le h1 (min_le_left _ _))) (fun δ h0 h1 => ?_)
    (fun δ h0 h1 => hE δ h0 (lt_of_lt_of_le h1 (min_le_left _ _)))
  have h1' : δ < δ0 := lt_of_lt_of_le h1 (min_le_left _ _)
  have h16 : δ < 1 / 16 := lt_of_lt_of_le h1 (min_le_right _ _)
  exact etot_pos_of_correct (gC P) (π δ) (n δ) (lift θ) (lift l0) (S δ) (hS δ) δ h0
    (by linarith) (hθ δ h0 h1') (hL δ h0 h1' _ ⟨l0, hl0, rfl⟩) (klq_gC_ne_top P θ l0)
    (hD_of_small δ h0 (by linarith))

/-- **Upper half: the frontier is attained inside the class.**  For every `ε ∈ (0, R(b))` the
stopped fixed-design tracking learners, at Markov horizons, form a δ-correct family of the
eventual class with one burn-in, and `limsup E|N|/log(1/δ) ≤ 1/(R(b) - ε)`. -/
theorem optimal_upper (Tst : Ans) (θ : E → ℝ) (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T)
    (Altf : Set (E → ℝ)) (hAf : Altf.Nonempty) (Γ : ℝ) (hΓ : 0 < Γ) (wstar : E → ℝ)
    (hws : IsAlloc wstar) (hopt : Jval (sc P.σ '' Altf) wstar (sc P.σ θ) = Γ) (b : ℝ)
    (hb0 : 0 < b) (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε)
    (hεR : ε < Rg P Tst θ Altf Γ b) :
    ∃ t₀ : ℕ, ∃ π : ℝ → Policy (E ⊕ Unit), ∃ n : ℝ → ℕ,
      ∃ S : ∀ δ, Set (Hist (E ⊕ Unit) (n δ)),
      (∀ δ, MeasurableSet (S δ)) ∧
      (∀ δ, 0 < δ → δ < 1 → 1 - δ ≤ (hist (gC P) (π δ) (lift θ) (n δ)).real (S δ)) ∧
      (∀ δ, 0 < δ → δ < 1 → ∀ l ∈ lift '' P.Alt Tst,
        (hist (gC P) (π δ) l (n δ)).real (S δ) ≤ δ) ∧
      (∀ δ, EventualClass (gC P) (π δ) (lift θ) (lift '' Altf) Γ b (n δ) t₀) ∧
      UpperRate (fun δ => etot (gC P) (π δ) (lift θ) (n δ)) (Rg P Tst θ Altf Γ b - ε) := by
  classical
  set R := Rg P Tst θ Altf Γ b with hRdef
  obtain ⟨l0, hl0⟩ := P.Alt_ne Tst
  haveI : Nonempty ↥(lift '' P.Alt Tst) := ⟨⟨lift l0, l0, hl0, rfl⟩⟩
  obtain ⟨f0, hf0⟩ := hAf
  haveI : Nonempty ↥(lift '' Altf) := ⟨⟨lift f0, f0, hf0, rfl⟩⟩
  have hopt' : Jt (gC P) (lift θ) (lift '' Altf) (lD wstar) = Γ := by
    rw [Jt_gC, rE_lD, hopt]
  -- a design strictly inside the budget, near the frontier
  obtain ⟨wh, hwh, hsac, hJwh⟩ := near_design (Jt (gC P) (lift θ) (lift '' Altf))
    (Jt (gC P) (lift θ) (lift '' P.Alt Tst)) Γ _
    (fun w hw => Jt_le_sum (gC P) (lift θ) (lift '' P.Alt Tst) ⟨lift l0, l0, hl0, rfl⟩ w hw)
    (lD wstar) (lD_alloc wstar hws) hopt' hΓ
    (fun a b ha hb β h0 h1 => Jt_concave (gC P) (lift θ) (lift '' Altf) a b ha hb β h0 h1)
    (fun a b ha hb β h0 h1 => Jt_concave (gC P) (lift θ) (lift '' P.Alt Tst) a b ha hb β h0 h1)
    b hb0 (ε / 2) (by linarith)
  have hJwh' : R - ε / 2 < Jt (gC P) (lift θ) (lift '' P.Alt Tst) wh := hJwh
  -- it does not sit on the dummy
  have hJt0 : 0 < Jt (gC P) (lift θ) (lift '' P.Alt Tst) wh := by linarith
  have hp : wh (Sum.inr ()) < 1 := by
    by_contra hp1
    push_neg at hp1
    have hsum := hwh.2
    rw [Fintype.sum_sum_type] at hsum
    simp only [Fintype.univ_unit, Finset.sum_singleton] at hsum
    have hreal0 : ∀ e, wh (Sum.inl e) = 0 := by
      have hle : ∑ e, wh (Sum.inl e) ≤ 0 := by linarith
      have hnn : ∀ e ∈ Finset.univ, 0 ≤ wh (Sum.inl e) := fun e _ => hwh.1 _
      intro e
      exact le_antisymm ((Finset.single_le_sum hnn (Finset.mem_univ e)).trans hle) (hwh.1 _)
    have hz : Jt (gC P) (lift θ) (lift '' P.Alt Tst) wh = 0 := by
      rw [Jt_gC]
      have hr : rE wh = fun _ => 0 := funext hreal0
      rw [hr]
      unfold Jval
      have hpen : ∀ ν, pen (fun _ : E => (0 : ℝ)) (sc P.σ θ) ν = 0 := fun ν => by simp [pen]
      have : pen (fun _ : E => (0 : ℝ)) (sc P.σ θ) '' (sc P.σ '' P.Alt Tst) = {0} := by
        ext x
        simp only [Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro ⟨ν, -, rfl⟩; exact hpen ν
        · rintro rfl; exact ⟨sc P.σ l0, ⟨l0, hl0, rfl⟩, hpen _⟩
      rw [this, csInf_singleton]
    linarith
  -- renormalise onto the cells
  obtain ⟨v, hv, hvJ⟩ := normalize_design P θ (P.Alt Tst) ⟨l0, hl0⟩ wh hwh hp
  set p := wh (Sum.inr ()) with hpdef
  have hp0 : 0 ≤ p := hwh.1 _
  have hq : 0 < 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hJv : Jt (gC P) (lift θ) (lift '' P.Alt Tst) wh ≤ Jval (sc P.σ '' P.Alt Tst) v (sc P.σ θ) := by
    rw [hvJ (P.Alt Tst) ⟨l0, hl0⟩, le_div_iff₀ hq]
    nlinarith
  have hJfv : Jt (gC P) (lift θ) (lift '' Altf) wh ≤ Jval (sc P.σ '' Altf) v (sc P.σ θ) := by
    rw [hvJ Altf ⟨f0, hf0⟩, le_div_iff₀ hq]
    have := Jt_nonneg (gC P) (lift θ) (lift '' Altf) wh hwh.1
    nlinarith
  have hbv : 1 - Jval (sc P.σ '' Altf) v (sc P.σ θ) / Γ < b := by
    have h1 : Jt (gC P) (lift θ) (lift '' Altf) wh / Γ ≤ Jval (sc P.σ '' Altf) v (sc P.σ θ) / Γ :=
      div_le_div_of_nonneg_right hJfv hΓ.le
    unfold sac at hsac
    linarith
  -- the true game of the design, and the slack
  have hJw : R - ε / 2 < Jw P Tst θ v := lt_of_lt_of_le hJwh' hJv
  set η := Jw P Tst θ v - (R - ε) with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hηJ : η < Jw P Tst θ v := by rw [hη]; linarith
  have hJpos : 0 < Jw P Tst θ v := by linarith
  obtain ⟨A, hA⟩ := fix_expect_bound P a ha Tst θ v hv hJpos η hη0 hηJ
  obtain ⟨t₀, ht₀⟩ := fix_eventual P a ha v hv θ Altf ⟨f0, hf0⟩ Γ b hΓ hbv
  set c : ℝ := (Fintype.card Ans : ℝ) with hc
  have hc1 : (1 : ℝ) ≤ c := by rw [hc]; exact_mod_cast Fintype.card_pos
  have hex : ∀ δ : ℝ, ∃ m : ℕ, 0 < δ → δ < 1 →
      1 - δ ≤ (hist (gC P) (fixPol P a ha v hv (δ / c)) (lift θ) m).real
        (ansEv P a (δ / c) Tst m) ∧
      ∀ l ∈ lift '' P.Alt Tst,
        (hist (gC P) (fixPol P a ha v hv (δ / c)) l m).real (ansEv P a (δ / c) Tst m) ≤ δ := by
    intro δ
    by_cases hδ : 0 < δ ∧ δ < 1
    · have hδc0 : 0 < δ / c := div_pos hδ.1 (by linarith)
      have hδc1 : δ / c < 1 := lt_of_le_of_lt (div_le_self hδ.1.le hc1) hδ.2
      obtain ⟨m, hm⟩ := fix_correct P a ha v hv Tst θ hwrong δ hδ.1 (hA _ hδc0 hδc1).1
      exact ⟨m, fun _ _ => hm⟩
    · exact ⟨0, fun h0 h1 => absurd ⟨h0, h1⟩ hδ⟩
  choose nf hnf using hex
  refine ⟨t₀, fun δ => fixPol P a ha v hv (δ / c), nf, fun δ => ansEv P a (δ / c) Tst (nf δ),
    fun δ => measurableSet_ansEv P a (δ / c) ha Tst (nf δ), fun δ h0 h1 => (hnf δ h0 h1).1,
    fun δ h0 h1 => (hnf δ h0 h1).2, fun δ => ht₀ (δ / c) (nf δ), ?_⟩
  -- the rate
  have hRε : 0 < R - ε := by linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
  refine CIGAMF.P13.PaperA7UpperChain.upper_rate_of_bound _ _ hRε fun η' hη' hη'R =>
    ⟨A + Real.log c / (R - ε), fun δ hδ hδ1 => ?_⟩
  have hδc0 : 0 < δ / c := div_pos hδ (by linarith)
  have hδc1 : δ / c < 1 := lt_of_le_of_lt (div_le_self hδ.le hc1) hδ1
  have hE := hA _ hδc0 hδc1
  have hEt : etot (gC P) (fixPol P a ha v hv (δ / c)) (lift θ) (nf δ)
      ≤ (∫⁻ ω, (tauG P a (δ / c) (oLearner (constO v hv)) θ ω).toENNReal
        ∂streamMeasure).toReal := fix_etot_le P a ha v hv (δ / c) θ (nf δ) hE.1
  have hlog : Real.log (1 / (δ / c)) = Real.log (1 / δ) + Real.log c := by
    rw [show 1 / (δ / c) = (1 / δ) * c by field_simp,
      Real.log_mul (by positivity) (by linarith)]
  have hJeq : Jw P Tst θ v - η = R - ε := by rw [hη]; ring
  rw [hJeq, hlog] at hE
  have hl0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hmono : Real.log (1 / δ) / (R - ε) ≤ Real.log (1 / δ) / (R - ε - η') :=
    div_le_div_of_nonneg_left hl0 (by linarith) (by linarith)
  have hsplit : (Real.log (1 / δ) + Real.log c) / (R - ε)
      = Real.log (1 / δ) / (R - ε) + Real.log c / (R - ε) := add_div _ _ _
  show etot (gC P) (fixPol P a ha v hv (δ / c)) (lift θ) (nf δ)
    ≤ Real.log (1 / δ) / (R - ε - η') + (A + Real.log c / (R - ε))
  linarith [hE.2]

end Optimal


/-! ## 6. The hypotheses are satisfiable: two Gaussian arms -/

section TwoArms

open CIGAMF.P13.PaperATwoArmRate

/-- **Every hypothesis of `optimal_lower` and `optimal_upper` holds on two Gaussian arms**, with
the frozen surrogate that lets only the leader move: the answer is unique, the frozen optimum
`(1, 0)` attains `Γ = Δ²/2`, and the frontier is positive at every budget `b ∈ (0, 1/2]`. -/
theorem optimal_satisfiable (θ : Fin 2 → ℝ) (hθ : θ 1 < θ 0) (b : ℝ) (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 2) :
    (∀ T, T ≠ 0 → θ ∈ twoSpec.Alt T) ∧ (altFrozen (θ 1)).Nonempty ∧ IsAlloc (wb 0)
      ∧ Jval (sc twoSpec.σ '' altFrozen (θ 1)) (wb 0) (sc twoSpec.σ θ) = (θ 0 - θ 1) ^ 2 / 2
      ∧ 0 < (θ 0 - θ 1) ^ 2 / 2
      ∧ 0 < Rg twoSpec 0 θ (altFrozen (θ 1)) ((θ 0 - θ 1) ^ 2 / 2) b := by
  have hΔ : 0 < θ 0 - θ 1 := by linarith
  have hΓ : 0 < (θ 0 - θ 1) ^ 2 / 2 := by positivity
  have hw0 := wb_alloc 0 le_rfl zero_le_one
  have hwb := wb_alloc b hb0.le (by linarith)
  have hJf0 : Jval (sc twoSpec.σ '' altFrozen (θ 1)) (wb 0) (sc twoSpec.σ θ)
      = (θ 0 - θ 1) ^ 2 / 2 := by
    rw [jf_two θ (wb 0) hθ.le hw0]; simp only [wb, Matrix.cons_val_zero]; ring
  refine ⟨fun T hT => ?_, ⟨fun _ => θ 1, by simp [altFrozen]⟩, hw0, hJf0, hΓ, ?_⟩
  · have hT1 : T = 1 := by omega
    subst hT1
    show θ 1 ≤ θ (1 - 1)
    simpa using hθ.le
  · obtain ⟨l0, hl0⟩ := twoSpec.Alt_ne 0
    haveI : Nonempty ↥(lift '' twoSpec.Alt 0) := ⟨⟨lift l0, l0, hl0, rfl⟩⟩
    have hJt : Jt (gC twoSpec) (lift θ) (lift '' twoSpec.Alt 0) (lD (wb b))
        = b * (1 - b) * (θ 0 - θ 1) ^ 2 / 2 := by
      rw [Jt_gC, rE_lD]
      have := jw_two θ (wb b) hθ.le hwb
      unfold Jw at this
      rw [this]; simp only [wb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring
    have hsac : sac (Jt (gC twoSpec) (lift θ) (lift '' altFrozen (θ 1))) ((θ 0 - θ 1) ^ 2 / 2)
        (lD (wb b)) ≤ b := by
      unfold sac
      rw [Jt_gC, rE_lD, jf_two θ (wb b) hθ.le hwb]
      simp only [wb, Matrix.cons_val_zero]
      field_simp
      ring_nf
      exact le_rfl
    have hle := R_le (Jt (gC twoSpec) (lift θ) (lift '' altFrozen (θ 1)))
      (Jt (gC twoSpec) (lift θ) (lift '' twoSpec.Alt 0)) ((θ 0 - θ 1) ^ 2 / 2) _
      (fun w hw => Jt_le_sum (gC twoSpec) (lift θ) (lift '' twoSpec.Alt 0)
        ⟨lift l0, l0, hl0, rfl⟩ w hw) b (lD (wb b)) (lD_alloc (wb b) hwb) hsac
    rw [hJt] at hle
    have : 0 < b * (1 - b) * (θ 0 - θ 1) ^ 2 / 2 := by
      have : 0 < 1 - b := by linarith
      positivity
    exact lt_of_lt_of_le this hle

end TwoArms

#print axioms klq_gC_inl
#print axioms infoAt_gC
#print axioms Jt_gC
#print axioms normalize_design
#print axioms ae_map_counts
#print axioms real_counts
#print axioms fix_eventual
#print axioms fix_etot_le
#print axioms etot_pos_of_correct
#print axioms fix_correct
#print axioms optimal_lower
#print axioms optimal_upper
#print axioms optimal_satisfiable

end CIGAMF.P13.PaperARepairGauss
