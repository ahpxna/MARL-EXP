import «LeanPaperBObstructionLawV1»
import «LeanPaperBScheduleV1»

/-!
# Paper B: pairwise likelihood-ratio tests on every channel, and the unconditional upper law

`tournament_law` (`LeanPaperBObstructionLawV1`) turns pairwise tests of exponent `c kappa` into a
safe decision, but it takes the tests as a hypothesis.  This module builds them on EVERY channel
in protocol form and discharges that hypothesis with the Hellinger information.

* `bc C w v q`: the Bhattacharyya coefficient `∫ sqrt(p_w p_v)` of query `q`; `bc_le_one`,
  `bc_symm`, `bc_dummy` (`= 1`: the dummy carries nothing).  `hel = 1 - bc`, in `[0, 1]`.
* `lintegral_sqrt_ratio`: under world `w`, the mean of `sqrt(p_v/p_w)` is `bc`.
* `lintegral_prod_sched`: on a scheduled policy the history law integrates a product of
  per-round functions of the observations to the product of their means.  No independence
  statement about the recursion is used; it is proved on the recursion.
* `block_error`: the likelihood-ratio test on a block of rounds prefers the wrong world with
  probability at most the product of the block's coefficients (Markov on `sqrt(LR)`).
* `bc_pow_le`: `bc^n <= exp(-n hel)`.
-/

namespace CIGAMF.P13.PaperBHellingerTest

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperBSchedule
open CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBObstructionLaw

/-! ## 1. The Bhattacharyya coefficient of a query -/

section Affinity

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- The Bhattacharyya coefficient of query `q` between worlds `w` and `v`. -/
noncomputable def bc (C : Channel W Q) (w v : W) (q : Q) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (Real.sqrt (C.dens w q y * C.dens v q y))

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem bc_symm (C : Channel W Q) (w v : W) (q : Q) : bc C w v q = bc C v w q := by
  unfold bc
  simp_rw [mul_comm (C.dens w q _)]

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem sqrt_mul_le_avg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ a / 2 + b / 2 := by
  calc Real.sqrt (a * b) ≤ Real.sqrt ((a / 2 + b / 2) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)])
    _ = a / 2 + b / 2 := Real.sqrt_sq (by positivity)

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
/-- **The coefficient is at most one**, by `sqrt(ab) <= (a+b)/2` and unit mass. -/
theorem bc_le_one (C : Channel W Q) (w v : W) (q : Q) : bc C w v q ≤ 1 := by
  unfold bc
  have hpt : ∀ y, ENNReal.ofReal (Real.sqrt (C.dens w q y * C.dens v q y))
      ≤ ENNReal.ofReal (C.dens w q y) * 2⁻¹ + ENNReal.ofReal (C.dens v q y) * 2⁻¹ := by
    intro y
    have ha := (C.pos w q y).le
    have hb := (C.pos v q y).le
    refine (ENNReal.ofReal_le_ofReal (sqrt_mul_le_avg _ _ ha hb)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_div_of_pos two_pos,
      ENNReal.ofReal_ofNat, div_eq_mul_inv, div_eq_mul_inv]
  have hmw : Measurable fun y => ENNReal.ofReal (C.dens w q y) := (C.meas w q).ennreal_ofReal
  have hmv : Measurable fun y => ENNReal.ofReal (C.dens v q y) := (C.meas v q).ennreal_ofReal
  calc ∫⁻ y, ENNReal.ofReal (Real.sqrt (C.dens w q y * C.dens v q y))
      ≤ ∫⁻ y, (ENNReal.ofReal (C.dens w q y) * 2⁻¹ + ENNReal.ofReal (C.dens v q y) * 2⁻¹) :=
        lintegral_mono hpt
    _ = (∫⁻ y, ENNReal.ofReal (C.dens w q y)) * 2⁻¹
          + (∫⁻ y, ENNReal.ofReal (C.dens v q y)) * 2⁻¹ := by
        rw [lintegral_add_left (hmw.mul_const _), lintegral_mul_const _ hmw,
          lintegral_mul_const _ hmv]
    _ = 1 := by rw [C.mass w q, C.mass v q, one_mul, ENNReal.inv_two_add_inv_two]

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem bc_ne_top (C : Channel W Q) (w v : W) (q : Q) : bc C w v q ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (bc_le_one C w v q)

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
/-- **The dummy carries nothing**: its coefficient is one. -/
theorem bc_dummy (C : Channel W Q) (w v : W) : bc C w v C.dummy = 1 := by
  unfold bc
  have : ∀ y, ENNReal.ofReal (Real.sqrt (C.dens w C.dummy y * C.dens v C.dummy y))
      = ENNReal.ofReal (C.dens w C.dummy y) := by
    intro y
    rw [← C.dummy_same w v y, ← sq, Real.sqrt_sq (C.pos w C.dummy y).le]
  simp_rw [this]
  exact C.mass w C.dummy

/-- The squared Hellinger distance of a query, `1 - bc`. -/
noncomputable def hel (C : Channel W Q) (w v : W) (q : Q) : ℝ := 1 - (bc C w v q).toReal

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem hel_nonneg (C : Channel W Q) (w v : W) (q : Q) : 0 ≤ hel C w v q := by
  unfold hel
  have : (bc C w v q).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using bc_le_one C w v q)
  linarith

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem hel_le_one (C : Channel W Q) (w v : W) (q : Q) : hel C w v q ≤ 1 := by
  unfold hel
  linarith [ENNReal.toReal_nonneg (a := bc C w v q)]

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem hel_symm (C : Channel W Q) (w v : W) (q : Q) : hel C w v q = hel C v w q := by
  unfold hel; rw [bc_symm]

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem hel_dummy (C : Channel W Q) (w v : W) : hel C w v C.dummy = 0 := by
  unfold hel; rw [bc_dummy]; simp

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem bc_eq_hel (C : Channel W Q) (w v : W) (q : Q) :
    bc C w v q = ENNReal.ofReal (1 - hel C w v q) := by
  unfold hel
  rw [sub_sub_cancel, ENNReal.ofReal_toReal (bc_ne_top C w v q)]

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
/-- **`bc^n <= exp(-n hel)`.** -/
theorem bc_pow_le (C : Channel W Q) (w v : W) (q : Q) (n : ℕ) :
    bc C w v q ^ n ≤ ENNReal.ofReal (Real.exp (-(n * hel C w v q))) := by
  rw [bc_eq_hel, ← ENNReal.ofReal_pow (by linarith [hel_le_one C w v q])]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 1 - hel C w v q ≤ Real.exp (-hel C w v q) := by
    linarith [Real.add_one_le_exp (-hel C w v q)]
  calc (1 - hel C w v q) ^ n ≤ Real.exp (-hel C w v q) ^ n :=
        pow_le_pow_left₀ (by linarith [hel_le_one C w v q]) h1 n
    _ = Real.exp (-(n * hel C w v q)) := by
        rw [← Real.exp_nat_mul]; ring_nf

/-! ## 2. One round: the mean of `sqrt(p_v / p_w)` under `w` -/

theorem measurable_sqrt_ratio (C : Channel W Q) (w v : W) (q : Q) :
    Measurable fun y => ENNReal.ofReal (Real.sqrt (C.dens v q y / C.dens w q y)) :=
  (Real.continuous_sqrt.measurable.comp ((C.meas v q).div (C.meas w q))).ennreal_ofReal

theorem lintegral_sqrt_ratio (C : Channel W Q) (w v : W) (q : Q) :
    ∫⁻ y, ENNReal.ofReal (Real.sqrt (C.dens v q y / C.dens w q y)) ∂obsLawC C w q
      = bc C w v q := by
  unfold obsLawC
  rw [lintegral_withDensity_eq_lintegral_mul _ (C.meas w q).ennreal_ofReal
    (measurable_sqrt_ratio C w v q)]
  unfold bc
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  have hw := C.pos w q y
  have hv := C.pos v q y
  rw [← ENNReal.ofReal_mul hw.le]
  congr 1
  have e : C.dens w q y * C.dens v q y = C.dens w q y ^ 2 * (C.dens v q y / C.dens w q y) := by
    field_simp
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hw.le]

/-! ## 3. Products along a scheduled history -/

/-- **The product rule on a scheduled policy.**  The history law integrates a product of
per-round functions of the observations to the product of the per-round means. -/
theorem lintegral_prod_sched (C : Channel W Q) (sched : ℕ → Q) (w : W) (f : ℕ → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∀ n, ∫⁻ ω, ∏ i : Fin n, f i (ω i).2 ∂hist C (schedPolicy sched) w n
      = ∏ i : Fin n, ∫⁻ y, f i y ∂obsLawC C w (sched i)
  | 0 => by
      haveI := hist_prob C (schedPolicy sched) w 0
      simp
  | n + 1 => by
      haveI := hist_prob C (schedPolicy sched) w n
      haveI := (schedPolicy sched).markov n
      haveI := obsKernel_markov C w n
      have hGn : Measurable fun ω : Hist Q n => ∏ i : Fin n, f i (ω i).2 :=
        Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_snd.comp (measurable_pi_apply i))
      have hGs : Measurable fun ω : Hist Q (n + 1) => ∏ i : Fin (n + 1), f i (ω i).2 :=
        Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_snd.comp (measurable_pi_apply i))
      simp only [hist]
      rw [lintegral_map hGs (measurable_snocMap n)]
      have hsplit : ∀ p : (Hist Q n × Q) × ℝ,
          ∏ i : Fin (n + 1), f i ((snocMap n p) i).2
            = (∏ i : Fin n, f i (p.1.1 i).2) * f n p.2 := by
        intro p
        rw [Fin.prod_univ_castSucc]
        simp [snocMap, Fin.snoc_castSucc, Fin.snoc_last]
      simp_rw [hsplit]
      have hmstep : Measurable fun p : (Hist Q n × Q) × ℝ =>
          (∏ i : Fin n, f i (p.1.1 i).2) * f n p.2 :=
        (hGn.comp measurable_fst.fst).mul ((hf n).comp measurable_snd)
      rw [Measure.lintegral_compProd hmstep]
      have hin : ∀ x : Hist Q n × Q,
          ∫⁻ y, (∏ i : Fin n, f i (x.1 i).2) * f n y ∂obsKernel C w n x
            = (∏ i : Fin n, f i (x.1 i).2) * ∫⁻ y, f n y ∂obsLawC C w x.2 := by
        intro x
        rw [lintegral_const_mul _ (hf n), obsKernel_apply]
      simp_rw [hin]
      have hm2 : Measurable fun x : Hist Q n × Q =>
          (∏ i : Fin n, f i (x.1 i).2) * ∫⁻ y, f n y ∂obsLawC C w x.2 :=
        (hGn.comp measurable_fst).mul
          ((Measurable.of_discrete (f := fun q : Q => ∫⁻ y, f n y ∂obsLawC C w q)).comp
            measurable_snd)
      rw [Measure.lintegral_compProd hm2]
      have hstep : ∀ a : Hist Q n,
          ∫⁻ q, (∏ i : Fin n, f i (a i).2) * ∫⁻ y, f n y ∂obsLawC C w q
              ∂((schedPolicy sched).step n a)
            = (∏ i : Fin n, f i (a i).2) * ∫⁻ y, f n y ∂obsLawC C w (sched n) := by
        intro a
        show ∫⁻ q, _ ∂(Kernel.deterministic (fun _ => sched n) measurable_const a) = _
        rw [Kernel.deterministic_apply, lintegral_dirac]
      simp_rw [hstep]
      rw [lintegral_mul_const _ hGn, lintegral_prod_sched C sched w f hf n, Fin.prod_univ_castSucc]
      simp

/-! ## 4. The likelihood-ratio test on a block of rounds -/

/-- The factor of the test statistic at round `k`: `sqrt(p_v/p_w)` inside the block, one outside. -/
noncomputable def lrFac (C : Channel W Q) (sched : ℕ → Q) (w v : W) (blk : ℕ → Prop)
    [DecidablePred blk] (k : ℕ) (y : ℝ) : ℝ≥0∞ :=
  if blk k then ENNReal.ofReal (Real.sqrt (C.dens v (sched k) y / C.dens w (sched k) y)) else 1

theorem measurable_lrFac (C : Channel W Q) (sched : ℕ → Q) (w v : W) (blk : ℕ → Prop)
    [DecidablePred blk] (k : ℕ) : Measurable (lrFac C sched w v blk k) := by
  unfold lrFac
  split_ifs
  · exact measurable_sqrt_ratio C w v (sched k)
  · exact measurable_const

/-- The rounds of a horizon that lie in the block. -/
def blockSet (H : ℕ) (blk : ℕ → Prop) [DecidablePred blk] : Finset (Fin H) :=
  Finset.univ.filter fun i : Fin H => blk i

/-- **The block test's error.**  Under world `w`, the event that the block's likelihood of `v` is
at least that of `w` has probability at most the product of the block's coefficients. -/
theorem block_error (C : Channel W Q) (sched : ℕ → Q) (w v : W) (H : ℕ) (blk : ℕ → Prop)
    [DecidablePred blk] :
    hist C (schedPolicy sched) w H
        {ω | ∏ i ∈ blockSet H blk, C.dens w (sched i) (ω i).2
          ≤ ∏ i ∈ blockSet H blk, C.dens v (sched i) (ω i).2}
      ≤ ∏ i ∈ blockSet H blk, bc C w v (sched i) := by
  haveI := hist_prob C (schedPolicy sched) w H
  set G : Hist Q H → ℝ≥0∞ := fun ω => ∏ i : Fin H, lrFac C sched w v blk i (ω i).2 with hG
  have hGm : Measurable G :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_lrFac C sched w v blk i).comp (measurable_snd.comp (measurable_pi_apply i))
  have hint : ∫⁻ ω, G ω ∂hist C (schedPolicy sched) w H
      = ∏ i ∈ blockSet H blk, bc C w v (sched i) := by
    rw [hG, lintegral_prod_sched C sched w _ (measurable_lrFac C sched w v blk) H]
    unfold blockSet
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold lrFac
    split_ifs
    · exact lintegral_sqrt_ratio C w v (sched i)
    · simp
  have hsub : {ω : Hist Q H | ∏ i ∈ blockSet H blk, C.dens w (sched i) (ω i).2
        ≤ ∏ i ∈ blockSet H blk, C.dens v (sched i) (ω i).2} ⊆ {ω | 1 ≤ G ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hpos : ∀ i ∈ blockSet H blk, 0 < C.dens w (sched i) (ω i).2 :=
      fun i _ => C.pos _ _ _
    have hGω : G ω = ENNReal.ofReal (∏ i ∈ blockSet H blk,
        Real.sqrt (C.dens v (sched i) (ω i).2 / C.dens w (sched i) (ω i).2)) := by
      rw [ENNReal.ofReal_prod_of_nonneg fun i _ => Real.sqrt_nonneg _, hG]
      unfold blockSet
      rw [Finset.prod_filter]
      rfl
    rw [hGω, ENNReal.one_le_ofReal]
    set P := ∏ i ∈ blockSet H blk,
      Real.sqrt (C.dens v (sched i) (ω i).2 / C.dens w (sched i) (ω i).2) with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
    have hP2 : P ^ 2 = (∏ i ∈ blockSet H blk, C.dens v (sched i) (ω i).2)
        / ∏ i ∈ blockSet H blk, C.dens w (sched i) (ω i).2 := by
      rw [hP, ← Finset.prod_pow, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact Real.sq_sqrt (div_nonneg (C.pos _ _ _).le (C.pos _ _ _).le)
    have hden : 0 < ∏ i ∈ blockSet H blk, C.dens w (sched i) (ω i).2 := Finset.prod_pos hpos
    have h1 : 1 ≤ P ^ 2 := by rw [hP2, one_le_div hden]; exact hω
    nlinarith
  calc hist C (schedPolicy sched) w H _ ≤ hist C (schedPolicy sched) w H {ω | 1 ≤ G ω} :=
        measure_mono hsub
    _ = 1 * hist C (schedPolicy sched) w H {ω | 1 ≤ G ω} := (one_mul _).symm
    _ ≤ ∫⁻ ω, G ω ∂hist C (schedPolicy sched) w H := mul_meas_ge_le_lintegral₀ hGm.aemeasurable 1
    _ = _ := hint

end Affinity

/-! ## 5. The tournament on a channel -/

section Tournament

variable {W Q A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
  [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] [Fintype Q]

/-- The Hellinger information of query `q`, as an `ℝ≥0`. -/
noncomputable def helNN (C : Channel W Q) (w v : W) (q : Q) : ℝ≥0 :=
  ⟨hel C w v q, hel_nonneg C w v q⟩

/-- **The Hellinger information of a pair**: that of its best query. -/
noncomputable def kH (C : Channel W Q) (w v : W) : ℝ≥0 := Finset.univ.sup (helNN C w v)

omit [Fintype W] [DecidableEq W] [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] in
theorem kH_symm (C : Channel W Q) (w v : W) : kH C w v = kH C v w := by
  unfold kH
  congr 1
  funext q
  exact Subtype.ext (hel_symm C w v q)

omit [Fintype W] [DecidableEq W] [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] in
theorem exists_best (C : Channel W Q) (w v : W) :
    ∃ q ∈ (Finset.univ : Finset Q), ∀ q' ∈ (Finset.univ : Finset Q), helNN C w v q' ≤ helNN C w v q :=
  Finset.exists_max_image _ _ ⟨C.dummy, Finset.mem_univ _⟩

/-- A best query of the pair. -/
noncomputable def qStar (C : Channel W Q) (w v : W) : Q := Classical.choose (exists_best C w v)

omit [Fintype W] [DecidableEq W] [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] in
theorem hel_qStar (C : Channel W Q) (w v : W) : hel C w v (qStar C w v) = kH C w v := by
  have h := (Classical.choose_spec (exists_best C w v)).2
  have : helNN C w v (qStar C w v) = kH C w v :=
    le_antisymm (Finset.le_sup (Finset.mem_univ _))
      (Finset.sup_le fun q _ => h q (Finset.mem_univ q))
  exact congrArg Subtype.val this

/-- A rank on the worlds, to orient each pair once. -/
noncomputable def rk (u : W) : ℕ := (Fintype.equivFin W u : ℕ)

omit [DecidableEq W] in
theorem rk_inj {u v : W} (h : rk u = rk v) : u = v :=
  (Fintype.equivFin W).injective (Fin.ext h)

/-- The oriented representative of the unordered pair `{u, v}`. -/
noncomputable def canon (u v : W) : W × W := if rk u < rk v then (u, v) else (v, u)

omit [DecidableEq W] in
theorem canon_symm {u v : W} (hne : u ≠ v) : canon u v = canon v u := by
  unfold canon
  have hr : rk u ≠ rk v := fun h => hne (rk_inj h)
  by_cases h1 : rk u < rk v
  · have h2 : ¬ rk v < rk u := by omega
    rw [if_pos h1, if_neg h2]
  · have h2 : rk v < rk u := by omega
    rw [if_neg h1, if_pos h2]

omit [DecidableEq W] in
theorem canon_cases (u v : W) : canon u v = (u, v) ∨ canon u v = (v, u) := by
  unfold canon; split_ifs <;> simp

omit [DecidableEq W] in
theorem canon_lt {u v : W} (hne : u ≠ v) : rk (canon u v).1 < rk (canon u v).2 := by
  unfold canon
  have hr : rk u ≠ rk v := fun h => hne (rk_inj h)
  split_ifs with h
  · exact h
  · simp only; omega

/-- The index of an ordered pair. -/
noncomputable def pidx (p : W × W) : ℕ := (Fintype.equivFin (W × W) p : ℕ)

omit [DecidableEq W] in
theorem pidx_lt (p : W × W) : pidx p < Fintype.card (W × W) := (Fintype.equivFin (W × W) p).isLt

omit [DecidableEq W] in
theorem pidx_symm (p : W × W) (h : pidx p < Fintype.card (W × W)) :
    (Fintype.equivFin (W × W)).symm ⟨pidx p, h⟩ = p := by
  unfold pidx
  exact (Fintype.equivFin (W × W)).symm_apply_apply p

/-- **The tournament's schedule.**  Round `i` belongs to block `i / n`; the block of an oriented
pair tested at threshold `t` queries that pair's best query, every other block the dummy. -/
noncomputable def tSched (C : Channel W Q) (t : ℝ≥0) (n : ℕ) (i : ℕ) : Q :=
  if h : i / n < Fintype.card (W × W) then
    (if rk ((Fintype.equivFin (W × W)).symm ⟨i / n, h⟩).1
          < rk ((Fintype.equivFin (W × W)).symm ⟨i / n, h⟩).2
        ∧ t ≤ kH C ((Fintype.equivFin (W × W)).symm ⟨i / n, h⟩).1
          ((Fintype.equivFin (W × W)).symm ⟨i / n, h⟩).2
      then qStar C ((Fintype.equivFin (W × W)).symm ⟨i / n, h⟩).1
        ((Fintype.equivFin (W × W)).symm ⟨i / n, h⟩).2
      else C.dummy)
  else C.dummy

/-- The block of the pair `{u, v}`. -/
def pblk (n : ℕ) (u v : W) : ℕ → Prop := fun i => i / n = pidx (canon u v)

noncomputable instance (n : ℕ) (u v : W) : DecidablePred (pblk n u v) :=
  fun i => inferInstanceAs (Decidable (i / n = pidx (canon u v)))

/-- The likelihood of world `x` on the block of `{u, v}`. -/
noncomputable def lik (C : Channel W Q) (t : ℝ≥0) (n : ℕ) (x u v : W)
    (ω : Hist Q (Fintype.card (W × W) * n)) : ℝ :=
  ∏ i ∈ blockSet (Fintype.card (W × W) * n) (pblk n u v), C.dens x (tSched C t n i) (ω i).2

/-- **`u` beats `v`**: its likelihood on their block is at least `v`'s, ties to the lower rank. -/
noncomputable def beatH (C : Channel W Q) (t : ℝ≥0) (n : ℕ) (u v : W) :
    Set (Hist Q (Fintype.card (W × W) * n)) :=
  if rk u < rk v then {ω | lik C t n v u v ω ≤ lik C t n u u v ω}
  else {ω | lik C t n v u v ω < lik C t n u u v ω}

omit [Fintype A] [DecidableEq A] [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q] in
theorem pblk_symm {u v : W} (hne : u ≠ v) (n : ℕ) : pblk n v u = pblk n u v := by
  unfold pblk; rw [canon_symm (Ne.symm hne)]

omit [Fintype A] [DecidableEq A] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem lik_symm (C : Channel W Q) (t : ℝ≥0) (n : ℕ) (x : W) {u v : W} (hne : u ≠ v) :
    lik C t n x v u = lik C t n x u v := by
  funext ω
  unfold lik blockSet
  simp only [pblk_symm hne]

omit [Fintype A] [DecidableEq A] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
/-- **The tests are antisymmetric.** -/
theorem beatH_anti (C : Channel W Q) (t : ℝ≥0) (n : ℕ) {u v : W} (hne : u ≠ v) :
    beatH C t n v u = (beatH C t n u v)ᶜ := by
  unfold beatH
  have hr : rk u ≠ rk v := fun h => hne (rk_inj h)
  rw [lik_symm C t n u hne, lik_symm C t n v hne]
  by_cases h1 : rk u < rk v
  · have h2 : ¬ rk v < rk u := by omega
    rw [if_pos h1, if_neg h2]
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  · have h2 : rk v < rk u := by omega
    rw [if_neg h1, if_pos h2]
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]

omit [Fintype A] [DecidableEq A] [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q] in
/-- A block has at least `n` rounds. -/
theorem card_block (n : ℕ) (u v : W) :
    n ≤ (blockSet (Fintype.card (W × W) * n) (pblk n u v)).card := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · omega
  set k := pidx (canon u v) with hk
  have hkK : k < Fintype.card (W × W) := pidx_lt _
  have hmap : ∀ j : Fin n, k * n + j < Fintype.card (W × W) * n := by
    intro j
    have : (k + 1) * n ≤ Fintype.card (W × W) * n := Nat.mul_le_mul_right _ hkK
    have := j.isLt
    nlinarith
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n)))
    (t := blockSet (Fintype.card (W × W) * n) (pblk n u v))
    (fun j => (⟨k * n + j, hmap j⟩ : Fin (Fintype.card (W × W) * n)))
    (by
      intro j _
      rw [Finset.mem_coe]
      unfold blockSet
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show (k * n + (j : ℕ)) / n = k
      rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j.isLt, zero_add])
    (by
      intro a _ b _ hab
      have := congrArg Fin.val hab
      simp only at this
      exact Fin.ext (by omega))
  simpa using h

theorem schedCost_le' (sched : ℕ → Q) (d : Q) (n : ℕ) : schedCost sched d n ≤ n := by
  unfold schedCost
  calc ∑ i : Fin n, (if sched i = d then 0 else 1) ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
    _ = n := by simp

/-- **A tested pair's test errs with probability at most `exp(-n kH)`.** -/
theorem beatH_error (C : Channel W Q) (t : ℝ≥0) (n : ℕ) (w v : W) (hne : w ≠ v)
    (htv : t ≤ kH C w v) :
    hist C (schedPolicy (tSched C t n)) w (Fintype.card (W × W) * n) (beatH C t n v w)
      ≤ ENNReal.ofReal (Real.exp (-(1 * n * (kH C w v : ℝ)))) := by
  set H := Fintype.card (W × W) * n
  set p := canon v w with hp
  have hsub : beatH C t n v w ⊆ {ω | ∏ i ∈ blockSet H (pblk n v w), C.dens w (tSched C t n i) (ω i).2
      ≤ ∏ i ∈ blockSet H (pblk n v w), C.dens v (tSched C t n i) (ω i).2} := by
    intro ω hω
    unfold beatH at hω
    split_ifs at hω
    · exact hω
    · exact le_of_lt (show lik C t n w v w ω < lik C t n v v w ω from hω)
  have hq : ∀ i ∈ blockSet H (pblk n v w), tSched C t n i = qStar C p.1 p.2 := by
    intro i hi0
    have hi : (i : ℕ) / n = pidx p := by
      unfold blockSet at hi0
      exact (Finset.mem_filter.mp hi0).2
    have hlt : (i : ℕ) / n < Fintype.card (W × W) := by rw [hi]; exact pidx_lt _
    unfold tSched
    rw [dif_pos hlt]
    have hsym : (Fintype.equivFin (W × W)).symm ⟨(i : ℕ) / n, hlt⟩ = p := by
      have : (⟨(i : ℕ) / n, hlt⟩ : Fin (Fintype.card (W × W))) = ⟨pidx p, pidx_lt p⟩ :=
        Fin.ext hi
      rw [this, pidx_symm]
    rw [hsym]
    have hkp : kH C p.1 p.2 = kH C w v := by
      rcases canon_cases v w with h | h <;> rw [hp, h]
      · exact kH_symm C w v |>.symm
    rw [if_pos ⟨canon_lt (Ne.symm hne), hkp ▸ htv⟩]
  have hhel : hel C w v (qStar C p.1 p.2) = kH C w v := by
    rcases canon_cases v w with h | h <;> rw [hp, h]
    · simp only; rw [hel_symm, hel_qStar, kH_symm]
    · simp only; rw [hel_qStar]
  calc hist C (schedPolicy (tSched C t n)) w H (beatH C t n v w)
      ≤ ∏ i ∈ blockSet H (pblk n v w), bc C w v (tSched C t n i) :=
        (measure_mono hsub).trans (block_error C (tSched C t n) w v H (pblk n v w))
    _ = bc C w v (qStar C p.1 p.2) ^ (blockSet H (pblk n v w)).card := by
        rw [Finset.prod_congr rfl fun i hi => by rw [hq i hi], Finset.prod_const]
    _ ≤ bc C w v (qStar C p.1 p.2) ^ n := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (card_block n v w)
        rw [hk, pow_add]
        exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (bc_le_one _ _ _ _))
    _ ≤ ENNReal.ofReal (Real.exp (-(n * hel C w v (qStar C p.1 p.2)))) := bc_pow_le _ _ _ _ _
    _ = ENNReal.ofReal (Real.exp (-(1 * n * (kH C w v : ℝ)))) := by rw [hhel, one_mul]

/-- **The upper law, unconditional, on every channel.**  If every obstruction contains a pair
whose best query has Hellinger information at least `t > 0`, the scheduled tournament with
`n >= log(|W|/delta)/t` rounds per tested pair is safe with probability `>= 1 - delta` at every
world, and costs at most `|W|^2 n` queries. -/
theorem hellinger_tournament (C : Channel W Q) (safe : W → Finset A) (t : ℝ≥0) (ht : 0 < t)
    (hres : Resolves (kH C) safe t) (a0 : A) (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (hn : Real.log ((Fintype.card W : ℝ) / δ) / t ≤ n) :
    (∀ w, hist C (schedPolicy (tSched C t n)) w (Fintype.card (W × W) * n)
        {ω | decode safe (pairSet (kH C) t) (beatH C t n) a0 ω ∉ safe w} ≤ ENNReal.ofReal δ)
      ∧ ∀ w, costN C (schedPolicy (tSched C t n)) w (Fintype.card (W × W) * n)
          ≤ ((Fintype.card W ^ 2 * n : ℕ) : ℝ≥0∞) := by
  refine ⟨(tournament_law safe (kH C) (kH_symm C) t ht hres (beatH C t n)
    (fun u v huv => beatH_anti C t n (Finset.mem_filter.mp huv).2.1) a0
    (fun w => hist C (schedPolicy (tSched C t n)) w (Fintype.card (W × W) * n)) 1 δ n one_pos hδ
    (Nat.cast_nonneg n) (by rwa [one_mul])
    (fun w v hwv => beatH_error C t n w v (Finset.mem_filter.mp hwv).2.1
      (Finset.mem_filter.mp hwv).2.2)).1, fun w => ?_⟩
  rw [costN_sched]
  have h1 := schedCost_le' (tSched C t n) C.dummy (Fintype.card (W × W) * n)
  have h3 : Fintype.card (W × W) * n = Fintype.card W ^ 2 * n := by
    rw [Fintype.card_prod]; ring
  exact_mod_cast h1.trans (le_of_eq h3)

/-- **The upper law at the Hellinger obstruction value.**  The obstruction value `tH` of the
Hellinger information exists, resolves every obstruction, and is tight on one of them; when it is
positive the tournament with `n >= log(|W|/delta)/tH` rounds per pair is safe with probability
`>= 1 - delta` at every world within `|W|^2 n` queries. -/
theorem hellinger_upper_star [Nonempty A] (C : Channel W Q) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty) (hex : ∃ H : Finset W, Unsafe safe H) (a0 : A) (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ tH : ℝ≥0, Resolves (kH C) safe tH
      ∧ (∃ H : Finset W, Unsafe safe H ∧ ∀ w ∈ H, ∀ w' ∈ H, w ≠ w' → kH C w w' ≤ tH)
      ∧ (0 < tH → ∀ n : ℕ, Real.log ((Fintype.card W : ℝ) / δ) / tH ≤ n →
          (∀ w, hist C (schedPolicy (tSched C tH n)) w (Fintype.card (W × W) * n)
              {ω | decode safe (pairSet (kH C) tH) (beatH C tH n) a0 ω ∉ safe w}
              ≤ ENNReal.ofReal δ)
          ∧ ∀ w, costN C (schedPolicy (tSched C tH n)) w (Fintype.card (W × W) * n)
              ≤ ((Fintype.card W ^ 2 * n : ℕ) : ℝ≥0∞)) := by
  obtain ⟨tH, hres, H, hH, htight⟩ :=
    obstruction_value (kH C) safe hex (two_le_card_of_unsafe safe hsafe)
  exact ⟨tH, hres, ⟨H, hH, htight⟩, fun htpos n hn =>
    hellinger_tournament C safe tH htpos hres a0 δ hδ n hn⟩

/-- **Comparing obstruction values.**  If one information is at most `K` times another, the
first's resolved thresholds are at most `K` times any tight threshold of the second. -/
theorem resolved_le_scale (κ1 κ2 : W → W → ℝ≥0) (K : ℝ≥0) (hcmp : ∀ u v, κ1 u v ≤ K * κ2 u v)
    (safe : W → Finset A) (t1 t2 : ℝ≥0) (h1 : Resolves κ1 safe t1) (H : Finset W)
    (hH : Unsafe safe H) (htight : ∀ w ∈ H, ∀ w' ∈ H, w ≠ w' → κ2 w w' ≤ t2) : t1 ≤ K * t2 := by
  obtain ⟨u, hu, v, hv, hne, hle⟩ := h1 H hH
  refine hle.trans ((hcmp u v).trans ?_)
  gcongr
  exact htight u hu v hv hne

end Tournament

/-! ## 6. The hypotheses are satisfiable: a Gaussian sign channel -/

section Example

/-- Two worlds, a dummy `N(0,1)` and one query `N(±1, 1)`. -/
noncomputable def gDens (w : Bool) (q : Fin 2) (y : ℝ) : ℝ :=
  if q = 0 then gaussianPDFReal 0 1 y else gaussianPDFReal (if w then 1 else -1) 1 y

noncomputable def gChan : Channel Bool (Fin 2) where
  dens := gDens
  dummy := 0
  meas := by intro w q; unfold gDens; split_ifs <;> exact measurable_gaussianPDFReal _ _
  pos := by intro w q y; unfold gDens; split_ifs <;> exact gaussianPDFReal_pos _ _ _ one_ne_zero
  mass := by intro w q; unfold gDens; split_ifs <;> exact lintegral_gaussianPDFReal_eq_one _ one_ne_zero
  dummy_same := by intro w w' y; simp [gDens]

theorem gauss_prod (y : ℝ) :
    gaussianPDFReal 1 1 y * gaussianPDFReal (-1) 1 y
      = (Real.exp (-1 / 2) * gaussianPDFReal 0 1 y) ^ 2 := by
  simp only [gaussianPDFReal, NNReal.coe_one]
  have e : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [← Real.exp_nat_mul]; norm_num
  calc (√(2 * π * 1))⁻¹ * rexp (-(y - 1) ^ 2 / (2 * 1))
        * ((√(2 * π * 1))⁻¹ * rexp (-(y - -1) ^ 2 / (2 * 1)))
      = (√(2 * π * 1))⁻¹ ^ 2 * rexp (-(y - 1) ^ 2 / (2 * 1) + -(y - -1) ^ 2 / (2 * 1)) := by
        rw [Real.exp_add]; ring
    _ = (√(2 * π * 1))⁻¹ ^ 2 * rexp (2 * (-1 / 2 + -(y - 0) ^ 2 / (2 * 1))) := by
        congr 2; ring
    _ = (rexp (-1 / 2) * ((√(2 * π * 1))⁻¹ * rexp (-(y - 0) ^ 2 / (2 * 1)))) ^ 2 := by
        rw [← e, Real.exp_add]; ring

theorem gChan_bc : bc gChan true false 1 = ENNReal.ofReal (Real.exp (-1 / 2)) := by
  unfold bc
  have hpt : ∀ y, ENNReal.ofReal (Real.sqrt (gChan.dens true 1 y * gChan.dens false 1 y))
      = ENNReal.ofReal (Real.exp (-1 / 2)) * ENNReal.ofReal (gaussianPDFReal 0 1 y) := by
    intro y
    show ENNReal.ofReal (Real.sqrt (gDens true 1 y * gDens false 1 y)) = _
    simp only [gDens, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, if_true,
      Bool.false_eq_true]
    rw [gauss_prod, Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le (gaussianPDFReal_nonneg _ _ _)),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (measurable_gaussianPDFReal 0 1).ennreal_ofReal,
    lintegral_gaussianPDFReal_eq_one _ one_ne_zero, mul_one]

theorem gChan_hel : hel gChan true false 1 = 1 - Real.exp (-1 / 2) := by
  unfold hel
  rw [gChan_bc, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- **The unconditional upper law is not vacuous**: on the Gaussian sign channel, identifying
the sign is resolved at `t = 1 - e^{-1/2} > 0`. -/
theorem hellinger_tournament_satisfiable :
    ∃ t : ℝ≥0, 0 < t ∧ Resolves (kH gChan) (fun w : Bool => ({w} : Finset Bool)) t := by
  have hpos : 0 < 1 - Real.exp (-1 / 2) := by
    have : Real.exp (-1 / 2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  refine ⟨⟨1 - Real.exp (-1 / 2), hpos.le⟩, by exact_mod_cast hpos, ?_⟩
  intro H hH
  obtain ⟨w1, hw1, h1⟩ := hH true
  obtain ⟨w2, hw2, h2⟩ := hH false
  have e1 : w1 = false := by simpa [eq_comm] using h1
  have e2 : w2 = true := by simpa [eq_comm] using h2
  subst e1; subst e2
  refine ⟨true, hw2, false, hw1, by decide, ?_⟩
  have : helNN gChan true false 1 ≤ kH gChan true false := Finset.le_sup (Finset.mem_univ _)
  refine le_trans (le_of_eq ?_) this
  exact Subtype.ext (gChan_hel).symm

end Example

#print axioms bc_le_one
#print axioms bc_pow_le
#print axioms lintegral_sqrt_ratio
#print axioms lintegral_prod_sched
#print axioms block_error
#print axioms beatH_anti
#print axioms beatH_error
#print axioms hellinger_tournament
#print axioms hellinger_upper_star
#print axioms resolved_le_scale
#print axioms gChan_bc
#print axioms hellinger_tournament_satisfiable

end CIGAMF.P13.PaperBHellingerTest
