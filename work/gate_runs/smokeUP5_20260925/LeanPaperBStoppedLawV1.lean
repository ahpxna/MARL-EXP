import «LeanPaperBFamilyDecoderV1»

/-!
# Paper B: the obstruction law for UNBOUNDED stopping rules, on every channel

`obstruction_lower`, `obstruction_lower_chi` and `obstruction_lower_star` quantify over
finite-horizon policies.  `LeanPaperBStoppedParityV1` extended the parity channel's lower bounds
to every almost-surely stopping policy by truncation.  This module does the same for EVERY
channel in protocol form, with any finite world set, any finite answer set and any safe-answer
correspondence, and then instantiates it on the latent family.

* `SPolicy Q A`: query kernels for every round, a measurable stop set after every number of
  rounds, and measurable outputs read at the stopping time.
* `stoppedPol S d`: after the stop has fired the policy issues the dummy `d`, which is free and
  carries no information.  One kernel policy serves every horizon, so the law of its first `n`
  rounds is `hist ... n`.
* `outT`: the output at the first stopping time within `n` rounds (`outT_first`).
* `costSt`: `sup_n` of the truncations' costs, the expected number of non-dummy queries before
  stopping.  No bound on the stopping time and no finiteness of its mean is assumed.
* `CorrectSt`: stops almost surely, uniformly over the finite world set, and at every horizon
  the stopped runs answer unsafely with probability at most `delta`.
* `trunc_correct`: a truncation where the unstopped mass is at most `eps` is correct at level
  `delta + eps`.
* `stopped_obstruction_lower`, `stopped_obstruction_lower_chi`, `stopped_obstruction_lower_star`:
  the obstruction law, at level `2 delta`, for every such policy.
* `ofFinite`, `costSt_ofFinite`, `correctSt_ofFinite`: a finite-horizon policy is a stopping
  policy with the same cost, and it is `CorrectSt` when it is correct.  So the hypotheses are
  satisfiable, and finite-horizon upper bounds are stopping-policy upper bounds.
* `family_safe_stopped_rate`, `family_id_stopped_rate`: both rates on the latent Gaussian family
  over every almost-surely stopping policy.
-/

namespace CIGAMF.P13.PaperBStoppedLaw

open MeasureTheory ProbabilityTheory InformationTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBObstructionLaw
open CIGAMF.P13.PaperBObstructionParity CIGAMF.P13.PaperBFamilyChannel
open CIGAMF.P13.PaperBFamilyDecoder CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperBSchedule

/-! ## 1. Histories and stopping policies -/

section Stop

variable {Q A : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [MeasurableSpace A]

/-- The first `j` rounds of an `n`-round history. -/
def hRestr {n : ℕ} (j : ℕ) (hj : j ≤ n) (x : Hist Q n) : Hist Q j :=
  fun i => x ⟨i, lt_of_lt_of_le i.isLt hj⟩

omit [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem measurable_hRestr {n : ℕ} (j : ℕ) (hj : j ≤ n) :
    Measurable (hRestr (Q := Q) (n := n) j hj) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem hRestr_self {n : ℕ} (x : Hist Q n) : hRestr n le_rfl x = x := by
  funext i; rfl

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem hRestr_hRestr {n k : ℕ} (i : ℕ) (hi : i ≤ k) (hk : k ≤ n) (x : Hist Q n) :
    hRestr i hi (hRestr k hk x) = hRestr i (hi.trans hk) x := by
  funext l; rfl

/-- **A stopping policy**: kernels for every round, a stop set after every number of rounds,
and an output read at the stopping time. -/
structure SPolicy (Q A : Type*) [MeasurableSpace Q] [MeasurableSpace A] where
  pol : Policy Q
  stop : ∀ n, Set (Hist Q n)
  stop_meas : ∀ n, MeasurableSet (stop n)
  out : ∀ n, Hist Q n → A
  out_meas : ∀ n, Measurable (out n)

/-- The stop has fired within the first `n` rounds. -/
def fired (S : SPolicy Q A) (n : ℕ) (x : Hist Q n) : Prop :=
  ∃ j, ∃ hj : j ≤ n, hRestr j hj x ∈ S.stop j

omit [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem measurableSet_fired (S : SPolicy Q A) (n : ℕ) :
    MeasurableSet {x : Hist Q n | fired S n x} := by
  have : {x : Hist Q n | fired S n x}
      = ⋃ j : ℕ, ⋃ hj : j ≤ n, (hRestr j hj) ⁻¹' (S.stop j) := by
    ext x
    simp only [fired, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
  rw [this]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun hj =>
    measurable_hRestr j hj (S.stop_meas j)

/-! ## 2. The stopped kernel policy -/

open Classical in
/-- Round `n`'s query kernel: the dummy once the stop has fired, the policy's kernel before. -/
noncomputable def sStep (S : SPolicy Q A) (d : Q) (n : ℕ) : Kernel (Hist Q n) Q :=
  Kernel.piecewise (measurableSet_fired S n) (Kernel.const _ (Measure.dirac d)) (S.pol.step n)

/-- **The stopped policy**, one kernel policy for every horizon. -/
noncomputable def stoppedPol (S : SPolicy Q A) (d : Q) : Policy Q where
  step := sStep S d
  markov n := by
    haveI := S.pol.markov n
    unfold sStep
    infer_instance

/-! ## 3. The output at the stopping time -/

open Classical in
/-- The output at the first stopping time within `n` rounds, `a0` if the stop has not fired. -/
noncomputable def outT (S : SPolicy Q A) (f : ∀ n, Hist Q n → A) (a0 : A) :
    ∀ n, Hist Q n → A
  | 0 => fun x => if x ∈ S.stop 0 then f 0 x else a0
  | n + 1 => fun x =>
      if fired S n (hRestr n (Nat.le_succ n) x) then outT S f a0 n (hRestr n (Nat.le_succ n) x)
      else if x ∈ S.stop (n + 1) then f (n + 1) x else a0

omit [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem measurable_outT (S : SPolicy Q A) (f : ∀ n, Hist Q n → A)
    (hf : ∀ n, Measurable (f n)) (a0 : A) : ∀ n, Measurable (outT S f a0 n)
  | 0 => by
      classical
      exact Measurable.ite (S.stop_meas 0) (hf 0) measurable_const
  | n + 1 => by
      classical
      have hpre : MeasurableSet {x : Hist Q (n + 1) | fired S n (hRestr n (Nat.le_succ n) x)} :=
        measurable_hRestr n (Nat.le_succ n) (measurableSet_fired S n)
      exact Measurable.ite hpre ((measurable_outT S f hf a0 n).comp (measurable_hRestr _ _))
        (Measurable.ite (S.stop_meas (n + 1)) (hf (n + 1)) measurable_const)

omit [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
/-- **The truncated output is the output at the first stopping time.** -/
theorem outT_first (S : SPolicy Q A) (f : ∀ n, Hist Q n → A) (a0 : A) :
    ∀ n (x : Hist Q n), fired S n x →
      ∃ j, ∃ hj : j ≤ n, hRestr j hj x ∈ S.stop j ∧
        (∀ i (hi : i < j), hRestr i (hi.le.trans hj) x ∉ S.stop i) ∧
        outT S f a0 n x = f j (hRestr j hj x)
  | 0, x, hx => by
      classical
      obtain ⟨j, hj, hs⟩ := hx
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      rw [hRestr_self] at hs
      refine ⟨0, le_rfl, by rw [hRestr_self]; exact hs, fun i hi => absurd hi (Nat.not_lt_zero _),
        ?_⟩
      show (if x ∈ S.stop 0 then f 0 x else a0) = _
      rw [if_pos hs, hRestr_self]
  | n + 1, x, hx => by
      classical
      by_cases hprev : fired S n (hRestr n (Nat.le_succ n) x)
      · obtain ⟨j, hj, hs, hfirst, heq⟩ := outT_first S f a0 n _ hprev
        refine ⟨j, hj.trans (Nat.le_succ n), by rwa [hRestr_hRestr] at hs, fun i hi => ?_, ?_⟩
        · have := hfirst i hi
          rwa [hRestr_hRestr] at this
        · show (if fired S n (hRestr n (Nat.le_succ n) x) then
              outT S f a0 n (hRestr n (Nat.le_succ n) x)
            else if x ∈ S.stop (n + 1) then f (n + 1) x else a0) = _
          rw [if_pos hprev, heq, hRestr_hRestr]
      · obtain ⟨j, hj, hs⟩ := hx
        have hjn : j = n + 1 := by
          by_contra hne
          exact hprev ⟨j, by omega, by rw [hRestr_hRestr]; exact hs⟩
        subst hjn
        rw [hRestr_self] at hs
        refine ⟨n + 1, le_rfl, by rw [hRestr_self]; exact hs, fun i hi => fun hsi => hprev
          ⟨i, by omega, by rw [hRestr_hRestr]; exact hsi⟩, ?_⟩
        show (if fired S n (hRestr n (Nat.le_succ n) x) then
            outT S f a0 n (hRestr n (Nat.le_succ n) x)
          else if x ∈ S.stop (n + 1) then f (n + 1) x else a0) = _
        rw [if_neg hprev, if_pos hs, hRestr_self]

end Stop

/-! ## 4. History laws under restriction -/

section Embed

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- Two policies with the same kernels before round `n` have the same `n`-round law. -/
theorem hist_congr (C : Channel W Q) (pl pl' : Policy Q) (w : W) :
    ∀ n, (∀ k < n, pl.step k = pl'.step k) → hist C pl w n = hist C pl' w n
  | 0, _ => rfl
  | n + 1, hs => by
      have ih := hist_congr C pl pl' w n fun k hk => hs k (by omega)
      have hn := hs n (by omega)
      show (((hist C pl w n) ⊗ₘ pl.step n) ⊗ₘ obsKernel C w n).map (snocMap n)
        = (((hist C pl' w n) ⊗ₘ pl'.step n) ⊗ₘ obsKernel C w n).map (snocMap n)
      rw [ih, hn]

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem hRestr_snoc (n : ℕ) (p : (Hist Q n × Q) × ℝ) :
    hRestr n (Nat.le_succ n) (snocMap n p) = p.1.1 := by
  funext i
  show Fin.snoc (α := fun _ => Q × ℝ) p.1.1 (p.1.2, p.2) (Fin.castSucc i) = p.1.1 i
  rw [Fin.snoc_castSucc]

/-- **The first `n` rounds of the `(n+1)`-round law are the `n`-round law.** -/
theorem hist_map_restr_succ (C : Channel W Q) (pl : Policy Q) (w : W) (n : ℕ) :
    (hist C pl w (n + 1)).map (hRestr n (Nat.le_succ n)) = hist C pl w n := by
  haveI := hist_prob C pl w n
  haveI := pl.markov n
  haveI := obsKernel_markov C w n
  show ((((hist C pl w n) ⊗ₘ pl.step n) ⊗ₘ obsKernel C w n).map (snocMap n)).map
      (hRestr n (Nat.le_succ n)) = hist C pl w n
  rw [Measure.map_map (measurable_hRestr _ _) (measurable_snocMap n)]
  have hcomp : (hRestr n (Nat.le_succ n)) ∘ (snocMap (Q := Q) n) = Prod.fst ∘ Prod.fst := by
    funext p; exact hRestr_snoc n p
  rw [hcomp, ← Measure.map_map measurable_fst measurable_fst]
  show (((hist C pl w n) ⊗ₘ pl.step n) ⊗ₘ obsKernel C w n).fst.fst = hist C pl w n
  rw [Measure.fst_compProd, Measure.fst_compProd]

theorem hist_map_restr (C : Channel W Q) (pl : Policy Q) (w : W) (N : ℕ) :
    ∀ k, (hist C pl w (N + k)).map (hRestr N (Nat.le_add_right N k)) = hist C pl w N
  | 0 => by
      have : hRestr (Q := Q) (n := N + 0) N (Nat.le_add_right N 0) = id := by
        funext x i; rfl
      rw [this, Measure.map_id]
      rfl
  | k + 1 => by
      have h1 : hRestr (Q := Q) (n := N + (k + 1)) N (Nat.le_add_right N (k + 1))
          = hRestr N (Nat.le_add_right N k) ∘ hRestr (N + k) (Nat.le_succ (N + k)) := by
        funext x; exact (hRestr_hRestr N _ _ x).symm
      rw [h1, ← Measure.map_map (measurable_hRestr _ _) (measurable_hRestr _ _)]
      have h2 : (hist C pl w (N + (k + 1))).map (hRestr (N + k) (Nat.le_succ (N + k)))
          = hist C pl w (N + k) := hist_map_restr_succ C pl w (N + k)
      rw [h2]
      exact hist_map_restr C pl w N k

theorem costN_mono (C : Channel W Q) (pl : Policy Q) (w : W) (n : ℕ) :
    ∀ k, costN C pl w n ≤ costN C pl w (n + k)
  | 0 => le_rfl
  | k + 1 => by
      refine (costN_mono C pl w n k).trans ?_
      rw [show n + (k + 1) = (n + k) + 1 by ring, costN_succ]
      exact le_self_add

end Embed

/-! ## 5. Truncation, cost, correctness, and the lower laws -/

section Law

variable {W Q A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
  [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] [Fintype Q]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Inhabited A]

/-- **The expected cost of the unbounded run**: the supremum over horizons of the truncations'
costs (non-dummy queries). -/
noncomputable def costSt (C : Channel W Q) (S : SPolicy Q A) (w : W) : ℝ≥0∞ :=
  ⨆ n, costN C (stoppedPol S C.dummy) w n

/-- **Correctness of a stopping policy**: it stops almost surely, uniformly over the finite world
set, and at every horizon the stopped runs answer unsafely with probability at most `delta`. -/
def CorrectSt (C : Channel W Q) (safe : W → Finset A) (δ : ℝ) (S : SPolicy Q A) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ n, ∀ w,
      hist C (stoppedPol S C.dummy) w n {x | ¬ fired S n x} ≤ ENNReal.ofReal ε) ∧
  ∀ n w, hist C (stoppedPol S C.dummy) w n
      {x | fired S n x ∧ outT S S.out default n x ∉ safe w} ≤ ENNReal.ofReal δ

omit [Fintype W] [DecidableEq W] [Fintype A] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q] [Inhabited A] in
theorem measurableSet_safeT (S : SPolicy Q A) (safe : W → Finset A) (a0 : A) (n : ℕ) (w : W) :
    MeasurableSet {x : Hist Q n | outT S S.out a0 n x ∈ safe w} :=
  measurable_outT S S.out S.out_meas a0 n (safe w).measurableSet

/-- A probability measure with bad mass at most `delta` has good mass at least `1 - delta`. -/
theorem good_of_bad {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Set Ω) (hG : MeasurableSet G) (δ : ℝ) (hδ : 0 ≤ δ) (h : μ Gᶜ ≤ ENNReal.ofReal δ) :
    1 - δ ≤ μ.real G := by
  have hc : μ.real Gᶜ ≤ δ := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hδ h
  rw [measureReal_compl hG, probReal_univ] at hc
  linarith

omit [Fintype W] [DecidableEq W] [Fintype A] [Fintype Q] in
/-- **A truncation is correct at level `delta + eps`.** -/
theorem trunc_correct (C : Channel W Q) (safe : W → Finset A) (δ ε : ℝ) (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (S : SPolicy Q A) (n : ℕ)
    (hstop : ∀ w, hist C (stoppedPol S C.dummy) w n {x | ¬ fired S n x} ≤ ENNReal.ofReal ε)
    (herr : ∀ w, hist C (stoppedPol S C.dummy) w n
      {x | fired S n x ∧ outT S S.out default n x ∉ safe w} ≤ ENNReal.ofReal δ) :
    ∀ w, 1 - (δ + ε) ≤ (hist C (stoppedPol S C.dummy) w n).real
      {x | outT S S.out default n x ∈ safe w} := by
  intro w
  haveI := hist_prob C (stoppedPol S C.dummy) w n
  refine good_of_bad _ _ (measurableSet_safeT S safe default n w) (δ + ε) (by linarith) ?_
  set μ := hist C (stoppedPol S C.dummy) w n
  have hsub : {x | outT S S.out default n x ∈ safe w}ᶜ
      ⊆ {x | fired S n x ∧ outT S S.out default n x ∉ safe w} ∪ {x | ¬ fired S n x} := by
    intro x hx
    by_cases hf : fired S n x
    · exact Or.inl ⟨hf, hx⟩
    · exact Or.inr hf
  calc μ {x | outT S S.out default n x ∈ safe w}ᶜ
      ≤ μ ({x | fired S n x ∧ outT S S.out default n x ∉ safe w} ∪ {x | ¬ fired S n x}) :=
        measure_mono hsub
    _ ≤ μ {x | fired S n x ∧ outT S S.out default n x ∉ safe w} + μ {x | ¬ fired S n x} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal ε := add_le_add (herr w) (hstop w)
    _ = ENNReal.ofReal (δ + ε) := (ENNReal.ofReal_add hδ hε).symm

/-- The truncation of a correct stopping policy, at the horizon where at most `delta` is still
running, is correct at level `2 delta`. -/
theorem trunc_two (C : Channel W Q) (safe : W → Finset A) (δ : ℝ) (hδ : 0 < δ)
    (S : SPolicy Q A) (hS : CorrectSt C safe δ S) :
    ∃ n, ∀ w, 1 - 2 * δ ≤ (hist C (stoppedPol S C.dummy) w n).real
      {x | outT S S.out default n x ∈ safe w} := by
  obtain ⟨n, hn⟩ := hS.1 δ hδ
  refine ⟨n, fun w => ?_⟩
  have := trunc_correct C safe δ δ hδ.le hδ.le S n hn (hS.2 n) w
  linarith

/-- **The obstruction law for unbounded stopping rules, with chi-square information.**  For
every obstruction `H`, every world `w0` in it, and every stopping policy that stops almost
surely and answers safely with probability `1 - delta`,
`((1 - 2 delta)/(|H| - 1)) log(1/(2 delta)) - log 2 <= t * E[#queries at w0]`. -/
theorem stopped_obstruction_lower_chi (C : Channel W Q) (S : SPolicy Q A) (safe : W → Finset A)
    (δ : ℝ) (hδ : 0 < δ) (h2δ : 2 * δ ≤ 1) (hS : CorrectSt C safe δ S)
    (H : Finset W) (hH : Unsafe safe H) (hcard : 2 ≤ H.card) (w0 : W) (hw0 : w0 ∈ H)
    (t : ℝ≥0∞) (hchi : ∀ v ∈ H, v ≠ w0 → ∀ q, q ≠ C.dummy → chi C w0 v q ≤ t) :
    ENNReal.ofReal ((1 - 2 * δ) / ((H.card : ℝ) - 1) * Real.log (1 / (2 * δ)) - Real.log 2)
      ≤ t * costSt C S w0 := by
  obtain ⟨n, hc⟩ := trunc_two C safe δ hδ S hS
  have h := obstruction_lower_chi C (stoppedPol S C.dummy) n (outT S S.out default n) safe
    (fun w => measurableSet_safeT S safe default n w) (2 * δ) (by linarith) h2δ hc H hH hcard w0
    hw0 t hchi
  refine h.trans ?_
  gcongr
  exact le_iSup (fun k => costN C (stoppedPol S C.dummy) w0 k) n

/-- **The obstruction law for unbounded stopping rules, with KL information.** -/
theorem stopped_obstruction_lower (C : Channel W Q) (S : SPolicy Q A) (safe : W → Finset A)
    (δ : ℝ) (hδ : 0 < δ) (h2δ : 2 * δ ≤ 1) (hS : CorrectSt C safe δ S)
    (H : Finset W) (hH : Unsafe safe H) (hcard : 2 ≤ H.card) (w0 : W) (hw0 : w0 ∈ H)
    (t : ℝ≥0) (hκ : ∀ v ∈ H, v ≠ w0 → ∀ q, q ≠ C.dummy → klq C w0 v q ≤ (t : ℝ≥0∞)) :
    ENNReal.ofReal ((1 - 2 * δ) / ((H.card : ℝ) - 1) * Real.log (1 / (2 * δ)) - Real.log 2)
      ≤ costSt C S w0 * (t : ℝ≥0∞) := by
  obtain ⟨n, hc⟩ := trunc_two C safe δ hδ S hS
  have h := obstruction_lower C (stoppedPol S C.dummy) n (outT S S.out default n) safe
    (fun w => measurableSet_safeT S safe default n w) (2 * δ) (by linarith) h2δ hc H hH hcard w0
    hw0 t hκ
  refine h.trans ?_
  gcongr
  exact le_iSup (fun k => costN C (stoppedPol S C.dummy) w0 k) n

/-- **The lower law at the obstruction information, for unbounded stopping rules.**  With a
per-query bound `kappa`, the obstruction information `tStar` resolves the correspondence and some
world pays `E[#queries] * tStar >= ((1 - 2 delta)/(|W| - 1)) log(1/(2 delta)) - log 2`. -/
theorem stopped_obstruction_lower_star [Nonempty A] (C : Channel W Q) (S : SPolicy Q A)
    (safe : W → Finset A) (hsafe : ∀ w, (safe w).Nonempty)
    (δ : ℝ) (hδ : 0 < δ) (h2δ : 2 * δ ≤ 1) (hS : CorrectSt C safe δ S)
    (κ : W → W → ℝ≥0) (hκ : ∀ w v, ∀ q, q ≠ C.dummy → klq C w v q ≤ (κ w v : ℝ≥0∞))
    (hex : ∃ H : Finset W, Unsafe safe H) :
    ∃ tStar : ℝ≥0, Resolves κ safe tStar
      ∧ ∃ w0 : W, ENNReal.ofReal ((1 - 2 * δ) / ((Fintype.card W : ℝ) - 1)
          * Real.log (1 / (2 * δ)) - Real.log 2) ≤ costSt C S w0 * (tStar : ℝ≥0∞) := by
  obtain ⟨n, hc⟩ := trunc_two C safe δ hδ S hS
  obtain ⟨tStar, hres, w0, h⟩ := obstruction_lower_star C (stoppedPol S C.dummy) n
    (outT S S.out default n) safe hsafe (fun w => measurableSet_safeT S safe default n w)
    (2 * δ) (by linarith) h2δ hc κ hκ hex
  refine ⟨tStar, hres, w0, h.trans ?_⟩
  gcongr
  exact le_iSup (fun k => costN C (stoppedPol S C.dummy) w0 k) n

end Law

/-! ## 6. Finite-horizon policies are stopping policies -/

section Finite

variable {W Q A : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [MeasurableSpace A] [Inhabited A]

/-- An output read at a fixed horizon `N`, and the default before it. -/
noncomputable def atN (N : ℕ) (f : Hist Q N → A) (n : ℕ) (x : Hist Q n) : A :=
  if h : N ≤ n then f (hRestr N h x) else default

omit [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem measurable_atN (N : ℕ) (f : Hist Q N → A) (hf : Measurable f) (n : ℕ) :
    Measurable (atN N f n) := by
  unfold atN
  by_cases h : N ≤ n
  · simp only [dif_pos h]; exact hf.comp (measurable_hRestr _ _)
  · simp only [dif_neg h]; exact measurable_const

/-- **A finite-horizon policy as a stopping policy**: stop at its horizon. -/
noncomputable def ofFinite (pol0 : Policy Q) (N : ℕ) (f : Hist Q N → A) (hf : Measurable f) :
    SPolicy Q A where
  pol := pol0
  stop n := {_x | N ≤ n}
  stop_meas _ := MeasurableSet.const _
  out := atN N f
  out_meas := measurable_atN N f hf

omit [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem fired_ofFinite (pol0 : Policy Q) (N : ℕ) (f : Hist Q N → A) (hf : Measurable f) (n : ℕ)
    (x : Hist Q n) : fired (ofFinite pol0 N f hf) n x ↔ N ≤ n := by
  constructor
  · rintro ⟨j, hj, hs⟩
    exact le_trans (show N ≤ j from hs) hj
  · intro h
    exact ⟨N, h, show N ≤ N from le_rfl⟩

omit [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem outT_ofFinite (pol0 : Policy Q) (N : ℕ) (f : Hist Q N → A) (hf : Measurable f) (a0 : A)
    (n : ℕ) (hn : N ≤ n) (x : Hist Q n) :
    outT (ofFinite pol0 N f hf) (ofFinite pol0 N f hf).out a0 n x = f (hRestr N hn x) := by
  obtain ⟨j, hj, hs, hfirst, heq⟩ :=
    outT_first (ofFinite pol0 N f hf) (ofFinite pol0 N f hf).out a0 n x
      ((fired_ofFinite pol0 N f hf n x).mpr hn)
  have hjN : j = N := by
    have h1 : N ≤ j := hs
    by_contra hne
    exact hfirst N (by omega) (show N ≤ N from le_rfl)
  subst hjN
  rw [heq]
  show atN j f j (hRestr j hj x) = _
  unfold atN
  rw [dif_pos le_rfl, hRestr_hRestr]

omit [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem step_ofFinite_lt (pol0 : Policy Q) (N : ℕ) (f : Hist Q N → A) (hf : Measurable f) (d : Q)
    (k : ℕ) (hk : k < N) : (stoppedPol (ofFinite pol0 N f hf) d).step k = pol0.step k := by
  classical
  refine Kernel.ext fun x => ?_
  show sStep (ofFinite pol0 N f hf) d k x = pol0.step k x
  unfold sStep
  rw [Kernel.piecewise_apply, if_neg (fun hx : x ∈ {x | fired (ofFinite pol0 N f hf) k x} =>
    absurd ((fired_ofFinite pol0 N f hf k x).mp hx) (by omega))]
  rfl

omit [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem step_ofFinite_ge (pol0 : Policy Q) (N : ℕ) (f : Hist Q N → A) (hf : Measurable f) (d : Q)
    (k : ℕ) (hk : N ≤ k) :
    (stoppedPol (ofFinite pol0 N f hf) d).step k = Kernel.const _ (Measure.dirac d) := by
  classical
  refine Kernel.ext fun x => ?_
  show sStep (ofFinite pol0 N f hf) d k x = _
  unfold sStep
  rw [Kernel.piecewise_apply, if_pos (show x ∈ {x | fired (ofFinite pol0 N f hf) k x} from
    (fired_ofFinite pol0 N f hf k x).mpr hk)]

/-- After the horizon the embedded policy spends nothing. -/
theorem costN_ofFinite_after (C : Channel W Q) (pol0 : Policy Q) (N : ℕ) (f : Hist Q N → A)
    (hf : Measurable f) (w : W) :
    ∀ k, costN C (stoppedPol (ofFinite pol0 N f hf) C.dummy) w (N + k)
      = costN C (stoppedPol (ofFinite pol0 N f hf) C.dummy) w N
  | 0 => rfl
  | k + 1 => by
      rw [show N + (k + 1) = (N + k) + 1 by ring, costN_succ, costN_ofFinite_after C pol0 N f hf w k]
      haveI := hist_prob C (stoppedPol (ofFinite pol0 N f hf) C.dummy) w (N + k)
      have hstep := step_ofFinite_ge pol0 N f hf C.dummy (N + k) (Nat.le_add_right _ _)
      rw [show (stoppedPol (ofFinite pol0 N f hf) C.dummy).step (N + k)
          = Kernel.const _ (Measure.dirac C.dummy) from hstep, Measure.compProd_const]
      have hset : {x : Hist Q (N + k) × Q | x.2 ≠ C.dummy}
          = Set.univ ×ˢ {q | q ≠ C.dummy} := by
        ext x; simp
      rw [hset, Measure.prod_prod]
      have : (Measure.dirac C.dummy) {q : Q | q ≠ C.dummy} = 0 := by
        rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
        simp
      rw [this, mul_zero, add_zero]

theorem costN_ofFinite_before (C : Channel W Q) (pol0 : Policy Q) (N : ℕ) (f : Hist Q N → A)
    (hf : Measurable f) (w : W) (n : ℕ) (hn : n ≤ N) :
    costN C (stoppedPol (ofFinite pol0 N f hf) C.dummy) w n = costN C pol0 w n := by
  unfold costN
  rw [hist_congr C _ _ w n fun k hk => step_ofFinite_lt pol0 N f hf C.dummy k (by omega)]

variable [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A] [Fintype Q]
  [MeasurableSingletonClass A]

omit [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A] [Fintype Q]
  [MeasurableSingletonClass A] in
/-- **The embedded policy costs what the finite-horizon policy costs.** -/
theorem costSt_ofFinite (C : Channel W Q) (pol0 : Policy Q) (N : ℕ) (f : Hist Q N → A)
    (hf : Measurable f) (w : W) :
    costSt C (ofFinite pol0 N f hf) w = costN C pol0 w N := by
  unfold costSt
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rcases le_or_gt n N with hn | hn
    · rw [costN_ofFinite_before C pol0 N f hf w n hn]
      obtain ⟨k, hk⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
      have := costN_mono C pol0 w n k
      rwa [← hk] at this
    · obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
      rw [costN_ofFinite_after C pol0 N f hf w k, costN_ofFinite_before C pol0 N f hf w N le_rfl]
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun n => costN C (stoppedPol (ofFinite pol0 N f hf) C.dummy) w n) N)
    rw [costN_ofFinite_before C pol0 N f hf w N le_rfl]

omit [Fintype W] [DecidableEq W] [Fintype A] [Fintype Q] in
/-- **A correct finite-horizon policy is a correct stopping policy.** -/
theorem correctSt_ofFinite (C : Channel W Q) (safe : W → Finset A) (δ : ℝ) (pol0 : Policy Q)
    (N : ℕ) (f : Hist Q N → A) (hf : Measurable f)
    (hcorr : ∀ w, hist C pol0 w N {x | f x ∉ safe w} ≤ ENNReal.ofReal δ) :
    CorrectSt C safe δ (ofFinite pol0 N f hf) := by
  refine ⟨fun ε _ => ⟨N, fun w => ?_⟩, fun n w => ?_⟩
  · have : {x : Hist Q N | ¬ fired (ofFinite pol0 N f hf) N x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact (fired_ofFinite pol0 N f hf N x).mpr le_rfl
    rw [this, measure_empty]
    exact zero_le
  rcases lt_or_ge n N with hn | hn
  · have : {x : Hist Q n | fired (ofFinite pol0 N f hf) n x
        ∧ outT (ofFinite pol0 N f hf) (ofFinite pol0 N f hf).out default n x ∉ safe w} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hf'
      exact absurd ((fired_ofFinite pol0 N f hf n x).mp hf') (by omega)
    rw [this, measure_empty]
    exact zero_le
  have hsub : {x : Hist Q n | fired (ofFinite pol0 N f hf) n x
        ∧ outT (ofFinite pol0 N f hf) (ofFinite pol0 N f hf).out default n x ∉ safe w}
      ⊆ (hRestr N hn) ⁻¹' {y | f y ∉ safe w} := by
    intro x hx
    have := hx.2
    rw [outT_ofFinite pol0 N f hf default n hn x] at this
    exact this
  refine (measure_mono hsub).trans ?_
  refine (Measure.le_map_apply (measurable_hRestr N hn).aemeasurable _).trans ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
  rw [hist_map_restr C _ w N k,
    hist_congr C _ _ w N fun j hj => step_ofFinite_lt pol0 N f hf C.dummy j hj]
  exact hcorr w

end Finite

/-! ## 7. Both rates on the latent family, over every almost-surely stopping policy -/

/-- **The safe decision on the latent family, unbounded stopping rules.**  Every finite probe
family of unit `l1` norm, with every stopping policy that stops almost surely and is safe with
probability `1 - delta`, pays `((1 - 2 delta) log(1/(2 delta)) - log 2)/(Cu h^2)` expected
queries at `u = v = +1`; and the decoder, stopping at its horizon, is such a policy with expected
cost at most `8 log(2/delta)/(G_dec h)^2 + 2` at every world. -/
theorem family_safe_stopped_rate (r : ℕ) (hr : 0 < r) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (h2δ : 2 * δ ≤ 1) :
    (∀ (k : ℕ) (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ)
        (_ : ∀ q, ∑ i, |aH q i| + ∑ i, |aT q i| ≤ 1) (S : SPolicy (Fin (k + 1)) (Fin (r + 3))),
        CorrectSt (famChan σ h hσ aH aT) (famSafe r) δ S →
        ENNReal.ofReal ((1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2)
          ≤ ENNReal.ofReal (Cu σ 1 * h ^ 2) * costSt (famChan σ h hσ aH aT) S (true, true))
    ∧ ∃ S : SPolicy (Fin 3) (Fin (r + 3)), CorrectSt (dChan r σ h hσ) (famSafe r) δ S
        ∧ ∀ w, costSt (dChan r σ h hσ) S w
          ≤ ENNReal.ofReal (8 * Real.log (2 / δ) / (Gdec σ * h) ^ 2 + 2) := by
  have hδ1 : δ ≤ 1 := by linarith
  refine ⟨fun k aH aT hn S hS => ?_, ?_⟩
  · obtain ⟨n, hc⟩ := trunc_two (famChan σ h hσ aH aT) (famSafe r) δ hδ S hS
    have hl := family_safe_lower σ h 1 hσ hh.le hh1 aH aT hn (stoppedPol S _) n
      (outT S S.out default n) (fun w => measurableSet_safeT S (famSafe r) default n w)
      (2 * δ) (by linarith) h2δ hc
    refine hl.trans ?_
    gcongr
    exact le_iSup (fun j => costN (famChan σ h hσ aH aT)
      (stoppedPol S (famChan σ h hσ aH aT).dummy) (true, true) j) n
  · obtain ⟨-, hcost, -⟩ := family_safe_rate r hr σ h δ hσ hh hh1 hδ hδ1
    refine ⟨ofFinite (schedPolicy schedS) (NS σ h δ) (safeOut r σ h (NS σ h δ))
      (measurable_safeOut r σ h _), correctSt_ofFinite _ _ _ _ _ _ _
        (fun w => safe_decoder_error r σ h δ hσ hh hh1 hδ hδ1 w), fun w => ?_⟩
    rw [costSt_ofFinite]
    exact hcost w

/-- **Identification on the latent family, unbounded stopping rules.** -/
theorem family_id_stopped_rate (r : ℕ) (hr : 0 < r) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (h2δ : 2 * δ ≤ 1) :
    (∀ (k : ℕ) (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ)
        (_ : ∀ q, ∑ i, |aH q i| + ∑ i, |aT q i| ≤ 1) (S : SPolicy (Fin (k + 1)) (Bool × Bool)),
        CorrectSt (famChan σ h hσ aH aT) (fun w => ({w} : Finset (Bool × Bool))) δ S →
        ENNReal.ofReal ((1 - 2 * δ) * Real.log (1 / (2 * δ)) - Real.log 2)
          ≤ ENNReal.ofReal (Cv r σ 1 * h ^ (2 * r))
            * costSt (famChan σ h hσ aH aT) S (true, true))
    ∧ ∃ S : SPolicy (Fin 3) (Bool × Bool),
        CorrectSt (dChan r σ h hσ) (fun w => ({w} : Finset (Bool × Bool))) δ S
        ∧ ∀ w, costSt (dChan r σ h hσ) S w
          ≤ ENNReal.ofReal (2 * (16 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2 + 2)) := by
  have hδ1 : δ ≤ 1 := by linarith
  refine ⟨fun k aH aT hn S hS => ?_, ?_⟩
  · obtain ⟨n, hc⟩ := trunc_two (famChan σ h hσ aH aT) (fun w => ({w} : Finset (Bool × Bool)))
      δ hδ S hS
    have hl := family_id_lower σ h 1 hσ hh.le hh1 aH aT hn (stoppedPol S _) n
      (outT S S.out default n)
      (fun w => measurableSet_safeT S (fun w => ({w} : Finset (Bool × Bool))) default n w)
      (2 * δ) (by linarith) h2δ hc
    refine hl.trans ?_
    gcongr
    exact le_iSup (fun j => costN (famChan σ h hσ aH aT)
      (stoppedPol S (famChan σ h hσ aH aT).dummy) (true, true) j) n
  · obtain ⟨-, hcost, -⟩ := family_id_rate r hr σ h δ hσ hh hh1 hδ hδ1
    refine ⟨ofFinite (schedPolicy (schedI (NI r σ h δ))) (2 * NI r σ h δ)
      (idOut r σ h (NI r σ h δ)) (measurable_idOut r σ h _), correctSt_ofFinite _ _ _ _ _ _ _
        (fun w => id_decoder_error r hr σ h δ hσ hh hh1 hδ w), fun w => ?_⟩
    rw [costSt_ofFinite]
    exact hcost w

#print axioms outT_first
#print axioms trunc_correct
#print axioms stopped_obstruction_lower_chi
#print axioms stopped_obstruction_lower
#print axioms stopped_obstruction_lower_star
#print axioms costSt_ofFinite
#print axioms correctSt_ofFinite
#print axioms family_safe_stopped_rate
#print axioms family_id_stopped_rate

end CIGAMF.P13.PaperBStoppedLaw
