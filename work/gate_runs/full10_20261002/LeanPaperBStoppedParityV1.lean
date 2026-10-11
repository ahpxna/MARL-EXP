import «LeanPaperBParityFinishV1»

/-!
# Paper B: the parity lower bounds for UNBOUNDED stopping rules

`parity_tip_finish` (`LeanPaperBParityFinishV1`) quantifies over policies with a finite horizon.
Here the lower half is extended to every randomised adaptive policy with a stopping rule that
need not be bounded, only almost surely finite.

* `SPol m` -- a stopping policy: query kernels for every round, a measurable stop decision
  after every number of rounds, and measurable answer and guess maps read at the stopping
  time.
* `stoppedPol` -- after the stop has fired the policy issues the dummy query (free, no
  information). ONE kernel policy serves every horizon, so the law of its first `n` rounds is
  `hist ... n` and nothing about infinite products is needed.
* `trunc S hm n` -- the finite-horizon policy `Pol m` that runs `stoppedPol S` for `n` rounds
  and answers what `S` answered at its stopping time, if it stopped by then
  (`outT_first`: the truncated output IS the output at the first stopping time).
* `costS` -- `sup_n` of the truncations' costs: the expected number of non-dummy queries
  before stopping (by monotone convergence, this is `E tau` of the unbounded run).
* `CorrectS` -- stops almost surely (uniformly over the finite world set: for every `eps` a
  horizon at which every world has stopped with probability `>= 1 - eps`) and, at every
  horizon, errs on the stopped runs with probability `<= delta`.

Results:

* `trunc_correct` -- a truncation at a horizon where the unstopped mass is `<= eps` is
  `Correct` at level `delta + eps`;
* `stopped_safe_lower`, `stopped_id_lower` -- for every such `S`, some world has
  `b log(1/(2 delta)) <= a h^(2s) costS`, with the constants of `safeLower` (`s = 1`) and
  `idLower` (`s = m - 1`), at level `2 delta`.

No bound on the stopping time, and no finiteness of `E tau`, is assumed: if `costS = top` the
statement holds trivially.
-/

namespace CIGAMF.P13.PaperBStoppedParity

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBParityExperiment CIGAMF.P13.PaperBEndgame
open CIGAMF.P13.PaperBRateClosure CIGAMF.P13.PaperBParityFinish

variable {m : ℕ}

/-! ## 1. Histories and stopping policies -/

/-- The first `j` rounds of an `n`-round history. -/
def hRestr {n : ℕ} (j : ℕ) (hj : j ≤ n) (x : Hist (Fin m) n) : Hist (Fin m) j :=
  fun i => x ⟨i, lt_of_lt_of_le i.isLt hj⟩

theorem measurable_hRestr {n : ℕ} (j : ℕ) (hj : j ≤ n) :
    Measurable (hRestr (m := m) (n := n) j hj) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

theorem hRestr_self {n : ℕ} (x : Hist (Fin m) n) : hRestr n le_rfl x = x := by
  funext i; rfl

theorem hRestr_hRestr {n k : ℕ} (i : ℕ) (hi : i ≤ k) (hk : k ≤ n) (x : Hist (Fin m) n) :
    hRestr i hi (hRestr k hk x) = hRestr i (hi.trans hk) x := by
  funext l; rfl

/-- **A stopping policy**: kernels for every round, a stop decision after every number of
rounds, and outputs read at the stopping time. -/
structure SPol (m : ℕ) where
  pol : Policy (Fin m)
  stop : ∀ n, Hist (Fin m) n → Prop
  stop_meas : ∀ n, MeasurableSet {x | stop n x}
  answer : ∀ n, Hist (Fin m) n → Fin m
  guess : ∀ n, Hist (Fin m) n → Fin m
  answer_meas : ∀ n, Measurable (answer n)
  guess_meas : ∀ n, Measurable (guess n)

/-- The stop has fired within the first `n` rounds. -/
def fired (S : SPol m) (n : ℕ) (x : Hist (Fin m) n) : Prop :=
  ∃ j, ∃ hj : j ≤ n, S.stop j (hRestr j hj x)

theorem measurableSet_fired (S : SPol m) (n : ℕ) :
    MeasurableSet {x : Hist (Fin m) n | fired S n x} := by
  have : {x : Hist (Fin m) n | fired S n x}
      = ⋃ j : ℕ, ⋃ hj : j ≤ n, (hRestr j hj) ⁻¹' {y | S.stop j y} := by
    ext x
    simp only [fired, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
  rw [this]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun hj =>
    measurable_hRestr j hj (S.stop_meas j)

/-! ## 2. The stopped kernel policy -/

open Classical in
/-- Round `n`'s query kernel: the dummy once the stop has fired, the policy's kernel before. -/
noncomputable def sStep (S : SPol m) (d : Fin m) (n : ℕ) : Kernel (Hist (Fin m) n) (Fin m) :=
  Kernel.piecewise (measurableSet_fired S n) (Kernel.const _ (Measure.dirac d)) (S.pol.step n)

/-- **The stopped policy**, one kernel policy for every horizon. -/
noncomputable def stoppedPol (S : SPol m) (d : Fin m) : Policy (Fin m) where
  step := sStep S d
  markov n := by
    haveI := S.pol.markov n
    unfold sStep
    infer_instance

/-! ## 3. The output at the stopping time -/

open Classical in
/-- The output at the first stopping time within `n` rounds, `d` if the stop has not fired. -/
noncomputable def outT (S : SPol m) (f : ∀ n, Hist (Fin m) n → Fin m) (d : Fin m) :
    ∀ n, Hist (Fin m) n → Fin m
  | 0 => fun x => if S.stop 0 x then f 0 x else d
  | n + 1 => fun x =>
      if fired S n (hRestr n (Nat.le_succ n) x) then outT S f d n (hRestr n (Nat.le_succ n) x)
      else if S.stop (n + 1) x then f (n + 1) x else d

theorem measurable_outT (S : SPol m) (f : ∀ n, Hist (Fin m) n → Fin m)
    (hf : ∀ n, Measurable (f n)) (d : Fin m) : ∀ n, Measurable (outT S f d n)
  | 0 => by
      classical
      exact Measurable.ite (S.stop_meas 0) (hf 0) measurable_const
  | n + 1 => by
      classical
      have hpre : MeasurableSet {x : Hist (Fin m) (n + 1) | fired S n (hRestr n (Nat.le_succ n) x)} :=
        measurable_hRestr n (Nat.le_succ n) (measurableSet_fired S n)
      exact Measurable.ite hpre ((measurable_outT S f hf d n).comp (measurable_hRestr _ _))
        (Measurable.ite (S.stop_meas (n + 1)) (hf (n + 1)) measurable_const)

/-- **The truncated output is the output at the first stopping time.** -/
theorem outT_first (S : SPol m) (f : ∀ n, Hist (Fin m) n → Fin m) (d : Fin m) :
    ∀ n (x : Hist (Fin m) n), fired S n x →
      ∃ j, ∃ hj : j ≤ n, S.stop j (hRestr j hj x) ∧
        (∀ i (hi : i < j), ¬ S.stop i (hRestr i (hi.le.trans hj) x)) ∧
        outT S f d n x = f j (hRestr j hj x)
  | 0, x, hx => by
      classical
      obtain ⟨j, hj, hs⟩ := hx
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      rw [hRestr_self] at hs
      refine ⟨0, le_rfl, by rw [hRestr_self]; exact hs, fun i hi => absurd hi (Nat.not_lt_zero _),
        ?_⟩
      show (if S.stop 0 x then f 0 x else d) = _
      rw [if_pos hs, hRestr_self]
  | n + 1, x, hx => by
      classical
      by_cases hprev : fired S n (hRestr n (Nat.le_succ n) x)
      · obtain ⟨j, hj, hs, hfirst, heq⟩ := outT_first S f d n _ hprev
        refine ⟨j, hj.trans (Nat.le_succ n), by rwa [hRestr_hRestr] at hs, fun i hi => ?_, ?_⟩
        · have := hfirst i hi
          rwa [hRestr_hRestr] at this
        · show (if fired S n (hRestr n (Nat.le_succ n) x) then
              outT S f d n (hRestr n (Nat.le_succ n) x)
            else if S.stop (n + 1) x then f (n + 1) x else d) = _
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
            outT S f d n (hRestr n (Nat.le_succ n) x)
          else if S.stop (n + 1) x then f (n + 1) x else d) = _
        rw [if_neg hprev, if_pos hs, hRestr_self]

/-! ## 4. Truncation, cost, correctness -/

/-- **The truncation at horizon `n`**, a finite-horizon policy of the parity experiment. -/
noncomputable def trunc (S : SPol m) (hm : 0 < m) (n : ℕ) : Pol m where
  N := n
  pol := stoppedPol S ⟨0, hm⟩
  answer := outT S S.answer ⟨0, hm⟩ n
  guess := outT S S.guess ⟨0, hm⟩ n

/-- **The expected cost of the unbounded run**: the supremum over horizons of the
truncations' costs (non-dummy queries). -/
noncomputable def costS (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (S : SPol m) (w : Fin m) :
    ℝ≥0∞ :=
  ⨆ n, costAt (parExp σ hσ hm) h (trunc S hm n) w

/-- **Correctness of a stopping policy**: it stops almost surely, uniformly over the finite
world set, and it errs on the stopped runs with probability at most `delta` at every horizon. -/
def CorrectS (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (task : Task) (h δ : ℝ) (S : SPol m) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ n, ∀ w,
      (parExp σ hσ hm).law h (trunc S hm n) w {ω | ¬ fired S n (restrictH m n ω)}
        ≤ ENNReal.ofReal ε) ∧
  ∀ n w, (parExp σ hσ hm).law h (trunc S hm n) w
      (wrong (parExp σ hσ hm) task (trunc S hm n) w ∩ {ω | fired S n (restrictH m n ω)})
    ≤ ENNReal.ofReal δ

/-- **A truncation is correct at level `delta + eps`.** -/
theorem trunc_correct (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (task : Task) (h δ ε : ℝ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (S : SPol m) (n : ℕ)
    (hstop : ∀ w, (parExp σ hσ hm).law h (trunc S hm n) w {ω | ¬ fired S n (restrictH m n ω)}
      ≤ ENNReal.ofReal ε)
    (herr : ∀ w, (parExp σ hσ hm).law h (trunc S hm n) w
      (wrong (parExp σ hσ hm) task (trunc S hm n) w ∩ {ω | fired S n (restrictH m n ω)})
      ≤ ENNReal.ofReal δ) :
    Correct (parExp σ hσ hm) task h (δ + ε) (trunc S hm n) := by
  refine ⟨⟨measurable_outT S S.answer S.answer_meas _ n,
    measurable_outT S S.guess S.guess_meas _ n⟩, fun w => ⟨?_, ?_⟩⟩
  · have : {ω : Om m | (parExp σ hσ hm).tau (trunc S hm n) ω = ⊤} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      show tauP hm (trunc S hm n) ω ≠ ⊤
      unfold tauP
      exact ENat.natCast_ne_top _
    rw [this, measure_empty]
  · set L := (parExp σ hσ hm).law h (trunc S hm n) w
    set Wr := wrong (parExp σ hσ hm) task (trunc S hm n) w
    set F := {ω : Om m | fired S n (restrictH m n ω)}
    have hsub : Wr ⊆ (Wr ∩ F) ∪ {ω | ¬ fired S n (restrictH m n ω)} := by
      intro ω hω
      by_cases hf : fired S n (restrictH m n ω)
      · exact Or.inl ⟨hω, hf⟩
      · exact Or.inr hf
    calc L Wr ≤ L ((Wr ∩ F) ∪ {ω | ¬ fired S n (restrictH m n ω)}) := measure_mono hsub
      _ ≤ L (Wr ∩ F) + L {ω | ¬ fired S n (restrictH m n ω)} := measure_union_le _ _
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal ε := add_le_add (herr w) (hstop w)
      _ = ENNReal.ofReal (δ + ε) := (ENNReal.ofReal_add hδ hε).symm

/-! ## 5. The lower bounds -/

/-- **The safe lower bound for every stopping policy**, at level `2 delta`. -/
theorem stopped_safe_lower (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ) (h2δ : 2 * δ ≤ δS m) (S : SPol m)
    (hS : CorrectS σ hσ hm .safe h δ S) :
    ∃ w, ENNReal.ofReal ((1 / (4 * ((m : ℝ) - 1))) * Real.log (1 / (2 * δ)))
      ≤ ENNReal.ofReal (aS m σ * h ^ (2 * 1)) * costS σ hσ hm h S w := by
  obtain ⟨n, hn⟩ := hS.1 δ hδ
  have hc := trunc_correct σ hσ hm .safe h δ δ hδ.le hδ.le S n hn (hS.2 n)
  rw [← two_mul] at hc
  have h14 : 2 * δ ≤ 1 / 4 := h2δ.trans (min_le_left _ _)
  have cert := safeLower σ hσ hm hm2 h (2 * δ) hh hh1 (by positivity) (by linarith)
    (h2δ.trans (min_le_right _ _))
  obtain ⟨w, v, hwv, hdem⟩ := cert.find_pair _ hc
  have hinfo := cert.stopped_information _ hc.1 w v hwv
  exact ⟨w, hdem.trans (hinfo.trans (mul_le_mul_right (le_iSup
    (fun k => costAt (parExp σ hσ hm) h (trunc S hm k) w) n) _))⟩

/-- **The identification lower bound for every stopping policy**, at level `2 delta`. -/
theorem stopped_id_lower (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ) (h2δ : 2 * δ ≤ δI m) (S : SPol m)
    (hS : CorrectS σ hσ hm .identify h δ S) :
    ∃ w, ENNReal.ofReal ((1 / 4) * Real.log (1 / (2 * δ)))
      ≤ ENNReal.ofReal (aI m σ * h ^ (2 * (m - 1))) * costS σ hσ hm h S w := by
  obtain ⟨n, hn⟩ := hS.1 δ hδ
  have hc := trunc_correct σ hσ hm .identify h δ δ hδ.le hδ.le S n hn (hS.2 n)
  rw [← two_mul] at hc
  have cert := idLower σ hσ hm hm2 h (2 * δ) hh hh1 (by positivity)
    (h2δ.trans (min_le_left _ _))
  obtain ⟨w, v, hwv, hdem⟩ := cert.find_pair _ hc
  have hinfo := cert.stopped_information _ hc.1 w v hwv
  exact ⟨w, hdem.trans (hinfo.trans (mul_le_mul_right (le_iSup
    (fun k => costAt (parExp σ hσ hm) h (trunc S hm k) w) n) _))⟩

/-! ## 6. Finite-horizon policies are stopping policies: satisfiability and the upper side -/

section Embed

variable {W : Type*}

/-- Two policies with the same kernels before round `n` have the same `n`-round law. -/
theorem hist_congr (C : Channel W (Fin m)) (pl pl' : Policy (Fin m)) (w : W) :
    ∀ n, (∀ k < n, pl.step k = pl'.step k) → hist C pl w n = hist C pl' w n
  | 0, _ => rfl
  | n + 1, hs => by
      have ih := hist_congr C pl pl' w n fun k hk => hs k (by omega)
      have hn := hs n (by omega)
      show (((hist C pl w n) ⊗ₘ pl.step n) ⊗ₘ obsKernel C w n).map (snocMap n)
        = (((hist C pl' w n) ⊗ₘ pl'.step n) ⊗ₘ obsKernel C w n).map (snocMap n)
      rw [ih, hn]

theorem hRestr_snoc (n : ℕ) (p : (Hist (Fin m) n × Fin m) × ℝ) :
    hRestr n (Nat.le_succ n) (snocMap n p) = p.1.1 := by
  funext i
  show Fin.snoc (α := fun _ => Fin m × ℝ) p.1.1 (p.1.2, p.2) (Fin.castSucc i) = p.1.1 i
  rw [Fin.snoc_castSucc]

/-- **The first `n` rounds of the `(n+1)`-round law are the `n`-round law.** -/
theorem hist_map_restr_succ (C : Channel W (Fin m)) (pl : Policy (Fin m)) (w : W) (n : ℕ) :
    (hist C pl w (n + 1)).map (hRestr n (Nat.le_succ n)) = hist C pl w n := by
  haveI := hist_prob C pl w n
  haveI := pl.markov n
  haveI := obsKernel_markov C w n
  show ((((hist C pl w n) ⊗ₘ pl.step n) ⊗ₘ obsKernel C w n).map (snocMap n)).map
      (hRestr n (Nat.le_succ n)) = hist C pl w n
  rw [Measure.map_map (measurable_hRestr _ _) (measurable_snocMap n)]
  have hcomp : (hRestr n (Nat.le_succ n)) ∘ (snocMap (Q := Fin m) n) = Prod.fst ∘ Prod.fst := by
    funext p; exact hRestr_snoc n p
  rw [hcomp, ← Measure.map_map measurable_fst measurable_fst]
  show (((hist C pl w n) ⊗ₘ pl.step n) ⊗ₘ obsKernel C w n).fst.fst = hist C pl w n
  rw [Measure.fst_compProd, Measure.fst_compProd]

theorem hist_map_restr (C : Channel W (Fin m)) (pl : Policy (Fin m)) (w : W) (N : ℕ) :
    ∀ k, (hist C pl w (N + k)).map (hRestr N (Nat.le_add_right N k)) = hist C pl w N
  | 0 => by
      have : hRestr (m := m) (n := N + 0) N (Nat.le_add_right N 0) = id := by
        funext x i; rfl
      rw [this, Measure.map_id]
      rfl
  | k + 1 => by
      have h1 : hRestr (m := m) (n := N + (k + 1)) N (Nat.le_add_right N (k + 1))
          = hRestr N (Nat.le_add_right N k) ∘ hRestr (N + k) (Nat.le_succ (N + k)) := by
        funext x; exact (hRestr_hRestr N _ _ x).symm
      rw [h1, ← Measure.map_map (measurable_hRestr _ _) (measurable_hRestr _ _)]
      have h2 : (hist C pl w (N + (k + 1))).map (hRestr (N + k) (Nat.le_succ (N + k)))
          = hist C pl w (N + k) := hist_map_restr_succ C pl w (N + k)
      rw [h2]
      exact hist_map_restr C pl w N k

theorem costN_mono (C : Channel W (Fin m)) (pl : Policy (Fin m)) (w : W) (n : ℕ) :
    ∀ k, costN C pl w n ≤ costN C pl w (n + k)
  | 0 => le_rfl
  | k + 1 => by
      refine (costN_mono C pl w n k).trans ?_
      rw [show n + (k + 1) = (n + k) + 1 by ring, costN_succ]
      exact le_self_add

end Embed

/-- An output read at a fixed horizon `N`, and `d` before it. -/
noncomputable def atN (N : ℕ) (f : Hist (Fin m) N → Fin m) (d : Fin m) (n : ℕ)
    (x : Hist (Fin m) n) : Fin m :=
  if h : N ≤ n then f (hRestr N h x) else d

theorem measurable_atN (N : ℕ) (f : Hist (Fin m) N → Fin m) (hf : Measurable f) (d : Fin m)
    (n : ℕ) : Measurable (atN N f d n) := by
  unfold atN
  by_cases h : N ≤ n
  · simp only [dif_pos h]; exact hf.comp (measurable_hRestr _ _)
  · simp only [dif_neg h]; exact measurable_const

/-- **A finite-horizon policy as a stopping policy**: stop at its horizon. -/
noncomputable def ofPol (P : Pol m) (hP : Measurable P.answer ∧ Measurable P.guess)
    (d : Fin m) : SPol m where
  pol := P.pol
  stop n _ := P.N ≤ n
  stop_meas _ := MeasurableSet.const _
  answer := atN P.N P.answer d
  guess := atN P.N P.guess d
  answer_meas := measurable_atN P.N P.answer hP.1 d
  guess_meas := measurable_atN P.N P.guess hP.2 d

theorem fired_ofPol (P : Pol m) (hP : Measurable P.answer ∧ Measurable P.guess) (d : Fin m)
    (n : ℕ) (x : Hist (Fin m) n) : fired (ofPol P hP d) n x ↔ P.N ≤ n := by
  constructor
  · rintro ⟨j, hj, hs⟩
    exact le_trans (show P.N ≤ j from hs) hj
  · intro h
    exact ⟨P.N, h, show P.N ≤ P.N from le_rfl⟩

theorem outT_ofPol (P : Pol m) (hP : Measurable P.answer ∧ Measurable P.guess) (d d' : Fin m)
    (g : Hist (Fin m) P.N → Fin m) (n : ℕ) (hn : P.N ≤ n) (x : Hist (Fin m) n) :
    outT (ofPol P hP d) (atN P.N g d) d' n x = g (hRestr P.N hn x) := by
  obtain ⟨j, hj, hs, hfirst, heq⟩ :=
    outT_first (ofPol P hP d) (atN P.N g d) d' n x ((fired_ofPol P hP d n x).mpr hn)
  have hjN : j = P.N := by
    have h1 : P.N ≤ j := hs
    by_contra hne
    exact hfirst P.N (by omega) (show P.N ≤ P.N from le_rfl)
  subst hjN
  rw [heq]
  unfold atN
  rw [dif_pos le_rfl, hRestr_hRestr]

theorem step_ofPol_lt (P : Pol m) (hP : Measurable P.answer ∧ Measurable P.guess) (d d' : Fin m)
    (k : ℕ) (hk : k < P.N) : (stoppedPol (ofPol P hP d) d').step k = P.pol.step k := by
  classical
  refine Kernel.ext fun x => ?_
  show sStep (ofPol P hP d) d' k x = P.pol.step k x
  unfold sStep
  rw [Kernel.piecewise_apply, if_neg (fun hx : x ∈ {x | fired (ofPol P hP d) k x} =>
    absurd ((fired_ofPol P hP d k x).mp hx) (by omega))]
  rfl

theorem step_ofPol_ge (P : Pol m) (hP : Measurable P.answer ∧ Measurable P.guess) (d d' : Fin m)
    (k : ℕ) (hk : P.N ≤ k) :
    (stoppedPol (ofPol P hP d) d').step k = Kernel.const _ (Measure.dirac d') := by
  classical
  refine Kernel.ext fun x => ?_
  show sStep (ofPol P hP d) d' k x = _
  unfold sStep
  rw [Kernel.piecewise_apply, if_pos (show x ∈ {x | fired (ofPol P hP d) k x} from
    (fired_ofPol P hP d k x).mpr hk)]

/-- After the horizon the embedded policy spends nothing. -/
theorem costN_ofPol_after {W : Type*} (C : Channel W (Fin m)) (P : Pol m)
    (hP : Measurable P.answer ∧ Measurable P.guess) (d : Fin m) (w : W) :
    ∀ k, costN C (stoppedPol (ofPol P hP d) C.dummy) w (P.N + k)
      = costN C (stoppedPol (ofPol P hP d) C.dummy) w P.N
  | 0 => rfl
  | k + 1 => by
      rw [show P.N + (k + 1) = (P.N + k) + 1 by ring, costN_succ,
        costN_ofPol_after C P hP d w k]
      haveI := hist_prob C (stoppedPol (ofPol P hP d) C.dummy) w (P.N + k)
      have hstep := step_ofPol_ge P hP d C.dummy (P.N + k) (Nat.le_add_right _ _)
      rw [show (stoppedPol (ofPol P hP d) C.dummy).step (P.N + k)
          = Kernel.const _ (Measure.dirac C.dummy) from hstep, Measure.compProd_const]
      have hset : {x : Hist (Fin m) (P.N + k) × Fin m | x.2 ≠ C.dummy}
          = Set.univ ×ˢ {q | q ≠ C.dummy} := by
        ext x; simp
      rw [hset, Measure.prod_prod]
      have : (Measure.dirac C.dummy) {q : Fin m | q ≠ C.dummy} = 0 := by
        rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
        simp
      rw [this, mul_zero, add_zero]

/-- **The embedded policy costs what the finite-horizon policy costs.** -/
theorem costS_ofPol (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (P : Pol m)
    (hP : Measurable P.answer ∧ Measurable P.guess) (d : Fin m) (w : Fin m) :
    costS σ hσ hm h (ofPol P hP d) w = costAt (parExp σ hσ hm) h P w := by
  set C := chanAt σ hσ hm h with hC
  have hd : C.dummy = ⟨0, hm⟩ := rfl
  have hc : ∀ n, costAt (parExp σ hσ hm) h (trunc (ofPol P hP d) hm n) w
      = costN C (stoppedPol (ofPol P hP d) C.dummy) w n :=
    fun n => costAt_eq σ hσ hm h (trunc (ofPol P hP d) hm n) w
  have hbefore : ∀ n, n ≤ P.N →
      costN C (stoppedPol (ofPol P hP d) C.dummy) w n = costN C P.pol w n := by
    intro n hn
    unfold costN
    rw [hist_congr C _ _ w n fun k hk => step_ofPol_lt P hP d C.dummy k (by omega)]
  unfold costS
  simp_rw [hc]
  rw [costAt_eq σ hσ hm h P w]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rcases le_or_gt n P.N with hn | hn
    · rw [hbefore n hn]
      obtain ⟨k, hk⟩ : ∃ k, P.N = n + k := ⟨P.N - n, by omega⟩
      have := costN_mono C P.pol w n k
      rwa [← hk] at this
    · obtain ⟨k, rfl⟩ : ∃ k, n = P.N + k := ⟨n - P.N, by omega⟩
      rw [costN_ofPol_after C P hP d w k, hbefore P.N le_rfl]
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun n => costN C (stoppedPol (ofPol P hP d) C.dummy) w n) P.N)
    rw [hbefore P.N le_rfl]

/-- **A correct finite-horizon policy is a correct stopping policy.** -/
theorem ofPol_correctS (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (task : Task) (h δ : ℝ) (P : Pol m)
    (hc : Correct (parExp σ hσ hm) task h δ P) (d : Fin m) :
    CorrectS σ hσ hm task h δ (ofPol P hc.1 d) := by
  refine ⟨fun ε _ => ⟨P.N, fun w => ?_⟩, fun n w => ?_⟩
  · have : {ω : Om m | ¬ fired (ofPol P hc.1 d) P.N (restrictH m P.N ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact (fired_ofPol P hc.1 d _ _).mpr le_rfl
    rw [this, measure_empty]
    exact zero_le
  rcases lt_or_ge n P.N with hn | hn
  · have : wrong (parExp σ hσ hm) task (trunc (ofPol P hc.1 d) hm n) w
        ∩ {ω | fired (ofPol P hc.1 d) n (restrictH m n ω)} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro _ hf
      exact absurd ((fired_ofPol P hc.1 d n _).mp hf) (by omega)
    rw [this, measure_empty]
    exact zero_le
  refine le_trans (measure_mono Set.inter_subset_left) ?_
  set g : Om m → Om m := fun ω => extendH m ⟨0, hm⟩ P.N (hRestr P.N hn (restrictH m n ω))
    with hg
  have hgm : Measurable g :=
    (measurable_extendH m _ _).comp ((measurable_hRestr _ _).comp (measurable_restrictH m n))
  have hans : ∀ ω, (parExp σ hσ hm).answer (trunc (ofPol P hc.1 d) hm n) ω
      = (parExp σ hσ hm).answer P (g ω) := by
    intro ω
    show outT (ofPol P hc.1 d) (atN P.N P.answer d) ⟨0, hm⟩ n (restrictH m n ω)
      = P.answer (restrictH m P.N (g ω))
    rw [outT_ofPol P hc.1 d ⟨0, hm⟩ P.answer n hn, hg, restrict_extend]
  have hgs : ∀ ω, (parExp σ hσ hm).guess (trunc (ofPol P hc.1 d) hm n) ω
      = (parExp σ hσ hm).guess P (g ω) := by
    intro ω
    show outT (ofPol P hc.1 d) (atN P.N P.guess d) ⟨0, hm⟩ n (restrictH m n ω)
      = P.guess (restrictH m P.N (g ω))
    rw [outT_ofPol P hc.1 d ⟨0, hm⟩ P.guess n hn, hg, restrict_extend]
  have hwr : wrong (parExp σ hσ hm) task (trunc (ofPol P hc.1 d) hm n) w
      = g ⁻¹' wrong (parExp σ hσ hm) task P w := by
    cases task
    · ext ω; simp only [wrong, Set.mem_setOf_eq, Set.mem_preimage, hans ω]
    · ext ω; simp only [wrong, Set.mem_setOf_eq, Set.mem_preimage, hgs ω]
  have hlaw : ((parExp σ hσ hm).law h (trunc (ofPol P hc.1 d) hm n) w).map g
      = (parExp σ hσ hm).law h P w := by
    show ((hist (chanAt σ hσ hm h) (stoppedPol (ofPol P hc.1 d) ⟨0, hm⟩) w n).map
        (extendH m ⟨0, hm⟩ n)).map g
      = (hist (chanAt σ hσ hm h) P.pol w P.N).map (extendH m ⟨0, hm⟩ P.N)
    rw [Measure.map_map hgm (measurable_extendH m _ _)]
    have hcomp : g ∘ extendH m ⟨0, hm⟩ n = extendH m ⟨0, hm⟩ P.N ∘ hRestr P.N hn := by
      funext x
      simp only [Function.comp, hg, restrict_extend]
    rw [hcomp, ← Measure.map_map (measurable_extendH m _ _) (measurable_hRestr _ _)]
    obtain ⟨k, rfl⟩ : ∃ k, n = P.N + k := ⟨n - P.N, by omega⟩
    rw [hist_map_restr (chanAt σ hσ hm h) _ w P.N k,
      hist_congr (chanAt σ hσ hm h) _ _ w P.N fun j hj =>
        step_ofPol_lt P hc.1 d ⟨0, hm⟩ j hj]
  rw [hwr]
  refine le_trans (Measure.le_map_apply hgm.aemeasurable _) ?_
  rw [hlaw]
  exact (hc.2 w).2

/-! ## 7. Both rates over every almost-surely stopping policy -/

/-- **Paper B endpoint, unbounded stopping rules.**  For every `m >= 2` worlds and noise
`sigma > 0`, on `0 < h <= 1` and `2 delta <= min(deltaS, deltaI)`:

* every safe-correct stopping policy has, at some world,
  `log(1/(2 delta)) / (4(m-1)) <= aS h^2 costS`, and a safe-correct stopping policy (the
  decoder, stopping at its horizon) has `costS <= C_safe log(1/delta)/h^2` at every world;
* every identification-correct stopping policy has, at some world,
  `log(1/(2 delta)) / 4 <= aI h^(2(m-1)) costS`, and one has
  `costS <= C_id log(1/delta)/h^(2(m-1))` at every world. -/
theorem stopped_parity_rates (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ) (h2δ : 2 * δ ≤ min (δS m) (δI m)) :
    (∀ S : SPol m, CorrectS σ hσ hm .safe h δ S → ∃ w,
      ENNReal.ofReal ((1 / (4 * ((m : ℝ) - 1))) * Real.log (1 / (2 * δ)))
        ≤ ENNReal.ofReal (aS m σ * h ^ (2 * 1)) * costS σ hσ hm h S w) ∧
    (∃ S : SPol m, CorrectS σ hσ hm .safe h δ S ∧ ∀ w,
      costS σ hσ hm h S w ≤ ENNReal.ofReal ((safeCert σ hσ hm hm2).C * scale h δ 1)) ∧
    (∀ S : SPol m, CorrectS σ hσ hm .identify h δ S → ∃ w,
      ENNReal.ofReal ((1 / 4) * Real.log (1 / (2 * δ)))
        ≤ ENNReal.ofReal (aI m σ * h ^ (2 * (m - 1))) * costS σ hσ hm h S w) ∧
    (∃ S : SPol m, CorrectS σ hσ hm .identify h δ S ∧ ∀ w,
      costS σ hσ hm h S w ≤ ENNReal.ofReal ((idCert σ hσ hm hm2).C * scale h δ (m - 1))) := by
  have hS2 : 2 * δ ≤ δS m := h2δ.trans (min_le_left _ _)
  have hI2 : 2 * δ ≤ δI m := h2δ.trans (min_le_right _ _)
  have hSδ : δ ≤ δS m := by linarith
  have hIδ : δ ≤ δI m := by linarith
  refine ⟨fun S hS => stopped_safe_lower σ hσ hm hm2 h δ hh hh1 hδ hS2 S hS, ?_,
    fun S hS => stopped_id_lower σ hσ hm hm2 h δ hh hh1 hδ hI2 S hS, ?_⟩
  · set D := (safeCert σ hσ hm hm2).upper h δ hh hh1 hδ hSδ
    exact ⟨ofPol D.code D.correct.1 ⟨0, hm⟩,
      ofPol_correctS σ hσ hm .safe h δ D.code D.correct ⟨0, hm⟩, fun w => by
        exact (costS_ofPol σ hσ hm h D.code D.correct.1 ⟨0, hm⟩ w).trans_le (D.cost w)⟩
  · set D := (idCert σ hσ hm hm2).upper h δ hh hh1 hδ hIδ
    exact ⟨ofPol D.code D.correct.1 ⟨0, hm⟩,
      ofPol_correctS σ hσ hm .identify h δ D.code D.correct ⟨0, hm⟩, fun w => by
        exact (costS_ofPol σ hσ hm h D.code D.correct.1 ⟨0, hm⟩ w).trans_le (D.cost w)⟩

/-- `log(1/(2 delta)) >= log(1/delta)/2` once `delta <= 1/4`. -/
theorem log_half_le (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    Real.log (1 / δ) / 2 ≤ Real.log (1 / (2 * δ)) := by
  have hsplit : Real.log (1 / (2 * δ)) = Real.log (1 / δ) - Real.log 2 := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul two_ne_zero hδ.ne']
    ring
  have h4 : (4 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hl4 : Real.log 4 ≤ Real.log (1 / δ) := Real.log_le_log (by norm_num) h4
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hsplit]
  linarith

/-- **The lower bounds in the `log(1/delta)` form of the endpoint**, over every
almost-surely stopping policy, with the constants halved. -/
theorem stopped_lower_log (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ) (h2δ : 2 * δ ≤ min (δS m) (δI m)) :
    (∀ S : SPol m, CorrectS σ hσ hm .safe h δ S → ∃ w,
      ENNReal.ofReal ((1 / (8 * ((m : ℝ) - 1))) * Real.log (1 / δ))
        ≤ ENNReal.ofReal (aS m σ * h ^ (2 * 1)) * costS σ hσ hm h S w) ∧
    (∀ S : SPol m, CorrectS σ hσ hm .identify h δ S → ∃ w,
      ENNReal.ofReal ((1 / 8) * Real.log (1 / δ))
        ≤ ENNReal.ofReal (aI m σ * h ^ (2 * (m - 1))) * costS σ hσ hm h S w) := by
  have hS2 : 2 * δ ≤ δS m := h2δ.trans (min_le_left _ _)
  have hI2 : 2 * δ ≤ δI m := h2δ.trans (min_le_right _ _)
  have hδ4 : δ ≤ 1 / 4 := by
    have : 2 * δ ≤ 1 / 4 := hS2.trans (min_le_left _ _)
    linarith
  have hlog := log_half_le δ hδ hδ4
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    linarith
  refine ⟨fun S hS => ?_, fun S hS => ?_⟩
  · obtain ⟨w, hw⟩ := stopped_safe_lower σ hσ hm hm2 h δ hh hh1 hδ hS2 S hS
    refine ⟨w, le_trans (ENNReal.ofReal_le_ofReal ?_) hw⟩
    have e : 1 / (8 * ((m : ℝ) - 1)) * Real.log (1 / δ)
        = 1 / (4 * ((m : ℝ) - 1)) * (Real.log (1 / δ) / 2) := by
      field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  · obtain ⟨w, hw⟩ := stopped_id_lower σ hσ hm hm2 h δ hh hh1 hδ hI2 S hS
    refine ⟨w, le_trans (ENNReal.ofReal_le_ofReal ?_) hw⟩
    have e : 1 / 8 * Real.log (1 / δ) = 1 / 4 * (Real.log (1 / δ) / 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hlog (by norm_num)

#print axioms outT_first
#print axioms trunc_correct
#print axioms stopped_safe_lower
#print axioms stopped_id_lower
#print axioms hist_map_restr
#print axioms costS_ofPol
#print axioms ofPol_correctS
#print axioms stopped_parity_rates
#print axioms stopped_lower_log

end CIGAMF.P13.PaperBStoppedParity
