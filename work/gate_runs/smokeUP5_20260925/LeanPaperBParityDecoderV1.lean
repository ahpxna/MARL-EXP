import «LeanPaperBParityTestV1»
import «LeanPaperBParityExperimentV1»

/-!
# Paper B: the two decoders on the parity experiment, correct in every world

Two fixed-budget policies of `LeanPaperBParityExperimentV1.parExp`, each ONE policy for all
worlds (it depends on `h`, `delta`, `sigma`, never on the world):

* `safeCode` -- `N_S` rounds of query `1`; if the nearest-mean test says "mask `-1`" (world
  `0`) answer `1`, else answer `0`.  The answer is wrong only when the test errs
  (`safe_correct`), and `N_S = ⌈8 log(2/delta) / (G_1^2 h^2)⌉`;
* `idCode` -- `N` rounds of each query `1, ..., m-1` in blocks; the guess is the world the
  vector of test outcomes points to (`decodeB`).  If every test is right the guess is the world
  (`points_truth`, `decodeB_eq`), so a wrong guess forces some test to err, and a union bound
  over the `m - 1` tests gives the error (`id_correct`), with
  `N = ⌈8 (m-1) log(2(m-1)/delta) / (G^2 h^(2(m-1)))⌉`.

The test errors are `test_error_plus` / `test_error_minus` on the actual history law; the gaps
are `gap_lower` (from the characteristic function of the observation law), bounded below
uniformly over `j <= k` by `gap_ge`.  The costs are the schedule's lengths (`costN_sched`),
and `budget_le` turns them into `C log(1/delta) / h^(2s)`.
-/

namespace CIGAMF.P13.PaperBParityDecoder

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBChiSq CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBParityLaw
open CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBParityChannel CIGAMF.P13.PaperBSchedule
open CIGAMF.P13.PaperBParityTest CIGAMF.P13.PaperBParityExperiment
open CIGAMF.P13.PaperBEndgame CIGAMF.P13.PaperBRateClosure

variable {m : ℕ}

/-! ## 1. Numerics -/

/-- The sample size of one test. -/
noncomputable def nSamp (K G h δ : ℝ) (k : ℕ) : ℕ :=
  ⌈8 * K * Real.log (2 * K / δ) / (G ^ 2 * h ^ (2 * k))⌉₊

/-- **The error of one test at sample size `nSamp`**, as a real number. -/
theorem err_bound (K G h δ g : ℝ) (k N : ℕ) (hK : 1 ≤ K) (hG : 0 < G) (hh : 0 < h)
    (hδ : 0 < δ) (hg : G * h ^ k ≤ g)
    (hN : 8 * K * Real.log (2 * K / δ) / (G ^ 2 * h ^ (2 * k)) ≤ N) (hN0 : 0 < N) :
    2 * Real.exp (-((N * g / 2) ^ 2) / (2 * (K * N))) ≤ δ / K := by
  have hK0 : 0 < K := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hGh : 0 < G * h ^ k := by positivity
  have hsq : (G * h ^ k) ^ 2 ≤ g ^ 2 := pow_le_pow_left₀ hGh.le hg 2
  have hD : 0 < G ^ 2 * h ^ (2 * k) := by positivity
  have hsq' : G ^ 2 * h ^ (2 * k) = (G * h ^ k) ^ 2 := by rw [mul_pow, pow_mul']
  have hlogle : Real.log (2 * K / δ) ≤ N * g ^ 2 / (8 * K) := by
    have h1 : 8 * K * Real.log (2 * K / δ) ≤ N * (G ^ 2 * h ^ (2 * k)) := by
      rwa [div_le_iff₀ hD] at hN
    rw [le_div_iff₀ (by positivity)]
    have h2 : N * (G ^ 2 * h ^ (2 * k)) ≤ N * g ^ 2 := by
      rw [hsq']; exact mul_le_mul_of_nonneg_left hsq hNR.le
    linarith
  have hX : (N * g / 2) ^ 2 / (2 * (K * N)) = N * g ^ 2 / (8 * K) := by
    field_simp
    ring
  rw [neg_div, hX]
  have hpos : 0 < 2 * K / δ := by positivity
  have hexp : Real.exp (-(N * g ^ 2 / (8 * K))) ≤ δ / (2 * K) := by
    calc Real.exp (-(N * g ^ 2 / (8 * K))) ≤ Real.exp (-Real.log (2 * K / δ)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = δ / (2 * K) := by rw [Real.exp_neg, Real.exp_log hpos, inv_div]
  have h2 : 2 * (δ / (2 * K)) = δ / K := by field_simp
  linarith

/-- `log(1/delta) >= 1` once `delta <= 1/4`. -/
theorem one_le_log (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) : 1 ≤ Real.log (1 / δ) := by
  have h4 : (4 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have he : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
  have : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) he
  rw [Real.log_exp] at this
  linarith [Real.log_le_log (by norm_num) h4]

/-- **The budget of `K` tests at sample size `nSamp`.** -/
theorem budget_le (K G h δ : ℝ) (k : ℕ) (hK : 1 ≤ K) (hG : 0 < G) (hh : 0 < h) (hh1 : h ≤ 1)
    (hδ : 0 < δ) (hδK : δ ≤ 1 / (2 * K)) (hδ4 : δ ≤ 1 / 4) :
    K * (nSamp K G h δ k : ℝ)
      ≤ K * (16 * K / G ^ 2 + 1) * (Real.log (1 / δ) / h ^ (2 * k)) := by
  have hK0 : 0 < K := by linarith
  set L := Real.log (1 / δ) with hLdef
  have hL1 : 1 ≤ L := one_le_log δ hδ hδ4
  have h2K : 2 * K ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp hδK
    linarith
  have hlog2K : Real.log (2 * K) ≤ L := Real.log_le_log (by positivity) h2K
  have hsplit : Real.log (2 * K / δ) = Real.log (2 * K) + L := by
    rw [hLdef, ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlogpos : 0 ≤ Real.log (2 * K / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    have := h2K
    rw [le_div_iff₀ hδ] at this
    nlinarith
  have hD : 0 < G ^ 2 * h ^ (2 * k) := by positivity
  have hhk : 0 < h ^ (2 * k) := by positivity
  have hhk1 : h ^ (2 * k) ≤ 1 := pow_le_one₀ hh.le hh1
  set X := 8 * K * Real.log (2 * K / δ) / (G ^ 2 * h ^ (2 * k)) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hceil : (nSamp K G h δ k : ℝ) < X + 1 := Nat.ceil_lt_add_one hX0
  have hXle : X ≤ 16 * K / G ^ 2 * (L / h ^ (2 * k)) := by
    rw [hXdef, hsplit]
    have : 8 * K * (Real.log (2 * K) + L) / (G ^ 2 * h ^ (2 * k))
        ≤ 8 * K * (2 * L) / (G ^ 2 * h ^ (2 * k)) := by
      apply div_le_div_of_nonneg_right _ hD.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have hone : 1 ≤ L / h ^ (2 * k) := by
    rw [le_div_iff₀ hhk]; linarith
  have : (nSamp K G h δ k : ℝ) ≤ (16 * K / G ^ 2 + 1) * (L / h ^ (2 * k)) := by
    have := hceil.le
    nlinarith
  calc K * (nSamp K G h δ k : ℝ) ≤ K * ((16 * K / G ^ 2 + 1) * (L / h ^ (2 * k))) :=
        mul_le_mul_of_nonneg_left this hK0.le
    _ = K * (16 * K / G ^ 2 + 1) * (L / h ^ (2 * k)) := by ring

theorem nSamp_pos (K G h δ : ℝ) (k : ℕ) (hK : 1 ≤ K) (hG : 0 < G) (hh : 0 < h) (hδ : 0 < δ)
    (hδK : δ ≤ 1 / (2 * K)) : 0 < nSamp K G h δ k := by
  unfold nSamp
  apply Nat.ceil_pos.mpr
  have hK0 : 0 < K := by linarith
  have h1 : 1 < 2 * K / δ := by
    rw [lt_div_iff₀ hδ]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp hδK
    nlinarith
  have := Real.log_pos h1
  positivity

/-! ## 2. The gap, uniformly over the tests -/

/-- The gap constant at order `k`. -/
noncomputable def Gc (k : ℕ) (σ : ℝ) : ℝ :=
  2 * Real.sin 1 * (3 / (4 * (k : ℝ))) ^ k * Real.exp (-(σ ^ 2 / 2))

theorem sin_one_pos : 0 < Real.sin 1 :=
  Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.pi_gt_three])

theorem Gc_pos (k : ℕ) (hk : 0 < k) (σ : ℝ) : 0 < Gc k σ := by
  unfold Gc
  have := sin_one_pos
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- **The gap of every test `j <= k` is at least `Gc k * h^k`.** -/
theorem gap_ge (σ h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (j k : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    Gc k σ * h ^ k ≤ |cP j h σ - cM j h σ| := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hg := gap_lower j (by omega) σ h hh (by linarith)
  set a := 3 / (4 * (k : ℝ)) * h with ha
  set b := 3 / (4 * (j : ℝ)) * h with hb
  have ha0 : 0 ≤ a := by positivity
  have hab : a ≤ b := by
    apply mul_le_mul_of_nonneg_right _ hh.le
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  have hb1 : b ≤ 1 := by
    have : 3 / (4 * (j : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc b = 3 / (4 * (j : ℝ)) * h := rfl
      _ ≤ 1 * 1 := mul_le_mul this hh1 hh.le zero_le_one
      _ = 1 := one_mul 1
  have ha1 : a ≤ 1 := hab.trans hb1
  have hpow : a ^ k ≤ b ^ j :=
    (pow_le_pow_of_le_one ha0 ha1 hjk).trans (pow_le_pow_left₀ ha0 hab j)
  have hc : 0 ≤ 2 * Real.sin 1 * Real.exp (-(σ ^ 2 / 2)) := by
    have := sin_one_pos; positivity
  calc Gc k σ * h ^ k = 2 * Real.sin 1 * Real.exp (-(σ ^ 2 / 2)) * a ^ k := by
        rw [ha, mul_pow]; unfold Gc; ring
    _ ≤ 2 * Real.sin 1 * Real.exp (-(σ ^ 2 / 2)) * b ^ j := mul_le_mul_of_nonneg_left hpow hc
    _ = 2 * Real.sin 1 * (3 / (4 * (j : ℝ))) ^ j * h ^ j * Real.exp (-(σ ^ 2 / 2)) := by
        rw [hb, mul_pow]; ring
    _ ≤ |cP j h σ - cM j h σ| := hg

/-! ## 3. The run law of a decoder -/

theorem law_restrict (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (P : Pol m) (w : Fin m)
    (S : Set (Hist (Fin m) P.N)) (hS : MeasurableSet S) :
    (parExp σ hσ hm).law h P w (restrictH m P.N ⁻¹' S)
      = hist (chanAt σ hσ hm h) P.pol w P.N S := by
  show lawAt σ hσ hm h P w _ = _
  unfold lawAt
  rw [Measure.map_apply (measurable_extendH m _ _) (measurable_restrictH m P.N hS),
    Set.preimage_preimage]
  congr 1
  ext x
  simp only [Set.mem_preimage, restrict_extend]

theorem tau_top_null (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (P : Pol m) (w : Fin m) :
    (parExp σ hσ hm).law h P w {ω | (parExp σ hσ hm).tau P ω = ⊤} = 0 := by
  have : {ω | (parExp σ hσ hm).tau P ω = ⊤} = ∅ := by
    ext ω
    simp [parExp, tauP]
  rw [this, measure_empty]

theorem schedCost_le (sched : ℕ → Fin m) (d : Fin m) (n : ℕ) : schedCost sched d n ≤ n := by
  unfold schedCost
  calc ∑ i : Fin n, (if sched i = d then 0 else 1) ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
    _ = n := by simp

theorem costAt_sched_le (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ) (P : Pol m) (w : Fin m)
    (sched : ℕ → Fin m) (hP : P.pol = schedPolicy sched) :
    costAt (parExp σ hσ hm) h P w ≤ (P.N : ℝ≥0∞) := by
  rw [costAt_eq, hP, costN_sched]
  exact_mod_cast schedCost_le sched _ P.N

/-- Two errors of size `e` each are at most `delta / K` in `ENNReal`. -/
theorem two_ofReal_le (e c : ℝ) (he : 2 * e ≤ c) :
    2 * ENNReal.ofReal e ≤ ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal he

/-! ## 4. The safe decoder -/

/-- Every round asks query `1`. -/
def schedS (hm2 : 2 ≤ m) : ℕ → Fin m := fun _ => ⟨1, by omega⟩

/-- The safe sample size. -/
noncomputable def NS (σ h δ : ℝ) : ℕ := nSamp 1 (Gc 1 σ) h δ 1

/-- **The safe decoder.** -/
noncomputable def safeCode (σ h δ : ℝ) (hm2 : 2 ≤ m) : Pol m where
  N := NS σ h δ
  pol := schedPolicy (schedS hm2)
  answer x := by
    classical
    exact if saysMinus m (schedS hm2) ⟨1, by omega⟩ (max h 0) σ (NS σ h δ) x
      then ⟨1, by omega⟩ else ⟨0, by omega⟩
  guess _ := ⟨0, by omega⟩

theorem cnt_schedS (hm2 : 2 ≤ m) (N : ℕ) :
    cnt m (schedS hm2) ⟨1, by omega⟩ N = N := by
  unfold cnt schedS
  simp

theorem safe_measurable (σ h δ : ℝ) (hm2 : 2 ≤ m) :
    Measurable (safeCode σ h δ hm2).answer ∧ Measurable (safeCode σ h δ hm2).guess := by
  classical
  refine ⟨?_, measurable_const⟩
  exact Measurable.ite (measurableSet_saysMinus m _ _ _ _ _) measurable_const measurable_const

/-- **The safe decoder is correct in every world.** -/
theorem safe_correct (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    Correct (parExp σ hσ hm) .safe h δ (safeCode σ h δ hm2) := by
  classical
  refine ⟨safe_measurable σ h δ hm2, fun w => ⟨tau_top_null σ hσ hm h _ w, ?_⟩⟩
  set P := safeCode σ h δ hm2 with hP
  have hmeas := safe_measurable σ h δ hm2
  rw [wrong_safe_eq σ hσ hm hm2]
  change (parExp σ hσ hm).law h P w (restrictH m P.N ⁻¹' {x | P.answer x = w}) ≤ _
  rw [law_restrict σ hσ hm h P w {x | P.answer x = w} (hmeas.1 (measurableSet_singleton w))]
  -- the numerics of the one test
  have hmax : max h 0 = h := max_eq_left hh.le
  have hh' : 0 < max h 0 := by rw [hmax]; exact hh
  have hh1' : max h 0 ≤ 1 := by rw [hmax]; exact hh1
  have hN0 : 0 < NS σ h δ :=
    nSamp_pos 1 (Gc 1 σ) h δ 1 le_rfl (Gc_pos 1 one_pos σ) hh hδ (by linarith)
  have hgap := gap_ge σ (max h 0) hh' hh1' 1 1 le_rfl le_rfl
  have hnum := err_bound 1 (Gc 1 σ) (max h 0) δ _ 1 (NS σ h δ) le_rfl (Gc_pos 1 one_pos σ) hh'
    hδ hgap (by rw [hmax]; exact Nat.le_ceil _) hN0
  have hbound : 2 * ENNReal.ofReal (Real.exp (-((cnt m (schedS hm2) ⟨1, by omega⟩ (NS σ h δ)
      * |cP 1 (max h 0) σ - cM 1 (max h 0) σ| / 2) ^ 2) / (2 * (NS σ h δ : ℝ))))
      ≤ ENNReal.ofReal δ := by
    apply two_ofReal_le
    rw [cnt_schedS]
    have : ((1 : ℝ) * (NS σ h δ : ℝ)) = (NS σ h δ : ℝ) := one_mul _
    rw [this, div_one] at hnum
    exact hnum
  have hj : ((⟨1, by omega⟩ : Fin m) : ℕ) ≠ 0 := by simp
  by_cases hw : (w : ℕ) = 0
  · -- world `0`: the mask of query `1` is `-1`; the answer `0` needs the test to err
    have hmask : maskR ((⟨1, by omega⟩ : Fin m) : ℕ) (w + 1) = -1 := by
      unfold maskR; rw [if_pos]; simp [hw]
    refine le_trans (measure_mono fun x hx => ?_) ((test_error_minus m σ (max h 0) hσ
      (le_max_right h 0) hm (schedS hm2) ⟨1, by omega⟩ w hj hmask (NS σ h δ) hN0).trans hbound)
    show ¬ saysMinus m (schedS hm2) ⟨1, by omega⟩ (max h 0) σ (NS σ h δ) x
    intro hs
    have hx' : (if saysMinus m (schedS hm2) ⟨1, by omega⟩ (max h 0) σ (NS σ h δ) x
        then (⟨1, by omega⟩ : Fin m) else ⟨0, by omega⟩) = w := hx
    rw [if_pos hs] at hx'
    have : (1 : ℕ) = (w : ℕ) := congrArg Fin.val hx'
    omega
  · -- world `w ≠ 0`: the mask is `+1`; answering `w` needs the test to say `-1`
    have hmask : maskR ((⟨1, by omega⟩ : Fin m) : ℕ) (w + 1) = 1 := by
      unfold maskR; rw [if_neg]; simp; omega
    refine le_trans (measure_mono fun x hx => ?_) ((test_error_plus m σ (max h 0) hσ
      (le_max_right h 0) hm (schedS hm2) ⟨1, by omega⟩ w hj hmask (NS σ h δ) hN0).trans hbound)
    show saysMinus m (schedS hm2) ⟨1, by omega⟩ (max h 0) σ (NS σ h δ) x
    by_contra hs
    have hx' : (if saysMinus m (schedS hm2) ⟨1, by omega⟩ (max h 0) σ (NS σ h δ) x
        then (⟨1, by omega⟩ : Fin m) else ⟨0, by omega⟩) = w := hx
    rw [if_neg hs] at hx'
    have : (0 : ℕ) = (w : ℕ) := congrArg Fin.val hx'
    omega

/-- **The safe decoder's budget.** -/
theorem safe_cost (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (w : Fin m) :
    costAt (parExp σ hσ hm) h (safeCode σ h δ hm2) w
      ≤ ENNReal.ofReal ((1 * (16 * 1 / Gc 1 σ ^ 2 + 1)) * scale h δ 1) := by
  refine (costAt_sched_le σ hσ hm h _ w (schedS hm2) rfl).trans ?_
  have hb := budget_le 1 (Gc 1 σ) h δ 1 le_rfl (Gc_pos 1 one_pos σ) hh hh1 hδ (by linarith)
    hδ4
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  unfold scale
  show ((nSamp 1 (Gc 1 σ) h δ 1 : ℕ) : ℝ) ≤ _
  linarith

/-! ## 5. The identification decoder -/

/-- The world a vector of test outcomes points to. -/
def Points (b : Fin m → Bool) (k : Fin m) : Prop :=
  ∀ j : Fin m, (j : ℕ) ≠ 0 → (b j = true ↔ (j : ℕ) = (k : ℕ) + 1)

theorem points_unique (b : Fin m → Bool) (k k' : Fin m) (hk : Points b k) (hk' : Points b k') :
    k = k' := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hj : (k : ℕ) + 1 < m := by have := k'.isLt; omega
    have h1 := (hk ⟨(k : ℕ) + 1, hj⟩ (by simp)).mpr rfl
    have h2 := (hk' ⟨(k : ℕ) + 1, hj⟩ (by simp)).mp h1
    simp at h2
    omega
  · have hj : (k' : ℕ) + 1 < m := by have := k.isLt; omega
    have h1 := (hk' ⟨(k' : ℕ) + 1, hj⟩ (by simp)).mpr rfl
    have h2 := (hk ⟨(k' : ℕ) + 1, hj⟩ (by simp)).mp h1
    simp at h2
    omega

open Classical in
/-- The decoding of the test outcomes. -/
noncomputable def decodeB (hm : 0 < m) (b : Fin m → Bool) : Fin m :=
  if hb : ∃ k, Points b k then Classical.choose hb else ⟨0, hm⟩

theorem decodeB_eq (hm : 0 < m) (b : Fin m → Bool) (k : Fin m) (hk : Points b k) :
    decodeB hm b = k := by
  unfold decodeB
  rw [dif_pos ⟨k, hk⟩]
  exact points_unique b _ _ (Classical.choose_spec (⟨k, hk⟩ : ∃ k, Points b k)) hk

/-- The block schedule: rounds `[(j-1) N, j N)` ask query `j`. -/
def schedI (hm2 : 2 ≤ m) (N : ℕ) : ℕ → Fin m :=
  fun i => ⟨min (i / N + 1) (m - 1), by omega⟩

theorem cnt_schedI (hm2 : 2 ≤ m) (N : ℕ) (hN : 0 < N) (j : Fin m) (hj : (j : ℕ) ≠ 0) :
    cnt m (schedI hm2 N) j ((m - 1) * N) = N := by
  classical
  unfold cnt
  rw [Fin.sum_univ_eq_sum_range (fun i => if schedI hm2 N i = j then (1 : ℝ) else 0)
    ((m - 1) * N), Finset.sum_boole]
  have hfilt : (Finset.range ((m - 1) * N)).filter (fun i => schedI hm2 N i = j)
      = Finset.Ico (((j : ℕ) - 1) * N) ((j : ℕ) * N) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hi, hs⟩
      have hv := congrArg Fin.val hs
      simp only [schedI] at hv
      have hdiv : i / N < m - 1 := (Nat.div_lt_iff_lt_mul hN).mpr hi
      rw [min_eq_left (by omega)] at hv
      have hq : i / N = (j : ℕ) - 1 := by omega
      constructor
      · rw [← hq]; exact Nat.div_mul_le_self i N
      · have h1 : i < (i / N + 1) * N := (Nat.div_lt_iff_lt_mul hN).mp (Nat.lt_succ_self _)
        rw [hq, show (j : ℕ) - 1 + 1 = j by omega] at h1
        exact h1
    · rintro ⟨h1, h2⟩
      have hjm : (j : ℕ) ≤ m - 1 := by have := j.isLt; omega
      have hq : i / N = (j : ℕ) - 1 := by
        apply le_antisymm
        · have : i / N < j := (Nat.div_lt_iff_lt_mul hN).mpr h2
          omega
        · exact (Nat.le_div_iff_mul_le hN).mpr h1
      refine ⟨lt_of_lt_of_le h2 (Nat.mul_le_mul_right _ hjm), ?_⟩
      apply Fin.ext
      show min (i / N + 1) (m - 1) = (j : ℕ)
      rw [hq]
      omega
  rw [hfilt, Nat.card_Ico]
  have : (j : ℕ) * N - ((j : ℕ) - 1) * N = N := by
    obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨(j : ℕ) - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, add_mul, one_mul, Nat.add_sub_cancel_left]
  rw [this]

/-- The number of tests, as a real number. -/
noncomputable def Km (m : ℕ) : ℝ := ((m - 1 : ℕ) : ℝ)

theorem one_le_Km (hm2 : 2 ≤ m) : 1 ≤ Km m := by
  unfold Km
  have : 1 ≤ m - 1 := by omega
  exact_mod_cast this

/-- The per-test sample size. -/
noncomputable def NI (m : ℕ) (σ h δ : ℝ) : ℕ := nSamp (Km m) (Gc (m - 1) σ) h δ (m - 1)

/-- The test outcomes of the identification decoder. -/
noncomputable def outcomes (hm2 : 2 ≤ m) (σ h δ : ℝ) (x : Hist (Fin m) ((m - 1) * NI m σ h δ)) :
    Fin m → Bool := by
  classical
  exact fun j => decide (saysMinus m (schedI hm2 (NI m σ h δ)) j (max h 0) σ
    ((m - 1) * NI m σ h δ) x)

/-- **The identification decoder.** -/
noncomputable def idCode (σ h δ : ℝ) (hm : 0 < m) (hm2 : 2 ≤ m) : Pol m where
  N := (m - 1) * NI m σ h δ
  pol := schedPolicy (schedI hm2 (NI m σ h δ))
  answer _ := ⟨0, hm⟩
  guess x := decodeB hm (outcomes hm2 σ h δ x)

theorem measurable_outcomes (hm2 : 2 ≤ m) (σ h δ : ℝ) :
    Measurable (outcomes hm2 σ h δ) := by
  classical
  refine measurable_pi_lambda _ fun j => ?_
  refine measurable_to_bool ?_
  have : (fun x => outcomes hm2 σ h δ x j) ⁻¹' {true}
      = {x | saysMinus m (schedI hm2 (NI m σ h δ)) j (max h 0) σ ((m - 1) * NI m σ h δ) x} := by
    ext x
    simp [outcomes]
  rw [this]
  exact measurableSet_saysMinus m _ _ _ _ _

theorem id_measurable (σ h δ : ℝ) (hm : 0 < m) (hm2 : 2 ≤ m) :
    Measurable (idCode σ h δ hm hm2).answer ∧ Measurable (idCode σ h δ hm hm2).guess :=
  ⟨measurable_const, show Measurable fun x => decodeB hm (outcomes hm2 σ h δ x) from
    (measurable_of_countable (decodeB hm)).comp (measurable_outcomes hm2 σ h δ)⟩

/-- The truth vector points to the world. -/
theorem points_truth (w : Fin m) : Points (fun j : Fin m => decide ((j : ℕ) = (w : ℕ) + 1)) w := by
  intro j _
  simp

/-- The mask of query `j` in world `w`. -/
theorem maskR_world (j w : ℕ) : maskR j (w + 1) = -1 ↔ j = w + 1 := by
  unfold maskR
  split_ifs with h
  · simp [h]
  · constructor
    · intro h'; norm_num at h'
    · intro h'; exact absurd h' h

/-- **The identification decoder is correct in every world.** -/
theorem id_correct (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (hδK : δ ≤ 1 / (2 * Km m)) :
    Correct (parExp σ hσ hm) .identify h δ (idCode σ h δ hm hm2) := by
  classical
  refine ⟨id_measurable σ h δ hm hm2, fun w => ⟨tau_top_null σ hσ hm h _ w, ?_⟩⟩
  set P := idCode σ h δ hm hm2 with hP
  have hmeas := id_measurable σ h δ hm hm2
  set N := NI m σ h δ with hNdef
  set H := (m - 1) * N with hHdef
  set sched := schedI hm2 N with hsched
  change (parExp σ hσ hm).law h P w (restrictH m P.N ⁻¹' {x | P.guess x ≠ w}) ≤ _
  rw [law_restrict σ hσ hm h P w {x | P.guess x ≠ w} (hmeas.2 (measurableSet_singleton w)).compl]
  -- the bad event of each test
  let Bad : Fin m → Set (Hist (Fin m) H) := fun j =>
    {x | ¬ (saysMinus m sched j (max h 0) σ H x ↔ (j : ℕ) = (w : ℕ) + 1)}
  let I : Finset (Fin m) := Finset.univ.erase ⟨0, hm⟩
  have hsub : {x : Hist (Fin m) H | P.guess x ≠ w} ⊆ ⋃ j ∈ I, Bad j := by
    intro x hx
    by_contra hnot
    apply hx
    show decodeB hm (outcomes hm2 σ h δ x) = w
    apply decodeB_eq
    intro j hj
    have hjI : j ∈ I := Finset.mem_erase.mpr ⟨fun h' => hj (by rw [h']), Finset.mem_univ _⟩
    have hgood : saysMinus m sched j (max h 0) σ H x ↔ (j : ℕ) = (w : ℕ) + 1 := by
      by_contra hb
      exact hnot (Set.mem_biUnion hjI hb)
    simp only [outcomes, decide_eq_true_iff]
    exact hgood
  -- numerics
  have hmax : max h 0 = h := max_eq_left hh.le
  have hh' : 0 < max h 0 := by rw [hmax]; exact hh
  have hh1' : max h 0 ≤ 1 := by rw [hmax]; exact hh1
  have hK := one_le_Km hm2
  have hm1 : 0 < m - 1 := by omega
  have hN0 : 0 < N := nSamp_pos _ _ h δ _ hK (Gc_pos (m - 1) hm1 σ) hh hδ hδK
  have hH0 : 0 < H := Nat.mul_pos hm1 hN0
  have hHR : (H : ℝ) = Km m * N := by rw [hHdef, Km]; push_cast; ring
  have hone : ∀ j ∈ I, hist (chanAt σ hσ hm h) P.pol w P.N (Bad j)
      ≤ ENNReal.ofReal (δ / Km m) := by
    intro j hjI
    have hj : (j : ℕ) ≠ 0 := by
      intro h0; exact (Finset.mem_erase.mp hjI).1 (Fin.ext h0)
    have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj
    have hjk : (j : ℕ) ≤ m - 1 := by have := j.isLt; omega
    have hgap := gap_ge σ (max h 0) hh' hh1' j (m - 1) hj1 hjk
    have hnum := err_bound (Km m) (Gc (m - 1) σ) (max h 0) δ _ (m - 1) N hK
      (Gc_pos (m - 1) hm1 σ) hh' hδ hgap (by rw [hmax]; exact Nat.le_ceil _) hN0
    have hbound : 2 * ENNReal.ofReal (Real.exp (-((cnt m sched j H
        * |cP j (max h 0) σ - cM j (max h 0) σ| / 2) ^ 2) / (2 * (H : ℝ))))
        ≤ ENNReal.ofReal (δ / Km m) := by
      apply two_ofReal_le
      rw [cnt_schedI hm2 N hN0 j hj, hHR]
      exact hnum
    by_cases hw : (j : ℕ) = (w : ℕ) + 1
    · have hmask : maskR (j : ℕ) (w + 1) = -1 := (maskR_world _ _).mpr hw
      refine le_trans (measure_mono fun x hx => ?_) ((test_error_minus m σ (max h 0) hσ
        (le_max_right h 0) hm sched j w hj hmask H hH0).trans hbound)
      show ¬ saysMinus m sched j (max h 0) σ H x
      intro hs
      exact hx ⟨fun _ => hw, fun _ => hs⟩
    · have hmask : maskR (j : ℕ) (w + 1) = 1 := by
        unfold maskR; rw [if_neg hw]
      refine le_trans (measure_mono fun x hx => ?_) ((test_error_plus m σ (max h 0) hσ
        (le_max_right h 0) hm sched j w hj hmask H hH0).trans hbound)
      show saysMinus m sched j (max h 0) σ H x
      by_contra hs
      exact hx ⟨fun h' => absurd h' hs, fun h' => absurd h' hw⟩
  have hcard : (I.card : ℝ≥0∞) = ((m - 1 : ℕ) : ℝ≥0∞) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  calc hist (chanAt σ hσ hm h) P.pol w P.N {x | P.guess x ≠ w}
      ≤ hist (chanAt σ hσ hm h) P.pol w P.N (⋃ j ∈ I, Bad j) := measure_mono hsub
    _ ≤ ∑ j ∈ I, hist (chanAt σ hσ hm h) P.pol w P.N (Bad j) := measure_biUnion_finset_le I Bad
    _ ≤ ∑ _j ∈ I, ENNReal.ofReal (δ / Km m) := Finset.sum_le_sum hone
    _ = ENNReal.ofReal δ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : ((m - 1 : ℕ) : ℝ) = Km m := rfl
        rw [this]
        field_simp [(by linarith : (0 : ℝ) < Km m).ne']

/-- **The identification decoder's budget.** -/
theorem id_cost (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (hδK : δ ≤ 1 / (2 * Km m)) (hδ4 : δ ≤ 1 / 4) (w : Fin m) :
    costAt (parExp σ hσ hm) h (idCode σ h δ hm hm2) w
      ≤ ENNReal.ofReal ((Km m * (16 * Km m / Gc (m - 1) σ ^ 2 + 1)) * scale h δ (m - 1)) := by
  refine (costAt_sched_le σ hσ hm h _ w (schedI hm2 (NI m σ h δ)) rfl).trans ?_
  have hm1 : 0 < m - 1 := by omega
  have hb := budget_le (Km m) (Gc (m - 1) σ) h δ (m - 1) (one_le_Km hm2) (Gc_pos _ hm1 σ) hh
    hh1 hδ hδK hδ4
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  unfold scale
  show (((m - 1) * NI m σ h δ : ℕ) : ℝ) ≤ _
  have : (((m - 1) * NI m σ h δ : ℕ) : ℝ)
      = Km m * (nSamp (Km m) (Gc (m - 1) σ) h δ (m - 1) : ℝ) := by
    rw [Nat.cast_mul]; rfl
  rw [this]
  linarith

#print axioms err_bound
#print axioms budget_le
#print axioms gap_ge
#print axioms safe_correct
#print axioms safe_cost
#print axioms cnt_schedI
#print axioms id_correct
#print axioms id_cost

end CIGAMF.P13.PaperBParityDecoder
