import «LeanPaperBSchedTestV1»
import «LeanPaperBParityGapV1»
import «LeanPaperBParityChannelV1»

/-!
# Paper B: the nearest-mean test of one parity query, on the actual history law

The decoders of Paper B run a FIXED schedule on the parity channel `parChan` and, for a query
`j >= 1`, compare the sum of the bounded feature `feat j` over the rounds given to `j` with the
two candidate means `n c_+` and `n c_-` (mask `+1` and mask `-1`), choosing the nearer one
(`saysMinus`).  The decoder knows `h` and `sigma`, hence both candidate means; it does not know
the world.

`test_error_plus` / `test_error_minus`: if the schedule gives `j` exactly `n` of the first `H`
rounds, the test errs with probability at most

    2 exp(-(n g / 2)^2 / (2 H)),      g = |c_+ - c_-|,

under the history law of the scheduled policy, in every world.  An error forces the centred sum
of the query-`j` feature to deviate by `n g / 2`, and both tails are `test_upper_tail` /
`test_lower_tail`.  `LeanPaperBParityGapV1.feature_gap_lower` bounds `g` below by a constant
times `h^j`.
-/

namespace CIGAMF.P13.PaperBParityTest

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBChiSq CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperBSchedule CIGAMF.P13.PaperBSchedTest CIGAMF.P13.PaperBParityGap
open CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBParityChannel

variable (m : ℕ)

/-- The law of a parity query `q >= 1` of the channel is the parity observation law. -/
theorem obsLawC_parChan (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) (w q : Fin m)
    (hq : (q : ℕ) ≠ 0) :
    obsLawC (parChan m σ h hσ hh hm) w q = obsLaw q (maskR q (w + 1)) h (var2 σ) := by
  rw [obsLaw_eq_withDensity _ _ _ σ hσ]
  show volume.withDensity (fun y => ENNReal.ofReal (parDens m σ h w q y)) = _
  congr 1
  funext y
  unfold parDens
  rw [if_neg hq]

/-- The feature the test of query `j` reads. -/
noncomputable def jFeat (j : Fin m) : Feature (Fin m) :=
  onQuery j (feat j) (continuous_feat j).measurable (feat_abs_le j)

theorem fmean_jFeat (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) (w j : Fin m)
    (hj : (j : ℕ) ≠ 0) :
    fmean (parChan m σ h hσ hh hm) w (jFeat m j) j
      = featMean j (obsLaw j (maskR j (w + 1)) h (var2 σ)) := by
  unfold fmean featMean
  rw [obsLawC_parChan m σ h hσ hh hm w j hj]
  congr 1
  funext y
  show (if j = j then feat j y else 0) = feat j y
  rw [if_pos rfl]

/-- The two candidate means. -/
noncomputable def cP (j : ℕ) (h σ : ℝ) : ℝ := featMean j (obsLaw j 1 h (var2 σ))
noncomputable def cM (j : ℕ) (h σ : ℝ) : ℝ := featMean j (obsLaw j (-1) h (var2 σ))

/-- The raw sum of the feature over the rounds given to `j`, and their number. -/
noncomputable def rawSum (sched : ℕ → Fin m) (j : Fin m) (H : ℕ) (x : Hist (Fin m) H) : ℝ :=
  ∑ i : Fin H, if sched i = j then feat j (x i).2 else 0

noncomputable def cnt (sched : ℕ → Fin m) (j : Fin m) (H : ℕ) : ℝ :=
  ∑ i : Fin H, if sched i = j then (1 : ℝ) else 0

theorem cnt_nonneg (sched : ℕ → Fin m) (j : Fin m) (H : ℕ) : 0 ≤ cnt m sched j H :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

theorem testSum_eq_raw (sched : ℕ → Fin m) (j : Fin m) (c : ℝ) (H : ℕ) (x : Hist (Fin m) H) :
    testSum sched j (feat j) c H x = rawSum m sched j H x - cnt m sched j H * c := by
  unfold testSum rawSum cnt
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- **The nearest-mean decision**: the test says "mask `-1`". -/
def saysMinus (sched : ℕ → Fin m) (j : Fin m) (h σ : ℝ) (H : ℕ) (x : Hist (Fin m) H) : Prop :=
  |rawSum m sched j H x - cnt m sched j H * cM j h σ|
    < |rawSum m sched j H x - cnt m sched j H * cP j h σ|

theorem measurable_rawSum (sched : ℕ → Fin m) (j : Fin m) (H : ℕ) :
    Measurable (rawSum m sched j H) := by
  unfold rawSum
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases hs : sched i = j
  · simp only [hs, if_pos]
    exact (continuous_feat j).measurable.comp (measurable_snd.comp (measurable_pi_apply i))
  · simp only [hs, if_neg, not_false_eq_true]
    exact measurable_const

theorem measurableSet_saysMinus (sched : ℕ → Fin m) (j : Fin m) (h σ : ℝ) (H : ℕ) :
    MeasurableSet {x | saysMinus m sched j h σ H x} := by
  unfold saysMinus
  have hr := measurable_rawSum m sched j H
  exact measurableSet_lt ((hr.sub measurable_const).abs) ((hr.sub measurable_const).abs)

/-- The deviation an error forces. -/
theorem dev_of_nearer (r n a b : ℝ) (hn : 0 ≤ n) (h : |r - n * b| ≤ |r - n * a|) :
    n * |a - b| / 2 ≤ |r - n * a| := by
  have htri : |n * a - n * b| ≤ |r - n * a| + |r - n * b| := by
    calc |n * a - n * b| = |(r - n * b) - (r - n * a)| := by ring_nf
      _ ≤ |r - n * b| + |r - n * a| := abs_sub _ _
      _ = |r - n * a| + |r - n * b| := add_comm _ _
  have : |n * a - n * b| = n * |a - b| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hn]
  linarith

/-- A deviation of `eps` in absolute value is one of the two tails. -/
theorem abs_ge_split (s ε : ℝ) (h : ε ≤ |s|) : ε ≤ s ∨ s ≤ -ε := by
  rcases le_or_gt 0 s with hs | hs
  · left; rwa [abs_of_nonneg hs] at h
  · right; rw [abs_of_neg hs] at h; linarith

/-- Both tails of the test statistic at deviation `eps`. -/
theorem two_tails (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) (sched : ℕ → Fin m)
    (j w : Fin m) (H : ℕ) (hH : 0 < H) (ε : ℝ) (hε : 0 ≤ ε) (S : Set (Hist (Fin m) H))
    (hS : ∀ x ∈ S, ε ≤ |testSum sched j (feat j)
      (fmean (parChan m σ h hσ hh hm) w (jFeat m j) j) H x|) :
    hist (parChan m σ h hσ hh hm) (schedPolicy sched) w H S
      ≤ 2 * ENNReal.ofReal (exp (-(ε ^ 2) / (2 * H))) := by
  set C := parChan m σ h hσ hh hm
  have hup := test_upper_tail C w sched j (feat j) (continuous_feat j).measurable
    (feat_abs_le j) H hH ε hε
  have hlo := test_lower_tail C w sched j (feat j) (continuous_feat j).measurable
    (feat_abs_le j) H hH ε hε
  calc hist C (schedPolicy sched) w H S
      ≤ hist C (schedPolicy sched) w H
          ({x | ε ≤ testSum sched j (feat j) (fmean C w (jFeat m j) j) H x}
            ∪ {x | testSum sched j (feat j) (fmean C w (jFeat m j) j) H x ≤ -ε}) :=
        measure_mono fun x hx => abs_ge_split _ ε (hS x hx)
    _ ≤ hist C (schedPolicy sched) w H
          {x | ε ≤ testSum sched j (feat j) (fmean C w (jFeat m j) j) H x}
        + hist C (schedPolicy sched) w H
          {x | testSum sched j (feat j) (fmean C w (jFeat m j) j) H x ≤ -ε} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (exp (-(ε ^ 2) / (2 * H)))
        + ENNReal.ofReal (exp (-(ε ^ 2) / (2 * H))) := add_le_add hup hlo
    _ = 2 * ENNReal.ofReal (exp (-(ε ^ 2) / (2 * H))) := (two_mul _).symm

/-- **The test errs rarely when the mask is `+1`.** -/
theorem test_error_plus (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) (sched : ℕ → Fin m)
    (j w : Fin m) (hj : (j : ℕ) ≠ 0) (hmask : maskR j (w + 1) = 1) (H : ℕ) (hH : 0 < H) :
    hist (parChan m σ h hσ hh hm) (schedPolicy sched) w H {x | saysMinus m sched j h σ H x}
      ≤ 2 * ENNReal.ofReal (exp (-((cnt m sched j H * |cP j h σ - cM j h σ| / 2) ^ 2)
          / (2 * H))) := by
  have hfm : fmean (parChan m σ h hσ hh hm) w (jFeat m j) j = cP j h σ := by
    rw [fmean_jFeat m σ h hσ hh hm w j hj, hmask]; rfl
  refine two_tails m σ h hσ hh hm sched j w H hH _
    (div_nonneg (mul_nonneg (cnt_nonneg m sched j H) (abs_nonneg _)) zero_le_two) _ ?_
  intro x hx
  rw [hfm, testSum_eq_raw]
  exact dev_of_nearer _ _ _ _ (cnt_nonneg m sched j H) (le_of_lt hx)

/-- **The test errs rarely when the mask is `-1`.** -/
theorem test_error_minus (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) (sched : ℕ → Fin m)
    (j w : Fin m) (hj : (j : ℕ) ≠ 0) (hmask : maskR j (w + 1) = -1) (H : ℕ) (hH : 0 < H) :
    hist (parChan m σ h hσ hh hm) (schedPolicy sched) w H {x | ¬ saysMinus m sched j h σ H x}
      ≤ 2 * ENNReal.ofReal (exp (-((cnt m sched j H * |cP j h σ - cM j h σ| / 2) ^ 2)
          / (2 * H))) := by
  have hfm : fmean (parChan m σ h hσ hh hm) w (jFeat m j) j = cM j h σ := by
    rw [fmean_jFeat m σ h hσ hh hm w j hj, hmask]; rfl
  refine two_tails m σ h hσ hh hm sched j w H hH _
    (div_nonneg (mul_nonneg (cnt_nonneg m sched j H) (abs_nonneg _)) zero_le_two) _ ?_
  intro x hx
  rw [hfm, testSum_eq_raw, abs_sub_comm (cP j h σ)]
  exact dev_of_nearer _ _ _ _ (cnt_nonneg m sched j H) (not_lt.mp hx)

/-- The gap of query `j`, from the observation law. -/
theorem gap_lower (j : ℕ) (hj : 0 < j) (σ h : ℝ) (hh : 0 < h) (hhj : h ≤ j) :
    2 * Real.sin 1 * (3 / (4 * (j : ℝ))) ^ j * h ^ j * Real.exp (-(σ ^ 2 / 2))
      ≤ |cP j h σ - cM j h σ| := by
  have := feature_gap_lower j hj h hh hhj (var2 σ)
  rw [var2_coe] at this
  exact this

#print axioms fmean_jFeat
#print axioms test_error_plus
#print axioms test_error_minus
#print axioms gap_lower

end CIGAMF.P13.PaperBParityTest
