import «LeanPaperBConcentrationV1»
import «LeanPaperBScheduleV1»

/-!
# Paper B: the error of one scheduled test

A fixed-budget decoder runs a scheduled policy and, for a query `j`, sums a bounded feature `f`
of the observations at the rounds the schedule gives to `j`.  If `f` has mean `c` under the
world's law of query `j` and the schedule gives `j` exactly `N` of the first `H` rounds, then
(`test_upper_tail`, `test_lower_tail`)

    P( sum over j-rounds of (f(Y) - c) >= dev N )  <=  exp(-(dev N)^2 / (2H)),

and the same for the lower tail.  The proof is `tail_hist_le` for the feature that is `f` on
query `j` and zero elsewhere, on the full-measure set where the recorded queries follow the
schedule (`hist_sched_ae`).
-/

namespace CIGAMF.P13.PaperBSchedTest

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBChiSq CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperBSchedule

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- The feature that reads `f` on query `j` and nothing elsewhere. -/
noncomputable def onQuery (j : Q) (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ y, |f y| ≤ 1) :
    Feature Q where
  φ q y := if q = j then f y else 0
  meas q := by
    by_cases hq : q = j
    · simp only [hq, if_true]; exact hf
    · simp only [hq, if_false]; exact measurable_const
  bdd q y := by
    by_cases hq : q = j
    · simp only [hq, if_true]; exact hb y
    · simp [hq]

/-- The test statistic: the centred sum of `f` over the rounds the schedule gives to `j`. -/
noncomputable def testSum (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ) (c : ℝ) (H : ℕ)
    (ω : Hist Q H) : ℝ :=
  ∑ i : Fin H, if sched i = j then f (ω i).2 - c else 0

theorem fmean_onQuery (C : Channel W Q) (w : W) (j : Q) (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∀ y, |f y| ≤ 1) (q : Q) :
    fmean C w (onQuery j f hf hb) q = if q = j then fmean C w (onQuery j f hf hb) j else 0 := by
  by_cases hq : q = j
  · rw [if_pos hq, hq]
  · rw [if_neg hq]
    unfold fmean onQuery
    simp [hq]

/-- On the schedule, the centred sum of the query-`j` feature IS the test statistic. -/
theorem centredSum_eq_testSum (C : Channel W Q) (w : W) (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ)
    (hf : Measurable f) (hb : ∀ y, |f y| ≤ 1) (H : ℕ) (ω : Hist Q H)
    (hω : ∀ i : Fin H, (ω i).1 = sched i) :
    centredSum C w (onQuery j f hf hb) H ω
      = testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω := by
  unfold centredSum testSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hω i, fmean_onQuery]
  by_cases hq : sched i = j
  · simp [onQuery, hq]
  · simp [onQuery, hq]

/-- **The upper tail of one scheduled test.** -/
theorem test_upper_tail (C : Channel W Q) (w : W) (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ)
    (hf : Measurable f) (hb : ∀ y, |f y| ≤ 1) (H : ℕ) (hH : 0 < H) (ε : ℝ) (hε : 0 ≤ ε) :
    hist C (schedPolicy sched) w H
        {ω | ε ≤ testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω}
      ≤ ENNReal.ofReal (exp (-(ε ^ 2) / (2 * H))) := by
  have htail := tail_hist_le C (schedPolicy sched) w (onQuery j f hf hb) H hH ε hε
  have hnull := hist_sched_null C sched w H
  calc hist C (schedPolicy sched) w H
        {ω | ε ≤ testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω}
      ≤ hist C (schedPolicy sched) w H
          ({ω | ε ≤ centredSum C w (onQuery j f hf hb) H ω} ∪ (onSched sched H)ᶜ) := by
        refine measure_mono fun ω hω => ?_
        by_cases hon : ω ∈ onSched sched H
        · left
          show ε ≤ centredSum C w (onQuery j f hf hb) H ω
          rw [centredSum_eq_testSum C w sched j f hf hb H ω hon]
          exact hω
        · right; exact hon
    _ ≤ hist C (schedPolicy sched) w H {ω | ε ≤ centredSum C w (onQuery j f hf hb) H ω}
          + hist C (schedPolicy sched) w H (onSched sched H)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (exp (-(ε ^ 2) / (2 * H))) := by rw [hnull, add_zero]; exact htail

theorem neg_bdd (f : ℝ → ℝ) (hb : ∀ y, |f y| ≤ 1) : ∀ y, |(fun y => -f y) y| ≤ 1 := by
  intro y; simpa using hb y

/-- The mean of `-f` is minus the mean of `f`. -/
theorem fmean_neg (C : Channel W Q) (w : W) (j : Q) (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∀ y, |f y| ≤ 1) :
    fmean C w (onQuery j (fun y => -f y) hf.neg (neg_bdd f hb)) j
      = -fmean C w (onQuery j f hf hb) j := by
  unfold fmean onQuery
  simp [integral_neg]

theorem testSum_neg (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ) (c : ℝ) (H : ℕ) (ω : Hist Q H) :
    testSum sched j (fun y => -f y) (-c) H ω = -testSum sched j f c H ω := by
  unfold testSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- **The lower tail of one scheduled test.** -/
theorem test_lower_tail (C : Channel W Q) (w : W) (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ)
    (hf : Measurable f) (hb : ∀ y, |f y| ≤ 1) (H : ℕ) (hH : 0 < H) (ε : ℝ) (hε : 0 ≤ ε) :
    hist C (schedPolicy sched) w H
        {ω | testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω ≤ -ε}
      ≤ ENNReal.ofReal (exp (-(ε ^ 2) / (2 * H))) := by
  have h := test_upper_tail C w sched j (fun y => -f y) hf.neg (neg_bdd f hb) H hH ε hε
  rw [fmean_neg] at h
  refine le_trans (measure_mono fun ω hω => ?_) h
  show ε ≤ testSum sched j (fun y => -f y) (-fmean C w (onQuery j f hf hb) j) H ω
  rw [testSum_neg]
  have : testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω ≤ -ε := hω
  linarith

#print axioms centredSum_eq_testSum
#print axioms test_upper_tail
#print axioms test_lower_tail

end CIGAMF.P13.PaperBSchedTest
