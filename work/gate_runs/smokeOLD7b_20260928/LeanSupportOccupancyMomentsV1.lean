import «LeanSupportPassiveSamplingMassV1»
import «LeanSupportPassiveAnswerMultiplicityV1»

/-! # Support: `L_N` as a random variable, and its first two moments.

`LeanSupportPassiveAnswerMultiplicityV1` proves inequalities about the EXPRESSION
`lambda + b(b-1)(1-2 gamma)^N` and says of itself that `L_N` is not a random
variable there, so nothing in it is a moment. This file supplies the missing
object and the two moments, on the product measure that
`LeanSupportPassiveSamplingMassV1` already builds.

* `unseenCount` — `L_N`, the number of unsafe tips no draw landed on, as a
  function on the sample space `Fin N → Points W`.
* `unseenCount_eq_sum` — it is the sum of the indicators of the `missed` events,
  which is what lets a moment be computed at all.
* `expected_unseen` — `E[L_N] = sum over tips of (1 - p(tip))^N`, by
  `lintegral_finset_sum` and the EQUALITY `miss_probability`.
* `expected_unseen_uniform` — with every tip of mass `gamma`, `E[L_N] = b (1-gamma)^N`,
  i.e. `lambda_N`, now a genuine expectation.
* `pair_miss_probability` — for two DISTINCT tips the chance that neither is ever
  drawn is exactly `(1 - p(w) - p(w'))^N`. This is the fact the second moment
  needs and it was not available before.
* `second_moment` — `E[L_N^2]` as the double sum of pair-miss probabilities, and
  `second_moment_uniform` — `E[L_N^2] = b(1-gamma)^N + b(b-1)(1-2gamma)^N`.

## WHAT THIS DOES NOT ESTABLISH

- These are moments of `L_N`, nothing more. `R_N^* = E[L_N/(a+L_N)]` is still NOT
  proved: it needs the posterior (the counting half is in
  `LeanSupportMinimaxCountingV1`), the Bayes lower bound, and the uniform-unseen
  policy's risk, none of which is here.
- `second_moment_le_lambda_add_sq` DOES now join the two: the inequality itself is
  still `LeanSupportPassiveAnswerMultiplicityV1.missing_second_moment_bound`, but
  both sides of it are here proved equal to the real moments of `unseenCount`, so
  `E[L_N^2] <= E[L_N] + E[L_N]^2` is a statement about the random variable. It
  assumes equal tip masses `gamma = ofReal g` with `0 <= g <= 1/2`.
- Everything is in `ℝ≥0∞`. No real-valued expectation, no integrability argument,
  and no concentration.
- Equal tip masses are a HYPOTHESIS of the two `_uniform` corollaries, not a
  feature of the model; the general statements above them do not assume it.
-/

namespace CIGAMF.P13.SupportOccupancyMoments
open Finset MeasureTheory
open scoped BigOperators ENNReal
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportUnboundedObstruction
open CIGAMF.P13.SupportMultiTipGeometry
open CIGAMF.P13.SupportPassiveSamplingMass
noncomputable section
variable {m : ℕ}

/-- `L_N`: the number of unsafe tips that no draw landed on. -/
def unseenCount (W : Finset (Fin m)) {N : ℕ} (x : Fin N → Points W) : ℕ :=
  (univ.filter (fun w : {w // w ∈ W} => ∀ i, x i ≠ some w)).card

theorem unseenCount_eq_sum (W : Finset (Fin m)) {N : ℕ} (x : Fin N → Points W) :
    (unseenCount W x : ℝ≥0∞)
      = ∑ w : {w // w ∈ W}, (missed W w N).indicator (fun _ => (1:ℝ≥0∞)) x := by
  classical
  unfold unseenCount
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : ∀ i, x i ≠ some w
  · rw [if_pos h, Set.indicator_of_mem (show x ∈ missed W w N from h)]
  · rw [if_neg h, Set.indicator_of_notMem (show x ∉ missed W w N from h)]

/-- `E[L_N]`, from the equality `miss_probability`. -/
theorem expected_unseen (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ) :
    ∫⁻ x, (unseenCount W x : ℝ≥0∞) ∂(iid W p N)
      = ∑ w : {w // w ∈ W}, (1 - p (some w))^N := by
  classical
  simp_rw [unseenCount_eq_sum W]
  rw [lintegral_finset_sum _ (fun w _ =>
    (measurable_const.indicator (missed_measurable W w N)))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [lintegral_indicator (missed_measurable W w N), lintegral_const,
    Measure.restrict_apply_univ, one_mul, miss_probability]

/-- With every tip of mass `gamma`, `E[L_N] = b (1-gamma)^N` -- `lambda_N`, now a
genuine expectation rather than a written-down expression. -/
theorem expected_unseen_uniform (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ)
    (gamma : ℝ≥0∞) (hunif : ∀ w : {w // w ∈ W}, p (some w) = gamma) :
    ∫⁻ x, (unseenCount W x : ℝ≥0∞) ∂(iid W p N)
      = (W.card : ℝ≥0∞) * (1 - gamma)^N := by
  rw [expected_unseen, Finset.sum_congr rfl (fun w _ => by rw [hunif w]),
    Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

/-! ## The pair event, and the second moment -/

/-- Neither of two tips was ever drawn. -/
def missedPair (W : Finset (Fin m)) (w w' : {w // w ∈ W}) (N : ℕ) :
    Set (Fin N → Points W) := {x | ∀ i, x i ≠ some w ∧ x i ≠ some w'}

theorem missedPair_eq_pi (W : Finset (Fin m)) (w w' : {w // w ∈ W}) (N : ℕ) :
    missedPair W w w' N
      = Set.univ.pi (fun _ : Fin N => (({some w, some w'} : Set (Points W))ᶜ)) := by
  ext x
  simp [missedPair, Set.mem_pi, not_or]

theorem missedPair_measurable (W : Finset (Fin m)) (w w' : {w // w ∈ W}) (N : ℕ) :
    MeasurableSet (missedPair W w w' N) := by
  rw [missedPair_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => trivial)

theorem missedPair_eq_inter (W : Finset (Fin m)) (w w' : {w // w ∈ W}) (N : ℕ) :
    missedPair W w w' N = missed W w N ∩ missed W w' N := by
  ext x
  simp [missedPair, missed, Set.mem_inter_iff, forall_and]

/-- THE PAIR FACT. For two DISTINCT tips the chance that neither is ever drawn is
exactly `(1 - p(w) - p(w'))^N`. -/
theorem pair_miss_probability (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ)
    (w w' : {w // w ∈ W}) (hne : w ≠ w') :
    iid W p N (missedPair W w w' N) = (1 - p (some w) - p (some w'))^N := by
  classical
  have hne' : (some w : Points W) ≠ some w' := by
    simpa using hne
  have hpair : (p.toMeasure) ({some w, some w'} : Set (Points W))
      = p (some w) + p (some w') := by
    have hun : ({some w, some w'} : Set (Points W))
        = ({some w} : Set (Points W)) ∪ ({some w'} : Set (Points W)) := by
      rw [Set.singleton_union]
    rw [hun, measure_union (Set.disjoint_singleton.mpr hne') trivial,
      PMF.toMeasure_apply_singleton p _ trivial,
      PMF.toMeasure_apply_singleton p _ trivial]
  have hmeas : ∀ _ : Fin N, (p.toMeasure) (({some w, some w'} : Set (Points W))ᶜ)
      = 1 - p (some w) - p (some w') := by
    intro _
    have hcompl : (p.toMeasure) (({some w, some w'} : Set (Points W))ᶜ)
        = 1 - (p.toMeasure) ({some w, some w'} : Set (Points W)) :=
      prob_compl_eq_one_sub trivial
    rw [hcompl, hpair, tsub_add_eq_tsub_tsub]
  rw [missedPair_eq_pi]
  unfold iid
  rw [Measure.pi_pi, Finset.prod_congr rfl (fun i _ => hmeas i), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- `E[L_N^2]` as the double sum over ordered pairs of tips. -/
theorem second_moment (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ) :
    ∫⁻ x, ((unseenCount W x : ℝ≥0∞))^2 ∂(iid W p N)
      = ∑ w : {w // w ∈ W}, ∑ w' : {w // w ∈ W},
          iid W p N (missed W w N ∩ missed W w' N) := by
  classical
  have hsq : ∀ x : Fin N → Points W, ((unseenCount W x : ℝ≥0∞))^2
      = ∑ w : {w // w ∈ W}, ∑ w' : {w // w ∈ W},
          (missed W w N ∩ missed W w' N).indicator (fun _ => (1:ℝ≥0∞)) x := by
    intro x
    rw [sq, unseenCount_eq_sum W x, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => ?_))
    by_cases h1 : x ∈ missed W w N <;> by_cases h2 : x ∈ missed W w' N <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2,
        Set.mem_inter_iff]
  simp_rw [hsq]
  rw [lintegral_finset_sum _ (fun w _ => by
    refine Finset.measurable_sum _ (fun w' _ => ?_)
    exact measurable_const.indicator
      ((missed_measurable W w N).inter (missed_measurable W w' N)))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [lintegral_finset_sum _ (fun w' _ => measurable_const.indicator
    ((missed_measurable W w N).inter (missed_measurable W w' N)))]
  refine Finset.sum_congr rfl (fun w' _ => ?_)
  rw [lintegral_indicator ((missed_measurable W w N).inter (missed_measurable W w' N)),
    lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- `E[L_N^2]` in closed form when every tip carries the same mass `gamma`:
`b (1-gamma)^N + b(b-1) (1-2 gamma)^N`. The diagonal of the double sum is the
first moment; the off-diagonal is `b(b-1)` genuine PAIR-miss probabilities. -/
theorem second_moment_uniform (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ)
    (gamma : ℝ≥0∞) (hunif : ∀ w : {w // w ∈ W}, p (some w) = gamma) :
    ∫⁻ x, ((unseenCount W x : ℝ≥0∞))^2 ∂(iid W p N)
      = (W.card : ℝ≥0∞) * (1 - gamma)^N
        + ((W.card * (W.card - 1) : ℕ) : ℝ≥0∞) * (1 - 2 * gamma)^N := by
  classical
  have hdiag : ∀ w : {w // w ∈ W},
      iid W p N (missed W w N ∩ missed W w N) = (1 - gamma)^N := by
    intro w
    rw [Set.inter_self, miss_probability, hunif]
  have hoff : ∀ w w' : {w // w ∈ W}, w ≠ w' →
      iid W p N (missed W w N ∩ missed W w' N) = (1 - 2 * gamma)^N := by
    intro w w' hne
    rw [← missedPair_eq_inter, pair_miss_probability W p N w w' hne, hunif, hunif,
      ← tsub_add_eq_tsub_tsub, ← two_mul]
  have hrow : ∀ w : {w // w ∈ W},
      ∑ w' : {w // w ∈ W}, iid W p N (missed W w N ∩ missed W w' N)
        = (1 - gamma)^N + ((W.card - 1 : ℕ) : ℝ≥0∞) * (1 - 2 * gamma)^N := by
    intro w
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w), hdiag w]
    congr 1
    rw [Finset.sum_congr rfl (fun w' hw' => hoff w w' (Finset.ne_of_mem_erase hw').symm),
      Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ w),
      Finset.card_univ, Fintype.card_coe]
  rw [second_moment, Finset.sum_congr rfl (fun w _ => hrow w), Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_coe, mul_add, Nat.cast_mul, mul_assoc]

/-! ## The real-valued moments, and the join with the inequality module

`LeanSupportPassiveAnswerMultiplicityV1.missing_second_moment_bound` is an
inequality between two REAL expressions; its own header says `L_N` is not a random
variable there. The next three theorems turn the two expressions into the actual
first and second moments of `unseenCount` and then apply that inequality, so
`E[L_N^2] <= lambda + lambda^2` becomes a statement about the random variable. -/

/-- `lambda_N = E[L_N]` as a real number. -/
theorem expected_unseen_uniform_real (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ)
    (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hunif : ∀ w : {w // w ∈ W}, p (some w) = ENNReal.ofReal g) :
    (∫⁻ x, (unseenCount W x : ℝ≥0∞) ∂(iid W p N)).toReal
      = (W.card : ℝ) * (1 - g)^N := by
  have h1g : (0:ℝ) ≤ 1 - g := by linarith
  have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal g = ENNReal.ofReal (1 - g) := by
    rw [ENNReal.ofReal_sub _ hg0, ENNReal.ofReal_one]
  rw [expected_unseen_uniform W p N _ hunif, e1, ← ENNReal.ofReal_pow h1g,
    ← ENNReal.ofReal_natCast W.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h1g N))]

/-- `E[L_N^2]` as a real number, in the exact closed form the inequality module
writes down. -/
theorem second_moment_uniform_real (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ)
    (g : ℝ) (hg0 : 0 ≤ g) (hg2 : g ≤ 1/2)
    (hunif : ∀ w : {w // w ∈ W}, p (some w) = ENNReal.ofReal g) :
    (∫⁻ x, ((unseenCount W x : ℝ≥0∞))^2 ∂(iid W p N)).toReal
      = (W.card : ℝ) * (1 - g)^N
        + (W.card : ℝ) * ((W.card : ℝ) - 1) * (1 - 2*g)^N := by
  have h1g : (0:ℝ) ≤ 1 - g := by linarith
  have h12g : (0:ℝ) ≤ 1 - 2*g := by linarith
  have hbb : ((W.card * (W.card - 1) : ℕ) : ℝ)
      = (W.card : ℝ) * ((W.card : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos W.card with h | h
    · simp [h]
    · rw [Nat.cast_mul, Nat.cast_sub h, Nat.cast_one]
  have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal g = ENNReal.ofReal (1 - g) := by
    rw [ENNReal.ofReal_sub _ hg0, ENNReal.ofReal_one]
  have e2 : (1 : ℝ≥0∞) - 2 * ENNReal.ofReal g = ENNReal.ofReal (1 - 2*g) := by
    rw [ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ 2*g), ENNReal.ofReal_one,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    norm_num
  rw [second_moment_uniform W p N _ hunif, e1, e2,
    ← ENNReal.ofReal_pow h1g, ← ENNReal.ofReal_pow h12g,
    ← ENNReal.ofReal_natCast W.card,
    ← ENNReal.ofReal_natCast (W.card * (W.card - 1)),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h1g N))
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h12g N)),
    ENNReal.toReal_ofReal
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h1g N))
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h12g N))), hbb]

/-- THE JOIN. `E[L_N^2] <= lambda + lambda^2` for the actual random variable
`unseenCount`, with `lambda = E[L_N]`. The inequality itself is
`missing_second_moment_bound`; what is new here is that both sides are moments. -/
theorem second_moment_le_lambda_add_sq (W : Finset (Fin m)) (p : PMF (Points W))
    (N : ℕ) (g : ℝ) (hg0 : 0 ≤ g) (hg2 : g ≤ 1/2)
    (hunif : ∀ w : {w // w ∈ W}, p (some w) = ENNReal.ofReal g) :
    (∫⁻ x, ((unseenCount W x : ℝ≥0∞))^2 ∂(iid W p N)).toReal
      ≤ (∫⁻ x, (unseenCount W x : ℝ≥0∞) ∂(iid W p N)).toReal
        + ((∫⁻ x, (unseenCount W x : ℝ≥0∞) ∂(iid W p N)).toReal)^2 := by
  rw [second_moment_uniform_real W p N g hg0 hg2 hunif,
    expected_unseen_uniform_real W p N g hg0 (by linarith) hunif]
  simpa using
    CIGAMF.P13.SupportPassiveAnswerMultiplicity.missing_second_moment_bound
      W.card N g hg0 hg2

#print axioms unseenCount_eq_sum
#print axioms expected_unseen
#print axioms expected_unseen_uniform
#print axioms missedPair_eq_pi
#print axioms missedPair_measurable
#print axioms missedPair_eq_inter
#print axioms pair_miss_probability
#print axioms second_moment
#print axioms second_moment_uniform
#print axioms expected_unseen_uniform_real
#print axioms second_moment_uniform_real
#print axioms second_moment_le_lambda_add_sq

end
end CIGAMF.P13.SupportOccupancyMoments
