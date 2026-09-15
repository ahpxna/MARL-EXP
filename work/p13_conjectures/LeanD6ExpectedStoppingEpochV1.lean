import «LeanD6UniformDiscoveryThresholdV1»

/-! # Step 4: the expected settling epoch

`eventually_correct` says the certification is eventually right almost surely,
but a.s. eventual correctness carries no rate: it does not say WHEN.  The
quantity that does is the index after which no epoch is ever bad again.

    settleIndex x = ∑' s0, 1{ some epoch at or after s0 is bad }

which counts, for each `s0`, whether trouble remains ahead.  On a path with
finitely many bad epochs it equals `last bad index + 1`; on a path with
infinitely many it is `∞`.  So a finite expectation for it is exactly the
statement that the algorithm settles in bounded expected epoch count.

`expected_settle_index` proves `E[settleIndex] <= 4 * eta d r0`, from the same
per-epoch tail `eta*(1/4)^s` used by `expected_bad_epoch_work`, summed twice --
once over the epochs at or after `s0`, once over `s0`.  Combined with Step 3,
`settle_index_threshold` makes the expected settling epoch smaller than any
target once `r0 >= 128*log(8*d/tol)`.

What this is and is not.  It is a last-bad-epoch result for the discovery /
revalidation layer: the layer with eventually correct labels. The last-bad index looks into
the future and is NOT a stopping time for the natural filtration.  It is
NOT the termination of the full adaptive allocation algorithm, and it is not the
`Gamma` rate, because it says nothing about the allocation inside good epochs
nor about phase-interval crossings.  It is the first of those three that the
existing tail estimate can actually pay for.
-/
namespace CIGAMF.P13.D6ExpectedStoppingEpoch
open scoped BigOperators ENNReal
open Finset MeasureTheory
open CIGAMF.P13.D6DiscoveryStopping CIGAMF.P13.D6DiscoveryVectorCertificate
open CIGAMF.P13.D6NuisanceFreeDiscoveryLaw CIGAMF.P13.D6RepeatedDiscovery
open CIGAMF.P13.D6UniformDiscoveryThreshold
noncomputable section
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Trouble still ahead at `s0`. -/
def tailBad (B : Finset J) (a : J) (r0 s0 : ℕ) : Set (Sample J) :=
  ⋃ k : ℕ,bad B a (epochSamples r0 (s0+k))

lemma tailBad_measurable (B : Finset J) (a : J) (r0 s0 : ℕ) :
    MeasurableSet (tailBad B a r0 s0) :=
  MeasurableSet.iUnion (fun k => bad_measurable B a _)

/-- The index after which no epoch is ever bad again. -/
def settleIndex (B : Finset J) (a : J) (r0 : ℕ) (x : Sample J) : ℝ≥0∞ :=
  ∑' s0 : ℕ,(tailBad B a r0 s0).indicator (fun _ => (1:ℝ≥0∞)) x

lemma quarter_le_half : (4⁻¹:ℝ≥0∞) ≤ 2⁻¹ := ENNReal.inv_le_inv.mpr (by norm_num)

lemma tsum_quarter_le_two : ∑' k : ℕ,(4⁻¹:ℝ≥0∞)^k ≤ 2 := by
  calc ∑' k : ℕ,(4⁻¹:ℝ≥0∞)^k ≤ ∑' k : ℕ,(2⁻¹:ℝ≥0∞)^k := by
        apply ENNReal.tsum_le_tsum
        intro k
        gcongr
        norm_num
    _ = 2 := ENNReal.tsum_geometric_two

/-- Trouble ahead decays geometrically in the starting epoch. -/
theorem bad_tail_after (m : J → Fin 4 → ℝ) (B : Finset J) (a : J)
    (hm : ∀ i,(∑ t,signs t*m i t)=target B a i) (r0 : ℕ) (hr0 : 512 ≤ r0) (s0 : ℕ) :
    vectorPath m (tailBad B a r0 s0) ≤ 2*eta (Fintype.card J) r0*(4⁻¹:ℝ≥0∞)^s0 := by
  calc vectorPath m (tailBad B a r0 s0)
      ≤ ∑' k : ℕ,vectorPath m (bad B a (epochSamples r0 (s0+k))) := measure_iUnion_le _
    _ ≤ ∑' k : ℕ,eta (Fintype.card J) r0*(4⁻¹:ℝ≥0∞)^(s0+k) :=
        ENNReal.tsum_le_tsum (fun k => epoch_tail m B a hm r0 hr0 (s0+k))
    _ = eta (Fintype.card J) r0*(4⁻¹:ℝ≥0∞)^s0*∑' k : ℕ,(4⁻¹:ℝ≥0∞)^k := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr (fun k => by rw [pow_add];ring)
    _ ≤ eta (Fintype.card J) r0*(4⁻¹:ℝ≥0∞)^s0*2 :=
        mul_le_mul_of_nonneg_left tsum_quarter_le_two (show 0 ≤ _ from zero_le)
    _ = 2*eta (Fintype.card J) r0*(4⁻¹:ℝ≥0∞)^s0 := by ring

/-- The algorithm settles in bounded expected epoch count. -/
theorem expected_settle_index (m : J → Fin 4 → ℝ) (B : Finset J) (a : J)
    (hm : ∀ i,(∑ t,signs t*m i t)=target B a i) (r0 : ℕ) (hr0 : 512 ≤ r0) :
    (∫⁻ x,settleIndex B a r0 x ∂vectorPath m) ≤ 4*eta (Fintype.card J) r0 := by
  unfold settleIndex
  rw [lintegral_tsum (fun s0 => (measurable_const.indicator
    (tailBad_measurable B a r0 s0)).aemeasurable)]
  calc ∑' s0 : ℕ,∫⁻ x,(tailBad B a r0 s0).indicator (fun _ => (1:ℝ≥0∞)) x ∂vectorPath m
      = ∑' s0 : ℕ,vectorPath m (tailBad B a r0 s0) := by
        refine tsum_congr (fun s0 => ?_)
        rw [lintegral_indicator_const (tailBad_measurable B a r0 s0),one_mul]
    _ ≤ ∑' s0 : ℕ,2*eta (Fintype.card J) r0*(4⁻¹:ℝ≥0∞)^s0 :=
        ENNReal.tsum_le_tsum (fun s0 => bad_tail_after m B a hm r0 hr0 s0)
    _ = 2*eta (Fintype.card J) r0*∑' s0 : ℕ,(4⁻¹:ℝ≥0∞)^s0 := by rw [ENNReal.tsum_mul_left]
    _ ≤ 2*eta (Fintype.card J) r0*2 := mul_le_mul_of_nonneg_left tsum_quarter_le_two (show 0 ≤ _ from zero_le)
    _ = 4*eta (Fintype.card J) r0 := by ring

/-- Uniform in `q`: the expected settling epoch falls below any target once the
revalidation budget clears the logarithmic threshold of Step 3. -/
theorem settle_index_threshold (m : J → Fin 4 → ℝ) (B : Finset J) (a : J)
    (hm : ∀ i,(∑ t,signs t*m i t)=target B a i) (r0 : ℕ) (hr0 : 512 ≤ r0)
    (tol : ℝ) (htol : 0 < tol)
    (hlog : 128*Real.log (4*(Fintype.card J:ℝ)/(tol/2)) ≤ (r0:ℝ)) :
    (∫⁻ x,settleIndex B a r0 x ∂vectorPath m) ≤ ENNReal.ofReal tol := by
  letI : Nonempty J := ⟨a⟩
  have hhalf : (0:ℝ) < tol/2 := by linarith
  have hb := bad_epoch_threshold (Fintype.card J) r0 (tol/2) hhalf Fintype.card_pos hlog
  have h2 : (4:ℝ≥0∞)*eta (Fintype.card J) r0 = 2*(2*eta (Fintype.card J) r0) := by ring
  refine (expected_settle_index m B a hm r0 hr0).trans ?_
  rw [h2]
  refine (mul_le_mul_of_nonneg_left hb (show (0:ℝ≥0∞) ≤ 2 from zero_le)).trans ?_
  have he : (2:ℝ≥0∞)=ENNReal.ofReal 2 := by simp
  rw [he,← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  linarith

#print axioms tailBad_measurable
#print axioms tsum_quarter_le_two
#print axioms bad_tail_after
#print axioms expected_settle_index
#print axioms settle_index_threshold
end
end CIGAMF.P13.D6ExpectedStoppingEpoch
