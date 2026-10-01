import «LeanPaperBParityDecoderV1»

/-!
# Paper B: the TipFinish endpoint, instantiated on the parity experiment

The two `UniformProtocolCertificate`s of `LeanPaperBRateClosureV1` are here CONSTRUCTED -- not
assumed -- for the ONE experiment `parExp sigma` of `LeanPaperBParityExperimentV1` (the
adaptive protocol on the parity channel):

* `safeCert` (order `s = 1`): lower `safeLower`, upper `safeCode` with `safe_correct` and
  `safe_cost`;
* `idCert` (order `s = m - 1`): lower `idLower`, upper `idCode` with `id_correct` and `id_cost`.

All constants depend only on `m` and `sigma`; they are uniform over `0 < h <= 1` and
`0 < delta <= delta0`.  `parity_tip_finish` then closes `TipFinish m hm (parExp sigma)` for every
`m >= 3` and every noise level `sigma > 0`: the safe task has minimax rate
`log(1/delta) / h^2` and identification has rate `log(1/delta) / h^(2(m-1))`, on the SAME
experiment, with the same cost convention.

Scope, stated exactly: the policy class is every randomised adaptive policy with a FINITE
horizon (bounded stopping time), with measurable outputs, on the parity channel with known
`sigma`; worlds are the `m` parity-membership worlds; the loss is `tipLoss m` at tolerance `0`.
-/

namespace CIGAMF.P13.PaperBParityFinish

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBParityExperiment CIGAMF.P13.PaperBParityDecoder
open CIGAMF.P13.PaperBEndgame CIGAMF.P13.PaperBRateClosure

variable {m : ℕ}

/-- The safe tolerance window for `delta`. -/
noncomputable def δS (m : ℕ) : ℝ := min (1 / 4) ((2 : ℝ) ^ (-(4 * ((m : ℝ) - 1))))

/-- The identification tolerance window for `delta`. -/
noncomputable def δI (m : ℕ) : ℝ := min (1 / 16) (1 / (2 * Km m))

/-- **The safe protocol certificate, order `1`.** -/
noncomputable def safeCert (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) :
    UniformProtocolCertificate (parExp σ hσ hm) .safe 1 where
  a := aS m σ
  b := 1 / (4 * ((m : ℝ) - 1))
  C := 1 * (16 * 1 / Gc 1 σ ^ 2 + 1)
  h₀ := 1
  δ₀ := δS m
  a_pos := aS_pos σ hσ
  b_pos := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    apply div_pos one_pos
    linarith
  C_pos := by have := Gc_pos 1 one_pos σ; positivity
  h₀_pos := one_pos
  δ₀_pos := by unfold δS; exact lt_min (by norm_num) (by positivity)
  δ₀_lt_one := by unfold δS; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  lower h δ hh hh1 hδ hδ0 :=
    safeLower σ hσ hm hm2 h δ hh hh1 hδ
      (by have := hδ0.trans (min_le_left _ _); linarith)
      (hδ0.trans (min_le_right _ _))
  upper h δ hh hh1 hδ hδ0 :=
    { code := safeCode σ h δ hm2
      correct := safe_correct σ hσ hm hm2 h δ hh hh1 hδ
        (by have := hδ0.trans (min_le_left _ _); linarith)
      cost := fun w => safe_cost σ hσ hm hm2 h δ hh hh1 hδ (hδ0.trans (min_le_left _ _)) w }

/-- **The identification protocol certificate, order `m - 1`.** -/
noncomputable def idCert (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) :
    UniformProtocolCertificate (parExp σ hσ hm) .identify (m - 1) where
  a := aI m σ
  b := 1 / 4
  C := Km m * (16 * Km m / Gc (m - 1) σ ^ 2 + 1)
  h₀ := 1
  δ₀ := δI m
  a_pos := aI_pos σ hσ
  b_pos := by norm_num
  C_pos := by
    have := Gc_pos (m - 1) (by omega) σ
    have := one_le_Km hm2
    have : 0 < Km m := by linarith
    positivity
  h₀_pos := one_pos
  δ₀_pos := by
    unfold δI
    have := one_le_Km hm2
    exact lt_min (by norm_num) (by apply div_pos one_pos; linarith)
  δ₀_lt_one := by unfold δI; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  lower h δ hh hh1 hδ hδ0 :=
    idLower σ hσ hm hm2 h δ hh hh1 hδ (hδ0.trans (min_le_left _ _))
  upper h δ hh hh1 hδ hδ0 :=
    { code := idCode σ h δ hm hm2
      correct := id_correct σ hσ hm hm2 h δ hh hh1 hδ (hδ0.trans (min_le_right _ _))
      cost := fun w => id_cost σ hσ hm hm2 h δ hh hh1 hδ (hδ0.trans (min_le_right _ _))
        (by have := hδ0.trans (min_le_left _ _); linarith) w }

/-- **Paper B endpoint.**  On the parity experiment with `m >= 3` worlds and noise
`sigma > 0`, the safe task has order `1` and identification has order `m - 1`, on the same
experiment. -/
theorem parity_tip_finish (m : ℕ) (hm : 3 ≤ m) (σ : ℝ) (hσ : 0 < σ) :
    TipFinish m hm (parExp σ hσ (by omega : 0 < m)) :=
  tip_finish_from_protocols m hm (parExp σ hσ (by omega)) (fun _ _ => rfl) le_rfl
    (hεmax (by omega)) (safeCert σ hσ (by omega) (by omega)) (idCert σ hσ (by omega) (by omega))

/-- The two rates on a common rectangle, explicitly. -/
theorem parity_rates (m : ℕ) (hm : 3 ≤ m) (σ : ℝ) (hσ : 0 < σ) :
    HasRate (parExp σ hσ (by omega : 0 < m)) .safe 1 ∧
    HasRate (parExp σ hσ (by omega : 0 < m)) .identify (m - 1) :=
  (parity_tip_finish m hm σ hσ).2.2.2.2

#print axioms safeCert
#print axioms idCert
#print axioms parity_tip_finish
#print axioms parity_rates

end CIGAMF.P13.PaperBParityFinish
