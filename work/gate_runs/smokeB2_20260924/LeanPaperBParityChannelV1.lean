import «LeanPaperBParityChiSqV1»
import «LeanPaperBProtocolV1»

/-!
# Paper B: the parity-membership experiment as a `Channel`

The concrete channel of Paper B, packaged for the adaptive protocol of `LeanPaperBProtocolV1`:

* worlds `w : Fin m`, world `w` being the paper's world `w + 1 ∈ {1, ..., m}`;
* queries `q : Fin m`; `q = 0` is the DUMMY -- pure noise `N(0, sigma^2)`, the same law in
  every world -- and `q = j >= 1` is the parity query `j`, whose mask is `-1` exactly in
  world `j` (`maskR`);
* the density of query `j >= 1` is `pdens j mask h sigma`, the density of `obsLaw`
  (`LeanPaperBParityChiSqV1.obsLaw_eq_withDensity`).

Per-query chi-squares between two worlds (`parChan_chi_le`): zero when the query cannot tell
them apart -- the dummy, or a query that names neither -- and at most `parC j sigma h0 h^(2j)`
otherwise.  So a pair's information per query is governed by the queries that NAME one of the
two worlds, which is where the resolving orders `s_safe = 1` and `s_id = m - 1` come from.
-/

namespace CIGAMF.P13.PaperBParityChannel

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBProtocol

variable (m : ℕ)

/-- The observation density of query `q` in world `w`. -/
noncomputable def parDens (σ h : ℝ) (w q : Fin m) (y : ℝ) : ℝ :=
  if (q : ℕ) = 0 then gaussianPDFReal 0 (var2 σ) y
  else pdens q (maskR q (w + 1)) h σ y

theorem maskR_pm (j w : ℕ) : maskR j w = 1 ∨ maskR j w = -1 := by
  unfold maskR; split_ifs <;> simp

/-- **The parity channel.** -/
noncomputable def parChan (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) :
    Channel (Fin m) (Fin m) where
  dens := parDens m σ h
  dummy := ⟨0, hm⟩
  meas := by
    intro w q
    unfold parDens
    split_ifs
    · exact (measurable_gaussianPDFReal 0 (var2 σ))
    · exact (continuous_pdens _ _ _ _).measurable
  pos := by
    intro w q y
    unfold parDens
    split_ifs with hq
    · exact gaussianPDFReal_pos _ _ _ (var2_ne_zero σ hσ)
    · exact pdens_pos q (Nat.pos_of_ne_zero hq) σ h h hσ hh le_rfl _ (maskR_pm _ _) y
  mass := by
    intro w q
    unfold parDens
    split_ifs
    · exact lintegral_gaussianPDF_eq_one 0 (var2_ne_zero σ hσ)
    · exact lintegral_pdens _ _ _ σ hσ
  dummy_same := by
    intro w w' y
    unfold parDens
    simp

/-- A query tells two worlds apart only if it names one of them. -/
theorem parDens_eq_of_masks (σ h : ℝ) (w w' q : Fin m)
    (hmask : maskR q (w + 1) = maskR q (w' + 1)) (y : ℝ) :
    parDens m σ h w q y = parDens m σ h w' q y := by
  unfold parDens
  split_ifs
  · rfl
  · rw [hmask]

/-- **The per-query chi-square between any two worlds.** -/
theorem parChan_chi_le (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hhh : h ≤ h₀) (hm : 0 < m)
    (w w' q : Fin m) :
    chi (parChan m σ h hσ hh hm) w w' q
      ≤ if maskR q (w + 1) = maskR q (w' + 1) then 0
        else ENNReal.ofReal (parC q σ h₀ * h ^ (2 * (q : ℕ))) := by
  unfold chi
  split_ifs with hmask
  · have : ∀ y, (parChan m σ h hσ hh hm).dens w q y = (parChan m σ h hσ hh hm).dens w' q y :=
      fun y => parDens_eq_of_masks m σ h w w' q hmask y
    simp [this]
  · have hq : (q : ℕ) ≠ 0 := by
      intro hq0
      apply hmask
      unfold maskR
      rw [if_neg (by omega), if_neg (by omega)]
    show ∫⁻ y, ENNReal.ofReal ((parDens m σ h w q y - parDens m σ h w' q y) ^ 2
        / parDens m σ h w' q y) ≤ _
    unfold parDens
    simp only [hq, if_false]
    exact parity_chiSq_le q (Nat.pos_of_ne_zero hq) σ h h₀ hσ hh hhh _ _ (maskR_pm _ _)
      (maskR_pm _ _)

/-- Worlds `w` and `w'` differ at query `q >= 1` only when `q` names one of them. -/
theorem masks_differ_iff (q w w' : ℕ) (hww : w ≠ w') :
    maskR q w ≠ maskR q w' ↔ (q = w ∨ q = w') := by
  unfold maskR
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [if_neg hc.1, if_neg hc.2] at h
    exact h rfl
  · rintro (rfl | rfl)
    · rw [if_pos rfl, if_neg hww]; norm_num
    · rw [if_neg (Ne.symm hww), if_pos rfl]; norm_num

#print axioms parChan_chi_le
#print axioms masks_differ_iff

end CIGAMF.P13.PaperBParityChannel
