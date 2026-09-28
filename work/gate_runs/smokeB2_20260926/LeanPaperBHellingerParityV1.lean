import «LeanPaperBHellingerFamilyV1»
import «LeanPaperBObstructionParityV1»

/-!
# Paper B: the general law, both sides, on the parity channel

`parity_safe_from_law` and `parity_id_from_law` (`LeanPaperBObstructionParityV1`) derive the parity
channel's two LOWER rates from the general obstruction law.  This module derives the two UPPER
rates from the general Hellinger tournament, so both sides of both parity rates are corollaries of
the one law.

* `Gc_anti`: the parity decoder's gap constant `Gc k` is antitone in `k`.
* `parity_hel_sep`: two worlds `w ≠ v` differ at the query `sep(w,v) = min(w,v) + 1`, whose
  feature gap is at least `Gc_{sep} h^{sep}` (`gap_ge`).  By `gap_sq_le_hel`, their Hellinger
  information is at least `(Gc_{m-1} h^{sep})^2/8`.
* `parity_kH_graded`: the Hellinger information dominates the graded information
  `C_H h^{2 sep}` with `C_H = Gc_{m-1}^2/8`.
* `parity_resolves_safe`, `parity_resolves_id`: the proved safe orders (`1` for the overlapping
  correspondence, `m - 1` for identification) resolve every obstruction at `C_H h^2` and
  `C_H h^{2(m-1)}`.
* **`parity_safe_general_upper`**, **`parity_id_general_upper`**: the general tournament is safe
  (resp. identifies) with probability `>= 1 - delta` within
  `m^2 ceil(log(m/delta)/(C_H h^{2s}))` queries, `s = 1` and `s = m - 1`.
-/

namespace CIGAMF.P13.PaperBHellingerParity

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperBSchedule
open CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBObstructionLaw CIGAMF.P13.PaperBHellingerTest
open CIGAMF.P13.PaperBHellingerFamily CIGAMF.P13.PaperBSchedTest CIGAMF.P13.PaperBParityGap
open CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBParityChannel
open CIGAMF.P13.PaperBParityExperiment CIGAMF.P13.PaperBParityTest CIGAMF.P13.PaperBParityDecoder
open CIGAMF.P13.PaperBObstructionParity

variable {m : ℕ}

/-- **The gap constant is antitone.** -/
theorem Gc_anti (σ : ℝ) (j k : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) : Gc k σ ≤ Gc j σ := by
  unfold Gc
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hb1 : 3 / (4 * (k : ℝ)) ≤ 3 / (4 * (j : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hb0 : 0 ≤ 3 / (4 * (k : ℝ)) := by positivity
  have hj1 : 3 / (4 * (j : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hp : (3 / (4 * (k : ℝ))) ^ k ≤ (3 / (4 * (j : ℝ))) ^ j :=
    calc (3 / (4 * (k : ℝ))) ^ k ≤ (3 / (4 * (j : ℝ))) ^ k := pow_le_pow_left₀ hb0 hb1 k
      _ ≤ (3 / (4 * (j : ℝ))) ^ j := pow_le_pow_of_le_one (by positivity) hj1 hjk
  have hs := sin_one_pos
  have := Real.exp_pos (-(σ ^ 2 / 2))
  gcongr

/-- The feature mean of query `j` on the channel is the parity feature mean of its mask. -/
theorem int_feat_eq (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ≥0) (w j : Fin m) (hj : (j : ℕ) ≠ 0) :
    ∫ y, feat j y ∂obsLawC (chanAt σ hσ hm (h : ℝ)) w j
      = featMean j (obsLaw j (maskR j (w + 1)) (max (h : ℝ) 0) (var2 σ)) := by
  have := fmean_jFeat m σ (max (h : ℝ) 0) hσ (le_max_right _ 0) hm w j hj
  unfold fmean jFeat onQuery at this
  simp only [if_true] at this
  exact this

/-- **Two worlds carry `(Gc_{m-1} h^{sep})^2/8` of Hellinger information.** -/
theorem parity_hel_sep (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (h : ℝ≥0) (hh : 0 < h) (hh1 : h ≤ 1)
    (w v : Fin m) (hwv : w ≠ v) :
    (Gc (m - 1) σ * (h : ℝ) ^ sepP w v) ^ 2 / 8
      ≤ (kH (chanAt σ hσ (by omega) (h : ℝ)) w v : ℝ) := by
  have hm : 0 < m := by omega
  have hmax : max (h : ℝ) 0 = h := max_eq_left h.2
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hh1R : (h : ℝ) ≤ 1 := by exact_mod_cast hh1
  -- the separating query: the smaller world plus one
  wlog hlt : (w : ℕ) < v generalizing w v
  · have hvw : (v : ℕ) < w := by
      have : (w : ℕ) ≠ v := fun e => hwv (Fin.ext e)
      omega
    have := this v w (Ne.symm hwv) hvw
    rwa [sepP_symm, kH_symm] at this
  have hs : sepP w v = (w : ℕ) + 1 := by unfold sepP; omega
  set j : Fin m := ⟨(w : ℕ) + 1, by have := v.isLt; omega⟩ with hjdef
  have hj0 : (j : ℕ) ≠ 0 := by simp [hjdef]
  have hg := gap_sq_le_hel (chanAt σ hσ hm (h : ℝ)) w v j (feat j) (continuous_feat j).measurable
    (feat_abs_le j)
  rw [int_feat_eq σ hσ hm h w j hj0, int_feat_eq σ hσ hm h v j hj0] at hg
  have hmw : maskR j ((w : ℕ) + 1) = -1 := by unfold maskR; simp [hjdef]
  have hmv : maskR j ((v : ℕ) + 1) = 1 := by unfold maskR; simp [hjdef]; omega
  have hw1 : ((w + 1 : ℕ)) = (w : ℕ) + 1 := rfl
  have hgap : Gc j σ * (h : ℝ) ^ (j : ℕ) ≤ |cP j (h : ℝ) σ - cM j (h : ℝ) σ| :=
    gap_ge σ (h : ℝ) hhR hh1R j j (by simp [hjdef]) le_rfl
  have hmeans : featMean j (obsLaw j (maskR j (w + 1)) (max (h : ℝ) 0) (var2 σ))
        - featMean j (obsLaw j (maskR j (v + 1)) (max (h : ℝ) 0) (var2 σ))
      = cM j (h : ℝ) σ - cP j (h : ℝ) σ := by
    rw [hmax, hmw, hmv]; rfl
  rw [hmeans] at hg
  have hanti : Gc (m - 1) σ ≤ Gc j σ := Gc_anti σ j (m - 1) (by simp [hjdef]) (by
    have := v.isLt; simp [hjdef]; omega)
  have hG0 : 0 ≤ Gc (m - 1) σ := (Gc_pos (m - 1) (by omega) σ).le
  have hpow0 : 0 ≤ (h : ℝ) ^ (j : ℕ) := pow_nonneg hhR.le _
  have hle : Gc (m - 1) σ * (h : ℝ) ^ (j : ℕ) ≤ |cM j (h : ℝ) σ - cP j (h : ℝ) σ| := by
    rw [abs_sub_comm]
    exact (mul_le_mul_of_nonneg_right hanti hpow0).trans hgap
  have hsq : (Gc (m - 1) σ * (h : ℝ) ^ (j : ℕ)) ^ 2 ≤ (cM j (h : ℝ) σ - cP j (h : ℝ) σ) ^ 2 := by
    rw [← sq_abs (cM j (h : ℝ) σ - cP j (h : ℝ) σ)]
    exact pow_le_pow_left₀ (mul_nonneg hG0 hpow0) hle 2
  have hjs : (j : ℕ) = sepP w v := by rw [hs]
  rw [← hjs]
  have hkq : helNN (chanAt σ hσ hm (h : ℝ)) w v j ≤ kH (chanAt σ hσ hm (h : ℝ)) w v :=
    Finset.le_sup (Finset.mem_univ _)
  have hkq' : hel (chanAt σ hσ hm (h : ℝ)) w v j ≤ (kH (chanAt σ hσ hm (h : ℝ)) w v : ℝ) := by
    exact_mod_cast hkq
  linarith

/-- The graded Hellinger constant `C_H = Gc_{m-1}^2 / 8`. -/
noncomputable def CH (m : ℕ) (σ : ℝ) : ℝ≥0 := ⟨Gc (m - 1) σ ^ 2 / 8, by positivity⟩

/-- **The Hellinger information dominates the graded information `C_H h^{2 sep}`.** -/
theorem parity_kH_graded (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (h : ℝ≥0) (hh : 0 < h)
    (hh1 : h ≤ 1) (w v : Fin m) (hwv : w ≠ v) :
    graded sepP (CH m σ) h w v ≤ kH (chanAt σ hσ (by omega) (h : ℝ)) w v := by
  have := parity_hel_sep σ hσ hm2 h hh hh1 w v hwv
  show ((CH m σ * h ^ (2 * sepP w v) : ℝ≥0) : ℝ) ≤ _
  have hC : ((CH m σ : ℝ≥0) : ℝ) = Gc (m - 1) σ ^ 2 / 8 := rfl
  push_cast
  rw [hC]
  calc Gc (m - 1) σ ^ 2 / 8 * (h : ℝ) ^ (2 * sepP w v)
      = (Gc (m - 1) σ * (h : ℝ) ^ sepP w v) ^ 2 / 8 := by rw [pow_mul]; ring
    _ ≤ _ := this

theorem resolves_of_le {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
    (κ1 κ2 : W → W → ℝ≥0) (safe : W → Finset A) (t : ℝ≥0)
    (hle : ∀ w v, w ≠ v → κ1 w v ≤ κ2 w v) (h : Resolves κ1 safe t) : Resolves κ2 safe t := by
  intro H hH
  obtain ⟨w, hw, v, hv, hne, ht⟩ := h H hH
  exact ⟨w, hw, v, hv, hne, ht.trans (hle w v hne)⟩

theorem CH_pos (σ : ℝ) (hm2 : 2 ≤ m) : 0 < CH m σ := by
  show (0 : ℝ) < Gc (m - 1) σ ^ 2 / 8
  have := Gc_pos (m - 1) (by omega) σ
  positivity

/-- **Every obstruction of the overlapping correspondence is resolved at `C_H h^2`.** -/
theorem parity_resolves_safe (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (h : ℝ≥0) (hh : 0 < h)
    (hh1 : h < 1) :
    Resolves (kH (chanAt σ hσ (by omega) (h : ℝ))) (coSafe : Fin m → Finset (Fin m))
      (CH m σ * h ^ (2 * 1)) :=
  resolves_of_le _ _ _ _ (fun w v hwv => parity_kH_graded σ hσ hm2 h hh hh1.le w v hwv)
    ((graded_resolves_iff sepP coSafe (CH m σ) h (CH_pos σ hm2) hh hh1 1).mpr
      (parity_coSafe_order (m := m) hm2).1)

/-- **Every obstruction of identification is resolved at `C_H h^{2(m-1)}`.** -/
theorem parity_resolves_id (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (h : ℝ≥0) (hh : 0 < h)
    (hh1 : h < 1) :
    Resolves (kH (chanAt σ hσ (by omega) (h : ℝ))) (fun w : Fin m => ({w} : Finset (Fin m)))
      (CH m σ * h ^ (2 * (m - 1))) :=
  resolves_of_le _ _ _ _ (fun w v hwv => parity_kH_graded σ hσ hm2 h hh hh1.le w v hwv)
    ((graded_resolves_iff sepP (fun w : Fin m => ({w} : Finset (Fin m))) (CH m σ) h
      (CH_pos σ hm2) hh hh1 (m - 1)).mpr (parity_id_order (m := m) hm2).1)

/-- **The general law attains the parity safe decision's rate.**  With
`n >= log(m/delta)/(C_H h^2)` rounds per pair, the general Hellinger tournament is safe with
probability `>= 1 - delta` at every world, within `m^2 n` queries. -/
theorem parity_safe_general_upper (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (h : ℝ≥0) (hh : 0 < h)
    (hh1 : h < 1) (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (hn : Real.log ((m : ℝ) / δ) / ((CH m σ * h ^ (2 * 1) : ℝ≥0) : ℝ) ≤ n) :
    (∀ w : Fin m, hist (chanAt σ hσ (by omega) (h : ℝ))
        (schedPolicy (tSched (chanAt σ hσ (by omega) (h : ℝ)) (CH m σ * h ^ (2 * 1)) n)) w
        (Fintype.card (Fin m × Fin m) * n)
        {ω | decode (coSafe : Fin m → Finset (Fin m))
            (pairSet (kH (chanAt σ hσ (by omega) (h : ℝ))) (CH m σ * h ^ (2 * 1)))
            (beatH (chanAt σ hσ (by omega) (h : ℝ)) (CH m σ * h ^ (2 * 1)) n) ⟨0, by omega⟩ ω
          ∉ (coSafe w : Finset (Fin m))} ≤ ENNReal.ofReal δ)
      ∧ ∀ w : Fin m, costN (chanAt σ hσ (by omega) (h : ℝ))
          (schedPolicy (tSched (chanAt σ hσ (by omega) (h : ℝ)) (CH m σ * h ^ (2 * 1)) n)) w
          (Fintype.card (Fin m × Fin m) * n) ≤ ((m ^ 2 * n : ℕ) : ℝ≥0∞) := by
  have ht : 0 < CH m σ * h ^ (2 * 1) := mul_pos (CH_pos σ hm2) (pow_pos hh _)
  have hn' : Real.log ((Fintype.card (Fin m) : ℝ) / δ) / ((CH m σ * h ^ (2 * 1) : ℝ≥0) : ℝ)
      ≤ n := by rwa [Fintype.card_fin]
  obtain ⟨h1, h2⟩ := hellinger_tournament (chanAt σ hσ (by omega) (h : ℝ))
    (coSafe : Fin m → Finset (Fin m)) _ ht (parity_resolves_safe σ hσ hm2 h hh hh1)
    ⟨0, by omega⟩ δ hδ n hn'
  exact ⟨h1, fun w => (h2 w).trans (le_of_eq (by rw [Fintype.card_fin]))⟩

/-- **The general law attains the parity identification rate.** -/
theorem parity_id_general_upper (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (h : ℝ≥0) (hh : 0 < h)
    (hh1 : h < 1) (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (hn : Real.log ((m : ℝ) / δ) / ((CH m σ * h ^ (2 * (m - 1)) : ℝ≥0) : ℝ) ≤ n) :
    (∀ w : Fin m, hist (chanAt σ hσ (by omega) (h : ℝ))
        (schedPolicy (tSched (chanAt σ hσ (by omega) (h : ℝ)) (CH m σ * h ^ (2 * (m - 1))) n)) w
        (Fintype.card (Fin m × Fin m) * n)
        {ω | decode (fun w : Fin m => ({w} : Finset (Fin m)))
            (pairSet (kH (chanAt σ hσ (by omega) (h : ℝ))) (CH m σ * h ^ (2 * (m - 1))))
            (beatH (chanAt σ hσ (by omega) (h : ℝ)) (CH m σ * h ^ (2 * (m - 1))) n)
            ⟨0, by omega⟩ ω ∉ ({w} : Finset (Fin m))} ≤ ENNReal.ofReal δ)
      ∧ ∀ w : Fin m, costN (chanAt σ hσ (by omega) (h : ℝ))
          (schedPolicy (tSched (chanAt σ hσ (by omega) (h : ℝ)) (CH m σ * h ^ (2 * (m - 1))) n))
          w (Fintype.card (Fin m × Fin m) * n) ≤ ((m ^ 2 * n : ℕ) : ℝ≥0∞) := by
  have ht : 0 < CH m σ * h ^ (2 * (m - 1)) := mul_pos (CH_pos σ hm2) (pow_pos hh _)
  have hn' : Real.log ((Fintype.card (Fin m) : ℝ) / δ)
      / ((CH m σ * h ^ (2 * (m - 1)) : ℝ≥0) : ℝ) ≤ n := by rwa [Fintype.card_fin]
  obtain ⟨h1, h2⟩ := hellinger_tournament (chanAt σ hσ (by omega) (h : ℝ))
    (fun w : Fin m => ({w} : Finset (Fin m))) _ ht (parity_resolves_id σ hσ hm2 h hh hh1)
    ⟨0, by omega⟩ δ hδ n hn'
  exact ⟨h1, fun w => (h2 w).trans (le_of_eq (by rw [Fintype.card_fin]))⟩

#print axioms Gc_anti
#print axioms parity_hel_sep
#print axioms parity_kH_graded
#print axioms parity_resolves_safe
#print axioms parity_resolves_id
#print axioms parity_safe_general_upper
#print axioms parity_id_general_upper

end CIGAMF.P13.PaperBHellingerParity
