import «LeanPaperBVisibleV1»
import «LeanPaperBHellingerParityV1»

/-!
# Paper B: the per-world decision law on the parity channel

`decision_order_visible` (`LeanPaperBVisibleV1`) gives the two-sided per-world law
`c/|Q| h^{2 d(w)} ≤ D_h(w) ≤ C h^{2 d(w)}` on any channel whose queries either see a pair with
graded information or are blind to it. On the parity channel the blind side and the upper side
were proved on `χ²` (`parChan_chi_le`), but the lower side only for the best query of a pair and
in Hellinger (`parity_hel_sep`). This module proves the missing per-query lower bound, on `χ²`,
at **every** visible query, and instantiates the law.

* `sqrt_sub_sq_le`, `hel_le_chi`: `2 H²_q ≤ χ²_q` for every channel and query
  (`(√p - √q)² ≤ (p - q)²/q` pointwise, and `∫(√p - √q)² = 2 H²`).
* `par_gap_visible`: if query `q` sees the pair `(w, w')` (it names one of them), the parity
  feature `feat q` has mean gap at least `Gc_q h^q` between the two worlds (`gap_ge`).
* **`par_chi_visible`**: hence `χ²_q(w, w') ≥ Gc_q² h^{2q} / 4`, and uniformly
  (`par_chi_visible_unif`) `χ²_q(w, w') ≥ cW h^{2q}` with `cW = Gc_{m-1}² / 4 > 0`.
  The route is feature gap → `l1` → Hellinger (`gap_sq_le_hel`) → `χ²` (`hel_le_chi`).
* `parKap`: the per-query `χ²` as a real number; `parKap_upper` (visible, `≤ CW h^{2q}` with
  `CW = Σ_{i<m} parC_i`), `parKap_blind` (`= 0`), `parKap_lower` (visible, `≥ cW h^{2q}`).
* **`parity_world_law`**: the two-sided per-world law on the parity channel, for every safe
  correspondence: with `d(w)` the decision order of the parity order table `parSq`,
  `cW/m · h^{2 d(w)} ≤ D_h(w)` and, when `d(w) ≥ 1`, `D_h(w) ≤ CW h^{2 d(w)}`.
* `parity_id_order`: for identification (`safe w = {w}`) the decision order is
  `d(w) = min(w + 1, m - 1)` in the paper's numbering (`w + 1 ∈ {1, …, m}`);
  **`parity_id_world_law`**: `D_h(w) ≍ h^{2 min(w+1, m-1)}` with the explicit constants above.
* `parity_world_instance`: the hypotheses are satisfiable (`m = 3`, `σ = 1`, `h = 1/2`,
  `h₀ = 1`), and `cW_pos`: the lower constant is positive.
-/

namespace CIGAMF.P13.PaperBParityWorld

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperBSchedule
open CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBObstructionLaw CIGAMF.P13.PaperBHellingerTest
open CIGAMF.P13.PaperBHellingerFamily CIGAMF.P13.PaperBSchedTest CIGAMF.P13.PaperBParityGap
open CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBParityChannel
open CIGAMF.P13.PaperBParityExperiment CIGAMF.P13.PaperBParityTest CIGAMF.P13.PaperBParityDecoder
open CIGAMF.P13.PaperBObstructionParity CIGAMF.P13.PaperBHellingerParity
open CIGAMF.P13.PaperBVisible CIGAMF.P13.PaperBDecisionOrder

/-! ## 1. Hellinger below chi-square, per query -/

/-- **Pointwise**: `(√a - √b)² ≤ (a - b)²/b`. -/
theorem sqrt_sub_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 / b := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb.le
  have hra := Real.sqrt_nonneg a
  have hrb := Real.sqrt_nonneg b
  have hprod : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    nlinarith
  have e : (a - b) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [← mul_pow, hprod]
  have hle : b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by nlinarith
  rw [e, le_div_iff₀ hb]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

section General

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- **`2 H²_q ≤ χ²_q`** for every channel and query. -/
theorem hel_le_chi (C : Channel W Q) (w v : W) (q : Q) :
    ENNReal.ofReal (2 * hel C w v q) ≤ chi C w v q := by
  set A := ∫⁻ y, ENNReal.ofReal ((Real.sqrt (C.dens w q y) - Real.sqrt (C.dens v q y)) ^ 2)
    with hAdef
  have hA : A + 2 * bc C w v q = 2 := lint_sqdiff C w v q
  have hbc := bc_ne_top C w v q
  have hAtop : A ≠ ⊤ := by
    intro h; rw [h, top_add] at hA; exact ENNReal.top_ne_ofNat hA
  have hAr : A.toReal = 2 - 2 * (bc C w v q).toReal := by
    have := congrArg ENNReal.toReal hA
    rw [ENNReal.toReal_add hAtop (ENNReal.mul_ne_top (by simp) hbc), ENNReal.toReal_mul] at this
    simp at this
    linarith
  have h1 : ENNReal.ofReal (2 * hel C w v q) = A := by
    unfold hel
    rw [← ENNReal.ofReal_toReal hAtop, hAr]
    congr 1
    ring
  rw [h1, hAdef]
  unfold chi
  refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
  exact sqrt_sub_sq_le _ _ (C.pos w q y).le (C.pos v q y)

end General

/-! ## 2. The per-query lower bound on the parity channel -/

variable {m : ℕ}

/-- The feature mean of query `j` on the parity channel. -/
theorem int_feat_par (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) (w j : Fin m)
    (hj : (j : ℕ) ≠ 0) :
    ∫ y, feat j y ∂obsLawC (parChan m σ h hσ hh hm) w j
      = featMean j (obsLaw j (maskR j (w + 1)) h (var2 σ)) := by
  have := fmean_jFeat m σ h hσ hh hm w j hj
  unfold fmean jFeat onQuery at this
  simp only [if_true] at this
  exact this

/-- **A visible query has feature gap `Gc_q h^q`.** -/
theorem par_gap_visible (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1) (hm : 0 < m)
    (w w' q : Fin m) (hww : w ≠ w') (hv : parVis m q w w') :
    Gc q σ * h ^ (q : ℕ) ≤ |∫ y, feat q y ∂obsLawC (parChan m σ h hσ hh.le hm) w q
        - ∫ y, feat q y ∂obsLawC (parChan m σ h hσ hh.le hm) w' q| := by
  obtain ⟨hq0, hq⟩ := hv
  rw [int_feat_par σ h hσ hh.le hm w q hq0, int_feat_par σ h hσ hh.le hm w' q hq0]
  have hne : (w : ℕ) ≠ w' := fun e => hww (Fin.ext e)
  have hg := gap_ge σ h hh hh1 q q (by omega) le_rfl
  rcases hq with hq | hq
  · have h1 : maskR q ((w : ℕ) + 1) = -1 := by unfold maskR; rw [if_pos hq]
    have h2 : maskR q ((w' : ℕ) + 1) = 1 := by unfold maskR; rw [if_neg (by omega)]
    rw [h1, h2]
    show Gc q σ * h ^ (q : ℕ) ≤ |cM q h σ - cP q h σ|
    rwa [abs_sub_comm]
  · have h1 : maskR q ((w : ℕ) + 1) = 1 := by unfold maskR; rw [if_neg (by omega)]
    have h2 : maskR q ((w' : ℕ) + 1) = -1 := by unfold maskR; rw [if_pos hq]
    rw [h1, h2]
    exact hg

/-- **Per-query `χ²` lower bound at every visible query**: `χ²_q(w,w') ≥ Gc_q² h^{2q}/4`. -/
theorem par_chi_visible (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1) (hm : 0 < m)
    (w w' q : Fin m) (hww : w ≠ w') (hv : parVis m q w w') :
    ENNReal.ofReal (Gc q σ ^ 2 / 4 * h ^ (2 * (q : ℕ)))
      ≤ chi (parChan m σ h hσ hh.le hm) w w' q := by
  have hgap := par_gap_visible σ h hσ hh hh1 hm w w' q hww hv
  have hsq := gap_sq_le_hel (parChan m σ h hσ hh.le hm) w w' q (feat q)
    (continuous_feat q).measurable (feat_abs_le q)
  set D := ∫ y, feat q y ∂obsLawC (parChan m σ h hσ hh.le hm) w q
    - ∫ y, feat q y ∂obsLawC (parChan m σ h hσ hh.le hm) w' q with hD
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hel_le_chi _ w w' q)
  have hq0 : 0 < (q : ℕ) := Nat.pos_of_ne_zero hv.1
  have hG0 : 0 ≤ Gc q σ * h ^ (q : ℕ) := mul_nonneg (Gc_pos q hq0 σ).le (pow_nonneg hh.le _)
  have h2 : (Gc q σ * h ^ (q : ℕ)) ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs D]
    exact pow_le_pow_left₀ hG0 hgap 2
  calc Gc q σ ^ 2 / 4 * h ^ (2 * (q : ℕ)) = (Gc q σ * h ^ (q : ℕ)) ^ 2 / 4 := by
        rw [pow_mul]; ring
    _ ≤ 2 * hel (parChan m σ h hσ hh.le hm) w w' q := by linarith

/-- The uniform lower constant `cW = Gc_{m-1}² / 4`. -/
noncomputable def cW (m : ℕ) (σ : ℝ) : ℝ := Gc (m - 1) σ ^ 2 / 4

theorem cW_pos (σ : ℝ) (hm2 : 2 ≤ m) : 0 < cW m σ := by
  unfold cW
  have := Gc_pos (m - 1) (by omega) σ
  positivity

/-- **Uniform per-query lower bound**: `χ²_q(w,w') ≥ cW h^{2q}` at every visible query. -/
theorem par_chi_visible_unif (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hm2 : 2 ≤ m) (w w' q : Fin m) (hww : w ≠ w') (hv : parVis m q w w') :
    ENNReal.ofReal (cW m σ * h ^ (2 * (q : ℕ)))
      ≤ chi (parChan m σ h hσ hh.le (by omega)) w w' q := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (par_chi_visible σ h hσ hh hh1 (by omega)
    w w' q hww hv)
  have hq1 : 1 ≤ (q : ℕ) := Nat.pos_of_ne_zero hv.1
  have hqm : (q : ℕ) ≤ m - 1 := by have := q.isLt; omega
  have hanti := Gc_anti σ q (m - 1) hq1 hqm
  have hG0 : 0 ≤ Gc (m - 1) σ := (Gc_pos (m - 1) (by omega) σ).le
  have hsq : Gc (m - 1) σ ^ 2 ≤ Gc q σ ^ 2 := pow_le_pow_left₀ hG0 hanti 2
  unfold cW
  have hp : 0 ≤ h ^ (2 * (q : ℕ)) := pow_nonneg hh.le _
  have : Gc (m - 1) σ ^ 2 / 4 ≤ Gc q σ ^ 2 / 4 := by linarith
  exact mul_le_mul_of_nonneg_right this hp

/-! ## 3. The per-query information as a real number, and its three bounds -/

/-- The per-query `χ²` of the parity channel, as a real number. -/
noncomputable def parKap (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) (q w w' : Fin m) : ℝ :=
  (chi (parChan m σ h hσ hh hm) w w' q).toReal

/-- The uniform upper constant `CW = Σ_{i<m} parC_i`. -/
noncomputable def CW (m : ℕ) (σ h₀ : ℝ) : ℝ := ∑ i ∈ Finset.range m, parC i σ h₀

theorem CW_nonneg (σ h₀ : ℝ) (hσ : 0 < σ) : 0 ≤ CW m σ h₀ :=
  Finset.sum_nonneg fun i _ => parC_nonneg i σ h₀ hσ

theorem parC_le_CW (σ h₀ : ℝ) (hσ : 0 < σ) (q : Fin m) : parC q σ h₀ ≤ CW m σ h₀ :=
  Finset.single_le_sum (f := fun i => parC i σ h₀) (fun i _ => parC_nonneg i σ h₀ hσ)
    (Finset.mem_range.mpr q.isLt)

theorem chi_visible_le (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hhh : h ≤ h₀) (hm : 0 < m)
    (q w w' : Fin m) (hww : w ≠ w') (hv : parVis m q w w') :
    chi (parChan m σ h hσ hh hm) w w' q ≤ ENNReal.ofReal (parC q σ h₀ * h ^ (2 * (q : ℕ))) := by
  have h1 := parChan_chi_le m σ h h₀ hσ hh hhh hm w w' q
  rwa [if_neg ((par_vis_iff m q w w' hww).mpr hv)] at h1

/-- **Upper side at a visible query.** -/
theorem parKap_upper (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hhh : h ≤ h₀) (hm : 0 < m)
    (q w w' : Fin m) (hww : w ≠ w') (hv : parVis m q w w') :
    parKap σ h hσ hh hm q w w' ≤ CW m σ h₀ * h ^ (2 * (q : ℕ)) := by
  unfold parKap
  have hp : 0 ≤ h ^ (2 * (q : ℕ)) := pow_nonneg hh _
  refine (ENNReal.toReal_le_of_le_ofReal (mul_nonneg (CW_nonneg σ h₀ hσ) hp) ?_)
  refine (chi_visible_le σ h h₀ hσ hh hhh hm q w w' hww hv).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (parC_le_CW σ h₀ hσ q) hp

/-- **A blind query carries nothing.** -/
theorem parKap_blind (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) (q w w' : Fin m)
    (hv : ¬ parVis m q w w') : parKap σ h hσ hh hm q w w' = 0 := by
  unfold parKap
  have hmask : maskR q ((w : ℕ) + 1) = maskR q ((w' : ℕ) + 1) := by
    by_cases hww : w = w'
    · rw [hww]
    · by_contra hne
      exact hv ((par_vis_iff m q w w' hww).mp hne)
  have h1 := parChan_chi_le m σ h h hσ hh le_rfl hm w w' q
  rw [if_pos hmask] at h1
  rw [nonpos_iff_eq_zero.mp h1, ENNReal.toReal_zero]

/-- **Lower side at a visible query.** -/
theorem parKap_lower (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1) (hhh : h ≤ h₀)
    (hm2 : 2 ≤ m) (q w w' : Fin m) (hww : w ≠ w') (hv : parVis m q w w') :
    cW m σ * h ^ (2 * (q : ℕ)) ≤ parKap σ h hσ hh.le (by omega) q w w' := by
  unfold parKap
  have hfin : chi (parChan m σ h hσ hh.le (by omega)) w w' q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (chi_visible_le σ h h₀ hσ hh.le hhh (by omega) q w w' hww hv)
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp
    (par_chi_visible_unif σ h hσ hh hh1 hm2 w w' q hww hv)

/-! ## 4. The per-world law on the parity channel -/

/-- **The two-sided per-world decision law on the parity channel**, for every safe
correspondence, with `κ = χ²` per query and explicit constants `cW`, `CW`. -/
theorem parity_world_law [NeZero m] {A : Type*} [Fintype A] [DecidableEq A] (σ h h₀ : ℝ)
    (hσ : 0 < σ) (hm2 : 2 ≤ m) (hh : 0 < h) (hh1 : h ≤ 1) (hhh : h ≤ h₀)
    (safe : Fin m → Finset A) (hsafe : ∀ w, (safe w).Nonempty) (w : Fin m) :
    (∃ a ∈ safe w, ∀ l, a ∉ safe l →
      cW m σ / m * h ^ (2 * dOrder (parSq m) safe hsafe w)
        ≤ ∑ q, (1 / (m : ℝ)) * parKap σ h hσ hh.le (by omega) q w l)
    ∧ (1 ≤ dOrder (parSq m) safe hsafe w → ∀ a ∈ safe w, ∀ α : Fin m → ℝ,
        (∀ q, 0 ≤ α q) → ∑ q, α q = 1 →
        ∃ l, a ∉ safe l ∧ ∑ q, α q * parKap σ h hσ hh.le (by omega) q w l
          ≤ CW m σ h₀ * h ^ (2 * dOrder (parSq m) safe hsafe w)) := by
  have hm : 0 < m := by omega
  have key := decision_order_visible (parVis m) (fun q _ _ => (q : ℕ)) m
    (parKap σ h hσ hh.le hm) (cW m σ) (CW m σ h₀) h safe hsafe (CW_nonneg σ h₀ hσ)
    (cW_pos σ hm2).le hh.le hh1
    (fun q u v huv hv => parKap_upper σ h h₀ hσ hh.le hhh hm q u v huv hv)
    (fun q u v huv hv => parKap_lower σ h h₀ hσ hh hh1 hhh hm2 q u v huv hv)
    (fun q u v hv => parKap_blind σ h hσ hh.le hm q u v hv)
    (fun u v huv => par_cover m u v huv) (fun q _ _ _ => q.isLt.le)
    (fun q u v => ENNReal.toReal_nonneg) w
  simp only [Fintype.card_fin] at key
  exact key

/-! ## 5. Identification: the decision order is `min(w + 1, m - 1)` -/

/-- **The identification order of world `w`** (paper numbering `w + 1`). -/
theorem parity_id_order [NeZero m] (hm2 : 2 ≤ m) (w : Fin m) :
    dOrder (parSq m) (fun u : Fin m => ({u} : Finset (Fin m)))
      (fun u => Finset.singleton_nonempty u) w = min ((w : ℕ) + 1) (m - 1) := by
  set d := min ((w : ℕ) + 1) (m - 1) with hd
  have hw := w.isLt
  -- the set of worlds still together with `w` at order `d` is `{w}`
  have hcs : CommonSafe (fun u : Fin m => ({u} : Finset (Fin m))) (near (parSq m) w d) := by
    refine ⟨w, fun u hu => ?_⟩
    simp only [near, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    by_cases huw : u = w
    · rw [huw]; exact Finset.mem_singleton_self _
    · exfalso
      rcases hu with hu | hlt
      · exact huw hu
      · have hs := par_sep m w u (Ne.symm huw)
        have hu := u.isLt
        have hne : (u : ℕ) ≠ w := fun e => huw (Fin.ext e)
        rw [hs] at hlt
        omega
  -- below `d`, some other world is still together with `w`
  have hmin : ∀ s, s < d →
      ¬ CommonSafe (fun u : Fin m => ({u} : Finset (Fin m))) (near (parSq m) w s) := by
    intro s hs hcs'
    obtain ⟨a, ha⟩ := hcs'
    have haw : a = w := Finset.mem_singleton.mp (ha w (mem_near_self _ w s))
    by_cases hlast : (w : ℕ) + 1 ≤ m - 1
    · set l : Fin m := ⟨m - 1, by omega⟩ with hl
      have hlw : l ≠ w := by intro e; rw [Fin.ext_iff] at e; simp [hl] at e; omega
      have hsep := par_sep m w l (Ne.symm hlw)
      have hlmem : l ∈ near (parSq m) w s := by
        simp only [near, Finset.mem_filter, Finset.mem_univ, true_and]
        right
        rw [hsep]; simp [hl]; omega
      have := Finset.mem_singleton.mp (ha l hlmem)
      exact hlw (this.symm.trans haw)
    · set l : Fin m := ⟨m - 2, by omega⟩ with hl
      have hlw : l ≠ w := by intro e; rw [Fin.ext_iff] at e; simp [hl] at e; omega
      have hsep := par_sep m w l (Ne.symm hlw)
      have hlmem : l ∈ near (parSq m) w s := by
        simp only [near, Finset.mem_filter, Finset.mem_univ, true_and]
        right
        rw [hsep]; simp [hl]; omega
      have := Finset.mem_singleton.mp (ha l hlmem)
      exact hlw (this.symm.trans haw)
  apply le_antisymm
  · by_contra hlt
    push_neg at hlt
    exact dOrder_min _ _ _ w d hlt hcs
  · by_contra hlt
    push_neg at hlt
    exact hmin _ hlt (dOrder_spec _ _ _ w)

/-- **The per-world identification law on the parity channel**:
`D_h(w) ≍ h^{2 min(w+1, m-1)}`, with the explicit constants `cW/m` and `CW`. -/
theorem parity_id_world_law [NeZero m] (σ h h₀ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (hh : 0 < h)
    (hh1 : h ≤ 1) (hhh : h ≤ h₀) (w : Fin m) :
    (∃ a ∈ ({w} : Finset (Fin m)), ∀ l : Fin m, a ∉ ({l} : Finset (Fin m)) →
      cW m σ / m * h ^ (2 * min ((w : ℕ) + 1) (m - 1))
        ≤ ∑ q, (1 / (m : ℝ)) * parKap σ h hσ hh.le (by omega) q w l)
    ∧ ∀ a ∈ ({w} : Finset (Fin m)), ∀ α : Fin m → ℝ, (∀ q, 0 ≤ α q) → ∑ q, α q = 1 →
        ∃ l : Fin m, a ∉ ({l} : Finset (Fin m)) ∧ ∑ q, α q * parKap σ h hσ hh.le (by omega) q w l
          ≤ CW m σ h₀ * h ^ (2 * min ((w : ℕ) + 1) (m - 1)) := by
  have hlaw := parity_world_law σ h h₀ hσ hm2 hh hh1 hhh
    (fun u : Fin m => ({u} : Finset (Fin m))) (fun u => Finset.singleton_nonempty u) w
  rw [parity_id_order hm2 w] at hlaw
  refine ⟨hlaw.1, hlaw.2 ?_⟩
  omega

/-! ## 6. The hypotheses are satisfiable -/

/-- **A concrete instance**: `m = 3`, `σ = 1`, `h = 1/2`, `h₀ = 1`, world `w = 0`. -/
theorem parity_world_instance :
    (∃ a ∈ ({0} : Finset (Fin 3)), ∀ l : Fin 3, a ∉ ({l} : Finset (Fin 3)) →
      cW 3 1 / 3 * (1 / 2 : ℝ) ^ (2 * min ((0 : Fin 3) + 1 : ℕ) (3 - 1))
        ≤ ∑ q, (1 / (3 : ℝ)) * parKap 1 (1 / 2) one_pos (by norm_num) (by norm_num) q 0 l)
    ∧ 0 < cW 3 1 := by
  refine ⟨?_, cW_pos 1 (by norm_num)⟩
  have := (parity_id_world_law (m := 3) 1 (1 / 2) 1 one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 0).1
  simpa using this

#print axioms sqrt_sub_sq_le
#print axioms hel_le_chi
#print axioms par_gap_visible
#print axioms par_chi_visible
#print axioms par_chi_visible_unif
#print axioms parKap_upper
#print axioms parKap_blind
#print axioms parKap_lower
#print axioms parity_world_law
#print axioms parity_id_order
#print axioms parity_id_world_law
#print axioms parity_world_instance

end CIGAMF.P13.PaperBParityWorld
