import «LeanPaperBObstructionLawV1»
import «LeanPaperBParityExperimentV1»

/-!
# Paper B: the obstruction law, instantiated on the parity channel

`LeanPaperBObstructionLawV1` states the lower law for every channel whose per-query
information between two worlds is bounded.  This module does two things.

* `obstruction_lower_chi`, `graded_lower_chi`: the same law with the per-query chi-square as
  the information bound, through `transcript_kl_le`.  On a graded channel,
  `chi <= C h^{2 sep}`, some world pays `E[#queries] * C h^{2 sStar}` at least
  `((1 - delta)/(|W| - 1)) log(1/delta) - log 2`, where `sStar` is the least safe order.
* On the parity channel `chanAt sigma h` it discharges every hypothesis.
  - The channel is graded with `sep w v = min (w+1) (v+1)` and constant `aS m sigma`
    (`parity_graded`). Query `q` separates two worlds only when `q` is one of their masks,
    and it carries at most `parC q * h^{2q}`.
  - The overlapping correspondence has least safe order `1` (`parity_coSafe_order`).
  - Identification has least safe order `m - 1` (`parity_id_order`).

  So the two lower rates, `log(1/delta)/h^2` for the safe decision and
  `log(1/delta)/h^{2(m-1)}` for identification, are corollaries of the one law
  (`parity_safe_from_law`, `parity_id_from_law`) rather than two separate constructions.
  This also shows the law's hypotheses are satisfiable on a real channel.
-/

namespace CIGAMF.P13.PaperBObstructionParity

open Finset MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBObstructionLaw CIGAMF.P13.PaperBProtocol
open CIGAMF.P13.PaperBObstruction CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityChiSq
open CIGAMF.P13.PaperBParityChannel CIGAMF.P13.PaperBParityExperiment

/-! ## 1. The law with chi-square information -/

section General

variable {W Q A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
  [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] [Fintype Q]

theorem obstruction_lower_chi (C : Channel W Q) (π : Policy Q) (n : ℕ) (out : Hist Q n → A)
    (safe : W → Finset A) (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ safe w})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : ∀ w, 1 - δ ≤ (hist C π w n).real {ω | out ω ∈ safe w})
    (H : Finset W) (hH : Unsafe safe H) (hcard : 2 ≤ H.card) (w0 : W) (hw0 : w0 ∈ H)
    (t : ℝ≥0∞) (hchi : ∀ v ∈ H, v ≠ w0 → ∀ q, q ≠ C.dummy → chi C w0 v q ≤ t) :
    ENNReal.ofReal ((1 - δ) / ((H.card : ℝ) - 1) * Real.log (1 / δ) - Real.log 2)
      ≤ t * costN C π w0 n := by
  haveI := hist_prob C π w0 n
  obtain ⟨v, hv, hne, hp⟩ := obstruction_pigeonhole (hist C π w0 n) out safe H hH hcard w0 hw0
    (1 - δ) (hcorr w0)
  haveI := hist_prob C π v n
  have hEmeas : MeasurableSet {ω | out ω ∉ safe v} := (hmeas v).compl
  have hQE : (hist C π v n).real {ω | out ω ∉ safe v} ≤ δ := by
    have hc : {ω | out ω ∉ safe v} = {ω | out ω ∈ safe v}ᶜ := rfl
    rw [hc, measureReal_compl (hmeas v), probReal_univ]
    linarith [hcorr v]
  have hev := event_klDiv_ge (hist C π w0 n) (hist C π v n) _ hEmeas δ hδ hQE
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  calc ENNReal.ofReal ((1 - δ) / ((H.card : ℝ) - 1) * Real.log (1 / δ) - Real.log 2)
      ≤ ENNReal.ofReal ((hist C π w0 n).real {ω | out ω ∉ safe v} * Real.log (1 / δ)
          - Real.log 2) := by
        apply ENNReal.ofReal_le_ofReal
        have := mul_le_mul_of_nonneg_right hp hlog
        linarith
    _ ≤ klDiv (hist C π w0 n) (hist C π v n) := hev
    _ ≤ t * costN C π w0 n := transcript_kl_le C π w0 v t (hchi v hv hne) n

/-- **The graded lower law.**  If `chi <= C h^{2 sep}` on every non-dummy query and `sStar` is
the least safe order, some world pays `C h^{2 sStar} * E[#queries] >= ((1 - delta)/(|W| - 1))
log(1/delta) - log 2`. -/
theorem graded_lower_chi [Nonempty A] (C : Channel W Q) (π : Policy Q) (n : ℕ)
    (out : Hist Q n → A) (safe : W → Finset A) (hsafe : ∀ w, (safe w).Nonempty)
    (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ safe w})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : ∀ w, 1 - δ ≤ (hist C π w n).real {ω | out ω ∈ safe w})
    (sep : W → W → ℕ) (Cc h : ℝ≥0) (hC : 0 < Cc) (h0 : 0 < h) (h1 : h < 1)
    (hchi : ∀ w v, w ≠ v → ∀ q, q ≠ C.dummy → chi C w v q ≤ ((graded sep Cc h w v : ℝ≥0) : ℝ≥0∞))
    (hex : ∃ H : Finset W, Unsafe safe H) (sStar : ℕ) (hS : SafeAt sep safe sStar)
    (hmin : ∀ s, SafeAt sep safe s → sStar ≤ s) :
    ∃ w0 : W, ENNReal.ofReal ((1 - δ) / ((Fintype.card W : ℝ) - 1) * Real.log (1 / δ)
        - Real.log 2) ≤ ((Cc * h ^ (2 * sStar) : ℝ≥0) : ℝ≥0∞) * costN C π w0 n := by
  have htwo := two_le_card_of_unsafe safe hsafe
  obtain ⟨-, H, hH, htight⟩ := graded_tStar sep safe hsafe hex Cc h hC h0 h1 sStar hS hmin
  have hcard := htwo H hH
  obtain ⟨w0, hw0⟩ : H.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨w0, le_trans ?_ (obstruction_lower_chi C π n out safe hmeas δ hδ hδ1 hcorr H hH hcard
    w0 hw0 _ (fun v hv hne q hq => (hchi w0 v (Ne.symm hne) q hq).trans
      (by exact_mod_cast htight w0 hw0 v hv (Ne.symm hne))))⟩
  apply ENNReal.ofReal_le_ofReal
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hHW : (H.card : ℝ) ≤ Fintype.card W := by exact_mod_cast Finset.card_le_univ H
  have hk : (0 : ℝ) < (H.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ H.card := by exact_mod_cast hcard
    linarith
  have hfrac : (1 - δ) / ((Fintype.card W : ℝ) - 1) ≤ (1 - δ) / ((H.card : ℝ) - 1) :=
    div_le_div_of_nonneg_left (by linarith) hk (by linarith)
  have := mul_le_mul_of_nonneg_right hfrac hlog
  linarith

end General

/-! ## 2. The parity channel is graded -/

variable {m : ℕ}

/-- The separation order of the parity channel: the smaller of the two masks. -/
def sepP (w v : Fin m) : ℕ := min ((w : ℕ) + 1) ((v : ℕ) + 1)

theorem sepP_symm (w v : Fin m) : sepP w v = sepP v w := by
  unfold sepP; exact min_comm _ _

theorem one_le_sepP (w v : Fin m) : 1 ≤ sepP w v := by
  unfold sepP; omega

/-- The parity constant as a non-negative real. -/
noncomputable def aSN (m : ℕ) (σ : ℝ) (hσ : 0 < σ) : ℝ≥0 := ⟨aS m σ, (aS_pos σ hσ).le⟩

/-- **The parity channel is graded**: query `q` separates `w` and `v` only when `q` is one of
their masks, hence `q >= sep w v`, and it carries at most `parC q * h^{2q} <= aS h^{2 sep}`. -/
theorem parity_graded (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (h : ℝ≥0) (hh : 0 < h) (hh1 : h ≤ 1)
    (w v : Fin m) (hwv : w ≠ v) (q : Fin m) (hq : q ≠ (⟨0, hm⟩ : Fin m)) :
    chi (chanAt σ hσ hm (h : ℝ)) w v q
      ≤ ((graded sepP (aSN m σ hσ) h w v : ℝ≥0) : ℝ≥0∞) := by
  have hmax : max (h : ℝ) 0 = h := max_eq_left h.2
  have hc := parChan_chi_le m σ (max (h : ℝ) 0) 1 hσ (le_max_right _ 0)
    (by rw [hmax]; exact_mod_cast hh1) hm w v q
  refine hc.trans ?_
  split_ifs with hmask
  · exact bot_le
  · have hne : (w : ℕ) + 1 ≠ (v : ℕ) + 1 := by
      intro he; apply hwv; ext; omega
    have hname := (masks_differ_iff q ((w : ℕ) + 1) ((v : ℕ) + 1) hne).mp hmask
    have hqs : sepP w v ≤ (q : ℕ) := by unfold sepP; omega
    have hpow : (h : ℝ) ^ (2 * (q : ℕ)) ≤ (h : ℝ) ^ (2 * sepP w v) :=
      pow_le_pow_of_le_one h.2 (by exact_mod_cast hh1) (by omega)
    have hpc : parC q σ 1 ≤ aS m σ := by
      unfold aS
      have := Finset.single_le_sum (fun i (_ : i ∈ Finset.range m) => parC_nonneg i σ 1 hσ)
        (Finset.mem_range.mpr q.isLt)
      linarith
    rw [hmax, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    unfold graded aSN
    push_cast
    calc parC q σ 1 * (h : ℝ) ^ (2 * (q : ℕ)) ≤ aS m σ * (h : ℝ) ^ (2 * (q : ℕ)) :=
          mul_le_mul_of_nonneg_right hpc (by positivity)
      _ ≤ aS m σ * (h : ℝ) ^ (2 * sepP w v) :=
          mul_le_mul_of_nonneg_left hpow (aS_pos σ hσ).le

/-! ## 3. The two safe orders -/

/-- **The overlapping correspondence has safe order `1`**, and no smaller. -/
theorem parity_coSafe_order (hm2 : 2 ≤ m) :
    SafeAt (sepP (m := m)) (coSafe : Fin m → Finset (Fin m)) 1
      ∧ ∀ s, SafeAt (sepP (m := m)) (coSafe : Fin m → Finset (Fin m)) s → 1 ≤ s := by
  refine ⟨(coSafe_order _ 1).mpr ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], ?_⟩,
    fun s hs => ?_⟩
  · unfold sepP; simp
  · obtain ⟨w, w', -, hle⟩ := (coSafe_order _ s).mp hs
    exact (one_le_sepP w w').trans hle

/-- **Identification has safe order `m - 1`**, and no smaller. -/
theorem parity_id_order (hm2 : 2 ≤ m) :
    SafeAt (sepP (m := m)) (fun w : Fin m => ({w} : Finset (Fin m))) (m - 1)
      ∧ ∀ s, SafeAt (sepP (m := m)) (fun w : Fin m => ({w} : Finset (Fin m))) s → m - 1 ≤ s := by
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  refine ⟨(id_order _ sepP_symm _).mpr fun w w' hne => ?_, fun s hs => ?_⟩
  · have hw := w.isLt
    have hw' := w'.isLt
    have hne' : (w : ℕ) ≠ w' := fun h => hne (Fin.ext h)
    unfold sepP
    omega
  · have h := (id_order _ sepP_symm s).mp hs ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩
      (by simp [Fin.ext_iff]; omega)
    unfold sepP at h
    simp only at h
    omega

/-! ## 4. The two parity lower rates, from the one law -/

/-- **The safe decision's lower rate, from the law.** -/
theorem parity_safe_from_law (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (h : ℝ≥0) (hh : 0 < h)
    (hh1 : h < 1) (π : Policy (Fin m)) (n : ℕ) (out : Hist (Fin m) n → Fin m)
    (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ (coSafe w : Finset (Fin m))})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : ∀ w, 1 - δ ≤ (hist (chanAt σ hσ (by omega) (h : ℝ)) π w n).real
      {ω | out ω ∈ (coSafe w : Finset (Fin m))}) :
    ∃ w0 : Fin m, ENNReal.ofReal ((1 - δ) / ((m : ℝ) - 1) * Real.log (1 / δ) - Real.log 2)
      ≤ ((aSN m σ hσ * h ^ (2 * 1) : ℝ≥0) : ℝ≥0∞)
          * costN (chanAt σ hσ (by omega) (h : ℝ)) π w0 n := by
  have hm : 0 < m := by omega
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hsafe : ∀ w : Fin m, (coSafe w : Finset (Fin m)).Nonempty := by
    intro w
    by_cases h0 : (w : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, by simp [coSafe, Fin.ext_iff, h0]⟩
    · exact ⟨⟨0, hm⟩, by simp [coSafe, Fin.ext_iff]; omega⟩
  obtain ⟨hS, hmin⟩ := parity_coSafe_order (m := m) hm2
  have := graded_lower_chi (chanAt σ hσ hm (h : ℝ)) π n out coSafe hsafe hmeas δ hδ hδ1 hcorr
    sepP (aSN m σ hσ) h (aS_pos σ hσ) hh hh1
    (fun w v hwv q hq => parity_graded σ hσ hm h hh hh1.le w v hwv q hq)
    ⟨Finset.univ, coSafe_univ_unsafe⟩ 1 hS hmin
  simpa [Fintype.card_fin] using this

/-- **Identification's lower rate, from the law.** -/
theorem parity_id_from_law (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (h : ℝ≥0) (hh : 0 < h)
    (hh1 : h < 1) (π : Policy (Fin m)) (n : ℕ) (out : Hist (Fin m) n → Fin m)
    (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ ({w} : Finset (Fin m))})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : ∀ w, 1 - δ ≤ (hist (chanAt σ hσ (by omega) (h : ℝ)) π w n).real
      {ω | out ω ∈ ({w} : Finset (Fin m))}) :
    ∃ w0 : Fin m, ENNReal.ofReal ((1 - δ) / ((m : ℝ) - 1) * Real.log (1 / δ) - Real.log 2)
      ≤ ((aSN m σ hσ * h ^ (2 * (m - 1)) : ℝ≥0) : ℝ≥0∞)
          * costN (chanAt σ hσ (by omega) (h : ℝ)) π w0 n := by
  have hm : 0 < m := by omega
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hex : ∃ H : Finset (Fin m), Unsafe (fun w : Fin m => ({w} : Finset (Fin m))) H := by
    refine ⟨{⟨0, hm⟩, ⟨1, by omega⟩}, fun a => ?_⟩
    by_cases ha : a = ⟨0, hm⟩
    · refine ⟨⟨1, by omega⟩, by simp, ?_⟩
      rw [Finset.mem_singleton, ha]
      simp [Fin.ext_iff]
    · exact ⟨⟨0, hm⟩, by simp, by rw [Finset.mem_singleton]; exact ha⟩
  obtain ⟨hS, hmin⟩ := parity_id_order (m := m) hm2
  have := graded_lower_chi (chanAt σ hσ hm (h : ℝ)) π n out (fun w => ({w} : Finset (Fin m)))
    (fun w => Finset.singleton_nonempty w) hmeas δ hδ hδ1 hcorr
    sepP (aSN m σ hσ) h (aS_pos σ hσ) hh hh1
    (fun w v hwv q hq => parity_graded σ hσ hm h hh hh1.le w v hwv q hq)
    hex (m - 1) hS hmin
  simpa [Fintype.card_fin] using this


/-! ## 5. The tournament's hypotheses are satisfiable

A perfect-observation instance: `Omega = W`, world `w` puts all mass on `w`, and a fixed linear
order decides which side of each pair owns the tie-break event.  Every test is exact, so every
error bound of `tournament_law` holds with error `0`.  This shows only that the hypotheses are
consistent; the parity channel's upper rates come from its own decoders (`idCode`, `safeCode`).
-/

section Satisfiable

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W] [MeasurableSpace W]
  [MeasurableSingletonClass W]

/-- `u` beats `v` unless the observation names the loser of the pair. -/
def perfectBeat (u v : W) : Set W := if u < v then {ω | ω ≠ v} else {ω | ω = u}

theorem perfectBeat_anti (u v : W) (huv : u ≠ v) : perfectBeat v u = (perfectBeat u v)ᶜ := by
  unfold perfectBeat
  rcases lt_or_gt_of_ne huv with h | h
  · rw [if_neg (not_lt.mpr h.le), if_pos h]
    ext ω; simp
  · rw [if_pos h, if_neg (not_lt.mpr h.le)]
    ext ω; simp

theorem perfectBeat_err (w v : W) (hwv : w ≠ v) :
    (Measure.dirac w) (perfectBeat v w) = 0 := by
  unfold perfectBeat
  split_ifs with h
  · have hS : MeasurableSet {ω : W | ω ≠ w} := (measurableSet_singleton w).compl
    rw [Measure.dirac_apply' _ hS]
    simp [Set.indicator]
  · have hS : MeasurableSet {ω : W | ω = v} := measurableSet_singleton v
    rw [Measure.dirac_apply' _ hS]
    simp [Set.indicator, hwv]

/-- **The tournament's hypotheses hold on the perfect-observation instance**, for every
threshold and every exponent. -/
theorem tournament_satisfiable (κ : W → W → ℝ≥0) (t : ℝ≥0) (c n : ℝ) :
    (∀ u v, (u, v) ∈ pairSet κ t → perfectBeat v u = (perfectBeat u v)ᶜ)
      ∧ ∀ w v, (w, v) ∈ pairSet κ t →
          (Measure.dirac w) (perfectBeat v w) ≤ ENNReal.ofReal (Real.exp (-(c * n * κ w v))) := by
  refine ⟨fun u v h => perfectBeat_anti u v ?_, fun w v h => ?_⟩
  · exact (Finset.mem_filter.mp h).2.1
  · rw [perfectBeat_err w v (Finset.mem_filter.mp h).2.1]
    exact bot_le

end Satisfiable

#print axioms obstruction_lower_chi
#print axioms graded_lower_chi
#print axioms parity_graded
#print axioms parity_coSafe_order
#print axioms parity_id_order
#print axioms parity_safe_from_law
#print axioms parity_id_from_law
#print axioms tournament_satisfiable

end CIGAMF.P13.PaperBObstructionParity
