import «LeanPaperBSafeOrderV1»
import «LeanPaperALowerKLV1»

/-!
# Paper B: the general law from obstruction and order to rate

The parity channel's two rates, `log(1/delta)/h^2` for the safe decision and
`log(1/delta)/h^{2(m-1)}` for identification, are instances of one law.  Fix a finite world
set `W` and a safe-answer correspondence `safe : W -> Finset A`.  Fix a per-query information
bound `kappa w w'` (the largest per-query divergence between two worlds).

* An **obstruction** is a set `H` of worlds with no common safe answer (`Unsafe safe H`).
* `Resolves kappa safe t`: every obstruction contains a distinct pair with `kappa >= t`.
* The **obstruction information** `tStar` is the value of `min over obstructions of max over
  their pairs of kappa`. `obstruction_value` proves it exists when every obstruction has at
  least two worlds. It is the largest threshold at which every obstruction is resolved
  (`resolves_iff_le`), and some obstruction has every pair at most `tStar`.

The law has two sides.

* **Lower, for every channel and every policy** (`obstruction_lower`,
  `obstruction_lower_star`).  If each non-dummy query carries at most `kappa w w'` between
  two worlds, then every finite-horizon policy that answers safely with probability
  `1 - delta` in every world spends, in some world of a tight obstruction,
  `E[#queries] * tStar >= ((1 - delta)/(|W| - 1)) log(1/delta) - log 2`.  The pair that
  carries the demand is chosen from the policy's own output distribution by pigeonhole over
  the obstruction.  Unlike `safe_pair_exists`, this is for EVERY safe correspondence, not the
  overlapping one.
* **Upper, by a tournament** (`decode_safe`, `decode_error`, `tournament_law`).  Test every
  pair whose information is at least `t`, keep the worlds that win all their tests, and
  output a common safe answer of the survivors.  If `Resolves kappa safe t`, the survivors
  always admit one, and the truth survives unless one of its own tests fails.  With tests of
  exponent `c kappa` and `n >= log(|W|/delta)/(c t)` samples per pair, the output is safe
  with probability `>= 1 - delta` at every world, at a total of at most `|W|^2 n` queries.

So the minimax cost is `Theta(log(1/delta) / tStar)` whenever the tests' exponent is
comparable to the divergence bound.

* **The order law** (`graded_resolves_iff`, `graded_tStar`).  On a graded channel,
  `kappa w w' = C h^{2 sep w w'}` with `0 < h < 1`, `Resolves` at `C h^{2s}` is EXACTLY
  `SafeAt sep safe s`, and `tStar = C h^{2 sStar}`, where `sStar` is the least safe order.
  `coSafe_order` and `id_order` give the two classical cases: for the overlapping
  correspondence `sStar` is the minimum separation order over all pairs, and for
  identification (`safe w = {w}`) it is the maximum.  On the parity channel these orders are
  `1` and `m - 1`, which recovers both rates of `parity_rates`.

The upper side's input is a stated property of a concrete decoder run: per-pair test errors
of exponent `c kappa`. It is a hypothesis of `tournament_law`, not a theorem about every
channel.  The combinatorics and the union bound are unconditional.
-/

namespace CIGAMF.P13.PaperBObstructionLaw

open Finset MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBSafe

/-! ## 1. Obstructions and the obstruction information -/

section Combinatorics

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

/-- Every obstruction contains a distinct pair carrying information at least `t`. -/
def Resolves (κ : W → W → ℝ≥0) (safe : W → Finset A) (t : ℝ≥0) : Prop :=
  ∀ H : Finset W, Unsafe safe H → ∃ w ∈ H, ∃ w' ∈ H, w ≠ w' ∧ t ≤ κ w w'

/-- The largest information among the distinct pairs of a set. -/
noncomputable def maxPair (κ : W → W → ℝ≥0) (H : Finset W) : ℝ≥0 :=
  H.offDiag.sup (fun p => κ p.1 p.2)

theorem le_maxPair (κ : W → W → ℝ≥0) (H : Finset W) {w w' : W} (hw : w ∈ H) (hw' : w' ∈ H)
    (hne : w ≠ w') : κ w w' ≤ maxPair κ H := by
  unfold maxPair
  exact Finset.le_sup (f := fun p : W × W => κ p.1 p.2) (s := H.offDiag) (b := (w, w'))
    (Finset.mem_offDiag.mpr ⟨hw, hw', hne⟩)

theorem resolves_mono (κ : W → W → ℝ≥0) (safe : W → Finset A) {t t' : ℝ≥0} (htt : t' ≤ t)
    (h : Resolves κ safe t) : Resolves κ safe t' := by
  intro H hH
  obtain ⟨w, hw, w', hw', hne, hle⟩ := h H hH
  exact ⟨w, hw, w', hw', hne, htt.trans hle⟩

/-- An obstruction has at least two worlds as soon as every world has a safe answer and the
answer set is non-empty. -/
theorem two_le_card_of_unsafe [Nonempty A] (safe : W → Finset A) (hsafe : ∀ w, (safe w).Nonempty)
    (H : Finset W) (hH : Unsafe safe H) : 2 ≤ H.card := by
  by_contra hcon
  push_neg at hcon
  rcases (by omega : H.card = 0 ∨ H.card = 1) with h0 | h1
  · have : H = ∅ := Finset.card_eq_zero.mp h0
    obtain ⟨a⟩ := ‹Nonempty A›
    obtain ⟨w, hw, -⟩ := hH a
    simp [this] at hw
  · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨a, ha⟩ := hsafe w
    obtain ⟨w', hw', hna⟩ := hH a
    rw [Finset.mem_singleton] at hw'
    subst hw'
    exact hna ha

/-- **The obstruction information exists.**  If some obstruction exists and every obstruction
has at least two worlds, there is `tStar` such that every obstruction is resolved at
`tStar` and some obstruction has every distinct pair at most `tStar`. -/
theorem obstruction_value (κ : W → W → ℝ≥0) (safe : W → Finset A)
    (hex : ∃ H : Finset W, Unsafe safe H)
    (htwo : ∀ H : Finset W, Unsafe safe H → 2 ≤ H.card) :
    ∃ tStar : ℝ≥0, Resolves κ safe tStar
      ∧ ∃ H : Finset W, Unsafe safe H
          ∧ ∀ w ∈ H, ∀ w' ∈ H, w ≠ w' → κ w w' ≤ tStar := by
  classical
  set U := (Finset.univ : Finset (Finset W)).filter (fun H => Unsafe safe H) with hU
  have hUne : U.Nonempty := by
    obtain ⟨H, hH⟩ := hex
    exact ⟨H, by simp [hU, hH]⟩
  obtain ⟨Hs, hHsU, hmin⟩ := Finset.exists_min_image U (maxPair κ) hUne
  have hHs : Unsafe safe Hs := (Finset.mem_filter.mp hHsU).2
  refine ⟨maxPair κ Hs, ?_, Hs, hHs, fun w hw w' hw' hne => le_maxPair κ Hs hw hw' hne⟩
  intro H hH
  have hHU : H ∈ U := by simp [hU, hH]
  have hle := hmin H hHU
  have hcard := htwo H hH
  have hoff : H.offDiag.Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := (Finset.one_lt_card (s := H)).mp (by omega)
    exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩⟩
  obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_sup H.offDiag hoff (fun p => κ p.1 p.2)
  obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
  refine ⟨p.1, h1, p.2, h2, h3, ?_⟩
  have : maxPair κ H = κ p.1 p.2 := hpeq
  rw [← this]
  exact hle

/-- **`tStar` is the largest resolved threshold.**  If `H` is an obstruction with every pair
at most `tStar` and `tStar` resolves, then a threshold resolves iff it is at most `tStar`. -/
theorem resolves_iff_le (κ : W → W → ℝ≥0) (safe : W → Finset A) (tStar : ℝ≥0)
    (hres : Resolves κ safe tStar) (H : Finset W) (hH : Unsafe safe H)
    (htight : ∀ w ∈ H, ∀ w' ∈ H, w ≠ w' → κ w w' ≤ tStar) (t : ℝ≥0) :
    Resolves κ safe t ↔ t ≤ tStar := by
  constructor
  · intro h
    obtain ⟨w, hw, w', hw', hne, hle⟩ := h H hH
    exact hle.trans (htight w hw w' hw' hne)
  · intro htt
    exact resolves_mono κ safe htt hres

end Combinatorics

/-! ## 2. The lower law, for every channel and every policy -/

section Lower

open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperBObstruction
open CIGAMF.P13.PaperBConcentration

variable {W Q A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
  [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] [Fintype Q]

/-- The dummy query carries no information. -/
theorem klq_dummy' (C : Channel W Q) (θ l : W) : klq C θ l C.dummy = 0 := by
  unfold klq
  have : obsLawC C θ C.dummy = obsLawC C l C.dummy := by
    unfold obsLawC
    congr 1
    funext y
    rw [C.dummy_same θ l]
  rw [this, klDiv_self]

/-- The cost of a history is the count of its non-dummy queries. -/
theorem tauN_eq_sum_cnt (dummy : Q) (n : ℕ) (ω : Hist Q n) :
    (tauN dummy n ω : ℝ≥0∞) = ∑ q, cntQ q n ω * (if q = dummy then 0 else 1) := by
  unfold tauN cntQ
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (ω i).1]
  · by_cases h : (ω i).1 = dummy <;> simp [h]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The accumulated divergence is at most cost times the per-query bound.** -/
theorem info_le_cost (C : Channel W Q) (π : Policy Q) (θ l : W) (n : ℕ) (t : ℝ≥0∞)
    (ht : ∀ q, q ≠ C.dummy → klq C θ l q ≤ t) :
    ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q ≤ costN C π θ n * t := by
  have h1 : ∀ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q
      ≤ (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * (if q = C.dummy then 0 else 1) * t := by
    intro q
    by_cases hq : q = C.dummy
    · subst hq
      simp [klq_dummy']
    · simp only [hq, if_false, mul_one]
      exact mul_le_mul_of_nonneg_left (ht q hq) (zero_le)
  calc ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q
      ≤ ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * (if q = C.dummy then 0 else 1) * t :=
        Finset.sum_le_sum fun q _ => h1 q
    _ = (∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * (if q = C.dummy then 0 else 1)) * t := by
        rw [Finset.sum_mul]
    _ = costN C π θ n * t := by
        congr 1
        unfold costN
        simp_rw [tauN_eq_sum_cnt]
        rw [lintegral_finsetSum _ (fun q _ => (measurable_cntQ q n).mul_const _)]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [lintegral_mul_const _ (measurable_cntQ q n)]

/-- **Pigeonhole over an obstruction.**  If the output is safe for `w0` with probability at
least `p`, then some other world `v` of the obstruction finds the output unsafe with
probability at least `p / (|H| - 1)`. -/
theorem obstruction_pigeonhole {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (out : Ω → A) (safe : W → Finset A) (H : Finset W)
    (hH : Unsafe safe H) (hcard : 2 ≤ H.card) (w0 : W) (hw0 : w0 ∈ H) (p : ℝ)
    (hp : p ≤ μ.real {ω | out ω ∈ safe w0}) :
    ∃ v ∈ H, v ≠ w0 ∧ p / ((H.card : ℝ) - 1) ≤ μ.real {ω | out ω ∉ safe v} := by
  classical
  set E := H.erase w0 with hE
  have hEcard : (E.card : ℝ) = (H.card : ℝ) - 1 := by
    rw [hE, Finset.card_erase_of_mem hw0, Nat.cast_sub (by omega)]
    simp
  have hEne : E.Nonempty := by
    rw [← Finset.card_pos, hE, Finset.card_erase_of_mem hw0]
    omega
  have hsub : {ω | out ω ∈ safe w0} ⊆ ⋃ v ∈ E, {ω | out ω ∉ safe v} := by
    intro ω hω
    obtain ⟨v, hv, hna⟩ := hH (out ω)
    have hne : v ≠ w0 := by
      rintro rfl
      exact hna hω
    exact Set.mem_biUnion (Finset.mem_erase.mpr ⟨hne, hv⟩) hna
  have hsum : p ≤ ∑ v ∈ E, μ.real {ω | out ω ∉ safe v} :=
    hp.trans ((measureReal_mono hsub (measure_ne_top μ _)).trans (measureReal_biUnion_finset_le E _))
  have hk : (0 : ℝ) < (H.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ H.card := by exact_mod_cast hcard
    linarith
  have hconst : ∑ _v ∈ E, p / ((H.card : ℝ) - 1) = p := by
    rw [Finset.sum_const, nsmul_eq_mul, hEcard]
    field_simp
  have hsum' : ∑ _v ∈ E, p / ((H.card : ℝ) - 1) ≤ ∑ v ∈ E, μ.real {ω | out ω ∉ safe v} := by
    rw [hconst]; exact hsum
  obtain ⟨v, hv, hle⟩ := Finset.exists_le_of_sum_le hEne hsum'
  exact ⟨v, (Finset.mem_erase.mp hv).2, (Finset.mem_erase.mp hv).1, hle⟩

/-- **The lower law.**  Every finite-horizon policy whose output is safe with probability
`1 - delta` in every world spends, at any world `w0` of an obstruction `H` whose pairs from
`w0` carry at most `t` per query, `E[#queries] * t >= ((1 - delta)/(|H| - 1)) log(1/delta)
- log 2`. -/
theorem obstruction_lower (C : Channel W Q) (π : Policy Q) (n : ℕ) (out : Hist Q n → A)
    (safe : W → Finset A) (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ safe w})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : ∀ w, 1 - δ ≤ (hist C π w n).real {ω | out ω ∈ safe w})
    (H : Finset W) (hH : Unsafe safe H) (hcard : 2 ≤ H.card) (w0 : W) (hw0 : w0 ∈ H)
    (t : ℝ≥0)
    (hκ : ∀ v ∈ H, v ≠ w0 → ∀ q, q ≠ C.dummy → klq C w0 v q ≤ (t : ℝ≥0∞)) :
    ENNReal.ofReal ((1 - δ) / ((H.card : ℝ) - 1) * Real.log (1 / δ) - Real.log 2)
      ≤ costN C π w0 n * (t : ℝ≥0∞) := by
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
    _ ≤ ∫⁻ ω, qsum (klq C w0 v) n ω ∂hist C π w0 n := transcript_kl_le_qsum C π w0 v n
    _ = ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π w0 n) * klq C w0 v q := lintegral_qsum_eq _ _
    _ ≤ costN C π w0 n * (t : ℝ≥0∞) := info_le_cost C π w0 v n _ (hκ v hv hne)

/-- **The lower law at the obstruction information.**  With a per-query bound `kappa`, some
world of a tight obstruction pays `E[#queries] * tStar >= ((1 - delta)/(|W| - 1))
log(1/delta) - log 2`. -/
theorem obstruction_lower_star [Nonempty A] (C : Channel W Q) (π : Policy Q) (n : ℕ)
    (out : Hist Q n → A) (safe : W → Finset A) (hsafe : ∀ w, (safe w).Nonempty)
    (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ safe w})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : ∀ w, 1 - δ ≤ (hist C π w n).real {ω | out ω ∈ safe w})
    (κ : W → W → ℝ≥0) (hκ : ∀ w v, ∀ q, q ≠ C.dummy → klq C w v q ≤ (κ w v : ℝ≥0∞))
    (hex : ∃ H : Finset W, Unsafe safe H) :
    ∃ tStar : ℝ≥0, Resolves κ safe tStar
      ∧ ∃ w0 : W, ENNReal.ofReal ((1 - δ) / ((Fintype.card W : ℝ) - 1) * Real.log (1 / δ)
          - Real.log 2) ≤ costN C π w0 n * (tStar : ℝ≥0∞) := by
  have htwo := two_le_card_of_unsafe safe hsafe
  obtain ⟨tStar, hres, H, hH, htight⟩ := obstruction_value κ safe hex htwo
  refine ⟨tStar, hres, ?_⟩
  have hcard := htwo H hH
  obtain ⟨w0, hw0⟩ : H.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨w0, le_trans ?_ (obstruction_lower C π n out safe hmeas δ hδ hδ1 hcorr H hH hcard w0
    hw0 tStar (fun v hv hne q hq => (hκ w0 v q hq).trans
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

end Lower

/-! ## 3. The upper law: a tournament over the resolved pairs -/

section Upper

variable {W A Ω : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
  [MeasurableSpace Ω]

open Classical in
/-- The worlds that win every one of their tests. -/
noncomputable def survivors (R : Finset (W × W)) (beat : W → W → Set Ω) (ω : Ω) : Finset W :=
  Finset.univ.filter (fun w => ∀ v, (w, v) ∈ R → ω ∈ beat w v)

open Classical in
/-- Output a common safe answer of the survivors, if there is one. -/
noncomputable def decode (safe : W → Finset A) (R : Finset (W × W)) (beat : W → W → Set Ω)
    (a0 : A) (ω : Ω) : A :=
  if h : ∃ a, ∀ u ∈ survivors R beat ω, a ∈ safe u then Classical.choose h else a0

/-- No two survivors form a tested pair: one of them lost. -/
theorem survivors_untested (R : Finset (W × W)) (hsymm : ∀ u v, (u, v) ∈ R → (v, u) ∈ R)
    (beat : W → W → Set Ω) (hanti : ∀ u v, (u, v) ∈ R → beat v u = (beat u v)ᶜ) (ω : Ω)
    (u : W) (hu : u ∈ survivors R beat ω) (v : W) (hv : v ∈ survivors R beat ω) :
    (u, v) ∉ R := by
  classical
  intro huv
  have h1 : ω ∈ beat u v := (Finset.mem_filter.mp hu).2 v huv
  have h2 : ω ∈ beat v u := (Finset.mem_filter.mp hv).2 u (hsymm u v huv)
  rw [hanti u v huv] at h2
  exact h2 h1

/-- **The tournament is safe whenever the truth wins its own tests.** -/
theorem decode_safe (safe : W → Finset A) (R : Finset (W × W))
    (hres : ∀ H : Finset W, Unsafe safe H → ∃ u ∈ H, ∃ v ∈ H, u ≠ v ∧ (u, v) ∈ R)
    (hsymm : ∀ u v, (u, v) ∈ R → (v, u) ∈ R)
    (beat : W → W → Set Ω) (hanti : ∀ u v, (u, v) ∈ R → beat v u = (beat u v)ᶜ)
    (a0 : A) (w : W) (ω : Ω) (hω : ∀ v, (w, v) ∈ R → ω ∈ beat w v) :
    decode safe R beat a0 ω ∈ safe w := by
  classical
  have hw : w ∈ survivors R beat ω := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hω⟩
  have hsafeS : ¬ Unsafe safe (survivors R beat ω) := by
    intro hU
    obtain ⟨u, hu, v, hv, -, huv⟩ := hres _ hU
    exact survivors_untested R hsymm beat hanti ω u hu v hv huv
  have hex : ∃ a, ∀ u ∈ survivors R beat ω, a ∈ safe u := by
    unfold Unsafe at hsafeS
    push_neg at hsafeS
    exact hsafeS
  unfold decode
  rw [dif_pos hex]
  exact Classical.choose_spec hex w hw

/-- **The tournament's error is at most the truth's own test errors, summed.** -/
theorem decode_error (safe : W → Finset A) (R : Finset (W × W))
    (hres : ∀ H : Finset W, Unsafe safe H → ∃ u ∈ H, ∃ v ∈ H, u ≠ v ∧ (u, v) ∈ R)
    (hsymm : ∀ u v, (u, v) ∈ R → (v, u) ∈ R)
    (beat : W → W → Set Ω) (hanti : ∀ u v, (u, v) ∈ R → beat v u = (beat u v)ᶜ)
    (a0 : A) (μ : Measure Ω) (w : W) (ε : ℝ≥0∞)
    (herr : ∀ v, (w, v) ∈ R → μ (beat v w) ≤ ε) :
    μ {ω | decode safe R beat a0 ω ∉ safe w} ≤ Fintype.card W * ε := by
  classical
  set F := (Finset.univ : Finset W).filter (fun v => (w, v) ∈ R) with hF
  have hsub : {ω | decode safe R beat a0 ω ∉ safe w} ⊆ ⋃ v ∈ F, beat v w := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    apply hω
    refine decode_safe safe R hres hsymm beat hanti a0 w ω fun v hv => ?_
    have hnot : ω ∉ beat v w := fun h => hcon v (by simp [hF, hv]) h
    rw [hanti w v hv] at hnot
    simpa using hnot
  calc μ {ω | decode safe R beat a0 ω ∉ safe w} ≤ μ (⋃ v ∈ F, beat v w) := measure_mono hsub
    _ ≤ ∑ v ∈ F, μ (beat v w) := measure_biUnion_finset_le F _
    _ ≤ ∑ _v ∈ F, ε := Finset.sum_le_sum fun v hv => herr v (Finset.mem_filter.mp hv).2
    _ = F.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card W * ε := by
        gcongr
        exact_mod_cast Finset.card_le_univ F

/-- The pairs tested at threshold `t`. -/
noncomputable def pairSet (κ : W → W → ℝ≥0) (t : ℝ≥0) : Finset (W × W) :=
  (Finset.univ : Finset (W × W)).filter (fun p => p.1 ≠ p.2 ∧ t ≤ κ p.1 p.2)

theorem pairSet_resolves (κ : W → W → ℝ≥0) (safe : W → Finset A) (t : ℝ≥0)
    (h : Resolves κ safe t) :
    ∀ H : Finset W, Unsafe safe H → ∃ u ∈ H, ∃ v ∈ H, u ≠ v ∧ (u, v) ∈ pairSet κ t := by
  intro H hH
  obtain ⟨u, hu, v, hv, hne, hle⟩ := h H hH
  exact ⟨u, hu, v, hv, hne, by simp [pairSet, hne, hle]⟩

theorem pairSet_symm (κ : W → W → ℝ≥0) (hκ : ∀ u v, κ u v = κ v u) (t : ℝ≥0) :
    ∀ u v, (u, v) ∈ pairSet κ t → (v, u) ∈ pairSet κ t := by
  intro u v h
  simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  exact ⟨Ne.symm h.1, (hκ u v) ▸ h.2⟩

/-- A test of exponent `c kappa` on `n >= log(|W|/delta)/(c t)` samples errs with
probability at most `delta / |W|` on every pair with `kappa >= t`. -/
theorem test_budget (c t κ δ n : ℝ) (hc : 0 < c) (ht : 0 < t) (hκ : t ≤ κ) (hδ : 0 < δ)
    (K : ℝ) (hK : 0 < K) (hn0 : 0 ≤ n) (hn : Real.log (K / δ) / (c * t) ≤ n) :
    Real.exp (-(c * n * κ)) ≤ δ / K := by
  have hct : 0 < c * t := mul_pos hc ht
  have hn1 : Real.log (K / δ) ≤ c * t * n := by
    rw [div_le_iff₀ hct] at hn
    linarith
  have hmono : c * t * n ≤ c * n * κ := by
    have := mul_le_mul_of_nonneg_left hκ (mul_nonneg hc.le hn0)
    nlinarith
  calc Real.exp (-(c * n * κ)) ≤ Real.exp (-Real.log (K / δ)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = δ / K := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp

/-- **The upper law.**  If every obstruction is resolved at `t`, the pairwise tests on the
pairs of `pairSet kappa t` have exponent `c kappa` on `n` samples, and
`n >= log(|W|/delta)/(c t)`, then the tournament's output is safe with probability
`>= 1 - delta` at every world.  It uses at most `|W|^2 n` queries. -/
theorem tournament_law (safe : W → Finset A) (κ : W → W → ℝ≥0) (hκ : ∀ u v, κ u v = κ v u)
    (t : ℝ≥0) (ht : 0 < t) (hres : Resolves κ safe t)
    (beat : W → W → Set Ω)
    (hanti : ∀ u v, (u, v) ∈ pairSet κ t → beat v u = (beat u v)ᶜ)
    (a0 : A) (μ : W → Measure Ω) (c δ n : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hn0 : 0 ≤ n)
    (hn : Real.log ((Fintype.card W : ℝ) / δ) / (c * t) ≤ n)
    (herr : ∀ w v, (w, v) ∈ pairSet κ t →
      μ w (beat v w) ≤ ENNReal.ofReal (Real.exp (-(c * n * κ w v)))) :
    (∀ w, μ w {ω | decode safe (pairSet κ t) beat a0 ω ∉ safe w} ≤ ENNReal.ofReal δ)
      ∧ ((pairSet κ t).card : ℝ) * n ≤ (Fintype.card W : ℝ) ^ 2 * n := by
  classical
  refine ⟨fun w => ?_, ?_⟩
  · have hWpos : (0 : ℝ) < Fintype.card W := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨w⟩
    have hε : ∀ v, (w, v) ∈ pairSet κ t →
        μ w (beat v w) ≤ ENNReal.ofReal (δ / Fintype.card W) := by
      intro v hv
      refine (herr w v hv).trans (ENNReal.ofReal_le_ofReal ?_)
      have hkv : (t : ℝ) ≤ κ w v := by
        have := (Finset.mem_filter.mp hv).2.2
        exact_mod_cast this
      exact test_budget c t (κ w v) δ n hc (by exact_mod_cast ht) hkv hδ _ hWpos hn0 hn
    have h := decode_error safe (pairSet κ t) (pairSet_resolves κ safe t hres)
      (pairSet_symm κ hκ t) beat hanti a0 (μ w) w _ hε
    refine h.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  · have hcard : ((pairSet κ t).card : ℝ) ≤ (Fintype.card W : ℝ) ^ 2 := by
      have : (pairSet κ t).card ≤ Fintype.card (W × W) := Finset.card_le_univ _
      rw [Fintype.card_prod] at this
      have h2 : ((pairSet κ t).card : ℝ) ≤ ((Fintype.card W * Fintype.card W : ℕ) : ℝ) := by
        exact_mod_cast this
      simpa [sq] using h2
    exact mul_le_mul_of_nonneg_right hcard hn0

end Upper

/-! ## 4. The order law on a graded channel -/

section Graded

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

/-- The graded information `C h^{2 sep}`. -/
noncomputable def graded (sep : W → W → ℕ) (C h : ℝ≥0) : W → W → ℝ≥0 :=
  fun w w' => C * h ^ (2 * sep w w')

/-- **Resolving at `C h^{2s}` is exactly the safe-order law at `s`.** -/
theorem graded_resolves_iff (sep : W → W → ℕ) (safe : W → Finset A) (C h : ℝ≥0) (hC : 0 < C)
    (h0 : 0 < h) (h1 : h < 1) (s : ℕ) :
    Resolves (graded sep C h) safe (C * h ^ (2 * s)) ↔ SafeAt sep safe s := by
  rw [safeAt_iff]
  have key : ∀ k : ℕ, C * h ^ (2 * s) ≤ C * h ^ (2 * k) ↔ k ≤ s := by
    intro k
    rw [mul_le_mul_iff_right₀ hC, pow_le_pow_iff_right_of_lt_one₀ h0 h1]
    constructor <;> intro hh <;> omega
  constructor
  · intro hr H hH
    obtain ⟨w, hw, w', hw', hne, hle⟩ := hr H hH
    exact ⟨w, hw, w', hw', hne, (key _).mp hle⟩
  · intro hs H hH
    obtain ⟨w, hw, w', hw', hne, hle⟩ := hs H hH
    exact ⟨w, hw, w', hw', hne, (key _).mpr hle⟩

/-- **The order law.**  On a graded channel the obstruction information is `C h^{2 sStar}`
with `sStar` the least order at which `SafeAt` holds: the rate exponent is twice the safe
order.  Stated as: every obstruction is resolved at `C h^{2 sStar}`, and some obstruction has
every pair at most `C h^{2 sStar}`. -/
theorem graded_tStar [Nonempty A] (sep : W → W → ℕ) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty) (hex : ∃ H : Finset W, Unsafe safe H)
    (C h : ℝ≥0) (hC : 0 < C) (h0 : 0 < h) (h1 : h < 1) (sStar : ℕ)
    (hS : SafeAt sep safe sStar) (hmin : ∀ s, SafeAt sep safe s → sStar ≤ s) :
    Resolves (graded sep C h) safe (C * h ^ (2 * sStar))
      ∧ ∃ H : Finset W, Unsafe safe H
          ∧ ∀ w ∈ H, ∀ w' ∈ H, w ≠ w' → graded sep C h w w' ≤ C * h ^ (2 * sStar) := by
  have htwo := two_le_card_of_unsafe safe hsafe
  refine ⟨(graded_resolves_iff sep safe C h hC h0 h1 sStar).mpr hS, ?_⟩
  obtain ⟨tStar, hres, H, hH, htight⟩ := obstruction_value (graded sep C h) safe hex htwo
  -- `tStar` is attained by some pair, hence of the form `C h^{2k}`
  have hcard := htwo H hH
  obtain ⟨w, hw, w', hw', hne, hle⟩ := hres H hH
  have heq : tStar = graded sep C h w w' := le_antisymm hle (htight w hw w' hw' hne)
  have hk : SafeAt sep safe (sep w w') := by
    have := resolves_mono (graded sep C h) safe (le_of_eq heq.symm) hres
    exact (graded_resolves_iff sep safe C h hC h0 h1 (sep w w')).mp this
  have hsk := hmin _ hk
  refine ⟨H, hH, fun u hu u' hu' hne' => (htight u hu u' hu' hne').trans ?_⟩
  rw [heq]
  unfold graded
  rw [mul_le_mul_iff_right₀ hC]
  exact pow_le_pow_of_le_one h0.le h1.le (by omega)

/-- **The overlapping correspondence** (`safe w = everything but w`): the safe order is the
least separation order over all pairs. -/
theorem coSafe_order (sep : W → W → ℕ) (s : ℕ) :
    SafeAt sep (coSafe : W → Finset W) s ↔ ∃ w w' : W, w ≠ w' ∧ sep w w' ≤ s :=
  coSafe_safeAt_iff sep s

/-- **Identification** (`safe w = {w}`): for a symmetric separation order, the safe order is
the largest separation order. -/
theorem id_order [Nonempty W] (sep : W → W → ℕ) (hsymm : ∀ w w', sep w w' = sep w' w) (s : ℕ) :
    SafeAt sep (fun w : W => ({w} : Finset W)) s ↔ ∀ w w' : W, w ≠ w' → sep w w' ≤ s := by
  rw [safeAt_iff]
  constructor
  · intro h w w' hne
    have hU : Unsafe (fun w : W => ({w} : Finset W)) {w, w'} := by
      intro a
      by_cases ha : a = w
      · refine ⟨w', by simp, ?_⟩
        rw [ha, Finset.mem_singleton]
        exact hne
      · refine ⟨w, by simp, ?_⟩
        rw [Finset.mem_singleton]
        exact ha
    obtain ⟨u, hu, u', hu', hne', hle⟩ := h _ hU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hu'
    rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl
    · exact absurd rfl hne'
    · exact hle
    · rw [hsymm]; exact hle
    · exact absurd rfl hne'
  · intro h H hH
    have h2 : 2 ≤ H.card := by
      by_contra hc
      push_neg at hc
      rcases (by omega : H.card = 0 ∨ H.card = 1) with h0 | h1
      · have : H = ∅ := Finset.card_eq_zero.mp h0
        obtain ⟨w, hw, -⟩ := hH (Classical.arbitrary W)
        simp [this] at hw
      · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
        obtain ⟨u, hu, hna⟩ := hH w
        rw [Finset.mem_singleton] at hu
        subst hu
        exact hna (Finset.mem_singleton_self _)
    obtain ⟨a, ha, b, hb, hab⟩ := (Finset.one_lt_card (s := H)).mp (by omega)
    exact ⟨a, ha, b, hb, hab, h a b hab⟩

end Graded

/-! ## Audit -/

#print axioms obstruction_value
#print axioms resolves_iff_le
#print axioms two_le_card_of_unsafe
#print axioms tauN_eq_sum_cnt
#print axioms info_le_cost
#print axioms obstruction_pigeonhole
#print axioms obstruction_lower
#print axioms obstruction_lower_star
#print axioms survivors_untested
#print axioms decode_safe
#print axioms decode_error
#print axioms test_budget
#print axioms tournament_law
#print axioms graded_resolves_iff
#print axioms graded_tStar
#print axioms coSafe_order
#print axioms id_order

end CIGAMF.P13.PaperBObstructionLaw
