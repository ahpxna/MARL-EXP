import «LeanPaperASacrificeDualityV1»

/-!
# Paper A: the repair frontier bounds the sequential cost of every budgeted policy

**Setting (any channel).** Worlds `W`, finite queries `Q` with a dummy, a world `θ`. A design is
a nonnegative vector on the informative queries summing to one. For a set `L` of alternatives,
the design's true information is `Jt(w) = inf_{λ ∈ L} Σ_q w_q KL_q(θ, λ)`.

**The budget classes.** A policy's *expected design* is `w̄_q = E_θ N_q / E_θ N`. A budget `b`
on a sacrifice `s` constrains `s(w̄) ≤ b`: this is the class `Π_b^exp`. When `s` is convex,
which is the case for `s = 1 - J_proxy/Γ` with `J_proxy` an infimum of linear forms, a
per-round budget or a pathwise budget on the realised design implies the expected one. So
`Π_b^exp` is the largest of the three classes, and the bound below covers all of them.

* `event_info`: one change of measure, for an event of probability `p` at `θ` and at most `δ` at
  `λ`: `p log(1/δ) - log 2 ≤ Σ_q E N_q KL_q(θ,λ)`.
* `budget_law`: **every `δ`-correct policy whose expected design meets the budget pays
  `E_θ N · R ≥ (1-δ) log(1/δ) - log 2`** for every `R` that bounds the true information of the
  designs within the budget. With `R = R_θ(b)` this is `E_θ N ≥ D_δ / R_θ(b)`.
* `budget_law_multi`: with several correct answers at `θ` the policy may split its answers; the
  answer it outputs most often at `θ` carries the bound with `(1-δ)/|correct|` in place of
  `1 - δ`.

**Repair, characterised** (in the abstract setting of `LeanPaperASacrificeDualityV1`):
* `no_threshold`: if any design has positive true information, then every positive budget buys
  positive information. There is no threshold `b₀ > 0` below which repair is free of effect.
* `linear_repair`: with a certificate pair and a design `v` with `Jt(v) > 0`, the frontier is
  linear on `[0, s(v)]`, pinched between `(Jt(v)/s(v)) b` and `b/Σν`.

**A second class** (`TwoArm`), with an alternative structure unlike the compression family.
* Two Gaussian arms, and the decision is which mean is larger.
* The frozen surrogate lets only the leader move: `J_proxy(w) = w₁Δ²/2` (`jproxy2_eq`). The
  true game lets both move: `Jt(w) = w₁w₂Δ²/2` (`jtrue2_eq`).
* The surrogate's optimum starves the second arm and learns nothing (`two_arm_starvation`).
* The frontier is exact: `R(b) = b(1-b)Δ²/2` on `[0, 1/2]` (`two_arm_frontier`), with slope
  `Δ²/2` at `0`. The certificate pair of the duality meets it at first order
  (`two_arm_certificate`).
-/

namespace CIGAMF.P13.PaperARepairLaw

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperALowerKL
open CIGAMF.P13.PaperALowerGame CIGAMF.P13.PaperBObstruction CIGAMF.P13.PaperASacrificeDuality
open CIGAMF.P13.PaperAFamilyLower

/-! ## 1. The budget law on any channel -/

section Channel

variable {W Q A : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q]

/-- The expected count of query `q` at world `θ` within horizon `n`. -/
noncomputable def ecnt (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) (q : Q) : ℝ :=
  (∫⁻ ω, cntQ q n ω ∂hist C π θ n).toReal

/-- The expected number of informative queries. -/
noncomputable def etot (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) : ℝ :=
  ∑ q, ecnt C π θ n q * (if q = C.dummy then 0 else 1)

/-- The expected design: informative counts over their total. -/
noncomputable def ebar (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) (q : Q) : ℝ :=
  ecnt C π θ n q * (if q = C.dummy then 0 else 1) / etot C π θ n

/-- The information of a design against an alternative. -/
noncomputable def infoAt (C : Channel W Q) (θ l : W) (w : Q → ℝ) : ℝ :=
  ∑ q, w q * (klq C θ l q).toReal

/-- The true information of a design: the infimum over the alternatives. -/
noncomputable def Jt (C : Channel W Q) (θ : W) (L : Set W) (w : Q → ℝ) : ℝ :=
  ⨅ l : L, infoAt C θ l w

theorem ecnt_nonneg (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) (q : Q) :
    0 ≤ ecnt C π θ n q := ENNReal.toReal_nonneg

theorem infoAt_nonneg (C : Channel W Q) (θ l : W) (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) :
    0 ≤ infoAt C θ l w :=
  Finset.sum_nonneg fun q _ => mul_nonneg (hw q) ENNReal.toReal_nonneg

/-- **One change of measure.** -/
theorem event_info (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ l : W) (S : Set (Hist Q n))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hl : (hist C π l n).real S ≤ δ)
    (hfin : ∀ q, klq C θ l q ≠ ⊤) :
    (hist C π θ n).real S * Real.log (1 / δ) - Real.log 2
      ≤ ∑ q, ecnt C π θ n q * (klq C θ l q).toReal := by
  haveI := hist_prob C π θ n
  haveI := hist_prob C π l n
  have hsum0 : 0 ≤ ∑ q, ecnt C π θ n q * (klq C θ l q).toReal :=
    Finset.sum_nonneg fun q _ => mul_nonneg (ecnt_nonneg C π θ n q) ENNReal.toReal_nonneg
  by_cases hD : 0 ≤ (hist C π θ n).real S * Real.log (1 / δ) - Real.log 2
  · have hev := event_klDiv_ge (hist C π θ n) (hist C π l n) S hS δ hδ hl
    have hchain : ENNReal.ofReal ((hist C π θ n).real S * Real.log (1 / δ) - Real.log 2)
        ≤ ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q :=
      hev.trans ((transcript_kl_le_qsum C π θ l n).trans (le_of_eq (lintegral_qsum_eq _ _)))
    exact real_of_change _ hD _ _ (fun q => lintegral_cntQ_ne_top C π θ q n) hfin hchain
  · linarith

theorem etot_mul_infoAt (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) (l : W)
    (hpos : 0 < etot C π θ n) :
    etot C π θ n * infoAt C θ l (ebar C π θ n) = ∑ q, ecnt C π θ n q * (klq C θ l q).toReal := by
  unfold infoAt ebar
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : q = C.dummy
  · subst hq
    rw [klq_dummy C θ l]
    simp
  · simp only [hq, if_false, mul_one]
    field_simp

theorem ebar_nonneg (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) (hpos : 0 < etot C π θ n)
    (q : Q) : 0 ≤ ebar C π θ n q := by
  unfold ebar
  exact div_nonneg (mul_nonneg (ecnt_nonneg _ _ _ _ _) (by split_ifs <;> norm_num)) hpos.le

/-- **The budget law.**  A policy that answers correctly with probability `1 - δ` at `θ` and
wrongly with probability at most `δ` at every alternative of `L` satisfies
`D_δ ≤ E_θ N · Jt(w̄)`. If its expected design meets a budget `s(w̄) ≤ b`, and `R` bounds the
true information of every design within the budget, then `D_δ ≤ E_θ N · R`. -/
theorem budget_law (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ : W) (L : Set W) [Nonempty L]
    (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist C π θ n).real S) (hL : ∀ l ∈ L, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hpos : 0 < etot C π θ n)
    (s : (Q → ℝ) → ℝ) (b R : ℝ) (hR : ∀ w : Q → ℝ, (∀ q, 0 ≤ w q) → s w ≤ b → Jt C θ L w ≤ R)
    (hbud : s (ebar C π θ n) ≤ b) :
    (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ etot C π θ n * Jt C θ L (ebar C π θ n)
      ∧ (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ etot C π θ n * R := by
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hw0 := ebar_nonneg C π θ n hpos
  have hper : ∀ l : L, ((1 - δ) * Real.log (1 / δ) - Real.log 2) / etot C π θ n
      ≤ infoAt C θ l (ebar C π θ n) := by
    intro l
    have h := event_info C π n θ l S hS δ hδ (hL l l.2) (hfin l l.2)
    rw [← etot_mul_infoAt C π θ n l hpos] at h
    rw [div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_right hθ hlog
    nlinarith
  have hJ : ((1 - δ) * Real.log (1 / δ) - Real.log 2) / etot C π θ n
      ≤ Jt C θ L (ebar C π θ n) := le_ciInf hper
  have h1 : (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ etot C π θ n * Jt C θ L (ebar C π θ n) := by
    have := (div_le_iff₀ hpos).mp hJ
    nlinarith
  refine ⟨h1, h1.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hR _ hw0 hbud) hpos.le

/-- **The budget law with several correct answers.**  If the output is correct at `θ` with
probability `1 - δ`, the answer `a` output most often carries `(1-δ)/|correct|`, and against the
alternatives where `a` is wrong the same budget bound holds. -/
theorem budget_law_multi [Fintype A] [DecidableEq A] (C : Channel W Q) (π : Policy Q) (n : ℕ)
    (θ : W) (out : Hist Q n → A) (hmeas : ∀ a, MeasurableSet {ω | out ω = a})
    (corr : Finset A) (hcorr : corr.Nonempty) (Alt : A → Set W) [∀ a, Nonempty (Alt a)]
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist C π θ n).real {ω | out ω ∈ corr})
    (hL : ∀ a ∈ corr, ∀ l ∈ Alt a, (hist C π l n).real {ω | out ω = a} ≤ δ)
    (hfin : ∀ a ∈ corr, ∀ l ∈ Alt a, ∀ q, klq C θ l q ≠ ⊤) (hpos : 0 < etot C π θ n) :
    ∃ a ∈ corr, (1 - δ) / corr.card * Real.log (1 / δ) - Real.log 2
      ≤ etot C π θ n * Jt C θ (Alt a) (ebar C π θ n) := by
  classical
  haveI := hist_prob C π θ n
  -- pigeonhole over the correct answers
  have hsub : {ω | out ω ∈ corr} = ⋃ a ∈ corr, {ω | out ω = a} := by ext ω; simp
  have hsum : 1 - δ ≤ ∑ a ∈ corr, (hist C π θ n).real {ω | out ω = a} := by
    refine hθ.trans ?_
    rw [hsub]
    exact measureReal_biUnion_finset_le corr _
  have hcard : (0 : ℝ) < corr.card := by exact_mod_cast hcorr.card_pos
  have hconst : ∑ _a ∈ corr, (1 - δ) / corr.card = 1 - δ := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hcard.ne']
  obtain ⟨a, ha, hpa⟩ := Finset.exists_le_of_sum_le hcorr (hconst.le.trans hsum)
  refine ⟨a, ha, ?_⟩
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hw0 := ebar_nonneg C π θ n hpos
  have hper : ∀ l : Alt a, ((1 - δ) / corr.card * Real.log (1 / δ) - Real.log 2) / etot C π θ n
      ≤ infoAt C θ l (ebar C π θ n) := by
    intro l
    have h := event_info C π n θ l _ (hmeas a) δ hδ (hL a ha l l.2) (hfin a ha l l.2)
    rw [← etot_mul_infoAt C π θ n l hpos] at h
    rw [div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_right hpa hlog
    nlinarith
  have hJ := (div_le_iff₀ hpos).mp (le_ciInf hper)
  calc _ ≤ _ := hJ
    _ = _ := mul_comm _ _

end Channel

/-! ## 2. Repair, characterised -/

section Characterisation

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **No threshold.**  If some design has positive true information, then every positive budget
buys a design with positive true information. -/
theorem no_threshold (Jf Jt : (ι → ℝ) → ℝ) (Γ : ℝ) (hΓ : 0 < Γ)
    (hconcf : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jf a + β * Jf b ≤ Jf (mixD β a b))
    (hconct : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jt a + β * Jt b ≤ Jt (mixD β a b))
    (wstar : ι → ℝ) (hws : IsAllocG wstar) (hopt : Jf wstar = Γ) (hJt0 : 0 ≤ Jt wstar)
    (v : ι → ℝ) (hv : IsAllocG v) (hJv : 0 < Jt v) (b : ℝ) (hb : 0 < b) :
    ∃ w, IsAllocG w ∧ sac Jf Γ w ≤ b ∧ 0 < Jt w := by
  by_cases hsv : sac Jf Γ v ≤ b
  · exact ⟨v, hv, hsv, hJv⟩
  · push_neg at hsv
    have hsv0 : 0 < sac Jf Γ v := hb.trans hsv
    obtain ⟨w, hw, hsw, hJw⟩ := repair_clipped Jf Jt Γ hΓ hconcf hconct wstar v hws hv hopt hJt0
      b hb.le hsv0
    refine ⟨w, hw, hsw, lt_of_lt_of_le ?_ hJw⟩
    exact mul_pos (lt_min one_pos (div_pos hb hsv0)) hJv

/-- **Linear repair, both sides.**  With a certificate pair and a design `v` with
`0 < Jt(v)` and `0 < s(v)`: for `b ∈ [0, s(v)]` some design within the budget carries
`(Jt(v)/s(v)) b`, and no design within the budget carries more than `b/Σν`. -/
theorem linear_repair (Jf Jt : (ι → ℝ) → ℝ) (Γ : ℝ) (hΓ : 0 < Γ)
    (hconcf : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jf a + β * Jf b ≤ Jf (mixD β a b))
    (hconct : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jt a + β * Jt b ≤ Jt (mixD β a b))
    (wstar : ι → ℝ) (hws : IsAllocG wstar) (hopt : Jf wstar = Γ) (hJt0 : 0 ≤ Jt wstar)
    (c : ι → ℝ) (hc : ∀ w, IsAllocG w → Jf w ≤ ∑ e, w e * c e)
    (L : κ → ι → ℝ) (hL : ∀ j w, IsAllocG w → Jt w ≤ ∑ e, w e * L j e)
    (ν : κ → ℝ) (hν : ∀ j, 0 ≤ ν j) (hcover : ∀ e, ∑ j, ν j * L j e ≤ margin c Γ e)
    (hνpos : 0 < ∑ j, ν j)
    (v : ι → ℝ) (hv : IsAllocG v) (hJv : 0 < Jt v) (hsv : 0 < sac Jf Γ v)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ sac Jf Γ v) :
    (∃ w, IsAllocG w ∧ sac Jf Γ w ≤ b ∧ Jt v / sac Jf Γ v * b ≤ Jt w)
      ∧ ∀ w, IsAllocG w → sac Jf Γ w ≤ b → Jt w ≤ b / ∑ j, ν j := by
  refine ⟨?_, fun w hw hsw => ?_⟩
  · obtain ⟨w, hw, hsw, hJw⟩ := repair_clipped Jf Jt Γ hΓ hconcf hconct wstar v hws hv hopt
      hJt0 b hb0 hsv
    refine ⟨w, hw, hsw, le_trans (le_of_eq ?_) hJw⟩
    rw [min_eq_right ((div_le_one hsv).mpr hb1)]
    ring
  · have h := frontier_upper Jf Jt Γ hΓ c hc L hL ν hν hcover w hw
    rw [le_div_iff₀ hνpos]
    linarith

end Characterisation

/-! ## 3. A second class: two Gaussian arms, and a surrogate that lets only the leader move -/

section TwoArm

variable (μ₁ μ₂ : ℝ)

/-- The true alternatives: the order of the means is reversed or tied. -/
def altTrue : Set (Fin 2 → ℝ) := {l | l 0 ≤ l 1}

/-- The frozen alternatives: only the leader moves, the other arm stays at `μ₂`. -/
def altFrozen : Set (Fin 2 → ℝ) := {l | l 0 ≤ μ₂ ∧ l 1 = μ₂}

/-- The Gaussian energy of a design against an alternative, unit variance. -/
noncomputable def en2 (w l : Fin 2 → ℝ) : ℝ :=
  (w 0 * (μ₁ - l 0) ^ 2 + w 1 * (μ₂ - l 1) ^ 2) / 2

noncomputable def jtrue2 (w : Fin 2 → ℝ) : ℝ := ⨅ l : altTrue, en2 μ₁ μ₂ w l

noncomputable def jproxy2 (w : Fin 2 → ℝ) : ℝ := ⨅ l : altFrozen μ₂, en2 μ₁ μ₂ w l

instance : Nonempty (altTrue) := ⟨⟨fun _ => 0, by simp [altTrue]⟩⟩

instance : Nonempty (altFrozen μ₂) := ⟨⟨fun _ => μ₂, by simp [altFrozen]⟩⟩

theorem en2_nonneg (w l : Fin 2 → ℝ) (hw : ∀ i, 0 ≤ w i) : 0 ≤ en2 μ₁ μ₂ w l := by
  unfold en2
  have := hw 0; have := hw 1
  positivity

/-- **The true game of two arms.**  For `μ₁ ≥ μ₂` and an allocation, `Jt(w) = w₀w₁Δ²/2`. -/
theorem jtrue2_eq (hμ : μ₂ ≤ μ₁) (w : Fin 2 → ℝ) (hw : IsAllocG w) :
    jtrue2 μ₁ μ₂ w = w 0 * w 1 * (μ₁ - μ₂) ^ 2 / 2 := by
  have hsum : w 0 + w 1 = 1 := by have := hw.2; simpa [Fin.sum_univ_two] using this
  have hw0 := hw.1 0; have hw1 := hw.1 1
  apply le_antisymm
  · -- the weighted mean is an alternative
    set m := w 0 * μ₁ + w 1 * μ₂ with hm
    have hmem : (fun _ : Fin 2 => m) ∈ altTrue := by simp [altTrue]
    refine (ciInf_le ⟨0, by rintro x ⟨l, rfl⟩; exact en2_nonneg μ₁ μ₂ w l hw.1⟩
      (⟨fun _ => m, hmem⟩ : altTrue)).trans (le_of_eq ?_)
    unfold en2
    simp only
    have h1 : μ₁ - m = w 1 * (μ₁ - μ₂) := by rw [hm]; linear_combination (μ₁) * hsum.symm
    have h2 : μ₂ - m = -(w 0 * (μ₁ - μ₂)) := by rw [hm]; linear_combination (μ₂) * hsum.symm
    rw [h1, h2]
    have : w 0 + w 1 = 1 := hsum
    have e : w 0 * (w 1 * (μ₁ - μ₂)) ^ 2 + w 1 * (-(w 0 * (μ₁ - μ₂))) ^ 2
        = w 0 * w 1 * (μ₁ - μ₂) ^ 2 * (w 0 + w 1) := by ring
    rw [e, this, mul_one]
  · refine le_ciInf fun l => ?_
    have hl : l.1 0 ≤ l.1 1 := l.2
    unfold en2
    set a := μ₁ - l.1 0
    set c := l.1 1 - μ₂
    have hac : μ₁ - μ₂ ≤ a + c := by simp only [a, c]; linarith
    have hΔ : 0 ≤ μ₁ - μ₂ := by linarith
    have hsq : (μ₁ - μ₂) ^ 2 ≤ (a + c) ^ 2 := pow_le_pow_left₀ hΔ hac 2
    have hcs : w 0 * w 1 * (a + c) ^ 2 ≤ w 0 * a ^ 2 + w 1 * c ^ 2 := by
      have key : w 0 * a ^ 2 + w 1 * c ^ 2 - w 0 * w 1 * (a + c) ^ 2
          = (w 0 * a - w 1 * c) ^ 2 := by
        have h1 : w 1 = 1 - w 0 := by linarith
        rw [h1]; ring
      nlinarith [sq_nonneg (w 0 * a - w 1 * c)]
    have hc2 : (μ₂ - l.1 1) ^ 2 = c ^ 2 := by simp only [c]; ring
    rw [hc2]
    have : w 0 * w 1 * (μ₁ - μ₂) ^ 2 ≤ w 0 * w 1 * (a + c) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hw0 hw1)
    linarith

/-- **The frozen game of two arms.**  `J_proxy(w) = w₀Δ²/2`. -/
theorem jproxy2_eq (hμ : μ₂ ≤ μ₁) (w : Fin 2 → ℝ) (hw : IsAllocG w) :
    jproxy2 μ₁ μ₂ w = w 0 * (μ₁ - μ₂) ^ 2 / 2 := by
  have hw0 := hw.1 0
  apply le_antisymm
  · have hmem : (fun i : Fin 2 => μ₂) ∈ altFrozen μ₂ := by simp [altFrozen]
    refine (ciInf_le ⟨0, by rintro x ⟨l, rfl⟩; exact en2_nonneg μ₁ μ₂ w l hw.1⟩
      (⟨fun _ => μ₂, hmem⟩ : altFrozen μ₂)).trans (le_of_eq ?_)
    unfold en2; simp
  · refine le_ciInf fun l => ?_
    obtain ⟨hl0, hl1⟩ := l.2
    unfold en2
    rw [hl1, sub_self]
    have h : (μ₁ - μ₂) ^ 2 ≤ (μ₁ - l.1 0) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have := mul_le_mul_of_nonneg_left h hw0
    nlinarith

/-- The frozen value `Γ = Δ²/2` is attained at the leader-only design. -/
def leader : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

theorem leader_alloc : IsAllocG leader := ⟨fun i => by unfold leader; split_ifs <;> norm_num,
  by simp [leader, Fin.sum_univ_two]⟩

theorem jproxy2_leader (hμ : μ₂ ≤ μ₁) : jproxy2 μ₁ μ₂ leader = (μ₁ - μ₂) ^ 2 / 2 := by
  rw [jproxy2_eq μ₁ μ₂ hμ leader leader_alloc]; simp [leader]

/-- **Starvation.**  The surrogate's optimum learns nothing about the decision. -/
theorem two_arm_starvation (hμ : μ₂ ≤ μ₁) : jtrue2 μ₁ μ₂ leader = 0 := by
  rw [jtrue2_eq μ₁ μ₂ hμ leader leader_alloc]; simp [leader]

/-- The sacrifice of a design is its mass on the second arm. -/
theorem two_arm_sac (hμ : μ₂ < μ₁) (w : Fin 2 → ℝ) (hw : IsAllocG w) :
    sac (jproxy2 μ₁ μ₂) ((μ₁ - μ₂) ^ 2 / 2) w = w 1 := by
  unfold sac
  rw [jproxy2_eq μ₁ μ₂ hμ.le w hw]
  have hΔ : (μ₁ - μ₂) ^ 2 ≠ 0 := by
    have h : 0 < μ₁ - μ₂ := by linarith
    positivity
  have hsum : w 0 + w 1 = 1 := by have := hw.2; simpa [Fin.sum_univ_two] using this
  have hΔ2 : (μ₁ - μ₂) ^ 2 / 2 ≠ 0 := by positivity
  rw [show w 0 * (μ₁ - μ₂) ^ 2 / 2 = w 0 * ((μ₁ - μ₂) ^ 2 / 2) by ring, mul_div_assoc,
    div_self hΔ2, mul_one]
  linarith

/-- **The exact frontier.**  For `b ∈ [0, 1/2]`, every design giving up at most `b` carries at
most `b(1-b)Δ²/2`, and the design `(1-b, b)` carries exactly that. -/
theorem two_arm_frontier (hμ : μ₂ < μ₁) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) :
    (∀ w, IsAllocG w → sac (jproxy2 μ₁ μ₂) ((μ₁ - μ₂) ^ 2 / 2) w ≤ b →
        jtrue2 μ₁ μ₂ w ≤ b * (1 - b) * (μ₁ - μ₂) ^ 2 / 2)
      ∧ ∃ w, IsAllocG w ∧ sac (jproxy2 μ₁ μ₂) ((μ₁ - μ₂) ^ 2 / 2) w ≤ b
          ∧ jtrue2 μ₁ μ₂ w = b * (1 - b) * (μ₁ - μ₂) ^ 2 / 2 := by
  refine ⟨fun w hw hs => ?_, ?_⟩
  · rw [two_arm_sac μ₁ μ₂ hμ w hw] at hs
    rw [jtrue2_eq μ₁ μ₂ hμ.le w hw]
    have hsum : w 0 + w 1 = 1 := by have := hw.2; simpa [Fin.sum_univ_two] using this
    have hw1 := hw.1 1
    have hmono : w 1 * (1 - w 1) ≤ b * (1 - b) := by nlinarith
    have h0 : w 0 = 1 - w 1 := by linarith
    rw [h0]
    have hΔ : 0 ≤ (μ₁ - μ₂) ^ 2 := sq_nonneg _
    nlinarith
  · set w : Fin 2 → ℝ := fun i => if i = 0 then 1 - b else b with hwdef
    have e0 : w 0 = 1 - b := by simp [hwdef]
    have e1 : w 1 = b := by simp [hwdef]
    have hw : IsAllocG w := by
      refine ⟨fun i => ?_, by rw [Fin.sum_univ_two, e0, e1]; ring⟩
      show 0 ≤ (if i = 0 then 1 - b else b)
      split_ifs <;> linarith
    refine ⟨w, hw, ?_, ?_⟩
    · rw [two_arm_sac μ₁ μ₂ hμ w hw, e1]
    · rw [jtrue2_eq μ₁ μ₂ hμ.le w hw, e0, e1]; ring

/-- **The certificate pair of the duality, on two arms.**  The frozen certificate `c = (Δ²/2, 0)`
and one true alternative (arm two raised to `μ₁`) with weight `2/Δ²` cover the margins, so
`frontier_upper` gives `Jt(w) ≤ s(w) Δ²/2`: the slope of the exact frontier at `0`. -/
theorem two_arm_certificate (hμ : μ₂ < μ₁) (w : Fin 2 → ℝ) (hw : IsAllocG w) :
    jtrue2 μ₁ μ₂ w * (2 / (μ₁ - μ₂) ^ 2)
      ≤ sac (jproxy2 μ₁ μ₂) ((μ₁ - μ₂) ^ 2 / 2) w := by
  have hΔ : 0 < (μ₁ - μ₂) ^ 2 := by
    have h : 0 < μ₁ - μ₂ := by linarith
    positivity
  set c : Fin 2 → ℝ := fun e => if e = 0 then (μ₁ - μ₂) ^ 2 / 2 else 0 with hcdef
  set L : Unit → Fin 2 → ℝ := fun _ e => if e = 0 then 0 else (μ₁ - μ₂) ^ 2 / 2 with hLdef
  have c0 : c 0 = (μ₁ - μ₂) ^ 2 / 2 := by simp [hcdef]
  have c1 : c 1 = 0 := by simp [hcdef]
  have L0 : ∀ j, L j 0 = 0 := fun j => by simp [hLdef]
  have L1 : ∀ j, L j 1 = (μ₁ - μ₂) ^ 2 / 2 := fun j => by simp [hLdef]
  have hc : ∀ w, IsAllocG w → jproxy2 μ₁ μ₂ w ≤ ∑ e, w e * c e := by
    intro w hw
    rw [jproxy2_eq μ₁ μ₂ hμ.le w hw, Fin.sum_univ_two, c0, c1]
    apply le_of_eq; ring
  have hL : ∀ j w, IsAllocG w → jtrue2 μ₁ μ₂ w ≤ ∑ e, w e * L j e := by
    intro j w hw
    rw [jtrue2_eq μ₁ μ₂ hμ.le w hw, Fin.sum_univ_two, L0 j, L1 j]
    have hsum : w 0 + w 1 = 1 := by have := hw.2; simpa [Fin.sum_univ_two] using this
    have hw1 := hw.1 1
    have hw0 : w 0 ≤ 1 := by have := hw.1 1; linarith
    have : w 0 * w 1 * (μ₁ - μ₂) ^ 2 ≤ 1 * w 1 * (μ₁ - μ₂) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw0 hw1) hΔ.le
    nlinarith
  have hcover : ∀ e, ∑ j : Unit, (fun _ => 2 / (μ₁ - μ₂) ^ 2) j * L j e
      ≤ margin c ((μ₁ - μ₂) ^ 2 / 2) e := by
    intro e
    unfold margin
    by_cases he : e = 0
    · subst he
      rw [c0, div_self (by positivity)]
      simp [L0]
    · have he1 : e = 1 := by omega
      subst he1
      rw [c1]
      simp only [L1]
      have key : 2 / (μ₁ - μ₂) ^ 2 * ((μ₁ - μ₂) ^ 2 / 2) = 1 := by
        rw [div_mul_div_comm, mul_comm (2:ℝ) ((μ₁ - μ₂) ^ 2),
          div_self (mul_ne_zero hΔ.ne' two_ne_zero)]
      simp only [Finset.univ_unique, Finset.sum_singleton, zero_div, sub_zero]
      rw [key]
  have h := frontier_upper (jproxy2 μ₁ μ₂) (jtrue2 μ₁ μ₂) ((μ₁ - μ₂) ^ 2 / 2) (by positivity)
    c hc L hL (fun _ => 2 / (μ₁ - μ₂) ^ 2) (fun _ => by positivity) hcover w hw
  simpa using h

end TwoArm

#print axioms event_info
#print axioms budget_law
#print axioms budget_law_multi
#print axioms no_threshold
#print axioms linear_repair
#print axioms jtrue2_eq
#print axioms jproxy2_eq
#print axioms two_arm_starvation
#print axioms two_arm_frontier
#print axioms two_arm_certificate

end CIGAMF.P13.PaperARepairLaw
