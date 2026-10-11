import «LeanPaperARepairLawV1»

/-!
# Paper A: the budget classes, nested, and why the expected sacrifice is not one of them

The budget law (`LeanPaperARepairLawV1.budget_law`) is proved for the class `Π_b^exp`: the
policy's *expected-count design* `w̄ = E N / E|N|` meets `s(w̄) ≤ b`. This module places the
two pathwise classes inside it. Here `s(w) = 1 - J_f(w)/Γ` and
`J_f(w) = inf_{λ ∈ L_f} Σ_q w_q KL_q(θ,λ)` is the frozen surrogate game on the same channel.

**The classes.** A count vector `N` meets the budget when, against every frozen alternative,
`(1-b) Γ |N| ≤ Σ_q N_q KL_q(θ,λ)`. This is the homogeneous form of `s(N/|N|) ≤ b` and needs no
division when `|N| = 0`.
* `PrefixClass`: almost every history meets the budget at every prefix.
* `TerminalClass`: almost every history meets the budget at the horizon.
* `EventualClass t₀`: almost every history whose informative total reaches `t₀` meets it.

**What is proved.**
* `prefix_terminal`: `Π^prefix ⊆ Π^terminal`.
* `terminal_expected`: `Π^terminal ⊆ Π^exp`.
  - `J_f` is an infimum of linear forms.
  - The expected design is the `|N|`-weighted mean of the realised designs.
  - So `J_f(w̄) ≥ (1-b)Γ`.
* `terminal_budget_law`: every δ-correct policy of the terminal class pays
  `E|N| · R ≥ (1-δ) log(1/δ) - log 2`.
* `eventual_expected`, `eventual_budget_law`: a policy of `EventualClass t₀` has
  `s(w̄) ≤ b + (1-b) t₀/E|N|`. So it pays `E|N| · R(b + t₀/E|N|) ≥ D_δ`.
  - As `δ → 0`, `E|N| → ∞` and the budget excess vanishes.
  - This is the class that a tracking learner with a fixed design inside the budget belongs
    to: its realised design enters the budget set after a deterministic burn-in.
* `mean_escapes` (two Gaussian arms): the constraint `E[s(N/|N|)] ≤ b` is **not** in the
  hierarchy.
  - Take two realised designs, of lengths `1` and `3`, each with probability `1/2`.
  - Their sacrifices average `1/4`.
  - Their length-weighted mean has sacrifice `3/8`, and carries strictly more true information
    than any design within `b = 1/4`.
  - So the bridge `s(w̄) ≤ b` fails for that constraint.
-/

namespace CIGAMF.P13.PaperAPolicyClasses

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperASacrificeDuality CIGAMF.P13.PaperARepairLaw CIGAMF.P13.PaperAFamilyLower

section Channel

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q]

/-- The informative indicator of a query. -/
noncomputable def infW (C : Channel W Q) (q : Q) : ℝ≥0∞ := if q = C.dummy then 0 else 1

/-- The counts within the first `t` rounds of a history of length `n`. -/
noncomputable def cntUpTo (q : Q) {n : ℕ} (t : ℕ) (ω : Hist Q n) : ℝ≥0∞ :=
  ∑ i : Fin n, if (i : ℕ) < t ∧ (ω i).1 = q then 1 else 0

theorem cntUpTo_n (q : Q) (n : ℕ) (ω : Hist Q n) : cntUpTo q n ω = cntQ q n ω := by
  unfold cntUpTo cntQ
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.is_lt]

/-- **A count vector meets the budget `b`**: against every frozen alternative, its surrogate
information is at least `(1-b)Γ` times its informative total. -/
def MeetsBudget (C : Channel W Q) (θ : W) (Lf : Set W) (Γ b : ℝ) (N : Q → ℝ≥0∞) : Prop :=
  ∀ l ∈ Lf, ENNReal.ofReal ((1 - b) * Γ) * ∑ q, N q * infW C q ≤ ∑ q, N q * klq C θ l q

/-- **The prefix class.** -/
def PrefixClass (C : Channel W Q) (π : Policy Q) (θ : W) (Lf : Set W) (Γ b : ℝ) (n : ℕ) :
    Prop :=
  ∀ t ≤ n, ∀ᵐ ω ∂hist C π θ n, MeetsBudget C θ Lf Γ b (fun q => cntUpTo q t ω)

/-- **The terminal class.** -/
def TerminalClass (C : Channel W Q) (π : Policy Q) (θ : W) (Lf : Set W) (Γ b : ℝ) (n : ℕ) :
    Prop :=
  ∀ᵐ ω ∂hist C π θ n, MeetsBudget C θ Lf Γ b (fun q => cntQ q n ω)

/-- **The eventual class**: the budget binds once the informative total reaches `t₀`. -/
def EventualClass (C : Channel W Q) (π : Policy Q) (θ : W) (Lf : Set W) (Γ b : ℝ) (n : ℕ)
    (t₀ : ℕ) : Prop :=
  ∀ᵐ ω ∂hist C π θ n, (t₀ : ℝ≥0∞) ≤ ∑ q, cntQ q n ω * infW C q →
    MeetsBudget C θ Lf Γ b (fun q => cntQ q n ω)

/-- **Prefix implies terminal.** -/
theorem prefix_terminal (C : Channel W Q) (π : Policy Q) (θ : W) (Lf : Set W) (Γ b : ℝ)
    (n : ℕ) (h : PrefixClass C π θ Lf Γ b n) : TerminalClass C π θ Lf Γ b n := by
  filter_upwards [h n le_rfl] with ω hω
  simpa only [cntUpTo_n] using hω

/-- **Terminal implies eventual**, for every burn-in. -/
theorem terminal_eventual (C : Channel W Q) (π : Policy Q) (θ : W) (Lf : Set W) (Γ b : ℝ)
    (n t₀ : ℕ) (h : TerminalClass C π θ Lf Γ b n) : EventualClass C π θ Lf Γ b n t₀ := by
  filter_upwards [h] with ω hω
  exact fun _ => hω

theorem toReal_infW_sum (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) :
    (∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * infW C q).toReal = etot C π θ n := by
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    unfold infW
    rw [ENNReal.toReal_mul]
    unfold ecnt
    split_ifs <;> simp
  · intro q _
    exact ENNReal.mul_ne_top (lintegral_cntQ_ne_top C π θ q n) (by unfold infW; split_ifs <;> simp)

theorem toReal_kl_sum (C : Channel W Q) (π : Policy Q) (θ l : W) (n : ℕ)
    (hfin : ∀ q, klq C θ l q ≠ ⊤) :
    (∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q).toReal
      = ∑ q, ecnt C π θ n q * (klq C θ l q).toReal := by
  rw [ENNReal.toReal_sum]
  · exact Finset.sum_congr rfl fun q _ => by rw [ENNReal.toReal_mul]; rfl
  · intro q _
    exact ENNReal.mul_ne_top (lintegral_cntQ_ne_top C π θ q n) (hfin q)

theorem lintegral_budget_lhs (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) (r : ℝ≥0∞) :
    ∫⁻ ω, r * ∑ q, cntQ q n ω * infW C q ∂hist C π θ n
      = r * ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * infW C q := by
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun q _ =>
    (measurable_cntQ q n).mul_const _)]
  congr 1
  rw [lintegral_finsetSum _ fun q _ => (measurable_cntQ q n).mul_const _]
  exact Finset.sum_congr rfl fun q _ => lintegral_mul_const _ (measurable_cntQ q n)

theorem lintegral_budget_rhs (C : Channel W Q) (π : Policy Q) (θ l : W) (n : ℕ) :
    ∫⁻ ω, ∑ q, cntQ q n ω * klq C θ l q ∂hist C π θ n
      = ∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q := by
  rw [lintegral_finsetSum _ fun q _ => (measurable_cntQ q n).mul_const _]
  exact Finset.sum_congr rfl fun q _ => lintegral_mul_const _ (measurable_cntQ q n)

/-- **Terminal implies expected**: the expected-count design meets the budget. -/
theorem terminal_expected (C : Channel W Q) (π : Policy Q) (θ : W) (Lf : Set W) [Nonempty Lf]
    (Γ b : ℝ) (n : ℕ) (hΓ : 0 < Γ) (hb : b ≤ 1) (hfin : ∀ l ∈ Lf, ∀ q, klq C θ l q ≠ ⊤)
    (hpos : 0 < etot C π θ n) (h : TerminalClass C π θ Lf Γ b n) :
    (1 - b) * Γ ≤ Jt C θ Lf (ebar C π θ n) ∧ sac (Jt C θ Lf) Γ (ebar C π θ n) ≤ b := by
  have hc : 0 ≤ (1 - b) * Γ := mul_nonneg (by linarith) hΓ.le
  have hper : ∀ l : Lf, (1 - b) * Γ ≤ infoAt C θ l (ebar C π θ n) := by
    intro l
    have hint : ∫⁻ ω, ENNReal.ofReal ((1 - b) * Γ) * ∑ q, cntQ q n ω * infW C q ∂hist C π θ n
        ≤ ∫⁻ ω, ∑ q, cntQ q n ω * klq C θ l q ∂hist C π θ n := by
      refine lintegral_mono_ae ?_
      filter_upwards [h] with ω hω
      exact hω l l.2
    rw [lintegral_budget_lhs, lintegral_budget_rhs] at hint
    have hR : (∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun q _ =>
        ENNReal.mul_ne_top (lintegral_cntQ_ne_top C π θ q n) (hfin l l.2 q)
    have hreal := ENNReal.toReal_mono hR hint
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, toReal_infW_sum,
      toReal_kl_sum C π θ l n (hfin l l.2), ← etot_mul_infoAt C π θ n l hpos] at hreal
    have := hreal
    nlinarith
  have hJ : (1 - b) * Γ ≤ Jt C θ Lf (ebar C π θ n) := le_ciInf hper
  refine ⟨hJ, ?_⟩
  unfold sac
  have : (1 - b) * Γ / Γ ≤ Jt C θ Lf (ebar C π θ n) / Γ := div_le_div_of_nonneg_right hJ hΓ.le
  rw [mul_div_assoc, div_self hΓ.ne', mul_one] at this
  linarith

/-- **The budget law on the terminal class.** -/
theorem terminal_budget_law (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ : W) (L Lf : Set W)
    [Nonempty L] [Nonempty Lf] (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hθ : 1 - δ ≤ (hist C π θ n).real S) (hL : ∀ l ∈ L, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hfinf : ∀ l ∈ Lf, ∀ q, klq C θ l q ≠ ⊤)
    (hpos : 0 < etot C π θ n) (Γ b R : ℝ) (hΓ : 0 < Γ) (hb : b ≤ 1)
    (hR : ∀ w : Q → ℝ, (∀ q, 0 ≤ w q) → sac (Jt C θ Lf) Γ w ≤ b → Jt C θ L w ≤ R)
    (hT : TerminalClass C π θ Lf Γ b n) :
    (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ etot C π θ n * R :=
  (budget_law C π n θ L S hS δ hδ hδ1 hθ hL hfin hpos (sac (Jt C θ Lf) Γ) b R hR
    (terminal_expected C π θ Lf Γ b n hΓ hb hfinf hpos hT).2).2

/-- **Eventual implies expected, up to the burn-in.** -/
theorem eventual_expected (C : Channel W Q) (π : Policy Q) (θ : W) (Lf : Set W) [Nonempty Lf]
    (Γ b : ℝ) (n t₀ : ℕ) (hΓ : 0 < Γ) (hb : b ≤ 1) (hfin : ∀ l ∈ Lf, ∀ q, klq C θ l q ≠ ⊤)
    (hpos : 0 < etot C π θ n) (h : EventualClass C π θ Lf Γ b n t₀) :
    (1 - b) * Γ * (1 - t₀ / etot C π θ n) ≤ Jt C θ Lf (ebar C π θ n)
      ∧ sac (Jt C θ Lf) Γ (ebar C π θ n) ≤ b + (1 - b) * t₀ / etot C π θ n := by
  have hc : 0 ≤ (1 - b) * Γ := mul_nonneg (by linarith) hΓ.le
  set r := ENNReal.ofReal ((1 - b) * Γ) with hr
  have hper : ∀ l : Lf, (1 - b) * Γ * (1 - t₀ / etot C π θ n) ≤ infoAt C θ l (ebar C π θ n) := by
    intro l
    have hpath : ∀ᵐ ω ∂hist C π θ n, r * ∑ q, cntQ q n ω * infW C q
        ≤ ∑ q, cntQ q n ω * klq C θ l q + r * t₀ := by
      filter_upwards [h] with ω hω
      by_cases ht : (t₀ : ℝ≥0∞) ≤ ∑ q, cntQ q n ω * infW C q
      · exact (hω ht l l.2).trans le_self_add
      · push_neg at ht
        have : r * ∑ q, cntQ q n ω * infW C q ≤ r * t₀ := by gcongr
        exact this.trans le_add_self
    have hint := lintegral_mono_ae hpath
    rw [lintegral_budget_lhs, lintegral_add_right _ measurable_const, lintegral_budget_rhs,
      lintegral_const] at hint
    have := hist_prob C π θ n
    rw [measure_univ, mul_one] at hint
    have hR : (∑ q, (∫⁻ ω, cntQ q n ω ∂hist C π θ n) * klq C θ l q) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun q _ =>
        ENNReal.mul_ne_top (lintegral_cntQ_ne_top C π θ q n) (hfin l l.2 q)
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hR, ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)⟩) hint
    rw [ENNReal.toReal_add hR (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.natCast_ne_top _)), ENNReal.toReal_mul, ENNReal.toReal_mul, hr,
      ENNReal.toReal_ofReal hc, toReal_infW_sum, toReal_kl_sum C π θ l n (hfin l l.2),
      ← etot_mul_infoAt C π θ n l hpos, ENNReal.toReal_natCast] at hreal
    have e : (1 - b) * Γ * (1 - t₀ / etot C π θ n)
        = ((1 - b) * Γ * etot C π θ n - (1 - b) * Γ * t₀) / etot C π θ n := by
      field_simp
    rw [e, div_le_iff₀ hpos]
    linarith
  have hJ := le_ciInf hper
  refine ⟨hJ, ?_⟩
  unfold sac
  have h2 : (1 - b) * Γ * (1 - t₀ / etot C π θ n) / Γ ≤ Jt C θ Lf (ebar C π θ n) / Γ :=
    div_le_div_of_nonneg_right hJ hΓ.le
  have e : (1 - b) * Γ * (1 - t₀ / etot C π θ n) / Γ
      = 1 - (b + (1 - b) * t₀ / etot C π θ n) := by
    field_simp
    ring
  rw [e] at h2
  linarith

/-- **The budget law on the eventual class**, with the budget excess `(1-b) t₀/E|N|`. -/
theorem eventual_budget_law (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ : W) (L Lf : Set W)
    [Nonempty L] [Nonempty Lf] (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hθ : 1 - δ ≤ (hist C π θ n).real S) (hL : ∀ l ∈ L, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hfinf : ∀ l ∈ Lf, ∀ q, klq C θ l q ≠ ⊤)
    (hpos : 0 < etot C π θ n) (Γ b : ℝ) (t₀ : ℕ) (hΓ : 0 < Γ) (hb : b ≤ 1) (Rf : ℝ → ℝ)
    (hR : ∀ b' : ℝ, ∀ w : Q → ℝ, (∀ q, 0 ≤ w q) → sac (Jt C θ Lf) Γ w ≤ b' → Jt C θ L w ≤ Rf b')
    (hE : EventualClass C π θ Lf Γ b n t₀) :
    (1 - δ) * Real.log (1 / δ) - Real.log 2
      ≤ etot C π θ n * Rf (b + (1 - b) * t₀ / etot C π θ n) :=
  (budget_law C π n θ L S hS δ hδ hδ1 hθ hL hfin hpos (sac (Jt C θ Lf) Γ) _ _
    (hR (b + (1 - b) * t₀ / etot C π θ n))
    (eventual_expected C π θ Lf Γ b n t₀ hΓ hb hfinf hpos hE).2).2

end Channel

/-! ## The expected sacrifice is not a budget class -/

section Escape

variable (μ₁ μ₂ : ℝ)

/-- Two realised designs and their length-weighted mean (lengths `1` and `3`, probability `1/2`
each). -/
def wA : Fin 2 → ℝ := ![1, 0]
noncomputable def wB : Fin 2 → ℝ := ![1 / 2, 1 / 2]
noncomputable def wMean : Fin 2 → ℝ := ![5 / 8, 3 / 8]

theorem wA_alloc : IsAllocG wA := ⟨fun i => by fin_cases i <;> simp [wA], by
  simp [wA, Fin.sum_univ_two]⟩
theorem wB_alloc : IsAllocG wB := ⟨fun i => by fin_cases i <;> simp [wB] <;> norm_num, by
  simp [wB, Fin.sum_univ_two]; norm_num⟩
theorem wMean_alloc : IsAllocG wMean := ⟨fun i => by fin_cases i <;> simp [wMean] <;> norm_num,
  by simp [wMean, Fin.sum_univ_two]; norm_num⟩

/-- **The expected sacrifice escapes the hierarchy.** -/
theorem mean_escapes (hμ : μ₂ < μ₁) :
    (∀ i, wMean i = ((1 / 2) * 1 * wA i + (1 / 2) * 3 * wB i) / ((1 / 2) * 1 + (1 / 2) * 3))
      ∧ (1 / 2) * sac (jproxy2 μ₁ μ₂) ((μ₁ - μ₂) ^ 2 / 2) wA
          + (1 / 2) * sac (jproxy2 μ₁ μ₂) ((μ₁ - μ₂) ^ 2 / 2) wB = 1 / 4
      ∧ sac (jproxy2 μ₁ μ₂) ((μ₁ - μ₂) ^ 2 / 2) wMean = 3 / 8
      ∧ ∀ w, IsAllocG w → sac (jproxy2 μ₁ μ₂) ((μ₁ - μ₂) ^ 2 / 2) w ≤ 1 / 4 →
          jtrue2 μ₁ μ₂ w < jtrue2 μ₁ μ₂ wMean := by
  refine ⟨fun i => by fin_cases i <;> simp [wMean, wA, wB] <;> norm_num, ?_, ?_, ?_⟩
  · rw [two_arm_sac μ₁ μ₂ hμ wA wA_alloc, two_arm_sac μ₁ μ₂ hμ wB wB_alloc]
    simp [wA, wB]; norm_num
  · rw [two_arm_sac μ₁ μ₂ hμ wMean wMean_alloc]; simp [wMean]
  · intro w hw hs
    have hup := (two_arm_frontier μ₁ μ₂ hμ (1 / 4) (by norm_num) (by norm_num)).1 w hw hs
    rw [jtrue2_eq μ₁ μ₂ hμ.le wMean wMean_alloc]
    have hΔ : 0 < (μ₁ - μ₂) ^ 2 := by have : 0 < μ₁ - μ₂ := by linarith
                                      positivity
    simp only [wMean, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at *
    nlinarith

end Escape

#print axioms prefix_terminal
#print axioms terminal_eventual
#print axioms terminal_expected
#print axioms terminal_budget_law
#print axioms eventual_expected
#print axioms eventual_budget_law
#print axioms mean_escapes

end CIGAMF.P13.PaperAPolicyClasses
