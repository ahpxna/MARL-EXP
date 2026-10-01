import «LeanPaperARepairGaussV1»
import «LeanPaperARepairStopV1»

/-!
# Paper A: the repair laws without a positivity hypothesis, and the stopped law satisfied

The laws of `LeanPaperARepairBridgeV1` and `LeanPaperARepairStopV1` take `0 < E|N|`, which
the manuscript does not state. It is not needed. When the expected informative total is zero,
every informative count is zero in expectation and the dummy carries no divergence, so the
change of measure gives `p log(1/δ) - log 2 ≤ 0`, which is the law with a zero right side.

* `event_law0`, `budget_law_alloc0`, `eventual_frontier_law0`: the horizon laws, any channel.
* `frontier_rate_lower0`: the lower rate on any channel, for δ-correct families of the
  eventual class, with positivity derived below `δ < 1/8` (`etot_pos_of_correct`).
* `stopped_budget_law0`: the law at the stopping time, any channel.
* `stopped_law_satisfiable`: on Gaussian cells, the stopped fixed-design learner at a Markov
  horizon, embedded as a stopping policy (`finStop`), meets every hypothesis of the stopped law,
  including the budget, which it meets at `b + (1-b) t₀ / E|N(τ)|` with one `t₀` for all δ.
  `stopped_law_satisfiable_two` instantiates it on two Gaussian arms for every `b ∈ (0, 1/2]`.
-/

namespace CIGAMF.P13.PaperARepairNoPos

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperASacrificeDuality CIGAMF.P13.PaperARepairLaw CIGAMF.P13.PaperAFamilyLower
open CIGAMF.P13.PaperAPolicyClasses CIGAMF.P13.PaperARepairRate CIGAMF.P13.PaperAEndgame
open CIGAMF.P13.PaperARepairBridge CIGAMF.P13.PaperARepairStop CIGAMF.P13.PaperBStoppedLaw
open CIGAMF.P13.PaperARepairGauss CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperABridge
open CIGAMF.P13.PaperABridgeDummy CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7DirectLower

/-! ## 1. The horizon laws, any channel -/

section Channel

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q]

theorem etot_nonneg (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) : 0 ≤ etot C π θ n :=
  Finset.sum_nonneg fun q _ => mul_nonneg (ecnt_nonneg C π θ n q) (by split_ifs <;> norm_num)

/-- With no informative query in expectation, the information against every alternative is
zero. -/
theorem info_zero (C : Channel W Q) (π : Policy Q) (θ : W) (n : ℕ) (h0 : etot C π θ n = 0)
    (l : W) : ∑ q, ecnt C π θ n q * (klq C θ l q).toReal = 0 := by
  unfold etot at h0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ =>
    mul_nonneg (ecnt_nonneg C π θ n q) (by split_ifs <;> norm_num))).mp h0
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q = C.dummy
  · subst hq; rw [klq_dummy]; simp
  · have h := hterm q (Finset.mem_univ q)
    simp only [hq, if_false, mul_one] at h
    rw [h, zero_mul]

/-- **The budget law with an event of probability `p`, without positivity.** -/
theorem event_law0 (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ : W) (L : Set W) [Nonempty L]
    (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ p : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : p ≤ (hist C π θ n).real S) (hL : ∀ l ∈ L, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) :
    p * Real.log (1 / δ) - Real.log 2 ≤ etot C π θ n * Jt C θ L (ebar C π θ n) := by
  rcases (etot_nonneg C π θ n).eq_or_lt with h0 | hpos
  · have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    obtain ⟨⟨l, hl⟩⟩ := ‹Nonempty L›
    have h := event_info C π n θ l S hS δ hδ (hL l hl) (hfin l hl)
    rw [info_zero C π θ n h0.symm l] at h
    rw [← h0, zero_mul]
    have := mul_le_mul_of_nonneg_right hθ hlog
    linarith
  · exact event_law C π n θ L S hS δ p hδ hδ1 hθ hL hfin hpos

/-- **The budget law on the simplex, without positivity.** -/
theorem budget_law_alloc0 (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ : W) (L : Set W)
    [Nonempty L] (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist C π θ n).real S) (hL : ∀ l ∈ L, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤)
    (s : (Q → ℝ) → ℝ) (b R : ℝ) (hR : ∀ w : Q → ℝ, IsAllocG w → s w ≤ b → Jt C θ L w ≤ R)
    (hbud : s (ebar C π θ n) ≤ b) :
    (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ etot C π θ n * R := by
  rcases (etot_nonneg C π θ n).eq_or_lt with h0 | hpos
  · have h := event_law0 C π n θ L S hS δ (1 - δ) hδ hδ1 hθ hL hfin
    rw [← h0, zero_mul] at h ⊢
    exact h
  · exact budget_law_alloc C π n θ L S hS δ hδ hδ1 hθ hL hfin hpos s b R hR hbud

/-- **The eventual-class law against the repair frontier, without positivity.** -/
theorem eventual_frontier_law0 (C : Channel W Q) (π : Policy Q) (n : ℕ) (θ : W) (L Lf : Set W)
    [Nonempty L] [Nonempty Lf] (l₀ : L) (S : Set (Hist Q n)) (hS : MeasurableSet S) (δ p : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : p ≤ (hist C π θ n).real S)
    (hL : ∀ l ∈ L, (hist C π l n).real S ≤ δ)
    (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hfinf : ∀ l ∈ Lf, ∀ q, klq C θ l q ≠ ⊤)
    (Γ b : ℝ) (t₀ : ℕ) (hΓ : 0 < Γ) (hb : b ≤ 1)
    (hE : EventualClass C π θ Lf Γ b n t₀) :
    p * Real.log (1 / δ) - Real.log 2
      ≤ etot C π θ n * Rfront (Jt C θ Lf) (Jt C θ L) Γ (b + (1 - b) * t₀ / etot C π θ n) := by
  rcases (etot_nonneg C π θ n).eq_or_lt with h0 | hpos
  · have h := event_law0 C π n θ L S hS δ p hδ hδ1 hθ hL hfin
    rw [← h0, zero_mul] at h ⊢
    exact h
  · exact eventual_frontier_law C π n θ L Lf l₀ S hS δ p hδ hδ1 hθ hL hfin hfinf hpos Γ b t₀ hΓ
      hb hE

/-- **The lower rate on any channel, without positivity.** Below `δ < 1/8` a correct policy
has a positive expected informative total, so positivity is a consequence. -/
theorem frontier_rate_lower0 (C : Channel W Q) (θ : W) (L Lf : Set W) [Nonempty L]
    [Nonempty Lf] (l₀ : L) (hfin : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤)
    (hfinf : ∀ l ∈ Lf, ∀ q, klq C θ l q ≠ ⊤)
    (Γ b : ℝ) (t₀ : ℕ) (hΓ : 0 < Γ) (hb0 : 0 < b) (hb : b ≤ 1)
    (wstar : Q → ℝ) (hws : IsAllocG wstar) (hopt : Jt C θ Lf wstar = Γ)
    (hRb : 0 < Rfront (Jt C θ Lf) (Jt C θ L) Γ b)
    (π : ℝ → Policy Q) (n : ℝ → ℕ) (S : ∀ δ, Set (Hist Q (n δ)))
    (hS : ∀ δ, MeasurableSet (S δ)) (δ0 : ℝ) (hδ0 : 0 < δ0) (hδ01 : δ0 ≤ 1)
    (hθ : ∀ δ, 0 < δ → δ < δ0 → 1 - δ ≤ (hist C (π δ) θ (n δ)).real (S δ))
    (hL : ∀ δ, 0 < δ → δ < δ0 → ∀ l ∈ L, (hist C (π δ) l (n δ)).real (S δ) ≤ δ)
    (hE : ∀ δ, 0 < δ → δ < δ0 → EventualClass C (π δ) θ Lf Γ b (n δ) t₀) :
    LowerRate (fun δ => etot C (π δ) θ (n δ)) (Rfront (Jt C θ Lf) (Jt C θ L) Γ b) := by
  obtain ⟨⟨l₁, hl₁⟩⟩ := ‹Nonempty L›
  set δ1 := min δ0 (1 / 8) with hδ1
  have hδ1pos : 0 < δ1 := lt_min hδ0 (by norm_num)
  have hlt : ∀ δ, δ < δ1 → δ < δ0 := fun δ h => lt_of_lt_of_le h (min_le_left _ _)
  have hlt8 : ∀ δ, δ < δ1 → δ < 1 / 8 := fun δ h => lt_of_lt_of_le h (min_le_right _ _)
  refine frontier_rate_lower C θ L Lf l₀ hfin hfinf Γ b t₀ hΓ hb0 hb wstar hws hopt hRb π n S hS
    δ1 hδ1pos ((min_le_left _ _).trans hδ01) (fun δ h1 h2 => hθ δ h1 (hlt δ h2))
    (fun δ h1 h2 => hL δ h1 (hlt δ h2)) (fun δ h1 h2 => ?_) (fun δ h1 h2 => hE δ h1 (hlt δ h2))
  have h8 := hlt8 δ h2
  exact etot_pos_of_correct C (π δ) (n δ) θ l₁ (S δ) (hS δ) δ h1 (by linarith)
    (hθ δ h1 (hlt δ h2)) (hL δ h1 (hlt δ h2) l₁ hl₁) (hfin l₁ hl₁) (hD_of_small δ h1 h8)

end Channel

/-! ## 2. The law at the stopping time, any channel -/

section Stopped

variable {W Q A : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem etotSt_nonneg (C : Channel W Q) (S : SPolicy Q A) (θ : W) : 0 ≤ etotSt C S θ :=
  Finset.sum_nonneg fun q _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

theorem infoSt_zero (C : Channel W Q) (S : SPolicy Q A) (θ : W) (h0 : etotSt C S θ = 0)
    (l : W) : ∑ q, (cntSt C S θ q).toReal * (klq C θ l q).toReal = 0 := by
  unfold etotSt at h0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ =>
    mul_nonneg (ENNReal.toReal_nonneg (a := cntSt C S θ q))
      (by split_ifs <;> norm_num))).mp h0
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q = C.dummy
  · subst hq; rw [klq_dummy]; simp
  · have h := hterm q (Finset.mem_univ q)
    simp only [hq, if_false, mul_one] at h
    rw [h, zero_mul]

/-- **The repair law at the stopping time, without positivity.** -/
theorem stopped_budget_law0 (C : Channel W Q) (S : SPolicy Q A) (θ : W) (L : Set W)
    [Nonempty L] (a0 a : A) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstop : ∀ ε : ℝ, 0 < ε → ∃ n,
      (hist C (stoppedPol S C.dummy) θ n).real {x | ¬ fired S n x} ≤ ε)
    (herr : ∀ n, (hist C (stoppedPol S C.dummy) θ n).real
      {x | fired S n x ∧ outT S S.out a0 n x ≠ a} ≤ δ)
    (halt : ∀ l ∈ L, ∀ n, (hist C (stoppedPol S C.dummy) l n).real (stopAns S a0 a n) ≤ δ)
    (hfinKL : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hfin : ∀ q, q ≠ C.dummy → cntSt C S θ q ≠ ⊤)
    (s : (Q → ℝ) → ℝ) (b R : ℝ)
    (hR : ∀ w : Q → ℝ, IsAllocG w → s w ≤ b → Jt C θ L w ≤ R) (hbud : s (ebarSt C S θ) ≤ b) :
    (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ etotSt C S θ * R := by
  rcases (etotSt_nonneg C S θ).eq_or_lt with h0 | hpos
  · obtain ⟨⟨l, hl⟩⟩ := ‹Nonempty L›
    have h2 := stopped_info C S θ l a0 a δ hδ hδ1 hstop herr (halt l hl) (hfinKL l hl) hfin
    rw [infoSt_zero C S θ h0.symm l] at h2
    rw [← h0, zero_mul]
    exact h2
  · exact stopped_budget_law C S θ L a0 a δ hδ hδ1 hstop herr halt hfinKL hfin hpos s b R hR hbud

/-! ### The embedded finite-horizon policy has the counts of the policy it embeds -/

theorem finStop_term (C : Channel W Q) (pol0 : Policy Q) (N : ℕ) (E0 : Set (Hist Q N))
    (hE0 : MeasurableSet E0) (w : W) (q : Q) :
    (cntSt C (finStop pol0 N E0 hE0) w q).toReal * (if q = C.dummy then 0 else 1)
      = ecnt C pol0 w N q * (if q = C.dummy then 0 else 1) := by
  by_cases hq : q = C.dummy
  · simp [hq]
  · unfold ecnt
    rw [finStop_cntSt C pol0 N E0 hE0 w q hq]

theorem finStop_etotSt (C : Channel W Q) (pol0 : Policy Q) (N : ℕ) (E0 : Set (Hist Q N))
    (hE0 : MeasurableSet E0) (w : W) :
    etotSt C (finStop pol0 N E0 hE0) w = etot C pol0 w N :=
  Finset.sum_congr rfl fun q _ => finStop_term C pol0 N E0 hE0 w q

theorem finStop_ebarSt (C : Channel W Q) (pol0 : Policy Q) (N : ℕ) (E0 : Set (Hist Q N))
    (hE0 : MeasurableSet E0) (w : W) :
    ebarSt C (finStop pol0 N E0 hE0) w = ebar C pol0 w N := by
  funext q
  unfold ebarSt ebar
  rw [finStop_term C pol0 N E0 hE0 w q, finStop_etotSt C pol0 N E0 hE0 w]

end Stopped

/-! ## 3. Every hypothesis of the stopped law holds, budget included, on Gaussian cells -/

section Gauss

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans)

/-- **The stopped law is satisfiable, budget included.** The stopped fixed-design learners of
`optimal_upper`, run to their Markov horizons and embedded as stopping policies, stop almost
surely, are correct on their stopped runs, have finite informative counts and a positive
informative total, and their whole-run expected design meets the budget `b + (1-b) t₀/E|N(τ)|`,
with one `t₀` for every `δ`. -/
theorem stopped_law_satisfiable (Tst : Ans) (θ : E → ℝ) (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T)
    (Altf : Set (E → ℝ)) (hAf : Altf.Nonempty) (Γ : ℝ) (hΓ : 0 < Γ) (wstar : E → ℝ)
    (hws : IsAlloc wstar) (hopt : Jval (sc P.σ '' Altf) wstar (sc P.σ θ) = Γ) (b : ℝ)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε)
    (hεR : ε < Rg P Tst θ Altf Γ b) :
    ∃ t₀ : ℕ, ∀ δ : ℝ, 0 < δ → δ < 1 / 8 → ∃ S' : SPolicy (E ⊕ Unit) Bool,
      (∀ ε' : ℝ, 0 < ε' → ∃ n,
        (hist (gC P) (stoppedPol S' (gC P).dummy) (lift θ) n).real {x | ¬ fired S' n x} ≤ ε')
      ∧ (∀ n, (hist (gC P) (stoppedPol S' (gC P).dummy) (lift θ) n).real
          {x | fired S' n x ∧ outT S' S'.out false n x ≠ true} ≤ δ)
      ∧ (∀ l ∈ lift '' P.Alt Tst, ∀ n,
          (hist (gC P) (stoppedPol S' (gC P).dummy) l n).real (stopAns S' false true n) ≤ δ)
      ∧ (∀ q, q ≠ (gC P).dummy → cntSt (gC P) S' (lift θ) q ≠ ⊤)
      ∧ 0 < etotSt (gC P) S' (lift θ)
      ∧ sac (Jt (gC P) (lift θ) (lift '' Altf)) Γ (ebarSt (gC P) S' (lift θ))
          ≤ b + (1 - b) * t₀ / etotSt (gC P) S' (lift θ) := by
  obtain ⟨t₀, π, n, S, hS, hθc, hLc, hE, -⟩ :=
    optimal_upper P Tst θ hwrong Altf hAf Γ hΓ wstar hws hopt b hb0 a ha ε hε hεR
  refine ⟨t₀, fun δ hδ hδ8 => ?_⟩
  have hδ1 : δ < 1 := by linarith
  obtain ⟨h1, h2, h3, h4⟩ := finStop_hyps (gC P) (π δ) (n δ) (lift θ) (lift '' P.Alt Tst)
    (S δ) (hS δ) δ hδ.le (hθc δ hδ hδ1) (hLc δ hδ hδ1)
  obtain ⟨l₁, hl₁⟩ := P.Alt_ne Tst
  have hpos : 0 < etot (gC P) (π δ) (lift θ) (n δ) :=
    etot_pos_of_correct (gC P) (π δ) (n δ) (lift θ) (lift l₁) (S δ) (hS δ) δ hδ hδ1.le
      (hθc δ hδ hδ1) (hLc δ hδ hδ1 _ ⟨l₁, hl₁, rfl⟩) (fun q => klq_gC_ne_top P θ l₁ q)
      (hD_of_small δ hδ hδ8)
  haveI : Nonempty (lift '' Altf) := (hAf.image lift).to_subtype
  have hfinf : ∀ l ∈ lift '' Altf, ∀ q, klq (gC P) (lift θ) l q ≠ ⊤ := by
    rintro _ ⟨l, -, rfl⟩ q
    exact klq_gC_ne_top P θ l q
  have hexp := (eventual_expected (gC P) (π δ) (lift θ) (lift '' Altf) Γ b (n δ) t₀ hΓ hb1
    hfinf hpos (hE δ)).2
  refine ⟨finStop (π δ) (n δ) (S δ) (hS δ), h1, h2, h3, h4, ?_, ?_⟩
  · rw [finStop_etotSt]; exact hpos
  · rw [finStop_ebarSt, finStop_etotSt]; exact hexp

end Gauss

section TwoArms

open CIGAMF.P13.PaperATwoArmRate

/-- **On two Gaussian arms, every hypothesis of the stopped law holds** for every budget
`b ∈ (0, 1/2]`: the frozen surrogate lets only the leader move, the frozen optimum `(1,0)`
attains `Γ = Δ²/2`, and the frontier is positive. -/
theorem stopped_law_satisfiable_two (θ : Fin 2 → ℝ) (hθ : θ 1 < θ 0) (b : ℝ) (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 2) :
    ∃ t₀ : ℕ, ∀ δ : ℝ, 0 < δ → δ < 1 / 8 → ∃ S' : SPolicy (Fin 2 ⊕ Unit) Bool,
      (∀ ε' : ℝ, 0 < ε' → ∃ n,
        (hist (gC twoSpec) (stoppedPol S' (gC twoSpec).dummy) (lift θ) n).real
          {x | ¬ fired S' n x} ≤ ε')
      ∧ (∀ n, (hist (gC twoSpec) (stoppedPol S' (gC twoSpec).dummy) (lift θ) n).real
          {x | fired S' n x ∧ outT S' S'.out false n x ≠ true} ≤ δ)
      ∧ (∀ l ∈ lift '' twoSpec.Alt 0, ∀ n,
          (hist (gC twoSpec) (stoppedPol S' (gC twoSpec).dummy) l n).real
            (stopAns S' false true n) ≤ δ)
      ∧ (∀ q, q ≠ (gC twoSpec).dummy → cntSt (gC twoSpec) S' (lift θ) q ≠ ⊤)
      ∧ 0 < etotSt (gC twoSpec) S' (lift θ)
      ∧ sac (Jt (gC twoSpec) (lift θ) (lift '' altFrozen (θ 1))) ((θ 0 - θ 1) ^ 2 / 2)
          (ebarSt (gC twoSpec) S' (lift θ))
          ≤ b + (1 - b) * t₀ / etotSt (gC twoSpec) S' (lift θ) := by
  obtain ⟨hw, hne, hal, hJ, hΓ, hR⟩ := optimal_satisfiable θ hθ b hb0 hb1
  exact stopped_law_satisfiable twoSpec 0 θ hw (altFrozen (θ 1)) hne _ hΓ (wb 0) hal hJ b hb0
    (by linarith) 1 one_pos _ (half_pos hR) (half_lt_self hR)

end TwoArms

#print axioms event_law0
#print axioms budget_law_alloc0
#print axioms eventual_frontier_law0
#print axioms frontier_rate_lower0
#print axioms stopped_budget_law0
#print axioms stopped_law_satisfiable
#print axioms stopped_law_satisfiable_two

end CIGAMF.P13.PaperARepairNoPos
