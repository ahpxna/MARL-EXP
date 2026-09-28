import «LeanPaperACertificatePerturbationV1»
import «LeanPaperA7AccumulationV1»

/-!
# Paper A7: a direct lower bound on the statistic the stopping rule reads

Blueprint 02, section 6.  The stopping rule of `scripts/EXP_paperA7_learner.py` fires when a
CERTIFIED LOWER value `Zlo` of the ridge statistic

    Zridge(T) = inf_{lambda in Alt_T} Qstat(a, sigma, N, mu_hat, lambda),
    Qstat = sum_e N_e^2 (mu_hat_e - lambda_e)^2 / (2 (a + N_e) sigma_e^2)

exceeds the threshold.  `direct_lower_bound` bounds `Zlo_t / t` below by the information the
counts have accumulated, with every loss explicit:

    Zlo_t / t >= (1/t) sum_{s in [n,t)} (1 - rho_s)(Gamma - eta_s)      (accumulation)
               - 2 B'^2 c / t                                          (tracking, B' = B/sqrt vmin)
               - r (4B + r) / (2 vmin) - a K (2B + r)^2 / (2 vmin t)   (raw mean and ridge a)
               - zeta                                                  (solver gap)

It is assembled from proved pieces: `accumulation_window` (in unit-variance coordinates `sc`),
`energy_ge_Jval` (the variance-weighted energy is `t` times the unit-variance game at the design
`N / t`), `sInf_Qstat_ge` and `perturbationCost_div_le`.

Named inputs, all stated as hypotheses of the theorem and none carrying its conclusion:
* `hgood` -- the per-round information of the designs on the window, in unit-variance
  coordinates (produced by `oracle_perturbation`);
* `hrad` -- the estimate's radius (the confidence event);
* `htrack` -- the tracking discrepancy (`LeanPaperA7WarmTrackV1.warm_htrack`);
* `hsolver` -- the SOLVER CONTRACT `inf Qstat - t zeta <= Zlo`.  Weak duality alone gives only
  `Zlo <= inf Qstat` (soundness); the lower direction is an approximation guarantee of the
  numerical inner solver that Lean cannot certify for the Python code.  It is kept as an
  explicit `zeta`, and the rate obtained is only as good as `zeta` is small.
-/

namespace CIGAMF.P13.PaperA7DirectLower

open Finset
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7Accumulation
open CIGAMF.P13.PaperACertificatePerturbation CIGAMF.P13.PaperA7Stream

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Unit-variance coordinates. -/
noncomputable def sc (σ : E → ℝ) (x : E → ℝ) : E → ℝ := fun e => x e / σ e

omit [DecidableEq E] in
theorem linearEnergy_eq_pen (N σ θ l : E → ℝ) (t : ℝ) (ht : 0 < t) (hσ : ∀ e, σ e ≠ 0) :
    linearEnergy N (fun e => σ e ^ 2) θ l = t * pen (fun e => N e / t) (sc σ θ) (sc σ l) := by
  unfold linearEnergy pen sc
  rw [Finset.sum_div, Finset.mul_sum]
  refine sum_congr rfl fun e _ => ?_
  have := hσ e
  field_simp
  try ring

/-- **The variance-weighted energy dominates `t` times the unit-variance game.** -/
theorem energy_ge_Jval (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (N σ θ : E → ℝ) (t : ℝ)
    (ht : 0 < t) (hN : ∀ e, 0 ≤ N e) (hσ : ∀ e, σ e ≠ 0) :
    t * Jval (sc σ '' Alt) (fun e => N e / t) (sc σ θ)
      ≤ sInf ((fun l => linearEnergy N (fun e => σ e ^ 2) θ l) '' Alt) := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨l, hl, rfl⟩
  show t * Jval (sc σ '' Alt) (fun e => N e / t) (sc σ θ)
    ≤ linearEnergy N (fun e => σ e ^ 2) θ l
  rw [linearEnergy_eq_pen N σ θ l t ht hσ]
  apply mul_le_mul_of_nonneg_left _ ht.le
  exact csInf_le (Jval_bddBelow _ _ _ fun e => div_nonneg (hN e) ht.le)
    ⟨sc σ l, ⟨l, hl, rfl⟩, rfl⟩

omit [DecidableEq E] in
/-- The box in unit-variance coordinates. -/
theorem sc_inBox (B vmin : ℝ) (hvmin : 0 < vmin) (σ : E → ℝ) (hσpos : ∀ e, 0 < σ e)
    (hvar : ∀ e, vmin ≤ σ e ^ 2) (x : E → ℝ) (hx : InBox B x) :
    InBox (B / Real.sqrt vmin) (sc σ x) := by
  intro e
  unfold sc
  rw [abs_div, abs_of_pos (hσpos e)]
  have hs : Real.sqrt vmin ≤ σ e := by
    rw [← Real.sqrt_sq (hσpos e).le]
    exact Real.sqrt_le_sqrt (hvar e)
  have hsv : 0 < Real.sqrt vmin := Real.sqrt_pos.mpr hvmin
  rw [div_le_div_iff₀ (hσpos e) hsv]
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hx e)
  calc |x e| * Real.sqrt vmin ≤ B * Real.sqrt vmin := mul_le_mul_of_nonneg_right (hx e) hsv.le
    _ ≤ B * σ e := mul_le_mul_of_nonneg_left hs hB

omit [DecidableEq E] in
/-- The radius in unit-variance coordinates. -/
theorem sc_radius (vmin : ℝ) (hvmin : 0 < vmin) (σ : E → ℝ) (hσpos : ∀ e, 0 < σ e)
    (hvar : ∀ e, vmin ≤ σ e ^ 2) (x y : E → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hxy : ∀ e, |x e - y e| ≤ r) : ∀ e, |sc σ x e - sc σ y e| ≤ r / Real.sqrt vmin := by
  intro e
  have hxy' : InBox r (fun e => x e - y e) := hxy
  have := sc_inBox r vmin hvmin σ hσpos hvar _ hxy' e
  unfold sc at this ⊢
  rw [← sub_div]
  exact this

/-- **The direct lower bound on the certified statistic.** -/
theorem direct_lower_bound (B a vmin : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (hvmin : 0 < vmin)
    (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (hbox : ∀ l ∈ Alt, InBox B l)
    (σ : E → ℝ) (hσpos : ∀ e, 0 < σ e) (hvar : ∀ e, vmin ≤ σ e ^ 2)
    (θ μh : E → ℝ) (hθ : InBox B θ) (r : ℝ) (hr : 0 ≤ r) (hrad : ∀ e, |μh e - θ e| ≤ r)
    (Γ : ℝ) (n t : ℕ) (hnt : n ≤ t) (ht : 0 < t)
    (w : ℕ → E → ℝ) (hw : ∀ s, IsAlloc (w s)) (ρ : ℕ → ℝ) (hρ : ∀ s, 0 ≤ ρ s ∧ ρ s ≤ 1)
    (u : E → ℝ) (hu : IsAlloc u) (η : ℕ → ℝ)
    (hgood : ∀ s, n ≤ s → s < t → Γ - η s ≤ Jval (sc σ '' Alt) (w s) (sc σ θ))
    (N : E → ℝ) (hN : ∀ e, 0 ≤ N e) (hNsum : ∑ e, N e = t) (c : ℝ)
    (htrack : ∑ e, |N e / t - avgTarget w ρ u t e| ≤ c / t)
    (Zlo ζ : ℝ) (hsolver : sInf ((fun l => Qstat a σ N μh l) '' Alt) - t * ζ ≤ Zlo) :
    (1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s)
        - 2 * (B / Real.sqrt vmin) ^ 2 * (c / t)
        - (r * (4 * B + r) / (2 * vmin)
            + a * (Fintype.card E : ℝ) * (2 * B + r) ^ 2 / (2 * vmin * t))
        - ζ
      ≤ Zlo / t := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hσ0 : ∀ e, σ e ≠ 0 := fun e => (hσpos e).ne'
  have hB' : 0 ≤ B / Real.sqrt vmin := div_nonneg hB (Real.sqrt_nonneg _)
  have hboxS : ∀ l ∈ sc σ '' Alt, InBox (B / Real.sqrt vmin) l := by
    rintro _ ⟨l, hl, rfl⟩
    exact sc_inBox B vmin hvmin σ hσpos hvar l (hbox l hl)
  have hacc := accumulation_window (B / Real.sqrt vmin) hB' (sc σ '' Alt) (hne.image _) hboxS
    (sc σ θ) (sc_inBox B vmin hvmin σ hσpos hvar θ hθ) Γ n t hnt ht w hw ρ hρ u hu η hgood
    N hN c htrack
  have hE := energy_ge_Jval Alt hne N σ θ t htR hN hσ0
  have hQ := sInf_Qstat_ge a B r N σ μh θ Alt hne ha hB hr hN hσ0 hθ hbox hrad
  have hP := perturbationCost_div_le a B r vmin t N (fun e => σ e ^ 2) ha.le hB hr hvmin htR hN
    hvar hNsum
  set J := Jval (sc σ '' Alt) (fun e => N e / t) (sc σ θ) with hJ
  set P := perturbationCost a B r N (fun e => σ e ^ 2) with hPdef
  have h1 : (t : ℝ) * J - P - t * ζ ≤ Zlo := by linarith
  have h2 : (J - P / t - ζ) * t = t * J - P - t * ζ := by
    field_simp
  calc (1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s)
        - 2 * (B / Real.sqrt vmin) ^ 2 * (c / t)
        - (r * (4 * B + r) / (2 * vmin)
            + a * (Fintype.card E : ℝ) * (2 * B + r) ^ 2 / (2 * vmin * t))
        - ζ
      ≤ J - P / t - ζ := by linarith
    _ ≤ Zlo / t := by rw [le_div_iff₀ htR, h2]; exact h1

#print axioms linearEnergy_eq_pen
#print axioms energy_ge_Jval
#print axioms sc_inBox
#print axioms direct_lower_bound

end CIGAMF.P13.PaperA7DirectLower
