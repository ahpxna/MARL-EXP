import «LeanPaperA7FreeAccumV1»
import «LeanPaperA7DirectLowerV1»
import «LeanPaperA7SqrtLipV1»

/-!
# Paper A7: the direct lower bound on the stopping statistic, without a box

`LeanPaperA7DirectLowerV1.direct_lower_bound` needs every alternative in a box (the raw-mean
perturbation `|(theta-l)^2 - (mu-l)^2| <= r(4B+r)` and the ridge loss `a(2B+r)^2` are
per-alternative bounds).  With the paper's unbounded alternative set the two losses are
handled differently, and both vanish relative to `t`:

* the RAW-MEAN perturbation, by Minkowski in the weights `N_e/sigma_e^2`
  (`energy_perturb`): `E(mu_hat, l) >= t J - R sqrt(2 t U)` for EVERY alternative, where
  `R^2 = sum_e N_e (mu_hat_e - theta_e)^2 / sigma_e^2`;
* the RIDGE, multiplicatively (`ridge_ge`): `N^2/(a+N) >= (1 - a/N_min) N`;
* on the good event the radius is logarithmic (`R_sq_le`): `R^2 <= 2 (1 + a/N_min) b`.

`direct_lower_free` then gives, with `c = 1 - a/N_min` and `Acc` the window accumulation,

    Zlo / t  >=  c ((1 - eps) Acc - sqrt(2 (1 + a/N_min) b) sqrt(2U) / sqrt t) - zeta.

As in `LeanPaperA7DirectLowerV1`, `hsolver` is the named solver contract; for the exact
infimum it holds with `zeta = 0`.
-/

namespace CIGAMF.P13.PaperA7DirectFree

open Finset
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7Accumulation
open CIGAMF.P13.PaperACertificatePerturbation CIGAMF.P13.PaperA7Stream
open CIGAMF.P13.PaperA7DirectLower CIGAMF.P13.PaperA7FreeAccum CIGAMF.P13.PaperA7SqrtLip

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
/-- The ridge statistic dominates the plain energy, multiplicatively. -/
theorem ridge_ge (a : ℝ) (ha : 0 < a) (σ N μh l : E → ℝ) (hσ : ∀ e, σ e ≠ 0) (Nmin : ℝ)
    (hNmin : 0 < Nmin) (hN : ∀ e, Nmin ≤ N e) :
    (1 - a / Nmin) * linearEnergy N (fun e => σ e ^ 2) μh l ≤ PaperA7Stream.Qstat a σ N μh l := by
  unfold linearEnergy PaperA7Stream.Qstat
  rw [mul_sum]
  refine sum_le_sum fun e _ => ?_
  have hNe : 0 < N e := lt_of_lt_of_le hNmin (hN e)
  have hs : 0 < σ e ^ 2 := by have := hσ e; positivity
  have hX : 0 ≤ (μh e - l e) ^ 2 := sq_nonneg _
  have hfac : (1 - a / Nmin) * N e ≤ N e ^ 2 / (a + N e) := by
    rw [le_div_iff₀ (by linarith)]
    have h1 : a / (a + N e) ≤ a / Nmin :=
      div_le_div_of_nonneg_left ha.le hNmin (by linarith [hN e])
    have h2 : N e / (a + N e) = 1 - a / (a + N e) := by field_simp; ring
    have h3 : 1 - a / Nmin ≤ N e / (a + N e) := by linarith
    have := mul_le_mul_of_nonneg_left h3 hNe.le
    calc (1 - a / Nmin) * N e * (a + N e) = N e * (1 - a / Nmin) * (a + N e) := by ring
      _ ≤ N e * (N e / (a + N e)) * (a + N e) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = N e ^ 2 := by field_simp
  calc (1 - a / Nmin) * (N e * (μh e - l e) ^ 2 / (2 * σ e ^ 2))
      = ((1 - a / Nmin) * N e) * (μh e - l e) ^ 2 / (2 * σ e ^ 2) := by ring
    _ ≤ (N e ^ 2 / (a + N e)) * (μh e - l e) ^ 2 / (2 * σ e ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hfac hX
    _ = N e ^ 2 * (μh e - l e) ^ 2 / (2 * (a + N e) * σ e ^ 2) := by
        field_simp

omit [DecidableEq E] in
theorem two_energy_eq (N σ x l : E → ℝ) (hσ : ∀ e, σ e ≠ 0) :
    2 * linearEnergy N (fun e => σ e ^ 2) x l = ∑ e, (N e / σ e ^ 2) * (x e - l e) ^ 2 := by
  unfold linearEnergy
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  have := hσ e
  field_simp

/-- **The raw-mean perturbation, for every alternative.** -/
theorem energy_perturb (Alt : Set (E → ℝ)) (N σ θ μh l : E → ℝ) (hl : l ∈ Alt) (t : ℝ)
    (ht : 0 < t) (hN : ∀ e, 0 ≤ N e) (hσ : ∀ e, σ e ≠ 0) (U : ℝ)
    (hU : Jval (sc σ '' Alt) (fun e => N e / t) (sc σ θ) ≤ U) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : Real.sqrt (∑ e, (N e / σ e ^ 2) * (θ e - μh e) ^ 2) ≤ R) :
    t * Jval (sc σ '' Alt) (fun e => N e / t) (sc σ θ) - R * Real.sqrt (2 * t * U)
      ≤ linearEnergy N (fun e => σ e ^ 2) μh l := by
  set J := Jval (sc σ '' Alt) (fun e => N e / t) (sc σ θ) with hJ
  have hwN : ∀ e, 0 ≤ N e / σ e ^ 2 := fun e => div_nonneg (hN e) (sq_nonneg _)
  have hJ0 : 0 ≤ J := Jval_nonneg (sc σ '' Alt) ⟨sc σ l, l, hl, rfl⟩ _ _
    fun e => div_nonneg (hN e) ht.le
  -- the true-world energy is at least t J
  have hEθ : t * J ≤ linearEnergy N (fun e => σ e ^ 2) θ l := by
    rw [linearEnergy_eq_pen N σ θ l t ht hσ]
    apply mul_le_mul_of_nonneg_left _ ht.le
    exact csInf_le (Jval_bddBelow _ _ _ fun e => div_nonneg (hN e) ht.le)
      ⟨sc σ l, ⟨l, hl, rfl⟩, rfl⟩
  -- Minkowski in the weights N/sigma^2
  have hmink := sqrt_wsum_add_le (fun e => N e / σ e ^ 2) (fun e => μh e - l e)
    (fun e => θ e - μh e) hwN
  have heq : ∀ e, (μh e - l e) + (θ e - μh e) = θ e - l e := fun e => by ring
  simp only [heq] at hmink
  rw [← two_energy_eq N σ θ l hσ, ← two_energy_eq N σ μh l hσ] at hmink
  set Eθ := linearEnergy N (fun e => σ e ^ 2) θ l
  set Eμ := linearEnergy N (fun e => σ e ^ 2) μh l
  have hEμ0 : 0 ≤ Eμ := by
    unfold Eμ linearEnergy
    exact sum_nonneg fun e _ => div_nonneg (mul_nonneg (hN e) (sq_nonneg _)) (by positivity)
  have hs1 : Real.sqrt (2 * (t * J)) ≤ Real.sqrt (2 * Eθ) := Real.sqrt_le_sqrt (by linarith)
  have hd : Real.sqrt (2 * (t * J)) ≤ Real.sqrt (2 * Eμ) + R := by linarith
  set s := Real.sqrt (2 * (t * J))
  set p := Real.sqrt (2 * Eμ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hss : s ^ 2 = 2 * (t * J) := Real.sq_sqrt (by positivity)
  have hpp : p ^ 2 = 2 * Eμ := Real.sq_sqrt (by linarith)
  have hmain : t * J - R * s ≤ Eμ := by
    rcases le_or_gt R s with hRs | hRs
    · have h1 : s - R ≤ p := by linarith
      have h2 : (s - R) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      nlinarith
    · nlinarith
  have hsU : s ≤ Real.sqrt (2 * t * U) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsU hR0]

omit [DecidableEq E] in
/-- **On the good event the weighted radius is logarithmic.** -/
theorem R_sq_le (a : ℝ) (ha : 0 < a) (σ N μh θ : E → ℝ) (hσ : ∀ e, σ e ≠ 0) (Nmin : ℝ)
    (hNmin : 0 < Nmin) (hN : ∀ e, Nmin ≤ N e) (b : ℝ)
    (hgood : PaperA7Stream.Qstat a σ N μh θ ≤ b) :
    ∑ e, (N e / σ e ^ 2) * (θ e - μh e) ^ 2 ≤ 2 * (1 + a / Nmin) * b := by
  unfold PaperA7Stream.Qstat at hgood
  have hterm : ∀ e, (N e / σ e ^ 2) * (θ e - μh e) ^ 2
      ≤ 2 * (1 + a / Nmin) * (N e ^ 2 * (μh e - θ e) ^ 2 / (2 * (a + N e) * σ e ^ 2)) := by
    intro e
    have hNe : 0 < N e := lt_of_lt_of_le hNmin (hN e)
    have hs : 0 < σ e ^ 2 := by have := hσ e; positivity
    have hsq : (θ e - μh e) ^ 2 = (μh e - θ e) ^ 2 := by ring
    rw [hsq]
    set X := (μh e - θ e) ^ 2
    have hX : 0 ≤ X := sq_nonneg _
    have hratio : (a + N e) / N e ≤ 1 + a / Nmin := by
      rw [add_div, div_self hNe.ne', add_comm (1 : ℝ)]
      have : a / N e ≤ a / Nmin := div_le_div_of_nonneg_left ha.le hNmin (hN e)
      linarith
    have heq : 2 * (1 + a / Nmin) * (N e ^ 2 * X / (2 * (a + N e) * σ e ^ 2))
        = (1 + a / Nmin) * (N e / (a + N e)) * (N e * X / σ e ^ 2) := by
      field_simp
    rw [heq]
    have hge : 1 ≤ (1 + a / Nmin) * (N e / (a + N e)) := by
      have hq : (a + N e) / N e * (N e / (a + N e)) = 1 := by field_simp
      calc (1 : ℝ) = (a + N e) / N e * (N e / (a + N e)) := hq.symm
        _ ≤ (1 + a / Nmin) * (N e / (a + N e)) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)
    have hY : 0 ≤ N e * X / σ e ^ 2 := by positivity
    calc N e / σ e ^ 2 * X = 1 * (N e * X / σ e ^ 2) := by ring
      _ ≤ (1 + a / Nmin) * (N e / (a + N e)) * (N e * X / σ e ^ 2) :=
          mul_le_mul_of_nonneg_right hge hY
  calc ∑ e, (N e / σ e ^ 2) * (θ e - μh e) ^ 2
      ≤ ∑ e, 2 * (1 + a / Nmin) * (N e ^ 2 * (μh e - θ e) ^ 2 / (2 * (a + N e) * σ e ^ 2)) :=
        sum_le_sum fun e _ => hterm e
    _ = 2 * (1 + a / Nmin) * ∑ e, N e ^ 2 * (μh e - θ e) ^ 2 / (2 * (a + N e) * σ e ^ 2) := by
        rw [mul_sum]
    _ ≤ 2 * (1 + a / Nmin) * b := by
        apply mul_le_mul_of_nonneg_left hgood (by positivity)

/-- **The box-free direct lower bound.** -/
theorem direct_lower_free (a : ℝ) (ha : 0 < a) (Alt : Set (E → ℝ)) (hne : Alt.Nonempty)
    (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) (θ μh : E → ℝ)
    (Γ : ℝ) (n t : ℕ) (hnt : n ≤ t) (ht : 0 < t)
    (w : ℕ → E → ℝ) (hw : ∀ s, IsAlloc (w s)) (ρ : ℕ → ℝ) (hρ : ∀ s, 0 ≤ ρ s ∧ ρ s ≤ 1)
    (u : E → ℝ) (hu : IsAlloc u) (η : ℕ → ℝ)
    (hgood : ∀ s, n ≤ s → s < t → Γ - η s ≤ Jval (sc σ '' Alt) (w s) (sc σ θ))
    (N : E → ℝ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (htrack : ∀ e, (1 - ε) * avgTarget w ρ u t e ≤ N e / t)
    (Nmin : ℝ) (hNmin : a ≤ Nmin) (hN : ∀ e, Nmin ≤ N e)
    (U : ℝ) (hU : Jval (sc σ '' Alt) (fun e => N e / t) (sc σ θ) ≤ U)
    (b : ℝ) (hb : 0 ≤ b) (hconf : PaperA7Stream.Qstat a σ N μh θ ≤ b)
    (Zlo ζ : ℝ) (hsolver : sInf ((fun l => PaperA7Stream.Qstat a σ N μh l) '' Alt) - t * ζ ≤ Zlo) :
    (1 - a / Nmin) * ((1 - ε) * ((1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s))
        - Real.sqrt (2 * (1 + a / Nmin) * b) * Real.sqrt (2 * U) / Real.sqrt t) - ζ
      ≤ Zlo / t := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hNmin0 : 0 < Nmin := lt_of_lt_of_le ha hNmin
  have hσ0 : ∀ e, σ e ≠ 0 := fun e => (hσ e).ne'
  have hN0 : ∀ e, 0 ≤ N e := fun e => le_trans hNmin0.le (hN e)
  have hc : 0 ≤ 1 - a / Nmin := by
    have : a / Nmin ≤ 1 := (div_le_one hNmin0).mpr hNmin
    linarith
  set J := Jval (sc σ '' Alt) (fun e => N e / t) (sc σ θ) with hJ
  set R := Real.sqrt (2 * (1 + a / Nmin) * b) with hRdef
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRle : Real.sqrt (∑ e, (N e / σ e ^ 2) * (θ e - μh e) ^ 2) ≤ R :=
    Real.sqrt_le_sqrt (R_sq_le a ha σ N μh θ hσ0 Nmin hNmin0 hN b hconf)
  -- every alternative: ridge >= c * plain energy >= c (t J - R sqrt(2 t U))
  have hall : ∀ l ∈ Alt, (1 - a / Nmin) * ((t : ℝ) * J - R * Real.sqrt (2 * t * U))
      ≤ PaperA7Stream.Qstat a σ N μh l := by
    intro l hl
    have h1 := energy_perturb Alt N σ θ μh l hl t htR hN0 hσ0 U hU R hR0 hRle
    have h2 := ridge_ge a ha σ N μh l hσ0 Nmin hNmin0 hN
    exact le_trans (mul_le_mul_of_nonneg_left h1 hc) h2
  have hinf : (1 - a / Nmin) * ((t : ℝ) * J - R * Real.sqrt (2 * t * U))
      ≤ sInf ((fun l => PaperA7Stream.Qstat a σ N μh l) '' Alt) := by
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨l, hl, rfl⟩
    exact hall l hl
  -- the accumulation
  have hacc := accumulation_window_free (sc σ '' Alt) (hne.image _) (sc σ θ) Γ n t hnt ht w hw
    ρ hρ u hu η hgood N ε hε0 hε1 htrack
  -- divide by t
  have hsq : Real.sqrt (2 * t * U) / t = Real.sqrt (2 * U) / Real.sqrt t := by
    have hst : Real.sqrt (t : ℝ) ≠ 0 := (Real.sqrt_pos.mpr htR).ne'
    rw [show (2 * (t : ℝ) * U) = t * (2 * U) by ring, Real.sqrt_mul htR.le, div_eq_iff htR.ne']
    field_simp
    rw [Real.sq_sqrt htR.le]
    ring
  have hZ : (1 - a / Nmin) * (J - R * (Real.sqrt (2 * U) / Real.sqrt t)) - ζ ≤ Zlo / t := by
    rw [le_div_iff₀ htR]
    have : (1 - a / Nmin) * (J - R * (Real.sqrt (2 * U) / Real.sqrt t)) * t
        = (1 - a / Nmin) * ((t : ℝ) * J - R * Real.sqrt (2 * t * U)) := by
      rw [← hsq]; field_simp
    nlinarith
  have hmono : (1 - ε) * ((1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s))
      - R * Real.sqrt (2 * U) / Real.sqrt t ≤ J - R * (Real.sqrt (2 * U) / Real.sqrt t) := by
    rw [mul_div_assoc]; linarith
  calc (1 - a / Nmin) * ((1 - ε) * ((1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s))
        - R * Real.sqrt (2 * U) / Real.sqrt t) - ζ
      ≤ (1 - a / Nmin) * (J - R * (Real.sqrt (2 * U) / Real.sqrt t)) - ζ := by
        have := mul_le_mul_of_nonneg_left hmono hc
        linarith
    _ ≤ Zlo / t := hZ

#print axioms ridge_ge
#print axioms energy_perturb
#print axioms R_sq_le
#print axioms direct_lower_free

end CIGAMF.P13.PaperA7DirectFree
