import «LeanPaperA7StreamV1»

/-!
Supervisor draft of 2026-09-23, COMPILED on 2026-09-23 after two lemma-name repairs
(`abs_add` does not exist in this Mathlib pin; `abs_sub_le` takes three arguments), with the
`v_min` corollary and the infimum step added.  Axioms {propext, Classical.choice, Quot.sound}.

Concrete deterministic bridge for A7: the implemented Qstat uses effective counts
N^2/(a+N), whereas the information game uses N. Estimate perturbation and the exact loss
from this regularisation are bounded here, for EVERY alternative lambda in the model box.
No good-event probability, tracking theorem, stopping tail, or oracle accuracy is assumed
proved by this file. The guide explains how to derive those and where this bound is used.

Residuals are N*(muHat-lambda)/sigma, never N*muHat/sigma except at the null lambda=0.
The existing Qstat already has the correct residual; do not replace its definition.
-/
namespace CIGAMF.P13.PaperACertificatePerturbation
open Finset
open CIGAMF.P13.PaperA7Stream

theorem effective_count_identity (a n : ℝ) (ha : 0 < a) (hn : 0 ≤ n) :
    n - n^2/(a+n) = a*n/(a+n) := by
  have hden : a+n ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem effective_count_loss_le (a n : ℝ) (ha : 0 < a) (hn : 0 ≤ n) :
    0 ≤ n - n^2/(a+n) ∧ n - n^2/(a+n) ≤ a := by
  rw [effective_count_identity a n ha hn]
  constructor
  · positivity
  · apply (div_le_iff₀ (by linarith : 0 < a+n)).2
    nlinarith [sq_nonneg a]

theorem sq_residual_bound (B r mu theta lam : ℝ)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (ht : |theta| ≤ B) (hl : |lam| ≤ B)
    (he : |mu-theta| ≤ r) : (mu-lam)^2 ≤ (2*B+r)^2 := by
  have hdist : |mu-lam| ≤ 2*B+r := by
    calc |mu-lam| = |(mu-theta)+(theta-lam)| := by congr 1 <;> ring
      _ ≤ |mu-theta|+|theta-lam| := abs_add_le _ _
      _ ≤ r+(|theta|+|lam|) := add_le_add he (abs_sub _ _)
      _ ≤ 2*B+r := by linarith
  have habs : 0 ≤ |mu-lam| := abs_nonneg _
  have hb : 0 ≤ 2*B+r := by positivity
  nlinarith [sq_abs (mu-lam)]

theorem sq_residual_difference (B r mu theta lam : ℝ)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (ht : |theta| ≤ B) (hl : |lam| ≤ B)
    (he : |mu-theta| ≤ r) :
    |(theta-lam)^2-(mu-lam)^2| ≤ r*(4*B+r) := by
  have htlam : |theta-lam| ≤ 2*B := (abs_sub _ _).trans (by linarith)
  have hmulam : |mu-lam| ≤ 2*B+r := by
    calc |mu-lam| = |(mu-theta)+(theta-lam)| := by congr 1 <;> ring
      _ ≤ |mu-theta|+|theta-lam| := abs_add_le _ _
      _ ≤ 2*B+r := by linarith
  have hsum : |(theta-lam)+(mu-lam)| ≤ 4*B+r :=
    (abs_add_le _ _).trans (by linarith)
  have hid : (theta-lam)^2-(mu-lam)^2 =
      (theta-mu)*((theta-lam)+(mu-lam)) := by ring
  rw [hid, abs_mul]
  exact mul_le_mul (by simpa [abs_sub_comm] using he) hsum
    (abs_nonneg _) hr

/-- Loss from the effective-count statistic at ONE cell, including estimate error. -/
theorem qcell_ge_true_energy (a n v B r mu theta lam : ℝ)
    (ha : 0 < a) (hn : 0 ≤ n) (hv : 0 < v)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (ht : |theta| ≤ B) (hl : |lam| ≤ B)
    (he : |mu-theta| ≤ r) :
    n*(theta-lam)^2/(2*v)
      - (n*r*(4*B+r)+a*(2*B+r)^2)/(2*v)
      ≤ n^2*(mu-lam)^2/(2*(a+n)*v) := by
  have hden : 0 < a+n := by linarith
  have hdiff := (abs_le.mp (sq_residual_difference B r mu theta lam hB hr ht hl he)).2
  have herr : n*(theta-lam)^2 - n*(mu-lam)^2 ≤ n*r*(4*B+r) := by
    have h := mul_le_mul_of_nonneg_left hdiff hn
    nlinarith
  have hc := effective_count_loss_le a n ha hn
  have hs := sq_residual_bound B r mu theta lam hB hr ht hl he
  have hreg : (n-n^2/(a+n))*(mu-lam)^2 ≤ a*(2*B+r)^2 :=
    (mul_le_mul_of_nonneg_right hc.2 (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hs ha.le)
  have hnum : n*(theta-lam)^2 - (n*r*(4*B+r)+a*(2*B+r)^2)
      ≤ (n^2/(a+n))*(mu-lam)^2 := by nlinarith
  have h := div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 2*v)
  have hv0 : v ≠ 0 := hv.ne'
  have hden0 : a+n ≠ 0 := hden.ne'
  have e1 : n*(theta-lam)^2/(2*v) - (n*r*(4*B+r)+a*(2*B+r)^2)/(2*v)
      = (n*(theta-lam)^2 - (n*r*(4*B+r)+a*(2*B+r)^2))/(2*v) := (sub_div _ _ _).symm
  have e2 : n^2*(mu-lam)^2/(2*(a+n)*v) = (n^2/(a+n))*(mu-lam)^2/(2*v) := by
    field_simp
    try ring
  rw [e1, e2]
  exact h

noncomputable def linearEnergy {E : Type*} [Fintype E]
    (N var theta lam : E → ℝ) : ℝ :=
  ∑ e, N e*(theta e-lam e)^2/(2*var e)

noncomputable def perturbationCost {E : Type*} [Fintype E]
    (a B r : ℝ) (N var : E → ℝ) : ℝ :=
  ∑ e, (N e*r*(4*B+r)+a*(2*B+r)^2)/(2*var e)

/-- Uniform in lambda. This is the missing deterministic comparison before taking infima. -/
theorem Qstat_ge_linearEnergy {E : Type*} [Fintype E]
    (a B r : ℝ) (N sigma mu theta lam : E → ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hN : ∀ e, 0 ≤ N e) (hs : ∀ e, sigma e ≠ 0)
    (ht : ∀ e, |theta e| ≤ B) (hl : ∀ e, |lam e| ≤ B)
    (he : ∀ e, |mu e-theta e| ≤ r) :
    linearEnergy N (fun e => sigma e^2) theta lam
      - perturbationCost a B r N (fun e => sigma e^2)
      ≤ Qstat a sigma N mu lam := by
  unfold linearEnergy perturbationCost Qstat
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro e heuniv
  exact qcell_ge_true_energy a (N e) (sigma e^2) B r (mu e) (theta e) (lam e)
    ha (hN e) (sq_pos_of_ne_zero (hs e)) hB hr (ht e) (hl e) (he e)

/-- The `v_min` corollary, before dividing by `t`: with every variance at least `vmin`, the
perturbation cost is at most `[(Σ N) r(4B+r) + d a (2B+r)²] / (2 vmin)`, `d` the number of cells. -/
theorem perturbationCost_le_vmin {E : Type*} [Fintype E]
    (a B r vmin : ℝ) (N var : E → ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hr : 0 ≤ r) (hvmin : 0 < vmin)
    (hN : ∀ e, 0 ≤ N e) (hvar : ∀ e, vmin ≤ var e) :
    perturbationCost a B r N var
      ≤ ((∑ e, N e) * r * (4*B+r) + (Fintype.card E : ℝ) * a * (2*B+r)^2) / (2*vmin) := by
  unfold perturbationCost
  have hterm : ∀ e, (N e*r*(4*B+r)+a*(2*B+r)^2)/(2*var e)
      ≤ (N e*r*(4*B+r)+a*(2*B+r)^2)/(2*vmin) := by
    intro e
    have hNe := hN e
    have hnum : 0 ≤ N e*r*(4*B+r)+a*(2*B+r)^2 := by positivity
    exact div_le_div_of_nonneg_left hnum (by positivity) (by linarith [hvar e])
  have hsum : ∑ e, (N e*r*(4*B+r)+a*(2*B+r)^2)
      = (∑ e, N e) * r * (4*B+r) + (Fintype.card E : ℝ) * a * (2*B+r)^2 := by
    rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  calc ∑ e, (N e*r*(4*B+r)+a*(2*B+r)^2)/(2*var e)
      ≤ ∑ e, (N e*r*(4*B+r)+a*(2*B+r)^2)/(2*vmin) := Finset.sum_le_sum fun e _ => hterm e
    _ = _ := by rw [← Finset.sum_div, hsum]

/-- **The displayed `v_min` corollary.**  If `Σ_e N_e = t > 0` then
`R_t / t ≤ r(4B+r)/(2 vmin) + a d (2B+r)² / (2 vmin t)`.  The first term vanishes with the
confidence radius `r`, the second with `1/t`; neither depends on the alternative `lambda`. -/
theorem perturbationCost_div_le {E : Type*} [Fintype E]
    (a B r vmin t : ℝ) (N var : E → ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hr : 0 ≤ r) (hvmin : 0 < vmin) (ht : 0 < t)
    (hN : ∀ e, 0 ≤ N e) (hvar : ∀ e, vmin ≤ var e) (hsum : ∑ e, N e = t) :
    perturbationCost a B r N var / t
      ≤ r*(4*B+r)/(2*vmin) + a*(Fintype.card E : ℝ)*(2*B+r)^2/(2*vmin*t) := by
  have h := perturbationCost_le_vmin a B r vmin N var ha hB hr hvmin hN hvar
  rw [hsum] at h
  have hv0 : vmin ≠ 0 := hvmin.ne'
  have ht0 : t ≠ 0 := ht.ne'
  calc perturbationCost a B r N var / t
      ≤ ((t*r*(4*B+r) + (Fintype.card E : ℝ)*a*(2*B+r)^2)/(2*vmin)) / t :=
        div_le_div_of_nonneg_right h ht.le
    _ = r*(4*B+r)/(2*vmin) + a*(Fintype.card E : ℝ)*(2*B+r)^2/(2*vmin*t) := by
        field_simp
        try ring

/-- The linear-count energy is nonnegative, so its image over any set is bounded below. -/
theorem linearEnergy_nonneg {E : Type*} [Fintype E] (N var theta lam : E → ℝ)
    (hN : ∀ e, 0 ≤ N e) (hvar : ∀ e, 0 < var e) : 0 ≤ linearEnergy N var theta lam := by
  unfold linearEnergy
  refine Finset.sum_nonneg fun e _ => ?_
  have hNe := hN e
  have hve := hvar e
  positivity

/-- **The bound survives the infimum over the actual alternatives.**  For any NONEMPTY set
`S` of boxed alternatives, the infimum of the implemented statistic is at least the infimum
of the linear-count energy minus the SAME `lambda`-free cost `R_t`.  This is a statement about
the exact `Z_t = inf Qstat`; the computed lower certificate `Zlo_t` loses a further `nu_t`,
which this file does not bound. -/
theorem sInf_Qstat_ge {E : Type*} [Fintype E]
    (a B r : ℝ) (N sigma mu theta : E → ℝ) (S : Set (E → ℝ)) (hS : S.Nonempty)
    (ha : 0 < a) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hN : ∀ e, 0 ≤ N e) (hs : ∀ e, sigma e ≠ 0)
    (ht : ∀ e, |theta e| ≤ B) (hl : ∀ lam ∈ S, ∀ e, |lam e| ≤ B)
    (he : ∀ e, |mu e-theta e| ≤ r) :
    sInf ((fun lam => linearEnergy N (fun e => sigma e^2) theta lam) '' S)
        - perturbationCost a B r N (fun e => sigma e^2)
      ≤ sInf ((fun lam => Qstat a sigma N mu lam) '' S) := by
  have hbdd : BddBelow ((fun lam => linearEnergy N (fun e => sigma e^2) theta lam) '' S) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨lam, -, rfl⟩
    exact linearEnergy_nonneg N _ theta lam hN fun e => sq_pos_of_ne_zero (hs e)
  apply le_csInf (hS.image _)
  rintro _ ⟨lam, hlam, rfl⟩
  have h1 : sInf ((fun lam => linearEnergy N (fun e => sigma e^2) theta lam) '' S)
      ≤ linearEnergy N (fun e => sigma e^2) theta lam := csInf_le hbdd ⟨lam, hlam, rfl⟩
  have h2 := Qstat_ge_linearEnergy a B r N sigma mu theta lam ha hB hr hN hs ht (hl lam hlam) he
  linarith

#print axioms effective_count_identity
#print axioms effective_count_loss_le
#print axioms sq_residual_bound
#print axioms sq_residual_difference
#print axioms qcell_ge_true_energy
#print axioms Qstat_ge_linearEnergy
#print axioms perturbationCost_le_vmin
#print axioms perturbationCost_div_le
#print axioms linearEnergy_nonneg
#print axioms sInf_Qstat_ge
end CIGAMF.P13.PaperACertificatePerturbation
