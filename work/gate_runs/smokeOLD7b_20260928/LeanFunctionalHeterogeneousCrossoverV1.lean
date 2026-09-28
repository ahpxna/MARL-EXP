import Mathlib

/-! # Functional: the crossover upper bound on a HETEROGENEOUS outsider.

`LeanFunctionalExtremaCrossoverV1` and `LeanFunctionalCrossoverLowerV1` handle the
family whose `n` middle cells all sit at `0` with variance `1`. That symmetry is
doing real work there, and the natural objection is that the law is an artefact
of it. This file removes it: middle cell `i` sits at an arbitrary mean `z i` with
an arbitrary variance `sig i > 0`, and the bound below depends on those only
through the single scalar

    Splus = sum_i  sig i / (g i + delta)^2,     g i = 1/2 - |z i|,  delta = d/2,

where `d = 1 - rho` is the capacity gap. Two families with different middle
distributions but the same value of that scalar get the same bound.

## What is proved

`FlipsH` is stated as "some pair of outsider cells is spread at least as far as
the incumbent", which is exactly `|lI1 - lI0| ≤ range(outsider)` unfolded, and is
what every witness actually exhibits.

* `witness_EE` — for EVERY allocation there is a flipping alternative costing
  `(endpoint mass) * d^2/32`. It moves the four endpoints to the common levels
  `±(1+rho)/4` and leaves every middle cell alone, so the middles' means and
  variances are irrelevant to it — and since middles can only widen the
  outsider's range, the flip condition survives them.
* `witness_middle` — for EVERY allocation and EVERY middle cell `i` there is a
  flipping alternative costing `wM i * (g i + delta)^2 / (2 * sig i)`. It keeps
  the incumbent at `±1/2` and pushes cell `i` just past the opposite endpoint,
  in whichever direction is cheaper.
* `min_middle_le` — the averaging step: the cheapest middle witness costs at most
  `u/(2 Splus)`, `u` the total middle mass. No optimisation, just
  `min_i a_i * (2 Splus) ≤ sum_i a_i * 2 sig i/(g i + delta)^2 = u`.
* `heterogeneous_upper` — combining them, for EVERY allocation there is a
  flipping alternative costing at most

        d^2 / (32 + 2 d^2 Splus).

  At `n Splus^{-1}`-scale with `d = c/sqrt n` and `Splus = n Hplus` this reads
  `n Gamma_n ≤ c^2/(32 + 2 c^2 Hplus)`, which is the upper half of the
  heterogeneous crossover law.

## WHAT THIS DOES NOT ESTABLISH

- This is the UPPER half only. The matching lower bound at the explicit
  allocation `u = c^2 H/(16 + c^2 H)`, `wM i ∝ sig i/(g i)^2` is NOT proved here.
  It is verified in exact rational arithmetic by
  `scripts/F2_heterogeneous_crossover_check.py` on 115 configurations inside the
  stated domain, where the value comes out EXACTLY `d^2/(32 + 2 d^2 S)` with
  `S = sum_i sig i/(g i)^2` — no slack factor — and the active pair is always the
  endpoint/endpoint one. That is numerical evidence, not a receipt.
- `Gamma` is not defined here. Each statement is "for every allocation there
  EXISTS a flipping alternative costing at most X", which bounds an infimum from
  above without naming it.
- No limit is taken and no `H_n → H` hypothesis is used: everything is finite and
  holds at every `n`. The limit law is not proved.
- The domain condition `g i ≥ delta` (middle cells strictly inside the endpoints)
  is NOT needed for this upper bound and is not assumed. It IS needed for the
  lower bound: the probe finds the value drops below `d^2/(32 + 2 d^2 S)` exactly
  when a middle cell escapes past an endpoint (`n=64, c=4, z=±3/8`, where
  `g0 = 1/8 < delta = 1/4`), and there the active pair becomes middle/middle.
- Nothing here concerns an algorithm, a stopping rule, or sample complexity.

## Collision

`Shahverdikondori–Badri–Kiyavash, Best Group Identification in Multi-Objective
Bandits (2025)` reduces to the range objective under `X ↦ (b + sX, b - sX)`, so
"identify the group of largest capacity" is NOT novel on its own. What this file
aims at is the sharp constant and the allocation on a family that is no longer
symmetric.
-/

namespace CIGAMF.P13.FunctionalHeterogeneousCrossover
open Finset
open scoped BigOperators
noncomputable section

variable {n : ℕ} (z : Fin n → ℝ)

/-- Distance from middle cell `i` to the nearer extreme of the incumbent. -/
def gap (z : Fin n → ℝ) (i : Fin n) : ℝ := 1/2 - |z i|

/-- Energy of an alternative. Incumbent cells have means `∓1/2` and variance `1`;
the outsider's endpoints have means `±rho/2` and variance `1`; middle cell `i`
has mean `z i` and variance `sig i`. -/
def energyH (wI0 wI1 wE0 wE1 : ℝ) (wM sig : Fin n → ℝ) (rho : ℝ)
    (lI0 lI1 lE0 lE1 : ℝ) (lM : Fin n → ℝ) : ℝ :=
  (wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2)/2
    + (wE0*(lE0-rho/2)^2 + wE1*(lE1+rho/2)^2
        + ∑ i, wM i*(lM i - z i)^2/sig i)/2

/-- `x` is the new value of one of the outsider's cells. -/
def IsCell (lE0 lE1 : ℝ) (lM : Fin n → ℝ) (x : ℝ) : Prop :=
  x = lE0 ∨ x = lE1 ∨ ∃ i, x = lM i

/-- The alternative reverses the Top-1 decision: some pair of outsider cells is
spread at least as far as the incumbent. This is `|lI1 - lI0| ≤ range(outsider)`
with the sup and inf unfolded to the witnessing pair. -/
def FlipsH (lI0 lI1 lE0 lE1 : ℝ) (lM : Fin n → ℝ) : Prop :=
  ∃ x y : ℝ, IsCell lE0 lE1 lM x ∧ IsCell lE0 lE1 lM y ∧ |lI1 - lI0| ≤ x - y

/-! ## Witness EE: open the four endpoints, leave every middle cell alone -/

theorem witness_EE (rho : ℝ) (h0 : 0 ≤ rho) (hr : rho ≤ 1)
    (wI0 wI1 wE0 wE1 : ℝ) (wM sig : Fin n → ℝ) :
    ∃ lI0 lI1 lE0 lE1 lM, FlipsH lI0 lI1 lE0 lE1 lM ∧
      energyH z wI0 wI1 wE0 wE1 wM sig rho lI0 lI1 lE0 lE1 lM
        = (wI0 + wI1 + wE0 + wE1)*(1-rho)^2/32 := by
  refine ⟨-(1+rho)/4, (1+rho)/4, (1+rho)/4, -(1+rho)/4, z, ?_, ?_⟩
  · exact ⟨(1+rho)/4, -(1+rho)/4, Or.inl rfl, Or.inr (Or.inl rfl), by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (1+rho)/4 - -(1+rho)/4)]⟩
  · unfold energyH
    have hz : ∀ i : Fin n, wM i*(z i - z i)^2/sig i = 0 := fun i => by simp
    rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_const_zero]
    ring

/-! ## Witness M: push one middle cell past the opposite endpoint -/

theorem witness_middle (rho : ℝ) (h0 : 0 ≤ rho) (hr : rho ≤ 1)
    (wI0 wI1 wE0 wE1 : ℝ) (wM sig : Fin n → ℝ) (i : Fin n) :
    ∃ lI0 lI1 lE0 lE1 lM, FlipsH lI0 lI1 lE0 lE1 lM ∧
      energyH z wI0 wI1 wE0 wE1 wM sig rho lI0 lI1 lE0 lE1 lM
        = wM i*(gap z i + (1-rho)/2)^2/(2*sig i) := by
  classical
  have habs : |(1:ℝ)/2 - -(1/2)| = 1 := by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2 - -(1/2))]; norm_num
  by_cases hzi : 0 ≤ z i
  · refine ⟨-(1/2), 1/2, rho/2, -(rho/2),
      Function.update z i (1/2 + (1-rho)/2), ?_, ?_⟩
    · refine ⟨1/2 + (1-rho)/2, -(rho/2), Or.inr (Or.inr ⟨i, by
        rw [Function.update_self]⟩), Or.inr (Or.inl rfl), ?_⟩
      rw [habs]; linarith
    · unfold energyH
      have hsplit : (∑ k, wM k*((Function.update z i (1/2 + (1-rho)/2)) k - z k)^2/sig k)
          = wM i*((1/2 + (1-rho)/2) - z i)^2/sig i := by
        rw [Finset.sum_eq_single i
          (fun k _ hk => by rw [Function.update_of_ne hk]; simp)
          (fun h => absurd (mem_univ i) h), Function.update_self]
      rw [hsplit]
      have hg : gap z i = 1/2 - z i := by unfold gap; rw [abs_of_nonneg hzi]
      rw [hg]; ring
  · push_neg at hzi
    refine ⟨-(1/2), 1/2, rho/2, -(rho/2),
      Function.update z i (-(1/2 + (1-rho)/2)), ?_, ?_⟩
    · refine ⟨rho/2, -(1/2 + (1-rho)/2), Or.inl rfl, Or.inr (Or.inr ⟨i, by
        rw [Function.update_self]⟩), ?_⟩
      rw [habs]; linarith
    · unfold energyH
      have hsplit : (∑ k, wM k*((Function.update z i (-(1/2 + (1-rho)/2))) k - z k)^2/sig k)
          = wM i*((-(1/2 + (1-rho)/2)) - z i)^2/sig i := by
        rw [Finset.sum_eq_single i
          (fun k _ hk => by rw [Function.update_of_ne hk]; simp)
          (fun h => absurd (mem_univ i) h), Function.update_self]
      rw [hsplit]
      have hg : gap z i = 1/2 + z i := by unfold gap; rw [abs_of_neg hzi]; ring
      rw [hg]; ring

/-! ## The averaging step and the combined bound -/

/-- `Splus = sum_i sig i/(g i + d/2)^2`: the ONLY way the middle distribution
enters the bound. -/
def Splus (z sig : Fin n → ℝ) (d : ℝ) : ℝ := ∑ i, sig i/(gap z i + d/2)^2

theorem min_middle_le (sig wM : Fin n → ℝ) (d : ℝ) (hn : 0 < n)
    (hsig : ∀ i, 0 < sig i) (hg : ∀ i, 0 < gap z i + d/2) (u : ℝ)
    (hu : ∑ i, wM i = u) :
    ∃ i : Fin n, wM i*(gap z i + d/2)^2/(2*sig i)*(2*Splus z sig d) ≤ u := by
  classical
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  obtain ⟨i0, -, hmin⟩ :=
    Finset.exists_min_image univ (fun i => wM i*(gap z i + d/2)^2/(2*sig i)) hne
  refine ⟨i0, ?_⟩
  have hterm : ∀ i : Fin n,
      (wM i*(gap z i + d/2)^2/(2*sig i))*(2*(sig i/(gap z i + d/2)^2)) = wM i := by
    intro i
    have hgi := hg i
    have h0 : gap z i + d/2 ≠ 0 := ne_of_gt hgi
    have h0' : gap z i * 2 + d ≠ 0 := by intro hc; linarith
    have h1 : (gap z i + d/2)^2 ≠ 0 := pow_ne_zero 2 h0
    have h2 : sig i ≠ 0 := ne_of_gt (hsig i)
    field_simp
  have hkey : ∑ i, (wM i0*(gap z i0 + d/2)^2/(2*sig i0))*(2*(sig i/(gap z i + d/2)^2))
      ≤ ∑ i, (wM i*(gap z i + d/2)^2/(2*sig i))*(2*(sig i/(gap z i + d/2)^2)) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hpos : (0:ℝ) < sig i/(gap z i + d/2)^2 :=
      div_pos (hsig i) (pow_pos (hg i) 2)
    exact mul_le_mul_of_nonneg_right (hmin i (mem_univ i)) (by linarith)
  rw [Finset.sum_congr rfl (fun i _ => hterm i), hu, ← Finset.mul_sum] at hkey
  have hS : (∑ i, 2*(sig i/(gap z i + d/2)^2)) = 2*Splus z sig d := by
    unfold Splus; rw [← Finset.mul_sum]
  rwa [hS] at hkey

/-- THE UPPER HALF. For EVERY allocation there is a flipping alternative costing
at most `d^2/(32 + 2 d^2 Splus)`. The middle distribution enters only through
`Splus`. -/
theorem heterogeneous_upper (rho : ℝ) (h0 : 0 ≤ rho) (hr : rho < 1) (hn : 0 < n)
    (wI0 wI1 wE0 wE1 : ℝ) (wM sig : Fin n → ℝ)
    (hsig : ∀ i, 0 < sig i)
    (hg : ∀ i, 0 < gap z i + (1-rho)/2)
    (hnorm : wI0 + wI1 + wE0 + wE1 + ∑ i, wM i = 1) :
    ∃ lI0 lI1 lE0 lE1 lM, FlipsH lI0 lI1 lE0 lE1 lM ∧
      energyH z wI0 wI1 wE0 wE1 wM sig rho lI0 lI1 lE0 lE1 lM
        ≤ (1-rho)^2/(32 + 2*(1-rho)^2*Splus z sig (1-rho)) := by
  classical
  set d : ℝ := 1 - rho with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hd2 : (0:ℝ) < d^2 := pow_pos hdpos 2
  set S : ℝ := Splus z sig d with hSdef
  have hSpos : 0 < S := by
    rw [hSdef]; unfold Splus
    exact Finset.sum_pos (fun i _ => div_pos (hsig i) (pow_pos (hg i) 2))
      ⟨⟨0, hn⟩, mem_univ _⟩
  have hden : (0:ℝ) < 32 + 2*d^2*S := by positivity
  set V : ℝ := d^2/(32 + 2*d^2*S) with hV
  have hVpos : 0 < V := by rw [hV]; positivity
  set P : ℝ := wI0 + wI1 + wE0 + wE1 with hP
  set u : ℝ := ∑ i, wM i with hu
  have hPu : P + u = 1 := by rw [hP, hu]; linarith [hnorm]
  by_cases hcase : P*d^2/32 ≤ V
  · obtain ⟨a, b, c, e, f, hf, heq⟩ :=
      witness_EE z rho h0 (by linarith) wI0 wI1 wE0 wE1 wM sig
    exact ⟨a, b, c, e, f, hf, by rw [heq, ← hd, ← hP]; exact hcase⟩
  · push_neg at hcase
    have hPgt : 32*V/d^2 < P := by
      rw [div_lt_iff₀ hd2]; linarith [hcase]
    have h1mV : 1 - 32*V/d^2 = 2*S*V := by
      rw [hV]; field_simp; ring
    have hult : u < 2*S*V := by linarith [hPu, hPgt, h1mV]
    obtain ⟨i, hi⟩ :=
      min_middle_le z sig wM d hn hsig (fun i => by rw [hd]; exact hg i) u rfl
    obtain ⟨a, b, c, e, f, hf, heq⟩ :=
      witness_middle z rho h0 (by linarith) wI0 wI1 wE0 wE1 wM sig i
    refine ⟨a, b, c, e, f, hf, ?_⟩
    rw [heq, ← hd]
    have hS2 : (0:ℝ) < 2*S := by linarith
    refine le_of_mul_le_mul_right ?_ hS2
    calc wM i*(gap z i + d/2)^2/(2*sig i)*(2*S) ≤ u := hi
      _ ≤ V*(2*S) := by linarith [hult]

#print axioms witness_EE
#print axioms witness_middle
#print axioms min_middle_le
#print axioms heterogeneous_upper

end
end CIGAMF.P13.FunctionalHeterogeneousCrossover
