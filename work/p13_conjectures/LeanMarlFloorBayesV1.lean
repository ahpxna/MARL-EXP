import Mathlib
import LeanMarlObstructionMassV1
import LeanMarlCommValueV1

/-!
# The obstruction-mass floor is a certified lower bound on the Bayes risk of the observation

`LeanMarlCommValueV1` proves the classical facts: every randomised policy on an observation has risk at least its Bayes
risk `bayesRisk obs`, and the per-class argmin attains it.  `LeanMarlObstructionMassV1` proves that every randomised policy
pays at least the total weight `∑ m H` of a disjoint family of obstructions inside the observation classes.  This module
connects them (external audit of 01/10/2026: "show the obstruction-mass certificate ≤ R*").

## WHAT IS PROVED
* `unsafeMass_point` — a point-mass policy is unsafe in world `F` with mass `1` or `0`.
* `risk_point` — the risk of the point mass at `pol` is the probability that `pol` acts unacceptably.
* `floor_le_bayes` — **the obstruction-mass floor is at most the Bayes risk**: `∑_{H ∈ fam} m H ≤ bayesRisk obs`.
  Consequently no student on `obs` — deterministic, randomised, or a sampler of oracle-action modes (CoDiMAD) — beats the
  floor, and the floor never exceeds what the best policy on `obs` achieves.
* `floor_le_bayes_witness` — the hypotheses are satisfiable: on the two-world identification witness the floor `1/2` is a
  lower bound of the Bayes risk of the constant observation.

## WHAT THIS DOES NOT ESTABLISH
- Novelty of the Bayes-risk facts (classical decision theory); this is a certificate, not a new concept.
- Anything about `safe` and `p` in E3: they are model inputs; the probes estimate a teacher-defined proxy.
-/

namespace CIGAMF.P13.MarlFloorBayes

open Finset
open CIGAMF.P13.UnifiedObstructionOrder

variable {World Act O : Type*} [Fintype World] [DecidableEq World] [Fintype Act] [DecidableEq Act]
  [Fintype O] [DecidableEq O]

/-- A deterministic policy as a point-mass randomised policy. -/
def point (pol : O → Act) : O → Act → ℝ := fun o a => if a = pol o then 1 else 0

theorem point_nonneg (pol : O → Act) : ∀ o a, 0 ≤ point pol o a := by
  intro o a; unfold point; split_ifs <;> norm_num

theorem point_sum (pol : O → Act) : ∀ o, ∑ a, point pol o a = 1 := by
  intro o; unfold point; simp

theorem unsafeMass_point (safe : World → Finset Act) (b : Act) (F : World) :
    unsafeMass safe (fun a => if a = b then (1 : ℝ) else 0) F = if b ∈ safe F then 0 else 1 := by
  unfold unsafeMass
  rw [Finset.sum_ite_eq']
  by_cases h : b ∈ safe F <;> simp [h]

theorem risk_point (safe : World → Finset Act) (p : World → ℝ) (obs : World → O) (pol : O → Act) :
    CIGAMF.P13.MarlObstructionMass.risk safe p obs (point pol) =
      ∑ F ∈ univ.filter (fun F => pol (obs F) ∉ safe F), p F := by
  unfold CIGAMF.P13.MarlObstructionMass.risk
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun F _ => ?_
  have : point pol (obs F) = fun a => if a = pol (obs F) then (1 : ℝ) else 0 := rfl
  rw [this, unsafeMass_point]
  by_cases h : pol (obs F) ∈ safe F <;> simp [h]

/-- **The obstruction-mass floor never exceeds the Bayes risk of the observation.** -/
theorem floor_le_bayes [Nonempty Act] (safe : World → Finset Act) (p : World → ℝ) (hp : ∀ F, 0 ≤ p F)
    (obs : World → O)
    (fam : Finset (Finset World)) (hdisj : (fam : Set (Finset World)).PairwiseDisjoint id)
    (hobs : ∀ H ∈ fam, IsObstruction safe H)
    (hcls : ∀ H ∈ fam, ∀ F ∈ H, ∀ G ∈ H, obs F = obs G)
    (m : Finset World → ℝ) (hm0 : ∀ H ∈ fam, 0 ≤ m H) (hm : ∀ H ∈ fam, ∀ F ∈ H, m H ≤ p F) :
    ∑ H ∈ fam, m H ≤ CIGAMF.P13.MarlCommValue.bayesRisk safe p obs := by
  obtain ⟨pol, hpol⟩ := CIGAMF.P13.MarlCommValue.bayes_attained safe p obs
  have h1 := CIGAMF.P13.MarlObstructionMass.obstruction_mass_floor safe p hp obs (point pol) (point_nonneg pol)
    (point_sum pol) fam hdisj hobs hcls m hm0 hm
  rw [risk_point] at h1
  rw [← hpol, CIGAMF.P13.MarlCommValue.badMass_sum_eq]
  exact h1

/-- **Satisfiable.**  Two worlds, identification, no observation, uniform law: the floor `1/2` bounds the Bayes risk. -/
theorem floor_le_bayes_witness :
    (1 : ℝ) / 2 ≤ CIGAMF.P13.MarlCommValue.bayesRisk CIGAMF.P13.MarlObstructionMass.idSafe2
      CIGAMF.P13.MarlObstructionMass.half CIGAMF.P13.MarlObstructionMass.noObs := by
  have h := floor_le_bayes CIGAMF.P13.MarlObstructionMass.idSafe2 CIGAMF.P13.MarlObstructionMass.half
    (fun _ => by unfold CIGAMF.P13.MarlObstructionMass.half; norm_num) CIGAMF.P13.MarlObstructionMass.noObs
    {univ} (by simp) (by simpa using CIGAMF.P13.MarlObstructionMass.univ_obstruction2)
    (by simp [CIGAMF.P13.MarlObstructionMass.noObs]) (fun _ => 1 / 2) (by norm_num)
    (by intro H _ F _; unfold CIGAMF.P13.MarlObstructionMass.half; rfl)
  simpa using h

end CIGAMF.P13.MarlFloorBayes

#print axioms CIGAMF.P13.MarlFloorBayes.unsafeMass_point
#print axioms CIGAMF.P13.MarlFloorBayes.risk_point
#print axioms CIGAMF.P13.MarlFloorBayes.floor_le_bayes
#print axioms CIGAMF.P13.MarlFloorBayes.floor_le_bayes_witness
