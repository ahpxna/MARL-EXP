import Mathlib
import LeanUnifiedObstructionOrderV1

/-!
# Quantitative compiled silence: the obstruction-mass floor

`LeanMarlCompiledSilenceV1` says WHETHER a zero-byte policy can be acceptable everywhere (no obstruction
inside a local observation class).  This module says HOW MUCH unacceptable probability every policy
must pay when obstructions do hide inside its observation classes, under a law `p` on worlds.

A (randomised) policy on an observation `obs : World → O` is a distribution `q o` on actions for each
observation; its risk is the probability of an unacceptable action,
`risk = Σ_F p F · unsafeMass safe (q (obs F)) F`.

## WHAT IS PROVED

* `unsafeMass_nonneg` — the unsafe mass of a distribution is non-negative.
* `obstruction_mass_floor` — **the floor.**  For any family of pairwise disjoint obstructions, each
  inside one observation class, and any weights `m H ≥ 0` below the world probabilities inside `H`,
  every randomised policy on `obs` has `Σ_H m H ≤ risk`.  With `m H = min_{F∈H} p F` this is the
  obstruction mass of the observation.  Applied to the local observation it is a floor for compiled
  silence; applied to a decoded view (`LeanMarlDecisionDepthV1.view`) it is a floor for every policy
  on that view, with the obstructions that the decoded senders do not split.
* `obstruction_nonempty` — with an action available, an obstruction is non-empty.
* `floor_witness` — the floor is attained: two worlds, identification, no observation, `p = (1/2,
  1/2)`: every randomised policy has risk at least `1/2`, and the uniform policy has risk exactly `1/2`.

## WHAT THIS DOES NOT ESTABLISH

- `safe` and `p` are model inputs; estimating them from rollouts is a labelled diagnostic.
- The floor uses disjoint obstructions only; it is not claimed to be the minimax risk in general.
- Nothing about learned students beyond the fact that a student is some policy on its observation.
-/

namespace CIGAMF.P13.MarlObstructionMass

open Finset
open CIGAMF.P13.UnifiedObstructionOrder

variable {World Act O : Type*} [Fintype World] [DecidableEq World] [Fintype Act] [DecidableEq Act]

variable (safe : World → Finset Act)

/-- The probability that a randomised policy on `obs` acts unacceptably. -/
noncomputable def risk (p : World → ℝ) (obs : World → O) (q : O → Act → ℝ) : ℝ :=
  ∑ F, p F * unsafeMass safe (q (obs F)) F

theorem unsafeMass_nonneg (r : Act → ℝ) (hr : ∀ a, 0 ≤ r a) (F : World) :
    0 ≤ unsafeMass safe r F :=
  Finset.sum_nonneg fun a _ => hr a

/-- An obstruction is non-empty as soon as some action exists. -/
theorem obstruction_nonempty [Nonempty Act] {H : Finset World} (hH : IsObstruction safe H) :
    H.Nonempty := by
  by_contra he
  rw [Finset.not_nonempty_iff_eq_empty] at he
  apply hH
  obtain ⟨a⟩ := ‹Nonempty Act›
  exact ⟨a, fun F hF => by simp [he] at hF⟩

/-- **The obstruction-mass floor.** -/
theorem obstruction_mass_floor [Nonempty Act] (p : World → ℝ) (hp : ∀ F, 0 ≤ p F)
    (obs : World → O)
    (q : O → Act → ℝ) (hq : ∀ o a, 0 ≤ q o a) (hqs : ∀ o, ∑ a, q o a = 1)
    (fam : Finset (Finset World)) (hdisj : (fam : Set (Finset World)).PairwiseDisjoint id)
    (hobs : ∀ H ∈ fam, IsObstruction safe H)
    (hcls : ∀ H ∈ fam, ∀ F ∈ H, ∀ G ∈ H, obs F = obs G)
    (m : Finset World → ℝ) (hm0 : ∀ H ∈ fam, 0 ≤ m H) (hm : ∀ H ∈ fam, ∀ F ∈ H, m H ≤ p F) :
    ∑ H ∈ fam, m H ≤ risk safe p obs q := by
  classical
  set u : World → ℝ := fun F => unsafeMass safe (q (obs F)) F with hu
  have hu0 : ∀ F, 0 ≤ u F := fun F => unsafeMass_nonneg safe _ (hq _) F
  -- each obstruction pays at least its weight
  have hH : ∀ H ∈ fam, m H ≤ ∑ F ∈ H, p F * u F := by
    intro H hHf
    obtain ⟨F0, hF0⟩ := obstruction_nonempty safe (hobs H hHf)
    have hcommon : ∑ F ∈ H, u F = ∑ F ∈ H, unsafeMass safe (q (obs F0)) F := by
      refine Finset.sum_congr rfl fun F hF => ?_
      simp only [hu]
      rw [hcls H hHf F hF F0 hF0]
    have hone : 1 ≤ ∑ F ∈ H, u F := by
      rw [hcommon]
      exact obstruction_total_unsafe_mass safe (hobs H hHf) (q (obs F0)) (hq _) (hqs _)
    calc m H = m H * 1 := (mul_one _).symm
      _ ≤ m H * ∑ F ∈ H, u F := mul_le_mul_of_nonneg_left hone (hm0 H hHf)
      _ = ∑ F ∈ H, m H * u F := Finset.mul_sum _ _ _
      _ ≤ ∑ F ∈ H, p F * u F :=
          Finset.sum_le_sum fun F hF => mul_le_mul_of_nonneg_right (hm H hHf F hF) (hu0 F)
  -- the disjoint obstructions are part of the whole sum
  have hunion : ∑ H ∈ fam, ∑ F ∈ H, p F * u F = ∑ F ∈ fam.biUnion id, p F * u F := by
    rw [Finset.sum_biUnion hdisj]
    rfl
  have hsub : ∑ F ∈ fam.biUnion id, p F * u F ≤ ∑ F, p F * u F :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun F _ _ => mul_nonneg (hp F) (hu0 F))
  calc ∑ H ∈ fam, m H ≤ ∑ H ∈ fam, ∑ F ∈ H, p F * u F := Finset.sum_le_sum hH
    _ = ∑ F ∈ fam.biUnion id, p F * u F := hunion
    _ ≤ ∑ F, p F * u F := hsub
    _ = risk safe p obs q := rfl

/-! ## The floor is attained -/

/-- Identification of one of two worlds. -/
def idSafe2 (w : Fin 2) : Finset (Fin 2) := {w}

def noObs (_w : Fin 2) : Unit := ()

noncomputable def half : Fin 2 → ℝ := fun _ => 1 / 2

theorem univ_obstruction2 : IsObstruction idSafe2 (univ : Finset (Fin 2)) := by
  rintro ⟨a, ha⟩
  have h0 := ha 0 (mem_univ _)
  have h1 := ha 1 (mem_univ _)
  simp only [idSafe2, Finset.mem_singleton] at h0 h1
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- **Attainment.**  Every randomised zero-byte policy has risk at least `1/2`; the uniform one
has risk exactly `1/2`. -/
theorem floor_witness :
    (∀ q : Unit → Fin 2 → ℝ, (∀ o a, 0 ≤ q o a) → (∀ o, ∑ a, q o a = 1) →
      1 / 2 ≤ risk idSafe2 half noObs q) ∧
    risk idSafe2 half noObs (fun _ _ => 1 / 2) = 1 / 2 := by
  constructor
  · intro q hq hqs
    have h := obstruction_mass_floor idSafe2 half (fun _ => by unfold half; norm_num) noObs q hq hqs
      {univ} (by simp) (by simpa using univ_obstruction2) (by simp [noObs])
      (fun _ => 1 / 2) (by norm_num) (by intro H _ F _; unfold half; rfl)
    simpa using h
  · have h0 : (univ.filter (fun a : Fin 2 => a ∉ idSafe2 0)).card = 1 := by decide
    have h1 : (univ.filter (fun a : Fin 2 => a ∉ idSafe2 1)).card = 1 := by decide
    unfold risk unsafeMass half
    rw [Fin.sum_univ_two, Finset.sum_const, Finset.sum_const, h0, h1]
    norm_num

end CIGAMF.P13.MarlObstructionMass

#print axioms CIGAMF.P13.MarlObstructionMass.unsafeMass_nonneg
#print axioms CIGAMF.P13.MarlObstructionMass.obstruction_nonempty
#print axioms CIGAMF.P13.MarlObstructionMass.obstruction_mass_floor
#print axioms CIGAMF.P13.MarlObstructionMass.floor_witness
