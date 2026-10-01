import Mathlib

/-! # Q-Intervention: the RANDOMIZED regret floor under raw measurement.

`scripts/G4_fixed_world_observation_classes.py:412` computes
`min over S of max over A of L_A(S)` — a DETERMINISTIC minimax. That is not a
bound for randomized procedures and may not be quoted as a floor for "every
algorithm". On the witness below the deterministic number is `13983/32768`
while the true randomized value is `2401/8192`, smaller by a factor `1.456`.
This file proves the randomized value, both directions, over EVERY distribution
on the decisions.

## The witness

The corpus's own compensated world with `k = 3`, `t0 = 1/8`, `rho = 1`,
`T = {0,1,2}`, `j = 5`, and the two hidden sets `A = {0,1,3}`, `B = {0,2,3}`.
`scripts/Q1_intervention_regret_floor.py` verifies in exact rational arithmetic
that the two worlds have the SAME raw histogram (32 atoms, total mass 1) and
produces the budget-1 loss table, which is transcribed here as `lossA`, `lossB`:

    decision      L_A            L_B
    {}            3/2            3/2
    {0}           54377/32768    54377/32768
    {1}           54377/32768    35169/32768
    {2}           35169/32768    54377/32768

Coordinates outside `T` have zero response, so they only pad the cardinality;
the four rows are the whole budget-1 decision space.

## What is proved

* `optA_eq`, `optB_eq` — each world's own optimum is `35169/32768`, attained at
  `{2}` for `A` and at `{1}` for `B`. The two optima are attained at DIFFERENT
  decisions; that is the whole difficulty.
* `regret_floor` — for EVERY probability vector `P` on the four decisions,
  `max (regretA P) (regretB P) ≥ 2401/8192`. The proof is an averaging argument:
  the max is at least the mean, and every column of the summed regret vector has
  coefficient at least `19208/32768`.
* `regret_floor_attained` — the mixed rule `1/2` on `{1}` and `1/2` on `{2}`
  attains exactly `2401/8192` on BOTH worlds, so the floor is the exact value of
  the game, not merely a bound.
* `blind_procedure_floor` — the bridge. A procedure observes a transcript in
  `Omega` and outputs a decision distribution. Because the two worlds induce the
  SAME transcript law, the same `mu` and the same `rule` appear for both worlds,
  so the induced decision distribution is literally one function and the floor
  applies verbatim — for any number of samples, adaptive or not, with any
  internal randomisation, and with any history-dependent stopping.

## WHAT THIS DOES NOT ESTABLISH

- The raw-law equality of the two worlds is NOT proved here. It is verified
  exactly (all 32 atoms, rational arithmetic) by the probe, and the loss table is
  transcribed from the same probe. Formalising the permutation transport
  `F_{pi A}(pi x) = F_A(x)` on `centeredWorld`, and hence the equality of laws,
  is a separate obligation and is not discharged in this file. Everything below
  is therefore a theorem about the TABLE, plus a bridge that becomes a statement
  about the worlds only once that equality is formalised.
- `Omega` is a finite transcript space with a probability vector on it. This
  covers any procedure with finitely many observable outcomes; it is not a
  general measure-theoretic statement, and the Gaussian noise channel is not
  modelled here.
- Nothing is proved about the contextual instrument. The probe records
  `E[(F_A - F_B)^2] = 28487865/536870912 > 0`, so context separates the two
  worlds, but no sample-size upper bound is proved — "the KL is positive so it
  suffices" is not an argument, and the likelihood-ratio constant is not computed.
- One configuration, one pair of worlds, budget one. No law in `k`, no statement
  about other budgets, no claim about `b_dec` or `b_id`.
-/

namespace CIGAMF.P13.QueryInterventionFloor
open Finset
open scoped BigOperators
noncomputable section

/-- The four budget-1 decisions: keep nothing in `T`, or keep one of `0, 1, 2`. -/
abbrev Dec := Fin 4

/-- Budget-1 loss table of world `A = {0,1,3}`. -/
def lossA : Dec → ℝ
  | 0 => 3/2
  | 1 => 54377/32768
  | 2 => 54377/32768
  | 3 => 35169/32768

/-- Budget-1 loss table of world `B = {0,2,3}`. -/
def lossB : Dec → ℝ
  | 0 => 3/2
  | 1 => 54377/32768
  | 2 => 35169/32768
  | 3 => 54377/32768

/-- The mixed rule that attains the floor: `1/2` on `{1}`, `1/2` on `{2}`. -/
def Pstar : Dec → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1/2
  | 3 => 1/2

/-- The common value of the two worlds' own optima. -/
def optval : ℝ := 35169/32768

theorem optA_eq : IsLeast (Set.range lossA) optval := by
  constructor
  · exact ⟨3, by simp [lossA, optval]⟩
  · rintro x ⟨S, rfl⟩
    fin_cases S <;> simp [lossA, optval] <;> norm_num

theorem optB_eq : IsLeast (Set.range lossB) optval := by
  constructor
  · exact ⟨2, by simp [lossB, optval]⟩
  · rintro x ⟨S, rfl⟩
    fin_cases S <;> simp [lossB, optval] <;> norm_num

/-- The two optima are attained at DIFFERENT decisions. -/
theorem optima_disagree : lossA 3 = optval ∧ lossB 2 = optval ∧
    optval < lossA 2 ∧ optval < lossB 3 := by
  refine ⟨by simp [lossA, optval], by simp [lossB, optval], ?_, ?_⟩ <;>
    simp only [lossA, lossB, optval] <;> norm_num

/-- Expected regret of a decision distribution on each world. -/
def regretA (P : Dec → ℝ) : ℝ := ∑ S, P S*(lossA S - optval)
def regretB (P : Dec → ℝ) : ℝ := ∑ S, P S*(lossB S - optval)

/-- THE FLOOR. Every distribution on the four decisions pays at least
`2401/8192` on one of the two worlds. -/
theorem regret_floor (P : Dec → ℝ) (hP : ∀ S, 0 ≤ P S) (hsum : ∑ S, P S = 1) :
    2401/8192 ≤ max (regretA P) (regretB P) := by
  have hmax : (regretA P + regretB P)/2 ≤ max (regretA P) (regretB P) := by
    rcases le_total (regretA P) (regretB P) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hsum4 : P 0 + P 1 + P 2 + P 3 = 1 := by
    rw [← hsum, Fin.sum_univ_four]
  have hexp : regretA P + regretB P
      = P 0*(27966/32768) + P 1*(38416/32768)
        + P 2*(19208/32768) + P 3*(19208/32768) := by
    unfold regretA regretB
    rw [Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [lossA, lossB, optval]
    ring
  -- every coefficient is at least 19208/32768, and the mass is one
  have hlow : (19208:ℝ)/32768 ≤ regretA P + regretB P := by
    rw [hexp]
    have h0 := hP 0; have h1 := hP 1; have h2 := hP 2; have h3 := hP 3
    nlinarith [hsum4, h0, h1, h2, h3]
  linarith

/-- The floor is EXACT: the mixed rule `1/2` on `{1}`, `1/2` on `{2}` attains it
on both worlds simultaneously. -/
theorem regret_floor_attained :
    ∃ P : Dec → ℝ, (∀ S, 0 ≤ P S) ∧ (∑ S, P S = 1) ∧
      regretA P = 2401/8192 ∧ regretB P = 2401/8192 := by
  refine ⟨Pstar, ?_, ?_, ?_, ?_⟩
  · intro S; fin_cases S <;> simp [Pstar] <;> norm_num
  · rw [Fin.sum_univ_four]; simp only [Pstar]; norm_num
  · unfold regretA; rw [Fin.sum_univ_four]; simp only [Pstar, lossA, optval]; norm_num
  · unfold regretB; rw [Fin.sum_univ_four]; simp only [Pstar, lossB, optval]; norm_num

/-- The deterministic minimax that `G4:412` computes is STRICTLY larger, so it
overstates the floor. -/
theorem deterministic_minimax_is_larger :
    2401/8192 < (13983:ℝ)/32768 ∧
    (∀ S : Dec, (13983:ℝ)/32768 ≤ max (lossA S - optval) (lossB S - optval)) := by
  constructor
  · norm_num
  · intro S
    fin_cases S <;> simp only [lossA, lossB, optval] <;> norm_num

/-- THE BRIDGE. A procedure reads a transcript in `Omega` and outputs a decision
distribution. Since the two worlds induce the SAME transcript law, one `mu` and
one `rule` serve for both, so the induced decision distribution is a single
function and the floor applies verbatim — any number of samples, adaptive or
not, any internal randomisation, any history-dependent stopping. -/
theorem blind_procedure_floor {Ω : Type*} [Fintype Ω] (mu : Ω → ℝ)
    (hmu : ∀ o, 0 ≤ mu o) (hmus : ∑ o, mu o = 1)
    (rule : Ω → Dec → ℝ) (hr : ∀ o S, 0 ≤ rule o S) (hrs : ∀ o, ∑ S, rule o S = 1) :
    2401/8192
      ≤ max (regretA (fun S => ∑ o, mu o*rule o S))
            (regretB (fun S => ∑ o, mu o*rule o S)) := by
  refine regret_floor _ (fun S => Finset.sum_nonneg (fun o _ => mul_nonneg (hmu o) (hr o S))) ?_
  rw [Finset.sum_comm]
  have : ∀ o : Ω, (∑ S, mu o*rule o S) = mu o := by
    intro o
    rw [← Finset.mul_sum, hrs o, mul_one]
  rw [Finset.sum_congr rfl (fun o _ => this o), hmus]

#print axioms optA_eq
#print axioms optB_eq
#print axioms optima_disagree
#print axioms regret_floor
#print axioms regret_floor_attained
#print axioms deterministic_minimax_is_larger
#print axioms blind_procedure_floor

end
end CIGAMF.P13.QueryInterventionFloor
