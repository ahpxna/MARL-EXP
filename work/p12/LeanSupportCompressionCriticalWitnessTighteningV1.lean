import Mathlib
import «LeanSupportCompressionCriticalWitnessV1»

/-!
# Exact support-query complexity for the CIG compression witness

This module strengthens the concrete three-cell support-compression witness.
The two support worlds differ only at cell `2`.  On this *actual* radius-based
compression objective, querying that one membership bit is both necessary and
sufficient to make an `ε < 1/2` decision over the two-world witness class.

This is intentionally not a claim about arbitrary support families or a global
support-query complexity theorem.
-/

namespace CIGAMF.P13.SupportCompressionCriticalWitnessTightening

open scoped symmDiff
open CIGAMF.P13.SupportCompressionCriticalWitness
open CIGAMF.P13.SupportCriticalIdentification

abbrev Cell := Fin 3

/-- The two exact support worlds in the concrete compression witness. -/
def witnessWorld (b : Bool) : Finset Cell :=
  if b then largeSupport else smallSupport

/-- A membership-query controller is successful if it is `ε`-good on both
    concrete support worlds. -/
def WitnessQuerySuccessful (eps : ℝ) (queries : Finset Cell) : Prop :=
  ∃ controller : (Cell → Bool) → Bool,
    ∀ b : Bool,
      supportCompressionRegret (witnessWorld b)
        (controller (QueryObservation queries (witnessWorld b))) ≤ eps

/-- The only query needed by the witness class: membership of support cell `2`. -/
def cell2Queries : Finset Cell := {2}

/-- Read the queried membership bit at cell `2`. -/
def cell2Controller (observation : Cell → Bool) : Bool := observation 2

private theorem witnessWorld_false : witnessWorld false = smallSupport := by
  simp [witnessWorld]

private theorem witnessWorld_true : witnessWorld true = largeSupport := by
  simp [witnessWorld]

private theorem cell2_absent_small : (2 : Cell) ∉ smallSupport := by decide
private theorem cell2_present_large : (2 : Cell) ∈ largeSupport := by decide

private theorem observation_cell2_small :
    QueryObservation cell2Queries smallSupport 2 = false := by
  simp [cell2Queries, QueryObservation, cell2_absent_small]

private theorem observation_cell2_large :
    QueryObservation cell2Queries largeSupport 2 = true := by
  simp [cell2Queries, QueryObservation, cell2_present_large]

/-- Querying membership of cell `2` and retaining the matching decision has
zero support-compression regret in each witness world. -/
theorem actual_support_cell2_query_zero_regret (b : Bool) :
    supportCompressionRegret (witnessWorld b)
      (cell2Controller (QueryObservation cell2Queries (witnessWorld b))) = 0 := by
  cases b
  · simp only [witnessWorld_false]
    rw [show cell2Controller (QueryObservation cell2Queries smallSupport) = false by
      exact observation_cell2_small]
    exact small_false_regret
  · simp only [witnessWorld_true]
    rw [show cell2Controller (QueryObservation cell2Queries largeSupport) = true by
      exact observation_cell2_large]
    exact large_true_regret

/-- The concrete decision-critical query `{2}` is sufficient for every
nonnegative tolerance on the two-world compression witness. -/
theorem actual_support_cell2_query_suffices
    {eps : ℝ} (heps : 0 ≤ eps) :
    WitnessQuerySuccessful eps cell2Queries := by
  refine ⟨cell2Controller, ?_⟩
  intro b
  rw [actual_support_cell2_query_zero_regret]
  exact heps

private theorem no_query_can_distinguish_witness_worlds
    (queries : Finset Cell) (hNo2 : (2 : Cell) ∉ queries) :
    ¬ ∃ a ∈ queries, Distinguishes a smallSupport largeSupport := by
  rintro ⟨a, ha, hdist⟩
  have hmem : a ∈ (smallSupport ∆ largeSupport) := by
    rw [Finset.mem_symmDiff]
    exact hdist
  have ha2 : a ∈ ({2} : Finset Cell) :=
    actual_support_worlds_differ_only_at_cell2 hmem
  have : a = 2 := by simpa using ha2
  subst a
  exact hNo2 ha

private theorem query_observation_equal_without_cell2
    (queries : Finset Cell) (hNo2 : (2 : Cell) ∉ queries) :
    QueryObservation queries smallSupport = QueryObservation queries largeSupport := by
  apply queryObservation_eq_of_no_distinguishing_query
  exact no_query_can_distinguish_witness_worlds queries hNo2

/-- In the actual radius-compression witness, any membership-query controller
that is `ε`-correct for `ε < 1/2` must query the unique decision-critical cell
`2`.  This is a concrete necessary-evidence theorem, not merely an abstract
critical-cell predicate. -/
theorem actual_support_query_requires_cell2
    {eps : ℝ} (heps : eps < 1 / 2) (queries : Finset Cell)
    (hSuccess : WitnessQuerySuccessful eps queries) :
    (2 : Cell) ∈ queries := by
  by_contra hNo2
  rcases hSuccess with ⟨controller, hcontroller⟩
  have hsame := query_observation_equal_without_cell2 queries hNo2
  have hsmall := hcontroller false
  have hlarge := hcontroller true
  rw [witnessWorld_false] at hsmall
  rw [witnessWorld_true] at hlarge
  rw [← hsame] at hlarge
  cases hchoice : controller (QueryObservation queries smallSupport)
  · rw [hchoice] at hsmall hlarge
    rw [large_false_regret] at hlarge
    linarith
  · rw [hchoice] at hsmall hlarge
    rw [small_true_regret] at hsmall
    linarith

/-- The exact minimum number of membership queries for `ε < 1/2` on this
finite CIG support-compression witness class is one. -/
theorem actual_support_witness_minimum_query_cardinality
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps : eps < 1 / 2) :
    ∃ optimal : Finset Cell,
      WitnessQuerySuccessful eps optimal ∧ optimal.card = 1 ∧
      ∀ queries : Finset Cell,
        WitnessQuerySuccessful eps queries → optimal.card ≤ queries.card := by
  refine ⟨cell2Queries, actual_support_cell2_query_suffices heps0, by simp [cell2Queries], ?_⟩
  intro queries hqueries
  have hmem : (2 : Cell) ∈ queries :=
    actual_support_query_requires_cell2 heps queries hqueries
  exact Finset.card_pos.mpr ⟨2, hmem⟩

end CIGAMF.P13.SupportCompressionCriticalWitnessTightening
