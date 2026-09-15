import Mathlib
import «LeanD6StrictRankOneM6ResponseSpansV1»
import «LeanD6ContrastRankPhaseDefinitionsV2»

/-!
# The m = 6 witness cell, and its strict Top-C separation

The decision cell is `S = {0,1,2}` against `T = {3,4,5}`.  The six extremal
action vectors recorded in the cell are the exact argmax/argmin points of the
retained residuals and of the responses; they are asserted here only as DATA,
and `ActiveDecisionCell.Valid` -- which is what pins them to the actual maxima
-- is deliberately NOT proved in this file.  It needs the loss layer.

What IS proved: the cell is a balanced complement, and Top-C is STRICT.  The
strictness is the whole point: the earlier m = 6 counterexample had all six
response spans equal, so its selected set came from an index-order tie-break and
it could only refute the non-strict claim.  Here the three selected coordinates
sit strictly above the other three, by exactly 1.
-/

namespace CIGAMF.P13.D6StrictRankOneM6StrictTopC

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6ContrastRankPhaseDefinitionsV2
open CIGAMF.P13.D6StrictRankOneM6Witness
open CIGAMF.P13.D6StrictRankOneM6ResponseSpans

def witnessSelected : Finset (Fin 6) := {0, 1, 2}
def witnessCompetitor : Finset (Fin 6) := {3, 4, 5}

/-- Argmax of the retained residual at `S = {0,1,2}`. -/
def witnessSelectedMax : Fin 6 → Fin 3 := ![0, 0, 0, 1, 1, 2]
/-- Argmin of the retained residual at `S = {0,1,2}`. -/
def witnessSelectedMin : Fin 6 → Fin 3 := ![1, 1, 1, 0, 0, 1]
/-- Argmax of the retained residual at `T = {3,4,5}`. -/
def witnessCompetitorMax : Fin 6 → Fin 3 := ![1, 1, 1, 0, 1, 0]
/-- Argmin of the retained residual at `T = {3,4,5}`. -/
def witnessCompetitorMin : Fin 6 → Fin 3 := ![0, 0, 0, 1, 1, 1]
/-- Per coordinate, the action attaining the maximal response.  Coordinate 5 is
the exception: its offset sits on action `2`, not action `1`. -/
def witnessResponseMax : Fin 6 → Fin 3 := ![1, 1, 1, 1, 1, 2]
/-- Per coordinate, the action attaining the minimal response. -/
def witnessResponseMin : Fin 6 → Fin 3 := ![0, 0, 0, 0, 0, 0]

def witnessCell : ActiveDecisionCell 5 (Fin 3) where
  q := cornerQ6
  selected := witnessSelected
  competitor := witnessCompetitor
  selectedMax := witnessSelectedMax
  selectedMin := witnessSelectedMin
  competitorMax := witnessCompetitorMax
  competitorMin := witnessCompetitorMin
  responseMax := witnessResponseMax
  responseMin := witnessResponseMin

theorem witnessCell_balanced : witnessCell.BalancedComplement := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/-- Strict Top-C: every selected coordinate has a strictly larger response span
than every unselected one.  `23 > 22`, margin exactly `1`. -/
theorem witnessCell_strictTopC : StrictTopC witnessCell witnessWorld := by
  intro i hi j hj
  have h0 := witnessResponse_span_zero
  have h1 := witnessResponse_span_one
  have h2 := witnessResponse_span_two
  have h3 := witnessResponse_span_three
  have h4 := witnessResponse_span_four
  have h5 := witnessResponse_span_five
  change osc (productResponse cornerQ6 witnessWorld j) <
    osc (productResponse cornerQ6 witnessWorld i)
  fin_cases i <;> fin_cases j <;>
    simp [witnessCell, witnessSelected] at hi hj ⊢ <;>
    simp only [h0, h1, h2, h3, h4, h5] <;>
    norm_num

end CIGAMF.P13.D6StrictRankOneM6StrictTopC
