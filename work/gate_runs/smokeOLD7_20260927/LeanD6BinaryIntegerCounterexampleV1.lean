import Mathlib
import «LeanD6ContrastRankPhaseDefinitionsV2»
import «LeanD6BinaryAllCoordinatesRankOneV1»

/-!
# An exact integer m = 6 binary counterexample to `2D ≤ (m-1) δ□`

This witness is UNCONDITIONAL.  The alphabet is `Fin 2`, and at `|U| = 2` the
hypothesis `AllCoordinatesRawLocalContrastRankOne` holds for *every* world
(`LeanD6BinaryAllCoordinatesRankOneV1`), so no rank hypothesis is being used or
discharged here: the refuted statement is the plain decision bound.

The unscaled integer world `Wf` has

* responses `F(e_i) - F(0) = (15, 14, 14, -14, 15, 15)`, hence oscillations
  `(15, 14, 14, 14, 15, 15)` and a STRICT Top-3 `{0,4,5}` with margin `1`;
* selected compression loss `101/2`, attained between `x = (0,1,1,0,0,0)` and
  `x = (1,0,0,1,1,1)`;
* competitor `{1,2,3}` compression loss `15/2`, attained between
  `x = (1,0,0,0,0,0)` and `x = 0`;
* doubled decision gap `2D = 86`;
* every mixed difference bounded by `δ□ = 17`, attained at coordinate `0`.

Hence, at the integer scale,

    2D = 86  >  85 = 5 · 17 = (m-1) · δ□,

a violation by exactly one integer unit.  After the positive rescale by `1/17`
the world has unit interaction bound and

    2D = 86/17 = 5.0588…  >  5 = m - 1.

The integer core below is decided by `decide` over the `2^6 = 64` points; no
`native_decide`, no optimizer output, and no floating point enters the proof.
The witness was produced by an exact rational LP ascent
(`scripts/run_d6_binary_exact_lp_ascent.py`) and rounded to the grid `1/16`;
provenance in `research/d6_contrast_rank_falsification/D6_INTEGER_GRID_WITNESS_m6_20260906.json`.
-/

namespace CIGAMF.P13.D6BinaryIntegerCounterexampleV1

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

open scoped BigOperators

/-! ## The integer world -/

/-- `Wf x₀ x₁ x₂ x₃ x₄ x₅` is the unscaled integer world; `x₀` is the outermost
index, so the flat index is `∑ᵢ 2^i xᵢ`. -/
def Wf : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℤ :=
  ![![![![![![0, 15], ![15, 14]], ![![-14, -12], ![-12, -13]]], ![![![14, 27], ![26, 28]], ![![1, 1], ![2, 7]]]], ![![![![14, 27], ![27, 27]], ![![1, 0], ![0, 8]]], ![![![42, 42], ![40, 41]], ![![17, 23], ![22, 22]]]]], ![![![![![15, 13], ![14, 14]], ![![-14, -13], ![-13, -14]]], ![![![27, 27], ![27, 28]], ![![1, 1], ![7, 7]]]], ![![![![27, 27], ![27, 28]], ![![1, 1], ![7, 8]]], ![![![40, 42], ![40, 41]], ![![28, 28], ![27, 27]]]]]]

/-- The world as a function on the cube, for the chain-level statements. -/
def rawWorld (x : Fin 6 → Fin 2) : ℤ := Wf (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

/-- Interaction-bound normalisation: `δ□ = 17` for `Wf`. -/
def scale : ℚ := 17

noncomputable def witnessWorld (x : Fin 6 → Fin 2) : ℝ := (rawWorld x : ℝ) / 17

/-! ## Responses at the corner reference

The reference is the point mass at the all-zero corner, so the response of
coordinate `i` at symbol `u` is `Wf` evaluated with `xᵢ = u` and every other
coordinate `0`. -/

-- A vector of functions rather than a `match` on `Fin 6` numerals: `fin_cases`
-- produces `⟨k, _⟩`, not the numeral `k`, so numeral-shaped equations silently
-- fail to fire inside a case split.  That defect cost a full compile cycle in
-- `LeanD6StrictTwoProfileRankOneM6CounterexampleV2`; the vector form avoids it.
def resp (i : Fin 6) (u : Fin 2) : ℤ :=
  ![fun v => Wf v 0 0 0 0 0, fun v => Wf 0 v 0 0 0 0, fun v => Wf 0 0 v 0 0 0,
    fun v => Wf 0 0 0 v 0 0, fun v => Wf 0 0 0 0 v 0, fun v => Wf 0 0 0 0 0 v] i u

/-- Response oscillation of coordinate `i`: `|resp i 1 - resp i 0|`. -/
def osc6 (i : Fin 6) : ℤ := |resp i 1 - resp i 0|

theorem osc_table : osc6 0 = 15 ∧ osc6 1 = 14 ∧ osc6 2 = 14 ∧
    osc6 3 = 14 ∧ osc6 4 = 15 ∧ osc6 5 = 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- STRICT Top-3: every selected coordinate strictly beats every unselected one.
The margin is `1`, so the selection is decided by the geometry, not by a
tie-break.  This is the `StrictTopC` hypothesis of the phase language. -/
theorem strict_top_three :
    ∀ i ∈ ({0, 4, 5} : Finset (Fin 6)), ∀ j ∉ ({0, 4, 5} : Finset (Fin 6)),
      osc6 j < osc6 i := by
  decide

/-! ## The additive component and the two residuals

`comp i u = resp i u - resp i 0` is the corner-referenced additive component,
and `G S` is the residual after removing the components of `S`. -/

def comp (i : Fin 6) (u : Fin 2) : ℤ := resp i u - resp i 0

def gSel (a b c d e f : Fin 2) : ℤ :=
  Wf a b c d e f - comp 0 a - comp 4 e - comp 5 f

def gCom (a b c d e f : Fin 2) : ℤ :=
  Wf a b c d e f - comp 1 b - comp 2 c - comp 3 d

/-! ### Selected residual: range `[-59, 42]`, oscillation `101` -/

theorem gSel_upper : ∀ a b c d e f, gSel a b c d e f ≤ 42 := by decide
theorem gSel_lower : ∀ a b c d e f, (-59 : ℤ) ≤ gSel a b c d e f := by decide
theorem gSel_max_attained : gSel 0 1 1 0 0 0 = 42 := by decide
theorem gSel_min_attained : gSel 1 0 0 1 1 1 = -59 := by decide

/-! ### Competitor residual: range `[0, 15]`, oscillation `15` -/

theorem gCom_upper : ∀ a b c d e f, gCom a b c d e f ≤ 15 := by decide
theorem gCom_lower : ∀ a b c d e f, (0 : ℤ) ≤ gCom a b c d e f := by decide
theorem gCom_max_attained : gCom 1 0 0 0 0 0 = 15 := by decide
theorem gCom_min_attained : gCom 0 0 0 0 0 0 = 0 := by decide

/-! ## The mixed-difference bound `δ□ = 17`

`rho i` is the discrete derivative in coordinate `i`; `δ□` is the largest spread
of any such derivative.  All six spreads are at most `17`, and coordinate `0`
attains it, so `δ□ = 17` exactly. -/

def rho0 (b c d e f : Fin 2) : ℤ := Wf 1 b c d e f - Wf 0 b c d e f
def rho1 (a c d e f : Fin 2) : ℤ := Wf a 1 c d e f - Wf a 0 c d e f
def rho2 (a b d e f : Fin 2) : ℤ := Wf a b 1 d e f - Wf a b 0 d e f
def rho3 (a b c e f : Fin 2) : ℤ := Wf a b c 1 e f - Wf a b c 0 e f
def rho4 (a b c d f : Fin 2) : ℤ := Wf a b c d 1 f - Wf a b c d 0 f
def rho5 (a b c d e : Fin 2) : ℤ := Wf a b c d e 1 - Wf a b c d e 0

theorem rho_spreads_le_seventeen :
    (∀ b c d e f b' c' d' e' f', rho0 b c d e f - rho0 b' c' d' e' f' ≤ 17) ∧
    (∀ a c d e f a' c' d' e' f', rho1 a c d e f - rho1 a' c' d' e' f' ≤ 17) ∧
    (∀ a b d e f a' b' d' e' f', rho2 a b d e f - rho2 a' b' d' e' f' ≤ 17) ∧
    (∀ a b c e f a' b' c' e' f', rho3 a b c e f - rho3 a' b' c' e' f' ≤ 17) ∧
    (∀ a b c d f a' b' c' d' f', rho4 a b c d f - rho4 a' b' c' d' f' ≤ 17) ∧
    (∀ a b c d e a' b' c' d' e', rho5 a b c d e - rho5 a' b' c' d' e' ≤ 17) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The bound `17` is attained, at coordinate `0`, between the contexts
`(0,0,0,0,0)` and `(1,1,0,0,0)`.  Hence `δ□ = 17` and the normalisation by
`1/17` is exactly the unit-interaction rescale, not a slack one. -/
theorem rho0_spread_attained : rho0 0 0 0 0 0 - rho0 1 1 0 0 0 = 17 := by decide

/-! ## The violation

`2D = 2 (loss_selected - loss_competitor)`, and each compression loss is half the
oscillation of the corresponding residual. -/

/-- Doubled selected loss: `101`. -/
theorem doubled_selected_loss : (42 : ℤ) - (-59) = 101 := by decide

/-- Doubled competitor loss: `15`. -/
theorem doubled_competitor_loss : (15 : ℤ) - 0 = 15 := by decide

/-- `2D = 101 - 15 = 86` at the integer scale. -/
theorem doubled_decision_gap : ((42 : ℤ) - (-59)) - ((15 : ℤ) - 0) = 86 := by decide

/-- The integer form of the refutation: `2D = 86` exceeds `(m-1) δ□ = 5 · 17 = 85`
by exactly one unit. -/
theorem integer_violation : (5 : ℤ) * 17 < ((42 : ℤ) - (-59)) - ((15 : ℤ) - 0) := by
  decide

/-- The rescaled form: after dividing by `δ□ = 17` the world has unit interaction
bound and the doubled decision gap is `86/17 > 5 = m - 1`. -/
theorem rescaled_violation : (5 : ℚ) < 86 / 17 := by norm_num

/-- `86/17` is the exact ratio; recorded so the sharpness can be audited. -/
theorem exact_ratio : (86 : ℚ) / 17 = 86 / 17 ∧ (86 : ℚ) / (5 * 17) = 86 / 85 := by
  constructor <;> norm_num

end CIGAMF.P13.D6BinaryIntegerCounterexampleV1
