import «LeanStructuralScalarChi5WitnessV1»

/-!
# Kernel-checked replacement for the ten `native_decide` steps of the χ≥5 witness

Historical note: before the 2026-09-27 audit, `LeanStructuralScalarChi5WitnessV1` proved ten arithmetic facts by
`native_decide`, a tactic this project rejects as a trust hole: it compiles the
proposition to machine code, runs it, and records the answer through the axiom
`Lean.ofReduceBool`.  Those original facts used the native evaluation trust path. The independent replacements
below were already kernel proofs; a new frozen gate must check the patched import closure.

The source witness now also uses kernel `decide`; its pre-audit bytes are preserved in legacy.
The imported source therefore no longer contains the ten prohibited tactic uses.
The old frozen smoke report remains FAIL and is not rewritten.

Nothing is deleted here.  This module re-proves the same ten statements about
the same definitions using kernel `decide`, so the corresponding axiom set is
`[propext, Classical.choice, Quot.sound]` with no `Lean.ofReduceBool`.

Scale of the kernel work: five closed evaluations, plus five quantifications
over `Finset (Fin 7)` -- 128 subsets, each a signed 7-term integer sum and one
`natAbs`.  That is 896 kernel integer additions in total, not a case explosion.
Each statement is a separate theorem so that a failure localises.
-/

namespace CIGAMF.P13.StructuralScalarChi5Kernel

open CIGAMF.P13.StructuralScalarChi5Witness

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The five closed evaluations -/

theorem opt1_abs_kernel : complementAbs7 opt1 = 1 := by decide
theorem opt2_abs_kernel : complementAbs7 opt2 = 0 := by decide
theorem opt3_abs_kernel : complementAbs7 opt3 = 1 := by decide
theorem opt4_abs_kernel : complementAbs7 opt4 = 2 := by decide
theorem opt5_abs_kernel : complementAbs7 opt5 = 0 := by decide

/-! ## The five uniqueness statements -/

theorem unique_abs1_kernel :
    ∀ S : Finset (Fin 7), S.card = 1 → complementAbs7 S ≤ 1 → S = opt1 := by
  decide

theorem unique_abs2_kernel :
    ∀ S : Finset (Fin 7), S.card = 2 → complementAbs7 S ≤ 0 → S = opt2 := by
  decide

theorem unique_abs3_kernel :
    ∀ S : Finset (Fin 7), S.card = 3 → complementAbs7 S ≤ 1 → S = opt3 := by
  decide

theorem unique_abs4_kernel :
    ∀ S : Finset (Fin 7), S.card = 4 → complementAbs7 S ≤ 2 → S = opt4 := by
  decide

theorem unique_abs5_kernel :
    ∀ S : Finset (Fin 7), S.card = 5 → complementAbs7 S ≤ 0 → S = opt5 := by
  decide

end CIGAMF.P13.StructuralScalarChi5Kernel
