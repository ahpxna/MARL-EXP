import Mathlib
import «LeanMarlRepairCalibrationV1»

/-!
# T2 debt: starvation with NONZERO allocation (the quantitative A-bridge on the needle class)

`LeanMarlRepairCalibrationV1.zero_allocation_impossible` only covers a protocol that never rolls
out some ambiguous repair.  Here the same per-repair lower bound is turned into cost statements
for protocols that DO roll it out, but rarely.

## WHAT IS PROVED

* `allocation_starvation` — if a protocol's expected rollouts on an ambiguous repair `T` are at
  most a fraction `ρ` of its expected total rollouts (null world), its total is at least
  `D / (ρ · β²/2)`, where `D = (1−α)log(1/α) − log 2`.
* `symmetric_design_cost` — a SYMMETRIC acquisition, one that rolls out every non-prefix k-set
  equally often in expectation (the natural design when nothing distinguishes the sets), must
  spend at least `(C(m,k) − 1) · D / (β²/2)`.  A protocol targeted at `Amb` needs only
  `|Amb| · ⌈8 log(|Amb|/α)/β²⌉` (`calibration_upper`).  The ratio is the starvation factor.

## WHAT THIS DOES NOT ESTABLISH

- That any particular proxy criterion is OPTIMISED by the symmetric design.  The statement is
  about the design, not about why a proxy would choose it.
- Anything outside the needle class of `LeanMarlRepairCalibrationV1`.
-/

namespace CIGAMF.P13.MarlStarvation

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperBPrivateQuery
open CIGAMF.P13.MarlEstimatedRevision CIGAMF.P13.MarlRepairCalibration

variable {m : ℕ}

/-- **Starvation with a nonzero allocation fraction.** -/
theorem allocation_starvation (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα1 : α ≤ 1)
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)})
    (T : Finset (Fin m)) (hT : T ∈ Amb g P k R β ε)
    (hcT : 1 - α ≤ (hist (rChan P) pol (needle β T) n).real
      {ω | Acc g P k R ε (needle β T) (out ω)})
    (ρ : ℝ≥0∞) (hρ : (∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) pol null0 n)
      ≤ ρ * costN (rChan P) pol null0 n) :
    ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2)
      ≤ ρ * costN (rChan P) pol null0 n * ENNReal.ofReal (β ^ 2 / 2) :=
  (per_repair_lower g P k R β ε α hP hTop pol n out hmeas hα hα1 h0 T hT hcT).trans
    (mul_le_mul_of_nonneg_right hρ bot_le)

/-- **A symmetric design pays for every k-set.** -/
theorem symmetric_design_cost (g : Fin m → ℝ) (P : Finset (Fin m)) (k R : ℕ) (β ε α : ℝ)
    (hP : P.card = k) (hTop : ∀ i ∈ P, ∀ j ∉ P, g j ≤ g i)
    (pol : Policy (Fin (NQ m))) (n : ℕ) (out : Hist (Fin (NQ m)) n → Finset (Fin m))
    (hmeas : ∀ S, MeasurableSet {ω | out ω = S}) (hα : 0 < α) (hα1 : α ≤ 1)
    (h0 : 1 - α ≤ (hist (rChan P) pol null0 n).real {ω | Acc g P k R ε null0 (out ω)})
    (T : Finset (Fin m)) (hT : T ∈ Amb g P k R β ε)
    (hcT : 1 - α ≤ (hist (rChan P) pol (needle β T) n).real
      {ω | Acc g P k R ε (needle β T) (out ω)})
    (hsym : ∀ S : Finset (Fin m), S.card = k → S ≠ P →
      (∫⁻ ω, cntQ (code S) n ω ∂hist (rChan P) pol null0 n)
        = ∫⁻ ω, cntQ (code T) n ω ∂hist (rChan P) pol null0 n) :
    ((((Finset.univ : Finset (Fin m)).powersetCard k).card - 1 : ℕ) : ℝ≥0∞)
        * ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2)
      ≤ costN (rChan P) pol null0 n * ENNReal.ofReal (β ^ 2 / 2) := by
  classical
  set F : Fin (NQ m) → ℝ≥0∞ := fun q => ∫⁻ ω, cntQ q n ω ∂hist (rChan P) pol null0 n with hF
  set D := ENNReal.ofReal ((1 - α) * Real.log (1 / α) - Real.log 2)
  set c := ENNReal.ofReal (β ^ 2 / 2)
  have hper := per_repair_lower g P k R β ε α hP hTop pol n out hmeas hα hα1 h0 T hT hcT
  set L := ((Finset.univ : Finset (Fin m)).powersetCard k).erase P with hL
  have hPmem : P ∈ (Finset.univ : Finset (Fin m)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hP⟩
  have hLcard : L.card = ((Finset.univ : Finset (Fin m)).powersetCard k).card - 1 :=
    Finset.card_erase_of_mem hPmem
  have hLeq : ∀ S ∈ L, F (code S) = F (code T) := by
    intro S hS
    obtain ⟨hSP, hSk⟩ := Finset.mem_erase.mp hS
    exact hsym S (Finset.mem_powersetCard.mp hSk).2 hSP
  calc ((((Finset.univ : Finset (Fin m)).powersetCard k).card - 1 : ℕ) : ℝ≥0∞) * D
      = ∑ _S ∈ L, D := by rw [Finset.sum_const, nsmul_eq_mul, hLcard]
    _ ≤ ∑ S ∈ L, F (code S) * c := Finset.sum_le_sum fun S hS => by rw [hLeq S hS]; exact hper
    _ = ∑ q ∈ L.image code, F q * c := by rw [Finset.sum_image (fun S _ T _ h => code_inj h)]
    _ ≤ ∑ q ∈ Finset.univ.filter (fun q => q ≠ code P), F q * c := by
        apply Finset.sum_le_sum_of_subset
        intro q hq
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h; exact (Finset.mem_erase.mp hS).1 (code_inj h)
    _ = costN (rChan P) pol null0 n * c := by
        rw [costN_eq_sum, Finset.sum_mul, rChan_dummy, Finset.sum_filter]
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases h : q = code P <;> simp [h, hF]

end CIGAMF.P13.MarlStarvation

#print axioms CIGAMF.P13.MarlStarvation.allocation_starvation
#print axioms CIGAMF.P13.MarlStarvation.symmetric_design_cost
