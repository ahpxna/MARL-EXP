import «LeanPaperCEndpointV1»

/-!
# Paper C (C3): the even breakpoint, at an actual law over rankings of `g_m`

`breakpoint_lower_even` (`LeanPaperCBreakpointV1`) closes the even side from three inputs:
the two-budget identity `hid`, the endpoint band `hband`, and attainment of the free value
`hfree`.  Those were stated about abstract `r1`, `rm`, `big`. This module instantiates the
endpoint identity and band at the concrete family. Its remaining `hfree` is an equality of
TWO ENDPOINT EXPECTATIONS, not an assumption that `maxRegret` attains the free optimum.
Accordingly this is a conditional endpoint obstruction, not a theorem identifying the
breakpoint or the all-budget optimum.

`LeanPaperCBandValueBridgeV1` supplies the unconditional quantitative lower bound on
`maxRegret` and `Vm` from membership in `FeasibleAt`, with no endpoint-equality premise.
Attainment of the breakpoint requires a separate explicit law and is not proved here.
-/

namespace CIGAMF.P13.PaperCBreak3

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCBand
open CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint

/-- **(C3, even) The breakpoint at an actual ranking law.**  Every input of
`breakpoint_lower_even` is discharged at `g_m`; only the band and the stipulated endpoint-expectation
equality remain, and those are the hypotheses the statement is about. -/
theorem breakpoint_even_at_ranking_law {R : Type*} [Fintype R]
    (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 0)
    (P : R → ℝ) (perm : R → Equiv.Perm (Fin (n + 2))) (D η : ℝ) (hD : 0 < D)
    (hsum : ∑ x, P x = 1)
    (hbandfirst : ∀ i ∈ heavySet (gFamily (n + 2)),
      1 / ((n : ℝ) + 2) - η / ((n : ℝ) + 2)
        ≤ ∑ x, P x * inPrefixInd (perm x) 1 i)
    (hbandlast : ∀ i ∈ heavySet (gFamily (n + 2)),
      ∑ x, P x * inPrefixInd (perm x) (n + 2 - 1) i
        ≤ (((n : ℝ) + 2) - 1) / ((n : ℝ) + 2) + η / ((n : ℝ) + 2))
    (hfree : ∑ x, P x * (regret (gFamily (n + 2)) (perm x) D 1
        + regret (gFamily (n + 2)) (perm x) D (n + 2 - 1))
      = 4 / (D * (((n : ℝ) + 2) - 1))) :
    (((n : ℝ) + 2) - 2) / (2 * (((n : ℝ) + 2) - 1)) ≤ η := by
  classical
  have hm2 : 1 < n + 2 := by omega
  have hmpos : 0 < n + 2 := by omega
  have hmR : (2 : ℝ) < (n : ℝ) + 2 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine breakpoint_lower_even P
    (fun x => regret (gFamily (n + 2)) (perm x) D 1)
    (fun x => regret (gFamily (n + 2)) (perm x) D (n + 2 - 1))
    (fun x => heavy (rankOf (gFamily (n + 2)) (perm x) ⟨0, hmpos⟩)
      + heavy (rankOf (gFamily (n + 2)) (perm x) ⟨n + 2 - 1, by omega⟩))
    ((n : ℝ) + 2) D η hmR hD
    (hid_on_regret hm2 (by omega) (gFamily (n + 2))
      (gFamily_isEvenFamily n hn hpar) perm D (ne_of_gt hD))
    ?_ hfree
  exact hband_even_of_endpoint_band P
    (fun i x => if i = perm x ⟨0, hmpos⟩ then (1 : ℝ) else 0)
    (fun i x => if i = perm x (⟨n + 2 - 1, by omega⟩ : Fin (n + 2)) then (1 : ℝ) else 0)
    _ (heavySet (gFamily (n + 2))) ((n : ℝ) + 2) η (by linarith)
    (by rw [gFamily_heavy_card n hn]; norm_num)
    (fun x => big_eq_sum_endpoints (gFamily (n + 2)) hmpos (perm x))
    (fun i hi => endpoint_first_lower hmpos P perm i ((n : ℝ) + 2) η (by linarith)
      (hbandfirst i hi))
    (fun i hi => endpoint_last_lower hmpos P perm i ((n : ℝ) + 2) η (by linarith) hsum
      (hbandlast i hi))

/-! ## Audit -/

#print axioms breakpoint_even_at_ranking_law

end CIGAMF.P13.PaperCBreak3
