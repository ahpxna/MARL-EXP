import «LeanPaperCEndpointV1»

/-!
# Paper C (C3): the even breakpoint, at an actual law over rankings of `g_m`

`breakpoint_lower_even` (`LeanPaperCBreakpointV1`) closes the even side from three inputs:
the two-budget identity `hid`, the endpoint band `hband`, and attainment of the free value
`hfree`.  Those were stated about abstract `r1`, `rm`, `big`, so the theorem did not yet say
anything about a ranking law.  This module instantiates all three at the family's own base
ranking, so the conclusion is about `maxRegret` of an actual distribution over permutations
of `g_m`.

Nothing new is proved here, and that is the point -- the pieces already existed and were
never joined:

* `hid` comes from `hid_on_regret` at `gFamily_isEvenFamily`;
* `hband` comes from `hband_even_of_endpoint_band`, fed with `big_eq_sum_endpoints`,
  `gFamily_heavy_card` (the heavy set has exactly two members) and the two endpoint lower
  bounds `endpoint_first_lower`, `endpoint_last_lower`;
* `hfree` is the caller's -- it is the statement that the law attains the free value, which
  is what the breakpoint is the obstruction to.

The conclusion reads: a law over rankings of `g_m` that obeys the endpoint band at `eta` and
still attains the free value forces

    eta  >=  (m - 2) / (2 (m - 1)),

so below that band width the free value is unattainable.  That is `eta_*(m)` for even `m`.
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
`breakpoint_lower_even` is discharged at `g_m`; only the band and the attainment of the free
value remain, and those are the hypotheses the statement is about. -/
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
