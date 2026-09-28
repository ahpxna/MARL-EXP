import «LeanPaperCEndpointLawV1»

/-!
# Paper C: stability, instantiated at the family

`trueValue_stable` (`LeanPaperCStabilityEndgameV1`) is the general statement: for ARBITRARY
real weights `g, g'` whose normalisers are at least `d > 0`, with the per-budget baseline
recomputed for each and the feasible item-band set held fixed,

    |V(g) - V(g')| <= 3 ||g - g'||_1 / d.

A general theorem is not yet a statement about the paper's object.  This module makes the
join: on `g_m` the physical, normalised value `trueValue` over the interior budgets IS the
paper's `value m eta` (`trueValue_family`, through the unconditional baseline identification
of `LeanPaperCBaselineAttainV1`), and the perturbation bound therefore controls how far the
TRUE optimum of any perturbed weight vector can sit from the exact law proved for `g_m`.

For even `m` that exact law is the whole frontier, so `even_frontier_robust` bounds the
perturbed optimum's distance from `max(2/((m+4)(m-1)), 4(1-eta)/(m(m+4)))`.  This is a
Lipschitz envelope, uniform over perturbations; it is not a claim that the price survives
at any particular scale, and a search that fails to find a destructive perturbation is not
evidence of a larger radius.
-/

namespace CIGAMF.P13.PaperCStabilityFamily

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCFrontier CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCBaselineAttain CIGAMF.P13.PaperCEndpointLaw

/-- The interior budgets `1, ..., m-1`, indexed as `trueValue` indexes them. -/
def interiorK (m : ℕ) : Finset (Fin (m + 1)) :=
  univ.filter (fun k => 1 ≤ k.val ∧ k.val ≤ m - 1)

theorem interiorK_nonempty (m : ℕ) (hm : 2 ≤ m) : (interiorK m).Nonempty :=
  ⟨⟨1, by omega⟩, by simp [interiorK]; omega⟩

/-- **On the family, the physical objective IS the paper's objective.** -/
theorem trueObjective_family (m : ℕ) (hm : 3 ≤ m) (P : Equiv.Perm (Fin m) → ℝ) :
    trueObjective (gFamily m) P (interiorK m) (interiorK_nonempty m (by omega))
      = objective m (by omega) P := by
  have hid : ∀ σ : Equiv.Perm (Fin m), ∀ k : Fin (m + 1), 1 ≤ k.val → k.val ≤ m - 1 →
      normalizedRegret (gFamily m) σ k = regret (gFamily m) σ (denom m) k.val :=
    fun σ k hk1 hk => family_regret_identification_unconditional m hm σ k hk1 (by omega)
  unfold trueObjective objective maxRegret
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun k hk => ?_
    have hk' : 1 ≤ k.val ∧ k.val ≤ m - 1 := by simpa [interiorK] using hk
    rw [Finset.sum_congr rfl (fun σ _ => by rw [hid σ k hk'.1 hk'.2])]
    exact Finset.le_sup' (fun k => ∑ σ, P σ * regret (gFamily m) (id σ) (denom m) k)
      (by simp [budgets]; omega)
  · refine Finset.sup'_le _ _ fun k hk => ?_
    have hk' : 1 ≤ k ∧ k ≤ m - 1 := by simpa [budgets] using hk
    have hmem : (⟨k, by omega⟩ : Fin (m + 1)) ∈ interiorK m := by
      simp [interiorK]; omega
    have := Finset.le_sup' (fun k => ∑ σ, P σ * normalizedRegret (gFamily m) σ k) hmem
    rw [Finset.sum_congr rfl (fun σ _ => by rw [hid σ ⟨k, by omega⟩ hk'.1 hk'.2])] at this
    exact this

/-- **On the family, the physical value IS the paper's value.** -/
theorem trueValue_family (m : ℕ) (hm : 3 ≤ m) (η : ℝ) :
    trueValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
      = value m (by omega) η := by
  unfold trueValue value Vm
  have hfun : (fun P => trueObjective (gFamily m) P (interiorK m)
      (interiorK_nonempty m (by omega)))
      = fun P => maxRegret P (gFamily m) id (denom m) (budgets m)
          (budgets_nonempty m (by omega)) :=
    funext fun P => trueObjective_family m hm P
  rw [hfun]

/-- **The perturbed TRUE optimum stays within the Lipschitz envelope of the family's exact
value**, for any real weights `g'` whose normaliser is at least `d`. -/
theorem family_value_robust (m : ℕ) (hm : 3 ≤ m) (g' : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (d : ℝ) (hd : 0 < d) (hdg : d ≤ (m : ℝ) + 4) (hg' : d ≤ normMass g') :
    |trueValue g' η (interiorK m) (interiorK_nonempty m (by omega)) - value m (by omega) η|
      ≤ 3 * l1 (gFamily m) g' / d := by
  haveI : NeZero m := ⟨by omega⟩
  have h := trueValue_stable (gFamily m) g' η hη (interiorK m)
    (interiorK_nonempty m (by omega)) d hd (by rw [normMass_gFamily m hm]; exact hdg) hg'
  rw [trueValue_family m hm η, abs_sub_comm] at h
  exact h

/-- **The even frontier, robustly**: the true optimum of any perturbation `g'` of `g_m` lies
within `3 ||g_m - g'||_1 / d` of the exact frontier. -/
theorem even_frontier_robust (m : ℕ) (hm : 4 ≤ m) (heven : Even m) (g' : Fin m → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (d : ℝ) (hd : 0 < d) (hdg : d ≤ (m : ℝ) + 4) (hg' : d ≤ normMass g') :
    |trueValue g' η (interiorK m) (interiorK_nonempty m (by omega))
        - max (freeValue m) (4 * (1 - η) / ((m : ℝ) * denom m))|
      ≤ 3 * l1 (gFamily m) g' / d := by
  have h := family_value_robust m (by omega) g' η hη d hd hdg hg'
  rw [even_frontier_all m hm heven η hη] at h
  exact h

#print axioms trueObjective_family
#print axioms trueValue_family
#print axioms family_value_robust
#print axioms even_frontier_robust

end CIGAMF.P13.PaperCStabilityFamily
