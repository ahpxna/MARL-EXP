import «LeanSupportMultiTipGeometryV1»

/-! # R4: the positive side of passive certification — decision-relevant mass.

`PASSIVE_DECISION_MASS_PROOF.md` closes the NEGATIVE half: with an anchor of
mass `1-eta` and a dangerous tip of mass `eta`, no passive uniformly correct
procedure can stop at the anchor-only world, because `eta` may be pushed below
any transcript-based threshold. So certification needs a hypothesis on the mass
of the dangerous region, and the open item was the POSITIVE condition: what has
to be assumed, and how many samples does it buy?

The condition should constrain only the region that can make a decision wrong —
NOT every support point. In the multi-tip geometry that region is pinned exactly
by `zero_radius_iff`: decision `j` is safe in world `W` iff `j ∉ W`. So the
decision-relevant region for `j` is the single tip `j`, and the assumption needed
is a lower bound on the mass of each PRESENT tip, not on every point of the
space.

WHAT IS PROVED HERE.

* `safe_of_unseen` — soundness, against the real `selectedRadius`: if the sample
  has caught every present tip, then every tip missing from the sample is a
  genuinely safe decision. No probability involved.
* `unsafe_of_seen` — the matching direction: a tip that WAS seen is genuinely
  unsafe. Together the two say the observed classification is exact, not merely
  conservative.
* `exists_certified_safe` — such a `j` exists whenever some tip is unseen.
* `one_minus_le_exp_neg_pow` — `(1-gamma)^N ≤ exp (-(gamma*N))`.
* `sample_size_suffices` — if `log (m/delta) ≤ gamma*N` then
  `m*(1-gamma)^N ≤ delta`: the union-bounded miss budget.

Read together: assume every present tip carries mass at least `gamma`. A tip is
missed by `N` i.i.d. draws with probability at most `(1-gamma)^N`; union over at
most `m` tips gives `m*(1-gamma)^N ≤ delta` once `N ≥ log(m/delta)/gamma`. On
that event the sample is complete, and `safe_of_unseen` turns it into a
certified safe decision. Sample size `O(log(m/delta)/gamma)` — with `gamma` the
decision-relevant mass, which is exactly the quantity the negative theorem
shows must be controlled.

WHAT THIS DOES NOT ESTABLISH.

- The probabilistic step is NOT formalised. That a set of mass `>= gamma` is
  missed by `N` i.i.d. draws with probability at most `(1-gamma)^N`, and the
  union bound over tips, are stated here only as the reading of
  `one_minus_le_exp_neg_pow` and `sample_size_suffices`, which are inequalities
  between real numbers. No measure space, product measure or sampling process
  appears in any statement below.
- `safe_of_unseen` assumes the sample is complete (`W ⊆ S`). It does not say the
  learner KNOWS completeness; that is precisely what the mass assumption buys,
  and only with probability `1 - delta`.
- This is the multi-tip geometry with one tip per decision. Nothing here covers
  heterogeneous tips, correlated supports, or a danger region larger than a
  single point.
- The negative theorem is unaffected: without a mass lower bound the hypothesis
  of `sample_size_suffices` is unusable, since `gamma` may be arbitrarily small.
-/

namespace CIGAMF.P13.SupportPassiveDecisionMass
open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportUnboundedObstruction
open CIGAMF.P13.SupportMultiTipGeometry
noncomputable section

variable {m : ℕ}

/-! ## Soundness against the real radius -/

/-- A tip absent from a COMPLETE sample is a genuinely safe decision. -/
theorem safe_of_unseen (hm : 2 ≤ m) (W S : Finset (Fin m)) (hcomplete : W ⊆ S)
    (j : Fin m) (hj : j ∉ S) : selectedRadius (components W) {j} = 0 := by
  rw [zero_radius_iff hm]
  exact fun h => hj (hcomplete h)

/-- A tip present in the sample is genuinely unsafe: the observed classification
is exact, not one-sided. -/
theorem unsafe_of_seen (hm : 2 ≤ m) (W S : Finset (Fin m)) (hSW : S ⊆ W)
    (j : Fin m) (hj : j ∈ S) : selectedRadius (components W) {j} ≠ 0 := by
  intro h
  rw [zero_radius_iff hm] at h
  exact h (hSW hj)

/-- On a complete sample the certified-safe set is exactly the safe set. -/
theorem certification_exact (hm : 2 ≤ m) (W S : Finset (Fin m)) (hSW : S ⊆ W)
    (hcomplete : W ⊆ S) (j : Fin m) :
    selectedRadius (components W) {j} = 0 ↔ j ∉ S := by
  constructor
  · intro h
    rw [zero_radius_iff hm] at h
    exact fun hjS => h (hSW hjS)
  · exact safe_of_unseen hm W S hcomplete j

/-- Whenever some tip is unseen, a certified safe decision exists. -/
theorem exists_certified_safe (hm : 2 ≤ m) (W S : Finset (Fin m)) (hcomplete : W ⊆ S)
    (hne : S ≠ univ) : ∃ j, j ∉ S ∧ selectedRadius (components W) {j} = 0 := by
  have hnot : ¬ ∀ j : Fin m, j ∈ S := fun h => hne (Finset.eq_univ_iff_forall.mpr h)
  push_neg at hnot
  obtain ⟨j, hj⟩ := hnot
  exact ⟨j, hj, safe_of_unseen hm W S hcomplete j hj⟩

/-! ## The miss budget -/

/-- `(1-gamma)^N ≤ exp (-(gamma*N))`. -/
theorem one_minus_le_exp_neg_pow (gamma : ℝ) (h0 : 0 ≤ gamma) (h1 : gamma ≤ 1) (N : ℕ) :
    (1-gamma)^N ≤ Real.exp (-(gamma*(N:ℝ))) := by
  have hstep : 1-gamma ≤ Real.exp (-gamma) := by
    have := Real.add_one_le_exp (-gamma)
    linarith
  have hpow : (1-gamma)^N ≤ (Real.exp (-gamma))^N :=
    pow_le_pow_left₀ (by linarith) hstep N
  have hexp : (Real.exp (-gamma))^N = Real.exp (-(gamma*(N:ℝ))) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rwa [hexp] at hpow

/-- Union-bounded miss budget: `N ≥ log(m/delta)/gamma` samples leave total miss
mass at most `delta`. -/
theorem sample_size_suffices (gamma delta : ℝ) (M N : ℕ)
    (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1) (hd : 0 < delta) (hM : 0 < M)
    (hN : Real.log ((M:ℝ)/delta) ≤ gamma*(N:ℝ)) :
    (M:ℝ)*(1-gamma)^N ≤ delta := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have hratio : 0 < (M:ℝ)/delta := by positivity
  have hstep := one_minus_le_exp_neg_pow gamma hg hg1 N
  have hmono : Real.exp (-(gamma*(N:ℝ))) ≤ Real.exp (-Real.log ((M:ℝ)/delta)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hlog : Real.exp (-Real.log ((M:ℝ)/delta)) = delta/(M:ℝ) := by
    rw [Real.exp_neg, Real.exp_log hratio, inv_div]
  have hchain : (1-gamma)^N ≤ delta/(M:ℝ) := by
    rw [← hlog]; exact hstep.trans hmono
  have := mul_le_mul_of_nonneg_left hchain hMpos.le
  rwa [mul_div_cancel₀ _ (ne_of_gt hMpos)] at this

#print axioms safe_of_unseen
#print axioms unsafe_of_seen
#print axioms certification_exact
#print axioms exists_certified_safe
#print axioms one_minus_le_exp_neg_pow
#print axioms sample_size_suffices

end
end CIGAMF.P13.SupportPassiveDecisionMass
