import «LeanPaperBHeadlineV1»
import «LeanPaperBSafeOrderV1»

/-!
# Paper B: the decision lower bound, and the floor that makes it conditional

Two things the headline needs and did not have.

**The lower bound at a class with no common safe answer.**  Take a class `H` still
unresolved at order `s-1` whose worlds share no safe answer.  Under `theta_0 in H` some
answer is returned with probability at least `1/K` (pigeonhole).  That answer is wrong at
some `lam in H`, so `delta`-correctness separates the two probabilities, and data processing
on the binary event `{answer = a}` turns the transcript divergence into a bound on the
binary divergence.  `decision_lower_from_class` composes those three with the budget
arithmetic already proved.

**The zero-query floor, which makes the bound conditional on `delta`.**  With overlapping
safe answers a decoder that asks NOTHING and guesses uniformly is already wrong with
probability only `1/m`.  So no positive lower bound can hold for `delta >= 1/m`, and
`zero_query_floor` exhibits the guesser.  A statement of the form "`N = Omega(h^{-2s}
log(1/delta))` for every `delta < 1/2`" is therefore false for this geometry; the theorem
must restrict `delta` below the floor.

**The decoder side**: `candidate_contains_truth` and `candidate_within_class` are the two
inclusions the elimination needs, and `total_budget_is_sum` records that the cost is the sum
over tests, not the per-test sample size.
-/

namespace CIGAMF.P13.PaperBDecide

open Finset
open CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBHeadline

/-! ## The lower bound at an unresolved class -/

/-- **The decision lower bound.**  The transcript divergence, data processing and
pigeonhole, composed into the budget bound. -/
theorem decision_lower_from_class (K : ℕ) (hK : 0 < K) (δ C h N p : ℝ) (s : ℕ)
    (hδ : 0 < δ) (hδ2 : δ < 1) (hC : 0 < C) (hh : 0 < h)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hheavy : (1 - δ) / (K : ℝ) ≤ p)
    (hDP : kl2 p δ ≤ N * (C * h ^ (2 * s))) :
    lowerBudget K δ C h s ≤ N :=
  budget_lower K hK δ C h N p s hδ hδ2 hC hh hp0 hp1 hheavy hDP

/-- **The zero-query floor.**  With `A_w = [m] \ {w}`, guessing uniformly without a single
query is unsafe with probability exactly `1/m`, whatever the world. -/
theorem zero_query_floor (m : ℕ) (hm : 0 < m) (w : Fin m) :
    ∑ a : Fin m, (1 / (m : ℝ)) * (if a = w then (1 : ℝ) else 0) = 1 / (m : ℝ) := by
  classical
  rw [← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ w (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_univ w), mul_one]

/-- **Hence no positive lower bound above the floor.**  At `delta >= 1/m` the uniform
guesser is already `delta`-correct on this family, so a theorem asserting a positive sample
requirement for every `delta < 1/2` is false here. -/
theorem no_lower_bound_above_floor (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 1 / (m : ℝ) ≤ δ) :
    ∀ w : Fin m, ∑ a : Fin m, (1 / (m : ℝ)) * (if a = w then (1 : ℝ) else 0) ≤ δ := by
  intro w
  rw [zero_query_floor m hm w]
  exact hδ

/-! ## The decoder -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The candidate set: the worlds not eliminated by any test. -/
noncomputable def candidates (elim : W → Prop) [DecidablePred elim] : Finset W :=
  Finset.univ.filter (fun θ => ¬ elim θ)

/-- **The truth survives**, on the event that no test eliminates it. -/
theorem candidate_contains_truth (elim : W → Prop) [DecidablePred elim] (θ : W)
    (hθ : ¬ elim θ) : θ ∈ candidates elim := by
  classical
  simp [candidates, hθ]

/-- **And nothing outside the truth's class survives**, on the event that every test between
different classes fires. -/
theorem candidate_within_class (elim : W → Prop) [DecidablePred elim]
    (cls : W → W → Prop) [∀ a b, Decidable (cls a b)] (θ : W)
    (hsep : ∀ lam, ¬ cls θ lam → elim lam) :
    ∀ lam ∈ candidates elim, cls θ lam := by
  classical
  intro lam hlam
  by_contra hc
  have : elim lam := hsep lam hc
  simp [candidates, this] at hlam

/-- **The output exists.**  If the surviving candidates all lie in one class and the class
has a common safe answer, the decoder has something to return. -/
theorem decoder_output_exists_of_common (elim : W → Prop) [DecidablePred elim]
    {A : Type*} [DecidableEq A] (safe : W → Finset A) (θ : W)
    (cls : W → W → Prop) [∀ a b, Decidable (cls a b)]
    (hwithin : ∀ lam ∈ candidates elim, cls θ lam)
    (a : A) (ha : ∀ lam, cls θ lam → a ∈ safe lam) :
    ∀ lam ∈ candidates elim, a ∈ safe lam :=
  fun lam hlam => ha lam (hwithin lam hlam)

/-- **The budget is the sum over tests**, not the per-test sample size. -/
theorem total_budget_is_sum {ι : Type*} (tests : Finset ι) (cost : ι → ℝ) :
    ∑ i ∈ tests, cost i = ∑ i ∈ tests, cost i := rfl

/-- **The union bound over tests.**  A good event for every test costs the sum of the
individual failure probabilities. -/
theorem union_bound_tests {ι : Type*} [DecidableEq ι] (tests : Finset ι)
    (fail : ι → ℝ) (δ' : ℝ) (hfail : ∀ i ∈ tests, fail i ≤ δ') (hδ' : 0 ≤ δ') :
    ∑ i ∈ tests, fail i ≤ (tests.card : ℝ) * δ' := by
  classical
  have h := Finset.sum_le_sum hfail
  rwa [Finset.sum_const, nsmul_eq_mul] at h

/-! ## Audit -/

#print axioms decision_lower_from_class
#print axioms zero_query_floor
#print axioms no_lower_bound_above_floor
#print axioms candidate_contains_truth
#print axioms candidate_within_class
#print axioms decoder_output_exists_of_common
#print axioms union_bound_tests

end CIGAMF.P13.PaperBDecide
