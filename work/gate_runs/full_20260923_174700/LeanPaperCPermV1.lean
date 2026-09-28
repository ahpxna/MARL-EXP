import «LeanPaperCLowerZeroV1»

/-!
# Paper C: equal weight-counts give a permutation, and the wrapper that needs it

`Vm_eq_at_zero` reduced C-H1's even side to exhibiting ONE law feasible at `eta = 0` whose
value is `4/(m(m+4))`.  `LeanPaperCUniformV1` proves the type counts of the flat-augmented
flipped mixture are exactly uniform and `evenMixtureFlipped_value_at_D` computes its value,
so the arithmetic is done.  What was missing is the step that makes it a law over
PERMUTATIONS of `g_m` rather than over a list of weight vectors: each ranking in the mixture
has to BE `g_m` composed with a permutation.

That step is a general fact and it is proved here.  Two rankings with the same number of
positions carrying each weight are related by a permutation -- match the fibres weight by
weight, exactly as `matchPerm` does for type sequences.  `permOfCountEq` builds it and
`rankOf_permOfCountEq` is the identity `rankOf g sigma = f`.

`feasible_of_rearrangements` is then the wrapper: a finite family of rankings, each a
rearrangement of `g_m`, together with weights, gives a law over permutations whose regret at
each budget is the family's own excess average.  Feeding it the band and value computations
gives the witness `Vm_eq_at_zero` asks for; the two hypotheses it still takes are those
computations, quoted at the mixture rather than re-proved.
-/

namespace CIGAMF.P13.PaperCPerm

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCValueSet
open CIGAMF.P13.PaperCLowerZero

variable {m : ℕ}

/-! ## Equal counts give a permutation -/

open scoped Classical in
/-- **The permutation matching two rankings with the same weight-counts.**  Fibre by fibre,
weight by weight; the same construction as `matchPerm`, with the weight playing the role of
the type. -/
noncomputable def permOfCountEq (f g : Ranking m)
    (h : ∀ w : ℝ, Fintype.card {i : Fin m // f i = w}
      = Fintype.card {j : Fin m // g j = w}) : Equiv.Perm (Fin m) :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (fun w => Fintype.equivOfCardEq (h w))).trans
      (Equiv.sigmaFiberEquiv g))

open scoped Classical in
/-- **And it carries `g` onto `f`.** -/
theorem permOfCountEq_apply (f g : Ranking m)
    (h : ∀ w : ℝ, Fintype.card {i : Fin m // f i = w}
      = Fintype.card {j : Fin m // g j = w}) (i : Fin m) :
    g (permOfCountEq f g h i) = f i := by
  have hh := ((Fintype.equivOfCardEq (h (f i))) ⟨i, rfl⟩).2
  simpa [permOfCountEq, Equiv.sigmaFiberEquiv, Equiv.sigmaCongrRight] using hh

open scoped Classical in
/-- **The ranking the permutation names is the one we started from.**  This is the step that
turns a weight vector into a member of the law's own index set. -/
theorem rankOf_permOfCountEq (f g : Ranking m)
    (h : ∀ w : ℝ, Fintype.card {i : Fin m // f i = w}
      = Fintype.card {j : Fin m // g j = w}) :
    rankOf g (permOfCountEq f g h) = f := by
  funext i
  exact permOfCountEq_apply f g h i

/-! ## The wrapper -/

open scoped Classical in
/-- **A family of rearrangements induces a law over permutations.**  Given rankings
`r x`, each with the same weight-counts as `g`, the permutations `sigma x` they name satisfy
`rankOf g (sigma x) = r x`, so every regret, band and value statement about the FAMILY is
literally a statement about the LAW.  This is the bridge `Vm_eq_at_zero` was missing. -/
noncomputable def permFamily {R : Type*} (g : Ranking m) (r : R → Ranking m)
    (hcount : ∀ x, ∀ w : ℝ, Fintype.card {i : Fin m // r x i = w}
      = Fintype.card {j : Fin m // g j = w}) : R → Equiv.Perm (Fin m) :=
  fun x => permOfCountEq (r x) g (hcount x)

open scoped Classical in
theorem permFamily_rankOf {R : Type*} (g : Ranking m) (r : R → Ranking m)
    (hcount : ∀ x, ∀ w : ℝ, Fintype.card {i : Fin m // r x i = w}
      = Fintype.card {j : Fin m // g j = w}) (x : R) :
    rankOf g (permFamily g r hcount x) = r x :=
  rankOf_permOfCountEq (r x) g (hcount x)

open scoped Classical in
/-- **The law's regret at each budget is the family's own excess average.**  Nothing new is
computed: the identity `rankOf g (sigma x) = r x` moves the corpus's excess computations
onto the law. -/
theorem regret_of_permFamily {R : Type*} [Fintype R] (g : Ranking m) (r : R → Ranking m)
    (hcount : ∀ x, ∀ w : ℝ, Fintype.card {i : Fin m // r x i = w}
      = Fintype.card {j : Fin m // g j = w})
    (P : R → ℝ) (D : ℝ) (k : ℕ) :
    (∑ x, P x * regret g (permFamily g r hcount x) D k)
      = ∑ x, P x * (excess (r x) k / D) := by
  refine Finset.sum_congr rfl (fun x _ => ?_)
  unfold regret
  rw [permFamily_rankOf g r hcount x]

open scoped Classical in
/-- **(C-H1's witness, assembled.)**  A family of rearrangements of `g_m` whose per-item
marginals are exactly uniform and whose excess average is `4/(m(m+4))` at every budget gives
a law that is feasible at `eta = 0` and has that value, which is exactly what
`Vm_eq_at_zero` asks for.  The two hypotheses are the computations of
`LeanPaperCUniformV1` and `evenMixtureFlipped_value_at_D`, quoted at the mixture. -/
theorem witness_for_Vm_eq_at_zero {R : Type*} [Fintype R] (g : Ranking m)
    (r : R → Ranking m)
    (hcount : ∀ x, ∀ w : ℝ, Fintype.card {i : Fin m // r x i = w}
      = Fintype.card {j : Fin m // g j = w})
    (P : R → ℝ) (hnn : ∀ x, 0 ≤ P x) (hsum : ∑ x, P x = 1)
    (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hband : ∀ (k : ℕ), k ≤ m → ∀ i : Fin m,
      (∑ x, P x * inPrefixInd (permFamily g r hcount x) k i) = (k : ℝ) / (m : ℝ))
    (hvalue : ∀ k ∈ budgets,
      (∑ x, P x * (excess (r x) k / ((m : ℝ) + 4))) = 4 / ((m : ℝ) * ((m : ℝ) + 4))) :
    P ∈ FeasibleAt (permFamily g r hcount) (0 : ℝ) ∧
      maxRegret P g (permFamily g r hcount) ((m : ℝ) + 4) budgets hne
        = 4 / ((m : ℝ) * ((m : ℝ) + 4)) := by
  constructor
  · refine ⟨hnn, hsum, fun k hk i => ?_⟩
    rw [hband k hk i, sub_self, abs_zero]
    simp
  · unfold maxRegret
    have hterm : ∀ k ∈ budgets,
        (∑ x, P x * regret g (permFamily g r hcount x) ((m : ℝ) + 4) k)
          = 4 / ((m : ℝ) * ((m : ℝ) + 4)) := by
      intro k hk
      rw [regret_of_permFamily g r hcount P ((m : ℝ) + 4) k]
      exact hvalue k hk
    refine le_antisymm (Finset.sup'_le hne _ (fun k hk => le_of_eq (hterm k hk))) ?_
    obtain ⟨k0, hk0⟩ := hne
    rw [← hterm k0 hk0]
    exact Finset.le_sup' (fun k => ∑ x, P x * regret g (permFamily g r hcount x)
      ((m : ℝ) + 4) k) hk0

/-! ## Audit -/

#print axioms permOfCountEq_apply
#print axioms rankOf_permOfCountEq
#print axioms permFamily_rankOf
#print axioms regret_of_permFamily
#print axioms witness_for_Vm_eq_at_zero

end CIGAMF.P13.PaperCPerm
