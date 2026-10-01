import «LeanPaperCEndpointV1»
import «LeanPaperCInstantiationV1»
import «LeanPaperCBreakpointV1»

/-!
# Paper C: the generic value lemmas, instantiated at the paper's own feasible set

`value_le_of_pointwise`, `value_stable_of_pointwise` and `max_stable_of_pointwise` of
`LeanPaperCBreakpointV1` are stated for an abstract feasible set `F` and abstract objectives
`f, g`.  `CLAIMS.md` recorded the residual honestly: they were never instantiated at Paper
C's own band-feasible set and at `V_m(eta)`, so they licensed nothing about the paper's
value.  This module writes those objects down and does the instantiation.

* `FeasibleAt` -- the laws over permutations whose per-item retained marginals lie inside
  the band at `eta`.  This is the paper's feasible set, not a stand-in.
* `Vm` -- the infimum of `maxRegret` over it, which is `V_m(eta)`.
* `maxRegret_nonneg`, `Vm_bddBelow` -- the side conditions the generic lemmas ask for, proved
  from `excess_nonneg` rather than assumed.
* `Vm_stable` -- the instantiation: a pointwise perturbation bound on the per-budget regret
  transfers to `V_m(eta)`, with the feasible set held fixed on both sides.
* `Vm_antitone` -- relaxing the band cannot raise the value, which is the monotonicity the
  breakpoint statement is about.
-/

namespace CIGAMF.P13.PaperCValueSet

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCBreakpoint

variable {R : Type*} [Fintype R] {m : ℕ}

/-! ## The paper's feasible set and value -/

/-- **The band-feasible set at `eta`**: probability laws over permutations whose per-item
retained marginals sit within `eta/m` of `k/m` at every budget. -/
def FeasibleAt (perm : R → Equiv.Perm (Fin m)) (η : ℝ) : Set (R → ℝ) :=
  {P | (∀ x, 0 ≤ P x) ∧ (∑ x, P x = 1) ∧
    ∀ (k : ℕ), k ≤ m → ∀ i : Fin m,
      |(∑ x, P x * inPrefixInd (perm x) k i) - (k : ℝ) / (m : ℝ)| ≤ η / (m : ℝ)}

/-- **The band is nested**: a wider band admits every law a narrower one does. -/
theorem feasible_mono (perm : R → Equiv.Perm (Fin m)) (η η' : ℝ) (hm : 0 < m)
    (hηη : η ≤ η') : FeasibleAt perm η ⊆ FeasibleAt perm η' := by
  rintro P ⟨hnn, hsum, hband⟩
  refine ⟨hnn, hsum, fun k hk i => ?_⟩
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine le_trans (hband k hk i) ?_
  have hdiff : 0 ≤ (η' - η) / (m : ℝ) := div_nonneg (by linarith) hmR.le
  have hsplit : (η' - η) / (m : ℝ) = η' / (m : ℝ) - η / (m : ℝ) := by ring
  linarith

/-- **Paper C's value at band `eta`.** -/
noncomputable def Vm (g : Ranking m) (perm : R → Equiv.Perm (Fin m)) (D η : ℝ)
    (budgets : Finset ℕ) (hne : budgets.Nonempty) : ℝ :=
  sInf ((fun P => maxRegret P g perm D budgets hne) '' FeasibleAt perm η)

/-! ## The feasible set is not empty

A band quantified over ALL budgets is unsatisfiable: at `k = m+1` every item is inside the
prefix, so the left side is `1` while `k/m = 1 + 1/m`.  An earlier version of `FeasibleAt`
had exactly that defect, which made every theorem about `Vm` vacuous while the gate stayed
clean.  The quantifier is bounded by `k <= m` above, and the witness below proves the set is
genuinely inhabited at `eta = 0`, so the defect cannot recur unnoticed. -/

/-- The cyclic family: `m` permutations, the `t`-th shifting every position by `t`. -/
noncomputable def cyclicPerm (m : ℕ) [NeZero m] (t : Fin m) : Equiv.Perm (Fin m) :=
  Equiv.addRight t

/-- The uniform law on the cyclic family. -/
noncomputable def cyclicLaw (m : ℕ) [NeZero m] : Fin m → ℝ := fun _ => 1 / (m : ℝ)

/-- **Each item's retained marginal under the cyclic law is exactly `k/m`.**  As `t` runs
over the shifts, `(cyclicPerm t).symm i = i - t` runs over every position exactly once, so
the number of shifts placing `i` inside the prefix is `k`. -/
theorem cyclic_marginal (m : ℕ) [NeZero m] (k : ℕ) (hk : k ≤ m) (i : Fin m) :
    (∑ t : Fin m, cyclicLaw m t * inPrefixInd (cyclicPerm m t) k i) = (k : ℝ) / (m : ℝ) := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hterm : ∀ t : Fin m,
      cyclicLaw m t * inPrefixInd (cyclicPerm m t) k i
        = (1 / (m : ℝ)) * (if ((i - t : Fin m) : ℕ) < k then (1 : ℝ) else 0) := by
    intro t
    unfold cyclicLaw inPrefixInd cyclicPerm
    have hsym : (Equiv.addRight t).symm i = i - t := by
      simp [sub_eq_add_neg]
    rw [hsym]
  rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Finset.mul_sum]
  have hbij : (∑ t : Fin m, (if ((i - t : Fin m) : ℕ) < k then (1 : ℝ) else 0))
      = ∑ u : Fin m, (if (u : ℕ) < k then (1 : ℝ) else 0) :=
    Fintype.sum_equiv (Equiv.subLeft i) _ _ (fun t => rfl)
  rw [hbij]
  have hcount : (∑ u : Fin m, (if (u : ℕ) < k then (1 : ℝ) else 0)) = (k : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then (1 : ℝ) else 0) m]
    have hfil : ∀ j ∈ Finset.range m,
        (if j < k then (1 : ℝ) else 0) = (if j ∈ Finset.range k then (1 : ℝ) else 0) := by
      intro j _
      by_cases hj : j < k
      · rw [if_pos hj, if_pos (Finset.mem_range.mpr hj)]
      · rw [if_neg hj, if_neg (fun hc => hj (Finset.mem_range.mp hc))]
    rw [Finset.sum_congr rfl hfil, Finset.sum_ite_mem,
      Finset.range_inter_range, min_eq_right hk, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hcount]
  field_simp

/-- **So the band-feasible set at `eta = 0` is inhabited.**  Every theorem about `Vm` below
is therefore about something. -/
theorem feasible_zero_nonempty (m : ℕ) [NeZero m] :
    (cyclicLaw m) ∈ FeasibleAt (cyclicPerm m) (0 : ℝ) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  refine ⟨fun _ => ?_, ?_, fun k hk i => ?_⟩
  · unfold cyclicLaw
    positivity
  · unfold cyclicLaw
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · rw [cyclic_marginal m k hk i, sub_self, abs_zero]
    simp

/-! ## The side conditions, proved -/

/-- **The objective is nonnegative** on the feasible set: every excess is, and the law is a
probability. -/
theorem maxRegret_nonneg (g : Ranking m) (perm : R → Equiv.Perm (Fin m)) (D : ℝ)
    (hD : 0 < D) (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hbud : ∀ k ∈ budgets, k ≤ m)
    (hw : ∀ (σ : Equiv.Perm (Fin m)) (i : Fin m),
      rankOf g σ i = -3 ∨ rankOf g σ i = -1 ∨ rankOf g σ i = 1 ∨ rankOf g σ i = 3)
    (P : R → ℝ) (hnn : ∀ x, 0 ≤ P x) :
    0 ≤ maxRegret P g perm D budgets hne := by
  obtain ⟨k, hk⟩ := hne
  have hterm : (0 : ℝ) ≤ ∑ x, P x * regret g (perm x) D k := by
    refine Finset.sum_nonneg (fun x _ => mul_nonneg (hnn x) ?_)
    unfold regret
    exact div_nonneg (excess_nonneg (rankOf g (perm x)) (hw (perm x)) k (hbud k hk)) hD.le
  exact le_trans hterm (Finset.le_sup' (fun k => ∑ x, P x * regret g (perm x) D k) hk)

/-- **So the value's defining set is bounded below**, which is what `sInf` needs to mean
anything. -/
theorem Vm_bddBelow (g : Ranking m) (perm : R → Equiv.Perm (Fin m)) (D η : ℝ)
    (hD : 0 < D) (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hbud : ∀ k ∈ budgets, k ≤ m)
    (hw : ∀ (σ : Equiv.Perm (Fin m)) (i : Fin m),
      rankOf g σ i = -3 ∨ rankOf g σ i = -1 ∨ rankOf g σ i = 1 ∨ rankOf g σ i = 3) :
    BddBelow ((fun P => maxRegret P g perm D budgets hne) '' FeasibleAt perm η) := by
  refine ⟨0, ?_⟩
  rintro y ⟨P, hP, rfl⟩
  exact maxRegret_nonneg g perm D hD budgets hne hbud hw P hP.1

/-! ## The instantiations -/

/-- **(#18) Stability of `V_m(eta)`.**  A pointwise bound on the per-budget regret under two
weight vectors transfers to the value, with the feasible set held fixed -- which is exactly
the hypothesis `value_stable_of_pointwise` consumes, now supplied by Paper C's own objects
rather than by an abstract `F`. -/
theorem Vm_stable (g g' : Ranking m) (perm : R → Equiv.Perm (Fin m)) (D η c : ℝ)
    (hD : 0 < D) (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hbud : ∀ k ∈ budgets, k ≤ m)
    (hw : ∀ (σ : Equiv.Perm (Fin m)) (i : Fin m),
      rankOf g σ i = -3 ∨ rankOf g σ i = -1 ∨ rankOf g σ i = 1 ∨ rankOf g σ i = 3)
    (hw' : ∀ (σ : Equiv.Perm (Fin m)) (i : Fin m),
      rankOf g' σ i = -3 ∨ rankOf g' σ i = -1 ∨ rankOf g' σ i = 1 ∨ rankOf g' σ i = 3)
    (hfne : (FeasibleAt perm η : Set (R → ℝ)).Nonempty)
    (hptwise : ∀ P ∈ FeasibleAt perm η, ∀ k ∈ budgets,
      |(∑ x, P x * regret g (perm x) D k) - (∑ x, P x * regret g' (perm x) D k)| ≤ c) :
    |Vm g perm D η budgets hne - Vm g' perm D η budgets hne| ≤ c := by
  refine value_stable_of_pointwise (FeasibleAt perm η)
    (fun P => maxRegret P g perm D budgets hne)
    (fun P => maxRegret P g' perm D budgets hne) c hfne
    (Vm_bddBelow g perm D η hD budgets hne hbud hw)
    (Vm_bddBelow g' perm D η hD budgets hne hbud hw') (fun P hP => ?_)
  exact max_stable_of_pointwise budgets hne
    (fun k => ∑ x, P x * regret g (perm x) D k)
    (fun k => ∑ x, P x * regret g' (perm x) D k) c (fun k hk => hptwise P hP k hk)

/-- **(#18) The value is antitone in the band.**  Relaxing the constraint cannot raise the
optimum, which is the direction the breakpoint statement needs. -/
theorem Vm_antitone (g : Ranking m) (perm : R → Equiv.Perm (Fin m)) (D η η' : ℝ)
    (hD : 0 < D) (hm : 0 < m) (hηη : η ≤ η')
    (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hbud : ∀ k ∈ budgets, k ≤ m)
    (hw : ∀ (σ : Equiv.Perm (Fin m)) (i : Fin m),
      rankOf g σ i = -3 ∨ rankOf g σ i = -1 ∨ rankOf g σ i = 1 ∨ rankOf g σ i = 3)
    (hfne : (FeasibleAt perm η : Set (R → ℝ)).Nonempty) :
    Vm g perm D η' budgets hne ≤ Vm g perm D η budgets hne := by
  refine csInf_le_csInf (Vm_bddBelow g perm D η' hD budgets hne hbud hw)
    (hfne.image _) ?_
  exact Set.image_mono (feasible_mono perm η η' hm hηη)

/-! ## Audit -/

#print axioms feasible_mono
#print axioms cyclic_marginal
#print axioms feasible_zero_nonempty
#print axioms maxRegret_nonneg
#print axioms Vm_bddBelow
#print axioms Vm_stable
#print axioms Vm_antitone

end CIGAMF.P13.PaperCValueSet
