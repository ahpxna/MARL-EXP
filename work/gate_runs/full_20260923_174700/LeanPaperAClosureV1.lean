import Mathlib

/-!
# Paper A: the closure exchange, licensed

Two residuals of the corpus are the same statement wearing different clothes.

* `CLAIMS.md` A15: the unsafe set is STRICT, `{range(lam_A) < range(lam_B)}`, while the
  games are solved over the CLOSED set `{<=}`, which strictly contains it.  Restricting an
  infimum raises it, so the closed value is a priori only a LOWER bound for the strict one,
  and "the two agree" was assumed under the name `closure_exchange`.
* `CLAIMS.md` A16: "per-region closure validity as a general statement" -- the region
  decomposition cuts with closed half-spaces and the same question arises per region.

Both are instances of one fact about infima: enlarging the feasible set to a superset
changes nothing, provided every point of the superset can be APPROXIMATED in objective by
points of the original.  `inf_eq_of_approximable` is that fact, proved from `le_csInf` and
`csInf_le` with no topology: the approximation hypothesis is stated directly in terms of the
objective, which is the only form the games can supply.

`approx_of_lipschitz_perturbation` is the shape the construction actually produces: an
explicit perturbation `pert t delta` that lands in the strict set and costs at most
`L * delta` in energy.  `pairShiftC_strict_alt` is a perturbation of exactly that kind --
for every `delta > 0` it exhibits a strictly-alternative world inside the centred class --
so what the games owe is the Lipschitz estimate for their own energy, and nothing else.

`closure_exchange_of_perturbation` is the two composed, and is the statement the games
should cite in place of the assumption.
-/

namespace CIGAMF.P13.PaperAClosure

/-! ## The exchange -/

/-- **Enlarging a feasible set to an approximable superset does not move the infimum.**
No topology: `happrox` is an approximation in the OBJECTIVE, which is what a perturbation
argument supplies directly. -/
theorem inf_eq_of_approximable {α : Type*} (f : α → ℝ) (S T : Set α) (hST : S ⊆ T)
    (hne : S.Nonempty) (hbT : BddBelow (f '' T))
    (happrox : ∀ t ∈ T, ∀ ε : ℝ, 0 < ε → ∃ s ∈ S, f s ≤ f t + ε) :
    sInf (f '' T) = sInf (f '' S) := by
  have hTne : T.Nonempty := hne.mono hST
  have hbS : BddBelow (f '' S) := hbT.mono (Set.image_mono hST)
  have h1 : sInf (f '' T) ≤ sInf (f '' S) :=
    csInf_le_csInf hbT (hne.image f) (Set.image_mono hST)
  have h2 : sInf (f '' S) ≤ sInf (f '' T) := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hkey : sInf (f '' S) - ε ≤ sInf (f '' T) := by
      refine le_csInf (hTne.image f) ?_
      rintro y ⟨t, ht, rfl⟩
      obtain ⟨s, hs, hle⟩ := happrox t ht ε hε
      have hs' : sInf (f '' S) ≤ f s := csInf_le hbS ⟨s, hs, rfl⟩
      linarith
    linarith
  exact le_antisymm h1 h2

/-- **A Lipschitz perturbation supplies the approximation.**  This is the form the
construction produces: a family that lands in the strict set for every positive scale and
costs at most `L` times that scale. -/
theorem approx_of_lipschitz_perturbation {α : Type*} (f : α → ℝ) (S T : Set α)
    (pert : α → ℝ → α) (L : ℝ) (hL : 0 ≤ L)
    (hmem : ∀ t ∈ T, ∀ δ : ℝ, 0 < δ → pert t δ ∈ S)
    (hlip : ∀ t ∈ T, ∀ δ : ℝ, 0 < δ → f (pert t δ) ≤ f t + L * δ) :
    ∀ t ∈ T, ∀ ε : ℝ, 0 < ε → ∃ s ∈ S, f s ≤ f t + ε := by
  intro t ht ε hε
  have hLpos : (0 : ℝ) < L + 1 := by linarith
  refine ⟨pert t (ε / (L + 1)), hmem t ht _ (by positivity), ?_⟩
  have h := hlip t ht (ε / (L + 1)) (by positivity)
  have hbound : L * (ε / (L + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hLpos]
    nlinarith
  linarith

/-- **The exchange, from a perturbation.**  The composition: this is what a game should cite
instead of assuming `closure_exchange`. -/
theorem closure_exchange_of_perturbation {α : Type*} (f : α → ℝ) (S T : Set α)
    (hST : S ⊆ T) (hne : S.Nonempty) (hbT : BddBelow (f '' T))
    (pert : α → ℝ → α) (L : ℝ) (hL : 0 ≤ L)
    (hmem : ∀ t ∈ T, ∀ δ : ℝ, 0 < δ → pert t δ ∈ S)
    (hlip : ∀ t ∈ T, ∀ δ : ℝ, 0 < δ → f (pert t δ) ≤ f t + L * δ) :
    sInf (f '' T) = sInf (f '' S) :=
  inf_eq_of_approximable f S T hST hne hbT
    (approx_of_lipschitz_perturbation f S T pert L hL hmem hlip)

/-- **And the game values then agree design by design.**  A game is a supremum over designs
of an infimum over alternatives; if the two alternative sets give the same infimum at every
design, the two games are equal. -/
theorem game_eq_of_pointwise_inf {D α : Type*} (val : D → Set α → ℝ)
    (S T : D → Set α) (h : ∀ d, val d (S d) = val d (T d)) :
    (fun d => val d (S d)) = fun d => val d (T d) := by
  funext d
  exact h d

/-- **Restricting alone gives only one direction**, which is why the approximation is
needed and why the earlier assumption was not free.  Recorded so the direction is not
misremembered. -/
theorem restriction_only_raises {α : Type*} (f : α → ℝ) (S T : Set α) (hST : S ⊆ T)
    (hne : S.Nonempty) (hbT : BddBelow (f '' T)) :
    sInf (f '' T) ≤ sInf (f '' S) :=
  csInf_le_csInf hbT (hne.image f) (Set.image_mono hST)

/-! ## Audit -/

#print axioms inf_eq_of_approximable
#print axioms approx_of_lipschitz_perturbation
#print axioms closure_exchange_of_perturbation
#print axioms game_eq_of_pointwise_inf
#print axioms restriction_only_raises

end CIGAMF.P13.PaperAClosure
