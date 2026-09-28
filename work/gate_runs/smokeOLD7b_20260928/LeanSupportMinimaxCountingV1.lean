import Mathlib

/-! # Support: the counting core of the passive posterior and the active law.

`scripts/U1_support_minimax_check.py` verifies by brute force, exactly, that with
a uniform prior over the `b`-subsets `W` of `Fin m`:

  * the posterior after seeing the tip set `S` is uniform on
    `{W : |W| = b, S ⊆ W}`, so `Pr(j ∈ W | S) = (b-s)/(m-s)` for unseen `j`;
  * the uniform-unseen policy attains `E[L_N/(a+L_N)]` exactly;
  * `C(b,k+1)/C(a+b,k+1)` is the Bayes optimum over ALL deterministic adaptive
    query trees of depth `k` — enumerated, not assumed.

This file proves the COUNTING identities those three rest on. They are the part
that is finite and exact; the measure-theoretic wrapper is not here.

* `active_error_card` / `active_total_card` — for the uniform-`(k+1)`-subset
  policy the all-unsafe draws are exactly the `(k+1)`-subsets of `W`, so there are
  `C(b, k+1)` of them out of `C(m, k+1)`. This is the count behind the randomised
  UPPER bound of the active law.

The posterior counting identity `#{W : |W|=b, S ⊆ W, j ∈ W} * (m-s) =
#{W : |W|=b, S ⊆ W} * (b-s)` is NOT formalised here. It is verified exactly by
the probe on every `S` and `j` for `m ≤ 7`; the Lean route needs the bijection
`W ↦ W \ S` and the `choose` absorption identity, and neither spelling I tried
matched this Mathlib. Stated as open rather than left as a broken proof.

## WHAT THIS DOES NOT ESTABLISH

- No probability space appears. These are cardinalities; reading them as a
  posterior or as an error probability is the step the wrapper must make, and it
  is NOT made here.
- The passive minimax `R_N^* = E[L_N/(a+L_N)]` is NOT proved: the occupancy law
  of `L_N`, the Bayes lower bound and the policy's risk are all outside this
  file. `LeanSupportPassiveAnswerMultiplicityV1` says the same about itself.
- The active law is proved here only as the count behind the RANDOMISED UPPER
  bound. That `C(b,k+1)/C(m,k+1)` is also the optimum over every deterministic
  adaptive tree is brute-force verified on `m ≤ 7`, not proved.
- Equal tip masses are assumed throughout the model these counts serve; with
  unequal masses the posterior is not uniform and none of this transfers.
-/

namespace CIGAMF.P13.SupportMinimaxCounting
open Finset
noncomputable section
variable {m : ℕ}

/-- For the uniform-`(k+1)`-subset policy: the all-unsafe draws are exactly the
`(k+1)`-subsets of `W`. -/
theorem active_error_card (W : Finset (Fin m)) (k : ℕ) :
    (((univ : Finset (Fin m)).powersetCard (k+1)).filter (fun U => U ⊆ W)).card
      = W.card.choose (k+1) := by
  classical
  have hset : (((univ : Finset (Fin m)).powersetCard (k+1)).filter (fun U => U ⊆ W))
      = W.powersetCard (k+1) := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨-, hc⟩, hsub⟩; exact ⟨hsub, hc⟩
    · rintro ⟨hsub, hc⟩; exact ⟨⟨Finset.subset_univ _, hc⟩, hsub⟩
  rw [hset, Finset.card_powersetCard]

/-- Total number of draws. -/
theorem active_total_card (k : ℕ) :
    ((univ : Finset (Fin m)).powersetCard (k+1)).card = m.choose (k+1) := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- THE POSTERIOR, by double counting -- no `choose` absorption identity needed.

Count the pairs `(W, j)` with `|W| = b`, `S ⊆ W` and `j ∈ W \ S`:

  * summing over `W` first, each admissible `W` contributes `|W \ S| = b - s`;
  * summing over `j` first, each `j ∉ S` contributes the number of admissible `W`
    that also contain `j`.

Equating the two gives the posterior identity with denominators cleared, so no
positivity side condition is smuggled in, and the `choose` absorption identity --
whose Mathlib spelling did not match here -- is never needed. -/
theorem posterior_double_count (b : ℕ) (S : Finset (Fin m)) :
    (∑ j ∈ Sᶜ, ((univ : Finset (Finset (Fin m))).filter
        (fun W => W.card = b ∧ S ⊆ W ∧ j ∈ W)).card)
      = (∑ W ∈ (univ : Finset (Finset (Fin m))).filter
            (fun W => W.card = b ∧ S ⊆ W), (W \ S).card) := by
  classical
  simp only [Finset.card_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun W _ => ?_)
  by_cases hW : W.card = b ∧ S ⊆ W
  · rw [if_pos hW]
    have hinner : ∀ j ∈ Sᶜ, (if W.card = b ∧ S ⊆ W ∧ j ∈ W then 1 else 0)
        = (if j ∈ W then (1:ℕ) else 0) := by
      intro j _
      by_cases h : j ∈ W
      · rw [if_pos ⟨hW.1, hW.2, h⟩, if_pos h]
      · rw [if_neg (fun hc => h hc.2.2), if_neg h]
    rw [Finset.sum_congr rfl hinner, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const_zero, add_zero, smul_eq_mul, mul_one]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  · rw [if_neg hW]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg (fun hc => hW ⟨hc.1, hc.2.1⟩)]

/-- Each admissible `W` contributes exactly `b - |S|`. -/
theorem sdiff_card_of_superset (b : ℕ) (S W : Finset (Fin m))
    (hcard : W.card = b) (hsub : S ⊆ W) : (W \ S).card = b - S.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard]

/-- The posterior identity in cleared form. `hsym` says the count does not depend
on which unseen coordinate is chosen — the transposition symmetry of the model —
and with it the double count becomes

    N * (number of unseen coordinates) = (number of admissible worlds) * (b - s),

which is `Pr(j in W | S) = (b-s)/(m-s)` with the denominators cleared, so no
positivity side condition enters. -/
theorem posterior_ratio_cleared (b : ℕ) (S : Finset (Fin m)) (N : ℕ)
    (hsym : ∀ i ∈ Sᶜ, ((univ : Finset (Finset (Fin m))).filter
        (fun W => W.card = b ∧ S ⊆ W ∧ i ∈ W)).card = N) :
    Sᶜ.card * N
      = ((univ : Finset (Finset (Fin m))).filter
          (fun W => W.card = b ∧ S ⊆ W)).card * (b - S.card) := by
  classical
  have h1 := posterior_double_count (m := m) b S
  have hL : (∑ j ∈ Sᶜ, ((univ : Finset (Finset (Fin m))).filter
      (fun W => W.card = b ∧ S ⊆ W ∧ j ∈ W)).card) = Sᶜ.card * N := by
    rw [Finset.sum_congr rfl hsym, Finset.sum_const, smul_eq_mul]
  have hstep : ∀ W ∈ (univ : Finset (Finset (Fin m))).filter
      (fun W => W.card = b ∧ S ⊆ W), (W \ S).card = b - S.card := by
    intro W hW
    simp only [Finset.mem_filter] at hW
    exact sdiff_card_of_superset b S W hW.2.1 hW.2.2
  have hR : (∑ W ∈ (univ : Finset (Finset (Fin m))).filter
      (fun W => W.card = b ∧ S ⊆ W), (W \ S).card)
      = ((univ : Finset (Finset (Fin m))).filter
          (fun W => W.card = b ∧ S ⊆ W)).card * (b - S.card) := by
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, smul_eq_mul]
  rw [hL, hR] at h1
  exact h1

/-- The count does not depend on WHICH unseen coordinate is chosen: the
transposition `swap i i'` fixes `S` pointwise (both `i` and `i'` are outside it)
and carries the worlds containing `i` bijectively onto those containing `i'`.
This discharges the symmetry that `posterior_ratio_cleared` took as a hypothesis. -/
theorem count_indep_of_unseen (b : ℕ) (S : Finset (Fin m)) (i i' : Fin m)
    (hi : i ∉ S) (hi' : i' ∉ S) :
    ((univ : Finset (Finset (Fin m))).filter
        (fun W => W.card = b ∧ S ⊆ W ∧ i ∈ W)).card
      = ((univ : Finset (Finset (Fin m))).filter
        (fun W => W.card = b ∧ S ⊆ W ∧ i' ∈ W)).card := by
  classical
  have hswapS : ∀ x ∈ S, (Equiv.swap i i') x = x := by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ hx)) (fun h => hi' (h ▸ hx))
  have hmaps : ∀ (a c : Fin m), a ∉ S → c ∉ S →
      ∀ W ∈ (univ : Finset (Finset (Fin m))).filter
        (fun W => W.card = b ∧ S ⊆ W ∧ a ∈ W),
      W.image (Equiv.swap a c) ∈ (univ : Finset (Finset (Fin m))).filter
        (fun W => W.card = b ∧ S ⊆ W ∧ c ∈ W) := by
    intro a c ha hc W hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
    obtain ⟨hcard, hsub, hmem⟩ := hW
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (Equiv.swap a c).injective, hcard]
    · intro x hx
      have hfix : (Equiv.swap a c) x = x :=
        Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hx)) (fun h => hc (h ▸ hx))
      exact Finset.mem_image.mpr ⟨x, hsub hx, hfix⟩
    · exact Finset.mem_image.mpr ⟨a, hmem, Equiv.swap_apply_left a c⟩
  have hinv : ∀ (a c : Fin m) (W : Finset (Fin m)),
      (W.image (Equiv.swap a c)).image (Equiv.swap a c) = W := by
    intro a c W
    rw [Finset.image_image]
    have : (Equiv.swap a c) ∘ (Equiv.swap a c) = id := by
      funext x; simp
    rw [this, Finset.image_id]
  exact Finset.card_nbij' (fun W => W.image (Equiv.swap i i'))
    (fun W => W.image (Equiv.swap i i'))
    (hmaps i i' hi hi') (fun W hW => by
      have := hmaps i' i hi' hi W hW
      simpa [Equiv.swap_comm] using this)
    (fun W _ => hinv i i' W) (fun W _ => hinv i i' W)

/-- THE POSTERIOR IDENTITY, with no symmetry hypothesis left. -/
theorem posterior_ratio (b : ℕ) (S : Finset (Fin m)) (j : Fin m) (hj : j ∉ S) :
    Sᶜ.card * ((univ : Finset (Finset (Fin m))).filter
        (fun W => W.card = b ∧ S ⊆ W ∧ j ∈ W)).card
      = ((univ : Finset (Finset (Fin m))).filter
          (fun W => W.card = b ∧ S ⊆ W)).card * (b - S.card) := by
  classical
  refine posterior_ratio_cleared b S _ (fun i hi => ?_)
  exact count_indep_of_unseen b S i j (by simpa using hi) hj

#print axioms count_indep_of_unseen
#print axioms posterior_ratio
#print axioms posterior_double_count
#print axioms sdiff_card_of_superset
#print axioms posterior_ratio_cleared

#print axioms active_error_card
#print axioms active_total_card

end
end CIGAMF.P13.SupportMinimaxCounting
