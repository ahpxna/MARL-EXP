import «LeanPaperARGamesV1»

/-!
# Paper A: the game of the ACTUAL frozen-linear surrogate

`LeanPaperARGamesV1` defines `ProxyAlt` by pinning the middle cells and then using the
TRUE ranges.  That is not the frozen-linear surrogate.  The surrogate, as
`LeanPaperASeparationV1` writes it in the eight-cell model, pins the extremum INDICES and
tests a single linear contrast on the four frozen cells:

    (lam 1 - lam 0) - (lam 5 - lam 4) <= 0.

The two sets differ, and the witness is explicit: arm `A` at `(0,1)`, both arm-`B` anchors
at `-2` and the middle cells at `0` has true `B`-range `2 > 1`, so it lies in `ProxyAlt`,
while its frozen contrast is `(1-0) - (-2-(-2)) = 1 > 0`, so it is not a frozen
alternative.  Set equality is therefore FALSE and must not be assumed.

What the separation argument actually needs is not equality of the sets but an inequality
between the two games' VALUES, and that is what this module proves: the frozen game is
bounded between the same two absolute constants, so the ratio `Gamma_true / Gamma_frozen`
obeys the same `Theta((rM)^{-1})` bracket.  The conclusion about the surrogate therefore
holds for the surrogate itself, not for a stand-in.
-/

namespace CIGAMF.P13.PaperAFrozen

open Finset
open CIGAMF.P13.PaperARPair
open CIGAMF.P13.ARGames

variable {r : ℕ}

/-- The frozen-linear surrogate's alternatives: one linear contrast on the four frozen
extremum cells, in the same form the eight-cell model uses. -/
def FrozenAlt (r : ℕ) : Set (Cell r → ℝ) :=
  {lam | (lam (Sum.inl 1) - lam (Sum.inl 0))
          - (lam (Sum.inl 2) - lam (Sum.inl 3)) ≤ 0}

/-- The world that separates the two alternative sets: arm `A` at `(0,1)`, arm `B`'s
frozen maximum pushed to `-2`, everything else at zero. -/
noncomputable def lamSplit (r : ℕ) : Cell r → ℝ :=
  Sum.elim (![0, 1, -2, 0] : Fin 4 → ℝ) (fun _ => 0)

theorem lamSplit_inl0 (r : ℕ) : lamSplit r (Sum.inl 0) = 0 := by simp [lamSplit]
theorem lamSplit_inl1 (r : ℕ) : lamSplit r (Sum.inl 1) = 1 := by simp [lamSplit]
theorem lamSplit_inl2 (r : ℕ) : lamSplit r (Sum.inl 2) = -2 := by simp [lamSplit]
theorem lamSplit_inl3 (r : ℕ) : lamSplit r (Sum.inl 3) = 0 := by simp [lamSplit]
theorem lamSplit_pair (r : ℕ) (p : Fin r × Bool) : lamSplit r (Sum.inr p) = 0 := rfl

/-- **The two alternative sets are not equal.**  Recorded as a theorem so the manuscript
cannot quietly assume otherwise: `lamSplit` has true `B`-range `2 > 1`, so the
restricted-coordinate game counts it as an alternative, while its frozen contrast is
`(1-0) - (-2-0) = 3 > 0`, so the surrogate does not. -/
theorem proxyAlt_ne_frozenAlt (r : ℕ) :
    lamSplit r ∈ ProxyAlt r ∧ lamSplit r ∉ FrozenAlt r := by
  constructor
  · refine ⟨fun p => lamSplit_pair r p, ?_⟩
    have hA : rangeA (lamSplit r) = 1 := by
      unfold rangeA; rw [lamSplit_inl0, lamSplit_inl1]; norm_num
    have hsup : (0 : ℝ) ≤ (BCells r).sup' (BCells_nonempty r) (lamSplit r) := by
      have := Finset.le_sup' (lamSplit r) (bAnchor3_mem r)
      rwa [lamSplit_inl3] at this
    have hinf : (BCells r).inf' (BCells_nonempty r) (lamSplit r) ≤ -2 := by
      have := Finset.inf'_le (lamSplit r) (bAnchor_mem r)
      rwa [lamSplit_inl2] at this
    show rangeA (lamSplit r) < rangeB (lamSplit r)
    unfold rangeB; rw [hA]; linarith
  · intro hmem
    have hc : (lamSplit r (Sum.inl 1) - lamSplit r (Sum.inl 0))
        - (lamSplit r (Sum.inl 2) - lamSplit r (Sum.inl 3)) ≤ 0 := hmem
    rw [lamSplit_inl0, lamSplit_inl1, lamSplit_inl2, lamSplit_inl3] at hc
    norm_num at hc

/-- A frozen alternative exists: raising arm `B`'s frozen maximum by `2` flips the
contrast. -/
theorem anchorBump2_frozen : anchorBump r 2 2 ∈ FrozenAlt r := by
  have h0 : anchorBump r 2 2 (Sum.inl 0) = -(1/2) := by
    unfold anchorBump; rw [if_neg (fun h => absurd (Sum.inl.inj h) (by decide)), theta0_inl0]
  have h1 : anchorBump r 2 2 (Sum.inl 1) = 1/2 := by
    unfold anchorBump; rw [if_neg (fun h => absurd (Sum.inl.inj h) (by decide)), theta0_inl1]
  have h2 : anchorBump r 2 2 (Sum.inl 2) = 2 := by
    unfold anchorBump; rw [if_pos rfl, theta0_inl2]; ring
  have h3 : anchorBump r 2 2 (Sum.inl 3) = 0 := by
    unfold anchorBump; rw [if_neg (fun h => absurd (Sum.inl.inj h) (by decide)), theta0_inl3]
  show (anchorBump r 2 2 (Sum.inl 1) - anchorBump r 2 2 (Sum.inl 0))
        - (anchorBump r 2 2 (Sum.inl 2) - anchorBump r 2 2 (Sum.inl 3)) ≤ 0
  rw [h0, h1, h2, h3]; norm_num

instance instNonemptyFrozen (r : ℕ) : Nonempty (FrozenAlt r) :=
  ⟨⟨anchorBump r 2 2, anchorBump2_frozen⟩⟩

noncomputable def frozenValue (M : ℝ) (w : Cell r → ℝ) : ℝ :=
  ⨅ lam : FrozenAlt r, energy w (pairVar M) (theta0 r) (lam : Cell r → ℝ)

noncomputable def frozenGame (r : ℕ) (M : ℝ) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, frozenValue M (w : Cell r → ℝ)

theorem bddBelow_frozen (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (Set.range (fun lam : FrozenAlt r =>
      energy w (pairVar M) (theta0 r) (lam : Cell r → ℝ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨lam, rfl⟩
  exact energy_nonneg M hM w _ _ hw

/-- Four numbers whose alternating sum reaches one carry squared norm at least `1/4`. -/
theorem four_sq_lower_one (x₀ x₁ x₂ x₃ : ℝ) (h : 1 ≤ x₀ - x₁ + x₂ - x₃) :
    1 / 4 ≤ x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 := by
  nlinarith [sq_nonneg (x₀ + x₁), sq_nonneg (x₀ - x₂), sq_nonneg (x₀ + x₃),
    sq_nonneg (x₁ + x₂), sq_nonneg (x₁ - x₃), sq_nonneg (x₂ + x₃), h]

/-- At the uniform-anchor design the energy is the anchors' squared displacement over `8`;
the pair cells carry no weight, so no hypothesis about them is needed. -/
theorem energy_wUnif (M : ℝ) (L : Cell r → ℝ) :
    energy (wUnif r) (pairVar M) (theta0 r) L
      = ((L (Sum.inl 0) - theta0 r (Sum.inl 0)) ^ 2
        + (L (Sum.inl 1) - theta0 r (Sum.inl 1)) ^ 2
        + (L (Sum.inl 2) - theta0 r (Sum.inl 2)) ^ 2
        + (L (Sum.inl 3) - theta0 r (Sum.inl 3)) ^ 2) / 8 := by
  unfold energy
  have hsplit : ∑ e : Cell r, wUnif r e * (L e - theta0 r e) ^ 2 / pairVar M e
      = (∑ a : Fin 4, wUnif r (Sum.inl a) * (L (Sum.inl a) - theta0 r (Sum.inl a)) ^ 2
          / pairVar (r := r) M (Sum.inl a))
        + ∑ p : Fin r × Bool,
            wUnif r (Sum.inr p) * (L (Sum.inr p) - theta0 r (Sum.inr p)) ^ 2
              / pairVar M (Sum.inr p) := Fintype.sum_sum_type _
  have hzero : ∀ p : Fin r × Bool,
      wUnif r (Sum.inr p) * (L (Sum.inr p) - theta0 r (Sum.inr p)) ^ 2
        / pairVar M (Sum.inr p) = 0 := by
    intro p
    have hw : wUnif r (Sum.inr p) = 0 := rfl
    rw [hw, zero_mul, zero_div]
  have hanch : ∀ a : Fin 4,
      wUnif r (Sum.inl a) * (L (Sum.inl a) - theta0 r (Sum.inl a)) ^ 2
        / pairVar (r := r) M (Sum.inl a)
        = (L (Sum.inl a) - theta0 r (Sum.inl a)) ^ 2 / 4 := by
    intro a
    have hw : wUnif r (Sum.inl a) = 1 / 4 := rfl
    have hv : pairVar (r := r) M (Sum.inl a) = 1 := rfl
    rw [hw, hv]; ring
  rw [hsplit, Finset.sum_congr rfl (fun p _ => hzero p),
      Finset.sum_congr rfl (fun a _ => hanch a), Finset.sum_const_zero, add_zero,
      Fin.sum_univ_four]
  ring

/-- **The frozen game is at least `1/32`.**  Flipping the frozen contrast means moving an
alternating sum of four unit-variance cells by one, which costs squared displacement
`1/4`. -/
theorem frozenValue_unif_ge (M : ℝ) (hM : 0 < M) :
    1 / 32 ≤ frozenValue M (wUnif r) := by
  refine le_ciInf (fun lam => ?_)
  have hc : ((lam : Cell r → ℝ) (Sum.inl 1) - (lam : Cell r → ℝ) (Sum.inl 0))
      - ((lam : Cell r → ℝ) (Sum.inl 2) - (lam : Cell r → ℝ) (Sum.inl 3)) ≤ 0 := lam.2
  rw [energy_wUnif M]
  -- Keep the displacements in the `lam - theta0` form the goal has; unfold `theta0`'s
  -- values ONLY inside the side goal.  Rewriting them into the main goal leaves `d - 0`
  -- in one place and `d` in another, which `linarith` treats as distinct atoms.
  have hsq : 1 / 4 ≤ ((lam : Cell r → ℝ) (Sum.inl 0) - theta0 r (Sum.inl 0)) ^ 2
      + ((lam : Cell r → ℝ) (Sum.inl 1) - theta0 r (Sum.inl 1)) ^ 2
      + ((lam : Cell r → ℝ) (Sum.inl 2) - theta0 r (Sum.inl 2)) ^ 2
      + ((lam : Cell r → ℝ) (Sum.inl 3) - theta0 r (Sum.inl 3)) ^ 2 := by
    refine four_sq_lower_one _ _ _ _ ?_
    -- the world is centred, so the anchor readings shift by +-1/2; the CONTRAST, and
    -- therefore the displacement bound, is unchanged
    rw [theta0_inl0, theta0_inl1, theta0_inl2, theta0_inl3]
    linarith
  linarith

/-- **The frozen game is at most `1`.**  Whichever of arm `B`'s two frozen anchors carries
less weight, moving it by two already flips the contrast. -/
theorem frozenValue_le (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w) :
    frozenValue M w ≤ 1 := by
  classical
  have hne23 : (Sum.inl 2 : Cell r) ≠ Sum.inl 3 := fun h =>
    absurd (Sum.inl.inj h) (by decide)
  have hsum2 : w (Sum.inl 2) + w (Sum.inl 3) ≤ 1 := by
    have hsub : ({Sum.inl 2, Sum.inl 3} : Finset (Cell r)) ⊆ univ := Finset.subset_univ _
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hw.1 e)
    rw [Finset.sum_pair hne23, hw.2] at h
    exact h
  have key : ∀ (a : Fin 4) (δ : ℝ), anchorBump r a δ ∈ FrozenAlt r →
      w (Sum.inl a) * δ ^ 2 / 2 ≤ 1 → frozenValue M w ≤ 1 := by
    intro a δ hmem hbnd
    have hle : frozenValue M w ≤ energy w (pairVar M) (theta0 r) (anchorBump r a δ) :=
      ciInf_le (bddBelow_frozen M hM w hw.1) (⟨anchorBump r a δ, hmem⟩ : FrozenAlt r)
    rw [energy_anchorBump] at hle
    linarith
  rcases le_total (w (Sum.inl 2)) (w (Sum.inl 3)) with h | h
  · refine key 2 2 anchorBump2_frozen ?_
    have : w (Sum.inl 2) ≤ 1 / 2 := by linarith [hw.1 (Sum.inl 3)]
    nlinarith [this, hw.1 (Sum.inl 2)]
  · -- lower arm B's other frozen anchor instead
    have hmem : anchorBump r 3 (-2) ∈ FrozenAlt r := by
      have h0 : anchorBump r 3 (-2) (Sum.inl 0) = -(1/2) := by
        unfold anchorBump; rw [if_neg (fun h => absurd (Sum.inl.inj h) (by decide)), theta0_inl0]
      have h1 : anchorBump r 3 (-2) (Sum.inl 1) = 1/2 := by
        unfold anchorBump; rw [if_neg (fun h => absurd (Sum.inl.inj h) (by decide)), theta0_inl1]
      have h2 : anchorBump r 3 (-2) (Sum.inl 2) = 0 := by
        unfold anchorBump; rw [if_neg (fun h => absurd (Sum.inl.inj h) (by decide)), theta0_inl2]
      have h3 : anchorBump r 3 (-2) (Sum.inl 3) = -2 := by
        unfold anchorBump; rw [if_pos rfl, theta0_inl3]; ring
      show (anchorBump r 3 (-2) (Sum.inl 1) - anchorBump r 3 (-2) (Sum.inl 0))
            - (anchorBump r 3 (-2) (Sum.inl 2) - anchorBump r 3 (-2) (Sum.inl 3)) ≤ 0
      rw [h0, h1, h2, h3]; norm_num
    refine key 3 (-2) hmem ?_
    have : w (Sum.inl 3) ≤ 1 / 2 := by linarith [hw.1 (Sum.inl 2)]
    nlinarith [this, hw.1 (Sum.inl 3)]

theorem bddAbove_frozen (M : ℝ) (hM : 0 < M) :
    BddAbove (Set.range (fun w : {w : Cell r → ℝ // IsAlloc w} =>
      frozenValue M (w : Cell r → ℝ))) := by
  refine ⟨1, ?_⟩
  rintro x ⟨w, rfl⟩
  exact frozenValue_le M hM (w : Cell r → ℝ) w.2

theorem frozenGame_ge (M : ℝ) (hM : 0 < M) : 1 / 32 ≤ frozenGame r M :=
  le_trans (frozenValue_unif_ge M hM)
    (le_ciSup (bddAbove_frozen M hM) (⟨wUnif r, wUnif_isAlloc r⟩))

theorem frozenGame_le (M : ℝ) (hM : 0 < M) : frozenGame r M ≤ 1 :=
  ciSup_le (fun w => frozenValue_le M hM (w : Cell r → ℝ) w.2)

/-- **`Theta((rM)^{-1})` against the ACTUAL frozen-linear surrogate.**

No set equality is assumed anywhere.  The frozen game is bounded between the same two
absolute constants as the restricted-coordinate game, by its own proofs, so the ratio
against the true game obeys the same bracket.  The separation is therefore a statement
about the surrogate the paper criticises. -/
theorem frozen_games_theta (M : ℝ) (hM : 0 < M) (hr : 0 < r) :
    1 / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueGame r M / frozenGame r M
      ∧ trueGame r M / frozenGame r M ≤ 16 / (M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hflo := frozenGame_ge (r := r) M hM
  have hfhi := frozenGame_le (r := r) M hM
  have hfpos : (0 : ℝ) < frozenGame r M := by linarith
  have htlo := trueGame_ge M hM hr
  have hthi := trueGame_le M hM hr
  have hZ : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by nlinarith
  have hZ128 : (0 : ℝ) < 128 * (4 + 2 * (r : ℝ) * M) := by linarith
  have hc : (0 : ℝ) ≤ 1 / (128 * (4 + 2 * (r : ℝ) * M)) := le_of_lt (div_pos one_pos hZ128)
  have hMr : (0 : ℝ) < M * (r : ℝ) := by positivity
  constructor
  · rw [le_div_iff₀ hfpos]
    have h1 : 1 / (128 * (4 + 2 * (r : ℝ) * M)) * frozenGame r M
        ≤ 1 / (128 * (4 + 2 * (r : ℝ) * M)) * 1 :=
      mul_le_mul_of_nonneg_left hfhi hc
    rw [mul_one] at h1
    linarith
  · rw [div_le_iff₀ hfpos]
    have hk : 16 / (M * (r : ℝ)) * (1 / 32) = 1 / (2 * M * (r : ℝ)) := by
      field_simp; ring
    have h2 : 16 / (M * (r : ℝ)) * (1 / 32) ≤ 16 / (M * (r : ℝ)) * frozenGame r M :=
      mul_le_mul_of_nonneg_left hflo (le_of_lt (div_pos (by norm_num) hMr))
    rw [hk] at h2
    have h3 : 1 / (8 * M * (r : ℝ)) ≤ 1 / (2 * M * (r : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hrr, hM]
    linarith

/-! ## Audit -/

#print axioms lamSplit_inl2
#print axioms proxyAlt_ne_frozenAlt
#print axioms anchorBump2_frozen
#print axioms four_sq_lower_one
#print axioms energy_wUnif
#print axioms frozenValue_unif_ge
#print axioms frozenValue_le
#print axioms frozenGame_ge
#print axioms frozenGame_le
#print axioms frozen_games_theta

end CIGAMF.P13.PaperAFrozen
