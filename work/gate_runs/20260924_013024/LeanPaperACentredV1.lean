import «LeanPaperARPairV1»

/-!
# Paper A: the centred construction, with the frozen game computed exactly

This replaces the earlier route (`AnchorMonotone`, then a homogeneity wrapper) with a
world on which the frozen-linear surrogate's game has a **closed form**, and from which
starvation follows in one line.

The world separates arm `B`'s extrema instead of leaving that arm flat:

    theta_A = (-1/2, 1/2),    theta_B = (-1/8, 1/8, 0, ..., 0).

Both arms sum to zero, so the world lies in the centred class where the per-cell Gaussian
KL equals the squared gap and `energy` IS the information.  The frozen contrast therefore
starts at a strictly positive margin

    g = range(theta_A) - range(theta_B) = 1 - 1/4 = 3/4,

which is what the flat-`B` world could not provide.

The consequences are exact rather than bracketed.  Shifting the four anchors by
`(+g/4, -g/4, -g/4, +g/4)` closes the contrast, keeps both arms centred and leaves the
middle cells untouched, at energy `(g^2/32)*a(w)` where `a(w)` is the anchor mass.  Hence

    J_frozen(w) <= (g^2/32) a(w) = (9/512) a(w),

and since `a(w) <= 1` for an allocation, `Gamma_frozen = 9/512`.  **Starvation is now a
one-line consequence of the upper bound alone**: a design attaining the optimum must have
`a(w) = 1`, i.e. nothing on the middle cells; and a design within `eps` of it leaks at most
`eps/Gamma_frozen = (512/9) eps`.  No monotonicity modulus and no homogeneity hypothesis is
used anywhere.
-/

namespace CIGAMF.P13.PaperACentred

open Finset
open CIGAMF.P13.PaperARPair

variable {r : ℕ}

/-! ## The world -/

/-- Arm `A` at `(-1/2, 1/2)`, arm `B`'s anchors at `(-1/8, 1/8)`, middles at zero. -/
noncomputable def thetaC (r : ℕ) : Cell r → ℝ :=
  Sum.elim (![-(1/2), 1/2, -(1/8), 1/8] : Fin 4 → ℝ) (fun _ => 0)

theorem thetaC_0 (r : ℕ) : thetaC r (Sum.inl 0) = -(1/2) := by simp [thetaC]
theorem thetaC_1 (r : ℕ) : thetaC r (Sum.inl 1) = 1/2 := by simp [thetaC]
theorem thetaC_2 (r : ℕ) : thetaC r (Sum.inl 2) = -(1/8) := by simp [thetaC]
theorem thetaC_3 (r : ℕ) : thetaC r (Sum.inl 3) = 1/8 := by simp [thetaC]
theorem thetaC_pair (r : ℕ) (p : Fin r × Bool) : thetaC r (Sum.inr p) = 0 := rfl

/-- **Both arms are centred**, so the per-cell Gaussian KL is the squared gap and the
games optimise information rather than a stand-in for it. -/
theorem thetaC_centred (r : ℕ) :
    thetaC r (Sum.inl 0) + thetaC r (Sum.inl 1) = 0
      ∧ thetaC r (Sum.inl 2) + thetaC r (Sum.inl 3)
          + ∑ p : Fin r × Bool, thetaC r (Sum.inr p) = 0 := by
  refine ⟨by rw [thetaC_0, thetaC_1]; ring, ?_⟩
  have hz : ∑ p : Fin r × Bool, thetaC r (Sum.inr p) = 0 :=
    Finset.sum_eq_zero (fun p _ => thetaC_pair r p)
  rw [thetaC_2, thetaC_3, hz]; ring

/-- The frozen contrast's margin at the true world: `range(A) - range(B) = 3/4`. -/
theorem frozen_margin (r : ℕ) :
    (thetaC r (Sum.inl 1) - thetaC r (Sum.inl 0))
      - (thetaC r (Sum.inl 3) - thetaC r (Sum.inl 2)) = 3/4 := by
  rw [thetaC_0, thetaC_1, thetaC_2, thetaC_3]; norm_num

/-! ## The frozen surrogate's alternatives -/

/-- One linear contrast on the four frozen extremum cells. -/
def FrozenAltC (r : ℕ) : Set (Cell r → ℝ) :=
  {lam | (lam (Sum.inl 1) - lam (Sum.inl 0))
          - (lam (Sum.inl 3) - lam (Sum.inl 2)) ≤ 0}

/-- The witness: shift the four anchors by `(+g/4, -g/4, -g/4, +g/4)` with `g = 3/4`. -/
noncomputable def lamStar (r : ℕ) : Cell r → ℝ :=
  Sum.elim (![-(5/16), 5/16, -(5/16), 5/16] : Fin 4 → ℝ) (fun _ => 0)

theorem lamStar_0 (r : ℕ) : lamStar r (Sum.inl 0) = -(5/16) := by simp [lamStar]
theorem lamStar_1 (r : ℕ) : lamStar r (Sum.inl 1) = 5/16 := by simp [lamStar]
theorem lamStar_2 (r : ℕ) : lamStar r (Sum.inl 2) = -(5/16) := by simp [lamStar]
theorem lamStar_3 (r : ℕ) : lamStar r (Sum.inl 3) = 5/16 := by simp [lamStar]
theorem lamStar_pair (r : ℕ) (p : Fin r × Bool) : lamStar r (Sum.inr p) = 0 := rfl

/-- It closes the contrast exactly. -/
theorem lamStar_frozen (r : ℕ) : lamStar r ∈ FrozenAltC r := by
  show (lamStar r (Sum.inl 1) - lamStar r (Sum.inl 0))
        - (lamStar r (Sum.inl 3) - lamStar r (Sum.inl 2)) ≤ 0
  rw [lamStar_0, lamStar_1, lamStar_2, lamStar_3]; norm_num

/-- It keeps both arms centred and leaves the middle cells untouched, so it stays in the
class on which `energy` is the information. -/
theorem lamStar_centred (r : ℕ) :
    lamStar r (Sum.inl 0) + lamStar r (Sum.inl 1) = 0
      ∧ lamStar r (Sum.inl 2) + lamStar r (Sum.inl 3) = 0
      ∧ ∀ p : Fin r × Bool, lamStar r (Sum.inr p) = thetaC r (Sum.inr p) := by
  refine ⟨by rw [lamStar_0, lamStar_1]; ring, by rw [lamStar_2, lamStar_3]; ring, ?_⟩
  intro p; rw [lamStar_pair, thetaC_pair]

instance instNonemptyFrozenC (r : ℕ) : Nonempty (FrozenAltC r) :=
  ⟨⟨lamStar r, lamStar_frozen r⟩⟩

/-! ## The anchor mass, and the exact energy of the witness -/

/-- The mass a design puts on the four anchors. -/
noncomputable def aMass (w : Cell r → ℝ) : ℝ := ∑ i : Fin 4, w (Sum.inl i)

theorem aMass_add_middle (w : Cell r → ℝ) (hw : IsAlloc w) :
    aMass w + ∑ p : Fin r × Bool, w (Sum.inr p) = 1 := by
  have hs : ∑ e : Cell r, w e
      = (∑ i : Fin 4, w (Sum.inl i)) + ∑ p : Fin r × Bool, w (Sum.inr p) :=
    Fintype.sum_sum_type _
  rw [← hw.2, hs]; rfl

theorem aMass_le_one (w : Cell r → ℝ) (hw : IsAlloc w) : aMass w ≤ 1 := by
  have h := aMass_add_middle w hw
  have hm : 0 ≤ ∑ p : Fin r × Bool, w (Sum.inr p) :=
    Finset.sum_nonneg (fun p _ => hw.1 _)
  linarith

/-- **The witness costs exactly `(g^2/32)·a(w) = (9/512)·a(w)`.**  Each of the four
anchors moves by `g/4 = 3/16` at unit variance; the middle cells do not move at all. -/
theorem energy_lamStar (M : ℝ) (w : Cell r → ℝ) :
    energy w (pairVar M) (thetaC r) (lamStar r) = (9 / 512) * aMass w := by
  unfold energy aMass
  have hsplit : ∑ e : Cell r, w e * (lamStar r e - thetaC r e) ^ 2 / pairVar M e
      = (∑ i : Fin 4, w (Sum.inl i) * (lamStar r (Sum.inl i) - thetaC r (Sum.inl i)) ^ 2
          / pairVar (r := r) M (Sum.inl i))
        + ∑ p : Fin r × Bool,
            w (Sum.inr p) * (lamStar r (Sum.inr p) - thetaC r (Sum.inr p)) ^ 2
              / pairVar M (Sum.inr p) := Fintype.sum_sum_type _
  have hzero : ∀ p : Fin r × Bool,
      w (Sum.inr p) * (lamStar r (Sum.inr p) - thetaC r (Sum.inr p)) ^ 2
        / pairVar M (Sum.inr p) = 0 := by
    intro p; rw [lamStar_pair, thetaC_pair, sub_self]; simp
  have hv : ∀ i : Fin 4, pairVar (r := r) M (Sum.inl i) = 1 := fun _ => rfl
  rw [hsplit, Finset.sum_congr rfl (fun p _ => hzero p), Finset.sum_const_zero, add_zero,
      Fin.sum_univ_four, hv 0, hv 1, hv 2, hv 3,
      lamStar_0, lamStar_1, lamStar_2, lamStar_3,
      thetaC_0, thetaC_1, thetaC_2, thetaC_3, Fin.sum_univ_four]
  ring

/-! ## The frozen game, exactly -/

noncomputable def wUnifC (r : ℕ) : Cell r → ℝ := Sum.elim (fun _ => 1 / 4) (fun _ => 0)

theorem wUnifC_isAlloc (r : ℕ) : IsAlloc (wUnifC r) := by
  constructor
  · intro e; cases e <;> norm_num [wUnifC]
  · have hs : ∑ e : Cell r, wUnifC r e
        = (∑ _i : Fin 4, (1 : ℝ) / 4) + ∑ _p : Fin r × Bool, (0 : ℝ) :=
      Fintype.sum_sum_type _
    rw [hs, Finset.sum_const, Finset.sum_const_zero, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, add_zero]
    norm_num

instance instNonemptyAllocC (r : ℕ) : Nonempty {w : Cell r → ℝ // IsAlloc w} :=
  ⟨⟨wUnifC r, wUnifC_isAlloc r⟩⟩

noncomputable def frozenValueC (M : ℝ) (w : Cell r → ℝ) : ℝ :=
  ⨅ lam : FrozenAltC r, energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ)

noncomputable def frozenGameC (r : ℕ) (M : ℝ) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, frozenValueC M (w : Cell r → ℝ)

theorem pairVarC_pos (M : ℝ) (hM : 0 < M) (e : Cell r) : 0 < pairVar M e := by
  cases e with
  | inl i => show (0 : ℝ) < 1; norm_num
  | inr p => exact hM

theorem energyC_nonneg (M : ℝ) (hM : 0 < M) (w lam : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ energy w (pairVar M) (thetaC r) lam := by
  unfold energy
  have h : 0 ≤ ∑ e, w e * (lam e - thetaC r e) ^ 2 / pairVar M e :=
    Finset.sum_nonneg (fun e _ =>
      div_nonneg (mul_nonneg (hw e) (sq_nonneg _)) (pairVarC_pos M hM e).le)
  linarith

theorem bddBelowC (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (Set.range (fun lam : FrozenAltC r =>
      energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨lam, rfl⟩
  exact energyC_nonneg M hM w _ hw

/-- **The upper bound, and everything else follows from it.** -/
theorem frozenValueC_le (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w) :
    frozenValueC M w ≤ (9 / 512) * aMass w := by
  have h : frozenValueC M w ≤ energy w (pairVar M) (thetaC r) (lamStar r) :=
    ciInf_le (bddBelowC M hM w hw.1) (⟨lamStar r, lamStar_frozen r⟩ : FrozenAltC r)
  rwa [energy_lamStar] at h

/-- **Starvation, in one line.**  A design attaining the frozen optimum puts *nothing* on
the middle cells.  This needs only the upper bound --- no monotonicity modulus, no
homogeneity hypothesis. -/
theorem starvation_at_optimum (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w)
    (hopt : (9 : ℝ) / 512 ≤ frozenValueC M w) :
    aMass w = 1 ∧ ∑ p : Fin r × Bool, w (Sum.inr p) = 0 := by
  have hle := frozenValueC_le M hM w hw
  have h1 : (9 : ℝ) / 512 ≤ 9 / 512 * aMass w := le_trans hopt hle
  have ha1 : (1 : ℝ) ≤ aMass w := by nlinarith
  have ha2 := aMass_le_one w hw
  have haeq : aMass w = 1 := le_antisymm ha2 ha1
  refine ⟨haeq, ?_⟩
  have := aMass_add_middle w hw
  linarith [haeq]

/-- **Near-optimal starvation.**  A design within `eps` of the frozen optimum leaks at most
`eps / Gamma_frozen = (512/9)·eps` onto the middle cells --- the bridge from static
starvation to the exploration cost of a policy. -/
theorem near_optimal_starvation (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w)
    (ε : ℝ) (hnear : (9 : ℝ) / 512 - ε ≤ frozenValueC M w) :
    ∑ p : Fin r × Bool, w (Sum.inr p) ≤ (512 / 9) * ε := by
  have hle := frozenValueC_le M hM w hw
  have h1 : (9 : ℝ) / 512 - ε ≤ 9 / 512 * aMass w := le_trans hnear hle
  have hmid := aMass_add_middle w hw
  nlinarith [h1, hmid]

/-! ## The matching lower bound at the uniform-anchor design -/

theorem four_sq_lower_gen (x₀ x₁ x₂ x₃ c : ℝ) (hc : 0 ≤ c) (h : c ≤ x₀ - x₁ + x₂ - x₃) :
    c ^ 2 / 4 ≤ x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 := by
  nlinarith [sq_nonneg (x₀ + x₁), sq_nonneg (x₀ - x₂), sq_nonneg (x₀ + x₃),
    sq_nonneg (x₁ + x₂), sq_nonneg (x₁ - x₃), sq_nonneg (x₂ + x₃), h, hc]

theorem energy_wUnifC (M : ℝ) (L : Cell r → ℝ) :
    energy (wUnifC r) (pairVar M) (thetaC r) L
      = ((L (Sum.inl 0) - thetaC r (Sum.inl 0)) ^ 2
        + (L (Sum.inl 1) - thetaC r (Sum.inl 1)) ^ 2
        + (L (Sum.inl 2) - thetaC r (Sum.inl 2)) ^ 2
        + (L (Sum.inl 3) - thetaC r (Sum.inl 3)) ^ 2) / 8 := by
  unfold energy
  have hsplit : ∑ e : Cell r, wUnifC r e * (L e - thetaC r e) ^ 2 / pairVar M e
      = (∑ i : Fin 4, wUnifC r (Sum.inl i) * (L (Sum.inl i) - thetaC r (Sum.inl i)) ^ 2
          / pairVar (r := r) M (Sum.inl i))
        + ∑ p : Fin r × Bool,
            wUnifC r (Sum.inr p) * (L (Sum.inr p) - thetaC r (Sum.inr p)) ^ 2
              / pairVar M (Sum.inr p) := Fintype.sum_sum_type _
  have hzero : ∀ p : Fin r × Bool,
      wUnifC r (Sum.inr p) * (L (Sum.inr p) - thetaC r (Sum.inr p)) ^ 2
        / pairVar M (Sum.inr p) = 0 := by
    intro p
    have hw : wUnifC r (Sum.inr p) = 0 := rfl
    rw [hw, zero_mul, zero_div]
  have hanch : ∀ i : Fin 4,
      wUnifC r (Sum.inl i) * (L (Sum.inl i) - thetaC r (Sum.inl i)) ^ 2
        / pairVar (r := r) M (Sum.inl i)
        = (L (Sum.inl i) - thetaC r (Sum.inl i)) ^ 2 / 4 := by
    intro i
    have hw : wUnifC r (Sum.inl i) = 1 / 4 := rfl
    have hv : pairVar (r := r) M (Sum.inl i) = 1 := rfl
    rw [hw, hv]; ring
  rw [hsplit, Finset.sum_congr rfl (fun p _ => hzero p),
      Finset.sum_congr rfl (fun i _ => hanch i), Finset.sum_const_zero, add_zero,
      Fin.sum_univ_four]
  ring

/-- The uniform-anchor design attains the bound, so the frozen game's value is exactly
`9/512`. -/
theorem frozenValueC_unif_ge (M : ℝ) (hM : 0 < M) :
    (9 : ℝ) / 512 ≤ frozenValueC M (wUnifC r) := by
  refine le_ciInf (fun lam => ?_)
  have hc : ((lam : Cell r → ℝ) (Sum.inl 1) - (lam : Cell r → ℝ) (Sum.inl 0))
      - ((lam : Cell r → ℝ) (Sum.inl 3) - (lam : Cell r → ℝ) (Sum.inl 2)) ≤ 0 := lam.2
  -- the contrast gives  d0 - d1 + d3 - d2 >= g, so the last two slots are 3 then 2;
  -- the squared sum is the same set either way
  have hbase := four_sq_lower_gen
      ((lam : Cell r → ℝ) (Sum.inl 0) - thetaC r (Sum.inl 0))
      ((lam : Cell r → ℝ) (Sum.inl 1) - thetaC r (Sum.inl 1))
      ((lam : Cell r → ℝ) (Sum.inl 3) - thetaC r (Sum.inl 3))
      ((lam : Cell r → ℝ) (Sum.inl 2) - thetaC r (Sum.inl 2))
      (3 / 4 : ℝ) (by norm_num)
      (by rw [thetaC_0, thetaC_1, thetaC_2, thetaC_3]; linarith)
  rw [energy_wUnifC M]
  norm_num at hbase
  linarith

theorem bddAboveC (M : ℝ) (hM : 0 < M) :
    BddAbove (Set.range (fun w : {w : Cell r → ℝ // IsAlloc w} =>
      frozenValueC M (w : Cell r → ℝ))) := by
  refine ⟨9 / 512, ?_⟩
  rintro x ⟨w, rfl⟩
  have h := frozenValueC_le M hM (w : Cell r → ℝ) w.2
  have ha := aMass_le_one (w : Cell r → ℝ) w.2
  nlinarith [h, ha]

/-- **`Gamma_frozen = 9/512`, exactly.** -/
theorem frozenGameC_eq (M : ℝ) (hM : 0 < M) : frozenGameC r M = 9 / 512 := by
  refine le_antisymm ?_ ?_
  · refine ciSup_le (fun w => ?_)
    have h := frozenValueC_le M hM (w : Cell r → ℝ) w.2
    have ha := aMass_le_one (w : Cell r → ℝ) w.2
    nlinarith [h, ha]
  · exact le_trans (frozenValueC_unif_ge M hM)
      (le_ciSup (bddAboveC M hM) (⟨wUnifC r, wUnifC_isAlloc r⟩))

/-! ## The true game at the same world, and the consequence of starvation

Two different game *values* do not by themselves make the surrogate's policy expensive: an
objective off by a constant picks the right optimiser.  What follows is the link that does
the work.  The true alternatives are the worlds where arm `B` at least matches arm `A`, so
the compression answer is no longer `A`; the set is taken CLOSED, which is the object
`closure_exchange` licenses.  A pair alternative moves only the two middle cells of one
pair, so a design that starves the middle cells has *exactly zero* information against it,
and a design that is merely `eps`-optimal for the surrogate has at most `64 eps/(9 M r)`.
-/

/-- The closed true-alternative set: arm `B`'s range at least matches arm `A`'s. -/
def TrueAltC (r : ℕ) : Set (Cell r → ℝ) := {lam | rangeA lam ≤ rangeB lam}

instance instNonemptyTrueAltC (r : ℕ) : Nonempty (TrueAltC r) := by
  refine ⟨⟨fun _ => 0, ?_⟩⟩
  have hA : rangeA (fun _ : Cell r => (0 : ℝ)) = 0 := by simp [rangeA]
  have hB : rangeB (fun _ : Cell r => (0 : ℝ)) = 0 := by
    simp [rangeB]
  simp only [TrueAltC, Set.mem_setOf_eq, hA, hB]
  norm_num

noncomputable def trueValueC (M : ℝ) (w : Cell r → ℝ) : ℝ :=
  ⨅ lam : TrueAltC r, energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ)

noncomputable def trueGameC (r : ℕ) (M : ℝ) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, trueValueC M (w : Cell r → ℝ)

theorem pairVarC_pair (M : ℝ) (p : Fin r × Bool) : pairVar M (Sum.inr p) = M := rfl

theorem pairShiftC_anchor (j : Fin r) (d : ℝ) (i : Fin 4) :
    pairShift (thetaC r) j d (Sum.inl i) = thetaC r (Sum.inl i) :=
  pairShift_rest (thetaC r) j d _ (by simp) (by simp)

theorem pairShiftC_rangeA (j : Fin r) (d : ℝ) :
    rangeA (pairShift (thetaC r) j d) = 1 := by
  unfold rangeA
  rw [pairShiftC_anchor j d 1, pairShiftC_anchor j d 0, thetaC_0, thetaC_1]
  norm_num

theorem pairShiftC_value_true (j : Fin r) (d : ℝ) :
    pairShift (thetaC r) j d (Sum.inr (j, true)) = d := by
  have h := pairShift_true (thetaC r) j d
  rw [thetaC_pair] at h
  linarith

theorem pairShiftC_value_false (j : Fin r) (d : ℝ) :
    pairShift (thetaC r) j d (Sum.inr (j, false)) = -d := by
  have h := pairShift_false (thetaC r) j d
  rw [thetaC_pair] at h
  linarith

/-- Moving one pair apart by `d >= 1/2` makes arm `B` match arm `A`, so the shifted world
is a true alternative. -/
theorem pairShiftC_mem_trueAlt (j : Fin r) (d : ℝ) (hd : 1 / 2 ≤ d) :
    pairShift (thetaC r) j d ∈ TrueAltC r := by
  have hsup : d ≤ (BCells r).sup' (BCells_nonempty r) (pairShift (thetaC r) j d) := by
    have h := Finset.le_sup' (pairShift (thetaC r) j d) (bPair_mem r j true)
    rwa [pairShiftC_value_true] at h
  have hinf : (BCells r).inf' (BCells_nonempty r) (pairShift (thetaC r) j d) ≤ -d := by
    have h := Finset.inf'_le (pairShift (thetaC r) j d) (bPair_mem r j false)
    rwa [pairShiftC_value_false] at h
  simp only [TrueAltC, Set.mem_setOf_eq, rangeB]
  rw [pairShiftC_rangeA]
  linarith

theorem bddBelowTrueC (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (Set.range (fun lam : TrueAltC r =>
      energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨lam, rfl⟩
  exact energyC_nonneg M hM w _ hw

theorem trueValueC_nonneg (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ trueValueC M w :=
  le_ciInf (fun lam => energyC_nonneg M hM w _ hw)

/-- The energy of the half-unit pair shift, exactly: the pair's own weight over `8M`. -/
theorem energy_pairShiftC (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (j : Fin r) :
    energy w (pairVar M) (thetaC r) (pairShift (thetaC r) j (1 / 2))
      = pairWeight w j / (8 * M) := by
  rw [pair_shift_energy w (pairVar M) (thetaC r) (pairShift (thetaC r) j (1 / 2)) j M
      (1 / 2) hM (pairVarC_pair M (j, true)) (pairVarC_pair M (j, false))
      (pairShift_true (thetaC r) j (1 / 2)) (pairShift_false (thetaC r) j (1 / 2))
      (fun e h1 h2 => pairShift_rest (thetaC r) j (1 / 2) e h1 h2)]
  field_simp
  ring

/-- **The true value is bounded by the lightest pair's weight.** -/
theorem trueValueC_le_pairWeight (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ)
    (hw : ∀ e, 0 ≤ w e) (j : Fin r) :
    trueValueC M w ≤ pairWeight w j / (8 * M) := by
  have h : trueValueC M w
      ≤ energy w (pairVar M) (thetaC r) (pairShift (thetaC r) j (1 / 2)) :=
    ciInf_le (bddBelowTrueC M hM w hw)
      (⟨pairShift (thetaC r) j (1 / 2), pairShiftC_mem_trueAlt j (1 / 2) le_rfl⟩ :
        TrueAltC r)
  rwa [energy_pairShiftC M hM w j] at h

/-- A pigeonhole at an arbitrary budget, not only at one. -/
theorem exists_light_pair_le (r : ℕ) (hr : 0 < r) (g : Fin r → ℝ) (S : ℝ)
    (hsum : ∑ j, g j ≤ S) : ∃ j, g j ≤ S / (r : ℝ) := by
  by_contra hcon
  push_neg at hcon
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hbig : ∑ _j : Fin r, S / (r : ℝ) < ∑ j, g j :=
    Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hr)) (fun j _ => hcon j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbig
  have hcancel : (r : ℝ) * (S / (r : ℝ)) = S := by field_simp
  rw [hcancel] at hbig
  linarith

theorem middle_eq_sum_pairWeight (w : Cell r → ℝ) :
    ∑ p : Fin r × Bool, w (Sum.inr p) = ∑ j : Fin r, pairWeight w j := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold pairWeight
  rw [Fintype.sum_bool]

/-- **The true game is at most `1/(8 M r)`.**  Every design leaves some pair with at most
`1/r` of the budget, and that pair's alternative costs only its own weight. -/
theorem trueGameC_le (r : ℕ) (hr : 0 < r) (M : ℝ) (hM : 0 < M) :
    trueGameC r M ≤ 1 / (8 * M * (r : ℝ)) := by
  refine ciSup_le (fun w => ?_)
  obtain ⟨j, hj⟩ := exists_light_pair_le r hr (pairWeight (w : Cell r → ℝ)) 1
    (sum_pairWeight_le_one _ w.2)
  have h := trueValueC_le_pairWeight M hM (w : Cell r → ℝ) w.2.1 j
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have : pairWeight (w : Cell r → ℝ) j / (8 * M) ≤ 1 / (r : ℝ) / (8 * M) :=
    div_le_div_of_nonneg_right hj (by positivity)
  calc trueValueC M (w : Cell r → ℝ) ≤ pairWeight (w : Cell r → ℝ) j / (8 * M) := h
    _ ≤ 1 / (r : ℝ) / (8 * M) := this
    _ = 1 / (8 * M * (r : ℝ)) := by field_simp

/-- **The separation at the centred world**: the surrogate's game is `9/512` for every `M`,
the true game is at most `1/(8Mr)`, so the ratio is at most `64/(9 M r)`. -/
theorem centred_ratio_le (r : ℕ) (hr : 0 < r) (M : ℝ) (hM : 0 < M) :
    trueGameC r M / frozenGameC r M ≤ 64 / (9 * M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrr
  rw [frozenGameC_eq M hM, div_le_iff₀ (by norm_num : (0 : ℝ) < 9 / 512)]
  have heq : 64 / (9 * M * (r : ℝ)) * (9 / 512) = 1 / (8 * M * (r : ℝ)) := by
    field_simp
    ring
  rw [heq]
  exact trueGameC_le r hr M hM

/-! ### Starvation, and what it costs -/

/-- **A design that starves the middle cells has exactly zero true information.** -/
theorem starved_trueValueC_zero (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r)
    (w : Cell r → ℝ) (hw : IsAlloc w) (hstarve : ∑ p : Fin r × Bool, w (Sum.inr p) = 0) :
    trueValueC M w = 0 := by
  refine le_antisymm ?_ (trueValueC_nonneg M hM w hw.1)
  obtain ⟨j, hj⟩ := exists_light_pair_le r hr (pairWeight w) 0
    (by rw [← middle_eq_sum_pairWeight, hstarve])
  have hz : pairWeight w j ≤ 0 := by
    have : (0 : ℝ) / (r : ℝ) = 0 := by simp
    rwa [this] at hj
  have h := trueValueC_le_pairWeight M hM w hw.1 j
  have : pairWeight w j / (8 * M) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hz (by positivity)
  linarith

/-- **The frozen optimum carries no information about the true decision.**  This is the
step from "the two games have different values" to "the surrogate's design is useless": it
needs no monotonicity modulus, only the exact frozen value. -/
theorem frozen_optimum_true_value_zero (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r)
    (w : Cell r → ℝ) (hw : IsAlloc w) (hopt : (9 : ℝ) / 512 ≤ frozenValueC M w) :
    trueValueC M w = 0 :=
  starved_trueValueC_zero M hM r hr w hw (starvation_at_optimum M hM w hw hopt).2

/-- **The `eps`-optimal version, which is what a learner actually has.**  A design within
`eps` of the surrogate's optimum carries true information at most `64 eps/(9 M r)`: the
leak is `eps` times the whole separation factor, so an approximate optimiser of the wrong
objective is still starved at a controlled rate. -/
theorem near_optimal_trueValueC_le (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r)
    (w : Cell r → ℝ) (hw : IsAlloc w) (ε : ℝ) (hε : 0 ≤ ε)
    (hnear : (9 : ℝ) / 512 - ε ≤ frozenValueC M w) :
    trueValueC M w ≤ 64 * ε / (9 * M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hmid := near_optimal_starvation M hM w hw ε hnear
  obtain ⟨j, hj⟩ := exists_light_pair_le r hr (pairWeight w) ((512 / 9) * ε)
    (by rw [← middle_eq_sum_pairWeight]; exact hmid)
  have h := trueValueC_le_pairWeight M hM w hw.1 j
  have hstep : pairWeight w j / (8 * M) ≤ ((512 / 9) * ε) / (r : ℝ) / (8 * M) :=
    div_le_div_of_nonneg_right hj (by positivity)
  calc trueValueC M w ≤ pairWeight w j / (8 * M) := h
    _ ≤ ((512 / 9) * ε) / (r : ℝ) / (8 * M) := hstep
    _ = 64 * ε / (9 * M * (r : ℝ)) := by field_simp; ring

/-- **The hypotheses are satisfiable.**  The uniform-anchor design attains the frozen
optimum and starves the pairs, so the zero above is reached and the statement is not
vacuous. -/
theorem centred_starvation_witness (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r) :
    (9 : ℝ) / 512 ≤ frozenValueC M (wUnifC r) ∧ trueValueC M (wUnifC r) = 0 := by
  refine ⟨frozenValueC_unif_ge M hM, ?_⟩
  refine frozen_optimum_true_value_zero M hM r hr (wUnifC r) (wUnifC_isAlloc r)
    (frozenValueC_unif_ge M hM)

/-! ## The centred class, as a restriction of the INFIMUM

`energy` is the Gaussian information only on the class where each arm's cells sum to zero.
Every statement above takes the infimum over *all* frozen alternatives, and exhibits a
witness that happens to be centred.  That is not the same thing: the model's alternative
set is `FrozenAlt ∩ Theta_0`, and restricting the set an infimum ranges over can only raise
it, so an upper bound proved on the larger set does NOT transfer.

It transfers here for a reason, not by luck.  The witness `lamStar` is itself centred, so it
survives the restriction and still bounds the restricted infimum above; and the lower bound
at the uniform-anchor design was proved for every candidate, so it holds a fortiori on a
subset.  Both sides therefore move together and the value is unchanged.
-/

/-- The centred class: each arm's cells sum to zero. -/
def Centred (r : ℕ) : Set (Cell r → ℝ) :=
  {x | x (Sum.inl 0) + x (Sum.inl 1) = 0
    ∧ x (Sum.inl 2) + x (Sum.inl 3) + ∑ p : Fin r × Bool, x (Sum.inr p) = 0}

theorem thetaC_mem_centred (r : ℕ) : thetaC r ∈ Centred r := thetaC_centred r

theorem lamStar_mem_centred (r : ℕ) : lamStar r ∈ Centred r := by
  refine ⟨by rw [lamStar_0, lamStar_1]; ring, ?_⟩
  have hz : ∑ p : Fin r × Bool, lamStar r (Sum.inr p) = 0 :=
    Finset.sum_eq_zero (fun p _ => lamStar_pair r p)
  rw [lamStar_2, lamStar_3, hz]; ring

/-- The surrogate's alternatives INSIDE the class where energy is the information. -/
def FrozenAltC₀ (r : ℕ) : Set (Cell r → ℝ) := FrozenAltC r ∩ Centred r

theorem lamStar_frozenC₀ (r : ℕ) : lamStar r ∈ FrozenAltC₀ r :=
  ⟨lamStar_frozen r, lamStar_mem_centred r⟩

instance instNonemptyFrozenC₀ (r : ℕ) : Nonempty (FrozenAltC₀ r) :=
  ⟨⟨lamStar r, lamStar_frozenC₀ r⟩⟩

noncomputable def frozenValueC₀ (M : ℝ) (w : Cell r → ℝ) : ℝ :=
  ⨅ lam : FrozenAltC₀ r, energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ)

noncomputable def frozenGameC₀ (r : ℕ) (M : ℝ) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, frozenValueC₀ M (w : Cell r → ℝ)

theorem bddBelowC₀ (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (Set.range (fun lam : FrozenAltC₀ r =>
      energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨lam, rfl⟩
  exact energyC_nonneg M hM w _ hw

/-- **Restricting the infimum can only raise it.**  Stated explicitly, because it is the
direction that makes the unrestricted upper bound insufficient. -/
theorem frozenValueC_le_restricted (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ)
    (hw : ∀ e, 0 ≤ w e) :
    frozenValueC M w ≤ frozenValueC₀ M w :=
  le_ciInf (fun lam => ciInf_le (bddBelowC M hM w hw)
    (⟨(lam : Cell r → ℝ), lam.2.1⟩ : FrozenAltC r))

/-- **The upper bound survives the restriction**, because the witness is centred. -/
theorem frozenValueC₀_le (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w) :
    frozenValueC₀ M w ≤ (9 / 512) * aMass w := by
  have h : frozenValueC₀ M w ≤ energy w (pairVar M) (thetaC r) (lamStar r) :=
    ciInf_le (bddBelowC₀ M hM w hw.1) (⟨lamStar r, lamStar_frozenC₀ r⟩ : FrozenAltC₀ r)
  rwa [energy_lamStar] at h

/-- **`Gamma_frozen = 9/512` on the centred class too**, so the closed form is a statement
about the model's own alternative set and not an artefact of ignoring the constraint. -/
theorem frozenGameC₀_eq (r : ℕ) (M : ℝ) (hM : 0 < M) : frozenGameC₀ r M = 9 / 512 := by
  refine le_antisymm ?_ ?_
  · refine ciSup_le (fun w => ?_)
    have h := frozenValueC₀_le M hM (w : Cell r → ℝ) w.2
    have ha := aMass_le_one (w : Cell r → ℝ) w.2
    nlinarith [h, ha]
  · have hbdd : BddAbove (Set.range (fun w : {w : Cell r → ℝ // IsAlloc w} =>
        frozenValueC₀ M (w : Cell r → ℝ))) := by
      refine ⟨9 / 512, ?_⟩
      rintro x ⟨w, rfl⟩
      have h := frozenValueC₀_le M hM (w : Cell r → ℝ) w.2
      have ha := aMass_le_one (w : Cell r → ℝ) w.2
      nlinarith [h, ha]
    have hunif : (9 : ℝ) / 512 ≤ frozenValueC₀ M (wUnifC r) :=
      le_trans (frozenValueC_unif_ge M hM)
        (frozenValueC_le_restricted M hM (wUnifC r) (wUnifC_isAlloc r).1)
    exact le_trans hunif (le_ciSup hbdd (⟨wUnifC r, wUnifC_isAlloc r⟩))

/-- **Starvation, on the restricted set.**  The `eps`-version too, so the bridge to the
sequential cost is stated for the model's own alternatives. -/
theorem starvation_at_optimum₀ (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w)
    (hopt : (9 : ℝ) / 512 ≤ frozenValueC₀ M w) :
    aMass w = 1 ∧ ∑ p : Fin r × Bool, w (Sum.inr p) = 0 := by
  have hle := frozenValueC₀_le M hM w hw
  have ha1 : (1 : ℝ) ≤ aMass w := by nlinarith [le_trans hopt hle]
  have haeq : aMass w = 1 := le_antisymm (aMass_le_one w hw) ha1
  refine ⟨haeq, ?_⟩
  have := aMass_add_middle w hw
  linarith [haeq]

theorem near_optimal_starvation₀ (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w)
    (ε : ℝ) (hnear : (9 : ℝ) / 512 - ε ≤ frozenValueC₀ M w) :
    ∑ p : Fin r × Bool, w (Sum.inr p) ≤ (512 / 9) * ε := by
  have hle := frozenValueC₀_le M hM w hw
  have h1 : (9 : ℝ) / 512 - ε ≤ 9 / 512 * aMass w := le_trans hnear hle
  have hmid := aMass_add_middle w hw
  nlinarith [h1, hmid]

/-- **And the consequence, on the restricted set.** -/
theorem frozen_optimum_true_value_zero₀ (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r)
    (w : Cell r → ℝ) (hw : IsAlloc w) (hopt : (9 : ℝ) / 512 ≤ frozenValueC₀ M w) :
    trueValueC M w = 0 :=
  starved_trueValueC_zero M hM r hr w hw (starvation_at_optimum₀ M hM w hw hopt).2

theorem near_optimal_trueValueC_le₀ (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r)
    (w : Cell r → ℝ) (hw : IsAlloc w) (ε : ℝ) (hε : 0 ≤ ε)
    (hnear : (9 : ℝ) / 512 - ε ≤ frozenValueC₀ M w) :
    trueValueC M w ≤ 64 * ε / (9 * M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hmid := near_optimal_starvation₀ M hM w hw ε hnear
  obtain ⟨j, hj⟩ := exists_light_pair_le r hr (pairWeight w) ((512 / 9) * ε)
    (by rw [← middle_eq_sum_pairWeight]; exact hmid)
  have h := trueValueC_le_pairWeight M hM w hw.1 j
  have hstep : pairWeight w j / (8 * M) ≤ ((512 / 9) * ε) / (r : ℝ) / (8 * M) :=
    div_le_div_of_nonneg_right hj (by positivity)
  calc trueValueC M w ≤ pairWeight w j / (8 * M) := h
    _ ≤ ((512 / 9) * ε) / (r : ℝ) / (8 * M) := hstep
    _ = 64 * ε / (9 * M * (r : ℝ)) := by field_simp; ring

/-! ### The TRUE game on the same class, and strict alternatives inside it

The restriction above was applied to the surrogate's game.  It has to be applied to the
true game as well, or the ratio compares an infimum over one set with an infimum over
another.  It transfers for the same reason: the pair-shift witness is centred --- arm `A`
is untouched and the two moved middle cells move by `+d` and `-d`, so every arm still sums
to zero.

The closed set also has to be shown to be the closure of something non-empty on the strict
side, or `d = 1/2` could be an artefact of admitting the boundary.  It is not: for every
`delta > 0` the shift by `1/2 + delta` is a STRICTLY alternative world lying in the class,
so the bound is approached from inside.
-/

theorem sum_pairShiftC_middles (j : Fin r) (d : ℝ) :
    ∑ p : Fin r × Bool, pairShift (thetaC r) j d (Sum.inr p) = 0 := by
  classical
  have hterm : ∀ p : Fin r × Bool, p ∉ ({(j, true), (j, false)} : Finset (Fin r × Bool)) →
      pairShift (thetaC r) j d (Sum.inr p) = 0 := by
    intro p hp
    have h1 : (Sum.inr p : Cell r) ≠ Sum.inr (j, true) := by
      simpa using fun h => hp (by simp [h])
    have h2 : (Sum.inr p : Cell r) ≠ Sum.inr (j, false) := by
      simpa using fun h => hp (by simp [h])
    rw [pairShift_rest (thetaC r) j d (Sum.inr p) h1 h2, thetaC_pair]
  have hne : ((j, true) : Fin r × Bool) ≠ (j, false) := by simp
  rw [← Finset.sum_subset
      (Finset.subset_univ ({(j, true), (j, false)} : Finset (Fin r × Bool)))
      (fun p _ hp => hterm p hp)]
  rw [Finset.sum_pair hne, pairShiftC_value_true, pairShiftC_value_false]
  ring

/-- The pair shift stays in the centred class, so it is a legitimate alternative of the
model and not only of the geometry. -/
theorem pairShiftC_mem_centred (j : Fin r) (d : ℝ) :
    pairShift (thetaC r) j d ∈ Centred r := by
  refine ⟨?_, ?_⟩
  · rw [pairShiftC_anchor j d 0, pairShiftC_anchor j d 1, thetaC_0, thetaC_1]; ring
  · rw [pairShiftC_anchor j d 2, pairShiftC_anchor j d 3, thetaC_2, thetaC_3,
        sum_pairShiftC_middles j d]
    ring

/-- The true alternatives INSIDE the class on which energy is the information. -/
def TrueAltC₀ (r : ℕ) : Set (Cell r → ℝ) := TrueAltC r ∩ Centred r

theorem pairShiftC_mem_trueAlt₀ (j : Fin r) (d : ℝ) (hd : 1 / 2 ≤ d) :
    pairShift (thetaC r) j d ∈ TrueAltC₀ r :=
  ⟨pairShiftC_mem_trueAlt j d hd, pairShiftC_mem_centred j d⟩

instance instNonemptyTrueAltC₀ (r : ℕ) [NeZero r] : Nonempty (TrueAltC₀ r) :=
  ⟨⟨pairShift (thetaC r) ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩ (1 / 2),
    pairShiftC_mem_trueAlt₀ _ _ le_rfl⟩⟩

noncomputable def trueValueC₀ (M : ℝ) (w : Cell r → ℝ) : ℝ :=
  ⨅ lam : TrueAltC₀ r, energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ)

noncomputable def trueGameC₀ (r : ℕ) (M : ℝ) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, trueValueC₀ M (w : Cell r → ℝ)

theorem bddBelowTrueC₀ (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (Set.range (fun lam : TrueAltC₀ r =>
      energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨lam, rfl⟩
  exact energyC_nonneg M hM w _ hw

theorem trueValueC₀_nonneg (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) [NeZero r]
    (hw : ∀ e, 0 ≤ w e) : 0 ≤ trueValueC₀ M w :=
  le_ciInf (fun lam => energyC_nonneg M hM w _ hw)

theorem trueValueC₀_le_pairWeight (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ)
    (hw : ∀ e, 0 ≤ w e) (j : Fin r) :
    trueValueC₀ M w ≤ pairWeight w j / (8 * M) := by
  have h : trueValueC₀ M w
      ≤ energy w (pairVar M) (thetaC r) (pairShift (thetaC r) j (1 / 2)) :=
    ciInf_le (bddBelowTrueC₀ M hM w hw)
      (⟨pairShift (thetaC r) j (1 / 2), pairShiftC_mem_trueAlt₀ j (1 / 2) le_rfl⟩ :
        TrueAltC₀ r)
  rwa [energy_pairShiftC M hM w j] at h

/-- **The true game on the centred class is still at most `1/(8Mr)`.** -/
theorem trueGameC₀_le (r : ℕ) (hr : 0 < r) (M : ℝ) (hM : 0 < M) :
    trueGameC₀ r M ≤ 1 / (8 * M * (r : ℝ)) := by
  refine ciSup_le (fun w => ?_)
  obtain ⟨j, hj⟩ := exists_light_pair_le r hr (pairWeight (w : Cell r → ℝ)) 1
    (sum_pairWeight_le_one _ w.2)
  have h := trueValueC₀_le_pairWeight M hM (w : Cell r → ℝ) w.2.1 j
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hstep : pairWeight (w : Cell r → ℝ) j / (8 * M) ≤ 1 / (r : ℝ) / (8 * M) :=
    div_le_div_of_nonneg_right hj (by positivity)
  calc trueValueC₀ M (w : Cell r → ℝ) ≤ pairWeight (w : Cell r → ℝ) j / (8 * M) := h
    _ ≤ 1 / (r : ℝ) / (8 * M) := hstep
    _ = 1 / (8 * M * (r : ℝ)) := by field_simp

/-- **The separation, with BOTH games restricted to the same class `Theta_0`, on the same
world `thetaC`.**  This is the statement the paper may quote: nothing here mixes a bound
from one construction with a value from another. -/
theorem centred_ratio₀_le (r : ℕ) (hr : 0 < r) (M : ℝ) (hM : 0 < M) :
    trueGameC₀ r M / frozenGameC₀ r M ≤ 64 / (9 * M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrr
  rw [frozenGameC₀_eq r M hM, div_le_iff₀ (by norm_num : (0 : ℝ) < 9 / 512)]
  have heq : 64 / (9 * M * (r : ℝ)) * (9 / 512) = 1 / (8 * M * (r : ℝ)) := by
    field_simp
    ring
  rw [heq]
  exact trueGameC₀_le r hr M hM

/-- **Strict alternatives lie inside the class**, so the closed set is not doing the work:
for every `delta > 0` the shift by `1/2 + delta` has arm `B`'s range STRICTLY above arm
`A`'s and is centred. -/
theorem pairShiftC_strict_alt (j : Fin r) (δ : ℝ) (hδ : 0 < δ) :
    rangeA (pairShift (thetaC r) j (1 / 2 + δ))
        < rangeB (pairShift (thetaC r) j (1 / 2 + δ))
      ∧ pairShift (thetaC r) j (1 / 2 + δ) ∈ Centred r := by
  refine ⟨?_, pairShiftC_mem_centred j (1 / 2 + δ)⟩
  have hsup : 1 / 2 + δ
      ≤ (BCells r).sup' (BCells_nonempty r) (pairShift (thetaC r) j (1 / 2 + δ)) := by
    have h := Finset.le_sup' (pairShift (thetaC r) j (1 / 2 + δ)) (bPair_mem r j true)
    rwa [pairShiftC_value_true] at h
  have hinf : (BCells r).inf' (BCells_nonempty r) (pairShift (thetaC r) j (1 / 2 + δ))
      ≤ -(1 / 2 + δ) := by
    have h := Finset.inf'_le (pairShift (thetaC r) j (1 / 2 + δ)) (bPair_mem r j false)
    rwa [pairShiftC_value_false] at h
  rw [pairShiftC_rangeA]
  unfold rangeB
  linarith

/-- The value at a strict alternative, so the bound is approached from inside the set. -/
theorem trueValueC₀_strict_le (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e)
    (j : Fin r) (δ : ℝ) (hδ : 0 < δ) :
    trueValueC₀ M w ≤ pairWeight w j * (1 / 2 + δ) ^ 2 / (2 * M) := by
  have hmem : pairShift (thetaC r) j (1 / 2 + δ) ∈ TrueAltC₀ r :=
    ⟨by
        have hs := pairShiftC_strict_alt (r := r) j δ hδ
        exact le_of_lt hs.1,
      pairShiftC_mem_centred j (1 / 2 + δ)⟩
  have h : trueValueC₀ M w
      ≤ energy w (pairVar M) (thetaC r) (pairShift (thetaC r) j (1 / 2 + δ)) :=
    ciInf_le (bddBelowTrueC₀ M hM w hw)
      (⟨pairShift (thetaC r) j (1 / 2 + δ), hmem⟩ : TrueAltC₀ r)
  rwa [pair_shift_energy w (pairVar M) (thetaC r) (pairShift (thetaC r) j (1 / 2 + δ)) j M
      (1 / 2 + δ) hM (pairVarC_pair M (j, true)) (pairVarC_pair M (j, false))
      (pairShift_true (thetaC r) j (1 / 2 + δ))
      (pairShift_false (thetaC r) j (1 / 2 + δ))
      (fun e h1 h2 => pairShift_rest (thetaC r) j (1 / 2 + δ) e h1 h2)] at h

/-- **The consequence, with both games on `Theta_0`.** -/
theorem frozen_optimum_trueValueC₀_zero (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r)
    [NeZero r] (w : Cell r → ℝ) (hw : IsAlloc w)
    (hopt : (9 : ℝ) / 512 ≤ frozenValueC₀ M w) :
    trueValueC₀ M w = 0 := by
  refine le_antisymm ?_ (trueValueC₀_nonneg M hM w hw.1)
  have hstarve := (starvation_at_optimum₀ M hM w hw hopt).2
  obtain ⟨j, hj⟩ := exists_light_pair_le r hr (pairWeight w) 0
    (by rw [← middle_eq_sum_pairWeight, hstarve])
  have hz : pairWeight w j ≤ 0 := by
    have h0 : (0 : ℝ) / (r : ℝ) = 0 := by simp
    rwa [h0] at hj
  have h := trueValueC₀_le_pairWeight M hM w hw.1 j
  have hneg : pairWeight w j / (8 * M) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hz (by positivity)
  linarith

theorem near_optimal_trueValueC₀_le (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r)
    (w : Cell r → ℝ) (hw : IsAlloc w) (ε : ℝ) (hε : 0 ≤ ε)
    (hnear : (9 : ℝ) / 512 - ε ≤ frozenValueC₀ M w) :
    trueValueC₀ M w ≤ 64 * ε / (9 * M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hmid := near_optimal_starvation₀ M hM w hw ε hnear
  obtain ⟨j, hj⟩ := exists_light_pair_le r hr (pairWeight w) ((512 / 9) * ε)
    (by rw [← middle_eq_sum_pairWeight]; exact hmid)
  have h := trueValueC₀_le_pairWeight M hM w hw.1 j
  have hstep : pairWeight w j / (8 * M) ≤ ((512 / 9) * ε) / (r : ℝ) / (8 * M) :=
    div_le_div_of_nonneg_right hj (by positivity)
  calc trueValueC₀ M w ≤ pairWeight w j / (8 * M) := h
    _ ≤ ((512 / 9) * ε) / (r : ℝ) / (8 * M) := hstep
    _ = 64 * ε / (9 * M * (r : ℝ)) := by field_simp; ring

/-! ### The true game is not free: a matching lower bound on the same construction

The upper bound says the adversary can always find a cheap alternative.  Without a lower
bound the ratio could be zero for a trivial reason.  The design that certifies it is
"weight proportional to variance",

    w_e = sigma_e^2 / (4 + 2 r M),

under which the energy of any candidate is the plain squared distance over `2(4+2rM)`.  A
world that reverses the decision must move the four extremum cells by a contrast of at
least `g = 3/4`, and Cauchy--Schwarz turns that into `9/64` of squared distance.
-/

/-- The variance-proportional design. -/
noncomputable def wCert (r : ℕ) (M : ℝ) : Cell r → ℝ :=
  fun e => pairVar M e / (4 + 2 * (r : ℝ) * M)

theorem wCert_isAlloc (r : ℕ) (M : ℝ) (hM : 0 < M) : IsAlloc (wCert r M) := by
  have hden : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by positivity
  refine ⟨fun e => ?_, ?_⟩
  · exact div_nonneg (pairVarC_pos M hM e).le hden.le
  · unfold wCert
    rw [← Finset.sum_div]
    have hs : ∑ e : Cell r, pairVar M e = 4 + 2 * (r : ℝ) * M := by
      have hsplit : ∑ e : Cell r, pairVar (r := r) M e
          = (∑ _a : Fin 4, (1 : ℝ)) + ∑ _p : Fin r × Bool, M :=
        Fintype.sum_sum_type _
      have h1 : (∑ _a : Fin 4, (1 : ℝ)) = 4 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
      have h2 : (∑ _p : Fin r × Bool, M) = 2 * (r : ℝ) * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
      rw [hsplit, h1, h2]
    rw [hs, div_self (ne_of_gt hden)]

/-- At that design the energy is the squared distance, scaled once. -/
theorem energy_wCert (r : ℕ) (M : ℝ) (hM : 0 < M) (L : Cell r → ℝ) :
    energy (wCert r M) (pairVar M) (thetaC r) L
      = (∑ e, (L e - thetaC r e) ^ 2) / (2 * (4 + 2 * (r : ℝ) * M)) := by
  have hden : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by positivity
  have key : ∀ e : Cell r,
      wCert r M e * (L e - thetaC r e) ^ 2 / pairVar M e
        = (L e - thetaC r e) ^ 2 / (4 + 2 * (r : ℝ) * M) := by
    intro e
    have hv : pairVar (r := r) M e ≠ 0 := ne_of_gt (pairVarC_pos M hM e)
    have hrw : wCert r M e * (L e - thetaC r e) ^ 2 / pairVar M e
        = pairVar M e / pairVar M e
            * ((L e - thetaC r e) ^ 2 / (4 + 2 * (r : ℝ) * M)) := by
      unfold wCert
      ring
    rw [hrw, div_self hv, one_mul]
  have hsum : ∑ e : Cell r, wCert r M e * (L e - thetaC r e) ^ 2 / pairVar M e
      = ∑ e : Cell r, (L e - thetaC r e) ^ 2 / (4 + 2 * (r : ℝ) * M) :=
    Finset.sum_congr rfl (fun e _ => key e)
  unfold energy
  rw [hsum, ← Finset.sum_div, div_div, mul_comm (4 + 2 * (r : ℝ) * M) 2]

/-- Arm `B`'s cells all carry `|theta| <= 1/8`, so `B`'s range at the true world is `1/4`. -/
theorem thetaC_bcell_bound (r : ℕ) (e : Cell r) (he : e ∈ BCells r) :
    -(1 / 8 : ℝ) ≤ thetaC r e ∧ thetaC r e ≤ 1 / 8 := by
  classical
  rw [BCells, Finset.mem_filter] at he
  obtain ⟨-, hb⟩ := he
  match e with
  | Sum.inl a =>
      have hor : a = 2 ∨ a = 3 := by
        simpa [isBCell, Bool.or_eq_true, decide_eq_true_iff] using hb
      rcases hor with rfl | rfl
      · rw [thetaC_2]; constructor <;> norm_num
      · rw [thetaC_3]; constructor <;> norm_num
  | Sum.inr p => rw [thetaC_pair]; constructor <;> norm_num

/-- **The contrast a true alternative must move, at `thetaC`.**  Arm `A`'s range is `1` and
arm `B`'s is `1/4`, so reversing the decision costs a contrast of at least `3/4` --- three
times what the `r`-pair world could force. -/
theorem contrast_movesC (r : ℕ) (L : Cell r → ℝ) (hrev : rangeA L ≤ rangeB L) :
    ∃ p ∈ BCells r, ∃ q ∈ BCells r,
      (3 : ℝ) / 4 ≤ (L (Sum.inl 0) - thetaC r (Sum.inl 0))
          - (L (Sum.inl 1) - thetaC r (Sum.inl 1))
          + (L p - thetaC r p) - (L q - thetaC r q) := by
  classical
  obtain ⟨p, hp, hpv⟩ := Finset.exists_mem_eq_sup' (BCells_nonempty r) L
  obtain ⟨q, hq, hqv⟩ := Finset.exists_mem_eq_inf' (BCells_nonempty r) L
  have hrB : rangeB L = L p - L q := by
    unfold rangeB; rw [hpv, hqv]
  have hA : L (Sum.inl 1) - L (Sum.inl 0) ≤ rangeA L := rangeA_ge L
  have hBθ : thetaC r p - thetaC r q ≤ 1 / 4 := by
    have hb := thetaC_bcell_bound r p hp
    have hbq := thetaC_bcell_bound r q hq
    linarith [hb.2, hbq.1]
  refine ⟨p, hp, q, hq, ?_⟩
  have hgap : thetaC r (Sum.inl 1) - thetaC r (Sum.inl 0) = 1 := by
    rw [thetaC_0, thetaC_1]; norm_num
  rw [hrB] at hrev
  linarith [hA, hrev, hBθ, hgap]

/-- The four cells the contrast names are distinct from arm `A`'s two, so their squares can
be split off the total. -/
theorem bcell_ne_anchorA (r : ℕ) (e : Cell r) (he : e ∈ BCells r) :
    e ≠ Sum.inl 0 ∧ e ≠ Sum.inl 1 := by
  classical
  rw [BCells, Finset.mem_filter] at he
  constructor <;> intro hc <;> rw [hc] at he <;> simp [isBCell] at he

/-- **The true value at the certifying design is bounded below.** -/
theorem trueValueC₀_wCert_ge (r : ℕ) (M : ℝ) (hM : 0 < M) [NeZero r] :
    (9 : ℝ) / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueValueC₀ M (wCert r M) := by
  classical
  have hden : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by positivity
  refine le_ciInf (fun lam => ?_)
  obtain ⟨L, hL⟩ : ∃ L : Cell r → ℝ, (L : Cell r → ℝ) = (lam : Cell r → ℝ) := ⟨_, rfl⟩
  have hrev : rangeA (lam : Cell r → ℝ) ≤ rangeB (lam : Cell r → ℝ) := lam.2.1
  obtain ⟨p, hp, q, hq, hcon⟩ := contrast_movesC r (lam : Cell r → ℝ) hrev
  set δ : Cell r → ℝ := fun e => (lam : Cell r → ℝ) e - thetaC r e with hδ
  by_cases hpq : p = q
  · -- the B-range collapses: the contrast lives on arm `A` alone, and two squares suffice
    subst hpq
    have h2 : (3 : ℝ) / 4 ≤ δ (Sum.inl 0) - δ (Sum.inl 1) := by
      simp only [hδ] at hcon ⊢; linarith
    have hsq : (9 : ℝ) / 32 ≤ δ (Sum.inl 0) ^ 2 + δ (Sum.inl 1) ^ 2 := by
      nlinarith [sq_nonneg (δ (Sum.inl 0) + δ (Sum.inl 1)), h2]
    have hsub : δ (Sum.inl 0) ^ 2 + δ (Sum.inl 1) ^ 2 ≤ ∑ e, δ e ^ 2 := by
      have hne : (Sum.inl 0 : Cell r) ≠ Sum.inl 1 := by
        intro h; exact absurd (Sum.inl.inj h) (by decide)
      have hss : ({Sum.inl 0, Sum.inl 1} : Finset (Cell r)) ⊆ Finset.univ :=
        Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg hss
        (fun e _ _ => sq_nonneg (δ e))
      rwa [Finset.sum_pair hne] at this
    have hkey : (9 : ℝ) / 64 ≤ ∑ e, ((lam : Cell r → ℝ) e - thetaC r e) ^ 2 := by
      simp only [hδ] at hsub hsq ⊢; linarith
    have hid : (9 : ℝ) / (128 * (4 + 2 * (r : ℝ) * M))
        = (9 / 64) / (2 * (4 + 2 * (r : ℝ) * M)) := by
      field_simp
      ring
    rw [energy_wCert r M hM, hid]
    exact div_le_div_of_nonneg_right hkey (by positivity)
  · have hdistinct : ((Sum.inl 0 : Cell r) ≠ Sum.inl 1) ∧ (Sum.inl 0 : Cell r) ≠ p
        ∧ (Sum.inl 0 : Cell r) ≠ q ∧ (Sum.inl 1 : Cell r) ≠ p
        ∧ (Sum.inl 1 : Cell r) ≠ q ∧ p ≠ q := by
      refine ⟨by intro h; exact absurd (Sum.inl.inj h) (by decide), ?_, ?_, ?_, ?_, hpq⟩
      · exact fun h => (bcell_ne_anchorA r p hp).1 h.symm
      · exact fun h => (bcell_ne_anchorA r q hq).1 h.symm
      · exact fun h => (bcell_ne_anchorA r p hp).2 h.symm
      · exact fun h => (bcell_ne_anchorA r q hq).2 h.symm
    have hsq : (9 : ℝ) / 64
        ≤ δ (Sum.inl 0) ^ 2 + δ (Sum.inl 1) ^ 2 + δ p ^ 2 + δ q ^ 2 := by
      have h := four_sq_lower_gen (δ (Sum.inl 0)) (δ (Sum.inl 1)) (δ p) (δ q) (3 / 4)
        (by norm_num) (by simp only [hδ] at hcon ⊢; linarith)
      norm_num at h
      linarith [h]
    have hsub : δ (Sum.inl 0) ^ 2 + δ (Sum.inl 1) ^ 2 + δ p ^ 2 + δ q ^ 2
        ≤ ∑ e, δ e ^ 2 := by
      obtain ⟨h01, h0p, h0q, h1p, h1q, hpq'⟩ := hdistinct
      have hss : ({Sum.inl 0, Sum.inl 1, p, q} : Finset (Cell r)) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hss
        (fun e _ _ => sq_nonneg (δ e))
      have hcard : ∑ e ∈ ({Sum.inl 0, Sum.inl 1, p, q} : Finset (Cell r)), δ e ^ 2
          = δ (Sum.inl 0) ^ 2 + δ (Sum.inl 1) ^ 2 + δ p ^ 2 + δ q ^ 2 := by
        rw [Finset.sum_insert (by simp [h01, h0p, h0q]),
            Finset.sum_insert (by simp [h1p, h1q]),
            Finset.sum_pair hpq']
        ring
      rwa [hcard] at hle
    have hkey : (9 : ℝ) / 64 ≤ ∑ e, ((lam : Cell r → ℝ) e - thetaC r e) ^ 2 := by
      simp only [hδ] at hsub hsq ⊢; linarith
    have hid : (9 : ℝ) / (128 * (4 + 2 * (r : ℝ) * M))
        = (9 / 64) / (2 * (4 + 2 * (r : ℝ) * M)) := by
      field_simp
      ring
    rw [energy_wCert r M hM, hid]
    exact div_le_div_of_nonneg_right hkey (by positivity)

/-- **`Gamma_true` is bounded below on the centred class.** -/
theorem trueGameC₀_ge (r : ℕ) (M : ℝ) (hM : 0 < M) [NeZero r] :
    (9 : ℝ) / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueGameC₀ r M := by
  have hbdd : BddAbove (Set.range (fun w : {w : Cell r → ℝ // IsAlloc w} =>
      trueValueC₀ M (w : Cell r → ℝ))) := by
    refine ⟨1 / (8 * M * (r : ℝ)), ?_⟩
    rintro x ⟨w, rfl⟩
    obtain ⟨j, hj⟩ := exists_light_pair_le r (Nat.pos_of_ne_zero (NeZero.ne r))
      (pairWeight (w : Cell r → ℝ)) 1 (sum_pairWeight_le_one _ w.2)
    have hrr : (0 : ℝ) < (r : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
    have h := trueValueC₀_le_pairWeight M hM (w : Cell r → ℝ) w.2.1 j
    have hstep : pairWeight (w : Cell r → ℝ) j / (8 * M) ≤ 1 / (r : ℝ) / (8 * M) :=
      div_le_div_of_nonneg_right hj (by positivity)
    have hid : 1 / (r : ℝ) / (8 * M) = 1 / (8 * M * (r : ℝ)) := by field_simp
    linarith [h, hstep, hid.le, hid.ge]
  exact le_trans (trueValueC₀_wCert_ge r M hM)
    (le_ciSup hbdd (⟨wCert r M, wCert_isAlloc r M hM⟩))

/-- **The separation, both sides, on one construction and one parameter class.**
`4/(4+2rM) <= Gamma_true/Gamma_frozen <= 64/(9rM)`: a `Theta((rM)^{-1})` gap that is
present already at `M = 1`, so it is not bought by inflating a variance. -/
theorem centred_separation (r : ℕ) (hr : 0 < r) (M : ℝ) (hM : 0 < M) [NeZero r] :
    4 / (4 + 2 * (r : ℝ) * M) ≤ trueGameC₀ r M / frozenGameC₀ r M
      ∧ trueGameC₀ r M / frozenGameC₀ r M ≤ 64 / (9 * M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hden : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by positivity
  refine ⟨?_, centred_ratio₀_le r hr M hM⟩
  rw [frozenGameC₀_eq r M hM, le_div_iff₀ (by norm_num : (0 : ℝ) < 9 / 512)]
  have heq : 4 / (4 + 2 * (r : ℝ) * M) * (9 / 512)
      = 9 / (128 * (4 + 2 * (r : ℝ) * M)) := by
    field_simp
    ring
  rw [heq]
  exact trueGameC₀_ge r M hM

/-! ## Audit -/

#print axioms thetaC_centred
#print axioms frozen_margin
#print axioms lamStar_frozen
#print axioms lamStar_centred
#print axioms energy_lamStar
#print axioms frozenValueC_le
#print axioms starvation_at_optimum
#print axioms near_optimal_starvation
#print axioms four_sq_lower_gen
#print axioms frozenValueC_unif_ge
#print axioms frozenGameC_eq

#print axioms trueGameC_le
#print axioms centred_ratio_le
#print axioms starved_trueValueC_zero
#print axioms frozen_optimum_true_value_zero
#print axioms near_optimal_trueValueC_le
#print axioms centred_starvation_witness
#print axioms frozenGameC₀_eq
#print axioms frozenValueC_le_restricted
#print axioms starvation_at_optimum₀
#print axioms frozen_optimum_true_value_zero₀
#print axioms near_optimal_trueValueC_le₀
#print axioms pairShiftC_mem_centred
#print axioms trueGameC₀_le
#print axioms centred_ratio₀_le
#print axioms pairShiftC_strict_alt
#print axioms trueValueC₀_strict_le
#print axioms frozen_optimum_trueValueC₀_zero
#print axioms near_optimal_trueValueC₀_le
#print axioms wCert_isAlloc
#print axioms energy_wCert
#print axioms contrast_movesC
#print axioms trueValueC₀_wCert_ge
#print axioms trueGameC₀_ge
#print axioms centred_separation

end CIGAMF.P13.PaperACentred
