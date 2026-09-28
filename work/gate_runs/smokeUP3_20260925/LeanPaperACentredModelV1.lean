import «LeanPaperACentredV1»

/-!
# Paper A: the centred construction as an actual observation model

`LeanPaperACentredV1` proves the separation for two games defined by `energy` over subsets
of a parameter class.  That is not yet a statement about compression: it has to be the case
that the class, the response map and the observation law appearing in the *information*
theorem are the ones appearing in the *compression* theorem.  Proving realisability at the
single world `thetaC` does not do it.

This module closes that gap for the construction, and it does so in the form that explains
why the class is what it is.

THE MODEL.  Two arms.  Arm `A` has two cells, arm `B` has `2 + 2r`.  The response of a
parameter `lam` at the pair `(a, b)` is additive,

    F_lam (a, b) = lam_A a + lam_B b,

and the reference is the uniform product.  Retaining one arm means explaining the response
by that arm's own marginal and paying the oscillation of what is left.

WHY `Theta_0` IS THE RIGHT CLASS, AND NOT AN EXTRA HYPOTHESIS.  The marginal of the
additive response is

    Q_A^lam a = lam_A a + mean_b (lam_B b),

so `Q_A^lam = lam_A` for every `a` **exactly when** arm `B`'s cells sum to zero.  Centring
is therefore not a convenience bolted onto the construction: it is precisely the condition
under which the uniform-product marginal recovers the coordinate, and `centred_iff_marginals`
below states that as an `iff` rather than as two separate requirements.

WHAT FOLLOWS.  Once the marginal is the coordinate, the residual after retaining `A` is
*literally* `lam_B`, so the compression loss of retaining `A` is half the range of arm `B` —
and the true-alternative set of `LeanPaperACentredV1`, `{lam | rangeA lam <= rangeB lam}`,
is exactly `{lam | loss of retaining B <= loss of retaining A}`: the worlds where the
decision flips.  The geometry the games are about is the compression loss, not a stand-in.
-/

namespace CIGAMF.P13.PaperACentredModel

open Finset
open CIGAMF.P13.PaperARPair
open CIGAMF.P13.PaperACentred

variable {r : ℕ}

/-! ## The two arms as index sets -/

/-- Arm `B`'s index set: its two extremum cells, then the `r` pairs. -/
abbrev BIdx (r : ℕ) := Bool ⊕ (Fin r × Bool)

/-- Arm `A`'s cells inside the flat cell space. -/
def aCell : Bool → Cell r := fun a => Sum.inl (if a then 1 else 0)

/-- Arm `B`'s cells inside the flat cell space. -/
def bCell : BIdx r → Cell r :=
  Sum.elim (fun b => Sum.inl (if b then 3 else 2)) (fun p => Sum.inr p)

/-- Arm `A`'s table. -/
def tblA (lam : Cell r → ℝ) : Bool → ℝ := fun a => lam (aCell a)

/-- Arm `B`'s table. -/
def tblB (lam : Cell r → ℝ) : BIdx r → ℝ := fun b => lam (bCell b)

theorem sum_tblA (lam : Cell r → ℝ) :
    ∑ a : Bool, tblA lam a = lam (Sum.inl 0) + lam (Sum.inl 1) := by
  rw [Fintype.sum_bool]
  simp [tblA, aCell]
  ring

theorem sum_tblB (lam : Cell r → ℝ) :
    ∑ b : BIdx r, tblB lam b
      = lam (Sum.inl 2) + lam (Sum.inl 3) + ∑ p : Fin r × Bool, lam (Sum.inr p) := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ b : Bool, tblB lam (Sum.inl b) = lam (Sum.inl 2) + lam (Sum.inl 3) := by
    rw [Fintype.sum_bool]
    simp [tblB, bCell]
    ring
  have h2 : ∑ p : Fin r × Bool, tblB lam (Sum.inr p) = ∑ p : Fin r × Bool, lam (Sum.inr p) :=
    rfl
  rw [h1, h2]

/-! ## The response, the uniform product reference and its marginals -/

/-- The additive response: arm `A`'s value plus arm `B`'s. -/
def respF (lam : Cell r → ℝ) : Bool × BIdx r → ℝ :=
  fun x => tblA lam x.1 + tblB lam x.2

/-- Arm `A`'s marginal under the uniform product reference. -/
noncomputable def margA (lam : Cell r → ℝ) (a : Bool) : ℝ :=
  (∑ b : BIdx r, respF lam (a, b)) / (Fintype.card (BIdx r) : ℝ)

/-- Arm `B`'s marginal under the uniform product reference. -/
noncomputable def margB (lam : Cell r → ℝ) (b : BIdx r) : ℝ :=
  (∑ a : Bool, respF lam (a, b)) / 2

theorem card_BIdx (r : ℕ) : (Fintype.card (BIdx r) : ℝ) = 2 + 2 * (r : ℝ) := by
  simp [BIdx, Fintype.card_sum, Fintype.card_prod]
  push_cast
  ring

theorem margA_eq (lam : Cell r → ℝ) (a : Bool) :
    margA lam a = tblA lam a + (∑ b : BIdx r, tblB lam b) / (2 + 2 * (r : ℝ)) := by
  have hpos : (0 : ℝ) < 2 + 2 * (r : ℝ) := by positivity
  have hsplit : ∑ b : BIdx r, respF lam (a, b)
      = (∑ _b : BIdx r, tblA lam a) + ∑ b : BIdx r, tblB lam b := by
    rw [← Finset.sum_add_distrib]
    rfl
  have hconst : ∑ _b : BIdx r, tblA lam a = (2 + 2 * (r : ℝ)) * tblA lam a := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_BIdx r]
  unfold margA
  rw [hsplit, hconst, card_BIdx r]
  field_simp

theorem margB_eq (lam : Cell r → ℝ) (b : BIdx r) :
    margB lam b = tblB lam b + (∑ a : Bool, tblA lam a) / 2 := by
  have hsplit : ∑ a : Bool, respF lam (a, b)
      = (∑ a : Bool, tblA lam a) + ∑ _a : Bool, tblB lam b := by
    rw [← Finset.sum_add_distrib]
    rfl
  have hconst : ∑ _a : Bool, tblB lam b = 2 * tblB lam b := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    norm_num
  unfold margB
  rw [hsplit, hconst]
  ring

/-- **The marginal recovers arm `A`'s coordinate exactly when arm `B` is centred.** -/
theorem margA_eq_tblA_iff (lam : Cell r → ℝ) :
    (∀ a, margA lam a = tblA lam a) ↔ ∑ b : BIdx r, tblB lam b = 0 := by
  have hpos : (0 : ℝ) < 2 + 2 * (r : ℝ) := by positivity
  constructor
  · intro h
    have hh := h true
    rw [margA_eq] at hh
    have hz : (∑ b : BIdx r, tblB lam b) / (2 + 2 * (r : ℝ)) = 0 := by linarith
    rcases div_eq_zero_iff.mp hz with h0 | h0
    · exact h0
    · exact absurd h0 (ne_of_gt hpos)
  · intro h a
    rw [margA_eq, h]
    simp

/-- **And arm `B`'s exactly when arm `A` is centred.** -/
theorem margB_eq_tblB_iff (lam : Cell r → ℝ) :
    (∀ b, margB lam b = tblB lam b) ↔ ∑ a : Bool, tblA lam a = 0 := by
  constructor
  · intro h
    have hh := h (Sum.inl true)
    rw [margB_eq] at hh
    have hz : (∑ a : Bool, tblA lam a) / 2 = 0 := by linarith
    linarith [hz]
  · intro h b
    rw [margB_eq, h]
    simp

/-- **`Theta_0` is the class on which both marginals recover their coordinates.**  Stated as
an equivalence, because that is what the class is *for*: it is not an extra hypothesis. -/
theorem centred_iff_marginals (lam : Cell r → ℝ) :
    lam ∈ Centred r ↔ ((∀ a, margA lam a = tblA lam a) ∧ ∀ b, margB lam b = tblB lam b) := by
  rw [margA_eq_tblA_iff, margB_eq_tblB_iff, sum_tblA, sum_tblB]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨h1, h2⟩

/-! ## The compression loss of retaining one arm -/

/-- Retaining `A`: what the response leaves unexplained at `(a, b)`. -/
noncomputable def residA (lam : Cell r → ℝ) (x : Bool × BIdx r) : ℝ :=
  respF lam x - margA lam x.1

/-- **On the centred class the residual after retaining `A` is exactly arm `B`'s table** ---
it does not depend on `a` at all. -/
theorem residA_eq (lam : Cell r → ℝ) (hc : lam ∈ Centred r) (x : Bool × BIdx r) :
    residA lam x = tblB lam x.2 := by
  have h := ((centred_iff_marginals lam).mp hc).1 x.1
  unfold residA respF
  rw [h]
  ring

/-! ## The compression loss of retaining one arm, as a range

The residual is a function of arm `B`'s index alone, so its oscillation over the grid is
arm `B`'s range — the very function the games' alternative sets are written with.  That is
what makes the geometry of `LeanPaperACentredV1` the geometry of the compression loss, and
not a stand-in for it.
-/

theorem isBCell_bCell (b : BIdx r) : isBCell (bCell b) = true := by
  cases b with
  | inl c => cases c <;> rfl
  | inr p => rfl

theorem mem_BCells_iff (e : Cell r) : e ∈ BCells r ↔ isBCell e = true := by
  rw [BCells, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem bCell_mem (b : BIdx r) : bCell b ∈ BCells r :=
  (mem_BCells_iff _).mpr (isBCell_bCell b)

/-- Arm `B`'s index set maps ONTO arm `B`'s cells. -/
theorem exists_bCell (e : Cell r) (he : e ∈ BCells r) : ∃ b : BIdx r, bCell b = e := by
  have h := (mem_BCells_iff e).mp he
  match e with
  | Sum.inl a =>
      have hor : a = 2 ∨ a = 3 := by
        simpa [isBCell, Bool.or_eq_true, decide_eq_true_iff] using h
      rcases hor with rfl | rfl
      · exact ⟨Sum.inl false, rfl⟩
      · exact ⟨Sum.inl true, rfl⟩
  | Sum.inr p => exact ⟨Sum.inr p, rfl⟩

theorem univ_BIdx_nonempty (r : ℕ) : (Finset.univ : Finset (BIdx r)).Nonempty :=
  ⟨Sum.inl false, Finset.mem_univ _⟩

/-- **Arm `B`'s range is the oscillation of its table.**  Proved by antisymmetry rather than
by rewriting the index set, which a dependent `sup'` does not admit. -/
theorem rangeB_eq_osc (lam : Cell r → ℝ) :
    rangeB lam
      = (Finset.univ : Finset (BIdx r)).sup' (univ_BIdx_nonempty r) (tblB lam)
        - (Finset.univ : Finset (BIdx r)).inf' (univ_BIdx_nonempty r) (tblB lam) := by
  classical
  have hsup : (BCells r).sup' (BCells_nonempty r) lam
      = (Finset.univ : Finset (BIdx r)).sup' (univ_BIdx_nonempty r) (tblB lam) := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup'_le _ _ (fun e he => ?_)
      obtain ⟨b, rfl⟩ := exists_bCell e he
      exact Finset.le_sup' (tblB lam) (Finset.mem_univ b)
    · refine Finset.sup'_le _ _ (fun b _ => ?_)
      exact Finset.le_sup' lam (bCell_mem b)
  have hinf : (BCells r).inf' (BCells_nonempty r) lam
      = (Finset.univ : Finset (BIdx r)).inf' (univ_BIdx_nonempty r) (tblB lam) := by
    refine le_antisymm ?_ ?_
    · refine Finset.le_inf' _ _ (fun b _ => ?_)
      exact Finset.inf'_le lam (bCell_mem b)
    · refine Finset.le_inf' _ _ (fun e he => ?_)
      obtain ⟨b, rfl⟩ := exists_bCell e he
      exact Finset.inf'_le (tblB lam) (Finset.mem_univ b)
  unfold rangeB
  rw [hsup, hinf]

/-- The loss of retaining arm `A`: half the oscillation of what arm `A` cannot explain. -/
noncomputable def lossRetainA (lam : Cell r → ℝ) : ℝ :=
  ((Finset.univ : Finset (BIdx r)).sup' (univ_BIdx_nonempty r) (fun b => residA lam (true, b))
    - (Finset.univ : Finset (BIdx r)).inf' (univ_BIdx_nonempty r)
        (fun b => residA lam (true, b))) / 2

/-- **Retaining `A` costs half arm `B`'s range.**  On the centred class, and by the residual
identity — not by definition. -/
theorem lossRetainA_eq (lam : Cell r → ℝ) (hc : lam ∈ Centred r) :
    lossRetainA lam = rangeB lam / 2 := by
  classical
  have hfun : (fun b : BIdx r => residA lam (true, b)) = tblB lam := by
    funext b
    exact residA_eq lam hc (true, b)
  unfold lossRetainA
  rw [hfun, ← rangeB_eq_osc]

/-! ## Which retained set is safe, at a tolerance

Retaining `A` is `eps`-unsafe exactly when its loss exceeds the competitor's by more than
`eps`.  With the two losses computed above this is a statement about the two ranges, and the
inequality is **strict**: at a tie, retaining `A` is still correct.
-/

/-- Retaining `A` is `eps`-unsafe against retaining `B`. -/
def UnsafeA (ε : ℝ) (lam : Cell r → ℝ) : Prop :=
  lossRetainA lam > rangeA lam / 2 + ε

/-- **The decision rule, in the ranges.**  `rangeA lam / 2` is the loss of retaining `B`,
so this is `L(A) > L(B) + eps`. -/
theorem unsafeA_iff_range_gap (ε : ℝ) (lam : Cell r → ℝ) (hc : lam ∈ Centred r) :
    UnsafeA ε lam ↔ rangeB lam > rangeA lam + 2 * ε := by
  unfold UnsafeA
  rw [lossRetainA_eq lam hc]
  constructor <;> intro h <;> linarith

/-- **At zero tolerance the unsafe set is the STRICT one**, and the closed set
`TrueAltC` of `LeanPaperACentredV1` contains it but is strictly larger: a tie is in the
closed set and is *not* unsafe.  Stating this is the point --- the games are solved over the
closed set, and that has to be justified rather than assumed. -/
theorem unsafeA_zero_iff (lam : Cell r → ℝ) (hc : lam ∈ Centred r) :
    UnsafeA 0 lam ↔ rangeA lam < rangeB lam := by
  rw [unsafeA_iff_range_gap 0 lam hc]
  constructor <;> intro h <;> linarith

theorem unsafe_subset_closed (lam : Cell r → ℝ) (hc : lam ∈ Centred r)
    (h : UnsafeA 0 lam) : lam ∈ TrueAltC r := by
  have := (unsafeA_zero_iff lam hc).mp h
  exact le_of_lt this

/-! ## Audit -/

#print axioms sum_tblA
#print axioms sum_tblB
#print axioms margA_eq
#print axioms margA_eq_tblA_iff
#print axioms margB_eq_tblB_iff
#print axioms centred_iff_marginals
#print axioms residA_eq
#print axioms exists_bCell
#print axioms rangeB_eq_osc
#print axioms lossRetainA_eq
#print axioms unsafeA_iff_range_gap
#print axioms unsafeA_zero_iff
#print axioms unsafe_subset_closed

end CIGAMF.P13.PaperACentredModel
