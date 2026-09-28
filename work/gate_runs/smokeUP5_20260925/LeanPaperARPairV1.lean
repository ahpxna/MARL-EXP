import Mathlib

/-!
# Paper A: the `r`-pair family -- separation without heteroscedasticity

The A-low separation of `LeanPaperASeparationV1` needs the variance `M` to grow: the ratio
is `64/M`, so at `M = 1` it says nothing.  That leaves the separation looking like an
artefact of a badly conditioned observation model.

It is not.  Widen the relation instead of the variance: give each arm `2r + 2` actions, with
`r` disjoint PAIRS of middle cells in arm `B`.  The frozen proxy still watches only the four
anchors, while the adversary may move whichever pair the design has measured least.  With
`r` pairs and a unit budget some pair carries weight at most `1/r`, so the true value falls
like `1/r` while the proxy value does not move at all.

    Gamma_proxy >= 1/512,        Gamma_true <= 1/(8 M r),
    hence   Gamma_true / Gamma_proxy <= 64/(r M).

At `M = 1` that is `64/r`, which tends to zero.  So the separation survives a HOMOGENEOUS
observation model, and what drives it is the number of alternatives the proxy ignores, not
the conditioning.

## SCOPE

The matching lower bound on `Gamma_true` -- which would turn `<=` into `Theta` -- is not
here.  It needs the range argument of the eight-cell case carried across to `2r + 2`
actions, and only the upper side is proved below.  What IS proved is enough for the
headline: no constant-factor guarantee, at fixed variance, as `r` grows.
-/

namespace CIGAMF.P13.PaperARPair

open scoped BigOperators

/-- A cell: one of four anchors, or one half of one of the `r` middle pairs. -/
abbrev Cell (r : ℕ) := Fin 4 ⊕ (Fin r × Bool)

variable {r : ℕ}

/-- The information a design gives against a candidate world. -/
noncomputable def energy (w var θ lam : Cell r → ℝ) : ℝ :=
  (∑ e, w e * (lam e - θ e) ^ 2 / var e) / 2

/-- An allocation. -/
def IsAlloc (w : Cell r → ℝ) : Prop := (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1

/-! ## Pigeonhole: some pair is barely measured -/

/-- **Among `r` disjoint pairs sharing at most a unit of weight, one pair carries at most
`1/r`.**  This is the whole mechanism: the adversary reads the design and then picks that
pair. -/
theorem exists_light_pair (r : ℕ) (hr : 0 < r) (g : Fin r → ℝ) (hg : ∀ j, 0 ≤ g j)
    (hsum : ∑ j, g j ≤ 1) : ∃ j, g j ≤ 1 / (r : ℝ) := by
  by_contra hcon
  push_neg at hcon
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hlt : ∀ j : Fin r, (1 : ℝ) / (r : ℝ) < g j := fun j => hcon j
  have hbig : ∑ _j : Fin r, (1 : ℝ) / (r : ℝ) < ∑ j, g j := by
    refine Finset.sum_lt_sum_of_nonempty ?_ (fun j _ => hlt j)
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hr)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbig
  rw [mul_one_div, div_self (ne_of_gt hrr)] at hbig
  linarith

/-- The weight a design puts on pair `j`. -/
noncomputable def pairWeight (w : Cell r → ℝ) (j : Fin r) : ℝ :=
  w (Sum.inr (j, true)) + w (Sum.inr (j, false))

theorem pairWeight_nonneg (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) (j : Fin r) :
    0 ≤ pairWeight w j :=
  add_nonneg (hw _) (hw _)

/-- The pairs are disjoint and sit inside the budget, so their weights sum to at most one. -/
theorem sum_pairWeight_le_one (w : Cell r → ℝ) (hw : IsAlloc w) :
    ∑ j : Fin r, pairWeight w j ≤ 1 := by
  classical
  obtain ⟨hpos, hsum⟩ := hw
  have hsplit : ∑ e : Cell r, w e
      = (∑ a : Fin 4, w (Sum.inl a)) + ∑ p : Fin r × Bool, w (Sum.inr p) :=
    Fintype.sum_sum_type _
  have hpair : ∑ p : Fin r × Bool, w (Sum.inr p) = ∑ j : Fin r, pairWeight w j := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold pairWeight
    rw [Fintype.sum_bool]
  have hanch : 0 ≤ ∑ a : Fin 4, w (Sum.inl a) :=
    Finset.sum_nonneg fun a _ => hpos _
  rw [hpair] at hsplit
  rw [hsplit] at hsum
  linarith

/-! ## The cost of moving one pair -/

/-- **The energy of a two-cell opposite shift, exactly.**  Only the two moved cells
contribute, and they both have variance `M`. -/
theorem pair_shift_energy (w var θ lam : Cell r → ℝ) (j : Fin r) (M d : ℝ) (hM : 0 < M)
    (hvt : var (Sum.inr (j, true)) = M) (hvf : var (Sum.inr (j, false)) = M)
    (hdt : lam (Sum.inr (j, true)) - θ (Sum.inr (j, true)) = d)
    (hdf : lam (Sum.inr (j, false)) - θ (Sum.inr (j, false)) = -d)
    (hrest : ∀ e, e ≠ Sum.inr (j, true) → e ≠ Sum.inr (j, false) → lam e = θ e) :
    energy w var θ lam = pairWeight w j * d ^ 2 / (2 * M) := by
  classical
  unfold energy pairWeight
  have hterm : ∀ e : Cell r, e ≠ Sum.inr (j, true) → e ≠ Sum.inr (j, false) →
      w e * (lam e - θ e) ^ 2 / var e = 0 := by
    intro e h1 h2
    rw [hrest e h1 h2]
    simp
  have hne : (Sum.inr (j, true) : Cell r) ≠ Sum.inr (j, false) := by simp
  rw [← Finset.sum_subset
      (Finset.subset_univ ({Sum.inr (j, true), Sum.inr (j, false)} : Finset (Cell r)))
      (fun e _ he => hterm e (by simpa using fun h => he (by simp [h]))
        (by simpa using fun h => he (by simp [h])))]
  rw [Finset.sum_pair hne, hdt, hdf, hvt, hvf]
  field_simp

/-- The candidate that moves one pair apart by `d`, named so that its values reduce without
beta-reduction gymnastics. -/
noncomputable def pairShift (θ : Cell r → ℝ) (j : Fin r) (d : ℝ) : Cell r → ℝ :=
  fun e => if e = Sum.inr (j, true) then θ e + d
    else if e = Sum.inr (j, false) then θ e - d else θ e

theorem pairShift_true (θ : Cell r → ℝ) (j : Fin r) (d : ℝ) :
    pairShift θ j d (Sum.inr (j, true)) - θ (Sum.inr (j, true)) = d := by
  unfold pairShift
  rw [if_pos rfl]
  ring

theorem pairShift_false (θ : Cell r → ℝ) (j : Fin r) (d : ℝ) :
    pairShift θ j d (Sum.inr (j, false)) - θ (Sum.inr (j, false)) = -d := by
  unfold pairShift
  rw [if_neg (by simp), if_pos rfl]
  ring

theorem pairShift_rest (θ : Cell r → ℝ) (j : Fin r) (d : ℝ) (e : Cell r)
    (h1 : e ≠ Sum.inr (j, true)) (h2 : e ≠ Sum.inr (j, false)) :
    pairShift θ j d e = θ e := by
  unfold pairShift
  rw [if_neg h1, if_neg h2]

/-- **The true game is at most `1/(8 M r)`, at fixed `M`.**

For every design there is a pair carrying at most `1/r`, and moving that pair by `d`
overshoots arm `A`'s range as soon as `d > 1/2`, so the adversary pays only
`d^2/(2 M r)`.  Letting `d` approach `1/2` gives `1/(8 M r)`. -/
theorem light_pair_energy_le (w var θ : Cell r → ℝ) (hw : IsAlloc w) (hr : 0 < r)
    (M : ℝ) (hM : 0 < M) (hvar : ∀ (j : Fin r) (b : Bool), var (Sum.inr (j, b)) = M)
    (d : ℝ) (hd : 0 < d) :
    ∃ j : Fin r, energy w var θ (pairShift θ j d) ≤ d ^ 2 / (2 * M * (r : ℝ)) := by
  obtain ⟨j, hj⟩ := exists_light_pair r hr (pairWeight w)
    (pairWeight_nonneg w hw.1) (sum_pairWeight_le_one w hw)
  refine ⟨j, ?_⟩
  rw [pair_shift_energy w var θ (pairShift θ j d) j M d hM (hvar j true) (hvar j false)
      (pairShift_true θ j d) (pairShift_false θ j d)
      (fun e h1 h2 => pairShift_rest θ j d e h1 h2)]
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpw : 0 ≤ pairWeight w j := pairWeight_nonneg w hw.1 j
  have hkey : pairWeight w j * (r : ℝ) ≤ 1 := (le_div_iff₀ hrr).mp hj
  have hprod : 2 * M * d ^ 2 * (pairWeight w j * (r : ℝ)) ≤ 2 * M * d ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hprod]

/-! ## The ratio, and what it says at fixed variance -/

/-- **The separation ratio.**  With the proxy pinned at `1/512` and the true game at most
`1/(8 M r)`, the ratio is at most `64/(r M)`. -/
theorem rpair_ratio_le (M Gtrue Gproxy : ℝ) (r : ℕ) (hr : 0 < r) (hM : 0 < M)
    (htrue : Gtrue ≤ 1 / (8 * M * (r : ℝ))) (hproxy : 1 / 512 ≤ Gproxy)
    (hpos : 0 < Gproxy) :
    Gtrue / Gproxy ≤ 64 / ((r : ℝ) * M) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h1 : Gtrue / Gproxy ≤ (1 / (8 * M * (r : ℝ))) / Gproxy :=
    div_le_div_of_nonneg_right htrue (le_of_lt hpos)
  have h2 : (1 / (8 * M * (r : ℝ))) / Gproxy ≤ (1 / (8 * M * (r : ℝ))) / (1 / 512) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hproxy
  have h3 : (1 / (8 * M * (r : ℝ))) / (1 / 512 : ℝ) = 64 / ((r : ℝ) * M) := by
    field_simp
    ring
  linarith [h1, h2, h3.le, h3.ge]

/-- **No constant factor, at FIXED variance.**  Take `M = 1`: for every candidate factor
`c` there is a number of pairs at which the ratio falls below it.  So the separation is not
an artefact of heteroscedasticity -- it is driven by how many alternatives the frozen proxy
declines to look at. -/
theorem no_constant_factor_at_unit_variance (c : ℝ) (hc : 0 < c) :
    ∃ r : ℕ, 0 < r ∧ ∀ Gtrue Gproxy : ℝ,
      Gtrue ≤ 1 / (8 * 1 * (r : ℝ)) → 1 / 512 ≤ Gproxy → 0 < Gproxy →
      Gtrue / Gproxy < c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (64 / c)
  refine ⟨n + 1, Nat.succ_pos n, fun Gtrue Gproxy ht hp hpos => ?_⟩
  have hrr : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hbig : 64 / c < ((n + 1 : ℕ) : ℝ) := by
    push_cast
    push_cast at hn
    linarith
  have hratio := rpair_ratio_le 1 Gtrue Gproxy (n + 1) (Nat.succ_pos n) one_pos ht hp hpos
  have hlt : 64 / (((n + 1 : ℕ) : ℝ) * 1) < c := by
    rw [mul_one, div_lt_iff₀ hrr]
    rw [div_lt_iff₀ hc] at hbig
    linarith
  linarith

/-! ## The matching lower bound

The upper bound says the adversary can be cheap.  The lower bound says it cannot be free,
and together they pin the ratio at `Theta((rM)^{-1})`.

The argument does not redo the eight-cell proof.  It picks the two extremes OF THE
ALTERNATIVE's arm-`B` table -- not of the displacement -- so the two indices are automatically
distinct once the alternative is strict, and the four cells it touches are four distinct
cells.  A linear contrast on those four must then move by at least `1/4`, and
Cauchy-Schwarz turns that into squared displacement `1/64`.

Arm `A` is represented by its two extreme anchors: the family's alternatives never move
arm `A`'s interior, so its range is the anchor spread. -/

/-- Arm `B`'s cells: its two anchors and all of the pairs. -/
def isBCell (e : Cell r) : Bool :=
  Sum.elim (fun a : Fin 4 => a = 2 || a = 3) (fun _ => true) e

def BCells (r : ℕ) : Finset (Cell r) := Finset.univ.filter (fun e => isBCell e = true)

theorem bAnchor_mem (r : ℕ) : (Sum.inl 2 : Cell r) ∈ BCells r := by
  rw [BCells, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, rfl⟩

theorem bPair_mem (r : ℕ) (j : Fin r) (b : Bool) :
    (Sum.inr (j, b) : Cell r) ∈ BCells r := by
  rw [BCells, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, rfl⟩

theorem BCells_nonempty (r : ℕ) : (BCells r).Nonempty := ⟨Sum.inl 2, bAnchor_mem r⟩

/-- Arm `B`'s range: the spread of the table over `B`'s cells. -/
noncomputable def rangeB (x : Cell r → ℝ) : ℝ :=
  (BCells r).sup' (BCells_nonempty r) x - (BCells r).inf' (BCells_nonempty r) x

/-- Arm `A`'s range, through its two anchors. -/
noncomputable def rangeA (x : Cell r → ℝ) : ℝ :=
  |x (Sum.inl 1) - x (Sum.inl 0)|

theorem rangeA_ge (x : Cell r → ℝ) : x (Sum.inl 1) - x (Sum.inl 0) ≤ rangeA x :=
  le_abs_self _

theorem rangeB_nonneg (x : Cell r → ℝ) : 0 ≤ rangeB x := by
  unfold rangeB
  have h1 : (BCells r).inf' (BCells_nonempty r) x ≤ x (Sum.inl 2) :=
    Finset.inf'_le x (bAnchor_mem r)
  have h2 : x (Sum.inl 2) ≤ (BCells r).sup' (BCells_nonempty r) x :=
    Finset.le_sup' x (bAnchor_mem r)
  linarith

/-- **The contrast a strict alternative must move.**

Choosing `p` and `q` as the extremes of the ALTERNATIVE's table makes them distinct as soon
as the alternative is strict, which is what keeps the four cells below from colliding. -/
theorem contrast_moves (r : ℕ) (θ lam : Cell r → ℝ)
    (hgap : θ (Sum.inl 1) - θ (Sum.inl 0) = 1)
    (hB : ∀ e ∈ BCells r, ∀ e' ∈ BCells r, θ e - θ e' ≤ 3 / 4)
    (hstrict : rangeA lam < rangeB lam) :
    ∃ p ∈ BCells r, ∃ q ∈ BCells r, p ≠ q ∧
      1 / 4 < (lam (Sum.inl 0) - θ (Sum.inl 0)) - (lam (Sum.inl 1) - θ (Sum.inl 1))
        + (lam p - θ p) - (lam q - θ q) := by
  classical
  obtain ⟨p, hp, hpv⟩ := Finset.exists_mem_eq_sup' (BCells_nonempty r) lam
  obtain ⟨q, hq, hqv⟩ := Finset.exists_mem_eq_inf' (BCells_nonempty r) lam
  have hrB : rangeB lam = lam p - lam q := by
    unfold rangeB
    rw [hpv, hqv]
  have hA : 1 + (lam (Sum.inl 1) - θ (Sum.inl 1)) - (lam (Sum.inl 0) - θ (Sum.inl 0))
      ≤ rangeA lam := by
    have := rangeA_ge lam
    linarith [hgap]
  have hBle : θ p - θ q ≤ 3 / 4 := hB p hp q hq
  have hne : p ≠ q := by
    intro h
    rw [h] at hrB
    have : rangeB lam = 0 := by rw [hrB]; ring
    have hA0 : 0 ≤ rangeA lam := abs_nonneg _
    linarith [hstrict, this, hA0]
  refine ⟨p, hp, q, hq, hne, ?_⟩
  rw [hrB] at hstrict
  linarith [hA, hstrict, hBle]

/-- Four numbers whose alternating sum exceeds `1/4` carry squared norm at least `1/64`. -/
theorem four_sq_lower (x₁ x₂ x₃ x₄ : ℝ) (h : 1 / 4 < x₁ - x₂ + x₃ - x₄) :
    1 / 64 ≤ x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 := by
  have hcs : 4 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) - (x₁ - x₂ + x₃ - x₄) ^ 2
      = (x₁ + x₂) ^ 2 + (x₁ - x₃) ^ 2 + (x₁ + x₄) ^ 2 + (x₂ + x₃) ^ 2
        + (x₂ - x₄) ^ 2 + (x₃ + x₄) ^ 2 := by ring
  have hnn : 0 ≤ (x₁ + x₂) ^ 2 + (x₁ - x₃) ^ 2 + (x₁ + x₄) ^ 2 + (x₂ + x₃) ^ 2
        + (x₂ - x₄) ^ 2 + (x₃ + x₄) ^ 2 := by positivity
  nlinarith [hcs, hnn, h]

/-- The variance profile: unit on the four anchors, `M` on the pairs. -/
noncomputable def pairVar (M : ℝ) : Cell r → ℝ := Sum.elim (fun _ => 1) (fun _ => M)

/-- The uniform-precision design: weight proportional to variance. -/
noncomputable def anchorDesign (r : ℕ) (M : ℝ) : Cell r → ℝ :=
  Sum.elim (fun _ => 1 / (4 + 2 * (r : ℝ) * M)) (fun _ => M / (4 + 2 * (r : ℝ) * M))

theorem anchorDesign_isAlloc (r : ℕ) (M : ℝ) (hM : 0 < M) :
    IsAlloc (anchorDesign r M) := by
  classical
  have hrn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hZ : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by nlinarith [hrn, hM.le]
  constructor
  · intro e
    cases e with
    | inl a => exact div_nonneg (by norm_num) hZ.le
    | inr p => exact div_nonneg hM.le hZ.le
  · have hsplit : ∑ e : Cell r, anchorDesign r M e
        = (∑ _a : Fin 4, 1 / (4 + 2 * (r : ℝ) * M))
          + ∑ _p : Fin r × Bool, M / (4 + 2 * (r : ℝ) * M) :=
      Fintype.sum_sum_type _
    rw [hsplit, Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
        Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
        nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    field_simp

/-- **The true game is at least `1/(128(4 + 2rM))`.**

With precision made uniform the energy is the plain squared displacement over `2Z`, and the
four cells the contrast touches already carry `1/64` of it. -/
theorem rpair_true_ge (r : ℕ) (M : ℝ) (hM : 0 < M) (θ lam : Cell r → ℝ)
    (hgap : θ (Sum.inl 1) - θ (Sum.inl 0) = 1)
    (hB : ∀ e ∈ BCells r, ∀ e' ∈ BCells r, θ e - θ e' ≤ 3 / 4)
    (hstrict : rangeA lam < rangeB lam) :
    1 / (128 * (4 + 2 * (r : ℝ) * M))
      ≤ energy (anchorDesign r M) (pairVar M) θ lam := by
  classical
  have hrn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hZ : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by nlinarith [hrn, hM.le]
  obtain ⟨p, hp, q, hq, hne, hcon⟩ := contrast_moves r θ lam hgap hB hstrict
  set d : Cell r → ℝ := fun e => lam e - θ e with hd
  have hfour : 1 / 64 ≤ d (Sum.inl 0) ^ 2 + d (Sum.inl 1) ^ 2 + d p ^ 2 + d q ^ 2 := by
    have := four_sq_lower (d (Sum.inl 0)) (d (Sum.inl 1)) (d p) (d q) (by
      simpa [hd] using hcon)
    linarith
  -- the design makes the precision uniform
  have hprec : ∀ e : Cell r,
      anchorDesign r M e * d e ^ 2 / pairVar M e
        = d e ^ 2 / (4 + 2 * (r : ℝ) * M) := by
    intro e
    cases e with
    | inl a =>
        unfold anchorDesign pairVar
        simp only [Sum.elim_inl]
        field_simp
    | inr t =>
        unfold anchorDesign pairVar
        simp only [Sum.elim_inr]
        field_simp
  have hsum : ∑ e : Cell r, anchorDesign r M e * d e ^ 2 / pairVar M e
      = (∑ e : Cell r, d e ^ 2) / (4 + 2 * (r : ℝ) * M) := by
    rw [Finset.sum_congr rfl (fun e _ => hprec e), ← Finset.sum_div]
  -- the four cells are distinct, so their squares are part of the total
  have hsub : ({Sum.inl 0, Sum.inl 1, p, q} : Finset (Cell r)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hA0 : (Sum.inl 0 : Cell r) ≠ Sum.inl 1 := by simp
  have hA0p : (Sum.inl 0 : Cell r) ≠ p := by
    intro h
    have : isBCell (Sum.inl (0 : Fin 4) : Cell r) = true := by
      rw [h]; simpa [BCells] using (Finset.mem_filter.mp hp).2
    simp [isBCell] at this
  have hA0q : (Sum.inl 0 : Cell r) ≠ q := by
    intro h
    have : isBCell (Sum.inl (0 : Fin 4) : Cell r) = true := by
      rw [h]; simpa [BCells] using (Finset.mem_filter.mp hq).2
    simp [isBCell] at this
  have hA1p : (Sum.inl 1 : Cell r) ≠ p := by
    intro h
    have : isBCell (Sum.inl (1 : Fin 4) : Cell r) = true := by
      rw [h]; simpa [BCells] using (Finset.mem_filter.mp hp).2
    simp [isBCell] at this
  have hA1q : (Sum.inl 1 : Cell r) ≠ q := by
    intro h
    have : isBCell (Sum.inl (1 : Fin 4) : Cell r) = true := by
      rw [h]; simpa [BCells] using (Finset.mem_filter.mp hq).2
    simp [isBCell] at this
  have hpart : d (Sum.inl 0) ^ 2 + d (Sum.inl 1) ^ 2 + d p ^ 2 + d q ^ 2
      ≤ ∑ e : Cell r, d e ^ 2 := by
    have hcard : ∑ e ∈ ({Sum.inl 0, Sum.inl 1, p, q} : Finset (Cell r)), d e ^ 2
        = d (Sum.inl 0) ^ 2 + d (Sum.inl 1) ^ 2 + d p ^ 2 + d q ^ 2 := by
      rw [Finset.sum_insert (by simp [hA0, hA0p, hA0q]),
          Finset.sum_insert (by simp [hA1p, hA1q]),
          Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
      ring
    rw [← hcard]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => sq_nonneg _)
  unfold energy
  rw [hsum, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hfour, hpart, hZ]

/-- **The two-sided bound.**  With the upper bound already in hand the ratio is pinned. -/
theorem rpair_ratio_ge (M Gtrue Gproxy : ℝ) (r : ℕ) (hr : 0 < r) (hM : 0 < M)
    (htrue : 1 / (128 * (4 + 2 * (r : ℝ) * M)) ≤ Gtrue)
    (hproxy : Gproxy ≤ 1 / 512) (hpos : 0 < Gproxy) :
    2 / (2 + (r : ℝ) * M) ≤ Gtrue / Gproxy := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hZ : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by nlinarith [hrr.le, hM.le]
  have h1 : (1 / (128 * (4 + 2 * (r : ℝ) * M))) / Gproxy ≤ Gtrue / Gproxy :=
    div_le_div_of_nonneg_right htrue (le_of_lt hpos)
  have h2 : (1 / (128 * (4 + 2 * (r : ℝ) * M))) / (1 / 512)
      ≤ (1 / (128 * (4 + 2 * (r : ℝ) * M))) / Gproxy :=
    div_le_div_of_nonneg_left (by positivity) hpos hproxy
  have h3 : (1 / (128 * (4 + 2 * (r : ℝ) * M))) / (1 / 512 : ℝ)
      = 2 / (2 + (r : ℝ) * M) := by
    field_simp
    ring
  linarith [h1, h2, h3.le, h3.ge]

/-- **`Theta((rM)^{-1})`, both sides.**  The proxy value is pinned at `1/512`, the true
value is squeezed between `1/(128(4+2rM))` and `1/(8Mr)`, so the ratio is bounded above and
below by constants times `1/(rM)`.  At `M = 1` the separation is `Theta(r^{-1})`: it exists
at UNIFORM variance, and what drives it is how many alternatives the frozen proxy declines
to look at. -/
theorem rpair_theta (M Gtrue Gproxy : ℝ) (r : ℕ) (hr : 0 < r) (hM : 0 < M)
    (hlo : 1 / (128 * (4 + 2 * (r : ℝ) * M)) ≤ Gtrue)
    (hhi : Gtrue ≤ 1 / (8 * M * (r : ℝ)))
    (hplo : 1 / 512 ≤ Gproxy) (hphi : Gproxy ≤ 1 / 512) (hpos : 0 < Gproxy) :
    2 / (2 + (r : ℝ) * M) ≤ Gtrue / Gproxy ∧ Gtrue / Gproxy ≤ 64 / ((r : ℝ) * M) :=
  ⟨rpair_ratio_ge M Gtrue Gproxy r hr hM hlo hphi hpos,
    rpair_ratio_le M Gtrue Gproxy r hr hM hhi hplo hpos⟩

/-! ## Allocation inefficiency: the surrogate does not merely misprice, it misdesigns

A ratio of optimal VALUES can diverge while the two objectives still select the same
design; an objective scaled by a wrong constant picks the right optimiser.  So the
separation above does not yet say the surrogate is harmful to use.  This section says it.

Two properties characterise the frozen surrogate without naming its formula: its value
depends only on the four anchor weights (`AnchorOnly`), and it strictly prefers anchor
mass (`AnchorMonotone`).  From those alone, EVERY maximiser starves the middle pairs ---
not one solver output that happened to return zeros, but every point of the argmax, since
sweeping any pair weight onto an anchor stays an allocation and strictly improves the
surrogate.  And a design that starves the pairs has EXACTLY ZERO information against a
pair alternative, because the alternative moves only cells the design never measures.

The conclusion is about the design, not the number: the allocation the surrogate selects
does not accumulate the information needed to refute a wrong decision. -/

section AllocationInefficiency

/-- **The surrogate sees only the anchors.** -/
def AnchorOnly (Jp : (Cell r → ℝ) → ℝ) : Prop :=
  ∀ w w' : Cell r → ℝ, (∀ i : Fin 4, w (Sum.inl i) = w' (Sum.inl i)) → Jp w = Jp w'

/-- **And it strictly prefers anchor mass.** -/
def AnchorMonotone (Jp : (Cell r → ℝ) → ℝ) : Prop :=
  ∀ w w' : Cell r → ℝ,
    (∀ i : Fin 4, w (Sum.inl i) ≤ w' (Sum.inl i)) →
    (∃ i : Fin 4, w (Sum.inl i) < w' (Sum.inl i)) → Jp w < Jp w'

/-- The design that sweeps every middle pair's weight onto the first anchor. -/
noncomputable def sweepToAnchor (w : Cell r → ℝ) : Cell r → ℝ :=
  Sum.elim
    (Fin.cons (w (Sum.inl 0) + ∑ p : Fin r × Bool, w (Sum.inr p))
      (fun i : Fin 3 => w (Sum.inl i.succ)) : Fin 4 → ℝ)
    (fun _ => 0)

theorem sweepToAnchor_isAlloc (w : Cell r → ℝ) (hw : IsAlloc w) :
    IsAlloc (sweepToAnchor w) := by
  classical
  obtain ⟨hnn, hsum⟩ := hw
  have hpair : (0 : ℝ) ≤ ∑ p : Fin r × Bool, w (Sum.inr p) :=
    Finset.sum_nonneg (fun p _ => hnn _)
  refine ⟨?_, ?_⟩
  · intro e
    cases e with
    | inl i =>
        simp only [sweepToAnchor, Sum.elim_inl]
        refine Fin.cases ?_ ?_ i
        · rw [Fin.cons_zero]; exact add_nonneg (hnn _) hpair
        · intro j; rw [Fin.cons_succ]; exact hnn _
    | inr p => simp [sweepToAnchor]
  · rw [Fintype.sum_sum_type] at hsum ⊢
    simp only [sweepToAnchor, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
    rw [Fin.sum_univ_succ, Fin.cons_zero] at *
    simp only [Fin.cons_succ] at *
    linarith [hsum]

theorem sweepToAnchor_anchor_ge (w : Cell r → ℝ) (hw : IsAlloc w) (i : Fin 4) :
    w (Sum.inl i) ≤ sweepToAnchor w (Sum.inl i) := by
  classical
  have hpair : (0 : ℝ) ≤ ∑ p : Fin r × Bool, w (Sum.inr p) :=
    Finset.sum_nonneg (fun p _ => hw.1 _)
  simp only [sweepToAnchor, Sum.elim_inl]
  refine Fin.cases ?_ ?_ i
  · rw [Fin.cons_zero]; linarith
  · intro j; rw [Fin.cons_succ]

theorem sweepToAnchor_anchor_lt (w : Cell r → ℝ) (hw : IsAlloc w)
    (hpos : 0 < ∑ p : Fin r × Bool, w (Sum.inr p)) :
    w (Sum.inl 0) < sweepToAnchor w (Sum.inl 0) := by
  simp only [sweepToAnchor, Sum.elim_inl, Fin.cons_zero]
  linarith

/-- **Step one: every surrogate optimum starves the middle pairs.**

Not one solver output with zero weights: EVERY maximiser.  If a design gave a pair any
weight, sweeping that weight onto an anchor keeps it an allocation and strictly raises the
surrogate's value, so the original was not a maximiser. -/
theorem proxy_optimum_starves_pairs (Jp : (Cell r → ℝ) → ℝ) (hAM : AnchorMonotone Jp)
    (w : Cell r → ℝ) (hw : IsAlloc w) (hmax : ∀ w', IsAlloc w' → Jp w' ≤ Jp w) :
    ∀ p : Fin r × Bool, w (Sum.inr p) = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨p0, hp0⟩ := hcon
  have hpos : 0 < ∑ p : Fin r × Bool, w (Sum.inr p) := by
    refine Finset.sum_pos' (fun p _ => hw.1 _) ⟨p0, Finset.mem_univ _, ?_⟩
    exact lt_of_le_of_ne (hw.1 _) (Ne.symm hp0)
  have hlt : Jp w < Jp (sweepToAnchor w) :=
    hAM w (sweepToAnchor w) (sweepToAnchor_anchor_ge w hw)
      ⟨0, sweepToAnchor_anchor_lt w hw hpos⟩
  exact absurd (hmax (sweepToAnchor w) (sweepToAnchor_isAlloc w hw)) (not_le.2 hlt)

/-- **Step two: a design that starves the pairs learns nothing about a pair alternative.**

The alternative moves only the two cells of one pair, and the design measures neither, so
the information is exactly zero -- not small, zero. -/
theorem starved_energy_zero (w var θ : Cell r → ℝ) (j : Fin r) (d : ℝ)
    (hz : ∀ p : Fin r × Bool, w (Sum.inr p) = 0) :
    energy w var θ (pairShift θ j d) = 0 := by
  classical
  unfold energy
  rw [Fintype.sum_sum_type]
  have h1 : ∀ i : Fin 4,
      w (Sum.inl i) * (pairShift θ j d (Sum.inl i) - θ (Sum.inl i)) ^ 2
        / var (Sum.inl i) = 0 := by
    intro i
    rw [pairShift_rest θ j d (Sum.inl i) (by simp) (by simp)]
    simp
  have h2 : ∀ p : Fin r × Bool,
      w (Sum.inr p) * (pairShift θ j d (Sum.inr p) - θ (Sum.inr p)) ^ 2
        / var (Sum.inr p) = 0 := by
    intro p
    rw [hz p]
    simp
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun p _ => h2 p)]
  simp

/-- **Allocation inefficiency.**  Every surrogate optimum has exactly zero true
information against every pair alternative, so its efficiency in the true game is zero
while the true game's value is strictly positive.  Mispricing the objective is not the
whole story: the design the surrogate selects does not accumulate the information needed
to refute a wrong decision. -/
theorem proxy_efficiency_zero (Jp : (Cell r → ℝ) → ℝ) (hAM : AnchorMonotone Jp)
    (w : Cell r → ℝ) (hw : IsAlloc w) (hmax : ∀ w', IsAlloc w' → Jp w' ≤ Jp w)
    (var θ : Cell r → ℝ) :
    ∀ (j : Fin r) (d : ℝ), energy w var θ (pairShift θ j d) = 0 :=
  fun j d => starved_energy_zero w var θ j d
    (proxy_optimum_starves_pairs Jp hAM w hw hmax)

/-- The same conclusion at the level of the true game's value: zero against a strictly
positive benchmark. -/
theorem proxy_true_value_zero (Jp : (Cell r → ℝ) → ℝ) (hAM : AnchorMonotone Jp)
    (w : Cell r → ℝ) (hw : IsAlloc w) (hmax : ∀ w', IsAlloc w' → Jp w' ≤ Jp w)
    (var θ : Cell r → ℝ) (Jt : (Cell r → ℝ) → ℝ) (Γt : ℝ) (j : Fin r) (d : ℝ)
    (hJt : Jt w ≤ energy w var θ (pairShift θ j d)) (hJtnn : 0 ≤ Jt w) (hΓ : 0 < Γt) :
    Jt w = 0 ∧ Jt w < Γt := by
  have hz := proxy_efficiency_zero Jp hAM w hw hmax var θ j d
  have : Jt w = 0 := le_antisymm (by rw [← hz]; exact hJt) hJtnn
  exact ⟨this, by rw [this]; exact hΓ⟩

end AllocationInefficiency

section ExtremaStability

/-! # Step one of the count bound: the extrema do not move near the true world

The accumulation argument needs a neighbourhood of the true world on which every
surrogate optimum has the SAME support, so that "the pairs are starved" is not an accident
of one parameter value.  The frozen surrogate reads the extrema, so what has to be stable
is which cells attain them.  A strict margin makes that automatic. -/

/-- `e` attains the maximum of `x` over the cells, with a strict margin `γ` over every
other cell. -/
def StrictArgmax (x : Cell r → ℝ) (e : Cell r) (γ : ℝ) : Prop :=
  ∀ e', e' ≠ e → x e' + γ ≤ x e

/-- **A strict margin survives a perturbation smaller than half of it.**

If `e` is the strict maximiser of `θ` by margin `γ`, then it is still the maximiser of any
`θ'` within `γ/2` in sup-norm.  So on that ball the surrogate reads the same cell as its
extremum, and `AnchorOnly` / `AnchorMonotone` continue to describe it. -/
theorem strictArgmax_stable (θ θ' : Cell r → ℝ) (e : Cell r) (γ : ℝ) (hγ : 0 < γ)
    (hmax : StrictArgmax θ e γ) (hclose : ∀ c, |θ' c - θ c| < γ / 2) :
    ∀ e', e' ≠ e → θ' e' < θ' e := by
  intro e' hne
  have h1 := hmax e' hne
  have h2 := abs_lt.mp (hclose e')
  have h3 := abs_lt.mp (hclose e)
  linarith [h1, h2.2, h3.1]

/-- The same for a strict minimiser. -/
def StrictArgmin (x : Cell r → ℝ) (e : Cell r) (γ : ℝ) : Prop :=
  ∀ e', e' ≠ e → x e + γ ≤ x e'

theorem strictArgmin_stable (θ θ' : Cell r → ℝ) (e : Cell r) (γ : ℝ) (hγ : 0 < γ)
    (hmin : StrictArgmin θ e γ) (hclose : ∀ c, |θ' c - θ c| < γ / 2) :
    ∀ e', e' ≠ e → θ' e < θ' e' := by
  intro e' hne
  have h1 := hmin e' hne
  have h2 := abs_lt.mp (hclose e')
  have h3 := abs_lt.mp (hclose e)
  linarith [h1, h2.1, h3.2]

/-- **Step one, assembled.**  On the ball of radius `γ/2` around a world whose anchor cells
are strict extrema by margin `γ`, the surrogate's extremum cells are constant.  Combined
with `proxy_optimum_starves_pairs`, every surrogate optimum on that whole ball starves the
middle pairs -- so the starvation is a property of a NEIGHBOURHOOD, not of one parameter
value, which is what an accumulation argument over a run needs. -/
theorem starvation_on_a_neighbourhood
    (θ : Cell r → ℝ) (eMax eMin : Cell r) (γ : ℝ) (hγ : 0 < γ)
    (hmax : StrictArgmax θ eMax γ) (hmin : StrictArgmin θ eMin γ)
    (Jp : (Cell r → ℝ) → ℝ) (hAM : AnchorMonotone Jp)
    (θ' : Cell r → ℝ) (hclose : ∀ c, |θ' c - θ c| < γ / 2)
    (w : Cell r → ℝ) (hw : IsAlloc w) (hmaxw : ∀ w', IsAlloc w' → Jp w' ≤ Jp w) :
    (∀ e', e' ≠ eMax → θ' e' < θ' eMax) ∧
    (∀ e', e' ≠ eMin → θ' eMin < θ' e') ∧
    (∀ p : Fin r × Bool, w (Sum.inr p) = 0) :=
  ⟨strictArgmax_stable θ θ' eMax γ hγ hmax hclose,
   strictArgmin_stable θ θ' eMin γ hγ hmin hclose,
   proxy_optimum_starves_pairs Jp hAM w hw hmaxw⟩

/-- **The margin hypotheses are satisfiable.**  An explicit world with a strict maximum
and a strict minimum, at margin one, so the stability statement is not vacuous. -/
theorem starvation_neighbourhood_nonvacuous (r : ℕ) :
    ∃ (θ : Cell r → ℝ) (eMax eMin : Cell r) (γ : ℝ),
      0 < γ ∧ StrictArgmax θ eMax γ ∧ StrictArgmin θ eMin γ := by
  classical
  have hne10 : (Sum.inl 1 : Cell r) ≠ Sum.inl 0 := by simp
  refine ⟨fun e => if e = Sum.inl 0 then (1 : ℝ) else if e = Sum.inl 1 then -1 else 0,
    Sum.inl 0, Sum.inl 1, 1, by norm_num, ?_, ?_⟩
  · intro e' hne
    simp only [if_pos rfl, if_neg hne]
    by_cases h1 : e' = Sum.inl 1
    · rw [if_pos h1]; norm_num
    · rw [if_neg h1]; norm_num
  · intro e' hne
    simp only [if_neg hne10, if_pos rfl]
    by_cases h0 : e' = Sum.inl 0
    · rw [if_pos h0]; norm_num
    · rw [if_neg h0]
      by_cases h1 : e' = Sum.inl 1
      · exact absurd h1 hne
      · rw [if_neg h1]; norm_num

end ExtremaStability

/-! ## Audit -/

#print axioms exists_light_pair
#print axioms sum_pairWeight_le_one
#print axioms pair_shift_energy
#print axioms pairShift_true
#print axioms pairShift_false
#print axioms light_pair_energy_le
#print axioms rpair_ratio_le
#print axioms contrast_moves
#print axioms four_sq_lower
#print axioms anchorDesign_isAlloc
#print axioms rpair_true_ge
#print axioms rpair_ratio_ge
#print axioms rpair_theta
#print axioms no_constant_factor_at_unit_variance

#print axioms sweepToAnchor_isAlloc
#print axioms proxy_optimum_starves_pairs
#print axioms starved_energy_zero
#print axioms proxy_efficiency_zero
#print axioms proxy_true_value_zero

#print axioms strictArgmax_stable
#print axioms strictArgmin_stable
#print axioms starvation_on_a_neighbourhood
#print axioms starvation_neighbourhood_nonvacuous

end CIGAMF.P13.PaperARPair
