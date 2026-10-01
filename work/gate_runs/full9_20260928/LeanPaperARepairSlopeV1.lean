import «LeanPaperAFrontierV1»

/-!
# Paper A: the exact slope of the repair frontier at zero sacrifice

`frontier_two_sided` (`LeanPaperAFrontierV1`) pins the repair frontier between
`9β/(128(4+2rM))` and `β/(8rM)`. The two bounds have the same order but not the same constant.
This module closes the constant at small sacrifice.

**The design.** `vB β = (1-β)·(uniform on the four frozen cells) + β·(uniform on the middles)`.
It keeps a `(1-β)` share of the surrogate value, so its sacrifice is at most `β`.

**The bound.** Every true alternative reverses `range(λ_A) ≤ range(λ_B)`. With `p, q` the cells
realising `λ_B`'s range, the deviations obey
`δ_{a0} - δ_{a1} + δ_p - δ_q ≥ 1 - (θ_p - θ_q)`,
and the weighted Cauchy–Schwarz (`weighted_four`) gives energy at least `g²/Σ 1/c_e`, where
`c_e = w_e/(2ν_e)` is `(1-β)/8` on a frozen cell and `β/(4rM)` on a middle. By the types of
`p, q`:
* two middles: `g = 1`, `Σ 1/c = 16/(1-β) + 8rM/β`;
* a middle and an anchor: `g ≥ 7/8`;
* two anchors: `g ≥ 3/4`, with no middle term;
* `p = q`: `g ≥ 1` on the arm-`A` cells alone.
Each case is at least `β/(8rM + 128β)` for `0 < β ≤ 1/2` (`trueValue_vB_ge`).

**The slope** (`frontier_slope`): for `0 < β ≤ 1/2`, some design with sacrifice at most `β` has
true information at least `β/(8rM + 128β)`, and no such design has more than `β/(8rM)`. So the
frontier is `β/(8rM) - O(β²)`: its slope at zero is exactly `1/(8rM)`, the constant of the
sacrifice law.
-/

namespace CIGAMF.P13.PaperARepairSlope

open Finset
open CIGAMF.P13.PaperARPair CIGAMF.P13.PaperACentred CIGAMF.P13.PaperAFrontier

variable {r : ℕ}

/-! ## 1. The design -/

/-- Uniform on the middle cells. -/
noncomputable def uMid (r : ℕ) : Cell r → ℝ :=
  Sum.elim (fun _ => 0) (fun _ => 1 / (2 * (r : ℝ)))

theorem uMid_isAlloc (r : ℕ) [NeZero r] : IsAlloc (uMid r) := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  refine ⟨fun e => ?_, ?_⟩
  · cases e with
    | inl a => simp [uMid]
    | inr p => simp only [uMid, Sum.elim_inr]; positivity
  · have hs : ∑ e : Cell r, uMid r e
        = (∑ _i : Fin 4, (0 : ℝ)) + ∑ _p : Fin r × Bool, 1 / (2 * (r : ℝ)) :=
      Fintype.sum_sum_type _
    rw [hs, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    field_simp

/-- **The small-sacrifice design.** -/
noncomputable def vB (r : ℕ) (β : ℝ) : Cell r → ℝ := mixW β (wUnifC r) (uMid r)

theorem vB_inl (β : ℝ) (a : Fin 4) : vB r β (Sum.inl a) = (1 - β) / 4 := by
  simp [vB, mixW, wUnifC, uMid]; ring

theorem vB_inr (β : ℝ) (p : Fin r × Bool) : vB r β (Sum.inr p) = β / (2 * (r : ℝ)) := by
  simp [vB, mixW, wUnifC, uMid]; ring

theorem vB_isAlloc [NeZero r] (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : IsAlloc (vB r β) :=
  mixW_isAlloc β hβ0 hβ1 _ _ (wUnifC_isAlloc r) (uMid_isAlloc r)

/-- **It keeps a `(1-β)` share of the surrogate value.** -/
theorem vB_frozen [NeZero r] (M : ℝ) (hM : 0 < M) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (1 - β) * (9 / 512) ≤ frozenValueC₀ M (vB r β) := by
  have hufr : (9 : ℝ) / 512 ≤ frozenValueC₀ M (wUnifC r) :=
    le_trans (frozenValueC_unif_ge M hM)
      (frozenValueC_le_restricted M hM (wUnifC r) (wUnifC_isAlloc r).1)
  have hconc := value_concave (FrozenAltC₀ r) M hM (wUnifC r) (uMid r)
    (wUnifC_isAlloc r).1 (uMid_isAlloc r).1 β hβ0 hβ1
  have hnn : 0 ≤ frozenValueC₀ M (uMid r) :=
    le_ciInf (fun lam => energyC_nonneg M hM _ _ (uMid_isAlloc r).1)
  have h1t : (0 : ℝ) ≤ 1 - β := by linarith
  calc (1 - β) * (9 / 512)
      ≤ (1 - β) * frozenValueC₀ M (wUnifC r) + β * frozenValueC₀ M (uMid r) := by
        nlinarith [hufr, hnn, h1t, hβ0]
    _ ≤ frozenValueC₀ M (vB r β) := hconc

/-! ## 2. Weighted Cauchy–Schwarz -/

theorem sq_tangent (c x t : ℝ) (hc : 0 < c) : 2 * t * x - t ^ 2 / c ≤ c * x ^ 2 := by
  have key : (c * x - t) ^ 2 / c = c * x ^ 2 - 2 * t * x + t ^ 2 / c := by
    rw [div_eq_iff hc.ne', add_mul, div_mul_cancel₀ _ hc.ne']; ring
  have h : 0 ≤ (c * x - t) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
  linarith

theorem weighted_four (c₁ c₂ c₃ c₄ x₁ x₂ x₃ x₄ g : ℝ) (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    (h₃ : 0 < c₃) (h₄ : 0 < c₄) (hg : 0 ≤ g) (h : g ≤ x₁ - x₂ + x₃ - x₄) :
    g ^ 2 / (1 / c₁ + 1 / c₂ + 1 / c₃ + 1 / c₄)
      ≤ c₁ * x₁ ^ 2 + c₂ * x₂ ^ 2 + c₃ * x₃ ^ 2 + c₄ * x₄ ^ 2 := by
  set S := 1 / c₁ + 1 / c₂ + 1 / c₃ + 1 / c₄ with hS
  have hSpos : 0 < S := by positivity
  set t := g / S with ht
  have ht0 : 0 ≤ t := div_nonneg hg hSpos.le
  have e1 := sq_tangent c₁ x₁ t h₁
  have e2 := sq_tangent c₂ (-x₂) t h₂
  have e3 := sq_tangent c₃ x₃ t h₃
  have e4 := sq_tangent c₄ (-x₄) t h₄
  rw [neg_sq] at e2 e4
  have hsum : t ^ 2 / c₁ + t ^ 2 / c₂ + t ^ 2 / c₃ + t ^ 2 / c₄ = t ^ 2 * S := by
    rw [hS]; ring
  have hlin : 2 * t * g ≤ 2 * t * (x₁ - x₂ + x₃ - x₄) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  have key : 2 * t * g - t ^ 2 * S ≤ c₁ * x₁ ^ 2 + c₂ * x₂ ^ 2 + c₃ * x₃ ^ 2 + c₄ * x₄ ^ 2 := by
    nlinarith [e1, e2, e3, e4, hsum, hlin]
  have hval : 2 * t * g - t ^ 2 * S = g ^ 2 / S := by
    rw [ht]; field_simp; ring
  linarith

theorem weighted_two (c₁ c₂ x₁ x₂ g : ℝ) (h₁ : 0 < c₁) (h₂ : 0 < c₂) (hg : 0 ≤ g)
    (h : g ≤ x₁ - x₂) : g ^ 2 / (1 / c₁ + 1 / c₂) ≤ c₁ * x₁ ^ 2 + c₂ * x₂ ^ 2 := by
  set S := 1 / c₁ + 1 / c₂ with hS
  have hSpos : 0 < S := by positivity
  set t := g / S with ht
  have ht0 : 0 ≤ t := div_nonneg hg hSpos.le
  have e1 := sq_tangent c₁ x₁ t h₁
  have e2 := sq_tangent c₂ (-x₂) t h₂
  rw [neg_sq] at e2
  have hsum : t ^ 2 / c₁ + t ^ 2 / c₂ = t ^ 2 * S := by rw [hS]; ring
  have hlin : 2 * t * g ≤ 2 * t * (x₁ - x₂) := mul_le_mul_of_nonneg_left h (by linarith)
  have key : 2 * t * g - t ^ 2 * S ≤ c₁ * x₁ ^ 2 + c₂ * x₂ ^ 2 := by
    nlinarith [e1, e2, hsum, hlin]
  have hval : 2 * t * g - t ^ 2 * S = g ^ 2 / S := by
    rw [ht]; field_simp; ring
  linarith

/-! ## 3. The numerical cases -/

section Num

variable (X β : ℝ) (hX : 0 < X) (hβ0 : 0 < β) (hβ : β ≤ 1 / 2)
include hX hβ0 hβ

theorem num_A : β / (8 * X + 128 * β) ≤ 1 ^ 2 / (1 / ((1 - β) / 8) + 1 / ((1 - β) / 8)) := by
  have h1 : 0 < 1 - β := by linarith
  have e : (1 : ℝ) ^ 2 / (1 / ((1 - β) / 8) + 1 / ((1 - β) / 8)) = (1 - β) / 16 := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_pos hX hβ0]

theorem num_MM : β / (8 * X + 128 * β)
    ≤ 1 ^ 2 / (1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / (β / (4 * X)) + 1 / (β / (4 * X))) := by
  have h1 : 0 < 1 - β := by linarith
  have e : (1 : ℝ) ^ 2 / (1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / (β / (4 * X))
      + 1 / (β / (4 * X))) = β * (1 - β) / (16 * β + 8 * X * (1 - β)) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg β) (by linarith : (0 : ℝ) ≤ 112 - 128 * β)]

theorem num_AM : β / (8 * X + 128 * β)
    ≤ (7 / 8) ^ 2 / (1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / ((1 - β) / 8)
      + 1 / (β / (4 * X))) := by
  have h1 : 0 < 1 - β := by linarith
  have e : (7 / 8 : ℝ) ^ 2 / (1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / ((1 - β) / 8)
      + 1 / (β / (4 * X))) = 49 * β * (1 - β) / (64 * (24 * β + 4 * X * (1 - β))) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hX hβ0, mul_nonneg (mul_nonneg hX.le hβ0.le) h1.le,
    mul_nonneg (sq_nonneg β) (by linarith : (0 : ℝ) ≤ 1 - 2 * β),
    mul_nonneg (mul_nonneg hX.le (sq_nonneg β)) h1.le]

theorem num_MA : β / (8 * X + 128 * β)
    ≤ (7 / 8) ^ 2 / (1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / (β / (4 * X))
      + 1 / ((1 - β) / 8)) := by
  have e : 1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / (β / (4 * X)) + 1 / ((1 - β) / 8)
      = 1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / (β / (4 * X)) := by ring
  rw [e]; exact num_AM X β hX hβ0 hβ

theorem num_AA : β / (8 * X + 128 * β)
    ≤ (3 / 4) ^ 2 / (1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / ((1 - β) / 8)
      + 1 / ((1 - β) / 8)) := by
  have h1 : 0 < 1 - β := by linarith
  have e : (3 / 4 : ℝ) ^ 2 / (1 / ((1 - β) / 8) + 1 / ((1 - β) / 8) + 1 / ((1 - β) / 8)
      + 1 / ((1 - β) / 8)) = 9 * (1 - β) / 512 := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_pos hX hβ0]

end Num

/-! ## 4. The true value of the design -/

theorem bcell_cases (e : Cell r) (he : e ∈ BCells r) :
    (e = Sum.inl 2 ∨ e = Sum.inl 3) ∨ ∃ p, e = Sum.inr p := by
  classical
  rw [BCells, Finset.mem_filter] at he
  obtain ⟨-, hb⟩ := he
  match e with
  | Sum.inl a =>
      left
      have hor : a = 2 ∨ a = 3 := by
        simpa [isBCell, Bool.or_eq_true, decide_eq_true_iff] using hb
      rcases hor with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  | Sum.inr p => exact Or.inr ⟨p, rfl⟩

/-- **The true information of the small-sacrifice design.** -/
theorem trueValue_vB_ge [NeZero r] (M : ℝ) (hM : 0 < M) (β : ℝ) (hβ0 : 0 < β)
    (hβ : β ≤ 1 / 2) :
    β / (8 * (r : ℝ) * M + 128 * β) ≤ trueValueC₀ M (vB r β) := by
  classical
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  set X : ℝ := (r : ℝ) * M with hXdef
  have hX : 0 < X := mul_pos hr hM
  have hTX : β / (8 * (r : ℝ) * M + 128 * β) = β / (8 * X + 128 * β) := by rw [hXdef]; ring_nf
  rw [hTX]
  have h1 : 0 < 1 - β := by linarith
  refine le_ciInf (fun lam => ?_)
  set L := (lam : Cell r → ℝ) with hL
  have hrev : rangeA L ≤ rangeB L := lam.2.1
  obtain ⟨p, hp, hpv⟩ := Finset.exists_mem_eq_sup' (BCells_nonempty r) L
  obtain ⟨q, hq, hqv⟩ := Finset.exists_mem_eq_inf' (BCells_nonempty r) L
  have hrB : rangeB L = L p - L q := by unfold rangeB; rw [hpv, hqv]
  have hA : L (Sum.inl 1) - L (Sum.inl 0) ≤ rangeA L := rangeA_ge L
  set δ : Cell r → ℝ := fun e => L e - thetaC r e with hδ
  have hcon : 1 - (thetaC r p - thetaC r q) ≤ δ (Sum.inl 0) - δ (Sum.inl 1) + δ p - δ q := by
    simp only [hδ]; rw [thetaC_0, thetaC_1]; linarith
  -- the per-cell coefficients
  set c : Cell r → ℝ := fun e => vB r β e / (2 * pairVar M e) with hc
  have cA : ∀ a : Fin 4, c (Sum.inl a) = (1 - β) / 8 := by
    intro a; simp only [hc, vB_inl]; simp [pairVar]; ring
  have cM : ∀ pr : Fin r × Bool, c (Sum.inr pr) = β / (4 * X) := by
    intro pr; simp only [hc, vB_inr]; simp [pairVar, hXdef]; field_simp; ring
  have hcpos : ∀ e, 0 ≤ c e := by
    intro e; cases e with
    | inl a => rw [cA]; positivity
    | inr pr => rw [cM]; positivity
  have henergy : energy (vB r β) (pairVar M) (thetaC r) L = ∑ e, c e * δ e ^ 2 := by
    unfold energy
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := pairVarC_pos M hM e
    simp only [hc, hδ]
    field_simp
  have hsub : ∀ S : Finset (Cell r), ∑ e ∈ S, c e * δ e ^ 2
      ≤ energy (vB r β) (pairVar M) (thetaC r) L := by
    intro S
    rw [henergy]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _ _ => mul_nonneg (hcpos e) (sq_nonneg _))
  have hne01 : (Sum.inl 0 : Cell r) ≠ Sum.inl 1 := by
    intro h; exact absurd (Sum.inl.inj h) (by decide)
  by_cases hpq : p = q
  · -- arm A alone
    subst hpq
    have h2 : 1 ≤ δ (Sum.inl 0) - δ (Sum.inl 1) := by linarith
    have hw := weighted_two (c (Sum.inl 0)) (c (Sum.inl 1)) (δ (Sum.inl 0)) (δ (Sum.inl 1)) 1
      (by rw [cA]; positivity) (by rw [cA]; positivity) zero_le_one h2
    have hS := hsub {Sum.inl 0, Sum.inl 1}
    rw [Finset.sum_pair hne01] at hS
    rw [cA, cA] at hw
    exact (num_A X β hX hβ0 hβ).trans (hw.trans (by rw [cA, cA] at hS; exact hS))
  · have hbp := bcell_ne_anchorA r p hp
    have hbq := bcell_ne_anchorA r q hq
    have hS := hsub {Sum.inl 0, Sum.inl 1, p, q}
    have hcard : ∑ e ∈ ({Sum.inl 0, Sum.inl 1, p, q} : Finset (Cell r)), c e * δ e ^ 2
        = c (Sum.inl 0) * δ (Sum.inl 0) ^ 2 + c (Sum.inl 1) * δ (Sum.inl 1) ^ 2
          + c p * δ p ^ 2 + c q * δ q ^ 2 := by
      rw [Finset.sum_insert (by simp [hne01, Ne.symm hbp.1, Ne.symm hbq.1]),
        Finset.sum_insert (by simp [Ne.symm hbp.2, Ne.symm hbq.2]), Finset.sum_pair hpq]
      ring
    rw [hcard, cA, cA] at hS
    have hθp := thetaC_bcell_bound r p hp
    have hθq := thetaC_bcell_bound r q hq
    rcases bcell_cases p hp with hpA | ⟨pp, rfl⟩ <;> rcases bcell_cases q hq with hqA | ⟨qq, rfl⟩
    · -- two anchors
      have hcp : c p = (1 - β) / 8 := by rcases hpA with rfl | rfl <;> exact cA _
      have hcq : c q = (1 - β) / 8 := by rcases hqA with rfl | rfl <;> exact cA _
      have hg : (3 / 4 : ℝ) ≤ δ (Sum.inl 0) - δ (Sum.inl 1) + δ p - δ q := by linarith
      have hw := weighted_four ((1 - β) / 8) ((1 - β) / 8) ((1 - β) / 8) ((1 - β) / 8)
        (δ (Sum.inl 0)) (δ (Sum.inl 1)) (δ p) (δ q) (3 / 4) (by positivity) (by positivity)
        (by positivity) (by positivity) (by norm_num) hg
      rw [hcp, hcq] at hS
      exact (num_AA X β hX hβ0 hβ).trans (hw.trans hS)
    · -- p anchor, q middle
      have hcp : c p = (1 - β) / 8 := by rcases hpA with rfl | rfl <;> exact cA _
      have hθq0 : thetaC r (Sum.inr qq) = 0 := thetaC_pair r qq
      have hg : (7 / 8 : ℝ) ≤ δ (Sum.inl 0) - δ (Sum.inl 1) + δ p - δ (Sum.inr qq) := by
        rw [hθq0] at hcon; linarith [hθp.2]
      have hw := weighted_four ((1 - β) / 8) ((1 - β) / 8) ((1 - β) / 8) (β / (4 * X))
        (δ (Sum.inl 0)) (δ (Sum.inl 1)) (δ p) (δ (Sum.inr qq)) (7 / 8) (by positivity)
        (by positivity) (by positivity) (by positivity) (by norm_num) hg
      rw [hcp, cM] at hS
      exact (num_AM X β hX hβ0 hβ).trans (hw.trans hS)
    · -- p middle, q anchor
      have hcq : c q = (1 - β) / 8 := by rcases hqA with rfl | rfl <;> exact cA _
      have hθp0 : thetaC r (Sum.inr pp) = 0 := thetaC_pair r pp
      have hg : (7 / 8 : ℝ) ≤ δ (Sum.inl 0) - δ (Sum.inl 1) + δ (Sum.inr pp) - δ q := by
        rw [hθp0] at hcon; linarith [hθq.1]
      have hw := weighted_four ((1 - β) / 8) ((1 - β) / 8) (β / (4 * X)) ((1 - β) / 8)
        (δ (Sum.inl 0)) (δ (Sum.inl 1)) (δ (Sum.inr pp)) (δ q) (7 / 8) (by positivity)
        (by positivity) (by positivity) (by positivity) (by norm_num) hg
      rw [cM, hcq] at hS
      exact (num_MA X β hX hβ0 hβ).trans (hw.trans hS)
    · -- two middles
      have hθp0 : thetaC r (Sum.inr pp) = 0 := thetaC_pair r pp
      have hθq0 : thetaC r (Sum.inr qq) = 0 := thetaC_pair r qq
      have hg : (1 : ℝ) ≤ δ (Sum.inl 0) - δ (Sum.inl 1) + δ (Sum.inr pp) - δ (Sum.inr qq) := by
        rw [hθp0, hθq0] at hcon; linarith
      have hw := weighted_four ((1 - β) / 8) ((1 - β) / 8) (β / (4 * X)) (β / (4 * X))
        (δ (Sum.inl 0)) (δ (Sum.inl 1)) (δ (Sum.inr pp)) (δ (Sum.inr qq)) 1 (by positivity)
        (by positivity) (by positivity) (by positivity) zero_le_one hg
      rw [cM, cM] at hS
      exact (num_MM X β hX hβ0 hβ).trans (hw.trans hS)

/-! ## 5. The slope -/

/-- **The repair frontier has slope exactly `1/(8rM)` at zero.**  For `0 < β ≤ 1/2`, a design
keeping a `(1-β)` share of the surrogate value has true information at least `β/(8rM + 128β)`,
and no such design has more than `β/(8rM)`. -/
theorem frontier_slope (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r) [NeZero r] (β : ℝ)
    (hβ0 : 0 < β) (hβ : β ≤ 1 / 2) :
    (∃ w : Cell r → ℝ, IsAlloc w ∧ (1 - β) * (9 / 512) ≤ frozenValueC₀ M w
        ∧ β / (8 * (r : ℝ) * M + 128 * β) ≤ trueValueC₀ M w)
      ∧ (∀ w : Cell r → ℝ, IsAlloc w → (1 - β) * (9 / 512) ≤ frozenValueC₀ M w →
          trueValueC₀ M w ≤ β / (8 * M * (r : ℝ))) :=
  ⟨⟨vB r β, vB_isAlloc β hβ0.le (by linarith), vB_frozen M hM β hβ0.le (by linarith),
      trueValue_vB_ge M hM β hβ0 hβ⟩,
    fun w hw hfeas => frontier_upper M hM r hr w hw β hβ0.le hfeas⟩

/-- **The gap between the two sides is second order.** -/
theorem slope_gap (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r) (β : ℝ) (hβ0 : 0 < β) :
    β / (8 * M * (r : ℝ)) - β / (8 * (r : ℝ) * M + 128 * β)
      ≤ 2 * β ^ 2 / ((r : ℝ) * M) ^ 2 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hX : 0 < (r : ℝ) * M := mul_pos hrR hM
  have e : β / (8 * M * (r : ℝ)) - β / (8 * (r : ℝ) * M + 128 * β)
      = 16 * β ^ 2 / ((r : ℝ) * M * (8 * ((r : ℝ) * M) + 128 * β)) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hX hβ0, sq_nonneg β, mul_pos (mul_pos hX hX) (sq_pos_of_pos hβ0)]

#print axioms trueValue_vB_ge
#print axioms frontier_slope
#print axioms slope_gap

end CIGAMF.P13.PaperARepairSlope
