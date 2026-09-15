import «LeanSupportSamplingLawV1»

/-! # Support: the end-point of package A -- decide vs recover, and the growing-`K` law.

`LeanSupportSamplingLawV1` supplies the probability facts (`E ∏ L_i = B(1-s)^N`, and
`Pr(every class still hides a tip) ≥ (1-s)^N`).  `LeanSupportDecideExponentV1` supplies
the pointwise `min_i L_i/(a_i+L_i) ≤ ∏_i L_i`.  What is still missing, per the audit,
is the assembly into an expectation bracket, the RECOVERY exponent, and the growing-`K`
form.  All three are here.

## THE TWO LAWS

Decide (fixed `K`):   `k₀ (1-s)^N ≤ R_dec(N) ≤ B (1-s)^N`,  `k₀ = min_i 1/(a_i+1)`,
`B = ∏ b_i`, `s = ∑ p_i`.

Recover: `R_rec = E[1 - ∏_i C(a_i+L_i, L_i)^{-1}]`, and pointwise

    1/2 ≤ 1 - ∏ C^{-1}   whenever ANY class still hides a tip,
    1 - ∏ C^{-1} ≤ ∑_i L_i,

so `(1/2)(1-p_min)^N ≤ R_rec ≤ (∑ b_i)(1-p_min)^N`: the recovery exponent is
`p_min`, not `s`.  That is the separation: deciding safely is governed by the TOTAL
unsafe mass, recovering the world by the SMALLEST class mass.

Growing `K` with `a_i = b_i = 1` and `p_i = P/K`: the decide risk is EXACT,
`R_dec = (1/2)(1-P)^N`, independent of `K`, while `R_rec = E[1 - 2^{-U}]` with `U` the
number of unseen classes -- a coupon-collector scale.

## WHAT IS PROVED

* `binary_decide_value` — with one safe and one unsafe tip per class the optimal decide
  risk is EXACTLY `1/2` when every class still hides its tip and `0` otherwise.
* `prod_ge_one_sub_sum` — Weierstrass: `1 - ∑(1-c_i) ≤ ∏ c_i`.
* `two_le_choose` — `2 ≤ C(a+L, L)` for `a, L ≥ 1`, by Pascal.
* `recover_lower_pointwise` — one hidden tip already costs `1/2` in recovery.
* `recover_upper_pointwise` — recovery risk is at most `∑_i L_i`.
* `growing_K_recover` — `∏ C^{-1} = (1/2)^U` exactly, in the `a_i = b_i = 1` model.
* `expect_mono`, `decide_upper_expect`, `decide_lower_expect` — the expectation steps
  that turn the pointwise bounds into the bracket.

## WHAT THIS DOES NOT ESTABLISH

- The coupon-collector CONSTANT for growing `K` (the `(K/P)(log K + log 1/ε)` scale) is
  not proved; `growing_K_recover` gives the exact risk as a function of `U`, which is
  the input to such an estimate.
- `k₀` and `B` are fixed-`K` constants: a uniform growing-`K` statement does not follow
  from them.
-/

namespace CIGAMF.P13.SupportDecideRecover

open Finset

/-- Weierstrass: `1 - ∑(1-c_i) ≤ ∏ c_i` for `c_i ∈ [0,1]`. -/
theorem prod_ge_one_sub_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ)
    (h0 : ∀ i, 0 ≤ c i) (h1 : ∀ i, c i ≤ 1) :
    1 - ∑ i ∈ s, (1 - c i) ≤ ∏ i ∈ s, c i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a t ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  have hp : 0 ≤ ∏ i ∈ t, c i := Finset.prod_nonneg fun i _ => h0 i
  have hple : ∏ i ∈ t, c i ≤ 1 := Finset.prod_le_one (fun i _ => h0 i) (fun i _ => h1 i)
  have hS : 0 ≤ ∑ i ∈ t, (1 - c i) := Finset.sum_nonneg fun i _ => by linarith [h1 i]
  nlinarith [ih, h0 a, h1 a, hp, hple, hS]

/-- `2 ≤ C(a+L, L)` for `a, L ≥ 1`, by Pascal. -/
theorem two_le_choose (a L : ℕ) (ha : 1 ≤ a) (hL : 1 ≤ L) : 2 ≤ (a + L).choose L := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hidx : a' + 1 + (L' + 1) = (a' + L' + 1) + 1 := by omega
  rw [hidx, Nat.choose_succ_succ']
  have h1 : 0 < (a' + L' + 1).choose L' := Nat.choose_pos (by omega)
  have h2 : 0 < (a' + L' + 1).choose (L' + 1) := Nat.choose_pos (by omega)
  omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The per-class recovery factor. -/
noncomputable def cfac (a L : ι → ℕ) (i : ι) : ℝ :=
  1 / (((a i + L i).choose (L i) : ℕ) : ℝ)

theorem cfac_pos (a L : ι → ℕ) (i : ι) : 0 < cfac a L i := by
  unfold cfac
  have : 0 < (a i + L i).choose (L i) := Nat.choose_pos (by omega)
  have hc : (0:ℝ) < (((a i + L i).choose (L i) : ℕ) : ℝ) := by exact_mod_cast this
  positivity

theorem cfac_le_one (a L : ι → ℕ) (i : ι) : cfac a L i ≤ 1 := by
  unfold cfac
  have : 1 ≤ (a i + L i).choose (L i) := Nat.choose_pos (by omega)
  have hc : (1:ℝ) ≤ (((a i + L i).choose (L i) : ℕ) : ℝ) := by exact_mod_cast this
  rw [div_le_one (by linarith)]
  linarith

/-- **One hidden tip already costs `1/2` in recovery.** -/
theorem recover_lower_pointwise (a L : ι → ℕ) (ha : ∀ i, 1 ≤ a i)
    (i₀ : ι) (h : 1 ≤ L i₀) :
    (1:ℝ) / 2 ≤ 1 - ∏ i, cfac a L i := by
  classical
  have hi0 : cfac a L i₀ ≤ 1 / 2 := by
    unfold cfac
    have h2 := two_le_choose (a i₀) (L i₀) (ha i₀) h
    have hc : (2:ℝ) ≤ (((a i₀ + L i₀).choose (L i₀) : ℕ) : ℝ) := by exact_mod_cast h2
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hsplit : ∏ i, cfac a L i = cfac a L i₀ * ∏ i ∈ univ.erase i₀, cfac a L i :=
    (Finset.mul_prod_erase _ _ (mem_univ i₀)).symm
  have hrest : ∏ i ∈ univ.erase i₀, cfac a L i ≤ 1 :=
    Finset.prod_le_one (fun i _ => (cfac_pos a L i).le) (fun i _ => cfac_le_one a L i)
  have hrestnn : 0 ≤ ∏ i ∈ univ.erase i₀, cfac a L i :=
    Finset.prod_nonneg fun i _ => (cfac_pos a L i).le
  rw [hsplit]
  nlinarith [hi0, hrest, hrestnn, (cfac_pos a L i₀).le]

/-- Recovery risk is at most `∑_i L_i`. -/
theorem recover_upper_pointwise (a L : ι → ℕ) :
    1 - ∏ i, cfac a L i ≤ ∑ i, (L i : ℝ) := by
  classical
  have hW := prod_ge_one_sub_sum (univ : Finset ι) (cfac a L)
    (fun i => (cfac_pos a L i).le) (fun i => cfac_le_one a L i)
  have hterm : ∀ i : ι, 1 - cfac a L i ≤ (L i : ℝ) := by
    intro i
    rcases Nat.eq_zero_or_pos (L i) with h | h
    · have hc : cfac a L i = 1 := by
        unfold cfac
        rw [h]
        simp
      rw [hc, h]
      norm_num
    · have h1 : (1:ℝ) ≤ (L i : ℝ) := by exact_mod_cast h
      have := (cfac_pos a L i).le
      linarith
  have hsum : ∑ i, (1 - cfac a L i) ≤ ∑ i, (L i : ℝ) :=
    Finset.sum_le_sum fun i _ => hterm i
  linarith [hW, hsum]

/-- **The growing-`K` model**: with one safe and one unsafe tip per class,
`∏ C^{-1} = (1/2)^U` with `U` the number of classes that still hide their tip. -/
theorem growing_K_recover (L : ι → ℕ) (hL : ∀ i, L i ≤ 1) :
    ∏ i, (1 / ((((1:ℕ) + L i).choose (L i) : ℕ) : ℝ))
      = (1 / 2 : ℝ) ^ (univ.filter (fun i => L i = 1)).card := by
  classical
  have hfac : ∀ i : ι, (1 / ((((1:ℕ) + L i).choose (L i) : ℕ) : ℝ))
      = if L i = 1 then (1 / 2 : ℝ) else 1 := by
    intro i
    have h1 := hL i
    rcases Nat.eq_zero_or_pos (L i) with h | h
    · rw [h]; norm_num
    · have he : L i = 1 := by omega
      rw [he]; norm_num
  simp only [hfac]
  rw [Finset.prod_ite]
  simp

/-- **The binary decide value.**  With one safe and one unsafe tip per class the
optimal decide risk is exactly `1/2` when every class still hides its tip, `0`
otherwise. -/
theorem binary_decide_value [Nonempty ι] (L : ι → ℕ) (hL : ∀ i, L i ≤ 1) :
    (univ.inf' univ_nonempty (fun i => (L i : ℝ) / (1 + L i)))
      = if (∀ i, L i = 1) then (1 : ℝ) / 2 else 0 := by
  classical
  by_cases hall : ∀ i, L i = 1
  · rw [if_pos hall]
    have hval : ∀ i : ι, (L i : ℝ) / (1 + L i) = 1 / 2 := by
      intro i; rw [hall i]; norm_num
    simp only [hval]
    exact le_antisymm (Finset.inf'_le _ (mem_univ (Classical.arbitrary ι)))
      (Finset.le_inf' _ _ fun i _ => le_rfl)
  · rw [if_neg hall]
    push_neg at hall
    obtain ⟨i₀, hi₀⟩ := hall
    have h0 : L i₀ = 0 := by have := hL i₀; omega
    refine le_antisymm ?_ ?_
    · have hle := Finset.inf'_le (fun i => (L i : ℝ) / (1 + L i)) (mem_univ i₀)
      simp only [h0, Nat.cast_zero, zero_div] at hle
      exact hle
    · refine Finset.le_inf' _ _ fun i _ => ?_
      positivity

section Expect

variable {Hist : Type*} [Fintype Hist]

/-- Expectation is monotone. -/
theorem expect_mono (w f g : Hist → ℝ) (hw : ∀ h, 0 ≤ w h) (hfg : ∀ h, f h ≤ g h) :
    ∑ h, w h * f h ≤ ∑ h, w h * g h :=
  Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hfg h) (hw h)

/-- The upper end: the decide risk is at most `E ∏ L_i`, hence `B(1-s)^N`. -/
theorem decide_upper_expect (w R prodL : Hist → ℝ) (Bval rho : ℝ)
    (hw : ∀ h, 0 ≤ w h) (hpt : ∀ h, R h ≤ prodL h)
    (hE : ∑ h, w h * prodL h = Bval * rho) :
    ∑ h, w h * R h ≤ Bval * rho := by
  have := expect_mono w R prodL hw hpt
  linarith [hE ▸ this]

/-- The lower end: on the event that every class still hides a tip the risk is at
least `k₀`, so the expectation is at least `k₀` times that probability. -/
theorem decide_lower_expect (w R ind : Hist → ℝ) (k0 Pgood : ℝ)
    (hw : ∀ h, 0 ≤ w h) (hk0 : 0 ≤ k0)
    (hpt : ∀ h, k0 * ind h ≤ R h)
    (hP : ∑ h, w h * ind h = Pgood) :
    k0 * Pgood ≤ ∑ h, w h * R h := by
  have hstep := expect_mono w (fun h => k0 * ind h) R hw hpt
  have hleft : ∑ h, w h * (k0 * ind h) = k0 * ∑ h, w h * ind h := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [hleft, hP] at hstep
  exact hstep

end Expect

#print axioms prod_ge_one_sub_sum
#print axioms two_le_choose
#print axioms cfac_pos
#print axioms cfac_le_one
#print axioms recover_lower_pointwise
#print axioms recover_upper_pointwise
#print axioms growing_K_recover
#print axioms binary_decide_value
#print axioms expect_mono
#print axioms decide_upper_expect
#print axioms decide_lower_expect

end CIGAMF.P13.SupportDecideRecover
