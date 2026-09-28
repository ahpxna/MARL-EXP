import «LeanPaperCExPostV1»
import «LeanPaperCEndpointLawV1»

/-!
# Paper C: the ex-post value under the band

With the budget chosen after the draw, the objective is `E_P[max_k r_k]` (`pathObjective`).
Under the retained-marginal band this module proves, for every `η >= 0`,

* even `m >= 4`: `V^post_m(η) = 2/(m+4)`: the band costs nothing ex post;
* odd `m >= 3`:  `V^post_m(η) = (2 + 2 max(0, 1-η)/m) / (m+4)`: the band costs a factor
  `1 + 1/m` at `η = 0` and nothing from `η = 1` on.

So the two linear factors of the paper do not multiply: ex post the free value is already
`m-1` times the ex-ante one, and the band adds at most `1/m` of it.

**Lower side.**  Every ordering has a budget of excess `2` (`exists_defect`).  For odd `m`,
an ordering with the `+3` last pays `4` at budget `m-1`, and the band's upper side at `m-1`
puts the `+3` last with probability at least `(1-η)/m`.

**Upper side.**  Uniform laws on the rotations of one ranking have exactly uniform retained
marginals, so they are feasible at `η = 0`.  For even `m` rotate the flat ranking: every
rotation pays exactly `2` at worst.  For odd `m` rotate the base ranking: the one rotation that
ends with `+3` pays `4`, every other pays `2`.  At `η = 1` the insertion law pays `2` on every
ranking; blending covers `[0, 1]`.
-/

namespace CIGAMF.P13.PaperCExPostBand

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCPerm
open CIGAMF.P13.PaperCRelabelBandJoin CIGAMF.P13.PaperCFam13
open CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCOddBreakpointEndgame
open CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCExPost CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCLawRelabel CIGAMF.P13.PaperCWindow CIGAMF.P13.PaperCOdd
open CIGAMF.P13.PaperCEven CIGAMF.P13.PaperCUniform CIGAMF.P13.PaperCRelabel
open CIGAMF.P13.PaperCOddWitnessJoin CIGAMF.P13.PaperCEvenWitnessJoin

/-! ## 1. Windows of an arbitrary sequence -/

noncomputable def preG (b : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range j, b i

noncomputable def winG (b : ℕ → ℝ) (m a k : ℕ) : ℝ := ∑ i ∈ range k, b ((a + i) % m)

theorem winG_eq (b : ℕ → ℝ) (m a k : ℕ) (ha : a < m) (hk : k ≤ m) :
    winG b m a k = (preG b (min (a + k) m) - preG b a) + preG b (a + k - m) := by
  classical
  have shift : ∀ n, ∑ i ∈ range n, b (a + i) = preG b (a + n) - preG b a := by
    intro n; unfold preG; rw [Finset.sum_range_add]; ring
  rcases Nat.lt_or_ge (a + k) (m + 1) with hno | hyes
  · have hmin : min (a + k) m = a + k := by omega
    have hsub : a + k - m = 0 := by omega
    rw [hmin, hsub, show preG b 0 = 0 by simp [preG], add_zero]
    have hterm : ∀ i ∈ range k, b ((a + i) % m) = b (a + i) := by
      intro i hi; rw [Finset.mem_range] at hi; rw [Nat.mod_eq_of_lt (by omega)]
    unfold winG; rw [Finset.sum_congr rfl hterm, shift k]
  · have hmin : min (a + k) m = m := by omega
    rw [hmin]
    have hsplit : k = (m - a) + (a + k - m) := by omega
    unfold winG
    rw [hsplit, Finset.sum_range_add]
    have hlow : ∀ i ∈ range (m - a), b ((a + i) % m) = b (a + i) := by
      intro i hi; rw [Finset.mem_range] at hi; rw [Nat.mod_eq_of_lt (by omega)]
    have hhigh : ∀ i ∈ range (a + k - m), b ((a + ((m - a) + i)) % m) = b i := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hidx : a + ((m - a) + i) = m + i := by omega
      rw [hidx, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh, shift (m - a)]
    have hma : a + (m - a) = m := by omega
    rw [hma]
    have hfix : a + (m - a + (a + k - m)) - m = a + k - m := by omega
    rw [hfix]
    rfl

/-- **The prefix of a rotated ranking is a window.** -/
theorem rot_prefix (m : ℕ) [NeZero m] (f : Ranking m) (b : ℕ → ℝ)
    (hfb : ∀ i : Fin m, f i = b i) (a : Fin m) (k : ℕ) (hk : k ≤ m) :
    prefixSum (rankOf f (cyclicPerm m a)) k = winG b m a.val k := by
  classical
  have happ : ∀ c : Fin m, (cyclicPerm m a) c = c + a := fun _ => rfl
  unfold prefixSum rankOf
  rw [sum_filter]
  have hterm : ∀ c : Fin m,
      (if (c : ℕ) < k then f ((cyclicPerm m a) c) else 0)
        = (if (c : ℕ) < k then b (((c : ℕ) + (a : ℕ)) % m) else 0) := by
    intro c
    rw [happ c, hfb, Fin.val_add]
  rw [Finset.sum_congr rfl (fun c _ => hterm c),
    Fin.sum_univ_eq_sum_range (fun j => if j < k then b ((j + (a : ℕ)) % m) else 0) m]
  have hsub : range k ⊆ range m := range_mono hk
  rw [← sum_subset hsub (fun i hi hni => by simp [not_lt.mpr (by simpa using hni)])]
  unfold winG
  apply sum_congr rfl
  intro i hi
  have hik : i < k := mem_range.mp hi
  rw [if_pos hik, Nat.add_comm]

/-! ## 2. Odd sizes: every rotation of the base pays at most `2`, except the one ending `+3` -/

theorem preN_small (j : ℕ) (h2 : 2 ≤ j) : preN j = 0 ∨ preN j = -1 := by
  rcases Nat.even_or_odd j with he | ho
  · left; exact preN_even j h2 (Nat.even_iff.mp he)
  · right; exact preN_odd j h2 (Nat.odd_iff.mp ho)

theorem odd_rot_excess (s a k : ℕ) (ha : a < 2 * s + 3) (hk1 : 1 ≤ k) (hk : k ≤ 2 * s + 2) :
    |win (2 * s + 3) a k| - ((k % 2 : ℕ) : ℝ) ≤ (if a = 1 then 4 else 2) := by
  rw [win_eq (2 * s + 3) a k (by omega) ha (by omega)]
  have hkb : (0 : ℝ) ≤ ((k % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases Nat.lt_or_ge (2 * s + 3) (a + k) with hw | hnw
  · -- wraps; then `a >= 2`
    have ha2 : 2 ≤ a := by omega
    rw [if_neg (by omega), show min (a + k) (2 * s + 3) = 2 * s + 3 by omega,
      preN_odd (2 * s + 3) (by omega) (by omega)]
    rcases Nat.lt_or_ge (a + k - (2 * s + 3)) 2 with hj | hj
    · have hj1 : a + k - (2 * s + 3) = 1 := by omega
      rw [hj1, preN_one]
      rcases Nat.even_or_odd a with he | ho
      · rw [preN_even a ha2 (Nat.even_iff.mp he)]; norm_num <;> linarith
      · rw [preN_odd a ha2 (Nat.odd_iff.mp ho)]
        have hko : k % 2 = 1 := by have := Nat.odd_iff.mp ho; omega
        rw [hko]; norm_num
    · rcases preN_small a ha2 with h1 | h1 <;> rcases preN_small _ hj with h2 | h2 <;>
        rw [h1, h2] <;> norm_num <;> linarith
  · rw [show min (a + k) (2 * s + 3) = a + k by omega,
      show a + k - (2 * s + 3) = 0 by omega, preN_zero, add_zero]
    by_cases h0 : a = 0
    · subst h0
      rw [if_neg (by omega), zero_add, preN_zero, sub_zero]
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have : k = 1 := by omega
        subst this; rw [preN_one]; norm_num
      · rcases preN_small k hk2 with h | h <;> rw [h] <;> norm_num <;> linarith
    by_cases h1 : a = 1
    · subst h1
      rw [if_pos rfl, preN_one]
      rcases preN_small (1 + k) (by omega) with h | h <;> rw [h] <;> norm_num <;> linarith
    · rw [if_neg h1]
      have ha2 : 2 ≤ a := by omega
      rcases preN_small a ha2 with h1' | h1' <;> rcases preN_small (a + k) (by omega) with h2 | h2 <;>
        rw [h1', h2] <;> norm_num <;> linarith

/-! ## 3. Even sizes: every rotation of the flat ranking pays at most `2` -/

theorem flatPre_mid (m j : ℕ) (hm4 : 4 ≤ m) (hj1 : 1 ≤ j) (hj : j ≤ m - 1) :
    preG (flatW m) j = if j % 2 = 1 then -3 else -2 := by
  have h := flatEven_prefix (m := m) (by omega) j hj1 hj
  rw [← h]
  unfold preG
  exact (sum_prefix_fin j (by omega) (flatW m)).symm

theorem flatPre_total (m : ℕ) (hm4 : 4 ≤ m) (heven : m % 2 = 0) : preG (flatW m) m = 0 := by
  have h := flatEven_total (m := m) (by omega) heven
  rw [← h]
  unfold preG
  exact (sum_prefix_fin m le_rfl (flatW m)).symm

theorem flatPre_small (m j : ℕ) (hm4 : 4 ≤ m) (hj1 : 1 ≤ j) (hj : j ≤ m - 1) :
    (preG (flatW m) j = -3 ∧ j % 2 = 1) ∨ (preG (flatW m) j = -2 ∧ j % 2 = 0) := by
  rw [flatPre_mid m j hm4 hj1 hj]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · right; rw [if_neg (by omega)]; exact ⟨rfl, h⟩
  · left; rw [if_pos h]; exact ⟨rfl, h⟩

theorem even_rot_excess (m a k : ℕ) (hm4 : 4 ≤ m) (heven : m % 2 = 0) (ha : a < m)
    (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |winG (flatW m) m a k| - ((k % 2 : ℕ) : ℝ) ≤ 2 := by
  rw [winG_eq (flatW m) m a k ha (by omega)]
  have hkb : (0 : ℝ) ≤ ((k % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h0 : preG (flatW m) 0 = 0 := by simp [preG]
  rcases lt_trichotomy (a + k) m with hlt | heq | hgt
  · rw [show min (a + k) m = a + k by omega, show a + k - m = 0 by omega, h0, add_zero]
    by_cases ha0 : a = 0
    · subst ha0
      rw [h0, sub_zero, zero_add]
      rcases flatPre_small m k hm4 hk1 hk with ⟨h, hp⟩ | ⟨h, hp⟩ <;> rw [h, hp] <;> norm_num
    · rcases flatPre_small m a hm4 (by omega) (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases flatPre_small m (a + k) hm4 (by omega) (by omega) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
        rw [h1, h2] <;> norm_num <;> linarith
  · rw [show min (a + k) m = m by omega, show a + k - m = 0 by omega, h0, add_zero,
      flatPre_total m hm4 heven]
    rcases flatPre_small m a hm4 (by omega) (by omega) with ⟨h, hp⟩ | ⟨h, hp⟩
    · rw [h, show k % 2 = 1 by omega]; norm_num
    · rw [h]; norm_num <;> linarith
  · rw [show min (a + k) m = m by omega, flatPre_total m hm4 heven]
    rcases flatPre_small m a hm4 (by omega) (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases flatPre_small m (a + k - m) hm4 (by omega) (by omega) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] <;> norm_num <;> linarith

/-! ## 4. The banded ex-post value -/

/-- The ex-post value under the band: the infimum of `E_P[max_k r_k]` over band-feasible
laws on all permutations. -/
noncomputable def postValue (m : ℕ) (hm : 3 ≤ m) (η : ℝ) : ℝ :=
  sInf ((fun P => pathObjective m (by omega) P) '' FeasibleAt (id : Perm m → _) η)

theorem worstBudget_nonneg {m : ℕ} (hm : 3 ≤ m) (σ : Perm m) :
    0 ≤ worstBudget m (by omega) σ :=
  le_trans (div_nonneg (by norm_num) (denom_pos m).le) (worstBudget_ge hm σ)

theorem post_le {m : ℕ} (hm : 3 ≤ m) (η : ℝ) (P : Perm m → ℝ)
    (hP : P ∈ FeasibleAt (id : Perm m → _) η) :
    postValue m hm η ≤ pathObjective m (by omega) P := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨Q, hQ, rfl⟩
    exact Finset.sum_nonneg (fun σ _ => mul_nonneg (hQ.1 σ) (worstBudget_nonneg hm σ))
  · exact ⟨P, hP, rfl⟩

theorem post_ge {m : ℕ} (hm : 3 ≤ m) (η : ℝ) (hη : 0 ≤ η) (c : ℝ)
    (h : ∀ P ∈ FeasibleAt (id : Perm m → _) η, c ≤ pathObjective m (by omega) P) :
    c ≤ postValue m hm η := by
  have : NeZero m := ⟨by omega⟩
  apply le_csInf ((allPerm_feasible_nonempty m η hη).image _)
  rintro _ ⟨P, hP, rfl⟩
  exact h P hP

theorem pathObjective_blend {m : ℕ} (hm : 3 ≤ m) (P Q : Perm m → ℝ) (t : ℝ) :
    pathObjective m (by omega) (blend t P Q)
      = (1 - t) * pathObjective m (by omega) P + t * pathObjective m (by omega) Q := by
  unfold pathObjective blend
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun σ _ => by ring)

/-! ### lower sides -/

theorem post_ge_two {m : ℕ} (hm : 3 ≤ m) (η : ℝ) (hη : 0 ≤ η) :
    2 / denom m ≤ postValue m hm η :=
  post_ge hm η hη _ (fun P hP => pathObjective_ge hm P ⟨hP.1, hP.2.1⟩)

/-- An odd ordering with the `+3` last pays `4` at budget `m-1`. -/
theorem worstBudget_plus {m : ℕ} (hm : 3 ≤ m) (hmo : m % 2 = 1) (σ : Perm m) :
    2 / denom m + 2 / denom m * (if plusItem m hm = σ ⟨m - 1, by omega⟩ then 1 else 0)
      ≤ worstBudget m (by omega) σ := by
  by_cases h : plusItem m hm = σ ⟨m - 1, by omega⟩
  · rw [if_pos h, mul_one]
    have hmem : m - 1 ∈ budgets m := by rw [mem_budgets]; omega
    refine le_trans ?_ (Finset.le_sup' (fun k => regret (gFamily m) σ (denom m) k) hmem)
    show _ ≤ excess (rankOf (gFamily m) σ) (m - 1) / denom m
    rw [excess_last (by omega) hmo _ (ranked_odd m hm hmo σ)]
    have hv : rankOf (gFamily m) σ ⟨m - 1, by omega⟩ = 3 := by
      show gFamily m (σ ⟨m - 1, by omega⟩) = 3
      rw [← h, plusItem_weight]
    rw [hv]
    have hD := denom_pos m
    rw [show |(-1 : ℝ) - 3| = 4 by norm_num]
    rw [← add_div]; norm_num
  · rw [if_neg h, mul_zero, add_zero]; exact worstBudget_ge hm σ

theorem post_ge_odd {m : ℕ} (hm : 3 ≤ m) (hmo : m % 2 = 1) (η : ℝ) (hη : 0 ≤ η) :
    2 / denom m + 2 * (1 - η) / ((m : ℝ) * denom m) ≤ postValue m hm η := by
  apply post_ge hm η hη
  intro P hP
  have hmass := last_plus_mass m hm η P hP
  unfold pathObjective
  calc 2 / denom m + 2 * (1 - η) / ((m : ℝ) * denom m)
      = 2 / denom m + 2 / denom m * ((1 - η) / (m : ℝ)) := by
        have := denom_pos m
        have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        field_simp
    _ ≤ 2 / denom m + 2 / denom m
          * ∑ σ, P σ * (if plusItem m hm = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) := by
        have := div_pos (by norm_num : (0 : ℝ) < 2) (denom_pos m)
        nlinarith
    _ = ∑ σ, P σ * (2 / denom m + 2 / denom m
          * (if plusItem m hm = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0)) := by
        rw [Finset.mul_sum]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hP.2.1, one_mul]
        congr 1
        exact Finset.sum_congr rfl (fun σ _ => by ring)
    _ ≤ _ := Finset.sum_le_sum (fun σ _ =>
          mul_le_mul_of_nonneg_left (worstBudget_plus hm hmo σ) (hP.1 σ))

/-! ### the witnesses -/

theorem rankOf_wperm {m : ℕ} (g : Ranking m) (c : WPerm g) (σ : Perm m) :
    rankOf g (c.val * σ) = rankOf g σ := by
  funext i
  show g (c.val (σ i)) = g (σ i)
  exact c.property (σ i)

theorem worstBudget_wperm {m : ℕ} (hm : 3 ≤ m) (c : WPerm (gFamily m)) (σ : Perm m) :
    worstBudget m (by omega) (c.val * σ) = worstBudget m (by omega) σ := by
  unfold worstBudget regret
  rw [rankOf_wperm]

theorem sym_sum {m : ℕ} {R : Type*} [Fintype R] (g : Ranking m) (base : R → Perm m)
    (q : R → ℝ) (F : Perm m → ℝ) (hF : ∀ (c : WPerm g) σ, F (c.val * σ) = F σ) :
    ∑ p, symLaw g q p * F (symPerm g base p) = ∑ x, q x * F (base x) := by
  have hcard : (Fintype.card (WPerm g) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (WPerm g) := Fintype.card_pos
    exact_mod_cast this.ne'
  unfold symLaw symPerm
  rw [Fintype.sum_prod_type]
  simp only [hF]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  field_simp

/-- **The insertion law pays `2` on every ranking**, and is feasible at `η = 1`. -/
theorem insertion_post (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) :
    ∃ P ∈ FeasibleAt (id : Perm m → _) 1, pathObjective m (by omega) P ≤ 2 / denom m := by
  refine ⟨pushLaw (symPerm (gFamily m) (insPerm m hm)) (symLaw (gFamily m) (insQ m)),
    feasible_push _ _ _ (band_of_prefix_counts (gFamily m) (insPerm m hm) (insQ m) 1
      (insQ_nonneg m hm) (insQ_sum m hm) (odd_hcounts m hm hmo)), ?_⟩
  unfold pathObjective
  rw [pushLaw_expect, sym_sum (gFamily m) (insPerm m hm) (insQ m)
    (fun σ => worstBudget m (by omega) σ) (fun c σ => worstBudget_wperm hm c σ)]
  have hwb : ∀ x, worstBudget m (by omega) (insPerm m hm x) ≤ 2 / denom m := by
    intro x
    apply worstBudget_le_of
    intro k hk
    rw [rankOf_insPerm, insRanking_excess m x (by have := x.isLt; omega) k
      (by rw [mem_budgets] at hk; omega)]
    split_ifs <;> norm_num
  calc ∑ x, insQ m x * worstBudget m (by omega) (insPerm m hm x)
      ≤ ∑ x, insQ m x * (2 / denom m) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hwb x) (insQ_nonneg m hm x))
    _ = 2 / denom m := by rw [← Finset.sum_mul, insQ_sum m hm, one_mul]

/-- **The rotation law of the odd base**: feasible at `η = 0`, paying `2 + 2/m` on average. -/
theorem odd_rotation_post (s : ℕ) :
    ∃ P ∈ FeasibleAt (id : Perm (2 * s + 3) → _) 0,
      pathObjective (2 * s + 3) (by omega) P
        ≤ (2 + 2 / ((2 * s + 3 : ℕ) : ℝ)) / denom (2 * s + 3) := by
  have : NeZero (2 * s + 3) := ⟨by omega⟩
  set m := 2 * s + 3 with hmdef
  have hm : 3 ≤ m := by omega
  refine ⟨pushLaw (fun a => oddToFamily s * cyclicPerm m a) (cyclicLaw m),
    feasible_push _ _ _ (feasible_left_relabel (cyclicLaw m) (cyclicPerm m) (oddToFamily s) 0
      (feasible_zero_nonempty m)), ?_⟩
  unfold pathObjective
  rw [pushLaw_expect]
  have hD := denom_pos m
  have hwb : ∀ a : Fin m, worstBudget m (by omega) (oddToFamily s * cyclicPerm m a)
      ≤ (if a.val = 1 then 4 else 2) / denom m := by
    intro a
    apply Finset.sup'_le
    intro k hk
    rw [mem_budgets] at hk
    show excess (rankOf (gFamily m) (oddToFamily s * cyclicPerm m a)) k / denom m ≤ _
    rw [rankOf_change_base (oddBase m) (gFamily m) (oddToFamily s) (oddToFamily_apply s)]
    apply div_le_div_of_nonneg_right _ hD.le
    unfold excess
    rw [rotated_prefix_eq_win m a k (by omega)]
    exact odd_rot_excess s a.val k a.isLt hk.1 (by omega)
  have hsum : ∑ a : Fin m, (if a.val = 1 then (4 : ℝ) else 2) = 2 * (m : ℝ) + 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = 1 then (4 : ℝ) else 2) m]
    have : ∀ j ∈ range m, (if j = 1 then (4 : ℝ) else 2) = 2 + (if j = 1 then 2 else 0) := by
      intro j _; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Finset.sum_ite_eq' (range m) 1, if_pos (Finset.mem_range.mpr (by omega))]
    ring
  calc ∑ a : Fin m, cyclicLaw m a * worstBudget m (by omega) (oddToFamily s * cyclicPerm m a)
      ≤ ∑ a : Fin m, cyclicLaw m a * ((if a.val = 1 then 4 else 2) / denom m) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hwb a)
          (by unfold cyclicLaw; positivity))
    _ = (2 + 2 / (m : ℝ)) / denom m := by
        unfold cyclicLaw
        rw [← Finset.mul_sum, ← Finset.sum_div, hsum]
        have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        field_simp
        try ring

/-- **The rotation law of the flat ranking**: feasible at `η = 0`, paying `2` on every
ranking. -/
theorem even_rotation_post (m : ℕ) (heven : Even m) (hm4 : 4 ≤ m) :
    ∃ P ∈ FeasibleAt (id : Perm m → _) 0, pathObjective m (by omega) P ≤ 2 / denom m := by
  have : NeZero m := ⟨by omega⟩
  have hm : 3 ≤ m := by omega
  refine ⟨pushLaw (fun a => flatToFamily m heven hm4 * cyclicPerm m a) (cyclicLaw m),
    feasible_push _ _ _ (feasible_left_relabel (cyclicLaw m) (cyclicPerm m)
      (flatToFamily m heven hm4) 0 (feasible_zero_nonempty m)), ?_⟩
  unfold pathObjective
  rw [pushLaw_expect]
  have hwb : ∀ a : Fin m,
      worstBudget m (by omega) (flatToFamily m heven hm4 * cyclicPerm m a) ≤ 2 / denom m := by
    intro a
    apply worstBudget_le_of
    intro k hk
    rw [mem_budgets] at hk
    rw [rankOf_change_base (flatEven m) (gFamily m) (flatToFamily m heven hm4)
      (flatToFamily_apply m heven hm4)]
    unfold excess
    rw [rot_prefix m (flatEven m) (flatW m) (flatEven_eq_flatW m) a k (by omega)]
    exact even_rot_excess m a.val k hm4 (Nat.even_iff.mp heven) a.isLt hk.1 hk.2
  calc ∑ a : Fin m, cyclicLaw m a * worstBudget m (by omega) (flatToFamily m heven hm4 * cyclicPerm m a)
      ≤ ∑ a : Fin m, cyclicLaw m a * (2 / denom m) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hwb a)
          (by unfold cyclicLaw; positivity))
    _ = 2 / denom m := by
        rw [← Finset.sum_mul]
        unfold cyclicLaw
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        field_simp

/-! ## 5. The two values -/

/-- **Even sizes: the band is free ex post.** -/
theorem expost_even (m : ℕ) (hm4 : 4 ≤ m) (heven : Even m) (η : ℝ) (hη : 0 ≤ η) :
    postValue m (by omega) η = 2 / denom m := by
  apply le_antisymm
  · obtain ⟨P, hP, hv⟩ := even_rotation_post m heven hm4
    exact (post_le (by omega) η P (feasible_mono id 0 η (by omega) hη hP)).trans hv
  · exact post_ge_two (by omega) η hη

/-- **Odd sizes: the band costs `1 + 1/m` at `η = 0`, falling linearly to nothing at
`η = 1`.** -/
theorem expost_odd (s : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    postValue (2 * s + 3) (by omega) η
      = (2 + 2 * max 0 (1 - η) / ((2 * s + 3 : ℕ) : ℝ)) / denom (2 * s + 3) := by
  set m := 2 * s + 3 with hmdef
  have hm : 3 ≤ m := by omega
  have hmo : m % 2 = 1 := by omega
  have hD := denom_pos m
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨P1, hP1f, hP1v⟩ := insertion_post m hm hmo
  rcases le_or_gt 1 η with h1 | h1
  · rw [max_eq_left (by linarith : 1 - η ≤ 0), mul_zero, zero_div, add_zero]
    apply le_antisymm
    · exact (post_le hm η P1 (feasible_mono id 1 η (by omega) h1 hP1f)).trans hP1v
    · exact post_ge_two hm η hη
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 - η)]
    apply le_antisymm
    · obtain ⟨Q0, hQ0f, hQ0v⟩ := odd_rotation_post s
      have hfeas : blend η Q0 P1 ∈ FeasibleAt (id : Perm m → _) η := by
        have h := blend_feasible Q0 P1 0 1 η hQ0f hP1f hη h1.le
        rwa [show (1 - η) * 0 + η * 1 = η by ring] at h
      calc postValue m hm η ≤ pathObjective m (by omega) (blend η Q0 P1) :=
            post_le hm η _ hfeas
        _ = (1 - η) * pathObjective m (by omega) Q0 + η * pathObjective m (by omega) P1 :=
            pathObjective_blend hm Q0 P1 η
        _ ≤ (1 - η) * ((2 + 2 / (m : ℝ)) / denom m) + η * (2 / denom m) := by
            have hA := mul_le_mul_of_nonneg_left hQ0v (by linarith : (0 : ℝ) ≤ 1 - η)
            have hB := mul_le_mul_of_nonneg_left hP1v hη
            linarith
        _ = (2 + 2 * (1 - η) / (m : ℝ)) / denom m := by
            field_simp
            ring
    · have h := post_ge_odd hm hmo η hη
      have e : 2 / denom m + 2 * (1 - η) / ((m : ℝ) * denom m)
          = (2 + 2 * (1 - η) / (m : ℝ)) / denom m := by
        field_simp
      linarith

end CIGAMF.P13.PaperCExPostBand

#print axioms CIGAMF.P13.PaperCExPostBand.winG_eq
#print axioms CIGAMF.P13.PaperCExPostBand.odd_rot_excess
#print axioms CIGAMF.P13.PaperCExPostBand.even_rot_excess
#print axioms CIGAMF.P13.PaperCExPostBand.expost_even
#print axioms CIGAMF.P13.PaperCExPostBand.expost_odd
