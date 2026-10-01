import «LeanPaperCOddKinkV1»

/-!
# Paper C: the odd frontier, part 2 -- the kink law, its value and its counts

The law attaining the crossing point `eta_t = 1 - 2/(m(m-1))` of the two odd lines, at
`m = 2s+3` with `s >= 2`.  In units of `u = 1/(m^2 (m-1))`:

* slot `t` in `{0, ..., m-3}`, versions A and B with equal mass: total `m^2 + 1` at each
  slot, except `m^2 - m + 4` at slot `0`;
* slot `m-2`, version A only: `m(m-1)`;
* `r3W` (the `+3` last): `2`;
* `r1W` (a `+1` last): `m-3`.

Every budget then carries expected excess exactly `2(m^2+1) u`: slot `t` puts its spike at
budget `t+1`, and at budget `m-1` the last slot, `r3W` (excess `4`) and `r1W` (excess `2`)
add up to the same.  This module proves the value; the band is part 3.
-/

namespace CIGAMF.P13.PaperCOddKinkLaw

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCPerm
open CIGAMF.P13.PaperCRelabelBandJoin CIGAMF.P13.PaperCFam13
open CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCOddBreakpointEndgame
open CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCRelaxedJoin CIGAMF.P13.PaperCOddKink

/-! ## 1. The components -/

/-- The index set: slots `0..m-3` with a version flag, then the three single components. -/
abbrev KIdx (s : ℕ) := (Fin (2 * s + 1) × Bool) ⊕ Fin 3

/-- The weight sequence of each component. -/
noncomputable def kwt (s : ℕ) : KIdx s → ℕ → ℝ
  | Sum.inl (t, b) => if b then spB (2 * s + 3) t else insWeight t
  | Sum.inr i => if i.val = 0 then insWeight (2 * s + 1)
      else if i.val = 1 then r3W (2 * s + 3) else r1W (2 * s + 3)

theorem kwt_cnt (s : ℕ) (hs : 1 ≤ s) (x : KIdx s) (w : ℝ) :
    cnt (kwt s x) w (2 * s + 3) = tcount (2 * s + 3) w := by
  rcases x with ⟨t, b⟩ | i
  · have ht : (t : ℕ) ≤ 2 * s := by have := t.isLt; omega
    cases b
    · show cnt (insWeight t) w (2 * s + 3) = _
      rw [cnt_insWeight]
      exact countIns_full (2 * s + 3) (by omega) t (by omega) w
    · exact cnt_spB s t ht w
  · have hi := i.isLt
    show cnt (if i.val = 0 then insWeight (2 * s + 1)
      else if i.val = 1 then r3W (2 * s + 3) else r1W (2 * s + 3)) w (2 * s + 3) = _
    by_cases h0 : i.val = 0
    · rw [if_pos h0, cnt_insWeight]
      exact countIns_full (2 * s + 3) (by omega) (2 * s + 1) (by omega) w
    · rw [if_neg h0]
      by_cases h1 : i.val = 1
      · rw [if_pos h1]; exact cnt_r3W s w
      · rw [if_neg h1]; exact cnt_r1W s hs w

/-- The permutation naming each component. -/
noncomputable def kperm (s : ℕ) (hs : 1 ≤ s) (x : KIdx s) : Equiv.Perm (Fin (2 * s + 3)) :=
  permOfCountEq (fun i : Fin (2 * s + 3) => kwt s x i) (gFamily (2 * s + 3))
    (rearr_of_cnt s (kwt s x) (kwt_cnt s hs x))

theorem kperm_apply (s : ℕ) (hs : 1 ≤ s) (x : KIdx s) (p : Fin (2 * s + 3)) :
    gFamily (2 * s + 3) (kperm s hs x p) = kwt s x p :=
  permOfCountEq_apply _ _ _ p

theorem rankOf_kperm (s : ℕ) (hs : 1 ≤ s) (x : KIdx s) :
    rankOf (gFamily (2 * s + 3)) (kperm s hs x) = fun i : Fin (2 * s + 3) => kwt s x i :=
  rankOf_permOfCountEq _ _ _

/-! ## 2. The masses -/

/-- `m` as a real. -/
noncomputable def mR (s : ℕ) : ℝ := 2 * (s : ℝ) + 3

/-- The unit mass `1/(m^2 (m-1))`. -/
noncomputable def uM (s : ℕ) : ℝ := 1 / (mR s ^ 2 * (mR s - 1))

/-- Total slot mass, in units. -/
noncomputable def alpha (s : ℕ) (t : ℕ) : ℝ :=
  if t = 0 then mR s ^ 2 - mR s + 4 else mR s ^ 2 + 1

noncomputable def kq (s : ℕ) : KIdx s → ℝ
  | Sum.inl (t, _) => alpha s t / 2 * uM s
  | Sum.inr i => if i.val = 0 then mR s * (mR s - 1) * uM s
      else if i.val = 1 then 2 * uM s else (mR s - 3) * uM s

theorem mR_pos (s : ℕ) : 3 ≤ mR s := by
  unfold mR; have : (0 : ℝ) ≤ s := Nat.cast_nonneg s; linarith

theorem uM_pos (s : ℕ) : 0 < uM s := by
  unfold uM; have := mR_pos s; apply div_pos one_pos; nlinarith

theorem alpha_pos (s : ℕ) (t : ℕ) : 0 < alpha s t := by
  unfold alpha; have := mR_pos s
  split_ifs <;> nlinarith

theorem kq_nonneg (s : ℕ) (x : KIdx s) : 0 ≤ kq s x := by
  have hu := uM_pos s; have hm := mR_pos s
  rcases x with ⟨t, b⟩ | i
  · exact mul_nonneg (div_nonneg (alpha_pos s t).le (by norm_num)) hu.le
  · show 0 ≤ (if i.val = 0 then mR s * (mR s - 1) * uM s
      else if i.val = 1 then 2 * uM s else (mR s - 3) * uM s)
    split_ifs
    · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hu.le
    · exact mul_nonneg (by norm_num) hu.le
    · exact mul_nonneg (by linarith) hu.le

/-- Sums over the index set, split into the slot part and the three singles. -/
theorem sum_KIdx (s : ℕ) (f : KIdx s → ℝ) :
    ∑ x, f x = ∑ t : Fin (2 * s + 1), (f (Sum.inl (t, false)) + f (Sum.inl (t, true)))
      + (f (Sum.inr 0) + f (Sum.inr 1) + f (Sum.inr 2)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_three]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Fintype.sum_bool]
  ring

/-- The slot masses add up: `sum_t alpha_t = (m-2)(m^2+1) - (m-3)`. -/
theorem sum_alpha (s : ℕ) :
    ∑ t : Fin (2 * s + 1), alpha s t = (mR s - 2) * (mR s ^ 2 + 1) - (mR s - 3) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => alpha s t) (2 * s + 1), Finset.sum_range_succ']
  have hrest : ∀ t ∈ range (2 * s), alpha s (t + 1) = mR s ^ 2 + 1 := by
    intro t _; unfold alpha; rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold alpha mR
  rw [if_pos rfl]
  push_cast
  ring

theorem kq_sum (s : ℕ) : ∑ x, kq s x = 1 := by
  rw [sum_KIdx]
  have hslot : ∀ t : Fin (2 * s + 1),
      kq s (Sum.inl (t, false)) + kq s (Sum.inl (t, true)) = alpha s t * uM s := by
    intro t; show alpha s t / 2 * uM s + alpha s t / 2 * uM s = _; ring
  rw [Finset.sum_congr rfl (fun t _ => hslot t), ← Finset.sum_mul, sum_alpha]
  show _ + (mR s * (mR s - 1) * uM s + 2 * uM s + (mR s - 3) * uM s) = 1
  have hm := mR_pos s
  have h1 : mR s - 1 ≠ 0 := by linarith
  have h2 : mR s ≠ 0 := by linarith
  unfold uM
  field_simp
  ring

/-! ## 3. Excess of each component -/

theorem prefixSum_congr_below {m : ℕ} (π π' : Ranking m) (k : ℕ)
    (h : ∀ i : Fin m, (i : ℕ) < k → π i = π' i) : prefixSum π k = prefixSum π' k := by
  unfold prefixSum
  refine Finset.sum_congr rfl (fun i hi => h i ?_)
  simpa using hi

/-- The excess each component carries at budget `k`, `1 <= k <= m-1`. -/
noncomputable def kex (s : ℕ) : KIdx s → ℕ → ℝ
  | Sum.inl (t, _) => fun k => if k = (t : ℕ) + 1 then 2 else 0
  | Sum.inr i => fun k => if i.val = 0 then (if k = 2 * s + 2 then 2 else 0)
      else if i.val = 1 then (if k = 2 * s + 2 then 4 else 0)
      else (if k = 1 then 2 else 0) + (if k = 2 * s + 2 then 2 else 0)

theorem excess_spB (s t : ℕ) (ht : t ≤ 2 * s) (k : ℕ) (hk : k ≤ 2 * s + 2) :
    excess (fun i : Fin (2 * s + 3) => spB (2 * s + 3) t i) k
      = excess (insRanking (2 * s + 3) t) k := by
  have hneg : prefixSum (fun i : Fin (2 * s + 3) => spB (2 * s + 3) t i) k
      = prefixSum (fun i : Fin (2 * s + 3) => -(insRanking (2 * s + 3) t i)) k := by
    apply prefixSum_congr_below
    intro i hi
    show spB (2 * s + 3) t i = -insWeight t i
    unfold spB
    rw [if_neg (show (i : ℕ) ≠ 2 * s + 3 - 1 by omega)]
  unfold excess
  rw [hneg, prefixSum_neg, abs_neg]

theorem kwt_inr (s : ℕ) (i : Fin 3) :
    kwt s (Sum.inr i) = if i.val = 0 then insWeight (2 * s + 1)
      else if i.val = 1 then r3W (2 * s + 3) else r1W (2 * s + 3) := rfl

theorem kex_inr (s : ℕ) (i : Fin 3) (k : ℕ) :
    kex s (Sum.inr i) k = if i.val = 0 then (if k = 2 * s + 2 then 2 else 0)
      else if i.val = 1 then (if k = 2 * s + 2 then 4 else 0)
      else (if k = 1 then 2 else 0) + (if k = 2 * s + 2 then 2 else 0) := rfl

theorem kex_eq (s : ℕ) (hs : 1 ≤ s) (x : KIdx s) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * s + 2) :
    excess (fun i : Fin (2 * s + 3) => kwt s x i) k = kex s x k := by
  rcases x with ⟨t, b⟩ | i
  · have ht : (t : ℕ) ≤ 2 * s := by have := t.isLt; omega
    have hins := insRanking_excess (2 * s + 3) t (by omega) k (by omega)
    cases b
    · exact hins
    · show excess (fun i : Fin (2 * s + 3) => spB (2 * s + 3) t i) k = _
      rw [excess_spB s t ht k hk]; exact hins
  · have hi := i.isLt
    rw [kwt_inr, kex_inr]
    by_cases h0 : i.val = 0
    · rw [if_pos h0, if_pos h0]
      have hA := insRanking_excess (2 * s + 3) (2 * s + 1) (by omega) k (by omega)
      rw [show 2 * s + 1 + 1 = 2 * s + 2 from rfl] at hA
      exact hA
    rw [if_neg h0, if_neg h0]
    by_cases h1 : i.val = 1
    · rw [if_pos h1, if_pos h1]
      have hbelow : ∀ k', k' ≤ 2 * s + 1 →
          prefixSum (fun j : Fin (2 * s + 3) => r3W (2 * s + 3) j) k'
            = prefixSum (insRanking (2 * s + 3) (2 * s + 1)) k' := by
        intro k' hk'
        apply prefixSum_congr_below
        intro j hj
        show r3W (2 * s + 3) j = insWeight (2 * s + 1) j
        unfold r3W
        rw [if_neg (show (j : ℕ) ≠ 2 * s + 3 - 2 by omega),
          if_neg (show (j : ℕ) ≠ 2 * s + 3 - 1 by omega),
          show 2 * s + 3 - 2 = 2 * s + 1 from by omega]
      rcases Nat.lt_or_ge k (2 * s + 2) with hlt | hge
      · have hk' : k ≤ 2 * s + 1 := by omega
        rw [if_neg (show k ≠ 2 * s + 2 by omega)]
        have hA := insRanking_excess (2 * s + 3) (2 * s + 1) (by omega) k (by omega)
        rw [if_neg (show k ≠ 2 * s + 1 + 1 by omega)] at hA
        unfold excess at hA ⊢
        rw [hbelow k hk']
        exact hA
      · have hk2 : k = 2 * s + 2 := by omega
        subst hk2
        rw [if_pos rfl]
        have hp := insRanking_prefix (2 * s + 3) (2 * s + 1) (by omega) (2 * s + 1) (by omega)
        rw [if_neg (show 2 * s + 1 ≠ 2 * s + 1 + 1 by omega),
          if_neg (show ¬ Even (2 * s + 1) from by
            rw [Nat.not_even_iff_odd]; exact ⟨s, rfl⟩)] at hp
        unfold excess
        rw [prefixSum_succ _ (2 * s + 1) (by omega), hbelow (2 * s + 1) le_rfl, hp]
        show |(-1 : ℝ) + r3W (2 * s + 3) (2 * s + 1)| - (((2 * s + 2) % 2 : ℕ) : ℝ) = 4
        unfold r3W
        rw [if_pos (show 2 * s + 1 = 2 * s + 3 - 2 by omega),
          show (2 * s + 2) % 2 = 0 from by omega]
        norm_num
    · rw [if_neg h1, if_neg h1]
      have hbelow : ∀ k', k' ≤ 2 * s + 1 →
          prefixSum (fun j : Fin (2 * s + 3) => r1W (2 * s + 3) j) k'
            = prefixSum (insRanking (2 * s + 3) 0) k' := by
        intro k' hk'
        apply prefixSum_congr_below
        intro j hj
        show r1W (2 * s + 3) j = insWeight 0 j
        unfold r1W
        rw [if_neg (show (j : ℕ) ≠ 2 * s + 3 - 2 by omega),
          if_neg (show (j : ℕ) ≠ 2 * s + 3 - 1 by omega)]
      rcases Nat.lt_or_ge k (2 * s + 2) with hlt | hge
      · have hk' : k ≤ 2 * s + 1 := by omega
        rw [if_neg (show k ≠ 2 * s + 2 by omega), add_zero]
        have hA := insRanking_excess (2 * s + 3) 0 (by omega) k (by omega)
        rw [show (0 : ℕ) + 1 = 1 from rfl] at hA
        unfold excess at hA ⊢
        rw [hbelow k hk']
        exact hA
      · have hk2 : k = 2 * s + 2 := by omega
        subst hk2
        rw [if_neg (show 2 * s + 2 ≠ 1 by omega), if_pos rfl, zero_add]
        have hp := insRanking_prefix (2 * s + 3) 0 (by omega) (2 * s + 1) (by omega)
        rw [if_neg (show 2 * s + 1 ≠ 0 + 1 by omega),
          if_neg (show ¬ Even (2 * s + 1) from by
            rw [Nat.not_even_iff_odd]; exact ⟨s, rfl⟩)] at hp
        unfold excess
        rw [prefixSum_succ _ (2 * s + 1) (by omega), hbelow (2 * s + 1) le_rfl, hp]
        show |(-1 : ℝ) + r1W (2 * s + 3) (2 * s + 1)| - (((2 * s + 2) % 2 : ℕ) : ℝ) = 2
        unfold r1W
        rw [if_pos (show 2 * s + 1 = 2 * s + 3 - 2 by omega),
          show (2 * s + 2) % 2 = 0 from by omega]
        norm_num

/-! ## 4. The value: flat at `2(m^2+1) u` -/

/-- The target value `V* = 2(m^2+1) u / D`. -/
noncomputable def vstar (s : ℕ) : ℝ := 2 * (mR s ^ 2 + 1) * uM s / denom (2 * s + 3)

theorem kslot_excess (s : ℕ) (k : ℕ) (hk1 : 1 ≤ k) :
    ∑ t : Fin (2 * s + 1), (kq s (Sum.inl (t, false)) * kex s (Sum.inl (t, false)) k
        + kq s (Sum.inl (t, true)) * kex s (Sum.inl (t, true)) k)
      = if k ≤ 2 * s + 1 then 2 * alpha s (k - 1) * uM s else 0 := by
  have hpt : ∀ t : Fin (2 * s + 1),
      kq s (Sum.inl (t, false)) * kex s (Sum.inl (t, false)) k
        + kq s (Sum.inl (t, true)) * kex s (Sum.inl (t, true)) k
      = (fun t : ℕ => if t = k - 1 then 2 * alpha s t * uM s else 0) t := by
    intro t
    show alpha s t / 2 * uM s * (if k = (t : ℕ) + 1 then 2 else 0)
      + alpha s t / 2 * uM s * (if k = (t : ℕ) + 1 then 2 else 0) = _
    by_cases h : (t : ℕ) = k - 1
    · rw [if_pos (show k = (t : ℕ) + 1 by omega)]
      show _ = if (t : ℕ) = k - 1 then _ else _
      rw [if_pos h]; ring
    · rw [if_neg (show k ≠ (t : ℕ) + 1 by omega)]
      show _ = if (t : ℕ) = k - 1 then _ else _
      rw [if_neg h]; ring
  rw [Finset.sum_congr rfl (fun t _ => hpt t),
    Fin.sum_univ_eq_sum_range (fun t : ℕ => if t = k - 1 then 2 * alpha s t * uM s else 0),
    Finset.sum_ite_eq' (range (2 * s + 1)) (k - 1)]
  by_cases hk : k ≤ 2 * s + 1
  · rw [if_pos (Finset.mem_range.mpr (by omega)), if_pos hk]
  · rw [if_neg (fun h => hk (by have := Finset.mem_range.mp h; omega)), if_neg hk]

theorem kmix_excess (s : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * s + 2) :
    ∑ x, kq s x * kex s x k = 2 * (mR s ^ 2 + 1) * uM s := by
  rw [sum_KIdx, kslot_excess s k hk1]
  show _ + (kq s (Sum.inr 0) * kex s (Sum.inr 0) k + kq s (Sum.inr 1) * kex s (Sum.inr 1) k
      + kq s (Sum.inr 2) * kex s (Sum.inr 2) k) = _
  simp only [kex_inr]
  show _ + ((if (0 : Fin 3).val = 0 then mR s * (mR s - 1) * uM s
      else if (0 : Fin 3).val = 1 then 2 * uM s else (mR s - 3) * uM s) * _
    + (if (1 : Fin 3).val = 0 then mR s * (mR s - 1) * uM s
      else if (1 : Fin 3).val = 1 then 2 * uM s else (mR s - 3) * uM s) * _
    + (if (2 : Fin 3).val = 0 then mR s * (mR s - 1) * uM s
      else if (2 : Fin 3).val = 1 then 2 * uM s else (mR s - 3) * uM s) * _) = _
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, if_true, if_false,
    show (1 : ℕ) ≠ 0 from by omega, show (2 : ℕ) ≠ 0 from by omega,
    show (2 : ℕ) ≠ 1 from by omega]
  rcases Nat.lt_or_ge k (2 * s + 2) with hlt | hge
  · have hne : k ≠ 2 * s + 2 := by omega
    rw [if_pos (show k ≤ 2 * s + 1 by omega)]
    simp only [hne, if_false]
    by_cases h1 : k = 1
    · subst h1
      simp only [if_true]
      unfold alpha; rw [if_pos rfl]; ring
    · simp only [h1, if_false]
      unfold alpha; rw [if_neg (show k - 1 ≠ 0 by omega)]; ring
  · have hk2 : k = 2 * s + 2 := by omega
    subst hk2
    simp only [show ¬ (2 * s + 2 ≤ 2 * s + 1) from by omega, show 2 * s + 2 ≠ 1 from by omega,
      if_false, if_true]
    ring

theorem kvalue (s : ℕ) (hs : 1 ≤ s) :
    ∀ k ∈ budgets (2 * s + 3),
      (∑ x, kq s x * regret (gFamily (2 * s + 3)) (kperm s hs x) (denom (2 * s + 3)) k)
        ≤ vstar s := by
  intro k hk
  have hk' : 1 ≤ k ∧ k ≤ 2 * s + 2 := by simp [budgets] at hk; omega
  apply le_of_eq
  have hreg : ∀ x, kq s x * regret (gFamily (2 * s + 3)) (kperm s hs x) (denom (2 * s + 3)) k
      = kq s x * kex s x k / denom (2 * s + 3) := by
    intro x
    unfold regret
    rw [rankOf_kperm, kex_eq s hs x k hk'.1 hk'.2]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hreg x), ← Finset.sum_div,
    kmix_excess s k hk'.1 hk'.2]
  rfl

/-! ## 5. Prefix counts, component by component -/

theorem pcc_eq (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (hk : k ≤ 2 * s + 3) (w : ℝ) :
    prefixClassCount (gFamily (2 * s + 3)) (kperm s hs) (kq s) k w
      = ∑ x, kq s x * cnt (kwt s x) w k := by
  unfold prefixClassCount
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  simp only [kperm_apply]
  exact sum_prefix_fin k hk (fun j => if kwt s x j = w then (1 : ℝ) else 0)

theorem cnt_spB_below (s t : ℕ) (k : ℕ) (hk : k ≤ 2 * s + 2) (w : ℝ) :
    cnt (spB (2 * s + 3) t) w k = countIns t (-w) k := by
  unfold cnt countIns
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  unfold spB
  rw [if_neg (show i ≠ 2 * s + 3 - 1 by omega)]
  by_cases h : insWeight t i = -w
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (fun h' => h (by linarith))]

theorem cnt_r3W_below (s k : ℕ) (hk : k ≤ 2 * s + 1) (w : ℝ) :
    cnt (r3W (2 * s + 3)) w k = countIns (2 * s + 1) w k := by
  unfold cnt countIns
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  unfold r3W
  rw [if_neg (show i ≠ 2 * s + 3 - 2 by omega), if_neg (show i ≠ 2 * s + 3 - 1 by omega),
    show 2 * s + 3 - 2 = 2 * s + 1 from by omega]

theorem cnt_r3W_last (s : ℕ) (w : ℝ) :
    cnt (r3W (2 * s + 3)) w (2 * s + 2)
      = countIns (2 * s + 1) w (2 * s + 1) + (if (-3 : ℝ) = w then 1 else 0) := by
  rw [show cnt (r3W (2 * s + 3)) w (2 * s + 2)
      = cnt (r3W (2 * s + 3)) w (2 * s + 1)
        + (if r3W (2 * s + 3) (2 * s + 1) = w then (1 : ℝ) else 0) from Finset.sum_range_succ _ _,
    cnt_r3W_below s (2 * s + 1) le_rfl w]
  unfold r3W
  rw [if_pos (show 2 * s + 1 = 2 * s + 3 - 2 by omega)]

theorem cnt_r1W_below (s k : ℕ) (hk : k ≤ 2 * s + 1) (w : ℝ) :
    cnt (r1W (2 * s + 3)) w k = countIns 0 w k := by
  unfold cnt countIns
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  unfold r1W
  rw [if_neg (show i ≠ 2 * s + 3 - 2 by omega), if_neg (show i ≠ 2 * s + 3 - 1 by omega)]

theorem cnt_r1W_last (s : ℕ) (w : ℝ) :
    cnt (r1W (2 * s + 3)) w (2 * s + 2)
      = countIns 0 w (2 * s + 1) + (if (-1 : ℝ) = w then 1 else 0) := by
  rw [show cnt (r1W (2 * s + 3)) w (2 * s + 2)
      = cnt (r1W (2 * s + 3)) w (2 * s + 1)
        + (if r1W (2 * s + 3) (2 * s + 1) = w then (1 : ℝ) else 0) from Finset.sum_range_succ _ _,
    cnt_r1W_below s (2 * s + 1) le_rfl w]
  unfold r1W
  rw [if_pos (show 2 * s + 1 = 2 * s + 3 - 2 by omega)]

/-- **The mixture's prefix count**, split into the symmetrised slot part and the three
singles. -/
theorem pcc_split (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (hk : k ≤ 2 * s + 2) (w : ℝ) :
    prefixClassCount (gFamily (2 * s + 3)) (kperm s hs) (kq s) k w
      = uM s * (∑ t : Fin (2 * s + 1), alpha s t / 2 * (countIns t w k + countIns t (-w) k)
        + mR s * (mR s - 1) * countIns (2 * s + 1) w k
        + 2 * cnt (r3W (2 * s + 3)) w k + (mR s - 3) * cnt (r1W (2 * s + 3)) w k) := by
  rw [pcc_eq s hs k (by omega) w, sum_KIdx]
  have hslot : ∀ t : Fin (2 * s + 1),
      kq s (Sum.inl (t, false)) * cnt (kwt s (Sum.inl (t, false))) w k
        + kq s (Sum.inl (t, true)) * cnt (kwt s (Sum.inl (t, true))) w k
      = uM s * (alpha s t / 2 * (countIns t w k + countIns t (-w) k)) := by
    intro t
    show alpha s t / 2 * uM s * cnt (insWeight t) w k
      + alpha s t / 2 * uM s * cnt (spB (2 * s + 3) t) w k = _
    rw [cnt_insWeight, cnt_spB_below s t k hk w]
    ring
  rw [Finset.sum_congr rfl (fun t _ => hslot t), ← Finset.mul_sum]
  show _ + (kq s (Sum.inr 0) * cnt (kwt s (Sum.inr 0)) w k
      + kq s (Sum.inr 1) * cnt (kwt s (Sum.inr 1)) w k
      + kq s (Sum.inr 2) * cnt (kwt s (Sum.inr 2)) w k) = _
  simp only [kwt_inr]
  show _ + ((if (0 : Fin 3).val = 0 then mR s * (mR s - 1) * uM s
      else if (0 : Fin 3).val = 1 then 2 * uM s else (mR s - 3) * uM s) * _
    + (if (1 : Fin 3).val = 0 then mR s * (mR s - 1) * uM s
      else if (1 : Fin 3).val = 1 then 2 * uM s else (mR s - 3) * uM s) * _
    + (if (2 : Fin 3).val = 0 then mR s * (mR s - 1) * uM s
      else if (2 : Fin 3).val = 1 then 2 * uM s else (mR s - 3) * uM s) * _) = _
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, if_true, if_false,
    show (1 : ℕ) ≠ 0 from by omega, show (2 : ℕ) ≠ 0 from by omega,
    show (2 : ℕ) ≠ 1 from by omega, cnt_insWeight]
  ring

end CIGAMF.P13.PaperCOddKinkLaw

#print axioms CIGAMF.P13.PaperCOddKinkLaw.kq_sum
#print axioms CIGAMF.P13.PaperCOddKinkLaw.kex_eq
#print axioms CIGAMF.P13.PaperCOddKinkLaw.kvalue
#print axioms CIGAMF.P13.PaperCOddKinkLaw.pcc_split
