import «LeanPaperCOddKinkBandV1»

/-!
# Paper C: the whole odd frontier

For every odd `m >= 3` and every `eta >= 0`,

    V_m(eta) = max { (m+3-(m+1) eta) / (m(m+4)),  V_free + max(0, 1-eta) / (m(m+4)) }.

* Lower side: the first line is `relaxed_value_odd`, the second `odd_line2_value`.
* Upper side: three laws and convexity.  The zero-band law (value `(m+3)/(m(m+4))` at
  `eta = 0`, `odd_allPerm_witness`), the kink law (value `L1(eta_t) = L2(eta_t)` at the
  crossing point `eta_t = 1 - 2/(m(m-1))`), and the insertion law (value `V_free` at
  `eta = 1`, `odd_endpoint_law`).  Blending the first two covers `[0, eta_t]` along `L1`,
  blending the last two covers `[eta_t, 1]` along `L2`, and past `1` the value is the free
  value (`odd_breakpoint`).

The kink law is `LeanPaperCOddKinkLawV1`/`LeanPaperCOddKinkBandV1` for `m >= 7`; for
`m = 3` and `m = 5` it is an explicit finite law, checked here by computation.
-/

namespace CIGAMF.P13.PaperCOddFrontier

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCPerm
open CIGAMF.P13.PaperCRelabelBandJoin CIGAMF.P13.PaperCFam13
open CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCOddBreakpointEndgame
open CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCRelaxedJoin CIGAMF.P13.PaperCOddKink
open CIGAMF.P13.PaperCOddKinkLaw CIGAMF.P13.PaperCOddKinkBand CIGAMF.P13.PaperCOddWitnessJoin

/-! ## 1. From finite data to a law on all permutations -/

theorem rearr_gen (m : ℕ) (hm : 3 ≤ m) (f : ℕ → ℝ) (h : ∀ w, cnt f w m = tcount m w) :
    ∀ w : ℝ, Fintype.card {i : Fin m // (fun i : Fin m => f (i : ℕ)) i = w}
      = Fintype.card {j : Fin m // gFamily m j = w} := by
  intro w
  have h1 : ((Fintype.card {i : Fin m // f (i : ℕ) = w} : ℕ) : ℝ) = tcount m w :=
    (card_eq_count f m w).trans (h w)
  exact_mod_cast h1.trans (card_gFamily_fibre m hm w).symm

/-- **A law from finite data.**  Rankings given as weight sequences with the family's
counts, a probability vector, the class counts inside the band at every interior budget,
and the per-budget value: then an actual law on all permutations of `g_m` is feasible at
`eta` and has objective at most `V`. -/
theorem law_of_data (m : ℕ) (hm : 3 ≤ m) {R : Type*} [Fintype R] (f : R → ℕ → ℝ)
    (q : R → ℝ) (η V : ℝ) (hη : 0 ≤ η)
    (hcnt : ∀ x w, cnt (f x) w m = tcount m w)
    (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (hband : ∀ k, 1 ≤ k → k ≤ m - 1 → ∀ w : ℝ, (w = -3 ∨ w = -1 ∨ w = 1 ∨ w = 3) →
      0 < tcount m w →
      |∑ x, q x * cnt (f x) w k - tcount m w * ((k : ℝ) / (m : ℝ))|
        ≤ tcount m w * (η / (m : ℝ)))
    (hval : ∀ k ∈ budgets m,
      ∑ x, q x * (excess (fun i : Fin m => f x i) k / denom m) ≤ V) :
    ∃ P ∈ FeasibleAt (id : Perm m → _) η, objective m (by omega) P ≤ V := by
  classical
  let perm : R → Equiv.Perm (Fin m) := fun x =>
    permOfCountEq (fun i : Fin m => f x i) (gFamily m) (rearr_gen m hm (f x) (hcnt x))
  have hperm : ∀ x p, gFamily m (perm x p) = f x p := fun x p => permOfCountEq_apply _ _ _ p
  have hrank : ∀ x, rankOf (gFamily m) (perm x) = fun i : Fin m => f x i :=
    fun x => rankOf_permOfCountEq _ _ _
  have hpcc : ∀ k, k ≤ m → ∀ w, prefixClassCount (gFamily m) perm q k w
      = ∑ x, q x * cnt (f x) w k := by
    intro k hk w
    unfold prefixClassCount
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    simp only [hperm]
    exact sum_prefix_fin k hk (fun j => if f x j = w then (1 : ℝ) else 0)
  have hcounts : ∀ k, k ≤ m → ∀ i : Fin m,
      |prefixClassCount (gFamily m) perm q k (gFamily m i)
          / ((weightClass (gFamily m) (gFamily m i)).card : ℝ) - (k : ℝ) / (m : ℝ)|
        ≤ η / (m : ℝ) := by
    refine hcounts_of (by omega) (gFamily m) perm q η hη
      (fun w k => prefixClassCount (gFamily m) perm q k w) (fun k _ w => rfl) ?_ ?_ ?_
    · intro w
      rw [hpcc 0 (by omega) w]
      simp [cnt]
    · intro i
      rw [hpcc m le_rfl, card_weightClass m hm]
      simp only [hcnt]
      rw [← Finset.sum_mul, hq1, one_mul]
    · intro k hk1 hk i
      rw [hpcc k (by omega), card_weightClass m hm]
      have hpos : 0 < tcount m (gFamily m i) := by
        have : 0 < (weightClass (gFamily m) (gFamily m i)).card :=
          Finset.card_pos.mpr ⟨i, by simp [weightClass]⟩
        rw [← card_weightClass m hm]; exact_mod_cast this
      exact ratio_band _ _ _ _ _ hpos
        (hband k hk1 hk (gFamily m i) (gFamily_weights m i) hpos)
  have hvalue : ∀ k ∈ budgets m,
      (∑ x, q x * regret (gFamily m) (perm x) (denom m) k) ≤ V := by
    intro k hk
    have := hval k hk
    unfold regret
    simp only [hrank]
    exact this
  exact actual_banded_witness_of_counts (gFamily m) perm q η (denom m) V (budgets m)
    (budgets_nonempty m (by omega)) hq hq1 hcounts hvalue

/-! ## 2. The kink law, for `m >= 7` -/

theorem etaT_nonneg (s : ℕ) : 0 ≤ etaT s := by
  unfold etaT
  have hm := mR_pos s
  rw [sub_nonneg, div_le_one (by nlinarith)]
  nlinarith

theorem kink_law (s : ℕ) (hs : 2 ≤ s) :
    ∃ P ∈ FeasibleAt (id : Perm (2 * s + 3) → _) (etaT s),
      objective (2 * s + 3) (by omega) P ≤ vstar s := by
  have hcast : ((2 * s + 3 : ℕ) : ℝ) = mR s := by unfold mR; push_cast; ring
  refine law_of_data (2 * s + 3) (by omega) (kwt s) (kq s) (etaT s) (vstar s) (etaT_nonneg s)
    (kwt_cnt s (by omega)) (kq_nonneg s) (kq_sum s) ?_ ?_
  · intro k hk1 hk w hw _
    have hk' : k ≤ 2 * s + 2 := by omega
    rw [hcast, ← pcc_eq s (by omega) k (by omega) w]
    rcases hw with h | h | h | h <;> subst h
    · rw [tcount_neg_three]; exact band_neg_three s (by omega) k hk1 hk'
    · rw [tcount_neg_one, show (2 * s + 3 - 1) / 2 = s + 1 from by omega]
      push_cast
      exact band_neg_one s hs k hk1 hk'
    · rw [tcount_one, show 2 * s + 3 - 2 - (2 * s + 3 - 1) / 2 = s from by omega]
      exact band_one s hs k hk1 hk'
    · rw [tcount_three]; exact band_three s (by omega) k hk1 hk'
  · intro k hk
    have hk' : 1 ≤ k ∧ k ≤ 2 * s + 2 := by simp [budgets] at hk; omega
    apply le_of_eq
    rw [Finset.sum_congr rfl (fun x _ => by rw [kex_eq s (by omega) x k hk'.1 hk'.2])]
    rw [show (∑ x, kq s x * (kex s x k / denom (2 * s + 3)))
        = (∑ x, kq s x * kex s x k) / denom (2 * s + 3) from by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun x _ => by ring),
      kmix_excess s k hk'.1 hk'.2]
    rfl

/-! ## 3. The kink laws at `m = 3` and `m = 5`, by computation -/

theorem cnt_of_four (m : ℕ) (f : ℕ → ℝ)
    (hf : ∀ i, i < m → f i = -3 ∨ f i = -1 ∨ f i = 1 ∨ f i = 3)
    (h3 : cnt f 3 m = tcount m 3) (hn3 : cnt f (-3) m = tcount m (-3))
    (h1 : cnt f 1 m = tcount m 1) (hn1 : cnt f (-1) m = tcount m (-1)) :
    ∀ w, cnt f w m = tcount m w := by
  intro w
  by_cases a : w = 3; · subst a; exact h3
  by_cases b : w = -3; · subst b; exact hn3
  by_cases c : w = 1; · subst c; exact h1
  by_cases d : w = -1; · subst d; exact hn1
  rw [tcount_other m w a b c d]
  unfold cnt
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have := hf i (Finset.mem_range.mp hi)
  rw [if_neg]
  rcases this with h | h | h | h <;> rw [h] <;> intro e
  · exact b e.symm
  · exact d e.symm
  · exact c e.symm
  · exact a e.symm

theorem prefixSum_range {m : ℕ} (f : ℕ → ℝ) (k : ℕ) (hk : k ≤ m) :
    prefixSum (fun i : Fin m => f i) k = ∑ j ∈ range k, f j :=
  sum_prefix_fin k hk f

theorem prefixSum_list (L : List ℝ) (m k : ℕ) (hk : k ≤ m) :
    prefixSum (fun i : Fin m => L.getD (i : ℕ) 0) k = ∑ j ∈ range k, L.getD j 0 :=
  sum_prefix_fin k hk (fun j => L.getD j 0)

/-- The `m = 3` kink law: four rankings, tabulated on `ℕ`. -/
def T3 : ℕ → List ℝ
  | 0 => [-3, 3, -1]
  | 1 => [-1, -3, 3]
  | 2 => [-1, 3, -3]
  | _ => [3, -3, -1]

noncomputable def Q3 : ℕ → ℝ
  | 0 => 1 / 9
  | 1 => 1 / 9
  | 2 => 1 / 3
  | _ => 4 / 9

noncomputable def f3 (x : Fin 4) (i : ℕ) : ℝ := (T3 x.val).getD i 0

noncomputable def q3 (x : Fin 4) : ℝ := Q3 x.val

theorem sum_fin4 (G : ℕ → ℝ) : ∑ x : Fin 4, G x.val = G 0 + G 1 + G 2 + G 3 := by
  rw [Fin.sum_univ_eq_sum_range G 4]; simp [Finset.sum_range_succ]

theorem sum_fin8 (G : ℕ → ℝ) :
    ∑ x : Fin 8, G x.val = G 0 + G 1 + G 2 + G 3 + G 4 + G 5 + G 6 + G 7 := by
  rw [Fin.sum_univ_eq_sum_range G 8]; simp [Finset.sum_range_succ]

theorem kink_law_three :
    ∃ P ∈ FeasibleAt (id : Perm 3 → _) (etaT 0), objective 3 (by omega) P ≤ vstar 0 := by
  have hη : etaT 0 = 2 / 3 := by unfold etaT mR; norm_num
  have hv : vstar 0 = 10 / 63 := by unfold vstar uM mR denom; norm_num
  rw [hη, hv]
  refine law_of_data 3 le_rfl f3 q3 (2 / 3) (10 / 63) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · intro x
    apply cnt_of_four
    · intro i hi
      have hx := x.isLt
      interval_cases i <;> interval_cases hv' : x.val <;> simp [f3, T3, hv'] <;> norm_num
    all_goals
      have hx := x.isLt
      interval_cases hv' : x.val <;>
        simp only [cnt, Finset.sum_range_succ, Finset.sum_range_zero, f3, T3, hv'] <;>
        norm_num [tcount]
  · intro x
    have hx := x.isLt
    unfold q3
    interval_cases x.val <;> norm_num [Q3]
  · rw [show (∑ x : Fin 4, q3 x) = ∑ x : Fin 4, Q3 x.val from rfl, sum_fin4]; norm_num [Q3]
  · intro k hk1 hk w hw hpos
    rw [show (∑ x : Fin 4, q3 x * cnt (f3 x) w k)
        = ∑ x : Fin 4, (fun n => Q3 n * cnt (fun i => (T3 n).getD i 0) w k) x.val from rfl,
      sum_fin4 (fun n => Q3 n * cnt (fun i => (T3 n).getD i 0) w k)]
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
      (try (exfalso; norm_num [tcount] at hpos; done)) <;>
      simp only [cnt, Finset.sum_range_succ, Finset.sum_range_zero, T3, Q3, tcount] <;>
      norm_num [abs_le]
  · intro k hk
    have hk' : k = 1 ∨ k = 2 := by simp [budgets] at hk; omega
    rw [show (∑ x : Fin 4, q3 x * (excess (fun i : Fin 3 => f3 x i) k / denom 3))
        = ∑ x : Fin 4, (fun n => Q3 n * (excess (fun i : Fin 3 => (T3 n).getD (i : ℕ) 0) k
            / denom 3)) x.val from rfl,
      sum_fin4 (fun n => Q3 n * (excess (fun i : Fin 3 => (T3 n).getD (i : ℕ) 0) k
            / denom 3))]
    rcases hk' with rfl | rfl <;>
      simp only [excess, prefixSum_list _ 3 1 (by norm_num), prefixSum_list _ 3 2 (by norm_num)] <;>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, T3, Q3] <;> norm_num [denom]

/-- The `m = 5` kink law: eight rankings, masses from an exact rational certificate. -/
def T5 : ℕ → List ℝ
  | 0 => [-3, 3, 1, -1, -1]
  | 1 => [-1, 1, -1, 3, -3]
  | 2 => [-1, 3, -3, -1, 1]
  | 3 => [-1, 3, -3, 1, -1]
  | 4 => [1, -1, -1, -3, 3]
  | 5 => [1, -1, -1, 3, -3]
  | 6 => [1, -1, 3, -3, -1]
  | _ => [3, -3, 1, -1, -1]

noncomputable def Q5 : ℕ → ℝ
  | 0 => 1 / 50
  | 1 => 1 / 10
  | 2 => 1 / 50
  | 3 => 6 / 25
  | 4 => 1 / 50
  | 5 => 1 / 10
  | 6 => 13 / 50
  | _ => 6 / 25

noncomputable def f5 (x : Fin 8) (i : ℕ) : ℝ := (T5 x.val).getD i 0

noncomputable def q5 (x : Fin 8) : ℝ := Q5 x.val

theorem cnt5 (x : Fin 8) : ∀ w, cnt (f5 x) w 5 = tcount 5 w := by
  apply cnt_of_four
  · intro i hi
    have hx := x.isLt
    interval_cases i <;> interval_cases hv' : x.val <;> simp [f5, T5, hv'] <;> norm_num
  all_goals
    have hx := x.isLt
    interval_cases hv' : x.val <;>
      simp only [cnt, Finset.sum_range_succ, Finset.sum_range_zero, f5, T5, hv'] <;>
      norm_num [tcount]

set_option maxHeartbeats 4000000 in
theorem band5 (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 5 - 1) (w : ℝ)
    (hw : w = -3 ∨ w = -1 ∨ w = 1 ∨ w = 3) (hpos : 0 < tcount 5 w) :
    |∑ x, q5 x * cnt (f5 x) w k - tcount 5 w * ((k : ℝ) / ((5 : ℕ) : ℝ))|
      ≤ tcount 5 w * ((9 / 10 : ℝ) / ((5 : ℕ) : ℝ)) := by
  rw [show (∑ x : Fin 8, q5 x * cnt (f5 x) w k)
      = ∑ x : Fin 8, (fun n => Q5 n * cnt (fun i => (T5 n).getD i 0) w k) x.val from rfl,
      sum_fin8 (fun n => Q5 n * cnt (fun i => (T5 n).getD i 0) w k)]
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk' with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [cnt, Finset.sum_range_succ, Finset.sum_range_zero, T5, Q5, tcount] <;>
    norm_num [abs_le]

set_option maxHeartbeats 4000000 in
theorem value5 : ∀ k ∈ budgets 5,
    ∑ x, q5 x * (excess (fun i : Fin 5 => f5 x i) k / denom 5) ≤ 13 / 225 := by
  intro k hk
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by simp [budgets] at hk; omega
  rw [show (∑ x : Fin 8, q5 x * (excess (fun i : Fin 5 => f5 x i) k / denom 5))
      = ∑ x : Fin 8, (fun n => Q5 n * (excess (fun i : Fin 5 => (T5 n).getD (i : ℕ) 0) k
          / denom 5)) x.val from rfl,
      sum_fin8 (fun n => Q5 n * (excess (fun i : Fin 5 => (T5 n).getD (i : ℕ) 0) k
          / denom 5))]
  rcases hk' with rfl | rfl | rfl | rfl <;>
    simp only [excess, prefixSum_list _ 5 1 (by norm_num), prefixSum_list _ 5 2 (by norm_num),
      prefixSum_list _ 5 3 (by norm_num), prefixSum_list _ 5 4 (by norm_num)] <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, T5, Q5] <;> norm_num [denom]

theorem kink_law_five :
    ∃ P ∈ FeasibleAt (id : Perm 5 → _) (etaT 1), objective 5 (by omega) P ≤ vstar 1 := by
  have hη : etaT 1 = 9 / 10 := by unfold etaT mR; norm_num
  have hv : vstar 1 = 13 / 225 := by unfold vstar uM mR denom; norm_num
  rw [hη, hv]
  refine law_of_data 5 (by norm_num) f5 q5 (9 / 10) (13 / 225) (by norm_num) cnt5 ?_ ?_
    (fun k hk1 hk w hw hpos => band5 k hk1 hk w hw hpos) value5
  · intro x
    have hx := x.isLt
    unfold q5
    interval_cases x.val <;> norm_num [Q5]
  · rw [show (∑ x : Fin 8, q5 x) = ∑ x : Fin 8, Q5 x.val from rfl, sum_fin8]; norm_num [Q5]

/-! ## 4. The frontier -/

theorem kink_all (s : ℕ) :
    ∃ P ∈ FeasibleAt (id : Perm (2 * s + 3) → _) (etaT s),
      objective (2 * s + 3) (by omega) P ≤ vstar s := by
  rcases s with _ | _ | s
  · exact kink_law_three
  · exact kink_law_five
  · exact kink_law (s + 2) (by omega)

/-- The two lines, at `m = 2s+3`. -/
noncomputable def line1 (s : ℕ) (η : ℝ) : ℝ :=
  (((2 * s + 3 : ℕ) : ℝ) + 3 - (((2 * s + 3 : ℕ) : ℝ) + 1) * η)
    / (((2 * s + 3 : ℕ) : ℝ) * (((2 * s + 3 : ℕ) : ℝ) + 4))

noncomputable def line2 (s : ℕ) (η : ℝ) : ℝ :=
  freeValue (2 * s + 3) + (1 - η) / (((2 * s + 3 : ℕ) : ℝ) * denom (2 * s + 3))

theorem cast_mR (s : ℕ) : ((2 * s + 3 : ℕ) : ℝ) = mR s := by unfold mR; push_cast; ring

theorem vstar_line1 (s : ℕ) : vstar s = line1 s (etaT s) := by
  unfold vstar line1 etaT uM denom
  rw [cast_mR]
  have hm := mR_pos s
  have h0 : mR s ≠ 0 := by linarith
  have h1 : mR s - 1 ≠ 0 := by linarith
  have h4 : mR s + 4 ≠ 0 := by linarith
  field_simp
  try ring

theorem vstar_line2 (s : ℕ) : vstar s = line2 s (etaT s) := by
  unfold vstar line2 etaT uM freeValue denom
  rw [cast_mR]
  have hm := mR_pos s
  have h0 : mR s ≠ 0 := by linarith
  have h1 : mR s - 1 ≠ 0 := by linarith
  have h4 : mR s + 4 ≠ 0 := by linarith
  field_simp
  try ring

theorem etaT_lt_one (s : ℕ) : etaT s < 1 := by
  unfold etaT
  have hm := mR_pos s
  have : 0 < 2 / (mR s * (mR s - 1)) := by apply div_pos (by norm_num); nlinarith
  linarith

theorem etaT_pos (s : ℕ) : 0 < etaT s := by
  unfold etaT
  have hm := mR_pos s
  rw [sub_pos, div_lt_one (by nlinarith)]
  nlinarith

/-- **The whole odd frontier.**  For every odd `m = 2s+3` and every `eta >= 0`,
`V_m(eta) = max(L1(eta), V_free + max(0, 1-eta)/(m(m+4)))`. -/
theorem odd_frontier_s (s : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    value (2 * s + 3) (by omega) η
      = max (line1 s η)
          (freeValue (2 * s + 3) + max 0 (1 - η) / (((2 * s + 3 : ℕ) : ℝ) * denom (2 * s + 3))) := by
  have hm3 : 3 ≤ 2 * s + 3 := by omega
  have hmo : (2 * s + 3) % 2 = 1 := by omega
  have hl1 : line1 s η ≤ value (2 * s + 3) (by omega) η := relaxed_value s η hη
  rcases le_or_gt 1 η with h1 | h1
  · -- past the breakpoint the value is the free value
    have hfree : value (2 * s + 3) (by omega) η = freeValue (2 * s + 3) :=
      (odd_breakpoint (2 * s + 3) hm3 hmo η hη).mpr h1
    rw [max_eq_left (by linarith : 1 - η ≤ 0), zero_div, add_zero]
    rw [hfree] at hl1 ⊢
    exact (max_eq_right hl1).symm
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 - η)]
    have hl2 : line2 s η ≤ value (2 * s + 3) (by omega) η := odd_line2_value s η hη
    apply le_antisymm
    · obtain ⟨K, hKf, hKv⟩ := kink_all s
      have ht := etaT_pos s
      have ht1 := etaT_lt_one s
      rcases le_or_gt η (etaT s) with h2 | h2
      · -- [0, eta_t]: blend the zero-band law with the kink law
        obtain ⟨P0, hP0f, hP0v⟩ := odd_allPerm_witness s (budgets (2 * s + 3))
          (budgets_nonempty _ (by omega)) (fun k hk => by simp [budgets] at hk; omega)
          (by simp [budgets]; try omega)
        let t := η / etaT s
        have htn : 0 ≤ t := div_nonneg hη ht.le
        have ht1' : t ≤ 1 := (div_le_one ht).2 h2
        have hfeas : blend t P0 K ∈ FeasibleAt (id : Perm (2 * s + 3) → _) η := by
          have h := blend_feasible P0 K 0 (etaT s) t hP0f hKf htn ht1'
          have heq : (1 - t) * 0 + t * etaT s = η := by
            simp only [t]; field_simp; try ring
          rwa [heq] at h
        have hobj0 : objective (2 * s + 3) (by omega) P0
            = (((2 * s + 3 : ℕ) : ℝ) + 3) / (((2 * s + 3 : ℕ) : ℝ) * (((2 * s + 3 : ℕ) : ℝ) + 4)) :=
          hP0v
        calc value (2 * s + 3) (by omega) η
            ≤ objective (2 * s + 3) (by omega) (blend t P0 K) :=
              value_le_witness (2 * s + 3) hm3 η _ hfeas
          _ ≤ (1 - t) * objective (2 * s + 3) (by omega) P0
                + t * objective (2 * s + 3) (by omega) K :=
              objective_blend_le (by omega) _ _ t htn ht1'
          _ ≤ (1 - t) * line1 s 0 + t * line1 s (etaT s) := by
              rw [hobj0, ← vstar_line1]
              have e0 : line1 s 0 = (((2 * s + 3 : ℕ) : ℝ) + 3)
                  / (((2 * s + 3 : ℕ) : ℝ) * (((2 * s + 3 : ℕ) : ℝ) + 4)) := by
                unfold line1; ring_nf
              rw [e0]
              have := mul_le_mul_of_nonneg_left hKv htn
              linarith
          _ = line1 s η := by
              have hteq : t * etaT s = η := by simp only [t]; field_simp
              unfold line1
              rw [← hteq]
              ring
          _ ≤ _ := le_max_left _ _
      · -- [eta_t, 1]: blend the kink law with the insertion law
        obtain ⟨I, hIf, hIv⟩ := odd_endpoint_law (2 * s + 3) hm3 hmo
        let t := (η - etaT s) / (1 - etaT s)
        have hd : 0 < 1 - etaT s := by linarith
        have htn : 0 ≤ t := div_nonneg (by linarith) hd.le
        have ht1' : t ≤ 1 := (div_le_one hd).2 (by linarith)
        have hfeas : blend t K I ∈ FeasibleAt (id : Perm (2 * s + 3) → _) η := by
          have h := blend_feasible K I (etaT s) 1 t hKf hIf htn ht1'
          have heq : (1 - t) * etaT s + t * 1 = η := by
            simp only [t]; field_simp; ring
          rwa [heq] at h
        calc value (2 * s + 3) (by omega) η
            ≤ objective (2 * s + 3) (by omega) (blend t K I) :=
              value_le_witness (2 * s + 3) hm3 η _ hfeas
          _ ≤ (1 - t) * objective (2 * s + 3) (by omega) K
                + t * objective (2 * s + 3) (by omega) I :=
              objective_blend_le (by omega) _ _ t htn ht1'
          _ ≤ (1 - t) * line2 s (etaT s) + t * freeValue (2 * s + 3) := by
              rw [← vstar_line2]
              have hA := mul_le_mul_of_nonneg_left hKv (by linarith : (0 : ℝ) ≤ 1 - t)
              have hB := mul_le_mul_of_nonneg_left hIv htn
              linarith
          _ = line2 s η := by
              have hteq : t * (1 - etaT s) = η - etaT s := by simp only [t]; field_simp
              have key : (1 - t) * (1 - etaT s) = 1 - η := by rw [sub_mul, one_mul, hteq]; ring
              unfold line2
              rw [← key]
              ring
          _ ≤ _ := le_max_right _ _
    · exact max_le hl1 hl2

/-- **The whole odd frontier, at any odd `m >= 3`.** -/
theorem odd_frontier (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (η : ℝ) (hη : 0 ≤ η) :
    value m (by omega) η
      = max (((m : ℝ) + 3 - ((m : ℝ) + 1) * η) / ((m : ℝ) * ((m : ℝ) + 4)))
          (freeValue m + max 0 (1 - η) / ((m : ℝ) * denom m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 3 := ⟨(m - 3) / 2, by omega⟩
  exact odd_frontier_s s η hη

/-- **The value at the kink**: `V_m(eta_t) = 2(m^2+1)/(m^2 (m-1)(m+4))`. -/
theorem odd_kink_value (s : ℕ) : value (2 * s + 3) (by omega) (etaT s) = vstar s := by
  rw [odd_frontier_s s (etaT s) (etaT_pos s).le,
    max_eq_right (by linarith [etaT_lt_one s] : (0 : ℝ) ≤ 1 - etaT s)]
  have h2 := vstar_line2 s
  unfold line2 at h2
  rw [← h2, ← vstar_line1 s, max_self]

end CIGAMF.P13.PaperCOddFrontier

#print axioms CIGAMF.P13.PaperCOddFrontier.law_of_data
#print axioms CIGAMF.P13.PaperCOddFrontier.kink_law
#print axioms CIGAMF.P13.PaperCOddFrontier.kink_all
#print axioms CIGAMF.P13.PaperCOddFrontier.odd_frontier_s
#print axioms CIGAMF.P13.PaperCOddFrontier.odd_frontier
#print axioms CIGAMF.P13.PaperCOddFrontier.odd_kink_value
