import «LeanPaperCBudgetExchangeV1»

/-!
# Paper C: one exchange reaches the budget-aware value of `g_m` for odd `m`

`m = 2h+3`, `h ≥ 1`. Headline `recourse_one_odd`: for odd `m ≥ 5` and every `η ≥ 0`,
`V^{(1)}_{g_m}(η) = B_{g_m}(η)`.

**The committed law.** Write the odd family as the even pair pattern `E` on `2h+2` positions
(`insWeight (2s)`: the heavy pair `(+3,-3)` at the even slot `2s`, lights `-1` at even
positions; `s` uniform on `0..h`; a global sign flip `b`) plus one extra `-1`, the *single*,
inserted at a uniform position `p ∈ {0, …, m-1}`; relabel inside each weight class. Every
item is in every prefix with probability exactly `k/m` (`oddLaw_feasible`, band `0`).

**The plans.** Budgets `1` and `m-1` draw the final set independently from a near-optimal
subset law. At every middle budget the plan always edits a costly prefix by one exchange:
* the single is after the prefix and `k = 2s+1` (one heavy item in the prefix): drop the light
  at `E`-index `2s-1`, add the partner heavy at `E`-index `2s+1`;
* the single is in the prefix, `k` is even and the prefix is costly (`b = 0`, or `k = 2s+2`):
  drop the single, add the item at `E`-index `k-1`.
Every final set then has zero regret, and the final item marginals are within
`h(h+2)/(h+1)^2 = 1 - 1/(h+1)^2` of `k/m` (`oddT_band`), which is below
`η_t = 1 - 2/(m(m-1))`. For `η ≤ η_t` the claim is `recourse_eq_aware_odd`.
-/

namespace CIGAMF.P13.PaperCBudgetExchangeOdd

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCRelabel
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCBudgetAware
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCStabilityFamily
open CIGAMF.P13.PaperCBudgetSharp CIGAMF.P13.PaperCRelabelBandJoin CIGAMF.P13.PaperCBudgetExchange
open CIGAMF.P13.PaperCPerm
open CIGAMF.P13.PaperCBudgetSym (orbitCount_eq sym_avg subCost_map card_wperm_pos class_card_m3
  class_card_p3 class_card_m1 class_card_p1)

/-! ## 1. Positions around the single -/

/-- The `E`-index of the absolute position `i` when the single sits at `p`. -/
def eidx (p i : ℕ) : ℕ := if i < p then i else i - 1

/-- **Reindexing around the slot `p`.** -/
theorem sum_slot (n p : ℕ) (hp : p ≤ n) (c : ℝ) (F : ℕ → ℝ) :
    ∑ i ∈ range (n + 1), (if i = p then c else F (eidx p i)) = c + ∑ j ∈ range n, F j := by
  induction n with
  | zero =>
      have : p = 0 := by omega
      subst this; simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.lt_or_ge n p with hlt | hge
      · have hpn : p = n + 1 := by omega
        subst hpn
        rw [if_pos rfl]
        have e : ∀ i ∈ range (n + 1), (if i = n + 1 then c else F (eidx (n + 1) i)) = F i := by
          intro i hi
          rw [mem_range] at hi
          rw [if_neg (by omega)]
          unfold eidx
          rw [if_pos hi]
        rw [Finset.sum_congr rfl e]
        ring
      · rw [ih hge, if_neg (by omega), Finset.sum_range_succ]
        unfold eidx
        rw [if_neg (by omega), show n + 1 - 1 = n by omega]
        ring

/-- The even pattern, sign-flipped when `b`. -/
noncomputable def ePat (s : ℕ) (b : Bool) (j : ℕ) : ℝ := (if b then -1 else 1) * insWeight (2 * s) j

/-- The odd pattern: the single at `p`, the even pattern around it. -/
noncomputable def oddPat (h s : ℕ) (b : Bool) (p : ℕ) : Ranking (2 * h + 1 + 2) :=
  fun i => if i.val = p then -1 else ePat s b (eidx p i.val)

/-- Sums over `Fin m` of functions of the position, as reindexed sums. -/
theorem fin_sum_slot (h p : ℕ) (hp : p ≤ 2 * h + 2) (c : ℝ) (F : ℕ → ℝ)
    (G : Fin (2 * h + 1 + 2) → ℝ) (hG : ∀ i, G i = if i.val = p then c else F (eidx p i.val)) :
    ∑ i, G i = c + ∑ j ∈ range (2 * h + 2), F j := by
  rw [Finset.sum_congr rfl fun i _ => hG i]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = p then c else F (eidx p i)) (2 * h + 1 + 2)]
  exact sum_slot (2 * h + 2) p hp c F

theorem tcount_odd_even (h : ℕ) (w : ℝ) :
    tcount (2 * h + 1 + 2) w = (if (-1 : ℝ) = w then 1 else 0) + tcount (2 * h + 2) w := by
  unfold tcount
  rw [show (2 * h + 1 + 2 - 1) / 2 = h + 1 by omega,
    show 2 * h + 1 + 2 - 2 - (h + 1) = h by omega,
    show (2 * h + 2 - 1) / 2 = h by omega, show 2 * h + 2 - 2 - h = h by omega]
  by_cases h3 : w = 3
  · subst h3; norm_num
  by_cases h4 : w = -3
  · subst h4; norm_num
  by_cases h1 : w = -1
  · subst h1; norm_num; ring
  by_cases h2 : w = 1
  · subst h2; norm_num
  have h1' : ¬ (-1 : ℝ) = w := fun e => h1 e.symm
  simp [h3, h4, h1, h2, h1']

/-- Weight counts of the even pattern over a prefix of `E`-indices. -/
theorem ePat_count (s : ℕ) (b : Bool) (J : ℕ) (w : ℝ) :
    ∑ j ∈ range J, (if ePat s b j = w then (1 : ℝ) else 0)
      = if b then countIns (2 * s) (-w) J else countIns (2 * s) w J := by
  unfold countIns ePat
  cases b
  · simp
  · simp only [if_true]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    apply propext
    constructor <;> intro hj <;> linarith

theorem oddPat_count_real (h s : ℕ) (hh : 1 ≤ h) (hs : s ≤ h) (b : Bool) (p : ℕ) (hp : p ≤ 2 * h + 2) (w : ℝ) :
    ((Fintype.card {i : Fin (2 * h + 1 + 2) // oddPat h s b p i = w} : ℕ) : ℝ)
      = tcount (2 * h + 1 + 2) w := by
  rw [Fintype.card_subtype, Finset.natCast_card_filter]
  rw [fin_sum_slot h p hp (if (-1 : ℝ) = w then 1 else 0)
    (fun j => if ePat s b j = w then (1 : ℝ) else 0) _ (fun i => by
      unfold oddPat
      by_cases hi : i.val = p
      · simp [hi]
      · simp [hi])]
  rw [ePat_count, tcount_odd_even]
  congr 1
  have hc : ∀ w', countIns (2 * s) w' (2 * h + 2) = tcount (2 * h + 2) w' :=
    fun w' => countIns_full (2 * h + 2) (by omega) (2 * s) (by omega) w'
  cases b
  · simp only [Bool.false_eq_true, if_false]; exact hc w
  · simp only [if_true]; rw [hc, tcount_neg (2 * h + 2) (by omega)]

theorem oddPat_count (h s : ℕ) (hh : 1 ≤ h) (hs : s ≤ h) (b : Bool) (p : ℕ) (hp : p ≤ 2 * h + 2) :
    ∀ w : ℝ, Fintype.card {i : Fin (2 * h + 1 + 2) // oddPat h s b p i = w}
      = Fintype.card {j : Fin (2 * h + 1 + 2) // gFamily (2 * h + 1 + 2) j = w} := by
  intro w
  have h1 := oddPat_count_real h s hh hs b p hp w
  have h2 := card_gFamily_fibre (2 * h + 1 + 2) (by omega) w
  exact_mod_cast h1.trans h2.symm

/-! ## 2. The committed law -/

section Law

variable (h : ℕ)

/-- The base index: slot `s`, flip `b`, single position `p`. -/
abbrev OIdx := Fin (h + 1) × Bool × Fin (2 * h + 1 + 2)

/-- The ranking of a base index. -/
noncomputable def oddBase (hh : 1 ≤ h) (x : OIdx h) : Equiv.Perm (Fin (2 * h + 1 + 2)) :=
  permOfCountEq (oddPat h x.1.val x.2.1 x.2.2.val) (gFamily (2 * h + 1 + 2))
    (oddPat_count h x.1.val hh (by have := x.1.isLt; omega) x.2.1 x.2.2.val
      (by have := x.2.2.isLt; omega))

theorem oddBase_apply (hh : 1 ≤ h) (x : OIdx h) (i : Fin (2 * h + 1 + 2)) :
    gFamily (2 * h + 1 + 2) (oddBase h hh x i) = oddPat h x.1.val x.2.1 x.2.2.val i :=
  permOfCountEq_apply _ _ _ i

/-- Uniform weights. -/
noncomputable def oddQ : OIdx h → ℝ :=
  fun _ => 1 / (2 * ((h : ℝ) + 1) * (2 * (h : ℝ) + 3))

theorem oddQ_nonneg : ∀ x, 0 ≤ oddQ h x := fun _ => by unfold oddQ; positivity

/-- The committed law. -/
noncomputable def oddLaw (hh : 1 ≤ h) : Equiv.Perm (Fin (2 * h + 1 + 2)) → ℝ :=
  pushLaw (symPerm (gFamily (2 * h + 1 + 2)) (oddBase h hh))
    (symLaw (gFamily (2 * h + 1 + 2)) (oddQ h))

/-- Averages over the base index. -/
theorem odd_avg (F : OIdx h → ℝ) :
    ∑ x, oddQ h x * F x = (1 / (2 * ((h : ℝ) + 1) * (2 * (h : ℝ) + 3)))
      * ∑ s : Fin (h + 1), ∑ p : Fin (2 * h + 1 + 2), (F (s, false, p) + F (s, true, p)) := by
  unfold oddQ
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Sums over the single position split at the budget. -/
theorem sum_pos_split (h k : ℕ) (hk : k ≤ 2 * h + 1 + 2) (A B : ℝ) :
    ∑ p : Fin (2 * h + 1 + 2), (if p.val < k then A else B)
      = (k : ℝ) * A + ((2 * h + 1 + 2 - k : ℕ) : ℝ) * B := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h1 : (univ.filter (fun p : Fin (2 * h + 1 + 2) => p.val < k)).card = k :=
    card_filter_lt _ _ hk
  have h2 : (univ.filter (fun p : Fin (2 * h + 1 + 2) => ¬ p.val < k)).card = 2 * h + 1 + 2 - k := by
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin (2 * h + 1 + 2)))) (fun p : Fin (2 * h + 1 + 2) => p.val < k)
    rw [h1, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [h1, h2]


/-! ## 3. Positions as a single indicator and a set of `E`-indices -/

/-- Positions described by whether the single is in, and which `E`-indices are in. -/
def posSet (p : ℕ) (inS : Bool) (F : Finset ℕ) : Finset (Fin (2 * h + 1 + 2)) :=
  univ.filter (fun i => (i.val = p ∧ inS = true) ∨ (i.val ≠ p ∧ eidx p i.val ∈ F))

theorem posSet_sum (p : ℕ) (hp : p ≤ 2 * h + 2) (inS : Bool) (F : Finset ℕ) (c : ℝ)
    (H : ℕ → ℝ) (G : Fin (2 * h + 1 + 2) → ℝ)
    (hG : ∀ i, G i = if i.val = p then c else H (eidx p i.val)) :
    ∑ i ∈ posSet h p inS F, G i
      = (if inS then c else 0) + ∑ j ∈ range (2 * h + 2), (if j ∈ F then H j else 0) := by
  unfold posSet
  rw [Finset.sum_filter]
  exact fin_sum_slot h p hp _ _ _ (fun i => by
    rw [hG i]
    by_cases hi : i.val = p
    · simp [hi]
    · simp [hi])

theorem filter_lt_posSet (p k : ℕ) :
    univ.filter (fun i : Fin (2 * h + 1 + 2) => i.val < k)
      = posSet h p (decide (p < k)) (range (if p < k then k - 1 else k)) := by
  ext i
  simp only [posSet, mem_filter, mem_univ, true_and, mem_range, decide_eq_true_eq]
  unfold eidx
  constructor
  · intro hi
    by_cases hip : i.val = p
    · exact Or.inl ⟨hip, by omega⟩
    · refine Or.inr ⟨hip, ?_⟩
      split_ifs <;> omega
  · rintro (⟨hip, hpk⟩ | ⟨hip, hmem⟩)
    · omega
    · split_ifs at hmem <;> omega

theorem sum_ite_range_mem (N J : ℕ) (hJ : J ≤ N) (f : ℕ → ℝ) :
    ∑ j ∈ range N, (if j ∈ range J then f j else 0) = ∑ j ∈ range J, f j := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.range_mono hJ)]

/-- **Prefix weight counts of a base ranking.** -/
theorem prefix_count (hh : 1 ≤ h) (x : OIdx h) (k : ℕ) (hk : k ≤ 2 * h + 1 + 2) (w : ℝ) :
    ∑ i ∈ univ.filter (fun i : Fin (2 * h + 1 + 2) => i.val < k),
        (if gFamily (2 * h + 1 + 2) (oddBase h hh x i) = w then (1 : ℝ) else 0)
      = (if x.2.2.val < k then (if (-1 : ℝ) = w then 1 else 0) else 0)
        + (if x.2.1 then countIns (2 * x.1.val) (-w) (if x.2.2.val < k then k - 1 else k)
           else countIns (2 * x.1.val) w (if x.2.2.val < k then k - 1 else k)) := by
  have hp := x.2.2.isLt
  rw [filter_lt_posSet h x.2.2.val k]
  rw [posSet_sum h x.2.2.val (by omega) _ _ (if (-1 : ℝ) = w then 1 else 0)
    (fun j => if ePat x.1.val x.2.1 j = w then (1 : ℝ) else 0) _ (fun i => by
      rw [oddBase_apply]
      unfold oddPat
      by_cases hi : i.val = x.2.2.val
      · simp [hi]
      · simp [hi])]
  rw [sum_ite_range_mem _ _ (by split_ifs <;> omega), ePat_count]
  simp only [decide_eq_true_eq]

/-- **Prefix sums of a base ranking.** -/
theorem prefix_sum (hh : 1 ≤ h) (x : OIdx h) (k : ℕ) (hk : k ≤ 2 * h + 1 + 2) :
    ∑ i ∈ univ.filter (fun i : Fin (2 * h + 1 + 2) => i.val < k),
        gFamily (2 * h + 1 + 2) (oddBase h hh x i)
      = (if x.2.2.val < k then (-1 : ℝ) else 0)
        + (if x.2.1 then -1 else 1)
          * prefixSum (insRanking (2 * h + 2) (2 * x.1.val)) (if x.2.2.val < k then k - 1 else k) := by
  have hp := x.2.2.isLt
  have hJ : (if x.2.2.val < k then k - 1 else k) ≤ 2 * h + 2 := by split_ifs <;> omega
  rw [filter_lt_posSet h x.2.2.val k]
  rw [posSet_sum h x.2.2.val (by omega) _ _ (-1) (fun j => ePat x.1.val x.2.1 j) _ (fun i => by
      rw [oddBase_apply]; rfl)]
  rw [sum_ite_range_mem _ _ hJ]
  simp only [decide_eq_true_eq]
  congr 1
  unfold ePat
  rw [← Finset.mul_sum]
  congr 1
  unfold prefixSum insRanking
  exact (sum_filter_lt (2 * h + 2) _ hJ (fun i => insWeight (2 * x.1.val) i)).symm

/-! ## 4. The committed law is in the band `0` -/

theorem fs_heavy (s J : ℕ) (w : ℝ) (hw : w = 3 ∨ w = -3) :
    countIns (2 * s) w J + countIns (2 * s) (-w) J = heavyCnt s J := by
  unfold heavyCnt
  rcases hw with rfl | rfl
  · rw [countIns_heavy]
  · rw [neg_neg, add_comm, countIns_heavy]

theorem fs_light (s J : ℕ) (w : ℝ) (hw : w = 1 ∨ w = -1) :
    countIns (2 * s) w J + countIns (2 * s) (-w) J = (J : ℝ) - heavyCnt s J := by
  unfold heavyCnt
  rcases hw with rfl | rfl
  · rw [add_comm, countIns_light]
  · rw [neg_neg, countIns_light]

/-- Flip sums of the prefix counts. -/
theorem prefix_flip (hh : 1 ≤ h) (s : Fin (h + 1)) (p : Fin (2 * h + 1 + 2)) (k : ℕ)
    (hk : k ≤ 2 * h + 1 + 2) (w : ℝ) :
    (∑ i ∈ univ.filter (fun i : Fin (2 * h + 1 + 2) => i.val < k),
        (if gFamily (2 * h + 1 + 2) (oddBase h hh (s, false, p) i) = w then (1 : ℝ) else 0))
      + (∑ i ∈ univ.filter (fun i : Fin (2 * h + 1 + 2) => i.val < k),
        (if gFamily (2 * h + 1 + 2) (oddBase h hh (s, true, p) i) = w then (1 : ℝ) else 0))
      = if p.val < k then
          2 * (if (-1 : ℝ) = w then 1 else 0)
            + (countIns (2 * s.val) w (k - 1) + countIns (2 * s.val) (-w) (k - 1))
        else countIns (2 * s.val) w k + countIns (2 * s.val) (-w) k := by
  rw [prefix_count h hh _ k hk, prefix_count h hh _ k hk]
  simp only [Bool.false_eq_true, if_false, if_true]
  by_cases hpk : p.val < k
  · simp only [hpk, if_true]; ring
  · simp only [hpk, if_false]; ring

/-- Double sums over slots and single positions. -/
theorem double_sum (k : ℕ) (hk : k ≤ 2 * h + 1 + 2) (α : ℝ) (β γ : Fin (h + 1) → ℝ) :
    ∑ s : Fin (h + 1), ∑ p : Fin (2 * h + 1 + 2), (if p.val < k then α + β s else γ s)
      = (k : ℝ) * (((h : ℝ) + 1) * α + ∑ s, β s)
        + ((2 * h + 1 + 2 - k : ℕ) : ℝ) * ∑ s, γ s := by
  simp_rw [sum_pos_split h k hk]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem heavy_sum_sub (J : ℕ) (hJ : J ≤ 2 * h + 2) :
    ∑ s : Fin (h + 1), ((J : ℝ) - heavyCnt s.val J) = ((h : ℝ) + 1) * J - J := by
  rw [Finset.sum_sub_distrib, heavy_sum h J hJ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

theorem mk_heavy (k : ℕ) (hk : k ≤ 2 * h + 1 + 2) :
    ((2 * h + 1 + 2 - k : ℕ) : ℝ) * ∑ s : Fin (h + 1), heavyCnt s.val k
      = ((2 * h + 1 + 2 - k : ℕ) : ℝ) * k := by
  by_cases hk' : k ≤ 2 * h + 2
  · rw [heavy_sum h k hk']
  · rw [show 2 * h + 1 + 2 - k = 0 by omega]; simp

theorem mk_light (k : ℕ) (hk : k ≤ 2 * h + 1 + 2) :
    ((2 * h + 1 + 2 - k : ℕ) : ℝ) * ∑ s : Fin (h + 1), ((k : ℝ) - heavyCnt s.val k)
      = ((2 * h + 1 + 2 - k : ℕ) : ℝ) * (((h : ℝ) + 1) * k - k) := by
  by_cases hk' : k ≤ 2 * h + 2
  · rw [heavy_sum_sub h k hk']
  · rw [show 2 * h + 1 + 2 - k = 0 by omega]; simp

/-- **The class average of the prefix counts is exact.** -/
theorem prefix_avg (hh : 1 ≤ h) (k : ℕ) (hk : k ≤ 2 * h + 1 + 2) (w : ℝ)
    (hw : w = -3 ∨ w = -1 ∨ w = 1 ∨ w = 3) :
    ∑ x, oddQ h x * (∑ i ∈ univ.filter (fun i : Fin (2 * h + 1 + 2) => i.val < k),
        (if gFamily (2 * h + 1 + 2) (oddBase h hh x i) = w then (1 : ℝ) else 0))
      = ((univ.filter (fun j : Fin (2 * h + 1 + 2) => gFamily (2 * h + 1 + 2) j = w)).card : ℝ)
        * ((k : ℝ) / (2 * (h : ℝ) + 3)) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hmk : ((2 * h + 1 + 2 - k : ℕ) : ℝ) = 2 * (h : ℝ) + 3 - k := by
    rw [Nat.cast_sub hk]; push_cast; ring
  rw [odd_avg h]
  rcases hw with rfl | rfl | rfl | rfl
  · rw [Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun p _ => (show _ =
        if p.val < k then (0 : ℝ) + heavyCnt s.val (k - 1) else heavyCnt s.val k by
      rw [prefix_flip h hh s p k hk, fs_heavy _ _ (-3) (Or.inr rfl),
        fs_heavy _ _ (-3) (Or.inr rfl)]
      norm_num)]
    rw [double_sum h k hk, heavy_sum h (k - 1) (by omega), mk_heavy h k hk,
      class_card_m3 (2 * h + 1) (by omega), hk1, hmk]
    push_cast
    field_simp
    ring
  · rw [Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun p _ => (show _ =
        if p.val < k then (2 + ((k - 1 : ℕ) : ℝ)) + (-heavyCnt s.val (k - 1))
        else ((k : ℝ) - heavyCnt s.val k) by
      rw [prefix_flip h hh s p k hk, fs_light _ _ (-1) (Or.inr rfl),
        fs_light _ _ (-1) (Or.inr rfl)]
      by_cases hpk : p.val < k <;> simp only [hpk, if_true, if_false] <;> norm_num <;> ring)]
    rw [double_sum h k hk, Finset.sum_neg_distrib, heavy_sum h (k - 1) (by omega),
      mk_light h k hk, class_card_m1 (2 * h + 1) (by omega),
      show (2 * h + 1 + 1) / 2 = h + 1 by omega, hk1, hmk]
    push_cast
    field_simp
    ring
  · rw [Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun p _ => (show _ =
        if p.val < k then ((k - 1 : ℕ) : ℝ) + (-heavyCnt s.val (k - 1))
        else ((k : ℝ) - heavyCnt s.val k) by
      rw [prefix_flip h hh s p k hk, fs_light _ _ 1 (Or.inl rfl),
        fs_light _ _ 1 (Or.inl rfl)]
      by_cases hpk : p.val < k <;> simp only [hpk, if_true, if_false] <;> norm_num <;> ring)]
    rw [double_sum h k hk, Finset.sum_neg_distrib, heavy_sum h (k - 1) (by omega),
      mk_light h k hk, class_card_p1 (2 * h + 1) (by omega),
      show 2 * h + 1 - (2 * h + 1 + 1) / 2 = h by omega, hk1, hmk]
    push_cast
    field_simp
    ring
  · rw [Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun p _ => (show _ =
        if p.val < k then (0 : ℝ) + heavyCnt s.val (k - 1) else heavyCnt s.val k by
      rw [prefix_flip h hh s p k hk, fs_heavy _ _ 3 (Or.inl rfl),
        fs_heavy _ _ 3 (Or.inl rfl)]
      norm_num)]
    rw [double_sum h k hk, heavy_sum h (k - 1) (by omega), mk_heavy h k hk,
      class_card_p3 (2 * h + 1) (by omega), hk1, hmk]
    push_cast
    field_simp
    ring

/-- **The committed law is in the band `0`**, hence in every band `η ≥ 0`. -/
theorem oddLaw_feasible (hh : 1 ≤ h) (η : ℝ) (hη : 0 ≤ η) :
    oddLaw h hh ∈ FeasibleAt (id : Equiv.Perm (Fin (2 * h + 1 + 2)) → _) η := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hmR : ((2 * h + 1 + 2 : ℕ) : ℝ) = 2 * (h : ℝ) + 3 := by push_cast; ring
  refine feasible_push _ _ η (band_of_prefix_counts _ _ _ η (oddQ_nonneg h) ?_ ?_)
  · have e := odd_avg h (fun _ => 1)
    simp only [mul_one] at e
    rw [e]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; field_simp; ring
  · intro k hk i
    unfold prefixClassCount weightClass
    rw [prefix_avg h hh k hk _ (gFamily_weights (2 * h + 1 + 2) i), hmR]
    refine band_of_eq (by positivity) hη ?_
    have hC : (0 : ℝ) < ((univ.filter (fun j : Fin (2 * h + 1 + 2) =>
        gFamily (2 * h + 1 + 2) j = gFamily (2 * h + 1 + 2) i)).card : ℝ) := by
      have : 0 < (univ.filter (fun j : Fin (2 * h + 1 + 2) =>
          gFamily (2 * h + 1 + 2) j = gFamily (2 * h + 1 + 2) i)).card :=
        Finset.card_pos.mpr ⟨i, by simp⟩
      exact_mod_cast this
    field_simp

/-! ## 5. Exchanges -/

theorem exch_card {α : Type*} [DecidableEq α] (P : Finset α) (a b : α) (ha : a ∈ P) (hb : b ∉ P) :
    (insert b (P.erase a)).card = P.card := by
  rw [Finset.card_insert_of_notMem (fun hm => hb (Finset.mem_of_mem_erase hm)),
    Finset.card_erase_add_one ha]

theorem exch_sdiff {α : Type*} [DecidableEq α] (P : Finset α) (a b : α) :
    (P \ insert b (P.erase a)).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun x hx y hy => ?_
  simp only [mem_sdiff, mem_insert, mem_erase, not_or, not_and] at hx hy
  have hxa : x = a := by by_contra hne; exact hx.2.2 hne hx.1
  have hya : y = a := by by_contra hne; exact hy.2.2 hne hy.1
  rw [hxa, hya]

theorem exch_count {α : Type*} [DecidableEq α] (P : Finset α) (a b : α) (ha : a ∈ P) (hb : b ∉ P)
    (f : α → Prop) [DecidablePred f] :
    (((insert b (P.erase a)).filter f).card : ℝ)
      = ((P.filter f).card : ℝ) - (if f a then 1 else 0) + (if f b then 1 else 0) := by
  rw [Finset.filter_insert, Finset.filter_erase]
  have hb' : b ∉ (P.filter f).erase a := fun hm =>
    hb (Finset.mem_of_mem_filter _ (Finset.mem_of_mem_erase hm))
  have he : (((P.filter f).erase a).card : ℝ) = ((P.filter f).card : ℝ) - (if f a then 1 else 0) := by
    by_cases hfa : f a
    · have h1 := Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨ha, hfa⟩)
      rw [if_pos hfa]
      have h2 : (((P.filter f).erase a).card : ℝ) + 1 = ((P.filter f).card : ℝ) := by
        exact_mod_cast h1
      linarith
    · rw [if_neg hfa, Finset.erase_eq_of_notMem (fun hm => hfa (Finset.mem_filter.mp hm).2)]
      ring
  by_cases hfb : f b
  · rw [if_pos hfb, if_pos hfb, Finset.card_insert_of_notMem hb']
    push_cast
    linarith
  · rw [if_neg hfb, if_neg hfb, he]
    ring

theorem exch_sum {α : Type*} [DecidableEq α] (P : Finset α) (a b : α) (ha : a ∈ P) (hb : b ∉ P)
    (g : α → ℝ) : ∑ i ∈ insert b (P.erase a), g i = ∑ i ∈ P, g i - g a + g b := by
  rw [Finset.sum_insert (fun hm => hb (Finset.mem_of_mem_erase hm))]
  have := Finset.sum_erase_add P g ha
  linarith

theorem mem_prefixSet_self {m : ℕ} (σ : Equiv.Perm (Fin m)) (k : Fin (m + 1)) (i : Fin m) :
    σ i ∈ prefixSet σ k ↔ i.val < k.val := by
  simp [prefixSet]

/-- A position, reduced mod `m` (it is the given value whenever it is used). -/
def modPos (v : ℕ) : Fin (2 * h + 1 + 2) := ⟨v % (2 * h + 1 + 2), Nat.mod_lt _ (by omega)⟩

theorem modPos_val (v : ℕ) (hv : v < 2 * h + 1 + 2) : (modPos h v).val = v := Nat.mod_eq_of_lt hv

/-- The absolute position of the `E`-index `e`. -/
def epos (p e : ℕ) : ℕ := if e < p then e else e + 1

/-- Exchange A: the single is after the prefix and the prefix holds one heavy item. -/
def exA (k s p : ℕ) : Prop := k ≤ p ∧ k = 2 * s + 1

/-- Exchange B: the single is in the prefix and the prefix is costly. -/
def exB (k s : ℕ) (b : Bool) (p : ℕ) : Prop := p < k ∧ k % 2 = 0 ∧ (b = false ∨ k = 2 * s + 2)

instance (k s p : ℕ) : Decidable (exA k s p) := by unfold exA; infer_instance
instance (k s : ℕ) (b : Bool) (p : ℕ) : Decidable (exB k s b p) := by unfold exB; infer_instance

/-- **The final sets.** -/
noncomputable def oddT (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (x : OIdx h) :
    Finset (Fin (2 * h + 1 + 2)) :=
  if exA k.val x.1.val x.2.2.val then
    insert (oddBase h hh x (modPos h (epos x.2.2.val (2 * x.1.val + 1))))
      ((prefixSet (oddBase h hh x) k).erase (oddBase h hh x (modPos h (2 * x.1.val - 1))))
  else if exB k.val x.1.val x.2.1 x.2.2.val then
    insert (oddBase h hh x (modPos h k.val))
      ((prefixSet (oddBase h hh x) k).erase (oddBase h hh x (modPos h x.2.2.val)))
  else prefixSet (oddBase h hh x) k

theorem oddPat_epos (s : ℕ) (b : Bool) (p e : ℕ) (hlt : epos p e < 2 * h + 1 + 2) :
    oddPat h s b p (modPos h (epos p e)) = ePat s b e := by
  unfold oddPat
  rw [modPos_val h _ hlt]
  unfold epos
  by_cases he : e < p
  · rw [if_pos he, if_neg (by omega)]
    unfold eidx
    rw [if_pos he]
  · rw [if_neg he, if_neg (by omega)]
    unfold eidx
    rw [if_neg (by omega), show e + 1 - 1 = e by omega]

theorem ePat_two_s_sub_one (s : ℕ) (hs : 1 ≤ s) (b : Bool) :
    ePat s b (2 * s - 1) = (if b then -1 else 1) := by
  unfold ePat
  rw [(insWeight_eq_one_iff (2 * s) (2 * s - 1)).mpr ⟨by omega, by omega, by
    rw [Nat.not_even_iff_odd]; exact ⟨s - 1, by omega⟩⟩]
  ring

theorem ePat_partner (s : ℕ) (b : Bool) : ePat s b (2 * s + 1) = (if b then -1 else 1) * (-3) := by
  unfold ePat
  rw [(insWeight_eq_neg_three_iff (2 * s) (2 * s + 1)).mpr rfl]

theorem ePat_odd_light (s j : ℕ) (hj : j % 2 = 1) (hne : j ≠ 2 * s + 1) (b : Bool) :
    ePat s b j = (if b then -1 else 1) := by
  unfold ePat
  rw [(insWeight_eq_one_iff (2 * s) j).mpr ⟨by omega, hne, by
    rw [Nat.not_even_iff_odd]; exact ⟨j / 2, by omega⟩⟩]
  ring

/-! ## 6. Counts and sums of the final sets -/

theorem prefixSet_count (hh : 1 ≤ h) (x : OIdx h) (k : Fin (2 * h + 1 + 2 + 1)) (w : ℝ) :
    ((((prefixSet (oddBase h hh x) k).filter (fun j => gFamily (2 * h + 1 + 2) j = w)).card : ℕ) : ℝ)
      = ∑ i ∈ univ.filter (fun i : Fin (2 * h + 1 + 2) => i.val < k.val),
          (if gFamily (2 * h + 1 + 2) (oddBase h hh x i) = w then (1 : ℝ) else 0) := by
  rw [prefixSet_eq_map, card_filter_map']

theorem prefixSet_gsum (hh : 1 ≤ h) (x : OIdx h) (k : Fin (2 * h + 1 + 2 + 1)) :
    ∑ j ∈ prefixSet (oddBase h hh x) k, gFamily (2 * h + 1 + 2) j
      = ∑ i ∈ univ.filter (fun i : Fin (2 * h + 1 + 2) => i.val < k.val),
          gFamily (2 * h + 1 + 2) (oddBase h hh x i) := by
  rw [prefixSet_eq_map, sum_map']

/-- The correction an exchange makes to the count of weight `w`. -/
noncomputable def corr (k s : ℕ) (b : Bool) (p : ℕ) (w : ℝ) : ℝ :=
  if exA k s p then
    -(if (if b then (-1 : ℝ) else 1) = w then 1 else 0)
      + (if (if b then (-1 : ℝ) else 1) * (-3) = w then 1 else 0)
  else if exB k s b p then
    -(if (-1 : ℝ) = w then 1 else 0) + (if ePat s b (k - 1) = w then 1 else 0)
  else 0

theorem corr_A (k s : ℕ) (b : Bool) (p : ℕ) (w : ℝ) (hA : exA k s p) :
    corr k s b p w = -(if (if b then (-1 : ℝ) else 1) = w then 1 else 0)
      + (if (if b then (-1 : ℝ) else 1) * (-3) = w then 1 else 0) := by
  unfold corr; rw [if_pos hA]

theorem corr_B (k s : ℕ) (b : Bool) (p : ℕ) (w : ℝ) (hA : ¬ exA k s p) (hB : exB k s b p) :
    corr k s b p w = -(if (-1 : ℝ) = w then 1 else 0) + (if ePat s b (k - 1) = w then 1 else 0) := by
  unfold corr; rw [if_neg hA, if_pos hB]

theorem corr_0 (k s : ℕ) (b : Bool) (p : ℕ) (w : ℝ) (hA : ¬ exA k s p) (hB : ¬ exB k s b p) :
    corr k s b p w = 0 := by
  unfold corr; rw [if_neg hA, if_neg hB]

theorem exch_A_data (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (hk2 : 2 ≤ k.val)
    (hkm : k.val ≤ 2 * h + 1) (x : OIdx h) (hA : exA k.val x.1.val x.2.2.val) :
    oddBase h hh x (modPos h (2 * x.1.val - 1)) ∈ prefixSet (oddBase h hh x) k ∧
    oddBase h hh x (modPos h (epos x.2.2.val (2 * x.1.val + 1))) ∉ prefixSet (oddBase h hh x) k ∧
    gFamily (2 * h + 1 + 2) (oddBase h hh x (modPos h (2 * x.1.val - 1))) = (if x.2.1 then -1 else 1) ∧
    gFamily (2 * h + 1 + 2) (oddBase h hh x (modPos h (epos x.2.2.val (2 * x.1.val + 1))))
      = (if x.2.1 then -1 else 1) * (-3) := by
  have hp := x.2.2.isLt
  have hs := x.1.isLt
  obtain ⟨hA1, hA2⟩ := hA
  have hr : (modPos h (2 * x.1.val - 1)).val = 2 * x.1.val - 1 := modPos_val h _ (by omega)
  have hqv : epos x.2.2.val (2 * x.1.val + 1) < 2 * h + 1 + 2 := by unfold epos; split_ifs <;> omega
  have hq : (modPos h (epos x.2.2.val (2 * x.1.val + 1))).val = epos x.2.2.val (2 * x.1.val + 1) :=
    modPos_val h _ hqv
  refine ⟨(mem_prefixSet_self _ _ _).mpr (by rw [hr]; omega), fun hm => ?_, ?_, ?_⟩
  · rw [mem_prefixSet_self, hq] at hm
    unfold epos at hm
    split_ifs at hm <;> omega
  · rw [oddBase_apply]
    unfold oddPat
    rw [hr, if_neg (by omega)]
    unfold eidx
    rw [if_pos (by omega)]
    exact ePat_two_s_sub_one _ (by omega) _
  · rw [oddBase_apply, oddPat_epos h _ _ _ _ hqv, ePat_partner]

theorem exch_B_data (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (hkm : k.val ≤ 2 * h + 1)
    (x : OIdx h) (hB : exB k.val x.1.val x.2.1 x.2.2.val) :
    oddBase h hh x (modPos h x.2.2.val) ∈ prefixSet (oddBase h hh x) k ∧
    oddBase h hh x (modPos h k.val) ∉ prefixSet (oddBase h hh x) k ∧
    gFamily (2 * h + 1 + 2) (oddBase h hh x (modPos h x.2.2.val)) = -1 ∧
    gFamily (2 * h + 1 + 2) (oddBase h hh x (modPos h k.val)) = ePat x.1.val x.2.1 (k.val - 1) := by
  have hp := x.2.2.isLt
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hr : (modPos h x.2.2.val).val = x.2.2.val := modPos_val h _ hp
  have hq : (modPos h k.val).val = k.val := modPos_val h _ (by omega)
  refine ⟨(mem_prefixSet_self _ _ _).mpr (by rw [hr]; exact hB1), fun hm => ?_, ?_, ?_⟩
  · rw [mem_prefixSet_self, hq] at hm; omega
  · rw [oddBase_apply]; unfold oddPat; rw [hr, if_pos rfl]
  · rw [oddBase_apply]; unfold oddPat; rw [hq, if_neg (by omega)]; unfold eidx; rw [if_neg (by omega)]

/-- **Final counts = prefix counts + the exchange correction.** -/
theorem oddT_count (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (hk2 : 2 ≤ k.val)
    (hkm : k.val ≤ 2 * h + 1) (x : OIdx h) (w : ℝ) :
    ((((oddT h hh k x).filter (fun j => gFamily (2 * h + 1 + 2) j = w)).card : ℕ) : ℝ)
      = (∑ i ∈ univ.filter (fun i : Fin (2 * h + 1 + 2) => i.val < k.val),
          (if gFamily (2 * h + 1 + 2) (oddBase h hh x i) = w then (1 : ℝ) else 0))
        + corr k.val x.1.val x.2.1 x.2.2.val w := by
  unfold oddT
  by_cases hA : exA k.val x.1.val x.2.2.val
  · rw [if_pos hA, corr_A _ _ _ _ _ hA]
    obtain ⟨m1, m2, g1, g2⟩ := exch_A_data h hh k hk2 hkm x hA
    rw [exch_count _ _ _ m1 m2, prefixSet_count, g1, g2]
    ring
  · rw [if_neg hA]
    by_cases hB : exB k.val x.1.val x.2.1 x.2.2.val
    · rw [if_pos hB, corr_B _ _ _ _ _ hA hB]
      obtain ⟨m1, m2, g1, g2⟩ := exch_B_data h hh k hkm x hB
      rw [exch_count _ _ _ m1 m2, prefixSet_count, g1, g2]
      ring
    · rw [if_neg hB, corr_0 _ _ _ _ _ hA hB, prefixSet_count, add_zero]

theorem oddT_card (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (hk2 : 2 ≤ k.val)
    (hkm : k.val ≤ 2 * h + 1) (x : OIdx h) : (oddT h hh k x).card = k.val := by
  unfold oddT
  by_cases hA : exA k.val x.1.val x.2.2.val
  · rw [if_pos hA]
    obtain ⟨m1, m2, -, -⟩ := exch_A_data h hh k hk2 hkm x hA
    rw [exch_card _ _ _ m1 m2, prefixSet_card]
  · rw [if_neg hA]
    by_cases hB : exB k.val x.1.val x.2.1 x.2.2.val
    · rw [if_pos hB]
      obtain ⟨m1, m2, -, -⟩ := exch_B_data h hh k hkm x hB
      rw [exch_card _ _ _ m1 m2, prefixSet_card]
    · rw [if_neg hB, prefixSet_card]

theorem oddT_sdiff (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (x : OIdx h) :
    (prefixSet (oddBase h hh x) k \ oddT h hh k x).card ≤ 1 := by
  unfold oddT
  split_ifs
  · exact exch_sdiff _ _ _
  · exact exch_sdiff _ _ _
  · simp

/-- **Every final set has zero regret.** -/
theorem oddT_gsum (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (hk2 : 2 ≤ k.val)
    (hkm : k.val ≤ 2 * h + 1) (x : OIdx h) :
    |∑ j ∈ oddT h hh k x, gFamily (2 * h + 1 + 2) j| = ((k.val % 2 : ℕ) : ℝ) := by
  have hp := x.2.2.isLt
  have hs := x.1.isLt
  have ha : 2 * x.1.val + 1 < 2 * h + 2 := by omega
  have hpre := prefix_sum h hh x k.val (by omega)
  unfold oddT
  by_cases hA : exA k.val x.1.val x.2.2.val
  · rw [if_pos hA]
    obtain ⟨m1, m2, g1, g2⟩ := exch_A_data h hh k hk2 hkm x hA
    obtain ⟨hA1, hA2⟩ := hA
    have hnp : ¬ x.2.2.val < k.val := by omega
    rw [exch_sum _ _ _ m1 m2, prefixSet_gsum, hpre, g1, g2, if_neg hnp, if_neg hnp,
      insRanking_prefix (2 * h + 2) (2 * x.1.val) ha k.val (by omega), if_pos hA2,
      if_pos (even_two_mul x.1.val), show k.val % 2 = 1 by omega]
    cases x.2.1 <;> norm_num
  · rw [if_neg hA]
    by_cases hB : exB k.val x.1.val x.2.1 x.2.2.val
    · rw [if_pos hB]
      obtain ⟨m1, m2, g1, g2⟩ := exch_B_data h hh k hkm x hB
      obtain ⟨hB1, hB2, hB3⟩ := hB
      rw [exch_sum _ _ _ m1 m2, prefixSet_gsum, hpre, g1, g2, if_pos hB1, if_pos hB1,
        insRanking_prefix (2 * h + 2) (2 * x.1.val) ha (k.val - 1) (by omega), hB2]
      by_cases hk2s : k.val = 2 * x.1.val + 2
      · rw [if_pos (show k.val - 1 = 2 * x.1.val + 1 by omega), if_pos (even_two_mul x.1.val),
          show k.val - 1 = 2 * x.1.val + 1 by omega, ePat_partner]
        cases x.2.1 <;> norm_num
      · have hb : x.2.1 = false := by
          rcases hB3 with h1 | h1
          · exact h1
          · exact absurd h1 hk2s
        rw [if_neg (show ¬ (k.val - 1 = 2 * x.1.val + 1) by omega),
          if_neg (show ¬ Even (k.val - 1) by
            rw [Nat.not_even_iff_odd]; exact ⟨k.val / 2 - 1, by omega⟩),
          ePat_odd_light _ _ (by omega) (by omega), hb]
        norm_num
    · rw [if_neg hB, prefixSet_gsum, hpre]
      unfold exA at hA
      unfold exB at hB
      by_cases hpk : x.2.2.val < k.val
      · rw [if_pos hpk, if_pos hpk,
          insRanking_prefix (2 * h + 2) (2 * x.1.val) ha (k.val - 1) (by omega)]
        rcases Nat.mod_two_eq_zero_or_one k.val with hk0 | hk1
        · have hb : x.2.1 = true := by
            by_contra hbf
            exact hB ⟨hpk, hk0, Or.inl (by simpa using hbf)⟩
          have hk2s : k.val ≠ 2 * x.1.val + 2 := fun e => hB ⟨hpk, hk0, Or.inr e⟩
          rw [if_neg (show ¬ (k.val - 1 = 2 * x.1.val + 1) by omega),
            if_neg (show ¬ Even (k.val - 1) by
              rw [Nat.not_even_iff_odd]; exact ⟨k.val / 2 - 1, by omega⟩), hb, hk0]
          norm_num
        · rw [if_neg (show ¬ (k.val - 1 = 2 * x.1.val + 1) by omega),
            if_pos (show Even (k.val - 1) from ⟨k.val / 2, by omega⟩), hk1]
          cases x.2.1 <;> norm_num
      · rw [if_neg hpk, if_neg hpk,
          insRanking_prefix (2 * h + 2) (2 * x.1.val) ha k.val (by omega)]
        have hk2s : k.val ≠ 2 * x.1.val + 1 := fun e => hA ⟨by omega, e⟩
        rw [if_neg hk2s]
        rcases Nat.mod_two_eq_zero_or_one k.val with hk0 | hk1
        · rw [if_pos (show Even k.val from ⟨k.val / 2, by omega⟩), hk0]
          norm_num
        · rw [if_neg (show ¬ Even k.val by
            rw [Nat.not_even_iff_odd]; exact ⟨k.val / 2, by omega⟩), hk1]
          cases x.2.1 <;> norm_num

theorem oddT_cost (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (hk2 : 2 ≤ k.val)
    (hkm : k.val ≤ 2 * h + 1) (x : OIdx h) :
    subCost (gFamily (2 * h + 1 + 2)) k (oddT h hh k x) = 0 := by
  unfold subCost
  rw [oddT_gsum h hh k hk2 hkm x,
    CIGAMF.P13.PaperCBaselineAttain.familyBaselineIdentification_holds (2 * h + 1 + 2) (by omega)
      k (by omega) (by omega)]
  simp

