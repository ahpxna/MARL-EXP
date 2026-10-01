import «LeanPaperCBudgetSharpV1»

/-!
# Paper C: one exchange reaches the budget-aware value of `g_m`, for even `m` and every `η`

`recourse_one_even`: for even `m ≥ 4` and every `η ≥ 0`,
`V^{(1)}_{g_m}(η) = B_{g_m}(η) = 4 max(1-η, 0)/(mD)`.

**The plan.**
* The committed law `P` is the *pair law*: the alternating light sequence with the heavy pair
  inserted at an EVEN position `2s` (`s` uniform on `0..h`, `m = 2h+2`), with a global sign
  flip, relabelled uniformly inside each weight class (`symLaw`, `symPerm` of
  `LeanPaperCRelabelBandJoinV1`). Every item is in every prefix with probability exactly
  `k/m` (`pair_feasible`, band `0`).
* At the budgets `1` and `m-1` the final set is drawn independently from a near-optimal
  subset law (one exchange always suffices there).
* At an odd middle budget `k = 2s+1` the prefix of the ranking with the pair at `2s` contains
  exactly one heavy item and costs `2/D`; with probability `θ = min(η, 1)` the plan swaps that
  heavy item for the light item at position `2s+2` (one exchange), which costs `0`. This moves
  probability `θ/m` off each heavy item and `θ/(mh)` onto each light item, so the final law is
  in the band `θ ≤ η`, and the cost is `4(1-θ)/(mD) = B`. Even middle budgets cost `0`.

Generic tools: `planJ`/`sym_plan` (a symmetrised plan built from base rankings and target sets,
with class-average final marginals) and `plan_mix` (plans over the same committed law mix, with
the band mixing linearly).
-/

namespace CIGAMF.P13.PaperCBudgetExchange

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCRelabel
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCBudgetAware
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCStabilityFamily
open CIGAMF.P13.PaperCBudgetSharp CIGAMF.P13.PaperCRelabelBandJoin
open CIGAMF.P13.PaperCBudgetSym (orbitCount_eq sym_avg subCost_map card_wperm_pos class_card_m3
  class_card_p3 class_card_m1 class_card_p1)

variable {m : ℕ}

/-! ## 1. Symmetrised plans -/

theorem prefixSet_eq_map (σ : Equiv.Perm (Fin m)) (k : Fin (m + 1)) :
    prefixSet σ k = (univ.filter (fun p : Fin m => p.val < k.val)).map σ.toEmbedding := by
  ext i; simp [prefixSet, Finset.mem_map_equiv]

theorem prefixSet_mul (c τ : Equiv.Perm (Fin m)) (k : Fin (m + 1)) :
    prefixSet (c * τ) k = (prefixSet τ k).map c.toEmbedding := by
  have e : (c * τ).toEmbedding = τ.toEmbedding.trans c.toEmbedding :=
    Function.Embedding.ext fun p => rfl
  rw [prefixSet_eq_map, prefixSet_eq_map, Finset.map_map, e]

section Plan

variable {R : Type*} [Fintype R]

/-- The plan: draw a relabelling `c` and a base index `x`, rank by `c * base x`, and end with
the moved target set `c(T x)`. -/
noncomputable def planJ (g : Ranking m) (base : R → Equiv.Perm (Fin m)) (q : R → ℝ)
    (T : R → Finset (Fin m)) : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ :=
  fun σ S => ∑ p : WPerm g × R,
    (if symPerm g base p = σ then symLaw g q p else 0)
      * (if (T p.2).map p.1.1.toEmbedding = S then 1 else 0)

theorem planJ_sumS (g : Ranking m) (base : R → Equiv.Perm (Fin m)) (q : R → ℝ)
    (T : R → Finset (Fin m)) (σ : Equiv.Perm (Fin m)) (f : Finset (Fin m) → ℝ) :
    ∑ S, planJ g base q T σ S * f S
      = ∑ p : WPerm g × R, (if symPerm g base p = σ then symLaw g q p else 0)
          * f ((T p.2).map p.1.1.toEmbedding) := by
  unfold planJ
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [ite_mul]

theorem planJ_total (g : Ranking m) (base : R → Equiv.Perm (Fin m)) (q : R → ℝ)
    (T : R → Finset (Fin m)) (f : Finset (Fin m) → ℝ) :
    ∑ σ, ∑ S, planJ g base q T σ S * f S
      = ∑ p : WPerm g × R, symLaw g q p * f ((T p.2).map p.1.1.toEmbedding) := by
  simp_rw [planJ_sumS]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem planJ_marg (g : Ranking m) (base : R → Equiv.Perm (Fin m)) (q : R → ℝ)
    (T : R → Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    ∑ S, planJ g base q T σ S = pushLaw (symPerm g base) (symLaw g q) σ := by
  have := planJ_sumS g base q T σ (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  unfold pushLaw
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : symPerm g base x = σ <;> simp [hx]

/-- **A symmetrised plan is feasible**, with class-average final marginals and the mixed
cost of its target sets. -/
theorem sym_plan (g : Ranking m) (base : R → Equiv.Perm (Fin m)) (q : R → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (k : Fin (m + 1)) (Rx : ℕ) (η : ℝ)
    (T : R → Finset (Fin m)) (hTc : ∀ x, (T x).card = k.val)
    (hTd : ∀ x, (prefixSet (base x) k \ T x).card ≤ Rx)
    (hband : ∀ i : Fin m, |∑ x, q x * ((((T x).filter (fun j => g j = g i)).card : ℝ)
        / ((univ.filter (fun j : Fin m => g j = g i)).card : ℝ)) - (k.val : ℝ) / m| ≤ η / m) :
    planJ g base q T ∈ PlanFeasible (pushLaw (symPerm g base) (symLaw g q)) k Rx η ∧
      planCost g k (planJ g base q T) = ∑ x, q x * subCost g k (T x) := by
  have hw0 : ∀ p, 0 ≤ symLaw g q p := symLaw_nonneg g q hq0
  refine ⟨⟨fun σ S => ?_, fun σ => planJ_marg g base q T σ, fun σ S hJ => ?_, fun i => ?_⟩, ?_⟩
  · refine Finset.sum_nonneg fun p _ => mul_nonneg ?_ (by split_ifs <;> norm_num)
    split_ifs
    · exact hw0 p
    · exact le_rfl
  · obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
    have h1 : symPerm g base p = σ := by
      by_contra h; apply hp; rw [if_neg h, zero_mul]
    have h2 : (T p.2).map p.1.1.toEmbedding = S := by
      by_contra h; apply hp; rw [if_neg h, mul_zero]
    subst h1 h2
    refine ⟨by rw [Finset.card_map, hTc], ?_⟩
    show (prefixSet (p.1.1 * base p.2) k \ (T p.2).map p.1.1.toEmbedding).card ≤ Rx
    rw [prefixSet_mul, ← Finset.map_sdiff, Finset.card_map]
    exact hTd p.2
  · rw [planJ_total g base q T (ind i)]
    unfold symLaw
    rw [sym_avg g T q _ (ind i) (fun x => orbitCount_eq g (T x) i)]
    exact hband i
  · unfold planCost
    rw [planJ_total g base q T (subCost g k)]
    unfold symLaw
    rw [sym_avg g T q (fun x => subCost g k (T x)) (subCost g k) (fun x => by
      simp_rw [subCost_map]; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])]

end Plan

/-- **Plans over the same committed law mix**, with the band mixing linearly. -/
theorem plan_mix (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) (Rx : ℕ) (η₀ η₁ t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (J₀ J₁ : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (h₀ : J₀ ∈ PlanFeasible P k Rx η₀) (h₁ : J₁ ∈ PlanFeasible P k Rx η₁) :
    (fun σ S => (1 - t) * J₀ σ S + t * J₁ σ S) ∈ PlanFeasible P k Rx ((1 - t) * η₀ + t * η₁) := by
  have h1t : 0 ≤ 1 - t := by linarith
  refine ⟨fun σ S => add_nonneg (mul_nonneg h1t (h₀.1 σ S)) (mul_nonneg ht0 (h₁.1 σ S)),
    fun σ => ?_, fun σ S hS => ?_, fun i => ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₀.2.1 σ, h₁.2.1 σ]; ring
  · by_cases h : J₀ σ S = 0
    · have : J₁ σ S ≠ 0 := by intro h'; apply hS; simp [h, h']
      exact h₁.2.2.1 σ S this
    · exact h₀.2.2.1 σ S h
  · have e : ∑ σ, ∑ S, ((1 - t) * J₀ σ S + t * J₁ σ S) * ind i S
        = (1 - t) * ∑ σ, ∑ S, J₀ σ S * ind i S + t * ∑ σ, ∑ S, J₁ σ S * ind i S := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun S _ => by ring
    rw [e]
    have b0 := h₀.2.2.2 i
    have b1 := h₁.2.2.2 i
    rw [abs_le] at b0 b1 ⊢
    obtain ⟨l0, u0⟩ := b0
    obtain ⟨l1, u1⟩ := b1
    have e2 : ((1 - t) * η₀ + t * η₁) / m = (1 - t) * (η₀ / m) + t * (η₁ / m) := by ring
    rw [e2]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left l0 h1t, mul_le_mul_of_nonneg_left l1 ht0]
    · nlinarith [mul_le_mul_of_nonneg_left u0 h1t, mul_le_mul_of_nonneg_left u1 ht0]

theorem planCost_mix (g : Ranking m) (k : Fin (m + 1)) (t : ℝ)
    (J₀ J₁ : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) :
    planCost g k (fun σ S => (1 - t) * J₀ σ S + t * J₁ σ S)
      = (1 - t) * planCost g k J₀ + t * planCost g k J₁ := by
  unfold planCost
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

theorem plan_mono (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) (Rx : ℕ) {η η' : ℝ}
    (h : η ≤ η') (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (hJ : J ∈ PlanFeasible P k Rx η) : J ∈ PlanFeasible P k Rx η' :=
  ⟨hJ.1, hJ.2.1, hJ.2.2.1, fun i =>
    (hJ.2.2.2 i).trans (div_le_div_of_nonneg_right h (Nat.cast_nonneg _))⟩

/-! ## 2. Counting positions of the inserted ranking -/

theorem insWeight_cases (a i : ℕ) :
    insWeight a i = -3 ∨ insWeight a i = -1 ∨ insWeight a i = 1 ∨ insWeight a i = 3 := by
  unfold insWeight
  split_ifs
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl rfl
  · rcases neg_one_pow_eq_or ℝ (i + 1) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  · rcases neg_one_pow_eq_or ℝ (i - 1) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)

/-- The four weight counts of a prefix add up to its length. -/
theorem countIns_all (a k : ℕ) :
    countIns a (-3) k + countIns a (-1) k + countIns a 1 k + countIns a 3 k = k := by
  unfold countIns
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun i _ => (show
      ((if insWeight a i = -3 then (1 : ℝ) else 0) + (if insWeight a i = -1 then 1 else 0)
        + (if insWeight a i = 1 then 1 else 0) + (if insWeight a i = 3 then 1 else 0)) = 1 by
      rcases insWeight_cases a i with h | h | h | h <;> rw [h] <;> norm_num)]
  simp

/-- Heavy count: the pair contributes `[a < k] + [a+1 < k]`. -/
theorem countIns_heavy (a k : ℕ) :
    countIns a 3 k + countIns a (-3) k
      = (if a < k then (1 : ℝ) else 0) + (if a + 1 < k then 1 else 0) := by
  rw [countIns_three, countIns_neg_three]

theorem countIns_light (a k : ℕ) :
    countIns a (-1) k + countIns a 1 k
      = (k : ℝ) - ((if a < k then (1 : ℝ) else 0) + (if a + 1 < k then 1 else 0)) := by
  have h1 := countIns_all a k
  have h2 := countIns_heavy a k
  linarith

/-- Sums over the first `k` positions of `Fin N`, as sums over `range k`. -/
theorem sum_filter_lt (N k : ℕ) (hk : k ≤ N) (F : ℕ → ℝ) :
    ∑ p ∈ univ.filter (fun p : Fin N => p.val < k), F p.val = ∑ i ∈ range k, F i := by
  rw [Finset.sum_filter]
  rw [show (∑ p : Fin N, if p.val < k then F p.val else 0)
      = ∑ i ∈ range N, (if i < k then F i else 0) from
    Fin.sum_univ_eq_sum_range (fun i => if i < k then F i else 0) N]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

/-- Even slots cover every position once: `Σ_{s ≤ h} ([2s<k] + [2s+1<k]) = k` for `k ≤ 2h+2`. -/
theorem pair_count_sum (h k : ℕ) (hk : k ≤ 2 * h + 2) :
    ∑ s : Fin (h + 1), ((if 2 * s.val < k then (1 : ℝ) else 0)
      + (if 2 * s.val + 1 < k then 1 else 0)) = k := by
  rw [Fin.sum_univ_eq_sum_range (fun s => (if 2 * s < k then (1 : ℝ) else 0)
      + (if 2 * s + 1 < k then 1 else 0)) (h + 1)]
  have key : ∀ n, ∑ s ∈ range n, ((if 2 * s < k then (1 : ℝ) else 0)
      + (if 2 * s + 1 < k then 1 else 0)) = ∑ p ∈ range (2 * n), (if p < k then (1 : ℝ) else 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
          Finset.sum_range_succ, Finset.sum_range_succ]
        ring
  rw [key, Finset.sum_boole]
  have : (range (2 * (h + 1))).filter (fun p => p < k) = range k := by
    ext p; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

/-! ## 3. The pair law, for `m = 2h+2` -/

section Pair

variable (h : ℕ) (hh : 1 ≤ h)

/-- The ranking with the heavy pair at the even position `2s`, sign-flipped when `b`. -/
noncomputable def pairBase (x : Fin (h + 1) × Bool) : Equiv.Perm (Fin (2 * h + 2)) :=
  evenPerm (2 * h + 2) (by omega) (by omega) (⟨2 * x.1.val, by have := x.1.isLt; omega⟩, x.2)

/-- Uniform weights on the `2(h+1)` rankings. -/
noncomputable def pairQ : Fin (h + 1) × Bool → ℝ := fun _ => 1 / (2 * ((h : ℝ) + 1))

theorem pairQ_nonneg : ∀ x, 0 ≤ pairQ h x := fun _ => by unfold pairQ; positivity

theorem pairBase_apply (x : Fin (h + 1) × Bool) (p : Fin (2 * h + 2)) :
    gFamily (2 * h + 2) (pairBase h hh x p)
      = (if x.2 then -1 else 1) * insWeight (2 * x.1.val) p.val := by
  unfold pairBase
  rw [evenPerm_apply]
  rcases x with ⟨s, b⟩
  cases b <;> simp [evenRk, insRanking]

/-- The committed law. -/
noncomputable def pairLaw : Equiv.Perm (Fin (2 * h + 2)) → ℝ :=
  pushLaw (symPerm (gFamily (2 * h + 2)) (pairBase h hh)) (symLaw (gFamily (2 * h + 2)) (pairQ h))

/-- Position count of weight `w` in the first `k` positions of a base ranking. -/
theorem pairBase_count (x : Fin (h + 1) × Bool) (k : ℕ) (hk : k ≤ 2 * h + 2) (w : ℝ) :
    ∑ p ∈ univ.filter (fun p : Fin (2 * h + 2) => p.val < k),
        (if gFamily (2 * h + 2) (pairBase h hh x p) = w then (1 : ℝ) else 0)
      = if x.2 then countIns (2 * x.1.val) (-w) k else countIns (2 * x.1.val) w k := by
  simp_rw [pairBase_apply h hh x]
  rcases x with ⟨s, b⟩
  cases b
  · simp only [Bool.false_eq_true, if_false, one_mul]
    exact sum_filter_lt _ k hk (fun i => if insWeight (2 * s.val) i = w then (1 : ℝ) else 0)
  · simp only [if_true]
    have e : ∀ p : Fin (2 * h + 2), ((if -1 * insWeight (2 * s.val) p.val = w then (1 : ℝ) else 0)
        = if insWeight (2 * s.val) p.val = -w then 1 else 0) := by
      intro p
      congr 1
      apply propext
      constructor <;> intro hp <;> linarith
    simp_rw [e]
    exact sum_filter_lt _ k hk (fun i => if insWeight (2 * s.val) i = -w then (1 : ℝ) else 0)

/-- Flip-summed prefix counts: heavy classes. -/
theorem pair_heavy_flip (s : Fin (h + 1)) (k : ℕ) (hk : k ≤ 2 * h + 2) (w : ℝ)
    (hw : w = 3 ∨ w = -3) :
    (∑ p ∈ univ.filter (fun p : Fin (2 * h + 2) => p.val < k),
        (if gFamily (2 * h + 2) (pairBase h hh (s, false) p) = w then (1 : ℝ) else 0))
      + (∑ p ∈ univ.filter (fun p : Fin (2 * h + 2) => p.val < k),
        (if gFamily (2 * h + 2) (pairBase h hh (s, true) p) = w then (1 : ℝ) else 0))
      = (if 2 * s.val < k then (1 : ℝ) else 0) + (if 2 * s.val + 1 < k then 1 else 0) := by
  rw [pairBase_count h hh _ k hk, pairBase_count h hh _ k hk]
  simp only [Bool.false_eq_true, if_false, if_true]
  rcases hw with rfl | rfl
  · rw [countIns_heavy]
  · rw [neg_neg, add_comm, countIns_heavy]

/-- Flip-summed prefix counts: light classes. -/
theorem pair_light_flip (s : Fin (h + 1)) (k : ℕ) (hk : k ≤ 2 * h + 2) (w : ℝ)
    (hw : w = 1 ∨ w = -1) :
    (∑ p ∈ univ.filter (fun p : Fin (2 * h + 2) => p.val < k),
        (if gFamily (2 * h + 2) (pairBase h hh (s, false) p) = w then (1 : ℝ) else 0))
      + (∑ p ∈ univ.filter (fun p : Fin (2 * h + 2) => p.val < k),
        (if gFamily (2 * h + 2) (pairBase h hh (s, true) p) = w then (1 : ℝ) else 0))
      = (k : ℝ) - ((if 2 * s.val < k then (1 : ℝ) else 0) + (if 2 * s.val + 1 < k then 1 else 0)) := by
  rw [pairBase_count h hh _ k hk, pairBase_count h hh _ k hk]
  simp only [Bool.false_eq_true, if_false, if_true]
  rcases hw with rfl | rfl
  · rw [add_comm, countIns_light]
  · rw [neg_neg, countIns_light]

/-- Averages over the pair law index split into slot sums of flip sums. -/
theorem pair_avg (F : Fin (h + 1) × Bool → ℝ) :
    ∑ x, pairQ h x * F x = (1 / (2 * ((h : ℝ) + 1))) * ∑ s : Fin (h + 1), (F (s, false) + F (s, true)) := by
  unfold pairQ
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_bool]
  ring

/-- **The pair law is in the band `0`**, hence in every band `η ≥ 0`. -/
theorem pair_feasible (η : ℝ) (hη : 0 ≤ η) :
    pairLaw h hh ∈ FeasibleAt (id : Equiv.Perm (Fin (2 * h + 2)) → _) η := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hmR : ((2 * h + 2 : ℕ) : ℝ) = 2 * (h : ℝ) + 2 := by push_cast; ring
  refine feasible_push _ _ η (band_of_prefix_counts _ _ _ η (pairQ_nonneg h) ?_ ?_)
  · have e := pair_avg h (fun _ => 1)
    simp only [mul_one] at e
    rw [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; field_simp; ring
  · intro k hk i
    unfold prefixClassCount weightClass
    rw [pair_avg h (fun x => ∑ p ∈ univ.filter (fun p : Fin (2 * h + 2) => p.val < k),
      (if gFamily (2 * h + 2) (pairBase h hh x p) = gFamily (2 * h + 2) i then (1 : ℝ) else 0))]
    rw [hmR]
    refine band_of_eq (by positivity) hη ?_
    rcases gFamily_weights (2 * h + 2) i with hw | hw | hw | hw <;> rw [hw]
    · rw [Finset.sum_congr rfl fun s _ => pair_heavy_flip h hh s k hk (-3) (Or.inr rfl),
        pair_count_sum h k hk, class_card_m3 (2 * h) (by omega)]
      field_simp; ring
    · rw [Finset.sum_congr rfl fun s _ => pair_light_flip h hh s k hk (-1) (Or.inr rfl),
        Finset.sum_sub_distrib, pair_count_sum h k hk, class_card_m1 (2 * h) (by omega),
        show (2 * h + 1) / 2 = h by omega]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp; ring
    · rw [Finset.sum_congr rfl fun s _ => pair_light_flip h hh s k hk 1 (Or.inl rfl),
        Finset.sum_sub_distrib, pair_count_sum h k hk, class_card_p1 (2 * h) (by omega),
        show 2 * h - (2 * h + 1) / 2 = h by omega]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp; ring
    · rw [Finset.sum_congr rfl fun s _ => pair_heavy_flip h hh s k hk 3 (Or.inl rfl),
        pair_count_sum h k hk, class_card_p3 (2 * h) (by omega)]
      field_simp; ring

end Pair

/-! ## 4. The plans at the middle budgets -/

section Middle

variable (h : ℕ) (hh : 1 ≤ h)

theorem card_filter_map' (g : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (A : Finset (Fin m)) (w : ℝ) :
    ((((A.map σ.toEmbedding).filter (fun j => g j = w)).card : ℕ) : ℝ)
      = ∑ p ∈ A, (if g (σ p) = w then (1 : ℝ) else 0) := by
  rw [Finset.filter_map, Finset.card_map, Finset.natCast_card_filter]
  rfl

theorem sum_map' (g : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (A : Finset (Fin m)) :
    ∑ j ∈ A.map σ.toEmbedding, g j = ∑ p ∈ A, g (σ p) := by
  rw [Finset.sum_map]; rfl

/-- The position `2s+2` (reduced mod `m`; it is `2s+2` whenever it is used). -/
def nextPos (s : Fin (h + 1)) : Fin (2 * h + 2) :=
  ⟨(2 * s.val + 2) % (2 * h + 2), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- Target positions at budget `k`: at `k = 2s+1` drop position `2s` (the heavy item) and add
position `2s+2`; otherwise keep the prefix. -/
noncomputable def posT (k : Fin (2 * h + 2 + 1)) (x : Fin (h + 1) × Bool) : Finset (Fin (2 * h + 2)) :=
  if 2 * x.1.val + 1 = k.val then insert (nextPos h x.1) (univ.filter (fun p : Fin (2 * h + 2) => p.val < 2 * x.1.val))
  else univ.filter (fun p : Fin (2 * h + 2) => p.val < k.val)

/-- The edited target sets. -/
noncomputable def editT (k : Fin (2 * h + 2 + 1)) (x : Fin (h + 1) × Bool) : Finset (Fin (2 * h + 2)) :=
  (posT h k x).map (pairBase h hh x).toEmbedding

/-- The unedited target sets: the prefixes. -/
noncomputable def preT (k : Fin (2 * h + 2 + 1)) (x : Fin (h + 1) × Bool) : Finset (Fin (2 * h + 2)) :=
  prefixSet (pairBase h hh x) k

theorem nextPos_val (s : Fin (h + 1)) (hs : 2 * s.val + 2 < 2 * h + 2) :
    (nextPos h s).val = 2 * s.val + 2 := Nat.mod_eq_of_lt hs

theorem nextPos_not_mem (s : Fin (h + 1)) (hs : 2 * s.val + 2 < 2 * h + 2) :
    nextPos h s ∉ univ.filter (fun p : Fin (2 * h + 2) => p.val < 2 * s.val) := by
  simp only [mem_filter, mem_univ, true_and, not_lt]
  rw [nextPos_val h s hs]; omega

theorem insWeight_next (s : ℕ) : insWeight (2 * s) (2 * s + 2) = -1 := by
  unfold insWeight
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show 2 * s + 2 - 1 = 2 * s + 1 by omega]
  exact (Odd.neg_one_pow ⟨s, rfl⟩)

theorem card_filter_lt (N k : ℕ) (hk : k ≤ N) :
    (univ.filter (fun p : Fin N => p.val < k)).card = k := by
  have := CIGAMF.P13.PaperCBaselineAttain.card_filter_Icc N 0 (k - 1)
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0; simp
  · have e : univ.filter (fun p : Fin N => p.val < k)
        = univ.filter (fun p : Fin N => 0 ≤ p.val ∧ p.val ≤ k - 1) := by
      ext p; simp only [mem_filter, mem_univ, true_and]; omega
    rw [e, this (by omega)]; omega

theorem editT_card (k : Fin (2 * h + 2 + 1)) (hk : k.val ≤ 2 * h) (x : Fin (h + 1) × Bool) :
    (editT h hh k x).card = k.val := by
  unfold editT posT
  rw [Finset.card_map]
  split_ifs with hx
  · rw [Finset.card_insert_of_notMem (nextPos_not_mem h x.1 (by omega)),
      card_filter_lt _ _ (by omega)]
    omega
  · exact card_filter_lt _ _ (by omega)

theorem editT_sdiff (k : Fin (2 * h + 2 + 1)) (hk : k.val ≤ 2 * h) (x : Fin (h + 1) × Bool) :
    (prefixSet (pairBase h hh x) k \ editT h hh k x).card ≤ 1 := by
  unfold editT posT
  rw [prefixSet_eq_map, ← Finset.map_sdiff, Finset.card_map]
  split_ifs with hx
  · refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [mem_sdiff, mem_filter, mem_univ, true_and, mem_insert, not_or] at ha hb
    apply Fin.ext; omega
  · simp

theorem preT_card (k : Fin (2 * h + 2 + 1)) (x : Fin (h + 1) × Bool) :
    (preT h hh k x).card = k.val := prefixSet_card _ k

theorem preT_sdiff (k : Fin (2 * h + 2 + 1)) (x : Fin (h + 1) × Bool) :
    (prefixSet (pairBase h hh x) k \ preT h hh k x).card ≤ 0 := by
  unfold preT; simp

/-- Flip-summed class counts of the edited targets. -/
theorem editT_flip (k : Fin (2 * h + 2 + 1)) (hk : k.val ≤ 2 * h) (s : Fin (h + 1)) (w : ℝ) :
    ((((editT h hh k (s, false)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      + ((((editT h hh k (s, true)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      = if 2 * s.val + 1 = k.val then
          ((if (-1 : ℝ) = w then 1 else 0) + (if (1 : ℝ) = w then 1 else 0)
            + (countIns (2 * s.val) w (2 * s.val) + countIns (2 * s.val) (-w) (2 * s.val)))
        else countIns (2 * s.val) w k.val + countIns (2 * s.val) (-w) k.val := by
  unfold editT
  rw [card_filter_map', card_filter_map']
  unfold posT
  dsimp only
  by_cases hx : 2 * s.val + 1 = k.val
  · repeat rw [if_pos hx]
    rw [Finset.sum_insert (nextPos_not_mem h s (by omega)),
      Finset.sum_insert (nextPos_not_mem h s (by omega)),
      pairBase_count h hh (s, false) (2 * s.val) (by omega),
      pairBase_count h hh (s, true) (2 * s.val) (by omega),
      pairBase_apply h hh, pairBase_apply h hh, nextPos_val h s (by omega), insWeight_next]
    simp only [Bool.false_eq_true, if_false, if_true]
    have e1 : (1 : ℝ) * -1 = -1 := by norm_num
    have e2 : (-1 : ℝ) * -1 = 1 := by norm_num
    rw [e1, e2]
    ring
  · repeat rw [if_neg hx]
    rw [pairBase_count h hh (s, false) k.val (by omega), pairBase_count h hh (s, true) k.val (by omega)]
    simp only [Bool.false_eq_true, if_false, if_true]

theorem preT_flip (k : Fin (2 * h + 2 + 1)) (s : Fin (h + 1)) (w : ℝ) :
    ((((preT h hh k (s, false)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      + ((((preT h hh k (s, true)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      = countIns (2 * s.val) w k.val + countIns (2 * s.val) (-w) k.val := by
  unfold preT
  rw [prefixSet_eq_map, prefixSet_eq_map, card_filter_map', card_filter_map',
    pairBase_count h hh (s, false) k.val (by have := k.isLt; omega),
    pairBase_count h hh (s, true) k.val (by have := k.isLt; omega)]
  simp only [Bool.false_eq_true, if_false, if_true]

end Middle

/-! ## 5. Flip sums, bands and costs at the middle budgets -/

section Costs

variable (h : ℕ) (hh : 1 ≤ h)

/-- The heavy count of the prefix of the ranking with the pair at `2s`. -/
noncomputable def heavyCnt (s k : ℕ) : ℝ :=
  (if 2 * s < k then (1 : ℝ) else 0) + (if 2 * s + 1 < k then 1 else 0)

theorem preT_flip_heavy (k : Fin (2 * h + 2 + 1)) (s : Fin (h + 1)) (w : ℝ) (hw : w = 3 ∨ w = -3) :
    ((((preT h hh k (s, false)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      + ((((preT h hh k (s, true)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      = heavyCnt s.val k.val := by
  rw [preT_flip h hh k s w]
  unfold heavyCnt
  rcases hw with rfl | rfl
  · rw [countIns_heavy]
  · rw [neg_neg, add_comm, countIns_heavy]

theorem preT_flip_light (k : Fin (2 * h + 2 + 1)) (s : Fin (h + 1)) (w : ℝ) (hw : w = 1 ∨ w = -1) :
    ((((preT h hh k (s, false)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      + ((((preT h hh k (s, true)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      = (k.val : ℝ) - heavyCnt s.val k.val := by
  rw [preT_flip h hh k s w]
  unfold heavyCnt
  rcases hw with rfl | rfl
  · rw [add_comm, countIns_light]
  · rw [neg_neg, countIns_light]

theorem editT_flip_heavy (k : Fin (2 * h + 2 + 1)) (hk : k.val ≤ 2 * h) (s : Fin (h + 1)) (w : ℝ)
    (hw : w = 3 ∨ w = -3) :
    ((((editT h hh k (s, false)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      + ((((editT h hh k (s, true)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      = heavyCnt s.val k.val - (if k.val = 2 * s.val + 1 then 1 else 0) := by
  rw [editT_flip h hh k hk s w]
  have e1 : ¬ (2 * s.val < 2 * s.val) := lt_irrefl _
  have e2 : ¬ (2 * s.val + 1 < 2 * s.val) := by omega
  by_cases hx : 2 * s.val + 1 = k.val
  · rw [if_pos hx, if_pos hx.symm]
    unfold heavyCnt
    rw [← hx]
    have e3 : 2 * s.val < 2 * s.val + 1 := by omega
    have e4 : ¬ (2 * s.val + 1 < 2 * s.val + 1) := lt_irrefl _
    simp only [e3, e4, if_true, if_false]
    rcases hw with rfl | rfl
    · rw [countIns_heavy]; simp only [e1, e2, if_false] <;> norm_num
    · rw [neg_neg, add_comm (countIns _ (-3) _), countIns_heavy]; simp only [e1, e2, if_false] <;> norm_num
  · rw [if_neg hx, if_neg (Ne.symm hx), sub_zero]
    unfold heavyCnt
    rcases hw with rfl | rfl
    · rw [countIns_heavy]
    · rw [neg_neg, add_comm, countIns_heavy]

theorem editT_flip_light (k : Fin (2 * h + 2 + 1)) (hk : k.val ≤ 2 * h) (s : Fin (h + 1)) (w : ℝ)
    (hw : w = 1 ∨ w = -1) :
    ((((editT h hh k (s, false)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      + ((((editT h hh k (s, true)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
      = ((k.val : ℝ) - heavyCnt s.val k.val) + (if k.val = 2 * s.val + 1 then 1 else 0) := by
  rw [editT_flip h hh k hk s w]
  have e1 : ¬ (2 * s.val < 2 * s.val) := lt_irrefl _
  have e2 : ¬ (2 * s.val + 1 < 2 * s.val) := by omega
  by_cases hx : 2 * s.val + 1 = k.val
  · rw [if_pos hx, if_pos hx.symm]
    unfold heavyCnt
    rw [← hx]
    have e3 : 2 * s.val < 2 * s.val + 1 := by omega
    have e4 : ¬ (2 * s.val + 1 < 2 * s.val + 1) := lt_irrefl _
    simp only [e3, e4, if_true, if_false]
    rcases hw with rfl | rfl
    · rw [add_comm (countIns _ 1 _), countIns_light]; simp only [e1, e2, if_false] <;> push_cast <;> norm_num <;> ring
    · rw [neg_neg, countIns_light]; simp only [e1, e2, if_false] <;> push_cast <;> norm_num <;> ring
  · rw [if_neg hx, if_neg (Ne.symm hx), add_zero]
    unfold heavyCnt
    rcases hw with rfl | rfl
    · rw [add_comm, countIns_light]
    · rw [neg_neg, countIns_light]

theorem heavy_sum (k : ℕ) (hk : k ≤ 2 * h + 2) :
    ∑ s : Fin (h + 1), heavyCnt s.val k = k := by
  unfold heavyCnt; exact pair_count_sum h k hk

theorem slot_sum (k : ℕ) (hk : k ≤ 2 * h + 1) (c : ℝ) :
    ∑ s : Fin (h + 1), (if k = 2 * s.val + 1 then c else 0) = if k % 2 = 1 then c else 0 := by
  split_ifs with hodd
  · rw [Finset.sum_eq_single (⟨(k - 1) / 2, by omega⟩ : Fin (h + 1))]
    · rw [if_pos (show k = 2 * ((k - 1) / 2) + 1 by omega)]
    · intro s _ hs
      rw [if_neg]
      intro h2; apply hs; exact Fin.ext (show s.val = (k - 1) / 2 by omega)
    · intro h'; exact absurd (mem_univ _) h'
  · exact Finset.sum_eq_zero fun s _ => if_neg (by omega)

/-- Class averages of a target family, reduced to slot sums of flip sums. -/
theorem class_avg (T : Fin (h + 1) × Bool → Finset (Fin (2 * h + 2))) (w C : ℝ) :
    ∑ x, pairQ h x * ((((T x).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℝ) / C)
      = (1 / (2 * ((h : ℝ) + 1))) * (∑ s : Fin (h + 1),
          (((((T (s, false)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ)
            + ((((T (s, true)).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℕ) : ℝ))) / C := by
  simp_rw [mul_div_assoc']
  rw [← Finset.sum_div, pair_avg h (fun x => (((T x).filter (fun j => gFamily (2 * h + 2) j = w)).card : ℝ))]

/-- **The prefixes are exactly in the band `0`.** -/
theorem preT_band (k : Fin (2 * h + 2 + 1)) (i : Fin (2 * h + 2)) :
    |∑ x, pairQ h x * ((((preT h hh k x).filter
        (fun j => gFamily (2 * h + 2) j = gFamily (2 * h + 2) i)).card : ℝ)
        / ((univ.filter (fun j : Fin (2 * h + 2) => gFamily (2 * h + 2) j = gFamily (2 * h + 2) i)).card : ℝ))
      - (k.val : ℝ) / ((2 * h + 2 : ℕ) : ℝ)| ≤ 0 / ((2 * h + 2 : ℕ) : ℝ) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hkm : k.val ≤ 2 * h + 2 := by have := k.isLt; omega
  refine band_of_eq (by positivity) le_rfl ?_
  rw [class_avg h]
  push_cast
  rcases gFamily_weights (2 * h + 2) i with hw | hw | hw | hw <;> rw [hw]
  · rw [Finset.sum_congr rfl fun s _ => preT_flip_heavy h hh k s (-3) (Or.inr rfl),
      heavy_sum h k.val hkm, class_card_m3 (2 * h) (by omega)]
    (try push_cast) <;> (try field_simp) <;> ring
  · rw [Finset.sum_congr rfl fun s _ => preT_flip_light h hh k s (-1) (Or.inr rfl),
      Finset.sum_sub_distrib, heavy_sum h k.val hkm, class_card_m1 (2 * h) (by omega),
      show (2 * h + 1) / 2 = h by omega]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    (try push_cast) <;> (try field_simp) <;> ring
  · rw [Finset.sum_congr rfl fun s _ => preT_flip_light h hh k s 1 (Or.inl rfl),
      Finset.sum_sub_distrib, heavy_sum h k.val hkm, class_card_p1 (2 * h) (by omega),
      show 2 * h - (2 * h + 1) / 2 = h by omega]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    (try push_cast) <;> (try field_simp) <;> ring
  · rw [Finset.sum_congr rfl fun s _ => preT_flip_heavy h hh k s 3 (Or.inl rfl),
      heavy_sum h k.val hkm, class_card_p3 (2 * h) (by omega)]
    (try push_cast) <;> (try field_simp) <;> ring

/-- **The edited targets are in the band `1`.** -/
theorem editT_band (k : Fin (2 * h + 2 + 1)) (hk : k.val ≤ 2 * h) (i : Fin (2 * h + 2)) :
    |∑ x, pairQ h x * ((((editT h hh k x).filter
        (fun j => gFamily (2 * h + 2) j = gFamily (2 * h + 2) i)).card : ℝ)
        / ((univ.filter (fun j : Fin (2 * h + 2) => gFamily (2 * h + 2) j = gFamily (2 * h + 2) i)).card : ℝ))
      - (k.val : ℝ) / ((2 * h + 2 : ℕ) : ℝ)| ≤ 1 / ((2 * h + 2 : ℕ) : ℝ) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hkm : k.val ≤ 2 * h + 2 := by omega
  have hM : (0 : ℝ) < ((2 * h + 2 : ℕ) : ℝ) := by positivity
  have hcast : ((2 * h + 2 : ℕ) : ℝ) = 2 * (h : ℝ) + 2 := by push_cast; ring
  set c : ℝ := if k.val % 2 = 1 then 1 else 0 with hc
  have hc0 : 0 ≤ c := by rw [hc]; split_ifs <;> norm_num
  have hc1 : c ≤ 1 := by rw [hc]; split_ifs <;> norm_num
  rw [class_avg h]
  rcases gFamily_weights (2 * h + 2) i with hw | hw | hw | hw <;> rw [hw]
  · rw [Finset.sum_congr rfl fun s _ => editT_flip_heavy h hh k hk s (-3) (Or.inr rfl),
      Finset.sum_sub_distrib, heavy_sum h k.val hkm, slot_sum h k.val (by omega) 1, ← hc,
      class_card_m3 (2 * h) (by omega)]
    refine band_of_diff hM (δ := -c / ((2 * h + 2 : ℕ) : ℝ)) (by (try push_cast) <;> (try field_simp) <;> ring) ?_
    rw [abs_div, abs_neg, abs_of_nonneg hc0, abs_of_pos hM, div_mul_cancel₀ _ hM.ne']
    exact hc1
  · rw [Finset.sum_congr rfl fun s _ => editT_flip_light h hh k hk s (-1) (Or.inr rfl),
      Finset.sum_add_distrib, Finset.sum_sub_distrib, heavy_sum h k.val hkm,
      slot_sum h k.val (by omega) 1, ← hc, class_card_m1 (2 * h) (by omega),
      show (2 * h + 1) / 2 = h by omega]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine band_of_diff hM (δ := c / (((2 * h + 2 : ℕ) : ℝ) * h)) (by (try push_cast) <;> (try field_simp) <;> ring) ?_
    rw [abs_of_nonneg (div_nonneg hc0 (by positivity)), div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (show c ≤ (h : ℝ) by linarith) hM.le]
  · rw [Finset.sum_congr rfl fun s _ => editT_flip_light h hh k hk s 1 (Or.inl rfl),
      Finset.sum_add_distrib, Finset.sum_sub_distrib, heavy_sum h k.val hkm,
      slot_sum h k.val (by omega) 1, ← hc, class_card_p1 (2 * h) (by omega),
      show 2 * h - (2 * h + 1) / 2 = h by omega]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine band_of_diff hM (δ := c / (((2 * h + 2 : ℕ) : ℝ) * h)) (by (try push_cast) <;> (try field_simp) <;> ring) ?_
    rw [abs_of_nonneg (div_nonneg hc0 (by positivity)), div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (show c ≤ (h : ℝ) by linarith) hM.le]
  · rw [Finset.sum_congr rfl fun s _ => editT_flip_heavy h hh k hk s 3 (Or.inl rfl),
      Finset.sum_sub_distrib, heavy_sum h k.val hkm, slot_sum h k.val (by omega) 1, ← hc,
      class_card_p3 (2 * h) (by omega)]
    refine band_of_diff hM (δ := -c / ((2 * h + 2 : ℕ) : ℝ)) (by (try push_cast) <;> (try field_simp) <;> ring) ?_
    rw [abs_div, abs_neg, abs_of_nonneg hc0, abs_of_pos hM, div_mul_cancel₀ _ hM.ne']
    exact hc1

/-- The prefix of the ranking with the pair at `2s` costs `2/D` at `k = 2s+1` and `0`
elsewhere. -/
theorem preT_cost (k : Fin (2 * h + 2 + 1)) (hk1 : 1 ≤ k.val) (hk : k.val < 2 * h + 2)
    (x : Fin (h + 1) × Bool) :
    subCost (gFamily (2 * h + 2)) k (preT h hh k x)
      = (if k.val = 2 * x.1.val + 1 then 2 else 0) / (2 * (h : ℝ) + 6) := by
  have e1 : subCost (gFamily (2 * h + 2)) k (preT h hh k x)
      = normalizedRegret (gFamily (2 * h + 2)) (pairBase h hh x) k := rfl
  rw [e1, CIGAMF.P13.PaperCBaselineAttain.family_regret_identification_unconditional (2 * h + 2)
    (by omega) _ k hk1 hk]
  unfold regret pairBase
  rw [rankOf_evenPerm]
  have ha : 2 * x.1.val + 1 < 2 * h + 2 := by have := x.1.isLt; omega
  have hex : excess (evenRk (2 * h + 2) (⟨2 * x.1.val, by have := x.1.isLt; omega⟩, x.2)) k.val
      = if k.val = 2 * x.1.val + 1 then 2 else 0 := by
    rcases x with ⟨s, b⟩
    cases b
    · exact insRanking_excess (2 * h + 2) (2 * s.val) ha k.val (by omega)
    · show excess (fun i => -(insRanking (2 * h + 2) (2 * s.val) i)) k.val = _
      rw [excess_neg]
      exact insRanking_excess (2 * h + 2) (2 * s.val) ha k.val (by omega)
  rw [hex]
  congr 1
  push_cast; ring

/-- The edited targets cost nothing at the middle budgets. -/
theorem editT_cost (k : Fin (2 * h + 2 + 1)) (hk1 : 1 ≤ k.val) (hk : k.val ≤ 2 * h)
    (x : Fin (h + 1) × Bool) : subCost (gFamily (2 * h + 2)) k (editT h hh k x) = 0 := by
  by_cases hx : 2 * x.1.val + 1 = k.val
  · have hs : 2 * x.1.val + 2 < 2 * h + 2 := by omega
    have hpre : ∑ p ∈ univ.filter (fun p : Fin (2 * h + 2) => p.val < 2 * x.1.val),
        gFamily (2 * h + 2) (pairBase h hh x p)
        = (if x.2 then -1 else 1)
          * prefixSum (insRanking (2 * h + 2) (2 * x.1.val)) (2 * x.1.val) := by
      simp_rw [pairBase_apply h hh x]
      rw [← Finset.mul_sum]; rfl
    unfold subCost editT posT
    rw [if_pos hx, sum_map', Finset.sum_insert (nextPos_not_mem h x.1 hs), pairBase_apply h hh,
      nextPos_val h x.1 hs, insWeight_next, hpre,
      insRanking_prefix (2 * h + 2) (2 * x.1.val) (by omega) (2 * x.1.val) (by omega),
      if_neg (show ¬ (2 * x.1.val = 2 * x.1.val + 1) by omega), if_pos (even_two_mul x.1.val),
      CIGAMF.P13.PaperCBaselineAttain.familyBaselineIdentification_holds (2 * h + 2) (by omega)
        k hk1 (by omega),
      show k.val % 2 = 1 by omega]
    rcases x with ⟨s, b⟩
    cases b <;> norm_num
  · have e : editT h hh k x = preT h hh k x := by
      unfold editT posT preT
      rw [if_neg hx, ← prefixSet_eq_map]
    rw [e, preT_cost h hh k hk1 (by omega) x, if_neg (by omega)]
    simp

theorem editT_eq_preT (k : Fin (2 * h + 2 + 1)) (hk : k.val % 2 = 0) :
    editT h hh k = preT h hh k := by
  funext x
  unfold editT posT preT
  rw [if_neg (by omega), ← prefixSet_eq_map]

/-- **The prefix plan**: band `0`; cost `4/(mD)` at odd middle budgets, `0` at even ones. -/
theorem J0_spec (k : Fin (2 * h + 2 + 1)) (hk1 : 1 ≤ k.val) (hk : k.val ≤ 2 * h) :
    planJ (gFamily (2 * h + 2)) (pairBase h hh) (pairQ h) (preT h hh k)
        ∈ PlanFeasible (pairLaw h hh) k 1 0 ∧
      planCost (gFamily (2 * h + 2)) k
          (planJ (gFamily (2 * h + 2)) (pairBase h hh) (pairQ h) (preT h hh k))
        = if k.val % 2 = 1 then 4 / ((2 * (h : ℝ) + 2) * (2 * (h : ℝ) + 6)) else 0 := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  obtain ⟨hJ, hc⟩ := sym_plan (gFamily (2 * h + 2)) (pairBase h hh) (pairQ h) (pairQ_nonneg h)
    k 1 0 (preT h hh k) (preT_card h hh k)
    (fun x => (preT_sdiff h hh k x).trans (Nat.zero_le 1)) (fun i => preT_band h hh k i)
  refine ⟨hJ, ?_⟩
  rw [hc, pair_avg h (fun x => subCost (gFamily (2 * h + 2)) k (preT h hh k x))]
  simp only [preT_cost h hh k hk1 (by omega)]
  have e : ∀ s : Fin (h + 1),
      (if k.val = 2 * s.val + 1 then (2 : ℝ) else 0) / (2 * (h : ℝ) + 6)
        + (if k.val = 2 * s.val + 1 then (2 : ℝ) else 0) / (2 * (h : ℝ) + 6)
      = (2 / (2 * (h : ℝ) + 6)) * (if k.val = 2 * s.val + 1 then (2 : ℝ) else 0) := by
    intro s; ring
  rw [Finset.sum_congr rfl fun s _ => e s, ← Finset.mul_sum, slot_sum h k.val (by omega) 2]
  split_ifs <;> field_simp <;> ring

/-- **The edited plan**: band `1`, cost `0` at every middle budget. -/
theorem J1_spec (k : Fin (2 * h + 2 + 1)) (hk1 : 1 ≤ k.val) (hk : k.val ≤ 2 * h) :
    planJ (gFamily (2 * h + 2)) (pairBase h hh) (pairQ h) (editT h hh k)
        ∈ PlanFeasible (pairLaw h hh) k 1 1 ∧
      planCost (gFamily (2 * h + 2)) k
          (planJ (gFamily (2 * h + 2)) (pairBase h hh) (pairQ h) (editT h hh k)) = 0 := by
  obtain ⟨hJ, hc⟩ := sym_plan (gFamily (2 * h + 2)) (pairBase h hh) (pairQ h) (pairQ_nonneg h)
    k 1 1 (editT h hh k) (editT_card h hh k hk) (editT_sdiff h hh k hk)
    (fun i => editT_band h hh k hk i)
  refine ⟨hJ, ?_⟩
  rw [hc]
  exact Finset.sum_eq_zero fun x _ => by rw [editT_cost h hh k hk1 hk x, mul_zero]

end Costs

/-! ## 6. One exchange reaches `B` -/

/-- **One exchange suffices on `g_m`, even `m`, at every band level**:
`V^{(1)}_{g_m}(η) = B_{g_m}(η) = 4 max(1-η, 0)/(mD)`. -/
theorem recourse_one_even (m : ℕ) (hm : 4 ≤ m) (heven : Even m) (η : ℝ) (hη : 0 ≤ η) :
    recourseValue (gFamily m) η 1 (interiorK m) (interiorK_nonempty m (by omega))
      = awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega)) := by
  obtain ⟨h, rfl⟩ : ∃ h, m = 2 * h + 2 := ⟨(m - 2) / 2, by obtain ⟨r, hr⟩ := heven; omega⟩
  have hh : 1 ≤ h := by omega
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  refine le_antisymm ?_ (aware_le_recourse _ η hη 1 _ _)
  have hB := aware_even_exact (2 * h + 2) hm heven η hη
  have hcast : ((2 * h + 2 : ℕ) : ℝ) = 2 * (h : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hB
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hnear : ∀ k : Fin (2 * h + 2 + 1), ∃ Q ∈ SubFeasible (m := 2 * h + 2) k.val η,
      ∑ S, Q S * subCost (gFamily (2 * h + 2)) k S
        < layerValue (gFamily (2 * h + 2)) η k + ε := by
    intro k
    obtain ⟨_, ⟨Q, hQ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((sub_nonempty η hη k).image _)
      (show layerValue (gFamily (2 * h + 2)) η k < layerValue (gFamily (2 * h + 2)) η k + ε by
        linarith)
    exact ⟨Q, hQ, hlt⟩
  choose Qf hQf hQc using hnear
  set θ : ℝ := min η 1 with hθ
  have hθ0 : 0 ≤ θ := le_min hη zero_le_one
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have hθη : θ ≤ η := min_le_left _ _
  have h1θ : 1 - θ = max (1 - η) 0 := by
    rcases le_total η 1 with h1 | h1
    · rw [hθ, min_eq_left h1, max_eq_left (by linarith)]
    · rw [hθ, min_eq_right h1, max_eq_right (by linarith)]; ring
  have hP := pair_feasible h hh η hη
  have hP1 : ∑ σ, pairLaw h hh σ = 1 := hP.2.1
  let J : Fin (2 * h + 2 + 1) → Equiv.Perm (Fin (2 * h + 2)) → Finset (Fin (2 * h + 2)) → ℝ :=
    fun k => if k.val = 1 ∨ k.val = 2 * h + 1 then indepPlan (pairLaw h hh) (Qf k)
      else fun σ S => (1 - θ) * planJ (gFamily (2 * h + 2)) (pairBase h hh) (pairQ h) (preT h hh k) σ S
        + θ * planJ (gFamily (2 * h + 2)) (pairBase h hh) (pairQ h) (editT h hh k) σ S
  have hmem : (interiorK (2 * h + 2)).sup' (interiorK_nonempty (2 * h + 2) (by omega))
      (fun k => planCost (gFamily (2 * h + 2)) k (J k))
      ∈ recourseSet (gFamily (2 * h + 2)) η 1 (interiorK (2 * h + 2))
        (interiorK_nonempty (2 * h + 2) (by omega)) := by
    refine ⟨pairLaw h hh, hP, J, fun k hk => ?_, rfl⟩
    have hk' : 1 ≤ k.val ∧ k.val ≤ 2 * h + 2 - 1 := by simpa [interiorK] using hk
    by_cases hend : k.val = 1 ∨ k.val = 2 * h + 1
    · simp only [J, if_pos hend]
      exact indep_feasible _ η hP k 1 (by omega) (Qf k) (hQf k)
    · simp only [J, if_neg hend]
      have h0 := (J0_spec h hh k (by omega) (by omega)).1
      have h1 := (J1_spec h hh k (by omega) (by omega)).1
      exact plan_mono _ k 1 (by linarith) _ (plan_mix _ k 1 0 1 θ hθ0 hθ1 _ _ h0 h1)
  refine lt_of_le_of_lt (csInf_le (recourse_bdd _ η 1 _ _) hmem) ?_
  rw [Finset.sup'_lt_iff]
  intro k hk
  have hk' : 1 ≤ k.val ∧ k.val ≤ 2 * h + 2 - 1 := by simpa [interiorK] using hk
  have hlay : layerValue (gFamily (2 * h + 2)) η k
      ≤ awareValue (gFamily (2 * h + 2)) η (interiorK (2 * h + 2))
        (interiorK_nonempty (2 * h + 2) (by omega)) :=
    Finset.le_sup' (fun k => layerValue (gFamily (2 * h + 2)) η k) hk
  by_cases hend : k.val = 1 ∨ k.val = 2 * h + 1
  · simp only [J, if_pos hend]
    rw [indep_cost _ _ hP1]
    linarith [hQc k]
  · simp only [J, if_neg hend]
    rw [planCost_mix, (J0_spec h hh k (by omega) (by omega)).2,
      (J1_spec h hh k (by omega) (by omega)).2, mul_zero, add_zero, h1θ, hB]
    have hM0 : 0 ≤ max (1 - η) 0 := le_max_right _ _
    have hle : max (1 - η) 0 * (if k.val % 2 = 1 then 4 / ((2 * (h : ℝ) + 2) * (2 * (h : ℝ) + 6)) else 0)
        ≤ 4 * max (1 - η) 0 / ((2 * (h : ℝ) + 2) * (2 * (h : ℝ) + 2 + 4)) := by
      split_ifs
      · apply le_of_eq; ring
      · rw [mul_zero]; positivity
    linarith

#print axioms sym_plan
#print axioms plan_mix
#print axioms pair_feasible
#print axioms preT_band
#print axioms editT_band
#print axioms J0_spec
#print axioms J1_spec
#print axioms recourse_one_even

end CIGAMF.P13.PaperCBudgetExchange
