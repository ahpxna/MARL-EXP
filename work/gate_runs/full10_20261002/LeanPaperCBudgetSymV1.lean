import «LeanPaperCBudgetGmV1»

/-!
# Paper C: symmetrised subset laws, typed sets of `g_m`, drop laws, mixing

Tools for UPPER bounds on the budget-aware layers `B_{g,k}(η)` (`layerValue`).

* `orbitCount_eq`: averaging a set `T` over the weight-preserving relabellings `WPerm g`, item
  `i` lies in the moved set with frequency `|T ∩ C(i)| / |C(i)|`, `C(i)` its weight class.
* `exists_sym_law`: a finite mixture of sets `T_x` with weights `q_x`, symmetrised over
  `WPerm g`, is a subset law whose item marginals are the class averages; its expected cost is
  the mixture of the costs of the `T_x` for any relabelling-invariant cost (e.g. `subCost`).
* `typed_set`, `exists_counts_law`: on `g_m`, any count vector `(a,b,c,d)` (numbers of `-3`,
  `-1`, `+1`, `+3`) is realised by a set; hence a mixture of count vectors whose type marginals
  are in the band is a banded subset law with cost `Σ q_x (|-3a-b+c+3d| - (k mod 2))/D`.
* `layer_le_drop1`, `layer_le_dropc`: a banded "drop" vector `π` gives laws at the budgets `1`
  (singletons) and `m-1` (complements of singletons).
* `sub_mono`, `sub_mix`: the banded subset laws grow with `η` and are closed under mixing, with
  the band mixing linearly.
-/

namespace CIGAMF.P13.PaperCBudgetSym

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCRelabel
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCBudgetAware
open CIGAMF.P13.PaperCBreakpoint CIGAMF.P13.PaperCBudgetFamilies CIGAMF.P13.PaperCRelaxedJoin

variable {m : ℕ}

/-! ## 1. Orbit counts under the weight-preserving relabellings -/

theorem ind_map (T : Finset (Fin m)) (c : Equiv.Perm (Fin m)) (i : Fin m) :
    ind i (T.map c.toEmbedding) = ind (c.symm i) T := by
  simp only [ind, Finset.mem_map_equiv]

/-- How many relabellings put item `i` into the moved copy of `T`. -/
noncomputable def orbitCount (g : Ranking m) (T : Finset (Fin m)) (i : Fin m) : ℝ :=
  ∑ c : WPerm g, ind i (T.map c.1.toEmbedding)

theorem orbitCount_const (g : Ranking m) (T : Finset (Fin m)) (a b : Fin m) (hab : g a = g b) :
    orbitCount g T b = orbitCount g T a := by
  obtain ⟨c₀, hc₀⟩ := wperm_orbit g a b hab
  obtain ⟨e, he⟩ := wperm_trans g c₀
  unfold orbitCount
  rw [← Equiv.sum_comp e (fun c : WPerm g => ind b (T.map c.1.toEmbedding))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ind_map, ind_map, he c, ← hc₀, symm_mul_apply, Equiv.symm_apply_apply]

theorem orbitCount_class_sum (g : Ranking m) (T : Finset (Fin m)) (w : ℝ) :
    ∑ a ∈ univ.filter (fun j : Fin m => g j = w), orbitCount g T a
      = (Fintype.card (WPerm g) : ℝ) * ((T.filter (fun j => g j = w)).card : ℝ) := by
  classical
  unfold orbitCount
  rw [Finset.sum_comm]
  have hc : ∀ c : WPerm g,
      ∑ a ∈ univ.filter (fun j : Fin m => g j = w), ind a (T.map c.1.toEmbedding)
        = ((T.filter (fun j => g j = w)).card : ℝ) := by
    intro c
    simp_rw [ind_map]
    have hre : ∑ a ∈ univ.filter (fun j : Fin m => g j = w), ind (c.1.symm a) T
        = ∑ b ∈ univ.filter (fun j : Fin m => g j = w), ind b T := by
      refine Finset.sum_nbij' (fun a => c.1.symm a) (fun b => c.1 b) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [mem_filter, mem_univ, true_and] at ha ⊢
        have := wperm_inv g c a
        rw [show (c.1⁻¹ : Equiv.Perm (Fin m)) a = c.1.symm a from rfl] at this
        rw [this, ha]
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb ⊢
        rw [c.2 b, hb]
      · intro a _; exact Equiv.apply_symm_apply _ _
      · intro b _; exact Equiv.symm_apply_apply _ _
      · intro a _; rfl
    rw [hre]
    unfold ind
    rw [Finset.sum_boole]
    congr 2
    ext j
    simp only [mem_filter, mem_univ, true_and]
    tauto
  rw [Finset.sum_congr rfl fun c _ => hc c, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The orbit frequency of an item is its class share of `T`.** -/
theorem orbitCount_eq (g : Ranking m) (T : Finset (Fin m)) (i : Fin m) :
    orbitCount g T i = (Fintype.card (WPerm g) : ℝ)
      * (((T.filter (fun j => g j = g i)).card : ℝ)
        / ((univ.filter (fun j : Fin m => g j = g i)).card : ℝ)) := by
  have hi : i ∈ univ.filter (fun j : Fin m => g j = g i) := by simp
  have h := marginal_eq_occupancy_div_card _ ⟨i, hi⟩ (orbitCount g T) _
    (fun a ha b hb => by
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact orbitCount_const g T b a (hb.trans ha.symm))
    (orbitCount_class_sum g T (g i)) i hi
  rw [h, mul_div_assoc]

/-! ## 2. The symmetrised subset law -/

section Sym

variable {R : Type*} [Fintype R]

/-- The mixture of the sets `T_x` (weights `q_x`), each moved by a uniform relabelling. -/
noncomputable def symLaw (g : Ranking m) (T : R → Finset (Fin m)) (q : R → ℝ) :
    Finset (Fin m) → ℝ :=
  fun S => ∑ p : WPerm g × R, q p.2 / (Fintype.card (WPerm g) : ℝ) *
    (if (T p.2).map p.1.1.toEmbedding = S then 1 else 0)

theorem symLaw_sum (g : Ranking m) (T : R → Finset (Fin m)) (q : R → ℝ)
    (f : Finset (Fin m) → ℝ) :
    ∑ S, symLaw g T q S * f S
      = ∑ p : WPerm g × R, q p.2 / (Fintype.card (WPerm g) : ℝ)
          * f ((T p.2).map p.1.1.toEmbedding) := by
  unfold symLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [ite_mul]

theorem card_wperm_pos (g : Ranking m) : (0 : ℝ) < (Fintype.card (WPerm g) : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem sym_avg (g : Ranking m) (T : R → Finset (Fin m)) (q : R → ℝ) (F : R → ℝ)
    (f : Finset (Fin m) → ℝ) (hf : ∀ x, ∑ c : WPerm g, f ((T x).map c.1.toEmbedding)
      = (Fintype.card (WPerm g) : ℝ) * F x) :
    ∑ p : WPerm g × R, q p.2 / (Fintype.card (WPerm g) : ℝ) * f ((T p.2).map p.1.1.toEmbedding)
      = ∑ x, q x * F x := by
  have hG := card_wperm_pos g
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only
  rw [← Finset.mul_sum, hf x]
  field_simp

/-- **A symmetrised mixture of sets is a banded subset law**, with class-average marginals
and the mixed cost for any relabelling-invariant cost. -/
theorem exists_sym_law (g : Ranking m) (η : ℝ) (k : ℕ) (T : R → Finset (Fin m)) (q : R → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1) (hT : ∀ x, (T x).card = k)
    (hband : ∀ i : Fin m, |∑ x, q x * ((((T x).filter (fun j => g j = g i)).card : ℝ)
        / ((univ.filter (fun j : Fin m => g j = g i)).card : ℝ)) - (k : ℝ) / m| ≤ η / m)
    (f : Finset (Fin m) → ℝ) (hf : ∀ (c : WPerm g) (S : Finset (Fin m)),
      f (S.map c.1.toEmbedding) = f S) :
    ∃ Q ∈ SubFeasible (m := m) k η, ∑ S, Q S * f S = ∑ x, q x * f (T x) := by
  have hG := card_wperm_pos g
  refine ⟨symLaw g T q, ⟨fun S => ?_, ?_, ?_, fun i => ?_⟩, ?_⟩
  · exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (div_nonneg (hq0 _) hG.le) (by split_ifs <;> norm_num)
  · have h1 := symLaw_sum g T q (fun _ => 1)
    rw [sym_avg g T q (fun _ => 1) (fun _ => 1) (fun x => by simp)] at h1
    simp only [mul_one] at h1
    rw [h1, hq1]
  · intro S hS
    obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
    have : (T p.2).map p.1.1.toEmbedding = S := by
      by_contra h; apply hp; rw [if_neg h, mul_zero]
    rw [← this, Finset.card_map, hT]
  · rw [symLaw_sum g T q (ind i),
      sym_avg g T q _ (ind i) (fun x => orbitCount_eq g (T x) i)]
    exact hband i
  · rw [symLaw_sum, sym_avg g T q (fun x => f (T x)) f (fun x => by
      simp_rw [hf]; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])]

end Sym

/-- The regret of a set is invariant under weight-preserving relabelling. -/
theorem subCost_map (g : Ranking m) (k : Fin (m + 1)) (c : WPerm g) (S : Finset (Fin m)) :
    subCost g k (S.map c.1.toEmbedding) = subCost g k S := by
  unfold subCost
  rw [Finset.sum_map]
  congr 3
  refine Finset.sum_congr rfl fun x _ => ?_
  exact c.2 x

/-! ## 3. Monotonicity and mixing of banded subset laws -/

theorem sub_mono (k : ℕ) {η η' : ℝ} (h : η ≤ η') (Q : Finset (Fin m) → ℝ)
    (hQ : Q ∈ SubFeasible (m := m) k η) : Q ∈ SubFeasible (m := m) k η' :=
  ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun i =>
    (hQ.2.2.2 i).trans (div_le_div_of_nonneg_right h (Nat.cast_nonneg _))⟩

theorem sub_mix (k : ℕ) (η₀ η₁ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Q₀ Q₁ : Finset (Fin m) → ℝ) (h₀ : Q₀ ∈ SubFeasible (m := m) k η₀)
    (h₁ : Q₁ ∈ SubFeasible (m := m) k η₁) :
    (fun S => (1 - t) * Q₀ S + t * Q₁ S) ∈ SubFeasible (m := m) k ((1 - t) * η₀ + t * η₁) := by
  have h1t : 0 ≤ 1 - t := by linarith
  refine ⟨fun S => add_nonneg (mul_nonneg h1t (h₀.1 S)) (mul_nonneg ht0 (h₁.1 S)), ?_, ?_,
    fun i => ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₀.2.1, h₁.2.1]; ring
  · intro S hS
    by_cases h : Q₀ S = 0
    · have : Q₁ S ≠ 0 := by intro h'; apply hS; simp [h, h']
      exact h₁.2.2.1 S this
    · exact h₀.2.2.1 S h
  · have e : ∑ S, ((1 - t) * Q₀ S + t * Q₁ S) * ind i S
        = (1 - t) * ∑ S, Q₀ S * ind i S + t * ∑ S, Q₁ S * ind i S := by
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

theorem mix_cost (Q₀ Q₁ : Finset (Fin m) → ℝ) (t : ℝ) (f : Finset (Fin m) → ℝ) :
    ∑ S, (fun S => (1 - t) * Q₀ S + t * Q₁ S) S * f S
      = (1 - t) * ∑ S, Q₀ S * f S + t * ∑ S, Q₁ S * f S := by
  simp only
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- **Layer upper bound by mixing two laws.** -/
theorem layer_le_mix (g : Ranking m) (k : Fin (m + 1)) (η₀ η₁ t η : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hη : (1 - t) * η₀ + t * η₁ ≤ η) (Q₀ Q₁ : Finset (Fin m) → ℝ)
    (h₀ : Q₀ ∈ SubFeasible (m := m) k.val η₀) (h₁ : Q₁ ∈ SubFeasible (m := m) k.val η₁) :
    layerValue g η k ≤ (1 - t) * ∑ S, Q₀ S * subCost g k S + t * ∑ S, Q₁ S * subCost g k S := by
  rw [← mix_cost]
  exact layer_le g η k _ (sub_mono k.val hη _ (sub_mix k.val η₀ η₁ t ht0 ht1 Q₀ Q₁ h₀ h₁))

/-! ## 4. Drop laws at the budgets `1` and `m-1` -/

theorem sum_mul_ind_single (π : Fin m → ℝ) (i : Fin m) :
    ∑ j, π j * ind i ({j} : Finset (Fin m)) = π i := by
  unfold ind
  simp only [Finset.mem_singleton, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem sum_mul_ind_compl (π : Fin m → ℝ) (i : Fin m) :
    ∑ j, π j * ind i ({j}ᶜ : Finset (Fin m)) = ∑ j, π j - π i := by
  have e : ∀ j, π j * ind i ({j}ᶜ : Finset (Fin m)) = π j - π j * ind i ({j} : Finset (Fin m)) := by
    intro j
    unfold ind
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, sum_mul_ind_single]

/-- **Singletons drawn from a banded drop vector.** -/
theorem layer_le_drop1 (g : Ranking m) (η : ℝ) (hm : 2 ≤ m) (π : Fin m → ℝ)
    (h0 : ∀ i, 0 ≤ π i) (h1 : ∑ i, π i = 1) (hb : ∀ i, |π i - 1 / (m : ℝ)| ≤ η / m) :
    layerValue g η ⟨1, by omega⟩ ≤ ∑ j, π j * subCost g ⟨1, by omega⟩ {j} := by
  have hQ := ptLaw_feasible (n := m) (fun j => ({j} : Finset (Fin m))) π 1 η h0 h1
    (fun j => Finset.card_singleton j) (fun i => by
      rw [sum_mul_ind_single]; simpa using hb i)
  have := layer_le g η ⟨1, by omega⟩ _ hQ
  rwa [ptLaw_sum] at this

/-- **Complements of singletons drawn from a banded drop vector.** -/
theorem layer_le_dropc (g : Ranking m) (η : ℝ) (hm : 2 ≤ m) (π : Fin m → ℝ)
    (h0 : ∀ i, 0 ≤ π i) (h1 : ∑ i, π i = 1) (hb : ∀ i, |π i - 1 / (m : ℝ)| ≤ η / m) :
    layerValue g η ⟨m - 1, by omega⟩ ≤ ∑ j, π j * subCost g ⟨m - 1, by omega⟩ {j}ᶜ := by
  have hQ := ptLaw_feasible (n := m) (fun j => ({j}ᶜ : Finset (Fin m))) π (m - 1) η h0 h1
    (fun j => by rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]) (fun i => by
      rw [sum_mul_ind_compl, h1]
      have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have e : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [e]
      have e2 : 1 - π i - ((m : ℝ) - 1) / m = -(π i - 1 / m) := by field_simp; ring
      rw [e2, abs_neg]
      exact hb i)
  have := layer_le g η ⟨m - 1, by omega⟩ _ hQ
  rwa [ptLaw_sum] at this

/-! ## 5. Typed sets of `g_m` and count-vector laws -/

theorem class_card (n : ℕ) (hn : 1 ≤ n) (w : ℝ) :
    (((univ : Finset (Fin (n + 2))).filter (fun j => gFamily (n + 2) j = w)).card : ℝ)
      = (if (-3 : ℝ) = w then 1 else 0) + (if (3 : ℝ) = w then 1 else 0)
        + (((n + 1) / 2 : ℕ) : ℝ) * (if (-1 : ℝ) = w then 1 else 0)
        + ((n - (n + 1) / 2 : ℕ) : ℝ) * (if (1 : ℝ) = w then 1 else 0) := by
  rw [Finset.natCast_card_filter]
  exact sum_fn_gFamily n hn (fun x => if x = w then 1 else 0)

theorem class_card_m3 (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (Fin (n + 2))).filter (fun j => gFamily (n + 2) j = -3)).card = 1 := by
  have := class_card n hn (-3); norm_num at this; exact_mod_cast this

theorem class_card_p3 (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (Fin (n + 2))).filter (fun j => gFamily (n + 2) j = 3)).card = 1 := by
  have := class_card n hn 3; norm_num at this; exact_mod_cast this

theorem class_card_m1 (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (Fin (n + 2))).filter (fun j => gFamily (n + 2) j = -1)).card
      = (n + 1) / 2 := by
  have := class_card n hn (-1); norm_num at this; exact_mod_cast this

theorem class_card_p1 (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (Fin (n + 2))).filter (fun j => gFamily (n + 2) j = 1)).card
      = n - (n + 1) / 2 := by
  have := class_card n hn 1; norm_num at this; exact_mod_cast this

theorem filter_eq_self_of_sub {m : ℕ} (g : Fin m → ℝ) (A : Finset (Fin m)) (w : ℝ)
    (hA : A ⊆ univ.filter (fun j => g j = w)) : A.filter (fun j => g j = w) = A := by
  refine Finset.filter_true_of_mem fun j hj => ?_
  have := hA hj; simpa using this

theorem filter_eq_empty_of_sub {m : ℕ} (g : Fin m → ℝ) (A : Finset (Fin m)) (w w' : ℝ)
    (hww : w ≠ w') (hA : A ⊆ univ.filter (fun j => g j = w)) :
    A.filter (fun j => g j = w') = ∅ := by
  refine Finset.filter_false_of_mem fun j hj => ?_
  have := hA hj; simp only [mem_filter, mem_univ, true_and] at this; rw [this]; exact hww

theorem disj_of_sub {m : ℕ} (g : Fin m → ℝ) (A B : Finset (Fin m)) (w w' : ℝ) (hww : w ≠ w')
    (hA : A ⊆ univ.filter (fun j => g j = w)) (hB : B ⊆ univ.filter (fun j => g j = w')) :
    Disjoint A B := by
  rw [Finset.disjoint_left]
  intro j hjA hjB
  have h1 := hA hjA; have h2 := hB hjB
  simp only [mem_filter, mem_univ, true_and] at h1 h2
  exact hww (h1.symm.trans h2)

theorem sum_of_sub {m : ℕ} (g : Fin m → ℝ) (A : Finset (Fin m)) (w : ℝ)
    (hA : A ⊆ univ.filter (fun j => g j = w)) : ∑ j ∈ A, g j = (A.card : ℝ) * w := by
  rw [Finset.sum_congr rfl fun j hj => (by have := hA hj; simpa using this : g j = w),
    Finset.sum_const, nsmul_eq_mul]

/-- **Every admissible count vector is realised by a set of `g_m`.** -/
theorem typed_set (n : ℕ) (hn : 1 ≤ n) (a b c d : ℕ) (ha : a ≤ 1) (hb : b ≤ (n + 1) / 2)
    (hc : c ≤ n - (n + 1) / 2) (hd : d ≤ 1) :
    ∃ T : Finset (Fin (n + 2)), T.card = a + b + c + d ∧
      (T.filter (fun j => gFamily (n + 2) j = -3)).card = a ∧
      (T.filter (fun j => gFamily (n + 2) j = -1)).card = b ∧
      (T.filter (fun j => gFamily (n + 2) j = 1)).card = c ∧
      (T.filter (fun j => gFamily (n + 2) j = 3)).card = d ∧
      ∑ j ∈ T, gFamily (n + 2) j = -3 * (a : ℝ) - b + c + 3 * d := by
  set g := gFamily (n + 2) with hg
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq
    (show a ≤ (univ.filter (fun j => g j = -3)).card by rw [class_card_m3 n hn]; exact ha)
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq
    (show b ≤ (univ.filter (fun j => g j = -1)).card by rw [class_card_m1 n hn]; exact hb)
  obtain ⟨E, hE, hEc⟩ := Finset.exists_subset_card_eq
    (show c ≤ (univ.filter (fun j => g j = 1)).card by rw [class_card_p1 n hn]; exact hc)
  obtain ⟨F, hF, hFc⟩ := Finset.exists_subset_card_eq
    (show d ≤ (univ.filter (fun j => g j = 3)).card by rw [class_card_p3 n hn]; exact hd)
  have dAB := disj_of_sub g A B (-3) (-1) (by norm_num) hA hB
  have dAE := disj_of_sub g A E (-3) 1 (by norm_num) hA hE
  have dAF := disj_of_sub g A F (-3) 3 (by norm_num) hA hF
  have dBE := disj_of_sub g B E (-1) 1 (by norm_num) hB hE
  have dBF := disj_of_sub g B F (-1) 3 (by norm_num) hB hF
  have dEF := disj_of_sub g E F 1 3 (by norm_num) hE hF
  have d1 : Disjoint (A ∪ B) E := Finset.disjoint_union_left.mpr ⟨dAE, dBE⟩
  have d2 : Disjoint (A ∪ B ∪ E) F :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨dAF, dBF⟩, dEF⟩
  refine ⟨A ∪ B ∪ E ∪ F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1,
      Finset.card_union_of_disjoint dAB, hAc, hBc, hEc, hFc]
  · rw [Finset.filter_union, Finset.filter_union, Finset.filter_union,
      filter_eq_self_of_sub g A _ hA, filter_eq_empty_of_sub g B (-1) (-3) (by norm_num) hB,
      filter_eq_empty_of_sub g E 1 (-3) (by norm_num) hE,
      filter_eq_empty_of_sub g F 3 (-3) (by norm_num) hF]
    simpa using hAc
  · rw [Finset.filter_union, Finset.filter_union, Finset.filter_union,
      filter_eq_self_of_sub g B _ hB, filter_eq_empty_of_sub g A (-3) (-1) (by norm_num) hA,
      filter_eq_empty_of_sub g E 1 (-1) (by norm_num) hE,
      filter_eq_empty_of_sub g F 3 (-1) (by norm_num) hF]
    simpa using hBc
  · rw [Finset.filter_union, Finset.filter_union, Finset.filter_union,
      filter_eq_self_of_sub g E _ hE, filter_eq_empty_of_sub g A (-3) 1 (by norm_num) hA,
      filter_eq_empty_of_sub g B (-1) 1 (by norm_num) hB,
      filter_eq_empty_of_sub g F 3 1 (by norm_num) hF]
    simpa using hEc
  · rw [Finset.filter_union, Finset.filter_union, Finset.filter_union,
      filter_eq_self_of_sub g F _ hF, filter_eq_empty_of_sub g A (-3) 3 (by norm_num) hA,
      filter_eq_empty_of_sub g B (-1) 3 (by norm_num) hB,
      filter_eq_empty_of_sub g E 1 3 (by norm_num) hE]
    simpa using hFc
  · rw [Finset.sum_union d2, Finset.sum_union d1, Finset.sum_union dAB,
      sum_of_sub g A _ hA, sum_of_sub g B _ hB, sum_of_sub g E _ hE, sum_of_sub g F _ hF,
      hAc, hBc, hEc, hFc]
    ring

/-- **A banded mixture of count vectors is a banded subset law of `g_m`**, with its exact
expected regret. -/
theorem exists_counts_law (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (k : Fin (n + 2 + 1))
    (hk1 : 1 ≤ k.val) (hkm : k.val < n + 2) {r : ℕ}
    (a b c d : Fin r → ℕ) (q : Fin r → ℝ)
    (ha : ∀ x, a x ≤ 1) (hb : ∀ x, b x ≤ (n + 1) / 2) (hc : ∀ x, c x ≤ n - (n + 1) / 2)
    (hd : ∀ x, d x ≤ 1) (hk : ∀ x, a x + b x + c x + d x = k.val)
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (bH : |∑ x, q x * (a x : ℝ) - (k.val : ℝ) / ((n : ℝ) + 2)| ≤ η / ((n : ℝ) + 2))
    (bP : |∑ x, q x * (d x : ℝ) - (k.val : ℝ) / ((n : ℝ) + 2)| ≤ η / ((n : ℝ) + 2))
    (bN : |∑ x, q x * ((b x : ℝ) / (((n + 1) / 2 : ℕ) : ℝ)) - (k.val : ℝ) / ((n : ℝ) + 2)|
      ≤ η / ((n : ℝ) + 2))
    (bQ : |∑ x, q x * ((c x : ℝ) / ((n - (n + 1) / 2 : ℕ) : ℝ)) - (k.val : ℝ) / ((n : ℝ) + 2)|
      ≤ η / ((n : ℝ) + 2)) :
    ∃ Q ∈ SubFeasible (m := n + 2) k.val η,
      ∑ S, Q S * subCost (gFamily (n + 2)) k S
        = ∑ x, q x * ((|-3 * (a x : ℝ) - b x + c x + 3 * d x| - ((k.val % 2 : ℕ) : ℝ))
            / ((n : ℝ) + 2 + 4)) := by
  choose T hTc hT3 hT1 hTp1 hTp3 hTs using fun x =>
    typed_set n hn (a x) (b x) (c x) (d x) (ha x) (hb x) (hc x) (hd x)
  have hbase : trueBaseline (gFamily (n + 2)) k = ((k.val % 2 : ℕ) : ℝ) :=
    CIGAMF.P13.PaperCBaselineAttain.familyBaselineIdentification_holds (n + 2) (by omega) k hk1
      hkm
  have hD : normMass (gFamily (n + 2)) = (n : ℝ) + 2 + 4 := by
    rw [CIGAMF.P13.PaperCBaselineAttain.normMass_gFamily (n + 2) (by omega)]; push_cast; ring
  have hcost : ∀ x, subCost (gFamily (n + 2)) k (T x)
      = (|-3 * (a x : ℝ) - b x + c x + 3 * d x| - ((k.val % 2 : ℕ) : ℝ)) / ((n : ℝ) + 2 + 4) := by
    intro x; unfold subCost; rw [hTs x, hbase, hD]
  have hband : ∀ i : Fin (n + 2),
      |∑ x, q x * ((((T x).filter (fun j => gFamily (n + 2) j = gFamily (n + 2) i)).card : ℝ)
        / ((univ.filter (fun j : Fin (n + 2) => gFamily (n + 2) j = gFamily (n + 2) i)).card : ℝ))
        - (k.val : ℝ) / ((n + 2 : ℕ) : ℝ)| ≤ η / ((n + 2 : ℕ) : ℝ) := by
    intro i
    have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    rcases gFamily_weights (n + 2) i with h | h | h | h
    · rw [h, class_card_m3 n hn]
      simp_rw [hT3]
      simpa using bH
    · rw [h, class_card_m1 n hn]
      simp_rw [hT1]
      exact bN
    · rw [h, class_card_p1 n hn]
      simp_rw [hTp1]
      exact bQ
    · rw [h, class_card_p3 n hn]
      simp_rw [hTp3]
      simpa using bP
  obtain ⟨Q, hQ, hQc⟩ := exists_sym_law (gFamily (n + 2)) η k.val T q hq0 hq1
    (fun x => by rw [hTc x, hk x]) hband (subCost (gFamily (n + 2)) k)
    (fun c S => subCost_map _ k c S)
  refine ⟨Q, hQ, ?_⟩
  rw [hQc]
  exact Finset.sum_congr rfl fun x _ => by rw [hcost x]

#print axioms orbitCount_eq
#print axioms exists_sym_law
#print axioms sub_mix
#print axioms layer_le_mix
#print axioms layer_le_drop1
#print axioms layer_le_dropc
#print axioms typed_set
#print axioms exists_counts_law

end CIGAMF.P13.PaperCBudgetSym
