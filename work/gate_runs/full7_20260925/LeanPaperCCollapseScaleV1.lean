import «LeanPaperCRatioJoinV1»

/-!
# Paper C: where the price collapses

`LeanPaperCRatioJoinV1` shows that every perturbation of `ℓ₁` size at most `1/2m` keeps a
linear price.  This module shows the scale is sharp: a single light item moved by `δ`
already brings the physical price ratio down to at most `10/δ`, so a perturbation of size
`δ` in `[1/m, 1]` leaves only `O(1/δ)` of the linear price.  With the matching lower side
`1/(16 ε)` for every perturbation of size `ε` in `[1/m, 1/6]`, the worst-case price ratio is
`Θ(min(m, 1/ε))`: linear exactly while `ε = O(1/m)`.

**The perturbation.**  `gD` moves the light negative at index `1` from `-1` to `-1+δ`.
Parity is what made the free value small: every prefix sum of `g_m` has the parity of its
length, so odd budgets cost at least `1` and even ones can cost `0`, and the per-budget
optimum is exactly `k mod 2`.  After the move the optimum drops to `1-δ` at odd budgets
(take the moved item) and stays `0` at even ones (leave it out).  A ranking then pays `δ` at
every odd budget before the moved item and at every even budget from it on, and each pair of
budgets `(2i+1, 2i+2)` contains one of the two.  So every ranking pays at least
`δ (m-1)/2` in total, and the free value is at least `δ/(2‖g'‖₁)`.
-/

namespace CIGAMF.P13.PaperCCollapseScale

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCFrontier
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCEndpointLaw
open CIGAMF.P13.PaperCStabilityFamily CIGAMF.P13.PaperCRelaxedJoin CIGAMF.P13.PaperCRatioJoin
open CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCBaselineAttain

/-! ## 1. The perturbed family -/

/-- The moved item: index `1`, a light negative. -/
def pI (s : ℕ) : Fin (2 * s + 3) := ⟨1, by omega⟩

theorem pI_mem_negSet (s : ℕ) : pI s ∈ negSet (2 * s + 3) := by
  simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and, pI]
  omega

theorem gFamily_pI (s : ℕ) : gFamily (2 * s + 3) (pI s) = -1 :=
  negSet_value (2 * s + 3) (by omega) (pI s) (pI_mem_negSet s)

/-- The perturbation. -/
noncomputable def gD (s : ℕ) (δ : ℝ) : Fin (2 * s + 3) → ℝ :=
  fun i => gFamily (2 * s + 3) i + (if i = pI s then δ else 0)

theorem sum_gD (s : ℕ) (δ : ℝ) (S : Finset (Fin (2 * s + 3))) :
    ∑ i ∈ S, gD s δ i = ∑ i ∈ S, gFamily (2 * s + 3) i + (if pI s ∈ S then δ else 0) := by
  unfold gD
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']

theorem l1_gD (s : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) : l1 (gFamily (2 * s + 3)) (gD s δ) = δ := by
  unfold l1 gD
  have : ∀ i, |gFamily (2 * s + 3) i - (gFamily (2 * s + 3) i + (if i = pI s then δ else 0))|
      = if i = pI s then δ else 0 := by
    intro i
    by_cases h : i = pI s
    · rw [if_pos h, show gFamily (2 * s + 3) i - (gFamily (2 * s + 3) i + δ) = -δ
        by ring, abs_neg, abs_of_nonneg hδ]
    · rw [if_neg h]; simp
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_ite_eq']
  simp

theorem normMass_gD (s : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    normMass (gD s δ) = ((2 * s + 3 : ℕ) : ℝ) + 4 - δ := by
  have hbase := CIGAMF.P13.PaperCBaselineAttain.normMass_gFamily (2 * s + 3) (by omega)
  unfold normMass at hbase ⊢
  have h1 := Finset.add_sum_erase (univ : Finset (Fin (2 * s + 3))) (fun i => |gD s δ i|)
    (Finset.mem_univ (pI s))
  have h2 := Finset.add_sum_erase (univ : Finset (Fin (2 * s + 3)))
    (fun i => |gFamily (2 * s + 3) i|) (Finset.mem_univ (pI s))
  have hrest : ∑ i ∈ univ.erase (pI s), |gD s δ i|
      = ∑ i ∈ univ.erase (pI s), |gFamily (2 * s + 3) i| := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    unfold gD; rw [if_neg (Finset.ne_of_mem_erase hi), add_zero]
  have hp : |gD s δ (pI s)| = 1 - δ := by
    unfold gD; rw [if_pos rfl, gFamily_pI, abs_of_nonpos (by linarith)]; ring
  have hq : |gFamily (2 * s + 3) (pI s)| = 1 := by rw [gFamily_pI]; norm_num
  rw [← h1, hrest, hp]
  rw [hq] at h2
  linarith

/-! ## 2. The per-budget optimum after the move -/

theorem baseline_gD_le (s : ℕ) (δ : ℝ) (S : Finset (Fin (2 * s + 3))) (k : Fin (2 * s + 3 + 1))
    (hS : S.card = k.val) : trueBaseline (gD s δ) k ≤ |∑ i ∈ S, gD s δ i| := by
  unfold trueBaseline baseline
  exact Finset.inf'_le _ (by simp [hS])

theorem baseline_odd (s : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : Fin (2 * s + 3 + 1))
    (hk1 : 1 ≤ k.val) (hk : k.val ≤ 2 * s + 1) (hodd : k.val % 2 = 1) :
    trueBaseline (gD s δ) k ≤ 1 - δ := by
  classical
  have hm : 3 ≤ 2 * s + 3 := by omega
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq
    (show k.val / 2 ≤ ((negSet (2 * s + 3)).erase (pI s)).card by
      rw [Finset.card_erase_of_mem (pI_mem_negSet s), negSet_card _ hm]; omega)
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq
    (show k.val / 2 ≤ (posSet (2 * s + 3)).card by rw [posSet_card _ hm]; omega)
  have hpA : pI s ∉ A := fun h => by
    have := hAsub h; simp at this
  have hAneg : A ⊆ negSet (2 * s + 3) := hAsub.trans (Finset.erase_subset _ _)
  have hdisj : Disjoint (insert (pI s) A) B := by
    rw [Finset.disjoint_insert_left]
    refine ⟨fun h => ?_, Disjoint.mono hAneg hBsub (negSet_disjoint_posSet _)⟩
    exact Finset.disjoint_left.mp (negSet_disjoint_posSet _) (pI_mem_negSet s) (hBsub h)
  refine (baseline_gD_le s δ (insert (pI s) A ∪ B) k ?_).trans (le_of_eq ?_)
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem hpA, hAcard, hBcard]
    omega
  · rw [sum_gD, if_pos (Finset.mem_union_left _ (Finset.mem_insert_self _ _)),
      Finset.sum_union hdisj, Finset.sum_insert hpA, gFamily_pI,
      sum_const_on_subset _ A (-1) (fun i hi => negSet_value _ hm i (hAneg hi)),
      sum_const_on_subset _ B 1 (fun i hi => posSet_value _ hm i (hBsub hi)), hAcard, hBcard]
    rw [show (-1 : ℝ) + ((k.val / 2 : ℕ) : ℝ) * (-1) + ((k.val / 2 : ℕ) : ℝ) * 1 + δ
        = -(1 - δ) by ring, abs_neg, abs_of_nonneg (by linarith)]

theorem baseline_even (s : ℕ) (δ : ℝ) (k : Fin (2 * s + 3 + 1))
    (hk1 : 1 ≤ k.val) (hk : k.val ≤ 2 * s + 2) (heven : k.val % 2 = 0) :
    trueBaseline (gD s δ) k ≤ 0 := by
  classical
  have hm : 3 ≤ 2 * s + 3 := by omega
  rcases Nat.lt_or_ge k.val (2 * s + 2) with hlt | hge
  · obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq
      (show k.val / 2 ≤ ((negSet (2 * s + 3)).erase (pI s)).card by
        rw [Finset.card_erase_of_mem (pI_mem_negSet s), negSet_card _ hm]; omega)
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq
      (show k.val / 2 ≤ (posSet (2 * s + 3)).card by rw [posSet_card _ hm]; omega)
    have hAneg : A ⊆ negSet (2 * s + 3) := hAsub.trans (Finset.erase_subset _ _)
    have hdisj : Disjoint A B := Disjoint.mono hAneg hBsub (negSet_disjoint_posSet _)
    have hpS : pI s ∉ A ∪ B := by
      rw [Finset.mem_union, not_or]
      refine ⟨fun h => by have := hAsub h; simp at this, fun h => ?_⟩
      exact Finset.disjoint_left.mp (negSet_disjoint_posSet _) (pI_mem_negSet s) (hBsub h)
    refine (baseline_gD_le s δ (A ∪ B) k ?_).trans (le_of_eq ?_)
    · rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]; omega
    · rw [sum_gD, if_neg hpS, Finset.sum_union hdisj,
        sum_const_on_subset _ A (-1) (fun i hi => negSet_value _ hm i (hAneg hi)),
        sum_const_on_subset _ B 1 (fun i hi => posSet_value _ hm i (hBsub hi)), hAcard, hBcard]
      simp
  · have hk2 : k.val = 2 * s + 2 := by omega
    have hfam : IsOddFamily (gFamily (2 * s + 3)) := by
      have := gFamily_isOddFamily (2 * s + 1) (by omega) (by omega)
      rwa [show 2 * s + 1 + 2 = 2 * s + 3 from by omega] at this
    refine (baseline_gD_le s δ ((univ : Finset (Fin (2 * s + 3))).erase (pI s)) k ?_).trans
      (le_of_eq ?_)
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    · rw [sum_gD, if_neg (Finset.notMem_erase _ _)]
      have htot := hfam.total
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (pI s)), gFamily_pI] at htot
      rw [show ∑ i ∈ univ.erase (pI s), gFamily (2 * s + 3) i = 0 by linarith]
      simp

/-! ## 3. Every ranking pays `δ` on half the budgets -/

theorem prefix_gD (s : ℕ) (δ : ℝ) (σ : Equiv.Perm (Fin (2 * s + 3))) (k : Fin (2 * s + 3 + 1)) :
    ∑ i ∈ prefixSet σ k, gD s δ i
      = prefixSum (rankOf (gFamily (2 * s + 3)) σ) k.val
        + (if pI s ∈ prefixSet σ k then δ else 0) := by
  classical
  rw [sum_gD]
  congr 1
  unfold prefixSet prefixSum rankOf
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Equiv.sum_comp σ
      (fun i => if ((σ.symm i : Fin (2 * s + 3)) : ℕ) < k.val then gFamily (2 * s + 3) i else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.symm_apply_apply]

/-- The budgets where a ranking must pay: odd ones before the moved item, even ones from it
on. -/
noncomputable def pays (j0 n : ℕ) : ℝ :=
  if (n % 2 = 1 ∧ ¬ j0 < n) ∨ (n % 2 = 0 ∧ j0 < n) then 1 else 0

theorem raw_ge_pays (s : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (σ : Equiv.Perm (Fin (2 * s + 3))) (k : Fin (2 * s + 3 + 1))
    (hk1 : 1 ≤ k.val) (hk : k.val ≤ 2 * s + 2) :
    δ * pays (σ.symm (pI s)).val k.val ≤ rawRegret (gD s δ) σ k := by
  classical
  have hmem : pI s ∈ prefixSet σ k ↔ (σ.symm (pI s)).val < k.val := by
    simp [prefixSet]
  have hw : ∀ i, rankOf (gFamily (2 * s + 3)) σ i = -3 ∨ rankOf (gFamily (2 * s + 3)) σ i = -1
      ∨ rankOf (gFamily (2 * s + 3)) σ i = 1 ∨ rankOf (gFamily (2 * s + 3)) σ i = 3 :=
    fun i => gFamily_weights _ (σ i)
  obtain ⟨j, hj⟩ := prefixSum_parity (rankOf (gFamily (2 * s + 3)) σ) hw k.val (by omega)
  have hraw0 := (raw_bounds (gD s δ) σ k).1
  unfold pays
  by_cases hc : (k.val % 2 = 1 ∧ ¬ (σ.symm (pI s)).val < k.val)
      ∨ (k.val % 2 = 0 ∧ (σ.symm (pI s)).val < k.val)
  · rw [if_pos hc, mul_one]
    unfold rawRegret
    rw [prefix_gD]
    rcases hc with ⟨hodd, hnot⟩ | ⟨heven, hin⟩
    · rw [if_neg (fun h => hnot (hmem.mp h)), add_zero]
      have hb := baseline_odd s δ hδ0 hδ1 k hk1 (by omega) hodd
      have h1 := one_le_abs_prefixSum_of_odd (rankOf (gFamily (2 * s + 3)) σ) hw k.val
        (by omega) hodd
      linarith
    · rw [if_pos (hmem.mpr hin)]
      have hb := baseline_even s δ k hk1 hk heven
      rw [hj, heven]
      push_cast
      rw [add_zero]
      have hjc : (j : ℝ) = 0 ∨ 1 ≤ (j : ℝ) ∨ (j : ℝ) ≤ -1 := by
        rcases lt_trichotomy j 0 with h | h | h
        · right; right; exact_mod_cast (show j ≤ -1 by omega)
        · left; exact_mod_cast h
        · right; left; exact_mod_cast (show 1 ≤ j by omega)
      rcases hjc with h0 | h1 | h1
      · rw [h0, mul_zero, zero_add, abs_of_nonneg hδ0]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [if_neg hc, mul_zero]; exact hraw0

/-- Each pair of budgets `(2i+1, 2i+2)` holds a paying one. -/
theorem pays_pairs (j0 t : ℕ) : (t : ℝ) ≤ ∑ n ∈ range (2 * t), pays j0 (n + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 from by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have hpair : 1 ≤ pays j0 (2 * t + 1) + pays j0 (2 * t + 1 + 1) := by
        unfold pays
        by_cases h : j0 < 2 * t + 1
        · rw [if_pos (show ((2 * t + 1 + 1) % 2 = 1 ∧ ¬ j0 < 2 * t + 1 + 1)
              ∨ ((2 * t + 1 + 1) % 2 = 0 ∧ j0 < 2 * t + 1 + 1) from Or.inr ⟨by omega, by omega⟩)]
          split_ifs <;> norm_num
        · rw [if_pos (show ((2 * t + 1) % 2 = 1 ∧ ¬ j0 < 2 * t + 1)
              ∨ ((2 * t + 1) % 2 = 0 ∧ j0 < 2 * t + 1) from Or.inl ⟨by omega, h⟩)]
          split_ifs <;> norm_num
      push_cast
      linarith

/-- Sums over the interior budgets, as sums over `ℕ`. -/
theorem sum_interiorK (s : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ interiorK (2 * s + 3), F k.val = ∑ n ∈ range (2 * s + 2), F (n + 1) := by
  unfold interiorK
  rw [Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun n => if 1 ≤ n ∧ n ≤ 2 * s + 3 - 1 then F n else 0)
      (2 * s + 3 + 1)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  rw [if_neg (show ¬ (1 ≤ 2 * s + 3 ∧ 2 * s + 3 ≤ 2 * s + 3 - 1) by omega),
    if_neg (show ¬ (1 ≤ 0 ∧ 0 ≤ 2 * s + 3 - 1) by omega), add_zero, add_zero]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have := Finset.mem_range.mp hn
  rw [if_pos (by omega)]

theorem card_interiorK (s : ℕ) : ((interiorK (2 * s + 3)).card : ℝ) = 2 * (s : ℝ) + 2 := by
  have h := sum_interiorK s (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range] at h
  rw [h]; push_cast; ring

/-! ## 4. The free value after the move is at least `δ/(2‖g'‖₁)` -/

theorem objective_gD_ge (s : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (P : Equiv.Perm (Fin (2 * s + 3)) → ℝ) (hP : ∀ σ, 0 ≤ P σ) (hP1 : ∑ σ, P σ = 1) :
    δ / (2 * normMass (gD s δ))
      ≤ trueObjective (gD s δ) P (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega)) := by
  have hNM : normMass (gD s δ) = ((2 * s + 3 : ℕ) : ℝ) + 4 - δ := normMass_gD s δ hδ0 hδ1
  have hNMpos : 0 < normMass (gD s δ) := by rw [hNM]; push_cast; linarith
  set K := interiorK (2 * s + 3)
  set E : Fin (2 * s + 3 + 1) → ℝ := fun k => ∑ σ, P σ * normalizedRegret (gD s δ) σ k
  have hsup : ∀ k ∈ K, E k ≤ trueObjective (gD s δ) P K (interiorK_nonempty _ (by omega)) :=
    fun k hk => Finset.le_sup' E hk
  have hsum_le : ∑ k ∈ K, E k ≤ (2 * (s : ℝ) + 2)
      * trueObjective (gD s δ) P K (interiorK_nonempty _ (by omega)) := by
    calc ∑ k ∈ K, E k ≤ ∑ _k ∈ K, trueObjective (gD s δ) P K (interiorK_nonempty _ (by omega)) :=
          Finset.sum_le_sum hsup
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_interiorK]
  have hper : ∀ σ, δ * ((s : ℝ) + 1) / normMass (gD s δ)
      ≤ ∑ k ∈ K, normalizedRegret (gD s δ) σ k := by
    intro σ
    have hpt : ∀ k ∈ K, δ * pays (σ.symm (pI s)).val k.val / normMass (gD s δ)
        ≤ normalizedRegret (gD s δ) σ k := by
      intro k hk
      have hk' : 1 ≤ k.val ∧ k.val ≤ 2 * s + 2 := by simp [K, interiorK] at hk; omega
      unfold normalizedRegret
      exact div_le_div_of_nonneg_right (raw_ge_pays s δ hδ0 hδ1 σ k hk'.1 hk'.2) hNMpos.le
    refine le_trans ?_ (Finset.sum_le_sum hpt)
    rw [← Finset.sum_div, ← Finset.mul_sum,
      sum_interiorK s (fun n => pays (σ.symm (pI s)).val n)]
    have hc := pays_pairs (σ.symm (pI s)).val (s + 1)
    rw [show 2 * (s + 1) = 2 * s + 2 from by ring] at hc
    push_cast at hc
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc hδ0) hNMpos.le
  have hswap : ∑ k ∈ K, E k = ∑ σ, P σ * ∑ k ∈ K, normalizedRegret (gD s δ) σ k := by
    simp only [E, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hmass : δ * ((s : ℝ) + 1) / normMass (gD s δ) ≤ ∑ k ∈ K, E k := by
    rw [hswap]
    calc δ * ((s : ℝ) + 1) / normMass (gD s δ)
        = ∑ σ, P σ * (δ * ((s : ℝ) + 1) / normMass (gD s δ)) := by
          rw [← Finset.sum_mul, hP1, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hper σ) (hP σ))
  have hs2 : (0 : ℝ) < 2 * (s : ℝ) + 2 := by positivity
  have key : δ * ((s : ℝ) + 1) / normMass (gD s δ) ≤ (2 * (s : ℝ) + 2)
      * trueObjective (gD s δ) P K (interiorK_nonempty _ (by omega)) := hmass.trans hsum_le
  rw [div_le_iff₀ (by positivity)]
  have k2 := (div_le_iff₀ hNMpos).mp key
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  apply le_of_mul_le_mul_left _ hs1
  linarith [k2]

theorem value_gD_ge (s : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (η : ℝ) (hη : 0 ≤ η) :
    δ / (2 * normMass (gD s δ))
      ≤ trueValue (gD s δ) η (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega)) := by
  have : NeZero (2 * s + 3) := ⟨by omega⟩
  apply le_csInf ((allPerm_feasible_nonempty (2 * s + 3) η hη).image _)
  rintro _ ⟨P, hP, rfl⟩
  exact objective_gD_ge s δ hδ0 hδ1 P hP.1 hP.2.1

/-! ## 5. The collapse, and the matching lower side -/

/-- **One light item moved by `δ` leaves at most `10/δ` of the price.** -/
theorem collapse_upper (s : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    l1 (gFamily (2 * s + 3)) (gD s δ) = δ
      ∧ 0 < trueValue (gD s δ) ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
          (interiorK_nonempty _ (by omega))
      ∧ trueValue (gD s δ) 0 (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega))
          / trueValue (gD s δ) ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
              (interiorK_nonempty _ (by omega)) ≤ 10 / δ := by
  have hm : 3 ≤ 2 * s + 3 := by omega
  have hmo : (2 * s + 3) % 2 = 1 := by omega
  set M : ℝ := ((2 * s + 3 : ℕ) : ℝ) with hMdef
  have hM3 : (3 : ℝ) ≤ M := by rw [hMdef]; push_cast; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  have hl1 := l1_gD s δ hδ0.le
  have hNM := normMass_gD s δ hδ0.le hδ1
  set d := M + 4 - δ with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have h0 := family_value_robust (2 * s + 3) hm (gD s δ) 0 le_rfl d hdpos (by rw [hd]; linarith)
    (by rw [hNM])
  rw [odd_zero_value (2 * s + 3) hm hmo, hl1] at h0
  have hup0 := (abs_le.mp h0).2
  have hlowM := value_gD_ge s δ hδ0.le hδ1 M (by linarith)
  rw [hNM] at hlowM
  have hbpos : 0 < δ / (2 * d) := by positivity
  refine ⟨hl1, lt_of_lt_of_le hbpos hlowM, ?_⟩
  have htvM : 0 < trueValue (gD s δ) M (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega)) :=
    lt_of_lt_of_le hbpos hlowM
  set V0 := (M + 3) / (M * (M + 4)) with hV0
  have hV0pos : 0 < V0 := by rw [hV0]; positivity
  have hnum : 0 ≤ V0 + 3 * δ / d := by positivity
  calc _ ≤ (V0 + 3 * δ / d)
          / trueValue (gD s δ) M (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega)) :=
        div_le_div_of_nonneg_right (by linarith) htvM.le
    _ ≤ (V0 + 3 * δ / d) / (δ / (2 * d)) := div_le_div_of_nonneg_left hnum hbpos hlowM
    _ = (2 * d * V0 + 6 * δ) / δ := by field_simp; ring
    _ ≤ 10 / δ := by
        apply div_le_div_of_nonneg_right _ hδ0.le
        have h2dV : 2 * d * V0 ≤ 4 := by
          rw [hV0, hd]
          rw [show 2 * (M + 4 - δ) * ((M + 3) / (M * (M + 4)))
              = 2 * (M + 4 - δ) * (M + 3) / (M * (M + 4)) by ring]
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        linarith

theorem collapse_arith (x e : ℝ) (hx : 3 ≤ x) (he1 : 1 / x ≤ e) (he2 : e ≤ 1 / 6) :
    1 / (16 * e) ≤ ((x + 3) / (x * (x + 4)) - 3 * e / (x + 3))
      / (2 / ((x + 4) * (x - 1)) + 3 * e / (x + 3)) := by
  have hx0 : 0 < x := by linarith
  have he : 0 < e := lt_of_lt_of_le (by positivity) he1
  have hxe : 1 ≤ x * e := by rwa [div_le_iff₀ hx0, mul_comm] at he1
  have hnum : 5 / (12 * (x + 4)) ≤ (x + 3) / (x * (x + 4)) - 3 * e / (x + 3) := by
    have a1 : 1 / (x + 4) ≤ (x + 3) / (x * (x + 4)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have a2 : 3 * e / (x + 3) ≤ 7 / (12 * (x + 4)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have a3 : 1 / (x + 4) - 7 / (12 * (x + 4)) = 5 / (12 * (x + 4)) := by
      field_simp; ring
    linarith
  have hden : 2 / ((x + 4) * (x - 1)) + 3 * e / (x + 3) ≤ 13 * e / (2 * (x + 4)) := by
    have b1 : 2 / ((x + 4) * (x - 1)) ≤ 3 * e / (x + 4) := by
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]; nlinarith
    have b2 : 3 * e / (x + 3) ≤ 7 * e / (2 * (x + 4)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have b3 : 3 * e / (x + 4) + 7 * e / (2 * (x + 4)) = 13 * e / (2 * (x + 4)) := by
      field_simp; ring
    linarith
  have hdenpos : 0 < 2 / ((x + 4) * (x - 1)) + 3 * e / (x + 3) := by
    have : 0 < 2 / ((x + 4) * (x - 1)) := by apply div_pos (by norm_num); nlinarith
    positivity
  rw [div_le_div_iff₀ (by positivity) hdenpos, one_mul]
  have c1 : 13 * e / (2 * (x + 4)) ≤ 5 / (12 * (x + 4)) * (16 * e) := by
    rw [show 5 / (12 * (x + 4)) * (16 * e) = 80 * e / (12 * (x + 4)) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have c2 : 5 / (12 * (x + 4)) * (16 * e)
      ≤ ((x + 3) / (x * (x + 4)) - 3 * e / (x + 3)) * (16 * e) :=
    mul_le_mul_of_nonneg_right hnum (by positivity)
  linarith

/-- **The matching lower side**: every perturbation of size `ε` in `[1/m, 1/6]` with a
positive perturbed free value keeps a price ratio of at least `1/(16 ε)`. -/
theorem collapse_lower (s : ℕ) (g' : Fin (2 * s + 3) → ℝ)
    (hε1 : 1 / ((2 * s + 3 : ℕ) : ℝ) ≤ l1 (gFamily (2 * s + 3)) g')
    (hε2 : l1 (gFamily (2 * s + 3)) g' ≤ 1 / 6)
    (hpos : 0 < trueValue g' ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
      (interiorK_nonempty _ (by omega))) :
    1 / (16 * l1 (gFamily (2 * s + 3)) g')
      ≤ trueValue g' 0 (interiorK (2 * s + 3)) (interiorK_nonempty _ (by omega))
        / trueValue g' ((2 * s + 3 : ℕ) : ℝ) (interiorK (2 * s + 3))
            (interiorK_nonempty _ (by omega)) := by
  have hm : 3 ≤ 2 * s + 3 := by omega
  have hmo : (2 * s + 3) % 2 = 1 := by omega
  set M : ℝ := ((2 * s + 3 : ℕ) : ℝ) with hMdef
  have hM3 : (3 : ℝ) ≤ M := by rw [hMdef]; push_cast; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  set ε := l1 (gFamily (2 * s + 3)) g'
  have hg' : M + 3 ≤ normMass g' := by
    have := normMass_ge (gFamily (2 * s + 3)) g'
    rw [CIGAMF.P13.PaperCRatioJoin.normMass_gFamily (2 * s + 3) hm] at this
    linarith
  have hsmall : 3 * ε / (M + 3) ≤ (M + 3) / (M * (M + 4)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hε2 (by positivity : (0 : ℝ) ≤ M * (M + 4))]
  have hr := physical_price_ratio (2 * s + 3) hm hmo g' (M + 3) (by positivity) (by linarith)
    hg' hpos hsmall
  refine le_trans ?_ hr
  have hF : freeValue (2 * s + 3) = 2 / ((M + 4) * (M - 1)) := by
    unfold freeValue denom; rw [hMdef]
  rw [hF]
  exact collapse_arith M ε hM3 hε1 hε2

end CIGAMF.P13.PaperCCollapseScale

#print axioms CIGAMF.P13.PaperCCollapseScale.value_gD_ge
#print axioms CIGAMF.P13.PaperCCollapseScale.collapse_upper
#print axioms CIGAMF.P13.PaperCCollapseScale.collapse_lower
