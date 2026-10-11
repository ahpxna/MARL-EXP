import «LeanPaperCBudgetAwareV1»
import «LeanPaperCTypedFlowV1»

/-!
# Paper C: the count model of the budget-aware value, and realising a layer law by a ranking

The budget-aware value `B_g(η) = max_{k ∈ K} B_{g,k}(η)` (`LeanPaperCBudgetAwareV1`) is defined
through a law `Q_k` on `k`-subsets whose item marginals are in the band at the ONE budget `k`.
Two things were argued in the manuscript and not formalized; both are proved here.

**Realisation (Limitation 5 of `paper_c.tex`).**  A subset law in the band at budget `k` is the
budget-`k` prefix law of a ranking law that is in the band (eq:band) at EVERY budget.  The
ranking draws `S ~ Q_k`, orders `S` uniformly at random, then orders the complement uniformly
at random (`uniLaw`, `realiseLaw`).  Its item marginal at budget `j` is `(j/k) q_i` for `j ≤ k`
and `q_i + (1 - q_i)(j-k)/(m-k)` for `j ≥ k` (`uniLaw_marginal`), whose distances to `j/m` are
`(j/k)(q_i - k/m)` and `(q_i - k/m)(m-j)/(m-k)` (`band_low`, `band_high`).
* `exists_realisation`: `Q ∈ SubFeasible k η → ∃ P ∈ FeasibleAt id η, pushK P k = Q`.
* `layer_eq_single_budget`: `B_{g,k}(η) = trueValue g η {k}`, the universal value for the single
  budget `k`; `aware_eq_max_single`: `B_g(η) = max_{k ∈ K} U_g^{\{k\}}(η)`.

The uniform order inside `S` is the corpus's own within-type relabelling `symLaw`
(`LeanPaperCFlowBandJoinV1`) for the two-type labelling "in `S`" / "not in `S`", applied to a
point law at a ranking whose first `|S|` items are `S` (`exists_prefix_perm`).

**COUNT = ITEM for a layer (supplement S8, "The numerical panel").**  For a typed multiset
`g = wt ∘ ty` the script `EXP_paperC_budget_recourse.py` solves, per budget, an LP over laws on
count vectors `v` (`v_τ ≤ n_τ`, `Σ v = k`) with the TYPE-marginal band
`|Σ_v x(v) v_τ / n_τ - k/m| ≤ η/m` for `n_τ > 0` (`CountLayerFeasible`) and cost
`(|Σ_τ w_τ v_τ| - b_k)/D` (`typedCost`).
* `subCost_eq_typedCost`: the regret of a set depends on it only through its type counts
  `cstate ty S`; `trueBaseline_eq_count` and `normMass_typed` identify `b_k` and `D` with the
  script's `baseline(w, n, k)` (minimum over admissible count vectors) and `Σ_τ |w_τ| n_τ`.
* `symSub` symmetrises a subset law within types (uniform type-preserving relabelling):
  `symSub_feasible`, `symSub_cost`, `symSub_counts`, `symSub_marginal` (each item marginal
  becomes its type average), `symSub_marginal_const`.
* `push_countFeasible`/`push_countCost` (item to count, by pushing forward the count vector) and
  `lift_feasible`/`lift_cost`/`lift_counts` (count to item: a subset with each count vector,
  then `symSub`).
* `layer_costs_eq_count`: the two programs have the SAME set of achievable costs; hence
  `layer_eq_count : B_{g,k}(η) = countLayerValue` and `aware_eq_count : B_g(η) = max_k` of the
  count layer LP values, which is what `aware_value` computes.
-/

namespace CIGAMF.P13.PaperCCountReduction

open Finset
open CIGAMF.P13.PaperCBudgetAware CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFlowBandJoin
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRelabel CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCFrontier

variable {d m : ℕ}

/-! ## Realisation of a subset law by a ranking law banded at every budget -/

/-- **The band after the prefix, below the budget.** -/
theorem band_low (q k j M η : ℝ) (hj : 0 ≤ j) (hjk : j ≤ k)
    (hq : |q - k / M| ≤ η / M) : |q * (j / k) - j / M| ≤ η / M := by
  have he : 0 ≤ η / M := (abs_nonneg _).trans hq
  rcases eq_or_lt_of_le (hj.trans hjk) with hk0 | hkpos
  · have hj0 : j = 0 := le_antisymm (hjk.trans hk0.symm.le) hj
    rw [hj0]; simpa using he
  · have e : q * (j / k) - j / M = (j / k) * (q - k / M) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg (div_nonneg hj hkpos.le)]
    calc j / k * |q - k / M| ≤ j / k * (η / M) :=
          mul_le_mul_of_nonneg_left hq (div_nonneg hj hkpos.le)
      _ ≤ 1 * (η / M) := mul_le_mul_of_nonneg_right ((div_le_one hkpos).2 hjk) he
      _ = η / M := one_mul _

/-- **The band after the budget**: filling the complement uniformly. -/
theorem band_high (q k j M η : ℝ) (hM : 0 < M) (hkj : k ≤ j) (hjM : j ≤ M)
    (hq : |q - k / M| ≤ η / M) :
    |q + (1 - q) * ((j - k) / (M - k)) - j / M| ≤ η / M := by
  have he : 0 ≤ η / M := (abs_nonneg _).trans hq
  rcases eq_or_lt_of_le (hkj.trans hjM) with hkM | hkM
  · have hj : j = k := le_antisymm (hkM ▸ hjM) hkj
    rw [hj]; simpa using hq
  · have hMk : 0 < M - k := sub_pos.mpr hkM
    have e : q + (1 - q) * ((j - k) / (M - k)) - j / M = (q - k / M) * ((M - j) / (M - k)) := by
      field_simp
      ring
    have h01 : 0 ≤ (M - j) / (M - k) := div_nonneg (by linarith) hMk.le
    have h1 : (M - j) / (M - k) ≤ 1 := (div_le_one hMk).2 (by linarith)
    rw [e, abs_mul, abs_of_nonneg h01]
    calc |q - k / M| * ((M - j) / (M - k)) ≤ (η / M) * ((M - j) / (M - k)) :=
          mul_le_mul_of_nonneg_right hq h01
      _ ≤ (η / M) * 1 := mul_le_mul_of_nonneg_left h1 he
      _ = η / M := mul_one _

theorem card_le_m (S : Finset (Fin m)) : S.card ≤ m := by
  simpa using Finset.card_le_univ S

/-- The budget `|S|`. -/
def cardIdx (S : Finset (Fin m)) : Fin (m + 1) := ⟨S.card, Nat.lt_succ_of_le (card_le_m S)⟩

theorem card_filter_lt (n : ℕ) (hn : n ≤ m) :
    (univ.filter (fun a : Fin m => a.val < n)).card = n := by
  have h := prefixSet_card (1 : Equiv.Perm (Fin m)) ⟨n, Nat.lt_succ_of_le hn⟩
  unfold prefixSet at h
  have e : ∀ x : Fin m, ((1 : Equiv.Perm (Fin m)).symm x) = x := fun x => rfl
  simp only [e] at h
  exact h

/-- **Every subset is the prefix of some ranking.** -/
theorem exists_prefix_perm (S : Finset (Fin m)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ a : Fin m, (σ a ∈ S ↔ a.val < S.card) := by
  classical
  have h1 : Fintype.card {a : Fin m // a.val < S.card} = Fintype.card {a : Fin m // a ∈ S} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, card_filter_lt S.card (card_le_m S)]
    simp
  have h2 : Fintype.card {a : Fin m // ¬ a.val < S.card}
      = Fintype.card {a : Fin m // ¬ a ∈ S} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun a => ?_⟩
  by_cases h : a.val < S.card
  · have hx := ((Fintype.equivOfCardEq h1) ⟨a, h⟩).property
    simp [Equiv.subtypeCongr, h, hx]
  · have hx := ((Fintype.equivOfCardEq h2) ⟨a, h⟩).property
    simpa [Equiv.subtypeCongr, h] using hx

/-- A ranking whose first `|S|` items are `S`. -/
noncomputable def secPerm (S : Finset (Fin m)) : Equiv.Perm (Fin m) :=
  (exists_prefix_perm S).choose

theorem secPerm_prefix (S : Finset (Fin m)) : prefixSet (secPerm S) (cardIdx S) = S := by
  ext i
  have h : secPerm S ((secPerm S).symm i) ∈ S ↔ ((secPerm S).symm i).val < S.card :=
    (exists_prefix_perm S).choose_spec ((secPerm S).symm i)
  rw [Equiv.apply_symm_apply] at h
  unfold prefixSet cardIdx
  rw [Finset.mem_filter]
  exact ⟨fun hh => h.mpr hh.2, fun hh => ⟨mem_univ _, h.mp hh⟩⟩

/-- The two-type labelling "in `S`" / "not in `S`". -/
def inTy (S : Finset (Fin m)) : Fin m → Fin 2 := fun i => if i ∈ S then 0 else 1

theorem inTy_eq_zero (S : Finset (Fin m)) (i : Fin m) : inTy S i = 0 ↔ i ∈ S := by
  unfold inTy; split_ifs with h <;> simp [h]

theorem ty_act (ty : Fin m → Fin d) (ρ : WPerm (typeLabel ty)) (i : Fin m) :
    ty (ρ.val i) = ty i :=
  (typeLabel_eq_iff ty _ _).mp (ρ.property i)

theorem prefixSet_mul (ρ σ : Equiv.Perm (Fin m)) (k : Fin (m + 1)) :
    prefixSet (ρ * σ) k = (prefixSet σ k).map ρ.toEmbedding := by
  ext i
  rw [Finset.mem_map_equiv]
  simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [symm_mul_apply]

theorem map_inTy (S : Finset (Fin m)) (ρ : WPerm (typeLabel (inTy S))) :
    S.map ρ.val.toEmbedding = S := by
  ext i
  rw [Finset.mem_map_equiv, ← inTy_eq_zero, ← inTy_eq_zero]
  have h := ty_act (inTy S) ρ (ρ.val.symm i)
  rw [Equiv.apply_symm_apply] at h
  rw [h]

/-- The point law at a ranking. -/
noncomputable def pointLaw (σ₀ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin m) → ℝ :=
  fun σ => if σ = σ₀ then 1 else 0

theorem pointLaw_ranking (σ₀ : Equiv.Perm (Fin m)) : RankingLaw (pointLaw σ₀) := by
  refine ⟨fun σ => by unfold pointLaw; split_ifs <;> norm_num, ?_⟩
  unfold pointLaw
  simp

theorem pointLaw_expect (σ₀ : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin m) → ℝ) :
    ∑ σ, pointLaw σ₀ σ * f σ = f σ₀ := by
  unfold pointLaw
  simp [ite_mul]

/-- **Uniform order inside `S`, then uniform order outside `S`.** -/
noncomputable def uniLaw (S : Finset (Fin m)) : Equiv.Perm (Fin m) → ℝ :=
  symLaw (inTy S) (pointLaw (secPerm S))

theorem uniLaw_ranking (S : Finset (Fin m)) : RankingLaw (uniLaw S) :=
  symLaw_probability _ _ (pointLaw_ranking _)

/-- **Its budget-`|S|` prefix is `S`, surely.** -/
theorem uniLaw_prefix (S : Finset (Fin m)) (f : Finset (Fin m) → ℝ) :
    ∑ σ, uniLaw S σ * f (prefixSet σ (cardIdx S)) = f S := by
  classical
  have hG : (Fintype.card (WPerm (typeLabel (inTy S))) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniLaw symLaw
  rw [pushLaw_expect, Fintype.sum_prod_type]
  have hin : ∀ ρ : WPerm (typeLabel (inTy S)),
      ∑ σ, pointLaw (secPerm S) σ / (Fintype.card (WPerm (typeLabel (inTy S))) : ℝ)
        * f (prefixSet (ρ.val * σ) (cardIdx S))
        = f S / (Fintype.card (WPerm (typeLabel (inTy S))) : ℝ) := by
    intro ρ
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [pointLaw_expect (secPerm S) (fun σ => f (prefixSet (ρ.val * σ) (cardIdx S))),
      prefixSet_mul, secPerm_prefix, map_inTy]
  rw [Finset.sum_congr rfl (fun ρ _ => hin ρ), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

/-- Prefix counts inside a prefix set. -/
theorem sum_inPrefix_prefix (σ : Equiv.Perm (Fin m)) (c j : ℕ) (hc : c ≤ m) :
    ∑ i ∈ univ.filter (fun i : Fin m => (σ.symm i).val < c), inPrefixInd σ j i
      = (min c j : ℕ) := by
  classical
  unfold inPrefixInd
  rw [Finset.sum_boole, Finset.filter_filter]
  have h := prefixSet_card σ ⟨min c j, Nat.lt_succ_of_le ((min_le_left _ _).trans hc)⟩
  unfold prefixSet at h
  have h' : (univ.filter (fun i : Fin m => (σ.symm i).val < min c j)).card = min c j := h
  rw [← h']
  congr 2
  ext i
  simp [lt_min_iff]

theorem sum_inPrefix_all (σ : Equiv.Perm (Fin m)) (j : ℕ) (hj : j ≤ m) :
    ∑ i, inPrefixInd σ j i = (j : ℝ) := by
  classical
  unfold inPrefixInd
  rw [Finset.sum_boole]
  have h := prefixSet_card σ ⟨j, Nat.lt_succ_of_le hj⟩
  unfold prefixSet at h
  have h' : (univ.filter (fun i : Fin m => (σ.symm i).val < j)).card = j := h
  rw [h']

theorem mult_inTy_in (S : Finset (Fin m)) : mult (inTy S) 0 = S.card := by
  unfold mult
  congr 1
  ext i; simp [inTy_eq_zero]

theorem mult_inTy_out (S : Finset (Fin m)) : mult (inTy S) 1 = m - S.card := by
  have h := mult_sum (inTy S)
  rw [Fin.sum_univ_two, mult_inTy_in] at h
  omega

/-- **The marginals of the uniform order**, inside and outside `S`. -/
theorem uniLaw_marginal (S : Finset (Fin m)) (j : ℕ) (hj : j ≤ m) (i : Fin m) :
    ∑ σ, uniLaw S σ * inPrefixInd σ j i
      = if i ∈ S then ((min S.card j : ℕ) : ℝ) / (S.card : ℝ)
        else ((j : ℝ) - ((min S.card j : ℕ) : ℝ)) / ((m : ℝ) - (S.card : ℝ)) := by
  classical
  have hmarg := symLaw_marginal (inTy S) (pointLaw (secPerm S)) ⟨j, Nat.lt_succ_of_le hj⟩ i
  simp only [pointLaw_expect] at hmarg
  change ∑ σ, uniLaw S σ * inPrefixInd σ j i = _ at hmarg
  rw [hmarg]
  have hS : univ.filter (fun i : Fin m => ((secPerm S).symm i).val < S.card) = S := by
    have := secPerm_prefix S
    unfold prefixSet cardIdx at this
    exact this
  have hin : ∑ i' ∈ S, inPrefixInd (secPerm S) j i' = ((min S.card j : ℕ) : ℝ) := by
    rw [← sum_inPrefix_prefix (secPerm S) S.card j (card_le_m S), hS]
  by_cases hi : i ∈ S
  · simp only [hi, ↓reduceIte]
    have hcl : univ.filter (fun j' => inTy S j' = inTy S i) = S := by
      ext x; simp [(inTy_eq_zero S i).mpr hi, inTy_eq_zero]
    have hti : inTy S i = 0 := (inTy_eq_zero S i).mpr hi
    rw [hcl, hin, hti, mult_inTy_in]
  · simp only [hi, ↓reduceIte]
    have hti : inTy S i = 1 := by unfold inTy; simp [hi]
    have hcl : univ.filter (fun j' => inTy S j' = inTy S i) = univ.filter (fun x => x ∉ S) := by
      ext x; rw [hti]; unfold inTy; by_cases hx : x ∈ S <;> simp [hx]
    have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun x : Fin m => x ∈ S)
      (fun x => inPrefixInd (secPerm S) j x)
    have hSS : univ.filter (fun x : Fin m => x ∈ S) = S := by ext; simp
    rw [sum_inPrefix_all _ j hj, hSS, hin] at hsplit
    rw [hcl, hti, mult_inTy_out, Nat.cast_sub (card_le_m S)]
    congr 1
    linarith

/-- **The realising ranking law**: draw `S ~ Q`, order `S` uniformly, then the rest uniformly. -/
noncomputable def realiseLaw (Q : Finset (Fin m) → ℝ) : Equiv.Perm (Fin m) → ℝ :=
  fun σ => ∑ S, Q S * uniLaw S σ

theorem realise_expect (Q : Finset (Fin m) → ℝ) (f : Equiv.Perm (Fin m) → ℝ) :
    ∑ σ, realiseLaw Q σ * f σ = ∑ S, Q S * ∑ σ, uniLaw S σ * f σ := by
  unfold realiseLaw
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun σ _ => by ring

/-- **Its budget-`k` prefix law is `Q`.** -/
theorem realise_prefix (Q : Finset (Fin m) → ℝ) (k : Fin (m + 1))
    (hsupp : ∀ S, Q S ≠ 0 → S.card = k.val) : pushK (realiseLaw Q) k = Q := by
  funext T
  unfold pushK
  rw [realise_expect Q (fun σ => if prefixSet σ k = T then (1 : ℝ) else 0)]
  have h : ∀ S, Q S * ∑ σ, uniLaw S σ * (if prefixSet σ k = T then (1 : ℝ) else 0)
      = Q S * (if S = T then 1 else 0) := by
    intro S
    by_cases hS : Q S = 0
    · rw [hS, zero_mul, zero_mul]
    · have hk : k = cardIdx S := Fin.ext (hsupp S hS).symm
      rw [hk, uniLaw_prefix S (fun U => if U = T then (1 : ℝ) else 0)]
  rw [Finset.sum_congr rfl fun S _ => h S]
  simp

/-- **Its item marginals are in the band at every budget.** -/
theorem realise_feasible (Q : Finset (Fin m) → ℝ) (k : Fin (m + 1)) (η : ℝ)
    (hQ : Q ∈ SubFeasible k.val η) :
    realiseLaw Q ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η := by
  obtain ⟨hnn, hsum, hsupp, hband⟩ := hQ
  refine ⟨fun σ => Finset.sum_nonneg fun S _ => mul_nonneg (hnn S) ((uniLaw_ranking S).1 σ),
    ?_, ?_⟩
  · have h1 := realise_expect Q (fun _ => 1)
    simp only [mul_one] at h1
    rw [h1, Finset.sum_congr rfl fun S _ => by rw [(uniLaw_ranking S).2, mul_one], hsum]
  · intro j hj i
    simp only [id_eq]
    have hM : (0 : ℝ) < m := by exact_mod_cast (Fin.pos i)
    rw [realise_expect Q (fun σ => inPrefixInd σ j i)]
    simp_rw [uniLaw_marginal _ j hj i]
    have hq := hband i
    rcases le_total j k.val with hjk | hkj
    · have h : ∀ S, Q S * (if i ∈ S then ((min S.card j : ℕ) : ℝ) / (S.card : ℝ)
          else ((j : ℝ) - ((min S.card j : ℕ) : ℝ)) / ((m : ℝ) - (S.card : ℝ)))
          = Q S * ind i S * ((j : ℝ) / (k.val : ℝ)) := by
        intro S
        by_cases hS : Q S = 0
        · simp [hS]
        · have hc := hsupp S hS
          have hmin : min S.card j = j := by omega
          by_cases hi : i ∈ S
          · rw [hmin, hc]
            simp only [hi, ↓reduceIte, ind, mul_one]
          · rw [hmin]
            simp only [hi, ↓reduceIte, ind, sub_self, zero_div, mul_zero, zero_mul]
      rw [Finset.sum_congr rfl fun S _ => h S, ← Finset.sum_mul]
      exact band_low _ _ _ _ _ (Nat.cast_nonneg _) (by exact_mod_cast hjk) hq
    · have h : ∀ S, Q S * (if i ∈ S then ((min S.card j : ℕ) : ℝ) / (S.card : ℝ)
          else ((j : ℝ) - ((min S.card j : ℕ) : ℝ)) / ((m : ℝ) - (S.card : ℝ)))
          = Q S * ind i S + Q S * (1 - ind i S) * (((j : ℝ) - k.val) / ((m : ℝ) - k.val)) := by
        intro S
        by_cases hS : Q S = 0
        · simp [hS]
        · have hc := hsupp S hS
          have hmin : min S.card j = S.card := by omega
          by_cases hi : i ∈ S
          · have hk0 : (S.card : ℝ) ≠ 0 := by
              have : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
              positivity
            rw [hmin]
            simp only [hi, ↓reduceIte, ind, div_self hk0, sub_self, mul_zero, zero_mul, add_zero,
              mul_one]
          · rw [hmin, hc]
            simp only [hi, ↓reduceIte, ind, sub_zero, mul_zero, zero_add, mul_one]
      rw [Finset.sum_congr rfl fun S _ => h S, Finset.sum_add_distrib, ← Finset.sum_mul]
      have hrest : ∑ S, Q S * (1 - ind i S) = 1 - ∑ S, Q S * ind i S := by
        simp_rw [mul_sub, mul_one]
        rw [Finset.sum_sub_distrib, hsum]
      rw [hrest]
      exact band_high _ _ _ _ _ hM (by exact_mod_cast hkj) (by exact_mod_cast hj) hq

/-- **(Realisation.)**  Every subset law at budget `k` in the band is the budget-`k` prefix law
of a ranking law that is in the band at EVERY budget. -/
theorem exists_realisation (Q : Finset (Fin m) → ℝ) (k : Fin (m + 1)) (η : ℝ)
    (hQ : Q ∈ SubFeasible k.val η) :
    ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η, pushK P k = Q :=
  ⟨realiseLaw Q, realise_feasible Q k η hQ, realise_prefix Q k hQ.2.2.1⟩

/-- The achievable layer costs are exactly the achievable single-budget costs of banded
ranking laws. -/
theorem layer_costs_eq_single (g : Fin m → ℝ) (η : ℝ) (k : Fin (m + 1)) :
    (fun Q => ∑ S, Q S * subCost g k S) '' SubFeasible k.val η
      = (fun P => ∑ σ, P σ * normalizedRegret g σ k) ''
          FeasibleAt (id : Equiv.Perm (Fin m) → _) η := by
  ext y
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨P, hP, hPQ⟩ := exists_realisation Q k η hQ
    refine ⟨P, hP, ?_⟩
    show ∑ σ, P σ * normalizedRegret g σ k = ∑ S, Q S * subCost g k S
    rw [← push_cost, hPQ]
  · rintro ⟨P, hP, rfl⟩
    exact ⟨pushK P k, push_feasible P η hP k, push_cost g P k⟩

/-- **The layer value is the single-budget universal value**: `B_{g,k}(η) = U_g^{\{k\}}(η)`. -/
theorem layer_eq_single_budget (g : Fin m → ℝ) (η : ℝ) (k : Fin (m + 1)) :
    layerValue g η k = trueValue g η {k} (Finset.singleton_nonempty k) := by
  unfold layerValue trueValue trueObjective
  simp only [Finset.sup'_singleton]
  rw [layer_costs_eq_single]

/-- **The budget-aware value is the worst single-budget universal value.** -/
theorem aware_eq_max_single (g : Fin m → ℝ) (η : ℝ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) :
    awareValue g η K hK = K.sup' hK (fun k => trueValue g η {k} (Finset.singleton_nonempty k)) := by
  unfold awareValue
  exact Finset.sup'_congr hK rfl fun k _ => layer_eq_single_budget g η k


/-! ## Type counts of a subset -/

/-- The number of items of type `τ` in `S`. -/
def tcount (ty : Fin m → Fin d) (S : Finset (Fin m)) (τ : Fin d) : ℕ :=
  (S.filter (fun i => ty i = τ)).card

theorem tcount_le_mult (ty : Fin m → Fin d) (S : Finset (Fin m)) (τ : Fin d) :
    tcount ty S τ ≤ mult ty τ :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))

theorem mult_le (ty : Fin m → Fin d) (τ : Fin d) : mult ty τ ≤ m := by
  unfold mult
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- **The count vector of a subset.** -/
def cstate (ty : Fin m → Fin d) (S : Finset (Fin m)) : CState d m :=
  fun τ => ⟨tcount ty S τ, Nat.lt_succ_of_le ((tcount_le_mult ty S τ).trans (mult_le ty τ))⟩

theorem cstate_val (ty : Fin m → Fin d) (S : Finset (Fin m)) (τ : Fin d) :
    ((cstate ty S τ : Fin (m + 1)) : ℕ) = tcount ty S τ := rfl

theorem sum_tcount (ty : Fin m → Fin d) (S : Finset (Fin m)) :
    ∑ τ, tcount ty S τ = S.card := by
  unfold tcount
  exact (Finset.card_eq_sum_card_fiberwise (f := ty) (t := univ) (by intro i _; simp)).symm

theorem sum_weight (ty : Fin m → Fin d) (wt : Fin d → ℝ) (S : Finset (Fin m)) :
    ∑ i ∈ S, typedG ty wt i = ∑ τ, wt τ * (tcount ty S τ : ℝ) := by
  rw [← Finset.sum_fiberwise S ty (typedG ty wt)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => show typedG ty wt i = wt τ by
    rw [Finset.mem_filter] at hi; simp [typedG, hi.2])]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rfl

/-- The normaliser of a typed multiset is `Σ_τ |w_τ| n_τ`, the script's `D`. -/
theorem normMass_typed (ty : Fin m → Fin d) (wt : Fin d → ℝ) :
    normMass (typedG ty wt) = ∑ τ, |wt τ| * (mult ty τ : ℝ) :=
  sum_weight ty (fun τ => |wt τ|) univ

/-- **The regret of a set depends on it only through its type counts.** -/
theorem subCost_eq_typedCost (ty : Fin m → Fin d) (wt : Fin d → ℝ) (k : Fin (m + 1))
    (S : Finset (Fin m)) :
    subCost (typedG ty wt) k S = typedCost ty wt k (cstate ty S) := by
  unfold subCost typedCost
  rw [sum_weight]
  rfl

theorem sum_ind_class (ty : Fin m → Fin d) (S : Finset (Fin m)) (τ : Fin d) :
    ∑ i ∈ univ.filter (fun i => ty i = τ), ind i S = (tcount ty S τ : ℝ) := by
  unfold ind tcount
  rw [Finset.sum_boole, Finset.filter_filter]
  congr 2
  ext i
  simp [and_comm]

/-- The count vector of a prefix is the corpus's layer map. -/
theorem cstate_prefix (ty : Fin m → Fin d) (σ : Equiv.Perm (Fin m)) (k : Fin (m + 1)) :
    cstate ty (prefixSet σ k) = rankLayer ty k σ := by
  funext τ
  apply Fin.ext
  have h1 := count_eq_item_sum ty σ k τ
  have h2 := sum_ind_class ty (prefixSet σ k) τ
  simp_rw [← inPrefix_eq_ind] at h2
  have : ((tcount ty (prefixSet σ k) τ : ℕ) : ℝ) = ((rankLayer ty k σ τ : ℕ) : ℝ) := by
    rw [h1, ← h2]
  exact_mod_cast this

/-- The baseline over `k`-sets is the minimum over admissible count vectors, the script's
`baseline(w, n, k)`. -/
def countLayer (ty : Fin m → Fin d) (k : ℕ) : Finset (CState d m) :=
  univ.filter (fun v => (∀ τ, ((v τ : Fin (m + 1)) : ℕ) ≤ mult ty τ) ∧
    ∑ τ, ((v τ : Fin (m + 1)) : ℕ) = k)

theorem cstate_mem (ty : Fin m → Fin d) (S : Finset (Fin m)) :
    cstate ty S ∈ countLayer ty S.card := by
  simp only [countLayer, mem_filter, mem_univ, true_and, cstate_val]
  exact ⟨tcount_le_mult ty S, sum_tcount ty S⟩

theorem countLayer_nonempty (ty : Fin m → Fin d) (k : Fin (m + 1)) :
    (countLayer ty k.val).Nonempty :=
  ⟨cstate ty (prefixSet 1 k), by
    have := cstate_mem ty (prefixSet 1 k)
    rwa [prefixSet_card] at this⟩

/-- **A section**: every admissible count vector is the count vector of a subset. -/
theorem exists_sec (ty : Fin m → Fin d) (v : CState d m)
    (hv : ∀ τ, ((v τ : Fin (m + 1)) : ℕ) ≤ mult ty τ) : ∃ S : Finset (Fin m), cstate ty S = v := by
  classical
  have h : ∀ τ, ∃ t ⊆ univ.filter (fun i => ty i = τ), t.card = ((v τ : Fin (m + 1)) : ℕ) :=
    fun τ => Finset.exists_subset_card_eq (hv τ)
  choose t ht hc using h
  refine ⟨univ.filter (fun i => i ∈ t (ty i)), ?_⟩
  funext τ
  apply Fin.ext
  rw [cstate_val, ← hc τ]
  unfold tcount
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hi, rfl⟩; exact hi
  · intro hi
    have h2 := ht τ hi
    simp only [mem_filter, mem_univ, true_and] at h2
    exact ⟨by rw [h2]; exact hi, h2⟩

theorem card_of_cstate (ty : Fin m → Fin d) (S : Finset (Fin m)) (v : CState d m)
    (h : cstate ty S = v) : S.card = ∑ τ, ((v τ : Fin (m + 1)) : ℕ) := by
  rw [← sum_tcount, ← h]
  rfl

theorem trueBaseline_eq_count (ty : Fin m → Fin d) (wt : Fin d → ℝ) (k : Fin (m + 1)) :
    trueBaseline (typedG ty wt) k = (countLayer ty k.val).inf' (countLayer_nonempty ty k)
      (fun v => |∑ τ, wt τ * (((v τ : Fin (m + 1)) : ℕ) : ℝ)|) := by
  unfold trueBaseline baseline
  apply le_antisymm
  · apply Finset.le_inf'
    intro v hv
    simp only [countLayer, mem_filter, mem_univ, true_and] at hv
    obtain ⟨S, hS⟩ := exists_sec ty v hv.1
    have hcard : S.card = k.val := by rw [card_of_cstate ty S v hS, hv.2]
    have hmem : S ∈ univ.filter (fun S : Finset (Fin m) => S.card = k.val) := by simp [hcard]
    calc _ ≤ |∑ i ∈ S, typedG ty wt i| := Finset.inf'_le _ hmem
      _ = _ := by rw [sum_weight, ← hS]; rfl
  · apply Finset.le_inf'
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    have hmem : cstate ty S ∈ countLayer ty k.val := hS ▸ cstate_mem ty S
    calc _ ≤ |∑ τ, wt τ * (((cstate ty S τ : Fin (m + 1)) : ℕ) : ℝ)| := Finset.inf'_le _ hmem
      _ = |∑ i ∈ S, typedG ty wt i| := by rw [sum_weight]; rfl

/-! ## Symmetrising a subset law within types -/

theorem tcount_map (ty : Fin m → Fin d) (ρ : WPerm (typeLabel ty)) (S : Finset (Fin m))
    (τ : Fin d) : tcount ty (S.map ρ.val.toEmbedding) τ = tcount ty S τ := by
  unfold tcount
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  exact Finset.filter_congr fun i _ => by simp [ty_act]

theorem cstate_map (ty : Fin m → Fin d) (ρ : WPerm (typeLabel ty)) (S : Finset (Fin m)) :
    cstate ty (S.map ρ.val.toEmbedding) = cstate ty S := by
  funext τ
  exact Fin.ext (tcount_map ty ρ S τ)

theorem ind_map (ρ : Equiv.Perm (Fin m)) (S : Finset (Fin m)) (i : Fin m) :
    ind i (S.map ρ.toEmbedding) = ind (ρ.symm i) S := by
  simp only [ind, Finset.mem_map_equiv]

/-- **Averaging over within-type relabellings replaces a value by its type average.** -/
theorem wavg (ty : Fin m → Fin d) (M : Fin m → ℝ) (i : Fin m) :
    (∑ ρ : WPerm (typeLabel ty), M (ρ.val.symm i)) / (Fintype.card (WPerm (typeLabel ty)) : ℝ)
      = (∑ j ∈ univ.filter (fun j => ty j = ty i), M j) / (mult ty (ty i) : ℝ) := by
  have hconst : ∀ j, ty j = ty i →
      ∑ ρ : WPerm (typeLabel ty), M (ρ.val.symm j)
        = ∑ ρ : WPerm (typeLabel ty), M (ρ.val.symm i) := by
    intro j hj
    obtain ⟨c, hc⟩ := wperm_orbit (typeLabel ty) i j ((typeLabel_eq_iff ty i j).2 hj.symm)
    obtain ⟨e, he⟩ := wperm_trans (typeLabel ty) c
    rw [← hc, ← Equiv.sum_comp e (fun ρ : WPerm (typeLabel ty) => M (ρ.val.symm (c.val i)))]
    refine Finset.sum_congr rfl fun c' _ => ?_
    simp only [he c', symm_mul_apply, Equiv.symm_apply_apply]
  have hclass : ∑ j ∈ univ.filter (fun j => ty j = ty i),
        ∑ ρ : WPerm (typeLabel ty), M (ρ.val.symm j)
      = (Fintype.card (WPerm (typeLabel ty)) : ℝ)
          * ∑ j ∈ univ.filter (fun j => ty j = ty i), M j := by
    rw [Finset.sum_comm]
    have hswap : ∀ ρ : WPerm (typeLabel ty),
        ∑ j ∈ univ.filter (fun j => ty j = ty i), M (ρ.val.symm j)
          = ∑ j ∈ univ.filter (fun j => ty j = ty i), M j := by
      intro ρ
      refine Finset.sum_nbij' (fun j => ρ.val.symm j) (fun j => ρ.val j) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        simp only [mem_filter, mem_univ, true_and] at hj ⊢
        have h := ty_act ty ρ (ρ.val.symm j)
        rw [Equiv.apply_symm_apply] at h
        rw [← h, hj]
      · intro j hj
        simp only [mem_filter, mem_univ, true_and] at hj ⊢
        rw [ty_act ty ρ j, hj]
      · intro j _; exact Equiv.apply_symm_apply _ _
      · intro j _; exact Equiv.symm_apply_apply _ _
      · intro j _; rfl
    rw [Finset.sum_congr rfl (fun ρ _ => hswap ρ), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hsum : ∑ j ∈ univ.filter (fun j => ty j = ty i),
        ∑ ρ : WPerm (typeLabel ty), M (ρ.val.symm j)
      = (mult ty (ty i) : ℝ) * ∑ ρ : WPerm (typeLabel ty), M (ρ.val.symm i) := by
    rw [Finset.sum_congr rfl (fun j hj => hconst j (by simpa using hj)), Finset.sum_const,
      nsmul_eq_mul]
    rfl
  have hG : (Fintype.card (WPerm (typeLabel ty)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hM : (mult ty (ty i) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mult_pos_at ty i))
  have key : (∑ ρ : WPerm (typeLabel ty), M (ρ.val.symm i)) * (mult ty (ty i) : ℝ)
      = (∑ j ∈ univ.filter (fun j => ty j = ty i), M j)
          * (Fintype.card (WPerm (typeLabel ty)) : ℝ) := by
    rw [mul_comm, ← hsum, hclass, mul_comm]
  rw [div_eq_div_iff hG hM]
  exact key

/-- **The within-type symmetrisation of a subset law**: relabel by a uniform type-preserving
permutation. -/
noncomputable def symSub (ty : Fin m → Fin d) (Q : Finset (Fin m) → ℝ) : Finset (Fin m) → ℝ :=
  pushLaw (fun z : WPerm (typeLabel ty) × Finset (Fin m) => z.2.map z.1.val.toEmbedding)
    (fun z => Q z.2 / (Fintype.card (WPerm (typeLabel ty)) : ℝ))

theorem symSub_expect (ty : Fin m → Fin d) (Q : Finset (Fin m) → ℝ) (f : Finset (Fin m) → ℝ) :
    ∑ T, symSub ty Q T * f T
      = (∑ ρ : WPerm (typeLabel ty), ∑ S, Q S * f (S.map ρ.val.toEmbedding))
          / (Fintype.card (WPerm (typeLabel ty)) : ℝ) := by
  unfold symSub
  rw [pushLaw_expect, Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun S _ => by ring

theorem symSub_nonneg (ty : Fin m → Fin d) (Q : Finset (Fin m) → ℝ) (hQ : ∀ S, 0 ≤ Q S) :
    ∀ T, 0 ≤ symSub ty Q T :=
  pushLaw_nonneg _ _ fun z => div_nonneg (hQ z.2) (Nat.cast_nonneg _)

/-- Any functional invariant under within-type relabelling has the same expectation. -/
theorem symSub_invariant (ty : Fin m → Fin d) (Q : Finset (Fin m) → ℝ) (f : Finset (Fin m) → ℝ)
    (hf : ∀ (ρ : WPerm (typeLabel ty)) (S : Finset (Fin m)), f (S.map ρ.val.toEmbedding) = f S) :
    ∑ T, symSub ty Q T * f T = ∑ S, Q S * f S := by
  have hG : (Fintype.card (WPerm (typeLabel ty)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [symSub_expect]
  simp_rw [hf]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem symSub_sum (ty : Fin m → Fin d) (Q : Finset (Fin m) → ℝ) :
    ∑ T, symSub ty Q T = ∑ S, Q S := by
  simpa using symSub_invariant ty Q (fun _ => 1) (fun _ _ => rfl)

theorem pushLaw_ne_zero {R S : Type*} [Fintype R] [Fintype S] (f : R → S) (P : R → ℝ) (y : S)
    (h : pushLaw f P y ≠ 0) : ∃ x, f x = y ∧ P x ≠ 0 := by
  classical
  unfold pushLaw at h
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨x, ?_, ?_⟩
  · by_contra hc
    exact hx (by simp [hc])
  · intro h0
    apply hx
    split_ifs <;> simp [h0]

theorem pushLaw_apply {R S : Type*} [Fintype R] [Fintype S] [DecidableEq S] (f : R → S)
    (P : R → ℝ) (y : S) : pushLaw f P y = ∑ x, P x * (if f x = y then 1 else 0) := by
  have h := pushLaw_expect f P (fun y' => if y' = y then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  rw [h]
  simp only [mul_ite, mul_one, mul_zero]

theorem symSub_support (ty : Fin m → Fin d) (Q : Finset (Fin m) → ℝ) (T : Finset (Fin m))
    (h : symSub ty Q T ≠ 0) :
    ∃ (ρ : WPerm (typeLabel ty)) (S : Finset (Fin m)), S.map ρ.val.toEmbedding = T ∧ Q S ≠ 0 := by
  obtain ⟨z, hz, hQz⟩ := pushLaw_ne_zero _ _ _ h
  exact ⟨z.1, z.2, hz, fun h0 => hQz (by simp [h0])⟩

/-- **The item marginal of the symmetrised law is the type average.** -/
theorem symSub_marginal (ty : Fin m → Fin d) (Q : Finset (Fin m) → ℝ) (i : Fin m) :
    ∑ T, symSub ty Q T * ind i T
      = (∑ j ∈ univ.filter (fun j => ty j = ty i), ∑ S, Q S * ind j S) / (mult ty (ty i) : ℝ) := by
  rw [symSub_expect]
  simp_rw [ind_map]
  exact wavg ty (fun j => ∑ S, Q S * ind j S) i

theorem symSub_marginal_const (ty : Fin m → Fin d) (Q : Finset (Fin m) → ℝ) (i j : Fin m)
    (h : ty i = ty j) : ∑ T, symSub ty Q T * ind i T = ∑ T, symSub ty Q T * ind j T := by
  rw [symSub_marginal, symSub_marginal, h]

theorem avg_band (C : Finset (Fin m)) (a : Fin m → ℝ) (t e : ℝ) (hC : 0 < C.card)
    (h : ∀ j ∈ C, |a j - t| ≤ e) : |(∑ j ∈ C, a j) / (C.card : ℝ) - t| ≤ e := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hC
  have heq : (∑ j ∈ C, a j) / (C.card : ℝ) - t = (∑ j ∈ C, (a j - t)) / C.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [heq, abs_div, abs_of_pos hc, div_le_iff₀ hc]
  calc |∑ j ∈ C, (a j - t)| ≤ ∑ j ∈ C, |a j - t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ C, e := Finset.sum_le_sum h
    _ = e * C.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **(Symmetrisation.)**  Symmetrising a band-feasible subset law within types keeps it
band-feasible, keeps its cost and its count law, and equalises item marginals within types. -/
theorem symSub_feasible (ty : Fin m → Fin d) (k : ℕ) (η : ℝ) (Q : Finset (Fin m) → ℝ)
    (hQ : Q ∈ SubFeasible k η) : symSub ty Q ∈ SubFeasible k η := by
  obtain ⟨hnn, hsum, hsupp, hband⟩ := hQ
  refine ⟨symSub_nonneg ty Q hnn, by rw [symSub_sum, hsum], fun T hT => ?_, fun i => ?_⟩
  · obtain ⟨ρ, S, hST, hQS⟩ := symSub_support ty Q T hT
    rw [← hST, Finset.card_map]
    exact hsupp S hQS
  · rw [symSub_marginal]
    exact avg_band _ _ _ _ (mult_pos_at ty i) fun j _ => hband j

theorem symSub_cost (ty : Fin m → Fin d) (wt : Fin d → ℝ) (k : Fin (m + 1))
    (Q : Finset (Fin m) → ℝ) :
    ∑ T, symSub ty Q T * subCost (typedG ty wt) k T = ∑ S, Q S * subCost (typedG ty wt) k S :=
  symSub_invariant ty Q _ fun ρ S => by rw [subCost_eq_typedCost, subCost_eq_typedCost, cstate_map]

theorem symSub_counts (ty : Fin m → Fin d) (Q : Finset (Fin m) → ℝ) :
    pushLaw (cstate ty) (symSub ty Q) = pushLaw (cstate ty) Q := by
  funext v
  rw [pushLaw_apply, pushLaw_apply]
  exact symSub_invariant ty Q _ fun ρ S => by rw [cstate_map]

/-! ## The count layer program of the script, and its equality with the item layer -/

/-- **The layer LP of `EXP_paperC_budget_recourse.py` (`aware_value`)**: a law on count vectors
`v` with `v_τ ≤ n_τ` and `Σ v = k`, and the type-marginal band
`k/m - η/m ≤ Σ_v x(v) v_τ / n_τ ≤ k/m + η/m` for every type with `n_τ > 0`. -/
def CountLayerFeasible (ty : Fin m → Fin d) (k : ℕ) (η : ℝ) : Set (CState d m → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1 ∧
    (∀ v, x v ≠ 0 → (∀ τ, ((v τ : Fin (m + 1)) : ℕ) ≤ mult ty τ) ∧
      ∑ τ, ((v τ : Fin (m + 1)) : ℕ) = k) ∧
    ∀ τ, 0 < mult ty τ →
      |(∑ v, x v * (((v τ : Fin (m + 1)) : ℕ) : ℝ)) / (mult ty τ : ℝ) - (k : ℝ) / m| ≤ η / m}

/-- The value of the count layer LP. -/
noncomputable def countLayerValue (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ)
    (k : Fin (m + 1)) : ℝ :=
  sInf ((fun x => ∑ v, x v * typedCost ty wt k v) '' CountLayerFeasible ty k.val η)

/-- **Item to count**: the count law of a band-feasible subset law is count-feasible. -/
theorem push_countFeasible (ty : Fin m → Fin d) (k : ℕ) (η : ℝ) (Q : Finset (Fin m) → ℝ)
    (hQ : Q ∈ SubFeasible k η) : pushLaw (cstate ty) Q ∈ CountLayerFeasible ty k η := by
  obtain ⟨hnn, hsum, hsupp, hband⟩ := hQ
  refine ⟨pushLaw_nonneg _ _ hnn, by rw [pushLaw_sum, hsum], fun v hv => ?_, fun τ hτ => ?_⟩
  · obtain ⟨S, hS, hQS⟩ := pushLaw_ne_zero _ _ _ hv
    subst hS
    refine ⟨fun τ => tcount_le_mult ty S τ, ?_⟩
    simp only [cstate_val]
    rw [sum_tcount, hsupp S hQS]
  · rw [pushLaw_expect (cstate ty) Q (fun v => (((v τ : Fin (m + 1)) : ℕ) : ℝ))]
    simp only [cstate_val]
    have e : ∀ S, Q S * ((tcount ty S τ : ℕ) : ℝ)
        = ∑ i ∈ univ.filter (fun i => ty i = τ), Q S * ind i S := by
      intro S
      rw [← sum_ind_class, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun S _ => e S, Finset.sum_comm]
    exact avg_band _ _ _ _ hτ fun j _ => hband j

theorem push_countCost (ty : Fin m → Fin d) (wt : Fin d → ℝ) (k : Fin (m + 1))
    (Q : Finset (Fin m) → ℝ) :
    ∑ v, pushLaw (cstate ty) Q v * typedCost ty wt k v = ∑ S, Q S * subCost (typedG ty wt) k S := by
  rw [pushLaw_expect]
  simp_rw [subCost_eq_typedCost]

open scoped Classical in
/-- A subset with a prescribed admissible count vector. -/
noncomputable def secSub (ty : Fin m → Fin d) (v : CState d m) : Finset (Fin m) :=
  if h : ∃ S, cstate ty S = v then h.choose else ∅

theorem secSub_spec (ty : Fin m → Fin d) (v : CState d m)
    (hv : ∀ τ, ((v τ : Fin (m + 1)) : ℕ) ≤ mult ty τ) : cstate ty (secSub ty v) = v := by
  have hex := exists_sec ty v hv
  unfold secSub
  rw [dif_pos hex]
  exact hex.choose_spec

/-- **The lift of a count law**: a subset with each count vector, then uniform relabelling
within types. -/
noncomputable def liftLayer (ty : Fin m → Fin d) (x : CState d m → ℝ) : Finset (Fin m) → ℝ :=
  symSub ty (pushLaw (secSub ty) x)

theorem sec_expect (ty : Fin m → Fin d) (k : ℕ) (η : ℝ) (x : CState d m → ℝ)
    (hx : x ∈ CountLayerFeasible ty k η) (f : Finset (Fin m) → ℝ) (c : CState d m → ℝ)
    (hc : ∀ S, f S = c (cstate ty S)) :
    ∑ S, pushLaw (secSub ty) x S * f S = ∑ v, x v * c v := by
  rw [pushLaw_expect]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : x v = 0
  · rw [hv, zero_mul, zero_mul]
  · rw [hc, secSub_spec ty v (hx.2.2.1 v hv).1]

/-- **Count to item**: the lift is band-feasible, has the same cost, and has count law `x`. -/
theorem lift_feasible (ty : Fin m → Fin d) (k : ℕ) (η : ℝ) (x : CState d m → ℝ)
    (hx : x ∈ CountLayerFeasible ty k η) : liftLayer ty x ∈ SubFeasible k η := by
  obtain ⟨hnn, hsum, hsupp, hband⟩ := hx
  refine ⟨symSub_nonneg ty _ (pushLaw_nonneg _ _ hnn), ?_, fun T hT => ?_, fun i => ?_⟩
  · rw [liftLayer, symSub_sum, pushLaw_sum, hsum]
  · obtain ⟨ρ, S, hST, hQS⟩ := symSub_support ty _ T hT
    obtain ⟨v, hvS, hxv⟩ := pushLaw_ne_zero _ _ _ hQS
    rw [← hST, Finset.card_map, card_of_cstate ty S v (hvS ▸ secSub_spec ty v (hsupp v hxv).1)]
    exact (hsupp v hxv).2
  · rw [liftLayer, symSub_marginal, Finset.sum_comm]
    have e : ∑ S, ∑ j ∈ univ.filter (fun j => ty j = ty i), pushLaw (secSub ty) x S * ind j S
        = ∑ v, x v * (((v (ty i) : Fin (m + 1)) : ℕ) : ℝ) := by
      simp_rw [← Finset.mul_sum, sum_ind_class]
      exact sec_expect ty k η x ⟨hnn, hsum, hsupp, hband⟩ _
        (fun v => (((v (ty i) : Fin (m + 1)) : ℕ) : ℝ)) (fun S => rfl)
    rw [e]
    exact hband (ty i) (mult_pos_at ty i)

theorem lift_cost (ty : Fin m → Fin d) (wt : Fin d → ℝ) (k : Fin (m + 1)) (η : ℝ)
    (x : CState d m → ℝ) (hx : x ∈ CountLayerFeasible ty k.val η) :
    ∑ T, liftLayer ty x T * subCost (typedG ty wt) k T = ∑ v, x v * typedCost ty wt k v := by
  rw [liftLayer, symSub_cost]
  exact sec_expect ty k.val η x hx _
    (typedCost ty wt k) (subCost_eq_typedCost ty wt k)

theorem lift_counts (ty : Fin m → Fin d) (k : ℕ) (η : ℝ) (x : CState d m → ℝ)
    (hx : x ∈ CountLayerFeasible ty k η) : pushLaw (cstate ty) (liftLayer ty x) = x := by
  rw [liftLayer, symSub_counts]
  funext w
  rw [pushLaw_apply]
  rw [sec_expect ty k η x hx (fun S => if cstate ty S = w then (1 : ℝ) else 0)
    (fun v => if v = w then (1 : ℝ) else 0) (fun S => rfl)]
  simp

/-- **COUNT = ITEM for a layer**: the achievable costs of the item layer program and of the
script's count layer LP are the same set. -/
theorem layer_costs_eq_count (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) (k : Fin (m + 1)) :
    (fun Q => ∑ S, Q S * subCost (typedG ty wt) k S) '' SubFeasible k.val η
      = (fun x => ∑ v, x v * typedCost ty wt k v) '' CountLayerFeasible ty k.val η := by
  ext y
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨pushLaw (cstate ty) Q, push_countFeasible ty k.val η Q hQ, push_countCost ty wt k Q⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨liftLayer ty x, lift_feasible ty k.val η x hx, lift_cost ty wt k η x hx⟩

/-- **The layer value is the count layer LP value.** -/
theorem layer_eq_count (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) (k : Fin (m + 1)) :
    layerValue (typedG ty wt) η k = countLayerValue ty wt η k := by
  unfold layerValue countLayerValue
  rw [layer_costs_eq_count]

/-- **The budget-aware value is the script's `aware_value`**: the maximum over the budgets of
the count layer LP values. -/
theorem aware_eq_count (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) :
    awareValue (typedG ty wt) η K hK = K.sup' hK (fun k => countLayerValue ty wt η k) := by
  unfold awareValue
  exact Finset.sup'_congr hK rfl fun k _ => layer_eq_count ty wt η k

#print axioms band_low
#print axioms band_high
#print axioms exists_prefix_perm
#print axioms uniLaw_prefix
#print axioms uniLaw_marginal
#print axioms realise_prefix
#print axioms realise_feasible
#print axioms exists_realisation
#print axioms layer_costs_eq_single
#print axioms layer_eq_single_budget
#print axioms aware_eq_max_single
#print axioms normMass_typed
#print axioms subCost_eq_typedCost
#print axioms cstate_prefix
#print axioms exists_sec
#print axioms trueBaseline_eq_count
#print axioms wavg
#print axioms symSub_marginal
#print axioms symSub_marginal_const
#print axioms symSub_feasible
#print axioms symSub_cost
#print axioms symSub_counts
#print axioms push_countFeasible
#print axioms push_countCost
#print axioms lift_feasible
#print axioms lift_cost
#print axioms lift_counts
#print axioms layer_costs_eq_count
#print axioms layer_eq_count
#print axioms aware_eq_count

end CIGAMF.P13.PaperCCountReduction
