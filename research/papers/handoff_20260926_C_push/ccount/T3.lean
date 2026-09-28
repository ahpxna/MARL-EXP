import «LeanPaperCBudgetAwareV1»
import «LeanPaperCTypedFlowV1»

namespace CIGAMF.P13.PaperCCountReduction

open Finset
open CIGAMF.P13.PaperCBudgetAware CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFlowBandJoin
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRelabel CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCFlowLaw

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
theorem sum_inPrefix_prefix (σ : Equiv.Perm (Fin m)) (c j : ℕ) (hc : c ≤ m) (hj : j ≤ m) :
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
    rw [← sum_inPrefix_prefix (secPerm S) S.card j (card_le_m S) hj, hS]
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

end CIGAMF.P13.PaperCCountReduction
