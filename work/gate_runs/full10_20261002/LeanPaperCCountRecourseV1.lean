import «LeanPaperCCountReductionV1»

/-!
# Paper C: the count model of recourse, and lifting count transports to item exchanges

`V_g^{(R)}(η)` (`recourseValue`, `LeanPaperCBudgetAwareV1`) is defined over ITEM plans: a
band-feasible ranking law `P` and, at each budget `k ∈ K`, a joint law `J(σ, T)` with ranking
marginal `P`, final `k`-sets `T` at most `R` exchanges from the prefix, and final item
marginals in the band.  `EXP_paperC_budget_recourse.py` (`recourse_value`) solves a COUNT
program instead: the banded count flow of `U_g` and, at each budget, a transport `z_k(v, u)`
from prefix count vectors `v` to final count vectors `u` with `|v - u|_1 // 2 ≤ R`, the
type-marginal band on the final law, and the final regret (`CountTransport`,
`countRecourseSet`).  The supplement said the lift of a count transport to item exchanges was
not formalized.  It is proved here, in both directions.

* `countDist_half`: for two count vectors of the same size, `|v - u|_1 / 2` is the excess
  `Σ_τ (v_τ - u_τ)_+`, so the script's integer division is exact.
* `exists_nested`, `nest_spec`: a final set with prescribed counts `u` that removes exactly
  `Σ_τ (v_τ - u_τ)_+` items of a set with counts `v`; `countDist_le`: conversely two equal-size
  sets differ by at least half the L1 distance of their count vectors.
* **Lift** (`lift_plan`, `lift_mem`): the flow's own ranking law `flowLaw`, the transport
  drawn given the prefix counts, the nested final set, then the SAME uniform type-preserving
  relabelling of the ranking and the final set (`symPlan`).  The ranking marginal is
  `bandFlowLaw ty F` (band-feasible by `bandFlowLaw_feasible`), exchanges are unchanged by
  relabelling, final item marginals become type averages (`symPlan_marginal`), and the cost is
  the transport's cost.
* **Projection** (`proj_transport`, `proj_mem`): the ranking law's flow `rankingFlow` and the
  joint law of (prefix counts, final counts) of an item plan (`zProj`).
* `recourse_sets_eq`: the two programs have the SAME set of achievable worst-budget costs, so
  `recourse_eq_count : V_g^{(R)}(η) = countRecourseValue`, i.e. the script's recourse numbers
  are values of the item model, not only of the typed model (up to the LP solver's floating
  point).  `countRecourse_nonempty`: the program is feasible for `η ≥ 0`.

The count flow here is the corpus's `LayeredFlow` with `CountFeasibleH ∧ FlowBand`, the same
object `typed_flow_equivalence` identifies with the flow LP of `U_g`.
-/

namespace CIGAMF.P13.PaperCCountRecourse

open Finset
open CIGAMF.P13.PaperCBudgetAware CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFlowBandJoin
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRelabel CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCNaming CIGAMF.P13.PaperCCountReduction CIGAMF.P13.PaperCFlow

variable {d m : ℕ}

/-! ## 1. Exchanges between count vectors -/

/-- The script's `sum(abs(a - c) for a, c in zip(v, u))`. -/
def countDist (v u : CState d m) : ℕ :=
  ∑ τ, Int.natAbs ((((v τ : Fin (m + 1)) : ℕ) : ℤ) - (((u τ : Fin (m + 1)) : ℕ) : ℤ))

/-- **Half the L1 distance of two count vectors of the same size is the excess.** -/
theorem countDist_half (v u : CState d m)
    (h : ∑ τ, ((v τ : Fin (m + 1)) : ℕ) = ∑ τ, ((u τ : Fin (m + 1)) : ℕ)) :
    countDist v u / 2 = ∑ τ, (((v τ : Fin (m + 1)) : ℕ) - ((u τ : Fin (m + 1)) : ℕ)) := by
  have k1 : ∀ τ, Int.natAbs ((((v τ : Fin (m + 1)) : ℕ) : ℤ) - (((u τ : Fin (m + 1)) : ℕ) : ℤ))
      = (((v τ : Fin (m + 1)) : ℕ) - ((u τ : Fin (m + 1)) : ℕ))
        + (((u τ : Fin (m + 1)) : ℕ) - ((v τ : Fin (m + 1)) : ℕ)) := fun τ => by omega
  have k2 : ∀ τ, (((v τ : Fin (m + 1)) : ℕ) - ((u τ : Fin (m + 1)) : ℕ)) + ((u τ : Fin (m + 1)) : ℕ)
      = (((u τ : Fin (m + 1)) : ℕ) - ((v τ : Fin (m + 1)) : ℕ)) + ((v τ : Fin (m + 1)) : ℕ) :=
    fun τ => by omega
  have hs : ∑ τ, (((v τ : Fin (m + 1)) : ℕ) - ((u τ : Fin (m + 1)) : ℕ))
        + ∑ τ, ((u τ : Fin (m + 1)) : ℕ)
      = ∑ τ, (((u τ : Fin (m + 1)) : ℕ) - ((v τ : Fin (m + 1)) : ℕ))
        + ∑ τ, ((v τ : Fin (m + 1)) : ℕ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => k2 τ
  rw [h] at hs
  have hs2 : ∑ τ, (((u τ : Fin (m + 1)) : ℕ) - ((v τ : Fin (m + 1)) : ℕ))
      = ∑ τ, (((v τ : Fin (m + 1)) : ℕ) - ((u τ : Fin (m + 1)) : ℕ)) := by omega
  unfold countDist
  rw [Finset.sum_congr rfl fun τ _ => k1 τ, Finset.sum_add_distrib, hs2]
  omega

/-- A nested choice inside one type: a subset of `B` of size `n` that removes as few items of
`A ⊆ B` as possible. -/
theorem exists_nested_fin {α : Type*} [DecidableEq α] (A B : Finset α) (hAB : A ⊆ B) (n : ℕ)
    (hn : n ≤ B.card) : ∃ T ⊆ B, T.card = n ∧ (A \ T).card = A.card - n := by
  by_cases h : n ≤ A.card
  · obtain ⟨T, hTA, hT⟩ := Finset.exists_subset_card_eq h
    exact ⟨T, hTA.trans hAB, hT, by rw [Finset.card_sdiff_of_subset hTA, hT]⟩
  · have h : A.card < n := Nat.lt_of_not_le h
    have hBA : n - A.card ≤ (B \ A).card := by
      rw [Finset.card_sdiff_of_subset hAB]; omega
    obtain ⟨C, hCB, hC⟩ := Finset.exists_subset_card_eq hBA
    refine ⟨A ∪ C, Finset.union_subset hAB (hCB.trans Finset.sdiff_subset), ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hCB Finset.disjoint_sdiff),
        hC]
      omega
    · rw [Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_left, Finset.card_empty]
      omega

/-- **A final set with prescribed counts and the fewest exchanges from `A`.** -/
theorem exists_nested (ty : Fin m → Fin d) (A : Finset (Fin m)) (u : CState d m)
    (hu : ∀ τ, ((u τ : Fin (m + 1)) : ℕ) ≤ mult ty τ) :
    ∃ T : Finset (Fin m), cstate ty T = u ∧
      (A \ T).card = ∑ τ, (tcount ty A τ - ((u τ : Fin (m + 1)) : ℕ)) := by
  classical
  have h : ∀ τ, ∃ t ⊆ univ.filter (fun i => ty i = τ), t.card = ((u τ : Fin (m + 1)) : ℕ) ∧
      (A.filter (fun i => ty i = τ) \ t).card = tcount ty A τ - ((u τ : Fin (m + 1)) : ℕ) :=
    fun τ => exists_nested_fin _ _ (Finset.filter_subset_filter _ (Finset.subset_univ A)) _ (hu τ)
  choose t ht hc hd using h
  have hT : ∀ τ, (univ.filter (fun i => i ∈ t (ty i))).filter (fun i => ty i = τ) = t τ := by
    intro τ
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hi, rfl⟩; exact hi
    · intro hi
      have h2 := ht τ hi
      simp only [mem_filter, mem_univ, true_and] at h2
      exact ⟨by rw [h2]; exact hi, h2⟩
  refine ⟨univ.filter (fun i => i ∈ t (ty i)), ?_, ?_⟩
  · funext τ
    apply Fin.ext
    rw [cstate_val]
    unfold tcount
    rw [hT, hc]
  · rw [Finset.card_eq_sum_card_fiberwise (f := ty) (t := univ) (by intro i _; simp)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← hd τ, ← hT τ]
    congr 1
    ext i
    simp only [mem_filter, mem_sdiff]
    tauto

/-- **The exchanges between two sets bound the count excess.** -/
theorem excess_le_sdiff (ty : Fin m → Fin d) (A B : Finset (Fin m)) :
    ∑ τ, (tcount ty A τ - tcount ty B τ) ≤ (A \ B).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := ty) (s := A \ B) (t := univ) (by intro i _; simp)]
  refine Finset.sum_le_sum fun τ _ => ?_
  have h1 : (A.filter (fun i => ty i = τ)).card
      ≤ ((A \ B).filter (fun i => ty i = τ)).card + (B.filter (fun i => ty i = τ)).card := by
    calc _ ≤ ((A.filter (fun i => ty i = τ)) \ (B.filter (fun i => ty i = τ))).card
          + (B.filter (fun i => ty i = τ)).card := Finset.card_le_card_sdiff_add_card
      _ = _ := by
        congr 2
        ext i
        simp only [mem_filter, mem_sdiff]
        tauto
  unfold tcount
  omega

theorem sum_cstate (ty : Fin m → Fin d) (S : Finset (Fin m)) :
    ∑ τ, ((cstate ty S τ : Fin (m + 1)) : ℕ) = S.card := sum_tcount ty S

/-- **Item exchanges bound count exchanges.** -/
theorem countDist_le (ty : Fin m → Fin d) (A B : Finset (Fin m)) (h : A.card = B.card) :
    countDist (cstate ty A) (cstate ty B) / 2 ≤ (A \ B).card := by
  rw [countDist_half _ _ (by rw [sum_cstate, sum_cstate, h])]
  exact excess_le_sdiff ty A B

open scoped Classical in
/-- The chosen final set with counts `u` nested with `A`. -/
noncomputable def nest (ty : Fin m → Fin d) (A : Finset (Fin m)) (u : CState d m) :
    Finset (Fin m) :=
  if h : ∃ T : Finset (Fin m), cstate ty T = u ∧
      (A \ T).card = ∑ τ, (tcount ty A τ - ((u τ : Fin (m + 1)) : ℕ)) then h.choose else ∅

theorem nest_spec (ty : Fin m → Fin d) (A : Finset (Fin m)) (u : CState d m)
    (hu : ∀ τ, ((u τ : Fin (m + 1)) : ℕ) ≤ mult ty τ) :
    cstate ty (nest ty A u) = u ∧
      (A \ nest ty A u).card = ∑ τ, (tcount ty A τ - ((u τ : Fin (m + 1)) : ℕ)) := by
  have hex := exists_nested ty A u hu
  unfold nest
  rw [dif_pos hex]
  exact hex.choose_spec

/-! ## 2. The count recourse program of the script -/

/-- **The transport of `EXP_paperC_budget_recourse.py` (`recourse_value`) at one budget**:
`z(v, u) ≥ 0` with `Σ_u z(v, u) = x(v)`, final count vectors `u` admissible (`u_τ ≤ n_τ`,
`Σ u = k`) and at most `R` exchanges away (`|v - u|_1 // 2 ≤ R`), and the type-marginal band
on the final law. -/
def CountTransport (ty : Fin m → Fin d) (x : CState d m → ℝ) (k R : ℕ) (η : ℝ) :
    Set (CState d m → CState d m → ℝ) :=
  {z | (∀ v u, 0 ≤ z v u) ∧ (∀ v, ∑ u, z v u = x v) ∧
    (∀ v u, z v u ≠ 0 → (∀ τ, ((u τ : Fin (m + 1)) : ℕ) ≤ mult ty τ) ∧
      ∑ τ, ((u τ : Fin (m + 1)) : ℕ) = k ∧ countDist v u / 2 ≤ R) ∧
    ∀ τ, 0 < mult ty τ →
      |(∑ v, ∑ u, z v u * (((u τ : Fin (m + 1)) : ℕ) : ℝ)) / (mult ty τ : ℝ) - (k : ℝ) / m|
        ≤ η / m}

/-- The regret of the final law of a transport. -/
noncomputable def transportCost (ty : Fin m → Fin d) (wt : Fin d → ℝ) (k : Fin (m + 1))
    (z : CState d m → CState d m → ℝ) : ℝ :=
  ∑ v, ∑ u, z v u * typedCost ty wt k u

/-- **The script's recourse program**: the banded count flow of `U_g` and a transport of
radius `R` at every budget of `K`; the value is the worst final regret. -/
def countRecourseSet (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : Set ℝ :=
  {y | ∃ F : LayeredFlow (CState d m), CountFeasibleH ty F ∧ FlowBand ty F η ∧
    ∃ z : Fin (m + 1) → CState d m → CState d m → ℝ,
      (∀ k ∈ K, z k ∈ CountTransport ty (F.x k.val) k.val R η) ∧
      y = K.sup' hK (fun k => transportCost ty wt k (z k))}

/-- The value of the script's recourse program. -/
noncomputable def countRecourseValue (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : ℝ :=
  sInf (countRecourseSet ty wt η R K hK)

/-! ## 3. Symmetrising a recourse plan within types -/

/-- Relabel the ranking and the final set by the same uniform type-preserving permutation. -/
noncomputable def symPlan (ty : Fin m → Fin d) (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) :
    Equiv.Perm (Fin m) → Finset (Fin m) → ℝ :=
  fun σ T => pushLaw
    (fun w : WPerm (typeLabel ty) × (Equiv.Perm (Fin m) × Finset (Fin m)) =>
      (w.1.val * w.2.1, w.2.2.map w.1.val.toEmbedding))
    (fun w => J w.2.1 w.2.2 / (Fintype.card (WPerm (typeLabel ty)) : ℝ)) (σ, T)

theorem symPlan_expect (ty : Fin m → Fin d) (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (f : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) :
    ∑ σ, ∑ T, symPlan ty J σ T * f σ T
      = (∑ ρ : WPerm (typeLabel ty), ∑ σ, ∑ T, J σ T * f (ρ.val * σ) (T.map ρ.val.toEmbedding))
          / (Fintype.card (WPerm (typeLabel ty)) : ℝ) := by
  have h := pushLaw_expect
    (fun w : WPerm (typeLabel ty) × (Equiv.Perm (Fin m) × Finset (Fin m)) =>
      (w.1.val * w.2.1, w.2.2.map w.1.val.toEmbedding))
    (fun w => J w.2.1 w.2.2 / (Fintype.card (WPerm (typeLabel ty)) : ℝ)) (fun p => f p.1 p.2)
  rw [Fintype.sum_prod_type] at h
  refine h.trans ?_
  simp_rw [Fintype.sum_prod_type, Finset.sum_div, div_mul_eq_mul_div]

theorem symPlan_nonneg (ty : Fin m → Fin d) (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (hJ : ∀ σ T, 0 ≤ J σ T) : ∀ σ T, 0 ≤ symPlan ty J σ T :=
  fun _ _ => pushLaw_nonneg _ _ (fun _ => div_nonneg (hJ _ _) (Nat.cast_nonneg _)) _

theorem symPlan_support (ty : Fin m → Fin d) (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (σ' : Equiv.Perm (Fin m)) (T' : Finset (Fin m)) (h : symPlan ty J σ' T' ≠ 0) :
    ∃ (ρ : WPerm (typeLabel ty)) (σ : Equiv.Perm (Fin m)) (T : Finset (Fin m)),
      ρ.val * σ = σ' ∧ T.map ρ.val.toEmbedding = T' ∧ J σ T ≠ 0 := by
  obtain ⟨w, hw, hJw⟩ := pushLaw_ne_zero _ _ _ h
  exact ⟨w.1, w.2.1, w.2.2, (Prod.mk.inj hw).1, (Prod.mk.inj hw).2,
    fun h0 => hJw (by simp [h0])⟩

theorem symPlan_invariant (ty : Fin m → Fin d) (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (f : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (hf : ∀ (ρ : WPerm (typeLabel ty)) σ T, f (ρ.val * σ) (T.map ρ.val.toEmbedding) = f σ T) :
    ∑ σ, ∑ T, symPlan ty J σ T * f σ T = ∑ σ, ∑ T, J σ T * f σ T := by
  have hG : (Fintype.card (WPerm (typeLabel ty)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [symPlan_expect]
  simp_rw [hf]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **The ranking marginal of the symmetrised plan is the symmetrised ranking law.** -/
theorem symPlan_row (ty : Fin m → Fin d) (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (σ' : Equiv.Perm (Fin m)) :
    ∑ T, symPlan ty J σ' T = symLaw ty (fun σ => ∑ T, J σ T) σ' := by
  have e1 : ∑ σ, ∑ T, symPlan ty J σ T * (if σ = σ' then (1 : ℝ) else 0)
      = ∑ T, symPlan ty J σ' T := by
    rw [Finset.sum_eq_single_of_mem σ' (Finset.mem_univ _) (fun σ _ hσ => by simp [hσ])]
    simp
  rw [← e1, symPlan_expect ty J (fun σ _ => if σ = σ' then (1 : ℝ) else 0), symLaw,
    pushLaw_apply, Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [div_mul_eq_mul_div, Finset.sum_mul]

/-- **The final item marginal of the symmetrised plan is the type average.** -/
theorem symPlan_marginal (ty : Fin m → Fin d) (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (i : Fin m) :
    ∑ σ, ∑ T, symPlan ty J σ T * ind i T
      = (∑ j ∈ univ.filter (fun j => ty j = ty i), ∑ σ, ∑ T, J σ T * ind j T)
          / (mult ty (ty i) : ℝ) := by
  rw [symPlan_expect ty J (fun _ T => ind i T)]
  simp_rw [ind_map]
  exact wavg ty (fun j => ∑ σ, ∑ T, J σ T * ind j T) i

theorem plan_class (ty : Fin m → Fin d) (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (τ : Fin d) :
    ∑ j ∈ univ.filter (fun j => ty j = τ), ∑ σ, ∑ T, J σ T * ind j T
      = ∑ σ, ∑ T, J σ T * (((cstate ty T τ : Fin (m + 1)) : ℕ) : ℝ) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.mul_sum, sum_ind_class]
  rfl

/-! ## 4. Lifting a count transport to item exchanges -/

theorem flowLaw_group (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) (k : Fin (m + 1)) (h : CState d m → ℝ) :
    ∑ σ, flowLaw ty F σ * h (rankLayer ty k σ) = ∑ v, F.x k.val v * h v := by
  rw [objective_transports (flowLaw ty F) ty k h]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [show flowX (flowLaw ty F) ty k v = occ (flowLaw ty F) (rankLayer ty k) v from rfl,
    flowLaw_occ ty F hF k v]

theorem flowLaw_le (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) (k : Fin (m + 1)) (σ : Equiv.Perm (Fin m)) :
    flowLaw ty F σ ≤ F.x k.val (rankLayer ty k σ) := by
  have h := flowLaw_group ty F hF k (fun v => if v = rankLayer ty k σ then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  rw [← h]
  have hs := Finset.single_le_sum
    (f := fun σ' => if rankLayer ty k σ' = rankLayer ty k σ then flowLaw ty F σ' else 0)
    (fun σ' _ => by
      split_ifs
      · exact flowLaw_nonneg ty F σ'
      · exact le_refl 0) (Finset.mem_univ σ)
  simpa using hs

/-- **The base plan**: given the prefix counts `v`, draw the final counts `u` with probability
`z(v, u)/x(v)` and take the final set nested with the prefix. -/
noncomputable def basePlan (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) (k : Fin (m + 1))
    (zk : CState d m → CState d m → ℝ) : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ :=
  fun σ T => ∑ u, flowLaw ty F σ * zk (rankLayer ty k σ) u / F.x k.val (rankLayer ty k σ)
    * (if nest ty (prefixSet σ k) u = T then 1 else 0)

theorem basePlan_nonneg (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) (k : Fin (m + 1))
    (zk : CState d m → CState d m → ℝ) (hz : ∀ v u, 0 ≤ zk v u) :
    ∀ σ T, 0 ≤ basePlan ty F k zk σ T := by
  intro σ T
  refine Finset.sum_nonneg fun u _ => mul_nonneg (div_nonneg (mul_nonneg
    (flowLaw_nonneg ty F σ) (hz _ u)) (F.xnn _ _)) ?_
  split_ifs <;> norm_num

theorem basePlan_expect (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) (k : Fin (m + 1))
    (zk : CState d m → CState d m → ℝ) (σ : Equiv.Perm (Fin m)) (f : Finset (Fin m) → ℝ) :
    ∑ T, basePlan ty F k zk σ T * f T
      = ∑ u, flowLaw ty F σ * zk (rankLayer ty k σ) u / F.x k.val (rankLayer ty k σ)
          * f (nest ty (prefixSet σ k) u) := by
  unfold basePlan
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp [Finset.sum_ite_eq]

theorem basePlan_row (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) (k : Fin (m + 1)) (R : ℕ) (η : ℝ)
    (zk : CState d m → CState d m → ℝ) (hz : zk ∈ CountTransport ty (F.x k.val) k.val R η)
    (σ : Equiv.Perm (Fin m)) : ∑ T, basePlan ty F k zk σ T = flowLaw ty F σ := by
  have h := basePlan_expect ty F k zk σ (fun _ => 1)
  simp only [mul_one] at h
  rw [h, ← Finset.sum_div, ← Finset.mul_sum, hz.2.1]
  by_cases hx : F.x k.val (rankLayer ty k σ) = 0
  · rw [hx, mul_zero, zero_div]
    have h1 := flowLaw_le ty F hF k σ
    rw [hx] at h1
    linarith [flowLaw_nonneg ty F σ]
  · field_simp

theorem basePlan_final (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) (k : Fin (m + 1)) (R : ℕ) (η : ℝ)
    (zk : CState d m → CState d m → ℝ) (hz : zk ∈ CountTransport ty (F.x k.val) k.val R η)
    (h : CState d m → ℝ) :
    ∑ σ, ∑ T, basePlan ty F k zk σ T * h (cstate ty T) = ∑ v, ∑ u, zk v u * h u := by
  have e1 : ∀ σ, ∑ T, basePlan ty F k zk σ T * h (cstate ty T)
      = flowLaw ty F σ
        * ((∑ u, zk (rankLayer ty k σ) u * h u) / F.x k.val (rankLayer ty k σ)) := by
    intro σ
    rw [basePlan_expect ty F k zk σ (fun T => h (cstate ty T)), Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hzu : zk (rankLayer ty k σ) u = 0
    · simp [hzu]
    · rw [(nest_spec ty (prefixSet σ k) u (hz.2.2.1 _ u hzu).1).1]
      ring
  rw [Finset.sum_congr rfl fun σ _ => e1 σ,
    flowLaw_group ty F hF k (fun v => (∑ u, zk v u * h u) / F.x k.val v)]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hx : F.x k.val v = 0
  · have hz0 : ∀ u, zk v u = 0 := by
      have hs := hz.2.1 v
      rw [hx] at hs
      exact fun u => (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => hz.1 v u)).mp hs u
        (Finset.mem_univ u)
    simp [hx, hz0]
  · field_simp

theorem basePlan_supp (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) (k : Fin (m + 1))
    (R : ℕ) (η : ℝ) (zk : CState d m → CState d m → ℝ)
    (hz : zk ∈ CountTransport ty (F.x k.val) k.val R η)
    (σ : Equiv.Perm (Fin m)) (T : Finset (Fin m)) (h : basePlan ty F k zk σ T ≠ 0) :
    T.card = k.val ∧ (prefixSet σ k \ T).card ≤ R := by
  unfold basePlan at h
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hT : nest ty (prefixSet σ k) u = T := by
    by_contra hc
    apply hu
    simp [hc]
  have hzu : zk (rankLayer ty k σ) u ≠ 0 := by
    intro h0
    apply hu
    rw [h0]
    simp
  obtain ⟨hmult, hsum, hdist⟩ := hz.2.2.1 _ u hzu
  obtain ⟨hc, hd⟩ := nest_spec ty (prefixSet σ k) u hmult
  rw [hT] at hc hd
  have hv : cstate ty (prefixSet σ k) = rankLayer ty k σ := cstate_prefix ty σ k
  have hvsum : ∑ τ, ((rankLayer ty k σ τ : Fin (m + 1)) : ℕ) = k.val := by
    rw [← hv, sum_cstate, prefixSet_card]
  refine ⟨by rw [card_of_cstate ty T u hc, hsum], ?_⟩
  rw [hd]
  have e : ∑ τ, (tcount ty (prefixSet σ k) τ - ((u τ : Fin (m + 1)) : ℕ))
      = countDist (rankLayer ty k σ) u / 2 := by
    rw [countDist_half _ _ (by rw [hvsum, hsum]), ← hv]
    rfl
  rw [e]
  exact hdist

/-- **The lift is an item recourse plan with the transport's cost.** -/
theorem lift_plan (ty : Fin m → Fin d) (wt : Fin d → ℝ) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) (k : Fin (m + 1)) (R : ℕ) (η : ℝ)
    (zk : CState d m → CState d m → ℝ) (hz : zk ∈ CountTransport ty (F.x k.val) k.val R η) :
    symPlan ty (basePlan ty F k zk) ∈ PlanFeasible (bandFlowLaw ty F) k R η ∧
      planCost (typedG ty wt) k (symPlan ty (basePlan ty F k zk)) = transportCost ty wt k zk := by
  refine ⟨⟨symPlan_nonneg ty _ (basePlan_nonneg ty F k zk hz.1), fun σ => ?_,
    fun σ T h => ?_, fun i => ?_⟩, ?_⟩
  · rw [symPlan_row]
    have e : (fun σ => ∑ T, basePlan ty F k zk σ T) = flowLaw ty F :=
      funext fun σ => basePlan_row ty F hF k R η zk hz σ
    rw [e]
    rfl
  · obtain ⟨ρ, σ₀, T₀, hσ, hT, hne⟩ := symPlan_support ty _ σ T h
    obtain ⟨hc, hd⟩ := basePlan_supp ty F k R η zk hz σ₀ T₀ hne
    subst hσ hT
    refine ⟨by rw [Finset.card_map, hc], ?_⟩
    rw [prefixSet_mul, ← Finset.map_sdiff, Finset.card_map]
    exact hd
  · rw [symPlan_marginal, plan_class,
      basePlan_final ty F hF k R η zk hz (fun c => (((c (ty i) : Fin (m + 1)) : ℕ) : ℝ))]
    exact hz.2.2.2 (ty i) (mult_pos_at ty i)
  · unfold planCost transportCost
    rw [symPlan_invariant ty _ (fun _ T => subCost (typedG ty wt) k T)
      (fun ρ σ T => by rw [subCost_eq_typedCost, subCost_eq_typedCost, cstate_map])]
    simp_rw [subCost_eq_typedCost]
    exact basePlan_final ty F hF k R η zk hz (typedCost ty wt k)

/-- **Count to item**: every value of the script's recourse program is achieved by an item
recourse plan. -/
theorem lift_mem (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) (hb : FlowBand ty F η)
    (z : Fin (m + 1) → CState d m → CState d m → ℝ)
    (hz : ∀ k ∈ K, z k ∈ CountTransport ty (F.x k.val) k.val R η) :
    K.sup' hK (fun k => transportCost ty wt k (z k)) ∈ recourseSet (typedG ty wt) η R K hK :=
  ⟨bandFlowLaw ty F, bandFlowLaw_feasible ty F η hF hb,
    fun k => symPlan ty (basePlan ty F k (z k)),
    fun k hk => (lift_plan ty wt F hF k R η (z k) (hz k hk)).1,
    Finset.sup'_congr hK rfl fun k hk => (lift_plan ty wt F hF k R η (z k) (hz k hk)).2.symm⟩

/-! ## 5. Projecting an item recourse plan to counts -/

/-- The joint law of (prefix counts, final counts) of a plan. -/
noncomputable def zProj (ty : Fin m → Fin d) (k : Fin (m + 1))
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) : CState d m → CState d m → ℝ :=
  fun v u => pushLaw
    (fun p : Equiv.Perm (Fin m) × Finset (Fin m) => (rankLayer ty k p.1, cstate ty p.2))
    (fun p => J p.1 p.2) (v, u)

theorem zProj_expect (ty : Fin m → Fin d) (k : Fin (m + 1))
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) (h : CState d m → CState d m → ℝ) :
    ∑ v, ∑ u, zProj ty k J v u * h v u
      = ∑ σ, ∑ T, J σ T * h (rankLayer ty k σ) (cstate ty T) := by
  have e := pushLaw_expect
    (fun p : Equiv.Perm (Fin m) × Finset (Fin m) => (rankLayer ty k p.1, cstate ty p.2))
    (fun p => J p.1 p.2) (fun q => h q.1 q.2)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at e
  exact e

theorem rankingFlow_x (P : Equiv.Perm (Fin m) → ℝ) (hP : ∀ x, 0 ≤ P x) (ty : Fin m → Fin d)
    (k : Fin (m + 1)) (v : CState d m) : (rankingFlow P hP ty).x k.val v = flowX P ty k v := by
  show flowX P ty (clampIdx m k.val) v = _
  rw [show clampIdx m k.val = k from Fin.ext (by simp [clampIdx]; omega)]

/-- **Item to count**: the projection of an item plan is a transport of the script. -/
theorem proj_transport (ty : Fin m → Fin d) (P : Equiv.Perm (Fin m) → ℝ) (η : ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) (R : ℕ)
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) (hJ : J ∈ PlanFeasible P k R η) :
    zProj ty k J ∈ CountTransport ty ((rankingFlow P hP.1 ty).x k.val) k.val R η := by
  refine ⟨fun v u => pushLaw_nonneg
      (fun p : Equiv.Perm (Fin m) × Finset (Fin m) => (rankLayer ty k p.1, cstate ty p.2))
      (fun p => J p.1 p.2) (fun p => hJ.1 p.1 p.2) (v, u), fun v => ?_,
    fun v u h => ?_, fun τ hτ => ?_⟩
  · rw [rankingFlow_x]
    have e := zProj_expect ty k J (fun v' _ => if v' = v then (1 : ℝ) else 0)
    have lhs : ∑ v', ∑ u, zProj ty k J v' u * (if v' = v then (1 : ℝ) else 0)
        = ∑ u, zProj ty k J v u := by
      rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ v) (fun v' _ hv' => by simp [hv'])]
      simp
    have e2 : ∑ σ, ∑ T, J σ T * (if rankLayer ty k σ = v then (1 : ℝ) else 0)
        = ∑ σ, P σ * (if rankLayer ty k σ = v then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [← Finset.sum_mul, hJ.2.1 σ]
    have rhs : ∑ w, flowX P ty k w * (if w = v then (1 : ℝ) else 0) = flowX P ty k v := by
      simp
    rw [← lhs, e, e2, objective_transports P ty k (fun w => if w = v then (1 : ℝ) else 0), rhs]
  · obtain ⟨p, hp, hJp⟩ := pushLaw_ne_zero _ _ _ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj hp
    obtain ⟨hc, hd⟩ := hJ.2.2.1 p.1 p.2 hJp
    subst h1 h2
    refine ⟨tcount_le_mult ty p.2, by rw [sum_cstate, hc], ?_⟩
    rw [← cstate_prefix]
    exact (countDist_le ty _ _ (by rw [prefixSet_card, hc])).trans hd
  · rw [zProj_expect ty k J (fun _ u => (((u τ : Fin (m + 1)) : ℕ) : ℝ)), ← plan_class]
    exact avg_band _ _ _ _ hτ fun j _ => hJ.2.2.2 j

theorem proj_cost (ty : Fin m → Fin d) (wt : Fin d → ℝ) (k : Fin (m + 1))
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) :
    transportCost ty wt k (zProj ty k J) = planCost (typedG ty wt) k J := by
  unfold transportCost planCost
  rw [zProj_expect ty k J (fun _ u => typedCost ty wt k u)]
  simp_rw [subCost_eq_typedCost]

theorem proj_mem (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) (P : Equiv.Perm (Fin m) → ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η)
    (J : Fin (m + 1) → Equiv.Perm (Fin m) → Finset (Fin m) → ℝ)
    (hJ : ∀ k ∈ K, J k ∈ PlanFeasible P k R η) :
    K.sup' hK (fun k => planCost (typedG ty wt) k (J k)) ∈ countRecourseSet ty wt η R K hK :=
  ⟨rankingFlow P hP.1 ty, rankingFlow_feasible P hP.1 hP.2.1 ty, rankingFlow_band ty η P hP,
    fun k => zProj ty k (J k), fun k hk => proj_transport ty P η hP k R (J k) (hJ k hk),
    Finset.sup'_congr hK rfl fun k _ => (proj_cost ty wt k (J k)).symm⟩

/-! ## 6. The script's recourse values are `V_g^{(R)}` -/

/-- **COUNT = ITEM for recourse**: the achievable worst-budget costs of item recourse plans
and of the script's count recourse program are the same set. -/
theorem recourse_sets_eq (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    recourseSet (typedG ty wt) η R K hK = countRecourseSet ty wt η R K hK := by
  ext y
  constructor
  · rintro ⟨P, hP, J, hJ, rfl⟩
    exact proj_mem ty wt η R K hK P hP J hJ
  · rintro ⟨F, hF, hb, z, hz, rfl⟩
    exact lift_mem ty wt η R K hK F hF hb z hz

/-- **`V_g^{(R)}(η)` is the value of the script's recourse LP.** -/
theorem recourse_eq_count (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    recourseValue (typedG ty wt) η R K hK = countRecourseValue ty wt η R K hK := by
  unfold recourseValue countRecourseValue
  rw [recourse_sets_eq]

/-- The script's recourse program is feasible at every nonnegative band width. -/
theorem countRecourse_nonempty [NeZero m] (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (R : ℕ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    (countRecourseSet ty wt η R K hK).Nonempty := by
  rw [← recourse_sets_eq]
  exact recourse_nonempty (typedG ty wt) η hη R K hK

#print axioms countDist_half
#print axioms exists_nested
#print axioms countDist_le
#print axioms symPlan_row
#print axioms symPlan_marginal
#print axioms basePlan_row
#print axioms basePlan_final
#print axioms basePlan_supp
#print axioms lift_plan
#print axioms lift_mem
#print axioms proj_transport
#print axioms proj_cost
#print axioms proj_mem
#print axioms recourse_sets_eq
#print axioms recourse_eq_count
#print axioms countRecourse_nonempty

end CIGAMF.P13.PaperCCountRecourse
