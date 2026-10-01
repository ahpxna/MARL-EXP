import «LeanPaperCTwoMagFourV1»
import «LeanPaperCLawPushV1»

/-!
# Paper C: knowing the budget, and editing the ranking after it is revealed

The universal value `U_g(η) = trueValue g η K` commits to one ranking law for every budget.

**Budget-aware value.** At a budget `k` a policy that knows `k` chooses a law `Q_k` on
`k`-subsets whose item marginals are within `η/m` of `k/m` (`SubFeasible`). The layer value
is `B_{g,k}(η) = inf E_{Q_k} r_k` (`layerValue`), and `B_g(η) = max_{k ∈ K} B_{g,k}(η)`
(`awareValue`).

* `push_feasible`, `push_cost`: a ranking law pushed to its budget-`k` prefix is a subset law
  with the same marginal and the same expected regret.
* `aware_le_true`: `B_g(η) ≤ U_g(η)`.
* `linear_lower`, `layer_ge_of_linear`: a **linear certificate** `α + Σ_{i∈S} β_i ≤ r_k(S)` on
  `k`-sets gives `B_{g,k}(η) ≥ (α + (k/m) Σ β_i - (η/m) Σ |β_i|)/D`.

**Recourse.** A policy commits to a band-feasible ranking law `P`; when `k` is revealed it
replaces at most `R` items of the prefix. A plan is a joint law `J(σ, T)` with `σ`-marginal `P`,
final sets `T` of size `k` with `|S_k(σ) \ T| ≤ R`, and final item marginals in the band
(`PlanFeasible`). `V_g^{(R)}(η)` is the best worst-budget cost (`recourseValue`).

* `aware_le_recourse`: `B_g ≤ V_g^{(R)}`.
* `recourse_le_true`, `recourse_zero`: `V_g^{(R)} ≤ U_g`, with equality at `R = 0`.
* `recourse_mono`: `V_g^{(R')} ≤ V_g^{(R)}` for `R ≤ R'`.
* `sdiff_card_le`: two `k`-sets differ by at most `min(k, m-k)` exchanges.
* `recourse_full`: if `min(k, m-k) ≤ R` for every budget of `K`, then `V_g^{(R)} = B_g`. In
  particular `R = ⌊m/2⌋` exchanges always reach the budget-aware value, and one exchange suffices
  at the budgets `1` and `m-1`.
-/

namespace CIGAMF.P13.PaperCBudgetAware

open Finset
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCFrontier
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCLawPush

variable {m : ℕ}

/-! ## 1. Subset laws and the budget-aware value -/

/-- Membership indicator. -/
noncomputable def ind (i : Fin m) (S : Finset (Fin m)) : ℝ := if i ∈ S then 1 else 0

/-- **Subset laws at budget `k` within the band `η`.** -/
def SubFeasible (k : ℕ) (η : ℝ) : Set (Finset (Fin m) → ℝ) :=
  {Q | (∀ S, 0 ≤ Q S) ∧ ∑ S, Q S = 1 ∧ (∀ S, Q S ≠ 0 → S.card = k) ∧
    ∀ i : Fin m, |∑ S, Q S * ind i S - (k : ℝ) / m| ≤ η / m}

/-- The normalised regret of removing the set `S` at budget `k`. -/
noncomputable def subCost (g : Fin m → ℝ) (k : Fin (m + 1)) (S : Finset (Fin m)) : ℝ :=
  (|∑ i ∈ S, g i| - trueBaseline g k) / normMass g

/-- **The layer value**: the best subset law at budget `k`. -/
noncomputable def layerValue (g : Fin m → ℝ) (η : ℝ) (k : Fin (m + 1)) : ℝ :=
  sInf ((fun Q => ∑ S, Q S * subCost g k S) '' SubFeasible k.val η)

/-- **The budget-aware value.** -/
noncomputable def awareValue (g : Fin m → ℝ) (η : ℝ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : ℝ :=
  K.sup' hK (fun k => layerValue g η k)

theorem normMass_nonneg (g : Fin m → ℝ) : 0 ≤ normMass g :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

theorem subCost_nonneg (g : Fin m → ℝ) (k : Fin (m + 1)) (S : Finset (Fin m))
    (hS : S.card = k.val) : 0 ≤ subCost g k S := by
  unfold subCost
  refine div_nonneg (sub_nonneg.mpr ?_) (normMass_nonneg g)
  unfold trueBaseline baseline
  exact Finset.inf'_le _ (by simp [hS])

theorem cost_nonneg (g : Fin m → ℝ) (k : Fin (m + 1)) (η : ℝ) (Q : Finset (Fin m) → ℝ)
    (hQ : Q ∈ SubFeasible k.val η) : 0 ≤ ∑ S, Q S * subCost g k S := by
  refine Finset.sum_nonneg fun S _ => ?_
  by_cases h : Q S = 0
  · rw [h, zero_mul]
  · exact mul_nonneg (hQ.1 S) (subCost_nonneg g k S (hQ.2.2.1 S h))

theorem layer_bdd (g : Fin m → ℝ) (η : ℝ) (k : Fin (m + 1)) :
    BddBelow ((fun Q => ∑ S, Q S * subCost g k S) '' SubFeasible k.val η) :=
  ⟨0, by rintro _ ⟨Q, hQ, rfl⟩; exact cost_nonneg g k η Q hQ⟩

theorem layer_le (g : Fin m → ℝ) (η : ℝ) (k : Fin (m + 1)) (Q : Finset (Fin m) → ℝ)
    (hQ : Q ∈ SubFeasible k.val η) : layerValue g η k ≤ ∑ S, Q S * subCost g k S :=
  csInf_le (layer_bdd g η k) ⟨Q, hQ, rfl⟩

theorem layer_nonneg (g : Fin m → ℝ) (η : ℝ) (k : Fin (m + 1))
    (hne : (SubFeasible (m := m) k.val η).Nonempty) : 0 ≤ layerValue g η k :=
  le_csInf (hne.image _) (by rintro _ ⟨Q, hQ, rfl⟩; exact cost_nonneg g k η Q hQ)

/-! ## 2. Ranking laws pushed to a budget -/

/-- The law of the budget-`k` prefix. -/
noncomputable def pushK (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) :
    Finset (Fin m) → ℝ :=
  fun S => ∑ σ, P σ * (if prefixSet σ k = S then 1 else 0)

theorem push_sum (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) (f : Finset (Fin m) → ℝ) :
    ∑ S, pushK P k S * f S = ∑ σ, P σ * f (prefixSet σ k) := by
  unfold pushK
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [ite_mul]

theorem inPrefix_eq_ind (σ : Equiv.Perm (Fin m)) (k : Fin (m + 1)) (i : Fin m) :
    inPrefixInd σ k.val i = ind i (prefixSet σ k) := by
  unfold inPrefixInd ind prefixSet
  simp

/-- **A ranking law's prefix is a subset law in the same band.** -/
theorem push_feasible (P : Equiv.Perm (Fin m) → ℝ) (η : ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) :
    pushK P k ∈ SubFeasible k.val η := by
  refine ⟨fun S => Finset.sum_nonneg fun σ _ => mul_nonneg (hP.1 σ) (by split_ifs <;> norm_num),
    ?_, ?_, fun i => ?_⟩
  · have := push_sum P k (fun _ => 1)
    simp only [mul_one] at this
    rw [this]; exact hP.2.1
  · intro S hS
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
    have : prefixSet σ k = S := by
      by_contra h; apply hσ; rw [if_neg h, mul_zero]
    rw [← this, prefixSet_card]
  · rw [push_sum P k (ind i)]
    have := hP.2.2 k.val (Nat.lt_succ_iff.mp k.isLt) i
    simpa only [id_eq, inPrefix_eq_ind] using this

theorem push_cost (g : Fin m → ℝ) (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) :
    ∑ S, pushK P k S * subCost g k S = ∑ σ, P σ * normalizedRegret g σ k := by
  rw [push_sum]; rfl

theorem layer_le_obj (g : Fin m → ℝ) (η : ℝ) (P : Equiv.Perm (Fin m) → ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) :
    layerValue g η k ≤ ∑ σ, P σ * normalizedRegret g σ k := by
  rw [← push_cost]; exact layer_le g η k _ (push_feasible P η hP k)

theorem sub_nonempty [NeZero m] (η : ℝ) (hη : 0 ≤ η) (k : Fin (m + 1)) :
    (SubFeasible (m := m) k.val η).Nonempty := by
  obtain ⟨P, hP⟩ := allPerm_feasible_nonempty m η hη
  exact ⟨_, push_feasible P η hP k⟩

/-- **Knowing the budget never hurts**: `B_g(η) ≤ U_g(η)`. -/
theorem aware_le_true [NeZero m] (g : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    awareValue g η K hK ≤ trueValue g η K hK := by
  unfold trueValue
  refine le_csInf ((allPerm_feasible_nonempty m η hη).image _) ?_
  rintro _ ⟨P, hP, rfl⟩
  refine Finset.sup'_le _ _ fun k hk => (layer_le_obj g η P hP k).trans ?_
  exact Finset.le_sup' (fun k => ∑ σ, P σ * normalizedRegret g σ k) hk

/-! ## 3. Linear certificates for a layer -/

/-- **A linear certificate bounds every subset law of the layer.** -/
theorem linear_lower (k : ℕ) (η : ℝ) (Q : Finset (Fin m) → ℝ) (hQ : Q ∈ SubFeasible k η)
    (f : Finset (Fin m) → ℝ) (α : ℝ) (β : Fin m → ℝ)
    (hS : ∀ S : Finset (Fin m), S.card = k → α + ∑ i ∈ S, β i ≤ f S) :
    α + (k : ℝ) / m * ∑ i, β i - η / m * ∑ i, |β i| ≤ ∑ S, Q S * f S := by
  have hlin : ∀ S, Q S * (α + ∑ i, β i * ind i S) ≤ Q S * f S := by
    intro S
    by_cases h : Q S = 0
    · rw [h, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (hQ.1 S)
      have e : ∑ i, β i * ind i S = ∑ i ∈ S, β i := by
        unfold ind
        simp [mul_ite, Finset.sum_ite_mem]
      rw [e]; exact hS S (hQ.2.2.1 S h)
  have hsum : ∑ S, Q S * (α + ∑ i, β i * ind i S) = α + ∑ i, β i * ∑ S, Q S * ind i S := by
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hQ.2.1, one_mul,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun S _ => by ring
  have hper : ∀ i, β i * ((k : ℝ) / m) - η / m * |β i| ≤ β i * ∑ S, Q S * ind i S := by
    intro i
    have hb := hQ.2.2.2 i
    have h1 : -(|β i| * (η / m)) ≤ β i * (∑ S, Q S * ind i S - (k : ℝ) / m) := by
      have := neg_abs_le (β i * (∑ S, Q S * ind i S - (k : ℝ) / m))
      rw [abs_mul] at this
      have h2 : |β i| * |∑ S, Q S * ind i S - (k : ℝ) / m| ≤ |β i| * (η / m) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      linarith
    nlinarith
  calc α + (k : ℝ) / m * ∑ i, β i - η / m * ∑ i, |β i|
      = α + ∑ i, (β i * ((k : ℝ) / m) - η / m * |β i|) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
        have e : ∀ i, (k : ℝ) / m * β i = β i * ((k : ℝ) / m) := fun i => mul_comm _ _
        simp_rw [e]; ring
    _ ≤ α + ∑ i, β i * ∑ S, Q S * ind i S := by
        gcongr with i; exact hper i
    _ = ∑ S, Q S * (α + ∑ i, β i * ind i S) := hsum.symm
    _ ≤ ∑ S, Q S * f S := Finset.sum_le_sum fun S _ => hlin S

/-- **The layer value from a linear certificate on the raw regret.** -/
theorem layer_ge_of_linear (g : Fin m → ℝ) (η : ℝ) (k : Fin (m + 1))
    (hne : (SubFeasible (m := m) k.val η).Nonempty) (hD : 0 < normMass g) (α : ℝ)
    (β : Fin m → ℝ)
    (hS : ∀ S : Finset (Fin m), S.card = k.val →
      α + ∑ i ∈ S, β i ≤ |∑ i ∈ S, g i| - trueBaseline g k) :
    (α + (k.val : ℝ) / m * ∑ i, β i - η / m * ∑ i, |β i|) / normMass g
      ≤ layerValue g η k := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨Q, hQ, rfl⟩
  have h := linear_lower k.val η Q hQ (fun S => |∑ i ∈ S, g i| - trueBaseline g k) α β hS
  rw [div_le_iff₀ hD]
  have e : (∑ S, Q S * subCost g k S) * normMass g
      = ∑ S, Q S * (|∑ i ∈ S, g i| - trueBaseline g k) := by
    unfold subCost
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    field_simp
  rw [e]; exact h

/-! ## 4. Recourse after the budget is revealed -/

/-- **Recourse plans** at budget `k` with at most `R` exchanges from the base law `P`. -/
def PlanFeasible (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) (R : ℕ) (η : ℝ) :
    Set (Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) :=
  {J | (∀ σ T, 0 ≤ J σ T) ∧ (∀ σ, ∑ T, J σ T = P σ) ∧
    (∀ σ T, J σ T ≠ 0 → T.card = k.val ∧ (prefixSet σ k \ T).card ≤ R) ∧
    ∀ i : Fin m, |∑ σ, ∑ T, J σ T * ind i T - (k.val : ℝ) / m| ≤ η / m}

/-- The expected regret of a plan. -/
noncomputable def planCost (g : Fin m → ℝ) (k : Fin (m + 1))
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) : ℝ :=
  ∑ σ, ∑ T, J σ T * subCost g k T

/-- The achievable worst-budget costs with `R` exchanges. -/
def recourseSet (g : Fin m → ℝ) (η : ℝ) (R : ℕ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    Set ℝ :=
  {x | ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η,
    ∃ J : Fin (m + 1) → Equiv.Perm (Fin m) → Finset (Fin m) → ℝ,
      (∀ k ∈ K, J k ∈ PlanFeasible P k R η) ∧ x = K.sup' hK (fun k => planCost g k (J k))}

/-- **The recourse value** `V_g^{(R)}(η)`. -/
noncomputable def recourseValue (g : Fin m → ℝ) (η : ℝ) (R : ℕ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : ℝ :=
  sInf (recourseSet g η R K hK)

/-- The law of the final set. -/
noncomputable def finalLaw (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) :
    Finset (Fin m) → ℝ :=
  fun T => ∑ σ, J σ T

theorem final_sum (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) (f : Finset (Fin m) → ℝ) :
    ∑ T, finalLaw J T * f T = ∑ σ, ∑ T, J σ T * f T := by
  unfold finalLaw
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem final_feasible (P : Equiv.Perm (Fin m) → ℝ) (η : ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) (R : ℕ)
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) (hJ : J ∈ PlanFeasible P k R η) :
    finalLaw J ∈ SubFeasible k.val η := by
  refine ⟨fun T => Finset.sum_nonneg fun σ _ => hJ.1 σ T, ?_, ?_, fun i => ?_⟩
  · have := final_sum J (fun _ => 1)
    simp only [mul_one] at this
    rw [this, Finset.sum_congr rfl fun σ _ => hJ.2.1 σ]; exact hP.2.1
  · intro T hT
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    exact (hJ.2.2.1 σ T hσ).1
  · rw [final_sum]; exact hJ.2.2.2 i

theorem layer_le_plan (g : Fin m → ℝ) (η : ℝ) (P : Equiv.Perm (Fin m) → ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) (R : ℕ)
    (J : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ) (hJ : J ∈ PlanFeasible P k R η) :
    layerValue g η k ≤ planCost g k J := by
  unfold planCost
  rw [← final_sum]
  exact layer_le g η k _ (final_feasible P η hP k R J hJ)

/-- The plan that keeps the prefix. -/
noncomputable def idPlan (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) :
    Equiv.Perm (Fin m) → Finset (Fin m) → ℝ :=
  fun σ T => P σ * (if T = prefixSet σ k then 1 else 0)

theorem idPlan_sum (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) (σ : Equiv.Perm (Fin m))
    (f : Finset (Fin m) → ℝ) : ∑ T, idPlan P k σ T * f T = P σ * f (prefixSet σ k) := by
  unfold idPlan
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [ite_mul]

theorem idPlan_feasible (P : Equiv.Perm (Fin m) → ℝ) (η : ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) (R : ℕ) :
    idPlan P k ∈ PlanFeasible P k R η := by
  refine ⟨fun σ T => mul_nonneg (hP.1 σ) (by split_ifs <;> norm_num), fun σ => ?_, ?_,
    fun i => ?_⟩
  · have := idPlan_sum P k σ (fun _ => 1)
    simpa only [mul_one] using this
  · intro σ T h
    have hT : T = prefixSet σ k := by
      by_contra hne; apply h; unfold idPlan; rw [if_neg hne, mul_zero]
    subst hT
    exact ⟨prefixSet_card σ k, by simp⟩
  · simp_rw [idPlan_sum P k _ (ind i)]
    have := hP.2.2 k.val (Nat.lt_succ_iff.mp k.isLt) i
    simpa only [id_eq, inPrefix_eq_ind] using this

theorem idPlan_cost (g : Fin m → ℝ) (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1)) :
    planCost g k (idPlan P k) = ∑ σ, P σ * normalizedRegret g σ k := by
  unfold planCost
  simp_rw [idPlan_sum]
  rfl

theorem recourse_bdd (g : Fin m → ℝ) (η : ℝ) (R : ℕ) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) : BddBelow (recourseSet g η R K hK) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨P, hP, J, hJ, rfl⟩
  obtain ⟨k, hk⟩ := hK
  refine le_trans ?_ (Finset.le_sup' (fun k => planCost g k (J k)) hk)
  unfold planCost
  rw [← final_sum]
  exact cost_nonneg g k η _ (final_feasible P η hP k R (J k) (hJ k hk))

theorem recourse_nonempty [NeZero m] (g : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : (recourseSet g η R K hK).Nonempty := by
  obtain ⟨P, hP⟩ := allPerm_feasible_nonempty m η hη
  exact ⟨_, P, hP, fun k => idPlan P k, fun k _ => idPlan_feasible P η hP k R, rfl⟩

/-- **Editing cannot beat knowing**: `B_g ≤ V_g^{(R)}`. -/
theorem aware_le_recourse [NeZero m] (g : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    awareValue g η K hK ≤ recourseValue g η R K hK := by
  refine le_csInf (recourse_nonempty g η hη R K hK) ?_
  rintro _ ⟨P, hP, J, hJ, rfl⟩
  refine Finset.sup'_le _ _ fun k hk => (layer_le_plan g η P hP k R (J k) (hJ k hk)).trans ?_
  exact Finset.le_sup' (fun k => planCost g k (J k)) hk

/-- **Editing never hurts**: `V_g^{(R)} ≤ U_g`. -/
theorem recourse_le_true [NeZero m] (g : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    recourseValue g η R K hK ≤ trueValue g η K hK := by
  unfold trueValue
  refine le_csInf ((allPerm_feasible_nonempty m η hη).image _) ?_
  rintro _ ⟨P, hP, rfl⟩
  refine csInf_le (recourse_bdd g η R K hK)
    ⟨P, hP, fun k => idPlan P k, fun k _ => idPlan_feasible P η hP k R, ?_⟩
  unfold trueObjective
  simp_rw [idPlan_cost]

/-- **No exchange, no gain**: `V_g^{(0)} = U_g`. -/
theorem recourse_zero [NeZero m] (g : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    recourseValue g η 0 K hK = trueValue g η K hK := by
  refine le_antisymm (recourse_le_true g η hη 0 K hK) ?_
  refine le_csInf (recourse_nonempty g η hη 0 K hK) ?_
  rintro _ ⟨P, hP, J, hJ, rfl⟩
  refine csInf_le (trueValue_bddBelow' g η K hK) ⟨P, hP, ?_⟩
  unfold trueObjective
  refine Finset.sup'_congr hK rfl fun k hk => ?_
  have hsupp : ∀ σ T, J k σ T ≠ 0 → T = prefixSet σ k := by
    intro σ T h
    obtain ⟨hc, hd⟩ := (hJ k hk).2.2.1 σ T h
    have hsub : prefixSet σ k ⊆ T := by
      rw [← Finset.sdiff_eq_empty_iff_subset]
      exact Finset.card_eq_zero.mp (Nat.le_zero.mp hd)
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc, prefixSet_card])).symm
  unfold planCost
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 : ∀ T, J k σ T * subCost g k T = J k σ T * subCost g k (prefixSet σ k) := by
    intro T
    by_cases h : J k σ T = 0
    · rw [h, zero_mul, zero_mul]
    · rw [hsupp σ T h]
  simp_rw [h1]
  rw [← Finset.sum_mul, (hJ k hk).2.1 σ]
  rfl
where
  trueValue_bddBelow' (g : Fin m → ℝ) (η : ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
      BddBelow ((fun P => trueObjective g P K hK) ''
        FeasibleAt (id : Equiv.Perm (Fin m) → _) η) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨P, hP, rfl⟩
    obtain ⟨k, hk⟩ := hK
    refine le_trans ?_ (Finset.le_sup' _ hk)
    rw [← push_cost]
    exact cost_nonneg g k η _ (push_feasible P η hP k)

/-- **More exchanges never hurt.** -/
theorem recourse_mono [NeZero m] (g : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η) (R R' : ℕ) (hRR : R ≤ R')
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    recourseValue g η R' K hK ≤ recourseValue g η R K hK := by
  refine csInf_le_csInf (recourse_bdd g η R' K hK) (recourse_nonempty g η hη R K hK) ?_
  rintro _ ⟨P, hP, J, hJ, rfl⟩
  refine ⟨P, hP, J, fun k hk => ?_, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hJ k hk
  exact ⟨h1, h2, fun σ T h => ⟨(h3 σ T h).1, (h3 σ T h).2.trans hRR⟩, h4⟩

/-- **Two `k`-sets differ by at most `min(k, m-k)` exchanges.** -/
theorem sdiff_card_le (S T : Finset (Fin m)) (k : ℕ) (hS : S.card = k) (hT : T.card = k) :
    (S \ T).card ≤ k ∧ (S \ T).card ≤ m - k := by
  refine ⟨hS ▸ Finset.card_le_card Finset.sdiff_subset, ?_⟩
  have hsub : S \ T ⊆ Tᶜ := fun x hx => by
    simp only [Finset.mem_sdiff] at hx; simpa using hx.2
  calc (S \ T).card ≤ Tᶜ.card := Finset.card_le_card hsub
    _ = m - k := by rw [Finset.card_compl, hT, Fintype.card_fin]

/-- The plan that draws the final set independently of the ranking. -/
noncomputable def indepPlan (P : Equiv.Perm (Fin m) → ℝ) (Q : Finset (Fin m) → ℝ) :
    Equiv.Perm (Fin m) → Finset (Fin m) → ℝ :=
  fun σ T => P σ * Q T

theorem indep_feasible (P : Equiv.Perm (Fin m) → ℝ) (η : ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) (R : ℕ)
    (hR : k.val ≤ R ∨ m - k.val ≤ R) (Q : Finset (Fin m) → ℝ) (hQ : Q ∈ SubFeasible k.val η) :
    indepPlan P Q ∈ PlanFeasible P k R η := by
  refine ⟨fun σ T => mul_nonneg (hP.1 σ) (hQ.1 T), fun σ => ?_, fun σ T h => ?_, fun i => ?_⟩
  · unfold indepPlan; rw [← Finset.mul_sum, hQ.2.1, mul_one]
  · have hQT : Q T ≠ 0 := fun h0 => h (by unfold indepPlan; rw [h0, mul_zero])
    have hc := hQ.2.2.1 T hQT
    refine ⟨hc, ?_⟩
    have := sdiff_card_le (prefixSet σ k) T k.val (prefixSet_card σ k) hc
    omega
  · have e : ∑ σ, ∑ T, indepPlan P Q σ T * ind i T = ∑ T, Q T * ind i T := by
      unfold indepPlan
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hP.2.1, one_mul]
    rw [e]; exact hQ.2.2.2 i

theorem indep_cost (g : Fin m → ℝ) (P : Equiv.Perm (Fin m) → ℝ) (hP1 : ∑ σ, P σ = 1)
    (k : Fin (m + 1)) (Q : Finset (Fin m) → ℝ) :
    planCost g k (indepPlan P Q) = ∑ T, Q T * subCost g k T := by
  unfold planCost indepPlan
  simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hP1, one_mul]

/-- **Enough exchanges reach the budget-aware value.**  If `min(k, m-k) ≤ R` at every budget
of `K`, then `V_g^{(R)} = B_g`. -/
theorem recourse_full [NeZero m] (g : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η) (R : ℕ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) (hR : ∀ k ∈ K, k.val ≤ R ∨ m - k.val ≤ R) :
    recourseValue g η R K hK = awareValue g η K hK := by
  refine le_antisymm ?_ (aware_le_recourse g η hη R K hK)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hnear : ∀ k : Fin (m + 1), ∃ Q ∈ SubFeasible (m := m) k.val η,
      ∑ S, Q S * subCost g k S < layerValue g η k + ε := by
    intro k
    obtain ⟨_, ⟨Q, hQ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((sub_nonempty η hη k).image _)
      (show layerValue g η k < layerValue g η k + ε by linarith)
    exact ⟨Q, hQ, hlt⟩
  choose Qf hQf hQc using hnear
  obtain ⟨P, hP⟩ := allPerm_feasible_nonempty m η hη
  have hmem : K.sup' hK (fun k => planCost g k (indepPlan P (Qf k))) ∈ recourseSet g η R K hK :=
    ⟨P, hP, fun k => indepPlan P (Qf k),
      fun k hk => indep_feasible P η hP k R (hR k hk) (Qf k) (hQf k), rfl⟩
  refine lt_of_le_of_lt (csInf_le (recourse_bdd g η R K hK) hmem) ?_
  rw [Finset.sup'_lt_iff]
  intro k hk
  rw [indep_cost g P hP.2.1]
  calc _ < layerValue g η k + ε := hQc k
    _ ≤ awareValue g η K hK + ε := by
      have := Finset.le_sup' (fun k => layerValue g η k) hk
      unfold awareValue; linarith

#print axioms push_feasible
#print axioms aware_le_true
#print axioms linear_lower
#print axioms layer_ge_of_linear
#print axioms aware_le_recourse
#print axioms recourse_le_true
#print axioms recourse_zero
#print axioms recourse_mono
#print axioms sdiff_card_le
#print axioms recourse_full

end CIGAMF.P13.PaperCBudgetAware
