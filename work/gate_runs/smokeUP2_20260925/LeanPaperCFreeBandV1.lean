import «LeanPaperCTypedFlowV1»

/-!
# Paper C: when the band is free, the additive price, and the size of the flow program

**The free threshold.** For a multiset `g` and budgets `K`:
* the free value is `V_free = V_g(m)`. At `η = m` the item band is vacuous
  (`feasible_m_eq`).
* The deviation of a law `μ` is `dev μ = m · max_{k ≤ m, i} |P_μ(i in the first k) - k/m|`, so
  `μ` is band-feasible at `η` exactly when `dev μ ≤ η` (`feasible_iff_dev`).
* The free threshold is `η_free = min{dev μ : μ a free optimum}`.

**What is proved.**
* `attain_value`, `attain_eta`: the band-feasible laws and the free optima are compact, so the
  value and the threshold are attained.
* `free_threshold`: for `η ≥ 0`, `V_g(η) = V_free` if and only if `η ≥ η_free`.
* `free_threshold_flow`: for a typed multiset `g = wt ∘ ty` the same threshold is read off the
  count-flow program of `LeanPaperCTypedFlowV1`: the band is free at `η` exactly when the flow
  value at `η` equals the flow value at `m`. Taken alone, `free_threshold` is close to a
  definition; the flow form is what makes `η_free` computable, by one parametric program over
  the count states.
* `support_box`, `card_box`: a count-feasible flow lives on the box `Π_τ [0, n_τ]` of
  `Π_τ (n_τ + 1)` states, where `n_τ` is the multiplicity of type `τ`. So for `d` fixed types
  the program has `O(m^d)` states per layer.
* **The additive price** `Δ_g(η) = V_g(η) - V_free`:
  - `gap_nonneg`, `gap_antitone`, `gap_zero_iff` (it vanishes exactly from `η_free` on);
  - `gap_stable`: `|Δ_g(η) - Δ_{g'}(η)| ≤ 6 ‖g - g'‖₁ / d` whenever both masses are at least
    `d`. This needs no lower bound on `V_free`, unlike the ratio `V_g(η)/V_free`, which the
    robust-ball module shows is not stable when `V_free` is small.
-/

namespace CIGAMF.P13.PaperCFreeBand

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCRelabel CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCFlowBandJoin CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFrontier

variable {m : ℕ} [NeZero m]

abbrev Law (m : ℕ) := Equiv.Perm (Fin m) → ℝ

/-- The retained marginal of item `i` at budget `k`. -/
noncomputable def marg (P : Law m) (k : ℕ) (i : Fin m) : ℝ := ∑ σ, P σ * inPrefixInd σ k i

/-- **The deviation of a law from the uniform band.** -/
noncomputable def dev (P : Law m) : ℝ :=
  (Finset.univ : Finset (Fin (m + 1) × Fin m)).sup' Finset.univ_nonempty
    (fun p => (m : ℝ) * |marg P p.1 p.2 - ((p.1 : ℕ) : ℝ) / m|)

theorem m_pos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)

theorem dev_nonneg (P : Law m) : 0 ≤ dev P := by
  refine le_trans ?_ (Finset.le_sup' (f := fun p : Fin (m + 1) × Fin m =>
    (m : ℝ) * |marg P p.1 p.2 - ((p.1 : ℕ) : ℝ) / m|) (Finset.mem_univ (0, ⟨0, by
      have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩)))
  exact mul_nonneg m_pos.le (abs_nonneg _)

/-- **Band-feasibility is a bound on the deviation.** -/
theorem feasible_iff_dev (P : Law m) (η : ℝ) :
    P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η
      ↔ (∀ σ, 0 ≤ P σ) ∧ (∑ σ, P σ = 1) ∧ dev P ≤ η := by
  have hm := m_pos (m := m)
  constructor
  · rintro ⟨hnn, hsum, hband⟩
    refine ⟨hnn, hsum, Finset.sup'_le _ _ fun p _ => ?_⟩
    have h := hband p.1 (Nat.lt_succ_iff.mp p.1.isLt) p.2
    have : |marg P p.1 p.2 - ((p.1 : ℕ) : ℝ) / m| ≤ η / m := h
    rw [le_div_iff₀ hm] at this
    linarith
  · rintro ⟨hnn, hsum, hdev⟩
    refine ⟨hnn, hsum, fun k hk i => ?_⟩
    have h := (Finset.le_sup' (f := fun p : Fin (m + 1) × Fin m =>
      (m : ℝ) * |marg P p.1 p.2 - ((p.1 : ℕ) : ℝ) / m|)
      (Finset.mem_univ ((⟨k, Nat.lt_succ_of_le hk⟩ : Fin (m + 1)), i))).trans hdev
    show |marg P k i - (k : ℝ) / m| ≤ η / m
    rw [le_div_iff₀ hm]
    simpa [mul_comm] using h

theorem marg_mem (P : Law m) (hnn : ∀ σ, 0 ≤ P σ) (hsum : ∑ σ, P σ = 1) (k : ℕ) (i : Fin m) :
    0 ≤ marg P k i ∧ marg P k i ≤ 1 := by
  have hind : ∀ σ, 0 ≤ inPrefixInd σ k i ∧ inPrefixInd σ k i ≤ 1 := fun σ => by
    unfold inPrefixInd; split_ifs <;> norm_num
  refine ⟨Finset.sum_nonneg fun σ _ => mul_nonneg (hnn σ) (hind σ).1, ?_⟩
  rw [← hsum]
  exact Finset.sum_le_sum fun σ _ => by
    have := hnn σ; have := (hind σ).2; nlinarith

/-- **At `η = m` the band is vacuous.** -/
theorem feasible_m_eq :
    FeasibleAt (id : Equiv.Perm (Fin m) → _) (m : ℝ) = {P | (∀ σ, 0 ≤ P σ) ∧ ∑ σ, P σ = 1} := by
  ext P
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun ⟨hnn, hsum⟩ => ⟨hnn, hsum, fun k hk i => ?_⟩⟩
  have hm := m_pos (m := m)
  obtain ⟨h0, h1⟩ := marg_mem P hnn hsum k i
  have hk0 : 0 ≤ (k : ℝ) / m := by positivity
  have hk1 : (k : ℝ) / m ≤ 1 := by
    rw [div_le_one hm]; exact_mod_cast hk
  rw [div_self hm.ne']
  show |marg P k i - (k : ℝ) / m| ≤ 1
  rw [abs_le]; constructor <;> linarith

theorem feasible_sub_m (η : ℝ) :
    FeasibleAt (id : Equiv.Perm (Fin m) → _) η ⊆ FeasibleAt (id : Equiv.Perm (Fin m) → _) m := by
  rw [feasible_m_eq]
  exact fun P h => ⟨h.1, h.2.1⟩

/-! ## 1. Compactness and attainment -/

theorem continuous_marg (k : ℕ) (i : Fin m) : Continuous fun P : Law m => marg P k i :=
  continuous_finsetSum _ fun σ _ => (continuous_apply σ).mul continuous_const

theorem continuous_dev : Continuous (dev (m := m)) := by
  unfold dev
  refine Continuous.finset_sup'_apply _ fun p _ => ?_
  exact continuous_const.mul (((continuous_marg _ _).sub continuous_const).abs)

theorem continuous_obj (g : Fin m → ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    Continuous fun P : Law m => trueObjective g P K hK := by
  unfold trueObjective
  refine Continuous.finset_sup'_apply _ fun k _ => ?_
  exact continuous_finsetSum _ fun σ _ => (continuous_apply σ).mul continuous_const

theorem isCompact_feasible (η : ℝ) :
    IsCompact (FeasibleAt (id : Equiv.Perm (Fin m) → _) η) := by
  have hset : FeasibleAt (id : Equiv.Perm (Fin m) → _) η
      = ((⋂ σ, {P : Law m | 0 ≤ P σ}) ∩ {P | ∑ σ, P σ = 1}) ∩ {P | dev P ≤ η} := by
    ext P
    rw [feasible_iff_dev]
    simp [and_assoc]
  rw [hset]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine IsClosed.inter (IsClosed.inter ?_ ?_) (isClosed_le continuous_dev continuous_const)
    · exact isClosed_iInter fun σ => isClosed_le continuous_const (continuous_apply σ)
    · exact isClosed_eq (continuous_finsetSum _ fun σ _ => continuous_apply σ) continuous_const
  · refine (isBounded_iff_forall_norm_le.mpr ⟨1, fun P hP => ?_⟩)
    obtain ⟨⟨hnn, hsum⟩, -⟩ := hP
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hnn hsum
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun σ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn σ), ← hsum]
    exact Finset.single_le_sum (f := P) (fun σ _ => hnn σ) (Finset.mem_univ σ)

/-- **The value is attained.** -/
theorem attain_value (g : Fin m → ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) (η : ℝ)
    (hη : 0 ≤ η) :
    ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η,
      trueObjective g P K hK = trueValue g η K hK := by
  obtain ⟨P, hP, hmin⟩ := (isCompact_feasible η).exists_isMinOn
    (allPerm_feasible_nonempty m η hη) (continuous_obj g K hK).continuousOn
  refine ⟨P, hP, ?_⟩
  unfold trueValue
  have hl : IsLeast ((fun P => trueObjective g P K hK) ''
      FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (trueObjective g P K hK) :=
    ⟨⟨P, hP, rfl⟩, by rintro _ ⟨Q, hQ, rfl⟩; exact hmin hQ⟩
  exact hl.csInf_eq.symm

/-- **The free value.** -/
noncomputable def Vfree (g : Fin m → ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : ℝ :=
  trueValue g m K hK

/-- The free optima. -/
def OptFree (g : Fin m → ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : Set (Law m) :=
  FeasibleAt (id : Equiv.Perm (Fin m) → _) m ∩ {P | trueObjective g P K hK = Vfree g K hK}

/-- **The free threshold.** -/
noncomputable def etaFree (g : Fin m → ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : ℝ :=
  sInf (dev '' OptFree g K hK)

theorem optFree_nonempty (g : Fin m → ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    (OptFree g K hK).Nonempty := by
  obtain ⟨P, hP, hv⟩ := attain_value g K hK m (Nat.cast_nonneg m)
  exact ⟨P, hP, hv⟩

/-- **The threshold is attained.** -/
theorem attain_eta (g : Fin m → ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    ∃ P ∈ OptFree g K hK, dev P = etaFree g K hK := by
  have hc : IsCompact (OptFree g K hK) :=
    (isCompact_feasible m).inter_right (isClosed_eq (continuous_obj g K hK) continuous_const)
  obtain ⟨P, hP, hmin⟩ := hc.exists_isMinOn (optFree_nonempty g K hK) continuous_dev.continuousOn
  refine ⟨P, hP, ?_⟩
  unfold etaFree
  have hl : IsLeast (dev '' OptFree g K hK) (dev P) :=
    ⟨⟨P, hP, rfl⟩, by rintro _ ⟨Q, hQ, rfl⟩; exact hmin hQ⟩
  exact hl.csInf_eq.symm

theorem etaFree_nonneg (g : Fin m → ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    0 ≤ etaFree g K hK := by
  obtain ⟨P, -, hP⟩ := attain_eta g K hK
  rw [← hP]; exact dev_nonneg P

theorem etaFree_le_m (g : Fin m → ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    etaFree g K hK ≤ m := by
  obtain ⟨P, hP, hdev⟩ := attain_eta g K hK
  rw [← hdev]
  exact ((feasible_iff_dev P m).mp hP.1).2.2

theorem value_le_of_sub (g : Fin m → ℝ) (hg : 0 < normMass g) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (η η' : ℝ) (hη : 0 ≤ η)
    (hsub : FeasibleAt (id : Equiv.Perm (Fin m) → _) η
      ⊆ FeasibleAt (id : Equiv.Perm (Fin m) → _) η') :
    trueValue g η' K hK ≤ trueValue g η K hK := by
  unfold trueValue
  obtain ⟨P, hP⟩ := allPerm_feasible_nonempty m η hη
  exact csInf_le_csInf (trueValue_bddBelow g hg η' K hK) ⟨_, P, hP, rfl⟩
    (Set.image_mono hsub)

theorem free_le_value (g : Fin m → ℝ) (hg : 0 < normMass g) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (η : ℝ) (hη : 0 ≤ η) : Vfree g K hK ≤ trueValue g η K hK :=
  value_le_of_sub g hg K hK η m hη (feasible_sub_m η)

/-- **The band is free exactly from `η_free` on.** -/
theorem free_threshold (g : Fin m → ℝ) (hg : 0 < normMass g) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (η : ℝ) (hη : 0 ≤ η) :
    trueValue g η K hK = Vfree g K hK ↔ etaFree g K hK ≤ η := by
  constructor
  · intro heq
    obtain ⟨P, hP, hv⟩ := attain_value g K hK η hη
    have hopt : P ∈ OptFree g K hK := ⟨feasible_sub_m η hP, hv.trans heq⟩
    have hbdd : BddBelow (dev '' OptFree g K hK) :=
      ⟨0, by rintro _ ⟨Q, -, rfl⟩; exact dev_nonneg Q⟩
    exact (csInf_le hbdd ⟨P, hopt, rfl⟩).trans ((feasible_iff_dev P η).mp hP).2.2
  · intro hle
    obtain ⟨P, hP, hdev⟩ := attain_eta g K hK
    have hPm := (feasible_iff_dev P m).mp hP.1
    have hPη : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η :=
      (feasible_iff_dev P η).mpr ⟨hPm.1, hPm.2.1, hdev.trans_le hle⟩
    apply le_antisymm
    · unfold trueValue
      rw [show Vfree g K hK = trueObjective g P K hK from hP.2.symm]
      exact csInf_le (trueValue_bddBelow g hg η K hK) ⟨P, hPη, rfl⟩
    · exact free_le_value g hg K hK η hη

/-! ## 2. The flow form of the threshold -/

/-- The value of the count-flow program at band `η`. -/
noncomputable def flowValue {d : ℕ} (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : ℝ :=
  sInf ((fun y => K.sup' hK y) ''
    {y | ∃ F, CountFeasibleH ty F ∧ FlowBand ty F η ∧ flowObj (typedCost ty wt) F = y})

theorem trueValue_eq_flow {d : ℕ} (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty) :
    trueValue (typedG ty wt) η K hK = flowValue ty wt η K hK := by
  unfold flowValue
  rw [← typed_banded_infima ty wt η (fun y => K.sup' hK y)]
  unfold trueValue trueObjective
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, hP, rfl⟩; exact ⟨_, ⟨P, hP, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨P, hP, rfl⟩, rfl⟩; exact ⟨P, hP, rfl⟩

/-- **The threshold, read off the flow program.** -/
theorem free_threshold_flow {d : ℕ} (ty : Fin m → Fin d) (wt : Fin d → ℝ)
    (hg : 0 < normMass (typedG ty wt)) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) (η : ℝ)
    (hη : 0 ≤ η) :
    flowValue ty wt η K hK = flowValue ty wt m K hK ↔ etaFree (typedG ty wt) K hK ≤ η := by
  rw [← trueValue_eq_flow, ← trueValue_eq_flow]
  exact free_threshold (typedG ty wt) hg K hK η hη

/-! ## 3. The size of the flow program -/

theorem mult_le {d : ℕ} (ty : Fin m → Fin d) (τ : Fin d) : mult ty τ ≤ m := by
  unfold mult
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

/-- The box of count states below the multiplicities. -/
noncomputable def box {d : ℕ} (ty : Fin m → Fin d) : Finset (CState d m) :=
  Fintype.piFinset fun τ => Finset.Iic (⟨mult ty τ, Nat.lt_succ_of_le (mult_le ty τ)⟩ : Fin (m + 1))

/-- **A count-feasible flow lives on the box.** -/
theorem support_box {d : ℕ} (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) (k : ℕ) (v : CState d m) (hv : F.x k v ≠ 0) : v ∈ box ty := by
  unfold box
  rw [Fintype.mem_piFinset]
  intro τ
  rw [Finset.mem_Iic, Fin.le_def]
  exact hF.2.2.2 k v hv τ

/-- **The box has `Π_τ (n_τ + 1)` states.** -/
theorem card_box {d : ℕ} (ty : Fin m → Fin d) : (box ty).card = ∏ τ, (mult ty τ + 1) := by
  unfold box
  rw [Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun τ _ => by rw [Fin.card_Iic]

/-! ## 4. The additive price -/

/-- **The additive price of the band.** -/
noncomputable def gap (g : Fin m → ℝ) (η : ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty) : ℝ :=
  trueValue g η K hK - Vfree g K hK

theorem gap_nonneg (g : Fin m → ℝ) (hg : 0 < normMass g) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (η : ℝ) (hη : 0 ≤ η) : 0 ≤ gap g η K hK := by
  unfold gap; linarith [free_le_value g hg K hK η hη]

theorem gap_antitone (g : Fin m → ℝ) (hg : 0 < normMass g) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (η η' : ℝ) (hη : 0 ≤ η) (hle : η ≤ η') :
    gap g η' K hK ≤ gap g η K hK := by
  unfold gap
  have := value_le_of_sub g hg K hK η η' hη
    (feasible_mono id η η' (Nat.pos_of_ne_zero (NeZero.ne m)) hle)
  linarith

theorem gap_zero_iff (g : Fin m → ℝ) (hg : 0 < normMass g) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (η : ℝ) (hη : 0 ≤ η) :
    gap g η K hK = 0 ↔ etaFree g K hK ≤ η := by
  unfold gap
  rw [sub_eq_zero]
  exact free_threshold g hg K hK η hη

/-- **The additive price is stable**, with no lower bound on the free value. -/
theorem gap_stable (g g' : Fin m → ℝ) (η : ℝ) (hη : 0 ≤ η) (K : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (d : ℝ) (hd : 0 < d) (hg : d ≤ normMass g) (hg' : d ≤ normMass g') :
    |gap g η K hK - gap g' η K hK| ≤ 6 * l1 g g' / d := by
  unfold gap Vfree
  have h1 := trueValue_stable g g' η hη K hK d hd hg hg'
  have h2 := trueValue_stable g g' m (Nat.cast_nonneg m) K hK d hd hg hg'
  have e : trueValue g η K hK - trueValue g m K hK - (trueValue g' η K hK - trueValue g' m K hK)
      = (trueValue g η K hK - trueValue g' η K hK) - (trueValue g m K hK - trueValue g' m K hK) := by
    ring
  rw [e]
  calc _ ≤ |trueValue g η K hK - trueValue g' η K hK| + |trueValue g m K hK - trueValue g' m K hK| :=
        abs_sub _ _
    _ ≤ 3 * l1 g g' / d + 3 * l1 g g' / d := add_le_add h1 h2
    _ = 6 * l1 g g' / d := by ring

#print axioms feasible_iff_dev
#print axioms feasible_m_eq
#print axioms attain_value
#print axioms attain_eta
#print axioms free_threshold
#print axioms trueValue_eq_flow
#print axioms free_threshold_flow
#print axioms support_box
#print axioms card_box
#print axioms gap_nonneg
#print axioms gap_antitone
#print axioms gap_zero_iff
#print axioms gap_stable

end CIGAMF.P13.PaperCFreeBand
