import «LeanPaperCEndgameV1»
import «LeanPaperCFrontierV1»
import «LeanPaperBTipV1»

/-!
DRAFT ENDGAME — not compiled. New downstream generalization: real signed weights, actual
selectedRadius, a RECOMPUTED optimal baseline, and a MOVING normalization.
No fixed-weight type partition is used in the optimization domain: all permutations with
item-marginal bands are retained, so small perturbations do not secretly change feasibility.

The generic physical/stability results are independent of the special gFamily. To transfer
the exact parity formulas from the earlier batch, FamilyBaselineIdentification below must
be instantiated (parity lower bound plus a cardinality-k subset attaining parity). It is
explicitly an OPEN join, not supplied as an axiom or hidden in the loss definition.
-/
namespace CIGAMF.P13.PaperCStabilityEndgame
open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.PaperCFrontier CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperBTip (osc_bool_of_zero)
variable {m : ℕ}

noncomputable def parts (g : Fin m → ℝ) (i : Fin m) (b : Bool) : ℝ :=
  if b then g i else 0

/-- A prefix of k DISCARDED components corresponds to retaining its complement, of size m-k. -/
theorem physical_radius (g : Fin m → ℝ) (S : Finset (Fin m)) :
    selectedRadius (parts g) Sᶜ = |∑ i ∈ S,g i|/2 := by
  classical
  unfold selectedRadius supportOsc
  rw [compl_compl, osc_bool_of_zero]
  · simp [sumComponent, parts]
  · simp [sumComponent, parts]

noncomputable def prefixSet (σ : Equiv.Perm (Fin m)) (k : Fin (m+1)) : Finset (Fin m) :=
  univ.filter (fun i => (σ.symm i).val < k.val)

lemma prefixSet_card (σ : Equiv.Perm (Fin m)) (k : Fin (m+1)) :
    (prefixSet σ k).card=k.val := by
  classical
  have he : prefixSet σ k = (univ.filter (fun i : Fin m => i.val < k.val)).map σ.toEmbedding := by
    ext i; simp [prefixSet]
  rw [he,card_map]
  simp [Finset.card_filter, Fin.sum_univ_eq_sum_range, Nat.le_of_lt_succ k.isLt]

lemma subsets_nonempty (k : Fin (m+1)) :
    (univ.filter (fun S : Finset (Fin m) => S.card=k.val)).Nonempty :=
  ⟨prefixSet 1 k,by simp [prefixSet_card]⟩

noncomputable def trueBaseline (g : Fin m → ℝ) (k : Fin (m+1)) : ℝ :=
  baseline k.val (subsets_nonempty k) g

noncomputable def bestPhysicalLoss (g : Fin m → ℝ) (k : Fin (m+1)) : ℝ :=
  (univ.filter (fun S : Finset (Fin m) => S.card=k.val)).inf' (subsets_nonempty k)
    (fun S => selectedRadius (parts g) Sᶜ)

/-- The baseline is the actual minimum of selectedRadius over retained size m-k. -/
theorem physical_minimum (g : Fin m → ℝ) (k : Fin (m+1)) :
    bestPhysicalLoss g k=trueBaseline g k/2 := by
  classical
  unfold bestPhysicalLoss trueBaseline baseline
  simp_rw [physical_radius]
  apply le_antisymm
  · obtain ⟨S,hS,hmin⟩ := Finset.exists_mem_eq_inf'
      (univ.filter (fun S : Finset (Fin m) => S.card=k.val)) (subsets_nonempty k)
      (fun S => |∑ i ∈ S,g i|)
    rw [← hmin]
    exact inf'_le _ hS
  · apply le_inf'
    intro S hS
    exact div_le_div_of_nonneg_right (inf'_le _ hS) (by norm_num)

noncomputable def normMass (g : Fin m → ℝ) : ℝ := ∑ i,|g i|
noncomputable def rawRegret (g : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (k : Fin (m+1)) : ℝ :=
  |∑ i ∈ prefixSet σ k,g i|-trueBaseline g k
noncomputable def normalizedRegret (g : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (k : Fin (m+1)) : ℝ := rawRegret g σ k/normMass g

/-- Normalization is by total component radius, normMass/2, not an arbitrary surrogate. -/
theorem physical_normalized_regret (g : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (k : Fin (m+1)) :
    (selectedRadius (parts g) (prefixSet σ k)ᶜ-bestPhysicalLoss g k)/(normMass g/2)
      = normalizedRegret g σ k := by
  rw [physical_radius,physical_minimum]
  unfold normalizedRegret rawRegret
  ring

lemma baseline_nonneg (g : Fin m → ℝ) (k : Fin (m+1)) : 0 ≤ trueBaseline g k := by
  apply le_inf'; intro S hS; exact abs_nonneg _

lemma baseline_le_prefix (g : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (k : Fin (m+1)) :
    trueBaseline g k≤|∑ i ∈ prefixSet σ k,g i| := by
  exact inf'_le _ (by simp [prefixSet_card])

lemma raw_bounds (g : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (k : Fin (m+1)) :
    0 ≤ rawRegret g σ k ∧ rawRegret g σ k ≤ normMass g := by
  have hp : |∑ i ∈ prefixSet σ k,g i|≤normMass g := by
    calc _ ≤ ∑ i ∈ prefixSet σ k,|g i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i,|g i| := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun i _ _ => abs_nonneg _)
  constructor
  · exact sub_nonneg.mpr (baseline_le_prefix g σ k)
  · dsimp [rawRegret]; linarith [baseline_nonneg g k]

lemma raw_stable (g g' : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (k : Fin (m+1)) :
    |rawRegret g σ k-rawRegret g' σ k|≤2*l1 g g' := by
  have h := regret_perturbation k.val (subsets_nonempty k) g g'
    (prefixSet σ k) 1 one_pos
  simpa [rawRegret,trueBaseline] using h

lemma normMass_stable (g g' : Fin m → ℝ) : |normMass g-normMass g'|≤l1 g g' := by
  unfold normMass l1
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _ => abs_abs_sub_abs_le_abs_sub _ _))

/-- The factor THREE pays for numerator (prefix + baseline) and moving denominator. -/
theorem normalized_regret_stable (g g' : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (k : Fin (m+1)) (d : ℝ) (hd : 0 < d) (hg : d ≤ normMass g) (hg' : d ≤ normMass g') :
    |normalizedRegret g σ k-normalizedRegret g' σ k|≤3*l1 g g'/d := by
  have hD : 0 < normMass g := hd.trans_le hg
  have hD' : 0 < normMass g' := hd.trans_le hg'
  have hR := raw_bounds g σ k
  have hR' := raw_bounds g' σ k
  have hδ : 0 ≤ l1 g g' := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hid : normalizedRegret g σ k-normalizedRegret g' σ k =
      (rawRegret g σ k-rawRegret g' σ k)/normMass g +
      (rawRegret g' σ k/normMass g')*((normMass g'-normMass g)/normMass g) := by
    unfold normalizedRegret
    field_simp; ring
  have hfrac : 0 ≤ rawRegret g' σ k/normMass g' ∧ rawRegret g' σ k/normMass g'≤1 :=
    ⟨div_nonneg hR'.1 hD'.le,(div_le_one hD').2 hR'.2⟩
  rw [hid]
  calc _ ≤ |(rawRegret g σ k-rawRegret g' σ k)/normMass g| +
        |(rawRegret g' σ k/normMass g')*((normMass g'-normMass g)/normMass g)| := abs_add _ _
    _ ≤ 2*l1 g g'/normMass g+l1 g g'/normMass g := by
      rw [abs_div,abs_mul,abs_div,abs_of_pos hD,abs_of_nonneg hfrac.1]
      apply add_le_add
      · exact div_le_div_of_nonneg_right (raw_stable g g' σ k) hD.le
      · have hnorm : |normMass g'-normMass g|≤l1 g g' := by
          rw [abs_sub_comm]; exact normMass_stable g g'
        exact (mul_le_mul_of_nonneg_right hfrac.2 (by positivity)).trans (by gcongr)
    _ = 3*l1 g g'/normMass g := by ring
    _ ≤ 3*l1 g g'/d := div_le_div_of_nonneg_left (by positivity) hd hg

noncomputable def trueObjective (g : Fin m → ℝ) (P : Equiv.Perm (Fin m) → ℝ)
    (K : Finset (Fin (m+1))) (hK : K.Nonempty) : ℝ :=
  K.sup' hK (fun k => ∑ σ,P σ*normalizedRegret g σ k)

noncomputable def trueValue (g : Fin m → ℝ) (η : ℝ)
    (K : Finset (Fin (m+1))) (hK : K.Nonempty) : ℝ :=
  sInf ((fun P => trueObjective g P K hK) '' FeasibleAt (id : Equiv.Perm (Fin m) → _) η)

lemma objective_stable (g g' : Fin m → ℝ) (P : Equiv.Perm (Fin m) → ℝ)
    (hP : ∀ σ,0 ≤ P σ) (hP1 : ∑ σ,P σ=1) (K : Finset (Fin (m+1))) (hK : K.Nonempty)
    (d : ℝ) (hd : 0 < d) (hg : d ≤ normMass g) (hg' : d ≤ normMass g') :
    |trueObjective g P K hK-trueObjective g' P K hK|≤3*l1 g g'/d := by
  apply abs_sup'_sub_le
  intro k hk
  exact abs_expect_sub_le P _ _ _ hP hP1
    (fun σ => normalized_regret_stable g g' σ k d hd hg hg')

lemma trueValue_bddBelow (g : Fin m → ℝ) (hg : 0 < normMass g) (η : ℝ)
    (K : Finset (Fin (m+1))) (hK : K.Nonempty) :
    BddBelow ((fun P => trueObjective g P K hK) '' FeasibleAt (id : Equiv.Perm (Fin m) → _) η) := by
  refine ⟨0,?_⟩
  rintro _ ⟨P,hP,rfl⟩
  obtain ⟨k,hk⟩ := hK
  apply le_trans _ (le_sup' _ hk)
  exact sum_nonneg (fun σ _ => mul_nonneg (hP.1 σ)
    (div_nonneg (raw_bounds g σ k).1 hg.le))

/-- The stability statement is about the full item-band optimum on arbitrary real weights.
It does not assume that perturbations preserve the original four weight classes. -/
theorem trueValue_stable (g g' : Fin m → ℝ) (η : ℝ) (hη : 0≤η) [NeZero m]
    (K : Finset (Fin (m+1))) (hK : K.Nonempty)
    (d : ℝ) (hd : 0 < d) (hg : d ≤ normMass g) (hg' : d ≤ normMass g') :
    |trueValue g η K hK-trueValue g' η K hK|≤3*l1 g g'/d := by
  exact value_stable_of_pointwise (FeasibleAt (id : Equiv.Perm (Fin m) → _) η)
    _ _ _ (allPerm_feasible_nonempty m η hη)
    (trueValue_bddBelow g (hd.trans_le hg) η K hK)
    (trueValue_bddBelow g' (hd.trans_le hg') η K hK)
    (fun P hP => objective_stable g g' P hP.1 hP.2.1 K hK d hd hg hg')

/-- OPEN transfer obligation for the special family. Prove parity as a lower bound and
construct a cardinality-k subset attaining it. For odd m, the last even budget is handled
by omitting a -1 item; do NOT reuse a zero-total argument from the even case. -/
def FamilyBaselineIdentification (m : ℕ) : Prop :=
  ∀ k : Fin (m+1), 1 ≤ k.val → k.val < m → trueBaseline (gFamily m) k=(k.val % 2:ℕ)

/-- Once the baseline is identified, the algebraic family regret is physical regret. -/
theorem family_regret_identification (hbase : FamilyBaselineIdentification m)
    (hnorm : normMass (gFamily m)=(m:ℝ)+4) (σ : Equiv.Perm (Fin m))
    (k : Fin (m+1)) (hk : 1 ≤ k.val) (hkm : k.val < m) :
    normalizedRegret (gFamily m) σ k=regret (gFamily m) σ ((m:ℝ)+4) k.val := by
  rw [normalizedRegret,rawRegret,hbase k hk hkm,hnorm]
  unfold regret excess prefixSum rankOf
  congr 2
  rw [sum_filter, ← Equiv.sum_comp σ]
  simp [prefixSet,Equiv.symm_apply_apply]

#print axioms physical_radius
#print axioms physical_minimum
#print axioms physical_normalized_regret
#print axioms normalized_regret_stable
#print axioms trueValue_stable
#print axioms family_regret_identification
end CIGAMF.P13.PaperCStabilityEndgame
