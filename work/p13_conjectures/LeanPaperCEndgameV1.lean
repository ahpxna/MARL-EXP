import «LeanPaperCEvenWitnessJoinV1»
import «LeanPaperCOddWitnessJoinV1»
import «LeanPaperCBandValueBridgeV1»
import «LeanPaperCFlowBandJoinV1»

/-!
DRAFT ENDGAME — not compiled. This is the downstream theorem assembly, not another witness
construction. It uses ALL interior budgets and ALL permutations of the actual gFamily.
Two upstream obligations remain named in EvenEndpointData: a concrete band-feasible free
law and a per-ranking sum lower bound. No such object is constructed by this file; until
an instance is supplied, even_frontier is a CONDITIONAL assembly, not a closed headline.
The zero-band parity theorems use the concrete joins already written in the earlier batch.
-/
namespace CIGAMF.P13.PaperCEndgame
open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet
open CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCEvenWitnessJoin
open CIGAMF.P13.PaperCOddWitnessJoin CIGAMF.P13.PaperCBandValueBridge

abbrev Perm (m : ℕ) := Equiv.Perm (Fin m)
def budgets (m : ℕ) : Finset ℕ := Icc 1 (m-1)
lemma budgets_nonempty (m : ℕ) (hm : 2 ≤ m) : (budgets m).Nonempty :=
  ⟨1,by simp [budgets]; omega⟩
noncomputable def denom (m : ℕ) : ℝ := (m:ℝ)+4
noncomputable def freeValue (m : ℕ) : ℝ := 2/(denom m*((m:ℝ)-1))
noncomputable def etaStar (m : ℕ) : ℝ := ((m:ℝ)-2)/(2*((m:ℝ)-1))
noncomputable def objective (m : ℕ) (hm : 2 ≤ m) (P : Perm m → ℝ) : ℝ :=
  maxRegret P (gFamily m) id (denom m) (budgets m) (budgets_nonempty m hm)
noncomputable def value (m : ℕ) (hm : 2 ≤ m) (η : ℝ) : ℝ :=
  Vm (gFamily m) id (denom m) η (budgets m) (budgets_nonempty m hm)
noncomputable def blend {ι : Type*} (t : ℝ) (P Q : ι → ℝ) :=
  fun x => (1-t)*P x+t*Q x

lemma blend_feasible {m : ℕ} (P Q : Perm m → ℝ) (a b t : ℝ)
    (hP : P ∈ FeasibleAt id a) (hQ : Q ∈ FeasibleAt id b) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    blend t P Q ∈ FeasibleAt id ((1-t)*a+t*b) := by
  classical
  refine ⟨fun x => add_nonneg (mul_nonneg (by linarith) (hP.1 x))
    (mul_nonneg ht (hQ.1 x)),?_,?_⟩
  · simp only [blend, sum_add_distrib, ← mul_sum, hP.2.1, hQ.2.1]; ring
  · intro k hk i
    have heq : (∑ σ, blend t P Q σ * inPrefixInd σ k i)-(k:ℝ)/(m:ℝ) =
        (1-t)*((∑ σ,P σ*inPrefixInd σ k i)-(k:ℝ)/(m:ℝ)) +
        t*((∑ σ,Q σ*inPrefixInd σ k i)-(k:ℝ)/(m:ℝ)) := by
      have hpt : ∀ σ, blend t P Q σ * inPrefixInd σ k i
          = (1-t) * (P σ * inPrefixInd σ k i) + t * (Q σ * inPrefixInd σ k i) := by
        intro σ; unfold blend; ring
      rw [Finset.sum_congr rfl (fun σ _ => hpt σ), Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [heq]
    calc _ ≤ |(1-t)*((∑ σ,P σ*inPrefixInd σ k i)-(k:ℝ)/(m:ℝ))| +
          |t*((∑ σ,Q σ*inPrefixInd σ k i)-(k:ℝ)/(m:ℝ))| := abs_add _ _
      _ ≤ (1-t)*(a/(m:ℝ))+t*(b/(m:ℝ)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg (by linarith : 0 ≤ 1-t)]
        exact add_le_add (mul_le_mul_of_nonneg_left (hP.2.2 k hk i) (by linarith))
          (mul_le_mul_of_nonneg_left (hQ.2.2 k hk i) ht)
      _ = _ := by ring

lemma objective_blend_le {m : ℕ} (hm : 2 ≤ m) (P Q : Perm m → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    objective m hm (blend t P Q) ≤ (1-t)*objective m hm P+t*objective m hm Q := by
  classical
  unfold objective maxRegret
  apply Finset.sup'_le
  intro k hk
  have hsplit : (∑ σ, blend t P Q σ * regret (gFamily m) (id σ) (denom m) k)
      = (1-t) * (∑ σ, P σ * regret (gFamily m) (id σ) (denom m) k)
        + t * (∑ σ, Q σ * regret (gFamily m) (id σ) (denom m) k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun σ _ => by unfold blend; ring)
  rw [hsplit]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_sup' _ hk) (by linarith))
    (mul_le_mul_of_nonneg_left (le_sup' _ hk) ht)

lemma value_le_witness (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (P : Perm m → ℝ)
    (hP : P ∈ FeasibleAt id η) : value m (by omega) η ≤ objective m (by omega) P := by
  apply csInf_le
  · exact Vm_bddBelow (gFamily m) id (denom m) η (by first | positivity | (unfold denom; positivity) | linarith | nlinarith)
      (budgets m) (budgets_nonempty m (by omega))
      (fun k hk => by simp [budgets] at hk; omega)
      (fun σ i => gFamily_weights m (σ i))
  · exact ⟨P,hP,rfl⟩

lemma value_lower (m : ℕ) (hm : 3 ≤ m) (η c : ℝ) (hη : 0≤η)
    (h : ∀ P ∈ FeasibleAt (id : Perm m → _) η, c ≤ objective m (by omega) P) :
    c ≤ value m (by omega) η := by
  letI : NeZero m := ⟨by omega⟩
  apply le_csInf ((allPerm_feasible_nonempty m η hη).image _)
  rintro _ ⟨P,hP,rfl⟩
  exact h P hP

/-- Explicit upstream proof interface, NOT an existence assertion. Endpoint is an actual
law; rankSum is universal over permutations. A solved menu or per-size LP cannot fill it. -/
structure EvenEndpointData (m : ℕ) (hm : 4 ≤ m) where
  endpoint : Perm m → ℝ
  endpoint_band : endpoint ∈ FeasibleAt id (etaStar m)
  endpoint_value : objective m (by omega) endpoint ≤ freeValue m
  rankSum : ∀ σ : Perm m,
    2/denom m ≤ ∑ k ∈ budgets m, regret (gFamily m) σ (denom m) k

lemma universal_free_lower (m : ℕ) (hm : 4 ≤ m) (E : EvenEndpointData m hm)
    (P : Perm m → ℝ) (hP : ∀ σ,0 ≤ P σ) (hP1 : ∑ σ,P σ=1) :
    freeValue m ≤ objective m (by omega) P := by
  classical
  have hsum : 2/denom m ≤ ∑ k ∈ budgets m,
      ∑ σ,P σ*regret (gFamily m) σ (denom m) k := by
    rw [sum_comm]
    calc 2/denom m = ∑ σ,P σ*(2/denom m) := by rw [← sum_mul,hP1,one_mul]
      _ ≤ ∑ σ,P σ*∑ k ∈ budgets m,regret (gFamily m) σ (denom m) k := by
        apply sum_le_sum; intro σ hσ
        exact mul_le_mul_of_nonneg_left (E.rankSum σ) (hP σ)
      _ = _ := by simp_rw [mul_sum]
  have hmax : (∑ k ∈ budgets m,∑ σ,P σ*regret (gFamily m) σ (denom m) k)
      ≤ ((m:ℝ)-1)*objective m (by omega) P := by
    calc _ ≤ ∑ _k ∈ budgets m, objective m (by omega) P := by
            apply sum_le_sum; intro k hk; exact le_sup' _ hk
      _ = _ := by simp [budgets, Nat.cast_sub (by omega : 1 ≤ m)]; try ring
  unfold freeValue
  rw [← div_div, div_le_iff₀ (by first | positivity | linarith | nlinarith)]
  exact hsum.trans hmax

lemma even_value_zero (m : ℕ) (hm : 4 ≤ m) (heven : Even m) :
    value m (by omega) 0 = 4/((m:ℝ)*denom m) := by
  exact even_allPerm_value m heven hm (budgets m) (budgets_nonempty m (by omega))
    (by simp [budgets]; try omega) (fun k hk => by simpa [budgets] using hk)

/-- FINAL even frontier, conditional only on the two named upstream obligations above. -/
theorem even_frontier (m : ℕ) (hm : 4 ≤ m) (heven : Even m)
    (E : EvenEndpointData m hm) (η : ℝ) (hη : 0≤η) :
    value m (by omega) η = max (freeValue m) (4*(1-η)/((m:ℝ)*denom m)) := by
  have hmR : (4:ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < etaStar m := by
    unfold etaStar
    apply div_pos <;> linarith
  have hfree := value_lower m (by omega) η (freeValue m) hη
    (fun P hP => universal_free_lower m hm E P hP.1 hP.2.1)
  have hband : 4*(1-η)/((m:ℝ)*denom m) ≤ value m (by omega) η := by
    convert Vm_allPerm_ge_band (m-2) (by omega) (by omega) (denom m) η
      (by first | positivity | (unfold denom; positivity) | linarith | nlinarith) hη (budgets m) (budgets_nonempty m (by omega))
      (by simp [budgets]; try omega) (by simp [budgets]; try omega) using 1 <;>
      simp [Nat.sub_add_cancel (by omega : 2 ≤ m), Nat.cast_sub (by omega : 2 ≤ m)]
  apply le_antisymm
  · by_cases hηs : η≤etaStar m
    · obtain ⟨P0,hP0,hV0⟩ := even_allPerm_witness m heven hm (budgets m)
        (budgets_nonempty m (by omega)) (fun k hk => by simpa [budgets] using hk)
      let t := η/etaStar m
      have ht : 0 ≤ t := div_nonneg hη hs.le
      have ht1 : t ≤ 1 := (div_le_one hs).2 hηs
      have hPf : blend t P0 E.endpoint ∈ FeasibleAt id η := by
        have h := blend_feasible P0 E.endpoint 0 (etaStar m) t hP0 E.endpoint_band ht ht1
        simpa [t,ne_of_gt hs] using h
      have hlinear : (1-t)*(4/((m:ℝ)*denom m))+t*freeValue m
          = 4*(1-η)/((m:ℝ)*denom m) := by
        dsimp [t,etaStar,freeValue,denom]
        field_simp; try ring
      calc value m (by omega) η ≤ objective m (by omega) (blend t P0 E.endpoint) :=
          value_le_witness m (by omega) η _ hPf
        _ ≤ (1-t)*objective m (by omega) P0+t*objective m (by omega) E.endpoint :=
          objective_blend_le (by omega) _ _ t ht ht1
        _ ≤ (1-t)*(4/((m:ℝ)*denom m))+t*freeValue m := by
          rw [show objective m (by omega) P0=4/((m:ℝ)*denom m) from hV0]
          gcongr; exact E.endpoint_value
        _ = 4*(1-η)/((m:ℝ)*denom m) := hlinear
        _ ≤ _ := le_max_right _ _
    · have hPf := feasible_mono (id : Perm m → _) (etaStar m) η (by omega)
        (le_of_not_ge hηs) E.endpoint_band
      exact (value_le_witness m (by omega) η _ hPf).trans
        (E.endpoint_value.trans (le_max_left _ _))
  · exact max_le hfree hband

/-- No bisection/tolerance in the breakpoint definition. -/
theorem even_breakpoint_iff (m : ℕ) (hm : 4 ≤ m) (heven : Even m)
    (E : EvenEndpointData m hm) (η : ℝ) (hη : 0≤η) :
    value m (by omega) η = freeValue m ↔ etaStar m ≤ η := by
  rw [even_frontier m hm heven E η hη, max_eq_left_iff]
  unfold etaStar freeValue
  have hmR : (4:ℝ) ≤ m := by exact_mod_cast hm
  rw [div_le_div_iff₀ (by first | positivity | (unfold denom; positivity) | linarith | nlinarith) (by first | positivity | (unfold denom; positivity) | linarith | nlinarith), div_le_iff₀ (by first | positivity | (unfold denom; positivity) | linarith | nlinarith)]
  unfold denom at *
  constructor <;> intro h <;> nlinarith

/-- The odd zero-band law is a concrete result from the earlier join, not an endpoint
assumption. No odd positive-band frontier is inferred from the even formula. -/
theorem odd_value_zero (s : ℕ) :
    value (2*s+3) (by omega) 0 =
      (((2*s+3:ℕ):ℝ)+3)/(((2*s+3:ℕ):ℝ)*denom (2*s+3)) := by
  exact odd_allPerm_value s (budgets (2*s+3)) (budgets_nonempty _ (by omega))
    (fun k hk => by simp [budgets] at hk; omega) (by simp [budgets]; try omega)

theorem odd_uniform_price_ratio (s : ℕ) :
    value (2*s+3) (by omega) 0 / freeValue (2*s+3) =
      ((((2*s+3:ℕ):ℝ)+3)*(((2*s+3:ℕ):ℝ)-1))/(2*((2*s+3:ℕ):ℝ)) := by
  rw [odd_value_zero]
  unfold freeValue denom
  field_simp; try ring

/-- OPEN terminal target for the separate odd-breakpoint argument. This is a definition
of the requested result, not a theorem claiming the narrow window is already closed. -/
def OddBreakpointFinish : Prop :=
  ∀ s : ℕ, ∀ η : ℝ, 0≤η →
    (value (2*s+3) (by omega) η = freeValue (2*s+3) ↔ 1≤η)

#print axioms blend_feasible
#print axioms universal_free_lower
#print axioms even_frontier
#print axioms even_breakpoint_iff
#print axioms odd_value_zero
#print axioms odd_uniform_price_ratio
end CIGAMF.P13.PaperCEndgame
