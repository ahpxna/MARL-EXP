import Mathlib
import «LeanSupportGeometryV4»

/-! Finite conditional-reference semantics.  `Riso` and `Rfeas` are distinct. -/

namespace CIGAMF.V4

open scoped BigOperators
open SupportGeometry

namespace Riso

variable {A : Type*} [Fintype A] [Nonempty A]

def response (primitive complement : A → ℝ) : A → ℝ :=
  fun a => primitive a + complement a

theorem R2_primitive_isolation_span_bound (primitive complement : A → ℝ) :
    |osc (response primitive complement) - osc primitive| ≤ osc complement := by
  change |osc (fun a => primitive a + complement a) - osc primitive| ≤ osc complement
  exact osc_add_deviation primitive complement

theorem R3_reference_independent_exact
    (primitive complement : A → ℝ) (c : ℝ)
    (hconstant : ∀ a, complement a = c) :
    osc (response primitive complement) = osc primitive := by
  have hz : osc complement = 0 := by
    have hfun : complement = fun _ => c := funext hconstant
    rw [hfun]
    let a0 : A := Classical.choice (inferInstance : Nonempty A)
    have hmax : maxVal (fun _ : A => c) = c := by
      apply le_antisymm
      · exact maxVal_le _ (fun _ => le_rfl)
      · exact le_maxVal (fun _ : A => c) a0
    have hmin : minVal (fun _ : A => c) = c := by
      apply le_antisymm
      · exact minVal_le _ a0
      · exact le_minVal _ (fun _ => le_rfl)
    simp [osc, hmax, hmin]
  have h := R2_primitive_isolation_span_bound primitive complement
  rw [hz] at h
  have habs : |osc (response primitive complement) - osc primitive| = 0 :=
    le_antisymm h (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

theorem R5_residual_rho_le_two_eta
    (residualExpectation : A → ℝ) (eta : ℝ)
    (hbound : ∀ a, |residualExpectation a| ≤ eta) :
    osc residualExpectation ≤ 2 * eta := by
  have hmax : maxVal residualExpectation ≤ eta := by
    apply maxVal_le
    intro a
    exact (abs_le.mp (hbound a)).2
  have hmin : -eta ≤ minVal residualExpectation := by
    apply le_minVal
    intro a
    exact (abs_le.mp (hbound a)).1
  simp only [osc]
  linarith

theorem R6_near_additive_isolation
    (primitive complement residualExpectation : A → ℝ) :
    |osc (fun a => primitive a + complement a + residualExpectation a) - osc primitive|
      ≤ osc complement + osc residualExpectation := by
  have h₁ := osc_add_deviation (fun a => primitive a + complement a) residualExpectation
  have h₂ := osc_add_deviation primitive complement
  calc
    |osc (fun a => primitive a + complement a + residualExpectation a) - osc primitive|
        ≤ |osc (fun a => primitive a + complement a + residualExpectation a) -
             osc (fun a => primitive a + complement a)| +
           |osc (fun a => primitive a + complement a) - osc primitive| := by
             exact abs_sub_le _ _ _
    _ ≤ osc residualExpectation + osc complement := add_le_add h₁ h₂
    _ = osc complement + osc residualExpectation := add_comm _ _

end Riso

namespace Rfeas

/- The feasible response is its own typed target.  No `chi_iso` quantity is
part of this definition. -/
structure FeasibleResponse (A : Type*) where
  value : A → ℝ

noncomputable def capacity {A : Type*} [Fintype A] [Nonempty A]
    (q : FeasibleResponse A) : ℝ := osc q.value

end Rfeas

namespace ReferenceFidelity

variable {A L U : Type*}
variable [Fintype A] [Nonempty A] [Fintype L] [Fintype U]
variable [DecidableEq L] [DecidableEq U]

/- `kappa a l u` is the l-th coordinate marginal mass at value u under the
conditional kernel row indexed by source action a.  No positivity or full
support is needed for the linear characterization. -/
def additiveComplementExpectation
    (kappa : A → L → U → ℝ) (h : L → U → ℝ) (a : A) : ℝ :=
  Finset.univ.sum (fun l => Finset.univ.sum (fun u => kappa a l u * h l u))

def UniversalAdditiveConstancy (kappa : A → L → U → ℝ) : Prop :=
  ∀ h : L → U → ℝ, ∀ a a' : A,
    additiveComplementExpectation kappa h a =
      additiveComplementExpectation kappa h a'

def CoordinateMarginalInvariant (kappa : A → L → U → ℝ) : Prop :=
  ∀ l u a a', kappa a l u = kappa a' l u

theorem RF1_universal_fidelity_iff_marginal_invariance
    (kappa : A → L → U → ℝ) :
    UniversalAdditiveConstancy kappa ↔ CoordinateMarginalInvariant kappa := by
  constructor
  · intro hUniversal l u a a'
    let basis : L → U → ℝ := fun l' u' =>
      if l' = l then (if u' = u then 1 else 0) else 0
    have h := hUniversal basis a a'
    simpa [additiveComplementExpectation, basis] using h
  · intro hInvariant h a a'
    unfold additiveComplementExpectation
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro u _
    rw [hInvariant l u a a']

theorem RF2_fidelity_implies_constant_complement
    (kappa : A → L → U → ℝ)
    (hInv : CoordinateMarginalInvariant kappa)
    (h : L → U → ℝ) (a a' : A) :
    additiveComplementExpectation kappa h a =
      additiveComplementExpectation kappa h a' := by
  exact (RF1_universal_fidelity_iff_marginal_invariance kappa).2 hInv h a a'

end ReferenceFidelity

end CIGAMF.V4
