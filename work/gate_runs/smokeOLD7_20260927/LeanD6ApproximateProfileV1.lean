import «LeanD6ApproximateAnswersV1»
import «LeanOpenQuadraticProfileV1»

/-! Exact real infima for distance-dependent bad nuisance intervals.
Strict boundary and empty-domain cases are kept separate. -/
namespace CIGAMF.P13.D6ApproximateProfile
open Set
open CIGAMF.P13.D6ApproximateAnswers CIGAMF.P13.OpenQuadraticProfile
noncomputable section

def badDomain (d : ℕ) (eps : ℝ) : Set ℝ := {nu | BadNuisance d eps nu}

theorem bad_domain_closed (d : ℕ) (hd : 0 < d) (eps : ℝ)
    (ht : 1 < 2-2*eps/(d : ℝ)) : badDomain d eps = Icc 0 1 := by
  ext nu
  simp only [badDomain,mem_setOf_eq,bad_nuisance_interval d hd,mem_Icc]
  constructor
  · rintro ⟨h0,h1,_⟩; exact ⟨h0,h1⟩
  · rintro ⟨h0,h1⟩; exact ⟨h0,h1,h1.trans_lt ht⟩

theorem bad_domain_half_open (d : ℕ) (hd : 0 < d) (eps : ℝ)
    (ht : 2-2*eps/(d : ℝ) ≤ 1) : badDomain d eps = Ico 0 (2-2*eps/(d : ℝ)) := by
  ext nu
  simp only [badDomain,mem_setOf_eq,bad_nuisance_interval d hd,mem_Ico]
  constructor
  · rintro ⟨h0,_,h1⟩; exact ⟨h0,h1⟩
  · rintro ⟨h0,h1⟩; exact ⟨h0,h1.le.trans ht,h1⟩

theorem bad_domain_empty (d : ℕ) (eps : ℝ) (he : 0 ≤ eps) (hd : (d : ℝ) ≤ eps) :
    badDomain d eps = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro nu h
  have hh := (bad_nuisance_nonempty d eps he).mp ⟨nu,h⟩
  linarith

lemma closed_inf_eq_min (f : ℝ → ℝ) (U p : ℝ) (hp : p ∈ Icc 0 U)
    (hmin : ∀ x ∈ Icc 0 U, f p ≤ f x) : sInf (f '' Icc 0 U) = f p := by
  have hb : BddBelow (f '' Icc 0 U) := ⟨f p,by rintro _ ⟨x,hx,rfl⟩; exact hmin x hx⟩
  apply le_antisymm
  · exact csInf_le hb ⟨p,hp,rfl⟩
  · apply le_csInf (show (f '' Icc 0 U).Nonempty from ⟨f p,p,hp,rfl⟩)
    rintro _ ⟨x,hx,rfl⟩; exact hmin x hx

theorem positive_curvature_bad_inf (d : ℕ) (hd : 0 < d) (eps a b c : ℝ)
    (he : eps < (d : ℝ)) (hc : 0 < c) :
    let U := min 1 (2-2*eps/(d : ℝ))
    let p := clipped c b U
    sInf ((fun nu => a-2*b*nu+c*nu^2) '' badDomain d eps) = a-2*b*p+c*p^2 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : 0 < 2-2*eps/(d : ℝ) := by
    rw [sub_pos,div_lt_iff₀ hdr]; linarith
  dsimp
  by_cases hU : 2-2*eps/(d : ℝ) ≤ 1
  · rw [min_eq_right hU,bad_domain_half_open d hd eps hU]
    obtain ⟨hp,hm⟩ := quadratic_minimum c b a _ hc ht.le
    exact half_open_inf_eq_minimum _ (by fun_prop) _ _ ht hp hm
  · have hU' := lt_of_not_ge hU
    rw [min_eq_left hU'.le,bad_domain_closed d hd eps hU']
    obtain ⟨hp,hm⟩ := quadratic_minimum c b a 1 hc (by norm_num)
    exact closed_inf_eq_min _ 1 _ hp hm

/-- Degenerate quadratics are affine; choose the correct endpoint by slope. -/
theorem zero_curvature_minimum (a b U : ℝ) (hU : 0 ≤ U) :
    let p := if 0 ≤ b then U else 0
    p ∈ Icc 0 U ∧ ∀ x ∈ Icc 0 U, a-2*b*p ≤ a-2*b*x := by
  dsimp
  split_ifs with hb
  · refine ⟨⟨hU,le_rfl⟩,?_⟩
    intro x hx
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hx.2)]
  · refine ⟨⟨le_rfl,hU⟩,?_⟩
    intro x hx
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hb) hx.1]

/-- General infimum monotonicity needed for Gamma_epsilon >= Gamma_0.
Nonempty approximate bad alternatives are explicit, avoiding real sInf empty. -/
theorem bad_information_mono (S T : Set ℝ) (hsub : S ⊆ T)
    (hS : S.Nonempty) (hT : BddBelow T) : sInf T ≤ sInf S := by
  apply le_csInf hS
  intro x hx
  exact csInf_le hT (hsub hx)

#print axioms bad_domain_closed
#print axioms bad_domain_half_open
#print axioms bad_domain_empty
#print axioms positive_curvature_bad_inf
#print axioms zero_curvature_minimum
#print axioms bad_information_mono
end
end CIGAMF.P13.D6ApproximateProfile
