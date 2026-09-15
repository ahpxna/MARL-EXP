import «LeanQueryResolutionMinimaxV1»

namespace CIGAMF.P13.QueryCriticalResolution
open Finset
open CIGAMF.P13.QueryResolutionMinimax
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Θ D : Type*} [Fintype Θ] [Nonempty Θ] [Fintype D] [Nonempty D]

def responseDistance (R : Θ → D → ℝ) (x z : Θ) : ℝ :=
  (univ.image (fun i => |R x i-R z i|)).max' (univ_nonempty.image _)

lemma responseDistance_le_iff (R : Θ → D → ℝ) (x z : Θ) (v : ℝ) :
    responseDistance R x z ≤ v ↔ ∀ i,|R x i-R z i| ≤ v := by
  unfold responseDistance
  constructor
  · intro h i
    exact (le_max' _ _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)).trans h
  · intro h
    obtain ⟨i,_,hi⟩ := mem_image.mp (max'_mem (univ.image (fun i : D => |R x i-R z i|)) (univ_nonempty.image _))
    rw [← hi]
    exact h i

lemma responseDistance_nonneg (R : Θ → D → ℝ) (x z : Θ) : 0 ≤ responseDistance R x z := by
  let i : D := Classical.choice inferInstance
  exact (abs_nonneg _).trans ((responseDistance_le_iff R x z _).mp le_rfl i)

lemma feasible_iff_pair_bound (R : Θ → D → ℝ) (g : Θ → ℝ) (eta eps : ℝ) (he : 0 ≤ eta) :
    eps ∈ feasibleErrors R g eta ↔ ∀ x z,Close R eta x z → |g x-g z| ≤ 2*eps := by
  constructor
  · intro h x z hc
    have hr := decoder_lower R g eta eps he h
    have hp := pair_bound R g eta he x z hc
    linarith
  · intro h
    have hr : radius R g eta he ≤ eps := by
      obtain ⟨p,hp,hv⟩ := mem_image.mp (max'_mem _ (pairs_nonempty R g eta he))
      have hd := h p.1 p.2 (mem_filter.mp hp).2
      unfold radius
      rw [← hv]
      linarith
    exact ⟨midpoint R g eta,fun x y hx => (midpoint_error R g eta he x y hx).trans hr⟩

def badPairs (g : Θ → ℝ) (eps : ℝ) : Finset (Θ × Θ) :=
  univ.filter (fun p => 2*eps< |g p.1-g p.2|)

def badDistances (R : Θ → D → ℝ) (g : Θ → ℝ) (eps : ℝ) : Finset ℝ :=
  (badPairs g eps).image (fun p => responseDistance R p.1 p.2)

def critical (R : Θ → D → ℝ) (g : Θ → ℝ) (eps : ℝ) (hn : (badPairs g eps).Nonempty) : ℝ :=
  (badDistances R g eps).min' (hn.image _)/2

theorem critical_nonneg (R : Θ → D → ℝ) (g : Θ → ℝ) (eps : ℝ)
    (hn : (badPairs g eps).Nonempty) : 0 ≤ critical R g eps hn := by
  obtain ⟨p,_,hp⟩ := mem_image.mp (min'_mem (badDistances R g eps) (hn.image _))
  unfold critical
  rw [← hp]
  exact div_nonneg (responseDistance_nonneg R p.1 p.2) (by norm_num)

theorem below_critical_sufficient (R : Θ → D → ℝ) (g : Θ → ℝ) (eta eps : ℝ)
    (he : 0 ≤ eta) (hn : (badPairs g eps).Nonempty) (hlt : eta<critical R g eps hn) :
    eps ∈ feasibleErrors R g eta := by
  apply (feasible_iff_pair_bound R g eta eps he).mpr
  intro x z hc
  by_contra h
  have hb : (x,z) ∈ badPairs g eps := by simp [badPairs]; linarith
  have hmem : responseDistance R x z ∈ badDistances R g eps := mem_image.mpr ⟨(x,z),hb,rfl⟩
  have hmin := min'_le _ _ hmem
  have hdist := (responseDistance_le_iff R x z (2*eta)).mpr hc
  unfold critical at hlt
  linarith

theorem at_critical_fails (R : Θ → D → ℝ) (g : Θ → ℝ) (eps : ℝ)
    (hn : (badPairs g eps).Nonempty) :
    eps ∉ feasibleErrors R g (critical R g eps hn) := by
  intro h
  obtain ⟨p,hp,hv⟩ := mem_image.mp (min'_mem (badDistances R g eps) (hn.image _))
  have hb : 2*eps< |g p.1-g p.2| := (mem_filter.mp hp).2
  have hc : Close R (critical R g eps hn) p.1 p.2 := by
    apply (responseDistance_le_iff R p.1 p.2 _).mp
    unfold critical
    rw [← hv]
    linarith
  have hh := (feasible_iff_pair_bound R g _ eps (critical_nonneg R g eps hn)).mp h p.1 p.2 hc
  linarith

theorem no_bad_pairs_sufficient (R : Θ → D → ℝ) (g : Θ → ℝ) (eta eps : ℝ)
    (he : 0 ≤ eta) (hn : badPairs g eps=∅) : eps ∈ feasibleErrors R g eta := by
  apply (feasible_iff_pair_bound R g eta eps he).mpr
  intro x z _
  by_contra h
  have hb : (x,z) ∈ badPairs g eps := by simp [badPairs]; linarith
  rw [hn] at hb
  simpa using hb

#print axioms feasible_iff_pair_bound
#print axioms critical_nonneg
#print axioms below_critical_sufficient
#print axioms at_critical_fails
#print axioms no_bad_pairs_sufficient
end
end CIGAMF.P13.QueryCriticalResolution
