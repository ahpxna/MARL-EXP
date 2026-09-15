import «LeanFunctionalFlatOutsiderRateV1»

namespace CIGAMF.P13.FunctionalFlatOutsiderMinimax
open scoped BigOperators
open CIGAMF.P13.FunctionalFlatOutsiderRate
noncomputable section

def Valid {K : ℕ} (p t : ℝ) (w : Fin K → ℝ) : Prop :=
  0 ≤ p ∧ 0 ≤ t ∧ (∀ i,0 ≤ w i) ∧ p+t+∑ i,w i=1

def costs {K : ℕ} (p t : ℝ) (w : Fin K → ℝ) : Set ℝ :=
  {v | ∃ x y z, Alternative x y z ∧ v=energy p t w x y z}

def information {K : ℕ} (p t : ℝ) (w : Fin K → ℝ) : ℝ := sInf (costs p t w)

def attainable (K : ℕ) : Set ℝ :=
  {v | ∃ (p t : ℝ) (w : Fin K → ℝ),Valid p t w ∧ v=information p t w}

lemma costs_bddBelow {K : ℕ} (p t : ℝ) (w : Fin K → ℝ) (hv : Valid p t w) :
    BddBelow (costs p t w) := by
  refine ⟨0,?_⟩
  rintro _ ⟨x,y,z,_,rfl⟩
  unfold energy
  apply div_nonneg _ (by norm_num)
  exact add_nonneg (add_nonneg (mul_nonneg hv.1 (sq_nonneg _))
    (mul_nonneg hv.2.1 (sq_nonneg _)))
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hv.2.2.1 i) (sq_nonneg _)))

theorem information_upper {K : ℕ} (hK : 2 ≤ K) (s : ℝ) (hs : 0 < s) (hsq : s^2=2*K)
    (p t : ℝ) (w : Fin K → ℝ) (hv : Valid p t w) : information p t w ≤ rate s := by
  obtain ⟨x,y,z,ha,he⟩ := arbitrary_allocation_upper hK s hs hsq p t w hv.2.2.2
  exact (csInf_le (costs_bddBelow p t w hv) ⟨x,y,z,ha,rfl⟩).trans he

theorem uniform_information {K : ℕ} (hK : 2 ≤ K) (s : ℝ) (hs : 0 < s) (hsq : s^2=2*K) :
    Valid (1/(2+s)) (1/(2+s)) (fun _ : Fin K => 2/(s*(2+s))) ∧
      information (1/(2+s)) (1/(2+s)) (fun _ : Fin K => 2/(s*(2+s)))=rate s := by
  obtain ⟨hp,hw,hm,hE⟩ := uniform_allocation s hs hsq
  have hv : Valid (1/(2+s)) (1/(2+s)) (fun _ : Fin K => 2/(s*(2+s))) :=
    ⟨hp.le,hp.le,fun i => (hw i).le,hm⟩
  refine ⟨hv,le_antisymm (information_upper hK s hs hsq _ _ _ hv) ?_⟩
  obtain ⟨x,y,z,ha,_⟩ := arbitrary_allocation_upper hK s hs hsq _ _ _ hm
  apply le_csInf (show (costs (1/(2+s)) (1/(2+s)) (fun _ : Fin K => 2/(s*(2+s)))).Nonempty
    from ⟨_,x,y,z,ha,rfl⟩)
  rintro _ ⟨x,y,z,ha,rfl⟩
  rw [hE]
  exact uniform_lower s hs x y z ha

theorem flat_outsider_exact_rate (K : ℕ) (hK : 2 ≤ K) :
    IsGreatest (attainable K) (1/(2*(2+Real.sqrt (2*(K : ℝ)))^2)) := by
  let s := Real.sqrt (2*(K : ℝ))
  have hk : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hsq : s^2=2*K := Real.sq_sqrt (by positivity)
  obtain ⟨hv,he⟩ := uniform_information hK s hs hsq
  refine ⟨⟨_,_,_,hv,he.symm⟩,?_⟩
  rintro v ⟨p,t,w,hv,rfl⟩
  exact information_upper hK s hs hsq p t w hv

theorem gamma_closed_form (K : ℕ) (hK : 2 ≤ K) :
    sSup (attainable K)=1/(2*(2+Real.sqrt (2*(K : ℝ)))^2) := by
  have h := flat_outsider_exact_rate K hK
  exact le_antisymm (csSup_le ⟨_,h.1⟩ h.2) (le_csSup ⟨_,h.2⟩ h.1)

#print axioms costs_bddBelow
#print axioms information_upper
#print axioms uniform_information
#print axioms flat_outsider_exact_rate
#print axioms gamma_closed_form
end
end CIGAMF.P13.FunctionalFlatOutsiderMinimax
