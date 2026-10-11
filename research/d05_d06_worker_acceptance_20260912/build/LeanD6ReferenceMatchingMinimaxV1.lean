import «LeanD6ReferenceEndpointWorldsV1»

/-! D05: matching finite-world certificates in the active reference phase.
The lower certificate is against every randomized actual decision, using an
explicit mixture of the full world and the uniform singleton-world prior.
The upper strategy uses T and its complement, both with the right budget.
No symmetry/WLOG premise about the learner is used. The sufficient reference
regime is inherited explicitly from Region; the inactive case is separate.
-/
namespace CIGAMF.P13.D6ReferenceMatchingMinimax
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceRetainedOscillation CIGAMF.P13.D6ReferenceFullCountLoss
open CIGAMF.P13.D6ReferenceLegalCountMinimum CIGAMF.P13.D6ReferencePhaseRegretBridge
open CIGAMF.P13.D6ReferenceOrbitAverage CIGAMF.P13.D6ReferenceEndpointWorlds
open CIGAMF.P13.D6ReferenceEndpointWorlds.Region
open CIGAMF.P13.D6ReferencePhaseValue CIGAMF.P13.D6SameResponseMarginCertificate
noncomputable section

lemma orbit_zero (k p c e r b h : ℝ) : orbitRisk k p c e r b h 0=risk0 e r h := by
  simp [orbitRisk,base,risk0]
  ring

/-- The `d = 1` correction value, proved separately so no `split_ifs` is needed
downstream. This is the step that previously produced impossible branches. -/
lemma orbit_one (k p c e r b h : ℝ) : orbitRisk k p c e r b h 1=riskOne k p c e r b h := by
  unfold orbitRisk riskOne
  norm_num

lemma orbit_ge_two (k p c e r b h : ℝ) (d : ℕ) (hd : 2 ≤ d) :
    orbitRisk k p c e r b h d=base k p c e r h d := by
  simp [orbitRisk,show d ≠ 0 by omega,show d ≠ 1 by omega]

lemma orbit_dominance (k : ℕ) (hk : 3 ≤ k) (p c e r b h : ℝ)
    (hb : 0 ≤ b) (hbe : b ≤ e) (hh : 1 ≤ h) (hhk : h ≤ k) (d : ℕ) (hd : d ≤ k) :
    (1-(d:ℝ)/k)*risk0 e r h+((d:ℝ)/k)*base k p c e r h k ≤ orbitRisk k p c e r b h d := by
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  by_cases h0 : d=0
  · subst d; simp [orbit_zero]
  by_cases h1 : d=1
  · subst d
    rw [orbit_one,Nat.cast_one]
    exact dominance_one k p c e r b h hkR hb hbe hh hhk
  · rw [orbit_ge_two _ _ _ _ _ _ _ d (by omega)]
    exact dominance_gen k p c e r h d hkR (hb.trans hbe) (by exact_mod_cast hd)

lemma endpoint_values (k p c e r : ℝ) (hk : k ≠ 0) (hpr : p+r=2*c) (hact : e ≤ k*r) :
    risk0 e r 1=uOne r e ∧ base k p c e r 1 k=vTerm k p e r ∧
    risk0 e r k=uTop k r e ∧ base k p c e r k k=0 := by
  have hmax : max e r=r+max 0 (e-r) := by
    rcases le_total e r with h | h
    · rw [max_eq_right h,max_eq_left (by linarith)]; ring
    · rw [max_eq_left h,max_eq_right (by linarith)]; ring
  have hdiff : max e r-e=max 0 (r-e) := by
    rcases le_total e r with h | h
    · rw [max_eq_right h,max_eq_right (by linarith)]
    · rw [max_eq_left h,max_eq_left (by linarith)]; ring
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [risk0,uOne,mul_one] using congrArg (fun x : ℝ => x/2) hdiff
  · unfold base vTerm
    have hcancel : 1*k/k=(1:ℝ) := by field_simp
    rw [hcancel]
    simp only [mul_one]
    rw [hmax]
    linear_combination hpr/2
  · unfold risk0 uTop
    rw [mul_comm r k,max_eq_right hact]
  · unfold base
    have hcancel : k*k/k=k := by field_simp
    rw [hcancel,mul_comm r k,max_eq_right hact]
    linear_combination k*hpr/2

lemma dual_orbit_lower (k : ℕ) (hk : 3 ≤ k) (p c e r b : ℝ)
    (hb : 0 ≤ b) (hbe : b ≤ e) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hp : 1/2 ≤ p)
    (hact : e ≤ (k:ℝ)*r) (hpr : p+r=2*c) (hc : 0 < c*((k:ℝ)-1))
    (d : ℕ) (hd : d ≤ k) :
    phaseValue k p c e r ≤
      (1-(vTerm k p e r-uOne r e)/(c*((k:ℝ)-1)))*orbitRisk k p c e r b 1 d+
      ((vTerm k p e r-uOne r e)/(c*((k:ℝ)-1)))*orbitRisk k p c e r b k d := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hw := weights_valid k p c e r hkR (hb.trans hbe) hr hr1 hp hact hpr hc
  have hv := endpoint_values k p c e r (by positivity) hpr hact
  have heq := phase_equalizers k p c e r hpr (ne_of_gt hc)
  have h1 := orbit_dominance k hk p c e r b 1 hb hbe (le_refl _) (by linarith) d hd
  have hK := orbit_dominance k hk p c e r b k hb hbe (by linarith) (le_refl _) d hd
  rw [hv.1,hv.2.1] at h1
  rw [hv.2.2.1,hv.2.2.2] at hK
  have hx := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1-(vTerm k p e r-uOne r e)/(c*((k:ℝ)-1)) by linarith [hw.2.2.2])
  have hy := mul_le_mul_of_nonneg_left hK hw.2.2.1
  have halg :
      (1-(vTerm k p e r-uOne r e)/(c*((k:ℝ)-1)))*
        ((1-(d:ℝ)/k)*uOne r e+((d:ℝ)/k)*vTerm k p e r)+
      ((vTerm k p e r-uOne r e)/(c*((k:ℝ)-1)))*
        ((1-(d:ℝ)/k)*uTop k r e+((d:ℝ)/k)*0) = phaseValue k p c e r := by
    calc
      _ = (1-(d:ℝ)/k)*((1-(vTerm k p e r-uOne r e)/(c*((k:ℝ)-1)))*uOne r e+
              ((vTerm k p e r-uOne r e)/(c*((k:ℝ)-1)))*uTop k r e)+
          ((d:ℝ)/k)*((1-(vTerm k p e r-uOne r e)/(c*((k:ℝ)-1)))*vTerm k p e r+
              ((vTerm k p e r-uOne r e)/(c*((k:ℝ)-1)))*0) := by ring
      _ = _ := by rw [heq.2.2.1,heq.2.2.2]; ring
  linarith

variable {q : ℕ} {j : I (2*q+1)} {T : Finset (I (2*q+1))}

lemma region_bounds (M : Region q j T) :
    0 ≤ M.b ∧ M.b ≤ M.e ∧ M.r ≤ 1 ∧ 0 < M.c := by
  have ht := world_parameters q j M.hq M.hT
  have ha := gateMass_bounds M.t M.ht0 M.ht1 T j (by have := ht.2.2.2; omega)
  have hb := slopeBval_nonneg M.t M.ht0 M.ht1 T j ht.2.2.2
  have hba := slope_order M.t M.ht1 T j ht.2.2.2
  have htlt : M.t < 1 := by
    by_contra hn
    have he : M.t=1 := by linarith [M.ht1]
    have hzero : slopeBval M.t T j=0 := by
      unfold slopeBval
      rw [he]
      have hpow : T.card+(others T j).card-1 ≠ 0 := by have := ht.2.2.2; omega
      simp [hpow]
    have hs := M.strong
    rw [hzero] at hs
    norm_num at hs
  have hgap := slope_gap M.t T j ht.2.2.2
  have hpos : 0 < (1-M.t)^(T.card+(others T j).card-1) := pow_pos (by linarith) _
  dsimp [a,b,c,e,r]
  exact ⟨hb,le_min hba (by linarith),by linarith [M.hr],by linarith⟩

lemma full_world_shape (M : Region q j T) (S : Finset (I (2*q+1))) :
    M.regret T S=orbitRisk ((q:ℝ)+1) M.p M.c M.e M.r M.b ((q:ℝ)+1) (T \ S).card := by
  classical
  have ht := world_parameters q j M.hq M.hT
  have hDA : (T \ S) ∩ T=T \ S := Finset.inter_eq_left.mpr Finset.sdiff_subset
  have hDB : (T \ S) ∩ others T j=∅ := by
    ext i
    constructor
    · intro hi
      have h1 := Finset.mem_inter.mp hi
      exact absurd (Finset.mem_sdiff.mp h1.1).1 (others_not_mem_A T j i h1.2)
    · intro hi
      exact absurd hi (by simp)
  have hk : ((q:ℝ)+1) ≠ 0 := by positivity
  rw [regret_counts M T S M.hT,hDA,hDB,Finset.card_empty,Finset.inter_self,ht.2.1]
  by_cases h0 : (T \ S).card=0
  · have hcorr : correction M.a M.b (T \ S).card 0 = min M.a (2*M.b) := by
      unfold correction
      rw [if_pos (⟨h0,rfl⟩ : (T \ S).card=0 ∧ (0:ℕ)=0)]
    unfold variableCost orbitRisk base
    rw [hcorr,if_pos h0,h0]
    dsimp [Region.p,Region.c,Region.e,Region.r]
    push_cast
    ring
  · have hcorr : correction M.a M.b (T \ S).card 0 = 0 := by
      unfold correction
      rw [if_neg (fun hc => h0 hc.1),if_neg (fun hc => h0 hc.1)]
    have hcancel : ((q:ℝ)+1)*((T \ S).card:ℝ)/((q:ℝ)+1)=((T \ S).card:ℝ) :=
      mul_div_cancel_left₀ _ hk
    unfold variableCost orbitRisk base
    rw [hcorr,if_neg h0,hcancel]
    by_cases h1 : (T \ S).card=1
    · rw [if_pos h1]
      dsimp [Region.p,Region.c,Region.e,Region.r]
      push_cast
      ring
    · rw [if_neg h1]
      dsimp [Region.p,Region.c,Region.e,Region.r]
      push_cast
      ring

/-- Pointwise lower certificate against an arbitrary actual retained set. -/
theorem actual_dual_lower (M : Region q j T) (hact : M.e ≤ ((q:ℝ)+1)*M.r)
    (S : Finset (I (2*q+1))) :
    phaseValue ((q:ℝ)+1) M.p M.c M.e M.r ≤
      (1-(vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*
        ((∑ i ∈ T,M.regret (singletonWorld T j i) S)/((q:ℝ)+1))+
      ((vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*M.regret T S := by
  have hb := region_bounds M
  have he : 0 ≤ M.e := hb.1.trans hb.2.1
  have hr : 0 ≤ M.r := by have := M.hq; nlinarith [show (0:ℝ) ≤ q by positivity]
  have hD : 0 < M.c*(((q+1:ℕ):ℝ)-1) := by
    rw [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    exact mul_pos hb.2.2.2 (by exact_mod_cast (show 0<q by have := M.hq; omega))
  have hd : (T \ S).card ≤ q+1 := by
    have ht := (world_parameters q j M.hq M.hT).2.1
    exact ht ▸ Finset.card_le_card Finset.sdiff_subset
  have hh := dual_orbit_lower (q+1) (by have := M.hq; omega) M.p M.c M.e M.r M.b hb.1 hb.2.1
    hr hb.2.2.1 M.hp (by simpa using hact) (by dsimp [p,c,r]; ring) hD (T \ S).card hd
  rw [actual_singleton_average M S,full_world_shape M S]
  simpa using hh

/-- Finite randomization is included explicitly; the prior is fixed before S. -/
theorem randomized_dual_lower (M : Region q j T) (hact : M.e ≤ ((q:ℝ)+1)*M.r)
    (decisions : Finset (Finset (I (2*q+1)))) (w : Finset (I (2*q+1)) → ℝ)
    (hw : ∀ S ∈ decisions,0 ≤ w S) (hn : ∑ S ∈ decisions,w S=1) :
    phaseValue ((q:ℝ)+1) M.p M.c M.e M.r ≤
      (1-(vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*
        ((∑ i ∈ T,∑ S ∈ decisions,w S*M.regret (singletonWorld T j i) S)/((q:ℝ)+1))+
      ((vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*
        (∑ S ∈ decisions,w S*M.regret T S) := by
  classical
  have h := Finset.sum_le_sum (fun S hS =>
    mul_le_mul_of_nonneg_left (actual_dual_lower M hact S) (hw S hS))
  rw [← Finset.sum_mul,hn,one_mul] at h
  refine h.trans (le_of_eq ?_)
  have e1 : (∑ S ∈ decisions,
        w S*((1-(vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*
          ((∑ i ∈ T,M.regret (singletonWorld T j i) S)/((q:ℝ)+1))))
      = (1-(vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*
        ((∑ i ∈ T,∑ S ∈ decisions,w S*M.regret (singletonWorld T j i) S)/((q:ℝ)+1)) := by
    have hstep : ∀ S : Finset (I (2*q+1)),
        w S*((1-(vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*
          ((∑ i ∈ T,M.regret (singletonWorld T j i) S)/((q:ℝ)+1)))
        = ((1-(vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))/((q:ℝ)+1))*
          (∑ i ∈ T,w S*M.regret (singletonWorld T j i) S) := by
      intro S
      rw [← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl (fun S _ => hstep S),← Finset.mul_sum,Finset.sum_comm]
    ring
  have e2 : (∑ S ∈ decisions,
        w S*(((vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*M.regret T S))
      = ((vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*
        (∑ S ∈ decisions,w S*M.regret T S) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun S _ => by ring)
  rw [Finset.sum_congr rfl (fun S (_ : S ∈ decisions) =>
      mul_add (w S)
        ((1-(vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*
          ((∑ i ∈ T,M.regret (singletonWorld T j i) S)/((q:ℝ)+1)))
        (((vTerm ((q:ℝ)+1) M.p M.e M.r-uOne M.r M.e)/(M.c*q))*M.regret T S)),
    Finset.sum_add_distrib,e1,e2]

/-- The two A-free decisions have the precise endpoint-interpolating risk. -/
theorem two_action_risk (M : Region q j T) (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j)
    (w : ℝ) : w*M.regret A T+(1-w)*M.regret A Tᶜ =
      mixRisk ((q:ℝ)+1) M.p M.c M.e M.r w (T ∩ A).card := by
  have ht := world_parameters q j M.hq M.hT
  have hDA : T \ Tᶜ=T := by ext i; simp
  have hsum := card_split A T j ht.1
  rw [ht.2.1] at hsum
  have hno0 : ¬ ((T ∩ A).card=0 ∧ (T ∩ others A j).card=0) := by
    have hh := overlap_positive M A hA; omega
  have hno1 : ¬ ((T ∩ A).card=0 ∧ (T ∩ others A j).card=1) := by
    have hh := overlap_positive M A hA; omega
  rw [regret_counts M A T hA,regret_counts M A Tᶜ hA,hDA]
  simp only [Finset.sdiff_self,Finset.empty_inter,Finset.card_empty,variable_zero]
  unfold variableCost correction
  rw [if_neg hno0,if_neg hno1]
  dsimp [mixRisk,risk0,base,p,c,e,r]
  have hk : (q:ℝ)+1 ≠ 0 := by positivity
  have hd : ((T ∩ others A j).card:ℝ)=((q:ℝ)+1)-((T ∩ A).card:ℝ) := by
    push_cast at hsum; linarith
  rw [hd]
  field_simp
  ring

/-- Actual primal matches the actual dual; both decisions obey the original budget. -/
theorem actual_primal_upper (M : Region q j T) (hact : M.e ≤ ((q:ℝ)+1)*M.r) :
    let w := vTerm ((q:ℝ)+1) M.p M.e M.r/(M.c*q)
    0 ≤ w ∧ w ≤ 1 ∧ Tᶜ.card=T.card ∧
      ∀ A ∈ worlds q j,w*M.regret A T+(1-w)*M.regret A Tᶜ ≤ phaseValue ((q:ℝ)+1) M.p M.c M.e M.r := by
  dsimp only
  have hb := region_bounds M
  have he : 0 ≤ M.e := hb.1.trans hb.2.1
  have hr : 0 ≤ M.r := by nlinarith [show (0:ℝ) ≤ q by positivity]
  have hkR : (3:ℝ) ≤ (q:ℝ)+1 := by exact_mod_cast (show 3≤q+1 by have := M.hq; omega)
  have hc : 0 < M.c*(((q:ℝ)+1)-1) := by
    rw [add_sub_cancel_right]
    exact mul_pos hb.2.2.2 (by exact_mod_cast (show 0<q by have := M.hq; omega))
  have hpr : M.p+M.r=2*M.c := by dsimp [p,r,c]; ring
  have hw := weights_valid ((q:ℝ)+1) M.p M.c M.e M.r hkR he hr hb.2.2.1 M.hp hact hpr hc
  have hv := endpoint_values ((q:ℝ)+1) M.p M.c M.e M.r (by positivity) hpr hact
  have heq := phase_equalizers ((q:ℝ)+1) M.p M.c M.e M.r hpr (ne_of_gt hc)
  simp only [add_sub_cancel_right] at hw heq
  refine ⟨hw.1,hw.2.1,(world_parameters q j M.hq M.hT).2.2.1,?_⟩
  intro A hA
  rw [two_action_risk M A hA]
  have hh : (1:ℝ) ≤ (T ∩ A).card := by exact_mod_cast overlap_positive M A hA
  have hhk : ((T ∩ A).card:ℝ) ≤ (q:ℝ)+1 := by
    have h := Finset.card_le_card (Finset.inter_subset_left : T ∩ A ⊆ T)
    rw [(world_parameters q j M.hq M.hT).2.1] at h
    exact_mod_cast h
  apply (endpoint_max ((q:ℝ)+1) M.p M.c M.e M.r _ _ (by linarith) hh hhk).trans
  unfold mixRisk
  rw [hv.1,hv.2.1,hv.2.2.1,hv.2.2.2,heq.1,heq.2.1,max_self]

#print axioms orbit_zero
#print axioms orbit_one
#print axioms orbit_ge_two
#print axioms orbit_dominance
#print axioms endpoint_values
#print axioms dual_orbit_lower
#print axioms region_bounds
#print axioms full_world_shape
#print axioms actual_dual_lower
#print axioms randomized_dual_lower
#print axioms two_action_risk
#print axioms actual_primal_upper
end
end CIGAMF.P13.D6ReferenceMatchingMinimax
