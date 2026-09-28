import «LeanPaperCFlowCertV1»

/-!
# Paper C: flows as weighted mixtures of type sequences

A primal certificate for the count-flow program, given as finitely many type sequences with
weights. Each type sequence `s : Fin m → Fin d` with the multiplicities of `ty` is served in
index order by the horizon path `stC s` (`LeanPaperCHorizonV1`).

* `mixFlow`: the layered flow of the mixture.
* `mixFlow_feasible`: it is count-feasible for `ty`.
* `mixFlow_obj`: its objective at budget `k` is `Σ_j w_j c_k(stC s_j k)`.
* `mixFlow_mean`: its type means are `Σ_j w_j (stC s_j k)_τ / n_τ`.

With `trueValue_eq_flow` (`LeanPaperCFreeBandV1`), a mixture that meets the band is an upper
bound on the value.
-/

namespace CIGAMF.P13.PaperCPathMix

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCFlowBandJoin CIGAMF.P13.PaperCVacuity
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFreeBand CIGAMF.P13.PaperCFlowCert

variable {d m P : ℕ}

/-- **The flow of a weighted mixture of type sequences.** -/
noncomputable def mixFlow (s : Fin P → Fin m → Fin d) (w : Fin P → ℝ) (hw : ∀ j, 0 ≤ w j) :
    LayeredFlow (CState d m) where
  x := fun k v => ∑ j, w j * (if v = stC (s j) k then 1 else 0)
  f := fun k v u => ∑ j, w j * (if v = stC (s j) k ∧ u = stC (s j) (k + 1) then 1 else 0)
  xnn := fun k v => Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (by split_ifs <;> norm_num)
  fnn := fun k v u => Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (by split_ifs <;> norm_num)
  outflow := by
    intro k v
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    by_cases hv : v = stC (s j) k
    · simp [hv]
    · simp [hv]
  inflow := by
    intro k u
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    by_cases hu : u = stC (s j) (k + 1)
    · simp [hu]
    · simp [hu]

/-- **The mixture is count-feasible** when every sequence has the multiplicities of `ty`. -/
theorem mixFlow_feasible (ty : Fin m → Fin d) (s : Fin P → Fin m → Fin d) (w : Fin P → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hmult : ∀ j τ, mult (s j) τ = mult ty τ) :
    CountFeasibleH ty (mixFlow s w hw) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ∑ v, ∑ j, w j * (if v = stC (s j) 0 then 1 else 0) = 1
    rw [Finset.sum_comm]
    have h1 : ∀ j, ∑ v : CState d m, w j * (if v = stC (s j) 0 then (1 : ℝ) else 0) = w j := by
      intro j; rw [← Finset.mul_sum]; simp
    rw [Finset.sum_congr rfl fun j _ => h1 j, hw1]
  · intro k hk v u hstep
    show ∑ j, w j * (if v = stC (s j) k ∧ u = stC (s j) (k + 1) then 1 else 0) = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    rintro ⟨rfl, rfl⟩
    exact hstep (stC_step (s j) k hk)
  · intro k hk v u hne
    show ∑ j, w j * (if v = stC (s j) k ∧ u = stC (s j) (k + 1) then 1 else 0) = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    rintro ⟨rfl, rfl⟩
    exact hne (stC_idle (s j) k hk).symm
  · intro k v hx τ
    have hx' : ∑ j, w j * (if v = stC (s j) k then 1 else 0) ≠ 0 := hx
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
    have hv : v = stC (s j) k := by
      by_contra h; exact hj (by rw [if_neg h, mul_zero])
    rw [hv, ← hmult j τ]
    exact cnt_le_mult (s j) (min k m) τ

theorem mixFlow_x (s : Fin P → Fin m → Fin d) (w : Fin P → ℝ) (hw : ∀ j, 0 ≤ w j) (k : ℕ)
    (g : CState d m → ℝ) :
    ∑ v, (mixFlow s w hw).x k v * g v = ∑ j, w j * g (stC (s j) k) := by
  show ∑ v, (∑ j, w j * (if v = stC (s j) k then 1 else 0)) * g v = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_assoc]

/-- **The objective of a mixture.** -/
theorem mixFlow_obj (s : Fin P → Fin m → Fin d) (w : Fin P → ℝ) (hw : ∀ j, 0 ≤ w j)
    (c : Fin (m + 1) → CState d m → ℝ) (k : Fin (m + 1)) :
    flowObj c (mixFlow s w hw) k = ∑ j, w j * c k (stC (s j) k) :=
  mixFlow_x s w hw k (c k)

/-- **The type means of a mixture.** -/
theorem mixFlow_mean (ty : Fin m → Fin d) (s : Fin P → Fin m → Fin d) (w : Fin P → ℝ)
    (hw : ∀ j, 0 ≤ w j) (k : Fin (m + 1)) (τ : Fin d) :
    typeMean ty (mixFlow s w hw) k τ
      = (∑ j, w j * ((stC (s j) k τ : ℕ) : ℝ)) / (mult ty τ : ℝ) := by
  unfold typeMean
  rw [mixFlow_x s w hw k (fun v => ((v τ : ℕ) : ℝ))]

/-! ## Mixing two flows -/

/-- **The convex combination of two layered flows.** -/
noncomputable def mixTwo (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (F G : LayeredFlow (CState d m)) :
    LayeredFlow (CState d m) where
  x := fun k v => (1 - θ) * F.x k v + θ * G.x k v
  f := fun k v u => (1 - θ) * F.f k v u + θ * G.f k v u
  xnn := fun k v => by
    have := F.xnn k v; have := G.xnn k v
    have : 0 ≤ 1 - θ := by linarith
    positivity
  fnn := fun k v u => by
    have := F.fnn k v u; have := G.fnn k v u
    have : 0 ≤ 1 - θ := by linarith
    positivity
  outflow := fun k v => by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, F.outflow, G.outflow]
  inflow := fun k u => by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, F.inflow, G.inflow]

theorem mixTwo_feasible (ty : Fin m → Fin d) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (F G : LayeredFlow (CState d m)) (hF : CountFeasibleH ty F) (hG : CountFeasibleH ty G) :
    CountFeasibleH ty (mixTwo θ hθ0 hθ1 F G) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ∑ v, ((1 - θ) * F.x 0 v + θ * G.x 0 v) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hF.1, hG.1]; ring
  · intro k hk v u hs
    show (1 - θ) * F.f k v u + θ * G.f k v u = 0
    rw [hF.2.1 k hk v u hs, hG.2.1 k hk v u hs]; ring
  · intro k hk v u hne
    show (1 - θ) * F.f k v u + θ * G.f k v u = 0
    rw [hF.2.2.1 k hk v u hne, hG.2.2.1 k hk v u hne]; ring
  · intro k v hx τ
    have hx' : (1 - θ) * F.x k v + θ * G.x k v ≠ 0 := hx
    by_cases hFx : F.x k v = 0
    · have hGx : G.x k v ≠ 0 := by
        intro h; apply hx'; rw [hFx, h]; ring
      exact hG.2.2.2 k v hGx τ
    · exact hF.2.2.2 k v hFx τ

theorem mixTwo_obj (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (F G : LayeredFlow (CState d m))
    (c : Fin (m + 1) → CState d m → ℝ) (k : Fin (m + 1)) :
    flowObj c (mixTwo θ hθ0 hθ1 F G) k = (1 - θ) * flowObj c F k + θ * flowObj c G k := by
  show ∑ v, ((1 - θ) * F.x k v + θ * G.x k v) * c k v = _
  unfold flowObj
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

theorem mixTwo_band (ty : Fin m → Fin d) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (F G : LayeredFlow (CState d m)) (hF : CountFeasibleH ty F) (hG : CountFeasibleH ty G)
    (η₁ η₂ : ℝ) (h1 : FlowBand ty F η₁) (h2 : FlowBand ty G η₂) :
    FlowBand ty (mixTwo θ hθ0 hθ1 F G) ((1 - θ) * η₁ + θ * η₂) := by
  intro k τ hτ
  have hmean : typeMean ty (mixTwo θ hθ0 hθ1 F G) k τ
      = (1 - θ) * typeMean ty F k τ + θ * typeMean ty G k τ := by
    unfold typeMean
    show (∑ v, ((1 - θ) * F.x k.val v + θ * G.x k.val v) * ((v τ : ℕ) : ℝ)) / (mult ty τ : ℝ) = _
    rw [show ∑ v, ((1 - θ) * F.x k.val v + θ * G.x k.val v) * ((v τ : ℕ) : ℝ)
        = (1 - θ) * ∑ v, F.x k.val v * ((v τ : ℕ) : ℝ) + θ * ∑ v, G.x k.val v * ((v τ : ℕ) : ℝ) by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring]
    ring
  rw [hmean]
  have e : (1 - θ) * typeMean ty F k τ + θ * typeMean ty G k τ - (k.val : ℝ) / (m : ℝ)
      = (1 - θ) * (typeMean ty F k τ - (k.val : ℝ) / (m : ℝ))
        + θ * (typeMean ty G k τ - (k.val : ℝ) / (m : ℝ)) := by ring
  rw [e]
  have hA := h1 k τ hτ
  have hB := h2 k τ hτ
  have hθ' : 0 ≤ 1 - θ := by linarith
  calc |(1 - θ) * (typeMean ty F k τ - (k.val : ℝ) / (m : ℝ))
        + θ * (typeMean ty G k τ - (k.val : ℝ) / (m : ℝ))|
      ≤ (1 - θ) * |typeMean ty F k τ - (k.val : ℝ) / (m : ℝ)|
        + θ * |typeMean ty G k τ - (k.val : ℝ) / (m : ℝ)| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg hθ', abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * (η₁ / m) + θ * (η₂ / m) :=
        add_le_add (mul_le_mul_of_nonneg_left hA hθ') (mul_le_mul_of_nonneg_left hB hθ0)
    _ = ((1 - θ) * η₁ + θ * η₂) / m := by ring

theorem band_mono (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) (η η' : ℝ)
    (h : FlowBand ty F η) (hle : η ≤ η') (hm : 0 < m) : FlowBand ty F η' := by
  intro k τ hτ
  refine (h k τ hτ).trans ?_
  exact div_le_div_of_nonneg_right hle (by exact_mod_cast hm.le)

#print axioms mixFlow_feasible
#print axioms mixFlow_obj
#print axioms mixFlow_mean
#print axioms mixTwo_feasible
#print axioms mixTwo_obj
#print axioms mixTwo_band
#print axioms band_mono

end CIGAMF.P13.PaperCPathMix
