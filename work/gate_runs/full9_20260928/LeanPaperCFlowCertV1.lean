import «LeanPaperCFreeBandV1»

/-!
# Paper C: dual certificates for the banded count-flow program

A lower bound on the flow program of `LeanPaperCTypedFlowV1` from a finite certificate. The
certificate has budget weights `μ`, band multipliers `ℓ`, and node potentials `φ` on the count
states. It is checked only on the reachable states: those inside the box and on their own
layer.

* `potential_bound`: for any layered flow, if `φ_k(v) ≤ C_k(v) + φ_{k+1}(w)` on every edge that
  carries flow, then `Σ_v x_0(v) φ_0(v) ≤ Σ_{k<M} Σ_v x_k(v) C_k(v) + Σ_v x_M(v) φ_M(v)`. The
  potentials telescope along the layers.
* `layer_served`: a count-feasible flow occupies at layer `k ≤ m` only states that have served
  `k` items.
* `cert_lower`: with `μ ≥ 0` summing to one on the budgets `K`, any `ℓ`, and `φ` meeting the edge
  inequality on reachable states, with node cost `μ_k c_k(v) + Σ_τ ℓ_{kτ}(v_τ/n_τ - k/m)`, every
  banded count-feasible flow has
  `max_{k∈K} E c_k ≥ φ_0(0) - (η/m) Σ_{k<m,τ} |ℓ_{kτ}|`.
  This is weak duality for the flow LP, proved once.
-/

namespace CIGAMF.P13.PaperCFlowCert

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCFlowBandJoin CIGAMF.P13.PaperCVacuity
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFreeBand

/-! ## 1. Potentials on any layered flow -/

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Potentials telescope along a layered flow.** -/
theorem potential_bound (F : LayeredFlow V) (C φ : ℕ → V → ℝ) (M : ℕ)
    (hedge : ∀ k < M, ∀ v w, F.f k v w ≠ 0 → φ k v ≤ C k v + φ (k + 1) w) :
    ∑ v, F.x 0 v * φ 0 v
      ≤ ∑ k ∈ range M, ∑ v, F.x k v * C k v + ∑ v, F.x M v * φ M v := by
  induction M with
  | zero => simp
  | succ M ih =>
    have ih' := ih fun k hk v w h => hedge k (by omega) v w h
    have hstep : ∑ v, F.x M v * φ M v
        ≤ ∑ v, F.x M v * C M v + ∑ w, F.x (M + 1) w * φ (M + 1) w := by
      calc ∑ v, F.x M v * φ M v = ∑ v, ∑ w, F.f M v w * φ M v := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [← F.outflow M v, Finset.sum_mul]
        _ ≤ ∑ v, ∑ w, F.f M v w * (C M v + φ (M + 1) w) := by
            refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => ?_
            by_cases h : F.f M v w = 0
            · rw [h]; simp
            · exact mul_le_mul_of_nonneg_left (hedge M (by omega) v w h) (F.fnn M v w)
        _ = ∑ v, F.x M v * C M v + ∑ w, F.x (M + 1) w * φ (M + 1) w := by
            simp only [mul_add, Finset.sum_add_distrib]
            congr 1
            · refine Finset.sum_congr rfl fun v _ => ?_
              rw [← F.outflow M v, Finset.sum_mul]
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun w _ => ?_
              rw [← F.inflow M w, Finset.sum_mul]
    rw [Finset.sum_range_succ]
    linarith

end Generic

/-! ## 2. Reachable states of a count-feasible flow -/

variable {d m : ℕ}

theorem inflow_pos (F : LayeredFlow (CState d m)) (k : ℕ) (v w : CState d m)
    (h : F.f k v w ≠ 0) : F.x (k + 1) w ≠ 0 := by
  have hpos : 0 < F.f k v w := lt_of_le_of_ne (F.fnn k v w) (Ne.symm h)
  have hle : F.f k v w ≤ F.x (k + 1) w := by
    rw [← F.inflow k w]
    exact Finset.single_le_sum (f := fun u => F.f k u w) (fun u _ => F.fnn k u w)
      (Finset.mem_univ v)
  exact (lt_of_lt_of_le hpos hle).ne'

theorem outflow_pos (F : LayeredFlow (CState d m)) (k : ℕ) (v w : CState d m)
    (h : F.f k v w ≠ 0) : F.x k v ≠ 0 := fun hx => h (F.no_flow_from_empty k v w hx)

/-- **Layer `k` holds only states that have served `k` items.** -/
theorem layer_served (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : CountFeasibleH ty F) : ∀ k, k ≤ m → ∀ v, F.x k v ≠ 0 → served v = k := by
  intro k
  induction k with
  | zero =>
    intro _ v hv
    unfold served
    simp [start_empty ty F hF v hv]
  | succ k ih =>
    intro hk w hw
    have hsum : ∑ u, F.f k u w ≠ 0 := by rw [F.inflow k w]; exact hw
    obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    have hstep : StepC v w := by
      by_contra hns
      exact hv (hF.2.1 k (by omega) v w hns)
    have hsv := ih (by omega) v (outflow_pos F k v w hv)
    rw [served_step v w hstep, hsv]
    push_cast; ring

/-- A state inside the box of the multiplicities. -/
def InBox (ty : Fin m → Fin d) (v : CState d m) : Prop := ∀ τ, (v τ : ℕ) ≤ mult ty τ

/-! ## 3. The certificate -/

/-- The band term of a certificate at a state. -/
noncomputable def bandTerm (ty : Fin m → Fin d) (ℓ : ℕ → Fin d → ℝ) (k : ℕ)
    (v : CState d m) : ℝ :=
  ∑ τ, ℓ k τ * (((v τ : ℕ) : ℝ) / (mult ty τ : ℝ) - (k : ℝ) / (m : ℝ))

/-- The node cost of a certificate. -/
noncomputable def nodeCost (ty : Fin m → Fin d) (c : Fin (m + 1) → CState d m → ℝ)
    (μ : ℕ → ℝ) (ℓ : ℕ → Fin d → ℝ) (k : ℕ) (v : CState d m) : ℝ :=
  μ k * c (Fin.ofNat (m + 1) k) v + bandTerm ty ℓ k v

theorem band_sum (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) (hF : CountFeasibleH ty F)
    (η : ℝ) (hband : FlowBand ty F η) (ℓ : ℕ → Fin d → ℝ)
    (hℓ0 : ∀ k τ, mult ty τ = 0 → ℓ k τ = 0) (k : ℕ) (hk : k ≤ m) :
    ∑ v, F.x k v * bandTerm ty ℓ k v ≤ (η / m) * ∑ τ, |ℓ k τ| := by
  have hmass := mass_one F hF.1 k
  have hswap : ∑ v, F.x k v * bandTerm ty ℓ k v
      = ∑ τ, ℓ k τ * (typeMean ty F ⟨k, Nat.lt_succ_of_le hk⟩ τ - (k : ℝ) / (m : ℝ)) := by
    unfold bandTerm
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hmean : typeMean ty F ⟨k, Nat.lt_succ_of_le hk⟩ τ
        = (∑ v, F.x k v * ((v τ : ℕ) : ℝ)) / (mult ty τ : ℝ) := rfl
    rw [hmean]
    calc ∑ v, F.x k v * (ℓ k τ * (((v τ : ℕ) : ℝ) / (mult ty τ : ℝ) - (k : ℝ) / (m : ℝ)))
        = ∑ v, (ℓ k τ / (mult ty τ : ℝ) * (F.x k v * ((v τ : ℕ) : ℝ))
            - ℓ k τ * ((k : ℝ) / (m : ℝ)) * F.x k v) :=
          Finset.sum_congr rfl fun v _ => by ring
      _ = ℓ k τ / (mult ty τ : ℝ) * ∑ v, F.x k v * ((v τ : ℕ) : ℝ)
            - ℓ k τ * ((k : ℝ) / (m : ℝ)) * ∑ v, F.x k v := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [hmass]; ring
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  by_cases h0 : mult ty τ = 0
  · rw [hℓ0 k τ h0]; simp
  · have hb := hband ⟨k, Nat.lt_succ_of_le hk⟩ τ (Nat.pos_of_ne_zero h0)
    have key : |ℓ k τ * (typeMean ty F ⟨k, Nat.lt_succ_of_le hk⟩ τ - (k : ℝ) / (m : ℝ))|
        ≤ |ℓ k τ| * (η / m) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    have := le_abs_self (ℓ k τ * (typeMean ty F ⟨k, Nat.lt_succ_of_le hk⟩ τ - (k : ℝ) / (m : ℝ)))
    nlinarith

/-- **Weak duality for the banded count-flow program.** -/
theorem cert_lower (ty : Fin m → Fin d) (c : Fin (m + 1) → CState d m → ℝ)
    (K : Finset (Fin (m + 1))) (hK : K.Nonempty)
    (μ : ℕ → ℝ) (hμ0 : ∀ k, 0 ≤ μ k) (hμK : ∀ k : Fin (m + 1), k ∉ K → μ k = 0)
    (hμm : ∀ k, m ≤ k → μ k = 0) (hμ1 : ∑ k ∈ range m, μ k = 1)
    (ℓ : ℕ → Fin d → ℝ) (hℓ0 : ∀ k τ, mult ty τ = 0 → ℓ k τ = 0)
    (φ : ℕ → CState d m → ℝ) (Φ : ℝ)
    (hedge : ∀ k < m, ∀ v w, InBox ty v → served v = k → InBox ty w → StepC v w →
      φ k v ≤ nodeCost ty c μ ℓ k v + φ (k + 1) w)
    (hend : ∀ v, InBox ty v → served v = m → φ m v = 0)
    (hstart : Φ ≤ φ 0 0)
    (η : ℝ) (F : LayeredFlow (CState d m)) (hF : CountFeasibleH ty F) (hband : FlowBand ty F η) :
    Φ - (η / m) * ∑ k ∈ range m, ∑ τ, |ℓ k τ| ≤ K.sup' hK (flowObj c F) := by
  -- the potential bound on the reachable edges
  have hedge' : ∀ k < m, ∀ v w, F.f k v w ≠ 0 →
      φ k v ≤ nodeCost ty c μ ℓ k v + φ (k + 1) w := by
    intro k hk v w h
    have hv := outflow_pos F k v w h
    have hw := inflow_pos F k v w h
    refine hedge k hk v w (hF.2.2.2 k v hv) (layer_served ty F hF k hk.le v hv)
      (hF.2.2.2 (k + 1) w hw) ?_
    by_contra hns
    exact h (hF.2.1 k hk v w hns)
  have hpot := potential_bound F (nodeCost ty c μ ℓ) φ m hedge'
  -- layer 0 is the empty state, layer m contributes nothing
  have h0 : ∑ v, F.x 0 v * φ 0 v = φ 0 0 := by
    have : ∀ v, F.x 0 v * φ 0 v = F.x 0 v * φ 0 0 := by
      intro v
      by_cases hv : F.x 0 v = 0
      · rw [hv]; simp
      · have : v = 0 := funext fun τ => Fin.ext (by simpa using start_empty ty F hF v hv τ)
        rw [this]
    rw [Finset.sum_congr rfl fun v _ => this v, ← Finset.sum_mul, mass_one F hF.1 0, one_mul]
  have hM : ∑ v, F.x m v * φ m v = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : F.x m v = 0
    · rw [hv, zero_mul]
    · rw [hend v (hF.2.2.2 m v hv) (layer_served ty F hF m le_rfl v hv), mul_zero]
  rw [h0, hM, add_zero] at hpot
  -- split the node cost
  have hsplit : ∑ k ∈ range m, ∑ v, F.x k v * nodeCost ty c μ ℓ k v
      = ∑ k ∈ range m, μ k * flowObj c F (Fin.ofNat (m + 1) k)
        + ∑ k ∈ range m, ∑ v, F.x k v * bandTerm ty ℓ k v := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    unfold nodeCost flowObj
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have hkm : k < m + 1 := by have := Finset.mem_range.mp hk; omega
    have hval : ((Fin.ofNat (m + 1) k : Fin (m + 1)) : ℕ) = k := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt hkm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hval]; ring
  have hband' : ∑ k ∈ range m, ∑ v, F.x k v * bandTerm ty ℓ k v
      ≤ (η / m) * ∑ k ∈ range m, ∑ τ, |ℓ k τ| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk =>
      band_sum ty F hF η hband ℓ hℓ0 k (by have := Finset.mem_range.mp hk; omega)
  -- the weighted objective is at most the worst budget
  have hmax : ∑ k ∈ range m, μ k * flowObj c F (Fin.ofNat (m + 1) k) ≤ K.sup' hK (flowObj c F) := by
    calc ∑ k ∈ range m, μ k * flowObj c F (Fin.ofNat (m + 1) k)
        ≤ ∑ k ∈ range m, μ k * K.sup' hK (flowObj c F) := by
          refine Finset.sum_le_sum fun k hk => ?_
          by_cases hkK : (Fin.ofNat (m + 1) k : Fin (m + 1)) ∈ K
          · exact mul_le_mul_of_nonneg_left (Finset.le_sup' _ hkK) (hμ0 k)
          · have hkm : k < m + 1 := by have := Finset.mem_range.mp hk; omega
            have hμk : μ k = 0 := by
              have := hμK _ hkK
              have hval : ((Fin.ofNat (m + 1) k : Fin (m + 1)) : ℕ) = k := by
                simp [Fin.ofNat, Nat.mod_eq_of_lt hkm]
              rwa [hval] at this
            rw [hμk]; simp
      _ = K.sup' hK (flowObj c F) := by rw [← Finset.sum_mul, hμ1, one_mul]
  linarith

#print axioms potential_bound
#print axioms layer_served
#print axioms band_sum
#print axioms cert_lower

end CIGAMF.P13.PaperCFlowCert
