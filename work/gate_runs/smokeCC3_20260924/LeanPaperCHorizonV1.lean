import «LeanPaperCVacuityV1»

/-!
# Paper C: the finite-horizon flow domain, and its start and end DERIVED

`countFeasible_empty` (`LeanPaperCVacuityV1`) shows the old domain has no unit flow: legality
at every `k` forces the expected served-count to grow past its own ceiling.  This module
gives the repaired domain and proves the two things that were previously ASSUMED about it.

* `CountFeasibleH` asks for legality only while items remain (`k < m`) and for the flow to
  idle afterwards, which is the self-loop continuation.  `horizon_flow` exhibits one, so the
  new domain is not empty either -- the mistake is not repeated in the other direction.
* `served_grows_H` is the count identity on the repaired domain: the expected served-count is
  `E_0 + k` up to the horizon and constant after.
* `start_empty` and `end_full` are the two conditions the old definition took as hypotheses.
  They are now **derived** from the LP's own capacity constraint `v_tau <= mult ty tau`:
  the served-count is at most `m` on the support, it grows by one a layer, so its value at
  layer `0` must be `0` and at layer `m` must be `m`, and the capacity then pins the state at
  both ends.

`mult_sum` is the arithmetic that makes the ceiling exactly `m`: every item has exactly one
type, so the multiplicities sum to the number of items.
-/

namespace CIGAMF.P13.PaperCHorizon

open Finset
open CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.CFinal
open CIGAMF.P13.PaperCVacuity

variable {d m : ℕ}

/-! ## The multiplicities sum to the number of items -/

theorem mult_sum (ty : Fin m → Fin d) : ∑ τ, mult ty τ = m := by
  classical
  unfold mult
  have h := Finset.card_eq_sum_card_fiberwise
    (f := ty) (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin d)))
    (fun j _ => Finset.mem_univ (ty j))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

/-! ## The repaired domain -/

/-- Legality while items remain, idling afterwards, and the LP's capacity constraint. -/
def CountFeasibleH (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) : Prop :=
  (∑ v, F.x 0 v = 1)
  ∧ (∀ k, k < m → ∀ v w, ¬ StepC v w → F.f k v w = 0)
  ∧ (∀ k, m ≤ k → ∀ v w, v ≠ w → F.f k v w = 0)
  ∧ (∀ k v, F.x k v ≠ 0 → ∀ τ, (v τ : ℕ) ≤ mult ty τ)

/-- **The served-count identity, up to the horizon.** -/
theorem served_grows_H (F : LayeredFlow (CState d m))
    (hlegal : ∀ k, k < m → ∀ v w, ¬ StepC v w → F.f k v w = 0)
    (h0 : ∑ v, F.x 0 v = 1) :
    ∀ k, k ≤ m → ∑ v, served v * F.x k v = (∑ v, served v * F.x 0 v) + (k : ℝ) := by
  classical
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hklt : k < m := by omega
      have hexpand : ∑ w, served w * F.x (k + 1) w
          = ∑ u, (served u + 1) * F.x k u := by
        have hl : ∀ w, served w * F.x (k + 1) w = ∑ u, served w * F.f k u w := by
          intro w
          rw [← Finset.mul_sum, F.inflow k w]
        rw [Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        have hterm : ∀ w, served w * F.f k u w = (served u + 1) * F.f k u w := by
          intro w
          by_cases hs : StepC u w
          · rw [served_step u w hs]
          · rw [hlegal k hklt u w hs, mul_zero, mul_zero]
        rw [Finset.sum_congr rfl (fun w _ => hterm w), ← Finset.mul_sum, F.outflow k u]
      rw [hexpand]
      have hsplit : ∑ u, (served u + 1) * F.x k u
          = (∑ u, served u * F.x k u) + ∑ u, F.x k u := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun u _ => by ring)
      rw [hsplit, ih (by omega), mass_one F h0 k]
      push_cast
      ring

/-- **On the support the served-count never exceeds the number of items.**  This is the
capacity constraint, summed. -/
theorem served_le_m (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hcap : ∀ k v, F.x k v ≠ 0 → ∀ τ, (v τ : ℕ) ≤ mult ty τ)
    (k : ℕ) (v : CState d m) (hv : F.x k v ≠ 0) : served v ≤ (m : ℝ) := by
  unfold served
  have hterm : ∀ τ : Fin d, ((v τ : ℕ) : ℝ) ≤ ((mult ty τ : ℕ) : ℝ) := by
    intro τ
    exact_mod_cast hcap k v hv τ
  calc ∑ τ : Fin d, ((v τ : ℕ) : ℝ)
      ≤ ∑ τ : Fin d, ((mult ty τ : ℕ) : ℝ) := Finset.sum_le_sum (fun τ _ => hterm τ)
    _ = (m : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (mult_sum ty)

/-- **The expected served-count at layer `0` is zero** -- derived, not assumed.  At the
horizon the count is `E_0 + m`, and it can never exceed `m`, so `E_0 <= 0`; it is also
nonnegative. -/
theorem expected_served_zero (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (h : CountFeasibleH ty F) : ∑ v, served v * F.x 0 v = 0 := by
  obtain ⟨h0, hlegal, -, hcap⟩ := h
  have hgrow := served_grows_H F hlegal h0 m le_rfl
  have hle : ∑ v, served v * F.x m v ≤ (m : ℝ) := by
    calc ∑ v, served v * F.x m v ≤ ∑ v, (m : ℝ) * F.x m v := by
          refine Finset.sum_le_sum (fun v _ => ?_)
          by_cases hv : F.x m v = 0
          · rw [hv, mul_zero, mul_zero]
          · exact mul_le_mul_of_nonneg_right (served_le_m ty F hcap m v hv) (F.xnn m v)
      _ = (m : ℝ) := by rw [← Finset.mul_sum, mass_one F h0 m, mul_one]
  have hnn : 0 ≤ ∑ v, served v * F.x 0 v :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (served_nonneg v) (F.xnn 0 v))
  linarith [hgrow, hle, hnn]

/-- **(Step 2, first half) Every state the flow occupies at layer `0` is empty.** -/
theorem start_empty (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (h : CountFeasibleH ty F) (v : CState d m) (hv : F.x 0 v ≠ 0) (τ : Fin d) :
    (v τ : ℕ) = 0 := by
  classical
  have hzero := expected_served_zero ty F h
  have hpos : 0 < F.x 0 v := lt_of_le_of_ne (F.xnn 0 v) (Ne.symm hv)
  have hterms : ∀ u, 0 ≤ served u * F.x 0 u :=
    fun u => mul_nonneg (served_nonneg u) (F.xnn 0 u)
  have hv0 : served v * F.x 0 v = 0 :=
    le_antisymm ((Finset.single_le_sum (fun u _ => hterms u) (Finset.mem_univ v)).trans
      (le_of_eq hzero)) (hterms v)
  have hs : served v = 0 := by
    rcases mul_eq_zero.mp hv0 with hs | hx
    · exact hs
    · exact absurd hx hv
  have hnn : ∀ σ : Fin d, (0 : ℝ) ≤ ((v σ : ℕ) : ℝ) := fun σ => by positivity
  have hle := Finset.single_le_sum (f := fun σ : Fin d => ((v σ : ℕ) : ℝ))
    (fun σ _ => hnn σ) (Finset.mem_univ τ)
  rw [← served] at hle
  have : ((v τ : ℕ) : ℝ) ≤ 0 := by rw [hs] at hle; exact hle
  have : ((v τ : ℕ) : ℝ) = 0 := le_antisymm this (hnn τ)
  exact_mod_cast this

/-- **(Step 2, second half) Every state the flow occupies at the horizon is full.**  The
expected count is exactly `m` there and no state exceeds `m`, so the support sits on the
capacity, which the LP pins coordinate by coordinate. -/
theorem end_full (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (h : CountFeasibleH ty F) (v : CState d m) (hv : F.x m v ≠ 0) (τ : Fin d) :
    (v τ : ℕ) = mult ty τ := by
  classical
  have hzero := expected_served_zero ty F h
  obtain ⟨h0, hlegal, -, hcap⟩ := h
  have hgrow := served_grows_H F hlegal h0 m le_rfl
  rw [hzero, zero_add] at hgrow
  -- every occupied state has served = m
  have hdefect : ∑ v', ((m : ℝ) - served v') * F.x m v' = 0 := by
    have hsplit : ∑ v', ((m : ℝ) - served v') * F.x m v'
        = (m : ℝ) * (∑ v', F.x m v') - ∑ v', served v' * F.x m v' := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun v' _ => by ring)
    rw [hsplit, mass_one F h0 m, mul_one, hgrow, sub_self]
  have hterms : ∀ u, 0 ≤ ((m : ℝ) - served u) * F.x m u := by
    intro u
    by_cases hu : F.x m u = 0
    · rw [hu, mul_zero]
    · exact mul_nonneg (by linarith [served_le_m ty F hcap m u hu]) (F.xnn m u)
  have hv0 : ((m : ℝ) - served v) * F.x m v = 0 :=
    le_antisymm ((Finset.single_le_sum (fun u _ => hterms u) (Finset.mem_univ v)).trans
      (le_of_eq hdefect)) (hterms v)
  have hs : served v = (m : ℝ) := by
    rcases mul_eq_zero.mp hv0 with hs | hx
    · linarith
    · exact absurd hx hv
  -- served = m together with the capacity forces equality coordinate by coordinate
  have hcapv : ∀ σ : Fin d, ((v σ : ℕ) : ℝ) ≤ ((mult ty σ : ℕ) : ℝ) := by
    intro σ
    exact_mod_cast hcap m v hv σ
  have htot : ∑ σ : Fin d, ((mult ty σ : ℕ) : ℝ) = (m : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (mult_sum ty)
  have heq : ∀ σ : Fin d, ((v σ : ℕ) : ℝ) = ((mult ty σ : ℕ) : ℝ) := by
    intro σ
    by_contra hne
    have hlt : ((v σ : ℕ) : ℝ) < ((mult ty σ : ℕ) : ℝ) :=
      lt_of_le_of_ne (hcapv σ) hne
    have hstrict : ∑ σ' : Fin d, ((v σ' : ℕ) : ℝ) < ∑ σ' : Fin d, ((mult ty σ' : ℕ) : ℝ) :=
      Finset.sum_lt_sum (fun σ' _ => hcapv σ') ⟨σ, Finset.mem_univ σ, hlt⟩
    rw [← served] at hstrict
    rw [hs, htot] at hstrict
    exact lt_irrefl _ hstrict
  exact_mod_cast heq τ

/-! ## The repaired domain is inhabited -/

/-- How many of the first `k` items carry type `τ`. -/
def cnt (ty : Fin m → Fin d) (k : ℕ) (τ : Fin d) : ℕ :=
  ∑ j : Fin m, if (j : ℕ) < k ∧ ty j = τ then 1 else 0

theorem cnt_le_mult (ty : Fin m → Fin d) (k : ℕ) (τ : Fin d) : cnt ty k τ ≤ mult ty τ := by
  classical
  unfold cnt mult
  rw [Finset.card_filter]
  refine Finset.sum_le_sum (fun j _ => ?_)
  split_ifs <;> simp_all

theorem mult_le_m (ty : Fin m → Fin d) (τ : Fin d) : mult ty τ ≤ m := by
  classical
  unfold mult
  calc (Finset.univ.filter (fun j : Fin m => ty j = τ)).card
      ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by rw [Finset.card_univ, Fintype.card_fin]

theorem cnt_lt (ty : Fin m → Fin d) (k : ℕ) (τ : Fin d) : cnt ty k τ < m + 1 :=
  Nat.lt_succ_of_le ((cnt_le_mult ty k τ).trans (mult_le_m ty τ))

/-- The state reached after the first `min k m` items have been served in index order. -/
def stC (ty : Fin m → Fin d) (k : ℕ) : CState d m :=
  fun τ => ⟨cnt ty (min k m) τ, cnt_lt ty (min k m) τ⟩

/-- **Serving one more item raises exactly one count.** -/
theorem cnt_succ (ty : Fin m → Fin d) (k : ℕ) (hk : k < m) (τ : Fin d) :
    cnt ty (k + 1) τ = cnt ty k τ + (if ty ⟨k, hk⟩ = τ then 1 else 0) := by
  classical
  have hsplit : ∀ j : Fin m,
      (if (j : ℕ) < k + 1 ∧ ty j = τ then (1 : ℕ) else 0)
        = (if (j : ℕ) < k ∧ ty j = τ then (1 : ℕ) else 0)
          + (if j = (⟨k, hk⟩ : Fin m) then (if ty j = τ then (1 : ℕ) else 0) else 0) := by
    intro j
    by_cases hj : j = (⟨k, hk⟩ : Fin m)
    · subst hj
      simp
    · have hne : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
      by_cases hlt : (j : ℕ) < k
      · have hlt' : (j : ℕ) < k + 1 := by omega
        simp [hj, hlt, hlt']
      · have h1 : ¬ ((j : ℕ) < k + 1) := by omega
        simp [hj, hlt, h1]
  unfold cnt
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (⟨k, hk⟩ : Fin m)
      (fun j => if ty j = τ then (1 : ℕ) else 0)]
  simp

/-- **Before the horizon the path takes a legal step.** -/
theorem stC_step (ty : Fin m → Fin d) (k : ℕ) (hk : k < m) :
    StepC (stC ty k) (stC ty (k + 1)) := by
  classical
  have hmin : min k m = k := by omega
  have hmin' : min (k + 1) m = k + 1 := by omega
  refine ⟨ty ⟨k, hk⟩, ?_, ?_⟩
  · show cnt ty (min (k + 1) m) (ty ⟨k, hk⟩) = cnt ty (min k m) (ty ⟨k, hk⟩) + 1
    rw [hmin, hmin', cnt_succ ty k hk, if_pos rfl]
  · intro τ' hτ'
    apply Fin.ext
    show cnt ty (min (k + 1) m) τ' = cnt ty (min k m) τ'
    rw [hmin, hmin', cnt_succ ty k hk, if_neg (fun h => hτ' h.symm), add_zero]

/-- **After the horizon the path stands still.** -/
theorem stC_idle (ty : Fin m → Fin d) (k : ℕ) (hk : m ≤ k) : stC ty (k + 1) = stC ty k := by
  have h1 : min k m = m := by omega
  have h2 : min (k + 1) m = m := by omega
  funext τ
  apply Fin.ext
  show cnt ty (min (k + 1) m) τ = cnt ty (min k m) τ
  rw [h1, h2]

/-- The deterministic unit flow that serves the items in index order and then idles. -/
noncomputable def horizonFlow (ty : Fin m → Fin d) : LayeredFlow (CState d m) where
  x := fun k v => if v = stC ty k then 1 else 0
  f := fun k v w => if v = stC ty k ∧ w = stC ty (k + 1) then 1 else 0
  xnn := by intro k v; split_ifs <;> norm_num
  fnn := by intro k v w; split_ifs <;> norm_num
  outflow := by
    intro k v
    by_cases hv : v = stC ty k <;> simp [hv]
  inflow := by
    intro k w
    by_cases hw : w = stC ty (k + 1) <;> simp [hw]

/-- **The repaired domain is not empty.**  `countFeasible_empty` showed the old domain had no
unit flow at all; this shows the repair did not overshoot in the other direction, so
`start_empty` and `end_full` are statements about something that exists. -/
theorem horizon_flow (ty : Fin m → Fin d) : CountFeasibleH ty (horizonFlow ty) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ∑ v, (if v = stC ty 0 then (1 : ℝ) else 0) = 1
    simp
  · intro k hk v w hstep
    show (if v = stC ty k ∧ w = stC ty (k + 1) then (1 : ℝ) else 0) = 0
    rw [if_neg]
    rintro ⟨hv, hw⟩
    subst hv; subst hw
    exact hstep (stC_step ty k hk)
  · intro k hk v w hne
    show (if v = stC ty k ∧ w = stC ty (k + 1) then (1 : ℝ) else 0) = 0
    rw [if_neg]
    rintro ⟨hv, hw⟩
    exact hne (by rw [hv, hw, stC_idle ty k hk])
  · intro k v hx τ
    have hv : v = stC ty k := by
      by_contra h
      exact hx (by show (if v = stC ty k then (1 : ℝ) else 0) = 0; rw [if_neg h])
    rw [hv]
    exact cnt_le_mult ty (min k m) τ

/-! ## Audit -/

#print axioms cnt_le_mult
#print axioms cnt_succ
#print axioms stC_step
#print axioms stC_idle
#print axioms horizon_flow
#print axioms mult_sum
#print axioms served_grows_H
#print axioms served_le_m
#print axioms expected_served_zero
#print axioms start_empty
#print axioms end_full

end CIGAMF.P13.PaperCHorizon
