import «LeanD6ScalarWidthSharpV1»
import «LeanD6MovingNuisanceRegretV1»

/-! # Package B: the scalar/joint boundary is sharp, and the local gain is quadratic.

`LeanD6ScalarWidthSharpV1.joint_mixture_scalar_bound_sharp` caps every legal
design by the B-scalar value `mu^2/(2q)` as soon as
`(1-mu)^2 * width <= mu^2 * charge`. In the power model `charge = width^z` and
`width = 2` (a B-pair with `h = false`) that condition reads `2^z >= 2(1-mu)^2/mu^2`,
i.e. `z >= z_* = 1 + 2 log_2((1-mu)/mu)`. Nothing so far showed the condition is
NECESSARY: the scalar design might have stayed optimal below `z_*`.

This file proves it does not. Fix `0 < mu < 1/2`, write `g = 1-mu`,
`V0 = mu^2/(2q)` and `cstar = 2 g^2/mu^2` (so the pair charge at the boundary is
`c_{z_*} = cstar`). For a pair charge `cz < cstar` (i.e. `z < z_*`) the explicit
two-width design

  * cost mass `1-eta` spread uniformly over the `q` B-scalars (charge 1 each),
  * cost mass `eta` spread uniformly over the ordered distinct pairs `(u,v)`
    from B, i.e. uniformly over the `C(q,2)` unordered B-pairs with `h = false`,
    each charged `cz`,

beats `V0` against EVERY wrong label and EVERY nuisance, by an amount that is
quadratic in the distance to the boundary.

WHAT IS PROVED HERE.

* `scalar_information_B`, `pair_information` — the per-measurement KL of this
  design computed from the ACTUAL construction means (`actual_mean_affine`,
  `actual_query_mean`), not from a fitted model.
* `design_swap_value` — for a label changing exactly one B coordinate the
  design's information is EXACTLY `C_eta + 2 B_eta x + A_eta x^2` in
  `x = nu - mu`, with the coefficients of the handoff.
* `design_multi_lower` — a label changing `d` B coordinates already collects
  `(1-eta) d V0` from the scalar half alone, so for small `eta` it is not the
  bottleneck.
* `design_value_lower` — combining the two branches over the COMPLETE family of
  wrong labels (`d = 1` and `d >= 2` exhaust it) and over ALL real nuisances:
  the design's value is at least `V0 + gain(eta)` with
  `gain(eta) = eta V0 (cstar/cz - 1) - 4 eta^2 g^2/(q(q-1) cz^2)`.
* `strict_improvement` — `gain(eta) > 0` for an explicit interval of `eta`
  whenever `cz < cstar`; hence the scalar design is STRICTLY suboptimal below
  the boundary and `z_*` is exactly the transition.
* `quadratic_gain` — at `eta = eta_0` the gain is `V0^2 (cstar/cz-1)^2
  q(q-1) cz^2/(16 g^2)`, which is `Theta((cstar/cz - 1)^2)`: the quadratic law.

WHAT THIS DOES NOT ESTABLISH.

- These are LOWER bounds on the value of ONE design, i.e. lower bounds on the
  game optimum. No matching dual upper bound over the whole design family is
  proved here; the numerical sandwich (probe `B1_d6_width_transition_local.py`)
  closes it only numerically, and only while `q h` is small.
- The constant `1/16` in `quadratic_gain` is not sharp: the slack comes from the
  crude bound `1/(1-eta) <= 2`. The sharp constant `1/8`, i.e.
  `(q-1) g^2 (log 2)^2 h^2/(8q)` with `h = z_* - z`, is NUMERICAL EVIDENCE only.
- Everything is stated in the charge variable `cz`; no `Real.rpow`, no
  logarithm, and hence no statement about `z` itself is formalised here. The
  translation `cz = 2^z`, `cstar/cz = 2^{z_*-z}` is arithmetic done outside Lean.
- `eta` is not optimised inside Lean beyond the explicit instantiation, and the
  hypothesis `eta <= cz/(cz+cstar)` (which keeps the `d >= 2` labels off the
  bottleneck) is carried, not discharged.
- Nothing here concerns adaptivity, stopping times, or query setup costs.
-/

namespace CIGAMF.P13.D6WidthTransitionLocal
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6GaussianQueryDominance
open CIGAMF.P13.D6MovingNuisanceRegret CIGAMF.P13.D6ScalarWidthRegion
noncomputable section
variable {n : ℕ}

/-- The two-width design, evaluated against the label `C` at nuisance `nu`.
Cost mass `1-eta` uniform on the `q` B-scalars (charge 1) and cost mass `eta`
uniform on the `q(q-1)` ordered distinct B-pairs (charge `cz` each); information
is cost mass times KL divided by charge, as in the width-cost game. -/
def designInfo (A C : Finset (I n)) (j : I n) (mu nu eta cz q : ℝ) : ℝ :=
  (1-eta)/q*(∑ i ∈ others A j, information A C j mu nu (.inl i))
    + eta/(q*(q-1)*cz)*(∑ u ∈ others A j, ∑ v ∈ others A j,
        if u = v then (0:ℝ) else information A C j mu nu (.inr ({u,v},false)))

lemma sum_off_const (S : Finset (I n)) (u : I n) (hu : u ∈ S) (c : ℝ) :
    (∑ v ∈ S, if u = v then (0:ℝ) else c) = ((S.card : ℝ)-1)*c := by
  have h : ∀ v ∈ S, (if u = v then (0:ℝ) else c) = c-(if u = v then c else 0) := by
    intro v _; split_ifs <;> ring
  rw [sum_congr rfl h, sum_sub_distrib, sum_const,
    Finset.sum_ite_eq S u (fun _ => c), if_pos hu, nsmul_eq_mul]
  ring

lemma card_erase_real (S : Finset (I n)) (b : I n) (hb : b ∈ S) (q : ℝ)
    (hS : (S.card : ℝ) = q) : ((S.erase b).card : ℝ) = q-1 := by
  have h1 : 1 ≤ S.card := card_pos.mpr ⟨b,hb⟩
  rw [card_erase_of_mem hb, Nat.cast_sub h1, hS, Nat.cast_one]

/-- Scalar KL of the design's B-coordinates, from the ACTUAL construction means. -/
lemma scalar_information_B (A C : Finset (I n)) (j i : I n) (hjA : j ∉ A) (hjC : j ∉ C)
    (mu nu : ℝ) (hi : i ∈ others A j) :
    information A C j mu nu (.inl i) = (if i ∈ C then mu^2 else (nu-mu)^2)/2 := by
  obtain ⟨hiA,hij⟩ := others_not_mem A j i hi
  have hmA : actualMean A j mu (Sum.inl i) = 1-mu := by
    rw [actual_mean_affine A j hjA 0 mu _ (by trivial)]
    simp [meanOffset, meanSlope, hiA, hij]
    ring
  have hmC : actualMean C j nu (Sum.inl i) = if i ∈ C then 1 else 1-nu := by
    rw [actual_mean_affine C j hjC 0 nu _ (by trivial)]
    by_cases hiC : i ∈ C
    · simp [meanOffset, meanSlope, hiC]
    · simp [meanOffset, meanSlope, hiC, hij]
      ring
  rw [information_eq_mean, hmA, hmC]
  by_cases hiC : i ∈ C
  · rw [if_pos hiC, if_pos hiC]; ring
  · rw [if_neg hiC, if_neg hiC]; ring

/-- Pair KL of the design's B-pairs, from the ACTUAL construction means. -/
lemma pair_information (A C : Finset (I n)) (j u v : I n) (hjA : j ∉ A) (hjC : j ∉ C)
    (mu nu : ℝ) (hu : u ∈ others A j) (hv : v ∈ others A j) (huv : u ≠ v) :
    information A C j mu nu (.inr ({u,v},false)) =
      (2*(nu-mu)+(1-nu)*((if u ∈ C then (1:ℝ) else 0)+(if v ∈ C then (1:ℝ) else 0)))^2/2 := by
  obtain ⟨_,hju⟩ := others_not_mem A j u hu
  obtain ⟨_,hjv⟩ := others_not_mem A j v hv
  have hjG : j ∉ ({u,v} : Finset (I n)) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun h => hju h.symm, fun h => hjv h.symm⟩
  have hcard : ({u,v} : Finset (I n)).card = 2 := Finset.card_pair huv
  have hGc : (false : Bool) = false → 2 ≤ ({u,v} : Finset (I n)).card := fun _ => by
    rw [hcard]
  have hsub : ({u,v} : Finset (I n)) ⊆ others A j :=
    insert_subset_iff.mpr ⟨hu, singleton_subset_iff.mpr hv⟩
  have hGA : (({u,v} : Finset (I n)) ∩ others A j).card = 2 := by
    rw [inter_eq_left.mpr hsub, hcard]
  have hGC : ((({u,v} : Finset (I n)) ∩ others C j).card : ℝ) =
      2-((if u ∈ C then (1:ℝ) else 0)+(if v ∈ C then (1:ℝ) else 0)) := by
    rw [inter_comm, ← sum_hit, Finset.sum_pair huv]
    have hu' : hit (others C j) u = 1-(if u ∈ C then (1:ℝ) else 0) := by
      unfold hit
      by_cases h : u ∈ C
      · simp [h, others, hju]
      · simp [h, others, hju]
    have hv' : hit (others C j) v = 1-(if v ∈ C then (1:ℝ) else 0) := by
      unfold hit
      by_cases h : v ∈ C
      · simp [h, others, hjv]
      · simp [h, others, hjv]
    rw [hu', hv']; ring
  have hmA : actualMean A j mu (Sum.inr ({u,v},false)) = 1+(1-mu)*2 := by
    show world A j mu (query {u,v} j false) = _
    rw [actual_query_mean A {u,v} j false hjA hjG hGc mu, hGA]
    norm_num [bit]
  have hmC : actualMean C j nu (Sum.inr ({u,v},false)) =
      1+(1-nu)*(2-((if u ∈ C then (1:ℝ) else 0)+(if v ∈ C then (1:ℝ) else 0))) := by
    show world C j nu (query {u,v} j false) = _
    rw [actual_query_mean C {u,v} j false hjC hjG hGc nu, hGC]
    norm_num [bit]
  rw [information_eq_mean, hmA, hmC]
  ring_nf

/-- EXACT value of the design against a label changing exactly one B coordinate:
the quadratic `C_eta + 2 B_eta x + A_eta x^2` of the handoff, in `x = nu - mu`. -/
theorem design_swap_value (A C : Finset (I n)) (j b : I n) (q mu nu eta cz : ℝ)
    (hq : 3 ≤ q) (hcz : 0 < cz) (hjA : j ∉ A) (hjC : j ∉ C)
    (hB : ((others A j).card : ℝ) = q) (hb : b ∈ others A j) (hbC : b ∈ C)
    (hone : ∀ i ∈ others A j, i ≠ b → i ∉ C) :
    designInfo A C j mu nu eta cz q =
      ((1-eta)*mu^2/(2*q)+eta*(1-mu)^2/(q*cz))
        + 2*(eta*(1-mu)/(q*cz))*(nu-mu)
        + ((1-eta)*(q-1)/(2*q)+eta*(2*q-3)/(q*cz))*(nu-mu)^2 := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (0:ℝ) < q-1 := by linarith
  have hind : ∀ i ∈ others A j,
      (if i ∈ C then (1:ℝ) else 0) = (if i = b then (1:ℝ) else 0) := by
    intro i hi
    by_cases h : i = b
    · subst h; rw [if_pos hbC, if_pos rfl]
    · rw [if_neg (hone i hi h), if_neg h]
  -- scalar half
  have hscal : (∑ i ∈ others A j, information A C j mu nu (.inl i))
      = (mu^2+(q-1)*(nu-mu)^2)/2 := by
    rw [← Finset.add_sum_erase _ _ hb,
      scalar_information_B A C j b hjA hjC mu nu hb, if_pos hbC]
    have herase : ∀ i ∈ (others A j).erase b,
        information A C j mu nu (.inl i) = (nu-mu)^2/2 := by
      intro i hi
      have hib : i ≠ b := (mem_erase.mp hi).1
      have hiB : i ∈ others A j := (mem_erase.mp hi).2
      rw [scalar_information_B A C j i hjA hjC mu nu hiB, if_neg (hone i hiB hib)]
    rw [sum_congr rfl herase, sum_const, nsmul_eq_mul,
      card_erase_real (others A j) b hb q hB]
    ring
  -- pair half
  have hpairval : ∀ u ∈ others A j, ∀ v ∈ others A j, u ≠ v →
      information A C j mu nu (.inr ({u,v},false)) =
      (2*(nu-mu)+(1-nu)*((if u = b then (1:ℝ) else 0)+(if v = b then (1:ℝ) else 0)))^2/2 := by
    intro u hu v hv huv
    rw [pair_information A C j u v hjA hjC mu nu hu hv huv, hind u hu, hind v hv]
  set P1 : ℝ := (2*(nu-mu)+(1-nu))^2/2 with hP1
  set P0 : ℝ := (2*(nu-mu))^2/2 with hP0
  have hinner_b : (∑ v ∈ others A j, if b = v then (0:ℝ)
      else information A C j mu nu (.inr ({b,v},false))) = (q-1)*P1 := by
    have h : ∀ v ∈ others A j, (if b = v then (0:ℝ)
        else information A C j mu nu (.inr ({b,v},false))) = (if b = v then (0:ℝ) else P1) := by
      intro v hv
      by_cases h : b = v
      · simp [h]
      · rw [if_neg h, if_neg h, hpairval b hb v hv h, if_pos rfl, if_neg (fun hc => h hc.symm)]
        rw [hP1]; ring_nf
    rw [sum_congr rfl h, sum_off_const (others A j) b hb P1, hB]
  have hinner_u : ∀ u ∈ (others A j).erase b,
      (∑ v ∈ others A j, if u = v then (0:ℝ)
        else information A C j mu nu (.inr ({u,v},false))) = P1+(q-2)*P0 := by
    intro u hu
    have hub : u ≠ b := (mem_erase.mp hu).1
    have huB : u ∈ others A j := (mem_erase.mp hu).2
    rw [← Finset.add_sum_erase _ _ hb, if_neg (fun hc => hub hc),
      hpairval u huB b hb (fun hc => hub hc), if_neg hub, if_pos rfl]
    have h : ∀ v ∈ (others A j).erase b, (if u = v then (0:ℝ)
        else information A C j mu nu (.inr ({u,v},false))) = (if u = v then (0:ℝ) else P0) := by
      intro v hv
      have hvb : v ≠ b := (mem_erase.mp hv).1
      have hvB : v ∈ others A j := (mem_erase.mp hv).2
      by_cases h : u = v
      · simp [h]
      · rw [if_neg h, if_neg h, hpairval u huB v hvB h, if_neg hub, if_neg hvb]
        rw [hP0]; ring_nf
    rw [sum_congr rfl h, sum_off_const ((others A j).erase b) u hu P0,
      card_erase_real (others A j) b hb q hB]
    rw [hP1]; ring_nf
  have hpair : (∑ u ∈ others A j, ∑ v ∈ others A j,
      if u = v then (0:ℝ) else information A C j mu nu (.inr ({u,v},false)))
      = 2*(q-1)*P1+(q-1)*(q-2)*P0 := by
    rw [← Finset.add_sum_erase _ _ hb, hinner_b, sum_congr rfl hinner_u, sum_const,
      nsmul_eq_mul, card_erase_real (others A j) b hb q hB]
    ring
  unfold designInfo
  rw [hscal, hpair, hP1, hP0]
  field_simp
  ring

/-- A label changing `d` B coordinates collects `(1-eta) d V0` from the scalar
half alone, whatever the nuisance: for small `eta` these are not the bottleneck. -/
theorem design_multi_lower (A C T : Finset (I n)) (j : I n) (q mu nu eta cz d : ℝ)
    (hq : 0 < q) (hcz : 0 < cz) (hq1 : 1 < q) (hjA : j ∉ A) (hjC : j ∉ C)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hTsub : T ⊆ others A j) (hTC : ∀ i ∈ T, i ∈ C) (hTcard : ((T.card : ℝ)) = d) :
    (1-eta)*d*mu^2/(2*q) ≤ designInfo A C j mu nu eta cz q := by
  have hnn : ∀ i ∈ others A j, 0 ≤ information A C j mu nu (.inl i) := by
    intro i hi
    rw [scalar_information_B A C j i hjA hjC mu nu hi]
    split_ifs <;> positivity
  have hTsum : (T.card : ℝ)*(mu^2/2) ≤ ∑ i ∈ T, information A C j mu nu (.inl i) := by
    have h : ∀ i ∈ T, mu^2/2 ≤ information A C j mu nu (.inl i) := by
      intro i hi
      rw [scalar_information_B A C j i hjA hjC mu nu (hTsub hi), if_pos (hTC i hi)]
    calc (T.card : ℝ)*(mu^2/2) = ∑ _i ∈ T, mu^2/2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum h
  have hmain : (T.card : ℝ)*(mu^2/2) ≤ ∑ i ∈ others A j, information A C j mu nu (.inl i) :=
    hTsum.trans (sum_le_sum_of_subset_of_nonneg hTsub (fun i hi _ => hnn i hi))
  have hpairnn : 0 ≤ ∑ u ∈ others A j, ∑ v ∈ others A j,
      (if u = v then (0:ℝ) else information A C j mu nu (.inr ({u,v},false))) := by
    refine sum_nonneg (fun u hu => sum_nonneg (fun v hv => ?_))
    by_cases h : u = v
    · rw [if_pos h]
    · rw [if_neg h, pair_information A C j u v hjA hjC mu nu hu hv h]
      positivity
  have hexp : designInfo A C j mu nu eta cz q
      = (1-eta)/q*(∑ i ∈ others A j, information A C j mu nu (.inl i))
        + eta/(q*(q-1)*cz)*(∑ u ∈ others A j, ∑ v ∈ others A j,
            if u = v then (0:ℝ) else information A C j mu nu (.inr ({u,v},false))) := rfl
  rw [hexp]
  have hcoef : 0 ≤ (1-eta)/q := by
    apply div_nonneg (by linarith) hq.le
  have h2 : 0 ≤ eta/(q*(q-1)*cz)*(∑ u ∈ others A j, ∑ v ∈ others A j,
      (if u = v then (0:ℝ) else information A C j mu nu (.inr ({u,v},false)))) := by
    apply mul_nonneg _ hpairnn
    apply div_nonneg heta0
    have : (0:ℝ) < q*(q-1)*cz := by
      apply mul_pos (mul_pos hq (by linarith)) hcz
    exact this.le
  have h1 : (1-eta)*d*mu^2/(2*q) ≤ (1-eta)/q*(∑ i ∈ others A j, information A C j mu nu (.inl i)) := by
    have := mul_le_mul_of_nonneg_left hmain hcoef
    rw [← hTcard]
    calc (1-eta)*(T.card : ℝ)*mu^2/(2*q) = (1-eta)/q*((T.card : ℝ)*(mu^2/2)) := by
          field_simp
      _ ≤ _ := this
  linarith

/-- Completing the square: the unconstrained profile of the `d = 1` quadratic. -/
theorem quadratic_profile_lower (Cc Bb Aa x : ℝ) (hA : 0 < Aa) :
    Cc-Bb^2/Aa ≤ Cc+2*Bb*x+Aa*x^2 := by
  have h : 0 ≤ Aa*(x+Bb/Aa)^2 := by positivity
  have he : Aa*(x+Bb/Aa)^2 = Aa*x^2+2*Bb*x+Bb^2/Aa := by
    field_simp; ring
  rw [he] at h
  linarith

/-- The design's value against the COMPLETE family of wrong labels and ALL real
nuisances: `V0 + gain(eta)`, with `gain` explicit.  `d = 1` and `d >= 2` exhaust
the family, and no nuisance range restriction is used (the bound holds for every
real `nu`, hence a fortiori on `[0,1]`). -/
theorem design_value_lower (A C : Finset (I n)) (j : I n) (q mu nu eta cz : ℝ)
    (hq : 3 ≤ q) (hcz : 0 < cz) (hmu : 0 < mu) (hmu1 : mu < 1)
    (hbelow : cz ≤ 2*(1-mu)^2/mu^2)
    (hjA : j ∉ A) (hjC : j ∉ C) (hne : C ≠ A) (hcard : C.card = A.card)
    (hB : ((others A j).card : ℝ) = q)
    (heta0 : 0 < eta) (hetab : eta ≤ cz/(cz+2*(1-mu)^2/mu^2)) :
    mu^2/(2*q)
      + (eta*(mu^2/(2*q))*((2*(1-mu)^2/mu^2)/cz-1)
        - 4*eta^2*(1-mu)^2/(q*(q-1)*cz^2))
      ≤ designInfo A C j mu nu eta cz q := by
  classical
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (0:ℝ) < q-1 := by linarith
  set cstar : ℝ := 2*(1-mu)^2/mu^2 with hcstar
  have hcstar0 : 0 < cstar := by rw [hcstar]; positivity
  have hden : 0 < cz+cstar := by linarith
  have heta2 : eta ≤ cz/(cz+cstar) := hetab
  have hmul2 : eta*(cz+cstar) ≤ cz := by
    rw [le_div_iff₀ hden] at heta2; linarith
  have h12 : eta ≤ 1/2 := by
    have h : cz/(cz+cstar) ≤ 1/2 := by
      rw [div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]; linarith
    linarith
  have hetale1 : eta ≤ 1 := by linarith
  set T : Finset (I n) := (others A j).filter (fun i => i ∈ C) with hT
  have hTsub : T ⊆ others A j := filter_subset _ _
  have hTC : ∀ i ∈ T, i ∈ C := by intro i hi; exact (mem_filter.mp hi).2
  obtain ⟨b,hbB,hbC⟩ := wrong_label_contains_B A C j hne hcard hjC
  have hbT : b ∈ T := mem_filter.mpr ⟨hbB,hbC⟩
  set V0 : ℝ := mu^2/(2*q) with hV0
  have hV0pos : 0 < V0 := by rw [hV0]; positivity
  set G : ℝ := eta*V0*(cstar/cz-1)-4*eta^2*(1-mu)^2/(q*(q-1)*cz^2) with hG
  have hGle : G ≤ eta*V0*(cstar/cz-1) := by
    have h : 0 ≤ 4*eta^2*(1-mu)^2/(q*(q-1)*cz^2) := by positivity
    rw [hG]; linarith
  have hTpos : 1 ≤ T.card := card_pos.mpr ⟨b,hbT⟩
  rcases eq_or_lt_of_le hTpos with h1 | h2
  · -- exactly one changed B coordinate: the d = 1 quadratic
    have hTcard : T.card = 1 := h1.symm
    have hone : ∀ i ∈ others A j, i ≠ b → i ∉ C := by
      intro i hi hib hiC
      have hiT : i ∈ T := mem_filter.mpr ⟨hi,hiC⟩
      exact hib (card_le_one.mp (le_of_eq hTcard) i hiT b hbT)
    rw [design_swap_value A C j b q mu nu eta cz hq hcz hjA hjC hB hbB hbC hone]
    set Cc : ℝ := (1-eta)*mu^2/(2*q)+eta*(1-mu)^2/(q*cz) with hCc
    set Bb : ℝ := eta*(1-mu)/(q*cz) with hBb
    set Aa : ℝ := (1-eta)*(q-1)/(2*q)+eta*(2*q-3)/(q*cz) with hAa
    have hpart1 : 0 ≤ (1-eta)*(q-1)/(2*q) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have hpart2 : 0 < eta*(2*q-3)/(q*cz) :=
      div_pos (mul_pos heta0 (by linarith)) (by positivity)
    have hApos : 0 < Aa := by rw [hAa]; linarith
    refine le_trans ?_ (quadratic_profile_lower Cc Bb Aa (nu-mu) hApos)
    have hAlow2 : (q-1)/(4*q) ≤ Aa := by
      have h1 : (q-1)/(4*q) ≤ (1-eta)*(q-1)/(2*q) := by
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 4*q) (by linarith : (0:ℝ) < 2*q)]
        nlinarith [mul_nonneg (mul_pos hq1 hq0).le (by linarith : (0:ℝ) ≤ 1 - 2*eta)]
      rw [hAa]; linarith
    have hBsq : Bb^2/Aa ≤ 4*eta^2*(1-mu)^2/(q*(q-1)*cz^2) := by
      rw [div_le_iff₀ hApos]
      have hX : (0:ℝ) ≤ 4*eta^2*(1-mu)^2/(q*(q-1)*cz^2) := by positivity
      have h1 : 4*eta^2*(1-mu)^2/(q*(q-1)*cz^2)*((q-1)/(4*q)) = Bb^2 := by
        rw [hBb]; field_simp
      calc Bb^2 = 4*eta^2*(1-mu)^2/(q*(q-1)*cz^2)*((q-1)/(4*q)) := h1.symm
        _ ≤ 4*eta^2*(1-mu)^2/(q*(q-1)*cz^2)*Aa := mul_le_mul_of_nonneg_left hAlow2 hX
    have hCcv : Cc = V0+eta*V0*(cstar/cz-1) := by
      rw [hCc, hV0, hcstar]; field_simp; ring
    rw [hG]
    have hfin : V0+eta*V0*(cstar/cz-1)-4*eta^2*(1-mu)^2/(q*(q-1)*cz^2) ≤ Cc-Bb^2/Aa := by
      rw [hCcv]; linarith
    linarith
  · -- two or more changed B coordinates
    have hTcard2 : (2:ℝ) ≤ (T.card : ℝ) := by exact_mod_cast h2
    have hmul := design_multi_lower A C T j q mu nu eta cz (T.card : ℝ) hq0 hcz
      (by linarith) hjA hjC heta0.le hetale1 hTsub hTC rfl
    have hrw : (1-eta)*(T.card : ℝ)*mu^2/(2*q) = (1-eta)*(T.card : ℝ)*V0 := by
      rw [hV0]; field_simp
    rw [hrw] at hmul
    have hkey : eta*(cstar/cz+1) ≤ 1 := by
      have hexp : eta*(cstar/cz+1) = eta*(cstar+cz)/cz := by field_simp
      rw [hexp, div_le_one hcz]; linarith
    have hstep2 : eta*V0*(cstar/cz+1) ≤ V0 := by
      have h := mul_le_mul_of_nonneg_left hkey hV0pos.le
      nlinarith
    have hGbound : G ≤ V0-2*eta*V0 := by
      have hid : eta*V0*(cstar/cz-1) = eta*V0*(cstar/cz+1)-2*eta*V0 := by ring
      rw [hid] at hGle; linarith
    have hfinal : V0+G ≤ (1-eta)*(T.card : ℝ)*V0 := by
      have hnn : 0 ≤ ((T.card : ℝ) - 2)*((1-eta)*V0) :=
        mul_nonneg (by linarith) (mul_nonneg (by linarith) hV0pos.le)
      have hexp2 : ((T.card : ℝ) - 2)*((1-eta)*V0)
          = (1-eta)*(T.card : ℝ)*V0 - (2*V0 - 2*(eta*V0)) := by ring
      have hGb : G ≤ V0 - 2*(eta*V0) := by
        have : V0 - 2*eta*V0 = V0 - 2*(eta*V0) := by ring
        linarith [hGbound, this]
      linarith [hnn, hexp2, hGb]
    linarith

/-- Below the boundary (`cz < cstar`) the gain is STRICTLY positive on an
explicit interval of `eta`: the B-scalar design is strictly suboptimal, so the
charge condition of `joint_mixture_scalar_bound_sharp` is sharp at width two. -/
theorem strict_improvement (q mu cz eta : ℝ)
    (hq : 3 ≤ q) (hcz : 0 < cz) (hmu : 0 < mu) (hmu1 : mu < 1)
    (hbelow : cz < 2*(1-mu)^2/mu^2) (heta0 : 0 < eta)
    (hsmall : eta < (mu^2/(2*q))*((2*(1-mu)^2/mu^2)/cz-1)*(q*(q-1)*cz^2)/(4*(1-mu)^2)) :
    0 < eta*((mu^2/(2*q))*((2*(1-mu)^2/mu^2)/cz-1))-4*eta^2*(1-mu)^2/(q*(q-1)*cz^2) := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (0:ℝ) < q-1 := by linarith
  have hg : 0 < (1-mu)^2 := by positivity
  have hratio : 1 < (2*(1-mu)^2/mu^2)/cz := by
    rw [lt_div_iff₀ hcz]; linarith
  set K : ℝ := (mu^2/(2*q))*((2*(1-mu)^2/mu^2)/cz-1) with hK
  have hKpos : 0 < K := by
    rw [hK]; exact mul_pos (by positivity) (by linarith)
  have hstep : 4*eta^2*(1-mu)^2/(q*(q-1)*cz^2) < eta*K := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < q*(q-1)*cz^2)]
    have hlt := hsmall
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4*(1-mu)^2)] at hlt
    nlinarith [mul_lt_mul_of_pos_left hlt heta0]
  linarith

/-- The quadratic law at the explicit near-optimal `eta`.  Pure algebra: the
maximiser of the proved lower bound `eta*V0*R - 4 eta^2 g2/(q(q-1)cz^2)` is
`eta0 = V0 R q(q-1) cz^2/(8 g2)` and the maximum is `V0^2 R^2 q(q-1) cz^2/(16 g2)`,
quadratic in the distance `R = cstar/cz - 1` to the boundary.  Read with
`V0 = mu^2/(2q)`, `g2 = (1-mu)^2`, `cstar = 2(1-mu)^2/mu^2`. -/
theorem quadratic_gain (q cz V0 R g2 eta0 : ℝ) (hq0 : 0 < q) (hq1 : 0 < q-1)
    (hcz : 0 < cz) (hg : 0 < g2)
    (heta : eta0 = V0*R*(q*(q-1)*cz^2)/(8*g2)) :
    eta0*V0*R-4*eta0^2*g2/(q*(q-1)*cz^2) = V0^2*R^2*(q*(q-1)*cz^2)/(16*g2) := by
  subst heta
  field_simp
  ring

#print axioms sum_off_const
#print axioms card_erase_real
#print axioms scalar_information_B
#print axioms pair_information
#print axioms design_swap_value
#print axioms design_multi_lower
#print axioms quadratic_profile_lower
#print axioms design_value_lower
#print axioms strict_improvement
#print axioms quadratic_gain

end
end CIGAMF.P13.D6WidthTransitionLocal
