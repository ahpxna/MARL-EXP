import «LeanPaperA7SqrtLipV1»
import «LeanPaperA7FreeAccumV1»

/-!
# Paper A7: a measurable oracle with vanishing error, without a box

The ideal learner needs, at every estimate `mu`, a design whose information is within a
vanishing factor of the game value, chosen MEASURABLY in `mu`.  An exact maximiser raises a
measurable-selection problem; a finite grid does not.

* `sqrtJ_le`, `continuous_Jval` -- for an allocation `w`, `sqrt(2 J(w, .))` is 1-Lipschitz in
  the sup norm with no box on the alternatives, so `J(w, .)` is continuous;
* `netSet k` -- the allocations with coordinates in `(1/k) ℕ`; `round_down` -- every allocation
  has a grid point below it up to `1/k` in every coordinate;
* `net_value_ge` -- for every allocation `w`, some grid point has
  `J >= (1 - K/(k beta)) (1 - beta) J(w)` (mix with the uniform design, then round down and use
  `Jval_scale_le`); no box is used;
* `argmaxIdx` -- among finitely many continuous scores, the FIRST maximiser; it is measurable
  (`measurable_argmaxIdx`) and attains the maximum (`argmaxIdx_spec`).
-/

namespace CIGAMF.P13.PaperA7NetOracle

open Finset
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7SqrtLip CIGAMF.P13.PaperA7Accumulation

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## 1. Continuity of the information of a design -/

theorem sqrtJ_le (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w μ μ' : E → ℝ) (hw : IsAlloc w)
    (r : ℝ) (hr : 0 ≤ r) (hclose : ∀ e, |μ' e - μ e| ≤ r) :
    Real.sqrt (2 * Jval Alt w μ') ≤ Real.sqrt (2 * Jval Alt w μ) + r := by
  set j' := Jval Alt w μ'
  have hρ := rho_le_of_alloc w μ μ' hw r hr hclose
  have hall : ∀ ν ∈ Alt, Real.sqrt (2 * j') - r ≤ Real.sqrt (2 * pen w μ ν) := by
    intro ν hν
    have h1 : j' ≤ pen w μ' ν := csInf_le (Jval_bddBelow Alt w μ' hw.1) ⟨ν, hν, rfl⟩
    have h2 : Real.sqrt (2 * j') ≤ Real.sqrt (2 * pen w μ' ν) := Real.sqrt_le_sqrt (by linarith)
    have h3 := sqrt_pen_le w μ μ' ν hw.1
    linarith
  set s := Real.sqrt (2 * j') - r
  rcases le_or_gt s 0 with hs | hs
  · have := Real.sqrt_nonneg (2 * Jval Alt w μ)
    linarith
  · -- square the uniform bound and pass to the infimum
    have hsq : s ^ 2 / 2 ≤ Jval Alt w μ := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨ν, hν, rfl⟩
      have h := hall ν hν
      have hp0 : 0 ≤ pen w μ ν := pen_nonneg w μ ν hw.1
      have : s ^ 2 ≤ (Real.sqrt (2 * pen w μ ν)) ^ 2 := pow_le_pow_left₀ hs.le h 2
      rw [Real.sq_sqrt (by linarith)] at this
      linarith
    have : s ≤ Real.sqrt (2 * Jval Alt w μ) := by
      rw [show s = Real.sqrt (s ^ 2) from (Real.sqrt_sq hs.le).symm]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith

theorem Jval_nonneg' (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w μ : E → ℝ) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ Jval Alt w μ := Jval_nonneg Alt hne w μ hw

/-- **The information of an allocation is continuous in the world.** -/
theorem continuous_Jval (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w : E → ℝ) (hw : IsAlloc w) :
    Continuous fun μ => Jval Alt w μ := by
  have hlip : LipschitzWith 1 fun μ : E → ℝ => Real.sqrt (2 * Jval Alt w μ) := by
    refine LipschitzWith.of_dist_le_mul fun μ μ' => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    have hc : ∀ e, |μ e - μ' e| ≤ dist μ μ' := fun e => by
      rw [← Real.dist_eq]; exact dist_le_pi_dist μ μ' e
    have hc' : ∀ e, |μ' e - μ e| ≤ dist μ μ' := fun e => by
      rw [abs_sub_comm]; exact hc e
    have h1 := sqrtJ_le Alt hne w μ' μ hw (dist μ μ') dist_nonneg hc
    have h2 := sqrtJ_le Alt hne w μ μ' hw (dist μ μ') dist_nonneg hc'
    rw [abs_le]
    constructor <;> linarith
  have hsq : (fun μ => Jval Alt w μ) = fun μ => (Real.sqrt (2 * Jval Alt w μ)) ^ 2 / 2 := by
    funext μ
    rw [Real.sq_sqrt (by have := Jval_nonneg Alt hne w μ hw.1; linarith)]
    ring
  rw [hsq]
  exact (hlip.continuous.pow 2).div_const 2

/-! ## 2. The grid of allocations -/

/-- The allocations with coordinates in `(1/k) ℕ`. -/
noncomputable def netSet (k : ℕ) : Finset (E → ℝ) :=
  (univ.filter fun n : E → Fin (k + 1) => ∑ e, (n e : ℕ) = k).image
    fun n e => ((n e : ℕ) : ℝ) / k

theorem netSet_alloc (k : ℕ) (hk : 0 < k) (w : E → ℝ) (hw : w ∈ netSet k) : IsAlloc w := by
  unfold netSet at hw
  rw [mem_image] at hw
  obtain ⟨n, hn, rfl⟩ := hw
  rw [mem_filter] at hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun e => by positivity, ?_⟩
  rw [← sum_div]
  have : (∑ e, ((n e : ℕ) : ℝ)) = k := by exact_mod_cast hn.2
  rw [this, div_self hkR.ne']

/-- **Every allocation has a grid point below it, up to `1/k`.** -/
theorem round_down [Nonempty E] (k : ℕ) (hk : 0 < k) (w : E → ℝ) (hw : IsAlloc w) :
    ∃ w' ∈ netSet k, ∀ e, w e - 1 / k ≤ w' e := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨e0⟩ := (inferInstance : Nonempty E)
  set n0 : E → ℕ := fun e => ⌊(k : ℝ) * w e⌋₊ with hn0
  have hn0le : ∀ e, (n0 e : ℝ) ≤ k * w e := fun e =>
    Nat.floor_le (mul_nonneg hkR.le (hw.1 e))
  have hsum0 : ∑ e, n0 e ≤ k := by
    have : (∑ e, (n0 e : ℝ)) ≤ k := by
      calc (∑ e, (n0 e : ℝ)) ≤ ∑ e, (k : ℝ) * w e := sum_le_sum fun e _ => hn0le e
        _ = k := by rw [← mul_sum, hw.2, mul_one]
    exact_mod_cast this
  set D := k - ∑ e, n0 e with hD
  set n : E → ℕ := fun e => n0 e + if e = e0 then D else 0 with hn
  have hsumn : ∑ e, n e = k := by
    rw [hn]
    simp only
    rw [sum_add_distrib, sum_ite_eq' univ e0 (fun _ => D), if_pos (mem_univ _), hD]
    omega
  have hnle : ∀ e, n e < k + 1 := by
    intro e
    have := single_le_sum (f := n) (fun e _ => Nat.zero_le _) (mem_univ e)
    omega
  refine ⟨fun e => ((n e : ℕ) : ℝ) / k, ?_, fun e => ?_⟩
  · unfold netSet
    rw [mem_image]
    refine ⟨fun e => ⟨n e, hnle e⟩, ?_, rfl⟩
    rw [mem_filter]
    exact ⟨mem_univ _, hsumn⟩
  · have hfl : (k : ℝ) * w e - 1 < n0 e := by
      have := Nat.lt_floor_add_one ((k : ℝ) * w e)
      linarith
    have hge : (n0 e : ℝ) ≤ n e := by
      have : n0 e ≤ n e := by rw [hn]; simp only; omega
      exact_mod_cast this
    rw [le_div_iff₀ hkR]
    have : (w e - 1 / k) * k = k * w e - 1 := by field_simp
    rw [this]
    linarith

/-- **The grid loses a vanishing factor of any allocation's information.** -/
theorem net_value_ge [Nonempty E] (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (μ : E → ℝ)
    (k : ℕ) (hk : 0 < k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hkβ : (Fintype.card E : ℝ) ≤ k * β) (w : E → ℝ) (hw : IsAlloc w) :
    ∃ w' ∈ netSet k, (1 - (Fintype.card E : ℝ) / (k * β)) * (1 - β) * Jval Alt w μ
      ≤ Jval Alt w' μ := by
  have hK : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  -- mix with the uniform design
  set u : E → ℝ := fun _ => 1 / (Fintype.card E : ℝ) with hu
  have hualloc : IsAlloc u := by
    refine ⟨fun e => by positivity, ?_⟩
    rw [hu]; simp only
    rw [sum_const, card_univ, nsmul_eq_mul]; field_simp
  set wβ : E → ℝ := fun e => (1 - β) * w e + β * u e with hwβ
  have hwβalloc : IsAlloc wβ := by
    refine ⟨fun e => add_nonneg (mul_nonneg (by linarith) (hw.1 e))
      (mul_nonneg hβ0.le (hualloc.1 e)), ?_⟩
    rw [hwβ]; simp only
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hw.2, hualloc.2]; ring
  have hmix := forced_mixture Alt hne w u μ hw.1 hualloc.1 β hβ0.le hβ1
  obtain ⟨w', hw'mem, hw'ge⟩ := round_down k hk wβ hwβalloc
  have hfloor : ∀ e, β / (Fintype.card E : ℝ) ≤ wβ e := by
    intro e
    rw [hwβ]; simp only
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β) (hw.1 e)
    rw [hu]; simp only
    rw [mul_one_div]; linarith
  set c := 1 - (Fintype.card E : ℝ) / (k * β) with hc
  have hc0 : 0 ≤ c := by
    rw [hc, sub_nonneg, div_le_one (by positivity)]; exact hkβ
  have hscale : ∀ e, c * wβ e ≤ w' e := by
    intro e
    have h1 : 1 / (k : ℝ) ≤ (Fintype.card E : ℝ) / (k * β) * wβ e := by
      have := hfloor e
      calc 1 / (k : ℝ) = (Fintype.card E : ℝ) / (k * β) * (β / (Fintype.card E : ℝ)) := by
            field_simp
        _ ≤ (Fintype.card E : ℝ) / (k * β) * wβ e :=
            mul_le_mul_of_nonneg_left this (by positivity)
    have := hw'ge e
    rw [hc]; nlinarith
  have hJw' := CIGAMF.P13.PaperA7FreeAccum.Jval_scale_le Alt hne w' wβ μ hwβalloc.1 c hc0
    hscale
  refine ⟨w', hw'mem, ?_⟩
  calc c * (1 - β) * Jval Alt w μ = c * ((1 - β) * Jval Alt w μ) := by ring
    _ ≤ c * Jval Alt wβ μ := mul_le_mul_of_nonneg_left hmix hc0
    _ ≤ Jval Alt w' μ := hJw'

/-! ## 3. A measurable first maximiser -/

/-- The indices attaining the maximum score. -/
noncomputable def maxSet {n : ℕ} (g : Fin n → (E → ℝ) → ℝ) (μ : E → ℝ) : Finset (Fin n) :=
  univ.filter fun i => ∀ j, g j μ ≤ g i μ

theorem maxSet_nonempty {n : ℕ} (hn : 0 < n) (g : Fin n → (E → ℝ) → ℝ) (μ : E → ℝ) :
    (maxSet g μ).Nonempty := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun i => g i μ) univ_nonempty
  exact ⟨i, mem_filter.mpr ⟨mem_univ _, fun j => hi j (mem_univ _)⟩⟩

/-- **The first maximiser.** -/
noncomputable def argmaxIdx {n : ℕ} (hn : 0 < n) (g : Fin n → (E → ℝ) → ℝ) (μ : E → ℝ) : Fin n :=
  (maxSet g μ).min' (maxSet_nonempty hn g μ)

theorem argmaxIdx_spec {n : ℕ} (hn : 0 < n) (g : Fin n → (E → ℝ) → ℝ) (μ : E → ℝ) (j : Fin n) :
    g j μ ≤ g (argmaxIdx hn g μ) μ := by
  have := (maxSet g μ).min'_mem (maxSet_nonempty hn g μ)
  exact (mem_filter.mp this).2 j

theorem measurable_argmaxIdx {n : ℕ} (hn : 0 < n) (g : Fin n → (E → ℝ) → ℝ)
    (hg : ∀ i, Measurable (g i)) : Measurable (argmaxIdx hn g) := by
  classical
  refine measurable_to_countable' fun i => ?_
  have hmem : ∀ i', MeasurableSet {μ | i' ∈ maxSet g μ} := by
    intro i'
    have : {μ | i' ∈ maxSet g μ} = ⋂ j, {μ | g j μ ≤ g i' μ} := by
      ext μ; simp [maxSet]
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (hg j) (hg i')
  have : argmaxIdx hn g ⁻¹' {i} = {μ | i ∈ maxSet g μ} ∩ ⋂ i' ∈ (univ.filter (· < i)),
      {μ | i' ∉ maxSet g μ} := by
    ext μ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_iInter, mem_filter, mem_univ, true_and]
    constructor
    · intro h
      rw [← h]
      refine ⟨(maxSet g μ).min'_mem _, fun i' hi' hmem' => ?_⟩
      exact absurd ((maxSet g μ).min'_le i' hmem') (not_le.mpr hi')
    · rintro ⟨hi, hlow⟩
      apply le_antisymm
      · exact (maxSet g μ).min'_le i hi
      · refine (maxSet g μ).le_min' _ i fun i' hi' => ?_
        by_contra hlt
        exact hlow i' (not_le.mp hlt) hi'
  rw [this]
  exact (hmem i).inter (MeasurableSet.biInter (Set.to_countable _) fun i' _ => (hmem i').compl)

#print axioms sqrtJ_le
#print axioms continuous_Jval
#print axioms round_down
#print axioms net_value_ge
#print axioms argmaxIdx_spec
#print axioms measurable_argmaxIdx

end CIGAMF.P13.PaperA7NetOracle
