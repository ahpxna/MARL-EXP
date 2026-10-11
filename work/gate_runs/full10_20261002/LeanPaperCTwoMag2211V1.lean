import «LeanPaperCPathMixV1»

/-!
# Paper C: the two-magnitude family with counts `(2,2,1,1)`, at every ratio

`g = (a, a, -a, -a, b, -b)` with `0 < b < a`, `D = ‖g‖₁ = 4a + 2b`, interior budgets
`K = {1,…,5}`.

**Theorem** (`twoMag2211_frontier`). For every `η ≥ 0`,
`V_g(η) = ((a-b)/D) · max((2-η)/3, 2/5)`.
So the frontier has one breakpoint, at `η = 4/5`, the price is `V_g(0)/V_g^free = 5/3`
(`twoMag2211_price`), and the free threshold is `η_free = 4/5` (`twoMag2211_etaFree`), whatever
the ratio `a/b`.

**The certificates.**
* Baselines (`base1` … `base5`): `b, 0, b, 0, b` at every ratio. An odd prefix has an odd count
  difference, so its sum is at least `b` in absolute value (`odd_counts`).
* Dual side, directly on laws over the `720` orders:
  - the band at the first position, on its UPPER side, puts one of the two `b`-items first with
    probability at most `(1+η)/3`. Every other first item costs `a - b` at budget one, so
    `E r₁ ≥ (a-b)(2-η)/3` (`lower_band`);
  - on every order `r₁ + … + r₅ ≥ 2(a-b)` (`per_order`), so the worst budget costs at least a
    fifth of that (`lower_free`). The case split: an `a`-item first or last pays at budget `1`
    or `5`; a `b`-item next to an `a`-item at the front or the back pays at budget `2` or `4`;
    otherwise both `b`-items sit together at one end and budget `3` pays.
* Primal side, on the count flow (`typed_flow_equivalence`):
  - `flow0`: six type sequences with weight `1/6` each, band-exact (`band0`), budget costs
    `(2/3, 1/3, 2/3, 1/3, 2/3)·(a-b)/D` (`obj0`);
  - `flow1`: seven type sequences with weights `1/5, 1/10`, deviation `4/5` (`band1`), every
    budget cost `(2/5)·(a-b)/D` (`obj1`);
  - for `η ≤ 4/5` the mixture `(1-θ) flow0 + θ flow1`, `θ = 5η/4`, meets the band `η` and costs
    at most `(2-η)/3 · (a-b)/D` at every budget. For `η ≥ 4/5`, `flow1` alone.
  Every state these sequences visit costs exactly `|v₊ₐ - v₋ₐ|·(a-b)/D` (`num0`, `num1`), so the
  primal costs are linear in `a - b` at every ratio.
-/

namespace CIGAMF.P13.PaperCTwoMag2211

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCRelabel CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCFlowBandJoin CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFrontier CIGAMF.P13.PaperCFreeBand
open CIGAMF.P13.PaperCPathMix

/-! ## 0. The objects -/

/-- The multiset `(a, a, -a, -a, b, -b)`. -/
noncomputable def g6 (a b : ℝ) : Fin 6 → ℝ := ![a, a, -a, -a, b, -b]

/-- Item types: `0 = +a`, `1 = -a`, `2 = +b`, `3 = -b`. -/
def tyC : Fin 6 → Fin 4 := ![0, 0, 1, 1, 2, 3]

/-- Type weights. -/
noncomputable def wtC (a b : ℝ) : Fin 4 → ℝ := ![a, -a, b, -b]

theorem g6_typed (a b : ℝ) : typedG tyC (wtC a b) = g6 a b := by
  funext i
  fin_cases i <;> rfl

theorem mult0 : mult tyC 0 = 2 := by decide
theorem mult1 : mult tyC 1 = 2 := by decide
theorem mult2 : mult tyC 2 = 1 := by decide
theorem mult3 : mult tyC 3 = 1 := by decide

variable {a b : ℝ}

theorem g6_sum (a b : ℝ) : ∑ i, g6 a b i = 0 := by
  rw [Fin.sum_univ_six]
  simp [g6] <;> ring

theorem abs_g6 (hb : 0 < b) (hab : b < a) (i : Fin 6) :
    |g6 a b i| = if i.val < 4 then a else b := by
  have ha : 0 < a := hb.trans hab
  fin_cases i <;> simp [g6, abs_of_pos ha, abs_of_pos hb]

theorem normMass_g6 (hb : 0 < b) (hab : b < a) : normMass (g6 a b) = 4 * a + 2 * b := by
  have ha : 0 < a := hb.trans hab
  unfold normMass
  rw [Fin.sum_univ_six]
  simp [g6, abs_of_pos ha, abs_of_pos hb] <;> ring

/-! ## 1. Baselines -/

theorem sum_typed {d m : ℕ} (ty : Fin m → Fin d) (w : Fin d → ℝ) (S : Finset (Fin m)) :
    ∑ i ∈ S, typedG ty w i = ∑ τ, w τ * ((S.filter fun i => ty i = τ).card : ℝ) := by
  rw [← Finset.sum_fiberwise S ty (typedG ty w)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have : ∀ i ∈ S.filter (fun i => ty i = τ), typedG ty w i = w τ := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    unfold typedG; rw [hi.2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Baselines are minima over count vectors.** -/
theorem baseline_ge_counts {d m : ℕ} (ty : Fin m → Fin d) (w : Fin d → ℝ) (k : Fin (m + 1))
    (L : ℝ)
    (h : ∀ u : Fin d → ℕ, (∀ τ, u τ ≤ mult ty τ) → ∑ τ, u τ = k.val →
      L ≤ |∑ τ, w τ * (u τ : ℝ)|) :
    L ≤ trueBaseline (typedG ty w) k := by
  unfold trueBaseline baseline
  refine Finset.le_inf' _ _ fun S hS => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [sum_typed]
  refine h (fun τ => (S.filter fun i => ty i = τ).card) (fun τ => ?_) ?_
  · unfold mult
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))
  · rw [← hS]
    exact (Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (ty i))).symm

theorem baseline_le_set (g : Fin 6 → ℝ) (k : Fin 7) (S : Finset (Fin 6)) (hS : S.card = k.val) :
    trueBaseline g k ≤ |∑ i ∈ S, g i| := by
  unfold trueBaseline baseline
  exact Finset.inf'_le _ (by simp [hS])

theorem sum_wtC (u : Fin 4 → ℕ) :
    ∑ τ, wtC a b τ * (u τ : ℝ) = a * ((u 0 : ℝ) - u 1) + b * ((u 2 : ℝ) - u 3) := by
  simp [wtC, Fin.sum_univ_four] <;> ring

/-- An odd prefix has an odd count difference, so its sum is at least `b`. -/
theorem odd_counts (hb : 0 < b) (hab : b < a) (x0 x1 x2 x3 : ℕ) (h0 : x0 ≤ 2) (h1 : x1 ≤ 2)
    (h2 : x2 ≤ 1) (h3 : x3 ≤ 1) (hp : (x0 + x1 + x2 + x3) % 2 = 1) :
    b ≤ |a * ((x0 : ℝ) - x1) + b * ((x2 : ℝ) - x3)| := by
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    first
    | omega
    | (rw [le_abs]; push_cast; first | (left; linarith) | (right; linarith))

theorem odd_ge (hb : 0 < b) (hab : b < a) (k : Fin 7) (hk : k.val % 2 = 1) :
    b ≤ trueBaseline (g6 a b) k := by
  rw [← g6_typed]
  refine baseline_ge_counts tyC (wtC a b) k b fun u hu hs => ?_
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  have h3 := hu 3
  rw [mult0] at h0
  rw [mult1] at h1
  rw [mult2] at h2
  rw [mult3] at h3
  rw [Fin.sum_univ_four] at hs
  rw [sum_wtC]
  exact odd_counts hb hab (u 0) (u 1) (u 2) (u 3) h0 h1 h2 h3 (by rw [hs]; exact hk)

theorem base1 (hb : 0 < b) (hab : b < a) : trueBaseline (g6 a b) 1 = b := by
  apply le_antisymm
  · refine (baseline_le_set (g6 a b) 1 {4} (by decide)).trans (le_of_eq ?_)
    simp [g6, abs_of_pos hb]
  · exact odd_ge hb hab 1 (by decide)

theorem base2 (hb : 0 < b) (hab : b < a) : trueBaseline (g6 a b) 2 = 0 := by
  apply le_antisymm
  · refine (baseline_le_set (g6 a b) 2 {0, 2} (by decide)).trans (le_of_eq ?_)
    simp [g6]
  · exact baseline_nonneg _ _

theorem base3 (hb : 0 < b) (hab : b < a) : trueBaseline (g6 a b) 3 = b := by
  apply le_antisymm
  · refine (baseline_le_set (g6 a b) 3 {0, 2, 4} (by decide)).trans (le_of_eq ?_)
    simp [g6, Finset.sum_insert, abs_of_pos hb]
  · exact odd_ge hb hab 3 (by decide)

theorem base4 (hb : 0 < b) (hab : b < a) : trueBaseline (g6 a b) 4 = 0 := by
  apply le_antisymm
  · refine (baseline_le_set (g6 a b) 4 {0, 2, 4, 5} (by decide)).trans (le_of_eq ?_)
    simp [g6, Finset.sum_insert]
  · exact baseline_nonneg _ _

theorem base5 (hb : 0 < b) (hab : b < a) : trueBaseline (g6 a b) 5 = b := by
  apply le_antisymm
  · refine (baseline_le_set (g6 a b) 5 {0, 1, 2, 3, 4} (by decide)).trans (le_of_eq ?_)
    simp [g6, Finset.sum_insert, abs_of_pos hb]
  · exact odd_ge hb hab 5 (by decide)

/-! ## 2. Prefix sums of an order -/

theorem prefix_sum6 (g : Fin 6 → ℝ) (σ : Equiv.Perm (Fin 6)) (k : Fin 7) :
    ∑ i ∈ prefixSet σ k, g i = ∑ j : Fin 6, if j.val < k.val then g (σ j) else 0 := by
  unfold prefixSet
  rw [Finset.sum_filter,
    ← Equiv.sum_comp σ (fun i => if ((σ.symm i : Fin 6) : ℕ) < k.val then g i else 0)]
  simp only [Equiv.symm_apply_apply]

theorem tot (σ : Equiv.Perm (Fin 6)) :
    g6 a b (σ 0) + g6 a b (σ 1) + g6 a b (σ 2) + g6 a b (σ 3) + g6 a b (σ 4) + g6 a b (σ 5)
      = 0 := by
  have h := Equiv.sum_comp σ (g6 a b)
  rw [g6_sum, Fin.sum_univ_six] at h
  exact h

theorem S1 (σ : Equiv.Perm (Fin 6)) : ∑ i ∈ prefixSet σ 1, g6 a b i = g6 a b (σ 0) := by
  rw [prefix_sum6, Fin.sum_univ_six]; simp

theorem S2 (σ : Equiv.Perm (Fin 6)) :
    ∑ i ∈ prefixSet σ 2, g6 a b i = g6 a b (σ 0) + g6 a b (σ 1) := by
  rw [prefix_sum6, Fin.sum_univ_six]; simp

theorem S3 (σ : Equiv.Perm (Fin 6)) :
    ∑ i ∈ prefixSet σ 3, g6 a b i = g6 a b (σ 0) + g6 a b (σ 1) + g6 a b (σ 2) := by
  rw [prefix_sum6, Fin.sum_univ_six]; simp

theorem S4 (σ : Equiv.Perm (Fin 6)) :
    ∑ i ∈ prefixSet σ 4, g6 a b i = -(g6 a b (σ 4) + g6 a b (σ 5)) := by
  rw [prefix_sum6, Fin.sum_univ_six]
  have h := tot (a := a) (b := b) σ
  simp
  linarith

theorem S5 (σ : Equiv.Perm (Fin 6)) : ∑ i ∈ prefixSet σ 5, g6 a b i = -g6 a b (σ 5) := by
  rw [prefix_sum6, Fin.sum_univ_six]
  have h := tot (a := a) (b := b) σ
  simp
  linarith

theorem raw1 (hb : 0 < b) (hab : b < a) (σ : Equiv.Perm (Fin 6)) :
    rawRegret (g6 a b) σ 1 = |g6 a b (σ 0)| - b := by
  unfold rawRegret; rw [S1, base1 hb hab]

theorem raw2 (hb : 0 < b) (hab : b < a) (σ : Equiv.Perm (Fin 6)) :
    rawRegret (g6 a b) σ 2 = |g6 a b (σ 0) + g6 a b (σ 1)| := by
  unfold rawRegret; rw [S2, base2 hb hab, sub_zero]

theorem raw3 (hb : 0 < b) (hab : b < a) (σ : Equiv.Perm (Fin 6)) :
    rawRegret (g6 a b) σ 3 = |g6 a b (σ 0) + g6 a b (σ 1) + g6 a b (σ 2)| - b := by
  unfold rawRegret; rw [S3, base3 hb hab]

theorem raw4 (hb : 0 < b) (hab : b < a) (σ : Equiv.Perm (Fin 6)) :
    rawRegret (g6 a b) σ 4 = |g6 a b (σ 4) + g6 a b (σ 5)| := by
  unfold rawRegret; rw [S4, base4 hb hab, sub_zero, abs_neg]

theorem raw5 (hb : 0 < b) (hab : b < a) (σ : Equiv.Perm (Fin 6)) :
    rawRegret (g6 a b) σ 5 = |g6 a b (σ 5)| - b := by
  unfold rawRegret; rw [S5, base5 hb hab, abs_neg]

/-! ## 3. The dual side -/

/-- An `a`-item next to a `b`-item. -/
theorem mixed_ge (hb : 0 < b) (hab : b < a) (i j : Fin 6) (hi : i.val < 4) (hj : ¬ j.val < 4) :
    a - b ≤ |g6 a b i + g6 a b j| := by
  have e1 : |g6 a b i| = a := by rw [abs_g6 hb hab, if_pos hi]
  have e2 : |g6 a b j| = b := by rw [abs_g6 hb hab, if_neg hj]
  have := abs_sub_abs_le_abs_sub (g6 a b i) (-g6 a b j)
  rw [abs_neg, sub_neg_eq_add, e1, e2] at this
  exact this

/-- The two `b`-items cancel. -/
theorem pair_zero (i j : Fin 6) (hi : ¬ i.val < 4) (hj : ¬ j.val < 4) (hij : i ≠ j) :
    g6 a b i + g6 a b j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [g6]

/-- **Every order pays `2(a - b)` over the five budgets.** -/
theorem per_order (hb : 0 < b) (hab : b < a) (σ : Equiv.Perm (Fin 6)) :
    2 * (a - b) ≤ rawRegret (g6 a b) σ 1 + rawRegret (g6 a b) σ 2 + rawRegret (g6 a b) σ 3
      + rawRegret (g6 a b) σ 4 + rawRegret (g6 a b) σ 5 := by
  have n1 := (raw_bounds (g6 a b) σ 1).1
  have n2 := (raw_bounds (g6 a b) σ 2).1
  have n3 := (raw_bounds (g6 a b) σ 3).1
  have n4 := (raw_bounds (g6 a b) σ 4).1
  have n5 := (raw_bounds (g6 a b) σ 5).1
  rw [raw1 hb hab] at n1 ⊢
  rw [raw2 hb hab] at n2 ⊢
  rw [raw3 hb hab] at n3 ⊢
  rw [raw4 hb hab] at n4 ⊢
  rw [raw5 hb hab] at n5 ⊢
  have hv : ∀ i j : Fin 6, i ≠ j → (σ i).val ≠ (σ j).val :=
    fun i j hij h => hij (σ.injective (Fin.ext h))
  have v01 := hv 0 1 (by decide)
  have v02 := hv 0 2 (by decide)
  have v05 := hv 0 5 (by decide)
  have v04 := hv 0 4 (by decide)
  have v12 := hv 1 2 (by decide)
  have v15 := hv 1 5 (by decide)
  have v34 := hv 3 4 (by decide)
  have v35 := hv 3 5 (by decide)
  have v45 := hv 4 5 (by decide)
  have l0 := (σ 0).isLt
  have l1 := (σ 1).isLt
  have l2 := (σ 2).isLt
  have l3 := (σ 3).isLt
  have l4 := (σ 4).isLt
  have l5 := (σ 5).isLt
  have htot := tot (a := a) (b := b) σ
  by_cases hA0 : (σ 0).val < 4 <;> by_cases hA5 : (σ 5).val < 4
  · -- an `a`-item first and last
    have e0 : |g6 a b (σ 0)| = a := by rw [abs_g6 hb hab, if_pos hA0]
    have e5 : |g6 a b (σ 5)| = a := by rw [abs_g6 hb hab, if_pos hA5]
    linarith
  · -- an `a`-item first, a `b`-item last
    have e0 : |g6 a b (σ 0)| = a := by rw [abs_g6 hb hab, if_pos hA0]
    by_cases hA4 : (σ 4).val < 4
    · have := mixed_ge hb hab (σ 4) (σ 5) hA4 hA5
      linarith
    · have hz := pair_zero (a := a) (b := b) (σ 4) (σ 5) hA4 hA5 (σ.injective.ne (by decide))
      have hA3 : (σ 3).val < 4 := by omega
      have e3 : |g6 a b (σ 0) + g6 a b (σ 1) + g6 a b (σ 2)| = a := by
        rw [show g6 a b (σ 0) + g6 a b (σ 1) + g6 a b (σ 2) = -g6 a b (σ 3) by linarith,
          abs_neg, abs_g6 hb hab, if_pos hA3]
      linarith
  · -- a `b`-item first, an `a`-item last
    have e5 : |g6 a b (σ 5)| = a := by rw [abs_g6 hb hab, if_pos hA5]
    by_cases hA1 : (σ 1).val < 4
    · have := mixed_ge hb hab (σ 1) (σ 0) hA1 hA0
      rw [add_comm] at this
      linarith
    · have hz := pair_zero (a := a) (b := b) (σ 0) (σ 1) hA0 hA1 (σ.injective.ne (by decide))
      have hA2 : (σ 2).val < 4 := by omega
      have e3 : |g6 a b (σ 0) + g6 a b (σ 1) + g6 a b (σ 2)| = a := by
        rw [hz, zero_add, abs_g6 hb hab, if_pos hA2]
      linarith
  · -- `b`-items first and last
    have hA1 : (σ 1).val < 4 := by omega
    have hA4 : (σ 4).val < 4 := by omega
    have h2 := mixed_ge hb hab (σ 1) (σ 0) hA1 hA0
    have h4 := mixed_ge hb hab (σ 4) (σ 5) hA4 hA5
    rw [add_comm] at h2
    linarith

/-- The interior budgets. -/
def K5 : Finset (Fin 7) := {1, 2, 3, 4, 5}

theorem K5_ne : K5.Nonempty := ⟨1, by simp [K5]⟩

theorem obj_ge (P : Equiv.Perm (Fin 6) → ℝ) (k : Fin 7) (hk : k ∈ K5) :
    ∑ σ, P σ * normalizedRegret (g6 a b) σ k ≤ trueObjective (g6 a b) P K5 K5_ne :=
  Finset.le_sup' (f := fun k => ∑ σ, P σ * normalizedRegret (g6 a b) σ k) hk

theorem marg_one (P : Equiv.Perm (Fin 6) → ℝ) (i : Fin 6) :
    marg P 1 i = ∑ σ, P σ * (if σ 0 = i then 1 else 0) := by
  unfold marg inPrefixInd
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  by_cases h : σ 0 = i
  · rw [if_pos h, if_pos]; rw [← h]; simp
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    have : σ.symm i = 0 := Fin.ext (by simpa using h')
    rw [← this, Equiv.apply_symm_apply]

/-- **The band's upper side on the two `b`-items.** -/
theorem lower_band (hb : 0 < b) (hab : b < a) (η : ℝ) (P : Equiv.Perm (Fin 6) → ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin 6) → _) η) :
    (a - b) / (4 * a + 2 * b) * ((2 - η) / 3) ≤ trueObjective (g6 a b) P K5 K5_ne := by
  obtain ⟨hnn, hsum, hband⟩ := hP
  refine le_trans ?_ (obj_ge P 1 (by simp [K5]))
  have hD : 0 < 4 * a + 2 * b := by linarith
  have hm : ∀ i : Fin 6, marg P 1 i ≤ (1 + η) / 6 := by
    intro i
    have h := hband 1 (by norm_num) i
    have : |marg P 1 i - 1 / 6| ≤ η / 6 := by simpa [marg] using h
    rw [abs_le] at this
    linarith
  have hsplit : ∀ σ : Equiv.Perm (Fin 6), P σ * normalizedRegret (g6 a b) σ 1
      = (a - b) / (4 * a + 2 * b) * (P σ - P σ * (if σ 0 = 4 then 1 else 0)
        - P σ * (if σ 0 = 5 then 1 else 0)) := by
    intro σ
    unfold normalizedRegret
    rw [raw1 hb hab, normMass_g6 hb hab, abs_g6 hb hab]
    by_cases h4 : σ 0 = 4
    · rw [if_neg (by rw [h4]; decide), if_pos h4, if_neg (by rw [h4]; decide)]; ring
    by_cases h5 : σ 0 = 5
    · rw [if_neg (by rw [h5]; decide), if_neg h4, if_pos h5]; ring
    · have : (σ 0).val < 4 := by
        have := (σ 0).isLt
        have h4' : (σ 0).val ≠ 4 := fun h => h4 (Fin.ext h)
        have h5' : (σ 0).val ≠ 5 := fun h => h5 (Fin.ext h)
        omega
      rw [if_pos this, if_neg h4, if_neg h5]; ring
  rw [Finset.sum_congr rfl fun σ _ => hsplit σ, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← marg_one, ← marg_one, hsum]
  have := hm 4
  have := hm 5
  have hc : 0 ≤ (a - b) / (4 * a + 2 * b) := div_nonneg (by linarith) hD.le
  nlinarith

/-- **The free lower bound.** -/
theorem lower_free (hb : 0 < b) (hab : b < a) (P : Equiv.Perm (Fin 6) → ℝ)
    (hnn : ∀ σ, 0 ≤ P σ) (hsum : ∑ σ, P σ = 1) :
    (a - b) / (4 * a + 2 * b) * (2 / 5) ≤ trueObjective (g6 a b) P K5 K5_ne := by
  have hD : 0 < 4 * a + 2 * b := by linarith
  have h1 := obj_ge (a := a) (b := b) P 1 (by simp [K5])
  have h2 := obj_ge (a := a) (b := b) P 2 (by simp [K5])
  have h3 := obj_ge (a := a) (b := b) P 3 (by simp [K5])
  have h4 := obj_ge (a := a) (b := b) P 4 (by simp [K5])
  have h5 := obj_ge (a := a) (b := b) P 5 (by simp [K5])
  have hsum5 : 2 * ((a - b) / (4 * a + 2 * b)) ≤ ∑ σ, P σ * normalizedRegret (g6 a b) σ 1
      + ∑ σ, P σ * normalizedRegret (g6 a b) σ 2 + ∑ σ, P σ * normalizedRegret (g6 a b) σ 3
      + ∑ σ, P σ * normalizedRegret (g6 a b) σ 4 + ∑ σ, P σ * normalizedRegret (g6 a b) σ 5 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    calc 2 * ((a - b) / (4 * a + 2 * b)) = ∑ σ, P σ * (2 * ((a - b) / (4 * a + 2 * b))) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun σ _ => by
          unfold normalizedRegret
          rw [normMass_g6 hb hab]
          have hp := per_order hb hab σ
          have : 2 * ((a - b) / (4 * a + 2 * b)) ≤ rawRegret (g6 a b) σ 1 / (4 * a + 2 * b)
              + rawRegret (g6 a b) σ 2 / (4 * a + 2 * b) + rawRegret (g6 a b) σ 3 / (4 * a + 2 * b)
              + rawRegret (g6 a b) σ 4 / (4 * a + 2 * b)
              + rawRegret (g6 a b) σ 5 / (4 * a + 2 * b) := by
            rw [← add_div, ← add_div, ← add_div, ← add_div, ← mul_div_assoc]
            exact div_le_div_of_nonneg_right hp hD.le
          have := hnn σ
          nlinarith
  linarith

/-! ## 4. The primal side: two mixtures of type sequences -/

/-- A flow's budget vector bounds the value. -/
theorem value_le_flow {d m : ℕ} [NeZero m] (ty : Fin m → Fin d) (w : Fin d → ℝ)
    (hg : 0 < normMass (typedG ty w)) (η : ℝ) (K : Finset (Fin (m + 1))) (hK : K.Nonempty)
    (F : LayeredFlow (CState d m)) (hF : CountFeasibleH ty F) (hB : FlowBand ty F η) :
    trueValue (typedG ty w) η K hK ≤ K.sup' hK (flowObj (typedCost ty w) F) := by
  obtain ⟨P, hP, hPy⟩ := (Set.ext_iff.mp (typed_flow_equivalence ty w η)
    (flowObj (typedCost ty w) F)).mpr ⟨F, hF, hB, rfl⟩
  unfold trueValue
  refine (csInf_le (trueValue_bddBelow _ hg η K hK) ⟨P, hP, rfl⟩).trans (le_of_eq ?_)
  show K.sup' hK (fun k => ∑ σ, P σ * normalizedRegret (typedG ty w) σ k) = _
  rw [hPy]

theorem sum_wtC_state (v : CState 4 6) :
    ∑ τ, wtC a b τ * (((v τ : Fin 7) : ℕ) : ℝ)
      = a * (((v 0 : ℕ) : ℝ) - (v 1 : ℕ)) + b * (((v 2 : ℕ) : ℝ) - (v 3 : ℕ)) := by
  simp [wtC, Fin.sum_univ_four] <;> ring

/-- **The cost of a count state.** -/
theorem cost_formula (hb : 0 < b) (hab : b < a) (k : Fin 7) (v : CState 4 6) :
    typedCost tyC (wtC a b) k v
      = (|a * (((v 0 : ℕ) : ℝ) - (v 1 : ℕ)) + b * (((v 2 : ℕ) : ℝ) - (v 3 : ℕ))|
          - trueBaseline (g6 a b) k) / (4 * a + 2 * b) := by
  unfold typedCost
  rw [sum_wtC_state, g6_typed, normMass_g6 hb hab]

/-! ### The zero-band law: six sequences, weight `1/6` each -/

/-- `AaaABb, AaBabA, aAbBAa, aBAbaA, BbaAAa, bAAaaB` (`A = +a`, `a = -a`, `B = +b`, `b = -b`). -/
def seq0 : Fin 6 → Fin 6 → Fin 4 :=
  ![![0, 1, 1, 0, 2, 3],
    ![0, 1, 2, 1, 3, 0],
    ![1, 0, 3, 2, 0, 1],
    ![1, 2, 0, 3, 1, 0],
    ![2, 3, 1, 0, 0, 1],
    ![3, 0, 0, 1, 1, 2]]

/-- The prefix counts of `seq0`. -/
def tab0 : Fin 6 → Fin 7 → Fin 4 → ℕ :=
  ![![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0], ![2, 2, 1, 0], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 1, 0], ![1, 2, 1, 0], ![1, 2, 1, 1], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 1], ![2, 1, 1, 1], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 1], ![1, 2, 1, 1], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![2, 1, 1, 1], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 1], ![2, 0, 0, 1], ![2, 1, 0, 1], ![2, 2, 0, 1], ![2, 2, 1, 1]]]

/-- The cost multiples `|v₊ₐ - v₋ₐ|` along `seq0`. -/
noncomputable def kap0 : Fin 6 → Fin 7 → ℝ :=
  ![![0, 1, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 1, 1, 0],
    ![0, 1, 0, 0, 0, 1, 0],
    ![0, 1, 1, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 2, 1, 0, 0]]

noncomputable def wgt0 : Fin 6 → ℝ := fun _ => 1 / 6

theorem wgt0_nonneg : ∀ j, 0 ≤ wgt0 j := fun _ => by unfold wgt0; norm_num

theorem wgt0_sum : ∑ j, wgt0 j = 1 := by
  simp [wgt0, Fin.sum_univ_six] <;> norm_num

set_option maxRecDepth 20000 in
theorem seq0_mult : ∀ j τ, mult (seq0 j) τ = mult tyC τ := by decide

set_option maxRecDepth 20000 in
theorem tab0_spec : ∀ j : Fin 6, ∀ k : Fin 7, ∀ τ : Fin 4,
    ((stC (seq0 j) k τ : Fin 7) : ℕ) = tab0 j k τ := by decide

/-- The zero-band flow. -/
noncomputable def flow0 : LayeredFlow (CState 4 6) := mixFlow seq0 wgt0 wgt0_nonneg

theorem feas0 : CountFeasibleH tyC flow0 :=
  mixFlow_feasible tyC seq0 wgt0 wgt0_nonneg wgt0_sum seq0_mult

theorem num0 (hb : 0 < b) (hab : b < a) (j : Fin 6) (k : Fin 7) (hk : k ∈ K5) :
    |a * ((tab0 j k 0 : ℝ) - (tab0 j k 1 : ℝ)) + b * ((tab0 j k 2 : ℝ) - (tab0 j k 3 : ℝ))|
      - trueBaseline (g6 a b) k = kap0 j k * (a - b) := by
  have ha : 0 < a := hb.trans hab
  simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    simp only [base1 hb hab, base2 hb hab, base3 hb hab, base4 hb hab, base5 hb hab] <;>
    fin_cases j <;> simp [tab0, kap0] <;>
    first
    | ring1
    | linarith
    | (rw [abs_of_nonneg (by linarith)]; ring1)
    | (rw [abs_of_nonpos (by linarith)]; ring1)

theorem obj0 (hb : 0 < b) (hab : b < a) (k : Fin 7) (hk : k ∈ K5) :
    flowObj (typedCost tyC (wtC a b)) flow0 k
      = (∑ j, wgt0 j * kap0 j k) * ((a - b) / (4 * a + 2 * b)) := by
  unfold flow0
  rw [mixFlow_obj, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cost_formula hb hab, tab0_spec, tab0_spec, tab0_spec, tab0_spec, num0 hb hab j k hk]
  ring

theorem obj0_le (hb : 0 < b) (hab : b < a) (k : Fin 7) (hk : k ∈ K5) :
    flowObj (typedCost tyC (wtC a b)) flow0 k ≤ 2 / 3 * ((a - b) / (4 * a + 2 * b)) := by
  have hD : 0 < 4 * a + 2 * b := by linarith
  have hc0 : 0 ≤ (a - b) / (4 * a + 2 * b) := div_nonneg (by linarith) hD.le
  rw [obj0 hb hab k hk]
  refine mul_le_mul_of_nonneg_right ?_ hc0
  simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [Fin.sum_univ_six, wgt0, kap0] <;> norm_num

theorem band0 : FlowBand tyC flow0 0 := by
  intro k τ _
  unfold flow0
  rw [mixFlow_mean]
  simp only [tab0_spec]
  rw [abs_le]
  fin_cases k <;> fin_cases τ <;> simp [Fin.sum_univ_six, tab0, wgt0, mult0, mult1, mult2, mult3] <;>
    norm_num

/-! ### The free law: seven sequences, deviation `4/5` -/

/-- `AabAaB, aAaABb, aAaAbB, BaAaAb, BbaAaA, bAaBAa, bBAaaA`. -/
def seq1 : Fin 7 → Fin 6 → Fin 4 :=
  ![![0, 1, 3, 0, 1, 2],
    ![1, 0, 1, 0, 2, 3],
    ![1, 0, 1, 0, 3, 2],
    ![2, 1, 0, 1, 0, 3],
    ![2, 3, 1, 0, 1, 0],
    ![3, 0, 1, 2, 0, 1],
    ![3, 2, 0, 1, 1, 0]]

/-- The prefix counts of `seq1`. -/
def tab1 : Fin 7 → Fin 7 → Fin 4 → ℕ :=
  ![![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 1], ![2, 1, 0, 1], ![2, 2, 0, 1], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0], ![2, 2, 1, 0], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0], ![2, 2, 0, 1], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 2, 1, 0], ![2, 2, 1, 0], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 2, 1, 1], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 1], ![1, 1, 0, 1], ![1, 1, 1, 1], ![2, 1, 1, 1], ![2, 2, 1, 1]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![1, 0, 1, 1], ![1, 1, 1, 1], ![1, 2, 1, 1], ![2, 2, 1, 1]]]

/-- The cost multiples along `seq1`. -/
noncomputable def kap1 : Fin 7 → Fin 7 → ℝ :=
  ![![0, 1, 0, 0, 1, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 0, 0, 1, 0],
    ![0, 0, 0, 1, 0, 1, 0]]

noncomputable def wgt1 : Fin 7 → ℝ := ![1 / 5, 1 / 10, 1 / 10, 1 / 5, 1 / 10, 1 / 5, 1 / 10]

theorem wgt1_nonneg : ∀ j, 0 ≤ wgt1 j := by
  intro j; fin_cases j <;> simp [wgt1] <;> norm_num

theorem wgt1_sum : ∑ j, wgt1 j = 1 := by
  simp [wgt1, Fin.sum_univ_seven] <;> norm_num

set_option maxRecDepth 20000 in
theorem seq1_mult : ∀ j τ, mult (seq1 j) τ = mult tyC τ := by decide

set_option maxRecDepth 20000 in
theorem tab1_spec : ∀ j : Fin 7, ∀ k : Fin 7, ∀ τ : Fin 4,
    ((stC (seq1 j) k τ : Fin 7) : ℕ) = tab1 j k τ := by decide

/-- The free flow. -/
noncomputable def flow1 : LayeredFlow (CState 4 6) := mixFlow seq1 wgt1 wgt1_nonneg

theorem feas1 : CountFeasibleH tyC flow1 :=
  mixFlow_feasible tyC seq1 wgt1 wgt1_nonneg wgt1_sum seq1_mult

theorem num1 (hb : 0 < b) (hab : b < a) (j : Fin 7) (k : Fin 7) (hk : k ∈ K5) :
    |a * ((tab1 j k 0 : ℝ) - (tab1 j k 1 : ℝ)) + b * ((tab1 j k 2 : ℝ) - (tab1 j k 3 : ℝ))|
      - trueBaseline (g6 a b) k = kap1 j k * (a - b) := by
  have ha : 0 < a := hb.trans hab
  simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    simp only [base1 hb hab, base2 hb hab, base3 hb hab, base4 hb hab, base5 hb hab] <;>
    fin_cases j <;> simp [tab1, kap1] <;>
    first
    | ring1
    | linarith
    | (rw [abs_of_nonneg (by linarith)]; ring1)
    | (rw [abs_of_nonpos (by linarith)]; ring1)

theorem obj1 (hb : 0 < b) (hab : b < a) (k : Fin 7) (hk : k ∈ K5) :
    flowObj (typedCost tyC (wtC a b)) flow1 k
      = (∑ j, wgt1 j * kap1 j k) * ((a - b) / (4 * a + 2 * b)) := by
  unfold flow1
  rw [mixFlow_obj, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cost_formula hb hab, tab1_spec, tab1_spec, tab1_spec, tab1_spec, num1 hb hab j k hk]
  ring

theorem obj1_le (hb : 0 < b) (hab : b < a) (k : Fin 7) (hk : k ∈ K5) :
    flowObj (typedCost tyC (wtC a b)) flow1 k ≤ 2 / 5 * ((a - b) / (4 * a + 2 * b)) := by
  have hD : 0 < 4 * a + 2 * b := by linarith
  have hc0 : 0 ≤ (a - b) / (4 * a + 2 * b) := div_nonneg (by linarith) hD.le
  rw [obj1 hb hab k hk]
  refine mul_le_mul_of_nonneg_right ?_ hc0
  simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    simp [Fin.sum_univ_seven, wgt1, kap1] <;> norm_num

theorem band1 : FlowBand tyC flow1 (4 / 5) := by
  intro k τ _
  unfold flow1
  rw [mixFlow_mean]
  simp only [tab1_spec]
  rw [abs_le]
  fin_cases k <;> fin_cases τ <;>
    simp [Fin.sum_univ_seven, tab1, wgt1, mult0, mult1, mult2, mult3] <;> norm_num

/-! ## 5. The frontier -/

theorem normMass_typed_pos (hb : 0 < b) (hab : b < a) : 0 < normMass (typedG tyC (wtC a b)) := by
  rw [g6_typed, normMass_g6 hb hab]; linarith

/-- **The frontier of `(a, a, -a, -a, b, -b)`, at every ratio.** -/
theorem twoMag2211_frontier (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) :
    trueValue (g6 a b) η K5 K5_ne = (a - b) / (4 * a + 2 * b) * max ((2 - η) / 3) (2 / 5) := by
  have hD : 0 < 4 * a + 2 * b := by linarith
  have hc0 : 0 ≤ (a - b) / (4 * a + 2 * b) := div_nonneg (by linarith) hD.le
  apply le_antisymm
  · rw [← g6_typed]
    rcases le_or_gt η (4 / 5) with hle | hgt
    · have hθ0 : 0 ≤ 5 * η / 4 := by positivity
      have hθ1 : 5 * η / 4 ≤ 1 := by linarith
      have hF := mixTwo_feasible tyC (5 * η / 4) hθ0 hθ1 flow0 flow1 feas0 feas1
      have hB := mixTwo_band tyC (5 * η / 4) hθ0 hθ1 flow0 flow1 feas0 feas1 0 (4 / 5) band0 band1
      rw [show (1 - 5 * η / 4) * 0 + 5 * η / 4 * (4 / 5) = η by ring] at hB
      refine (value_le_flow tyC (wtC a b) (normMass_typed_pos hb hab) η K5 K5_ne _ hF hB).trans
        (Finset.sup'_le _ _ fun k hk => ?_)
      rw [mixTwo_obj, max_eq_left (by linarith)]
      have h0 := mul_le_mul_of_nonneg_left (obj0_le hb hab k hk)
        (show (0 : ℝ) ≤ 1 - 5 * η / 4 by linarith)
      have h1 := mul_le_mul_of_nonneg_left (obj1_le hb hab k hk) hθ0
      nlinarith
    · have hB := band_mono tyC flow1 (4 / 5) η band1 hgt.le (by norm_num)
      refine (value_le_flow tyC (wtC a b) (normMass_typed_pos hb hab) η K5 K5_ne _ feas1 hB).trans
        (Finset.sup'_le _ _ fun k hk => ?_)
      rw [max_eq_right (by linarith)]
      have := obj1_le hb hab k hk
      linarith
  · unfold trueValue
    obtain ⟨P0, hP0⟩ := allPerm_feasible_nonempty 6 η hη
    refine le_csInf ⟨_, P0, hP0, rfl⟩ ?_
    rintro _ ⟨P, hP, rfl⟩
    have h1 := lower_band hb hab η P hP
    have h2 := lower_free hb hab P hP.1 hP.2.1
    rcases le_total ((2 - η) / 3) (2 / 5) with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1

/-- **The price is `5/3` and the band is free from `η = 4/5`, at every ratio.** -/
theorem twoMag2211_price (hb : 0 < b) (hab : b < a) :
    trueValue (g6 a b) 0 K5 K5_ne = 5 / 3 * trueValue (g6 a b) 6 K5 K5_ne
      ∧ ∀ η, 4 / 5 ≤ η → trueValue (g6 a b) η K5 K5_ne = trueValue (g6 a b) 6 K5 K5_ne := by
  refine ⟨?_, fun η hη => ?_⟩
  · rw [twoMag2211_frontier hb hab 0 le_rfl, twoMag2211_frontier hb hab 6 (by norm_num)]
    rw [max_eq_left (by norm_num), max_eq_right (by norm_num)]
    ring
  · rw [twoMag2211_frontier hb hab η (by linarith), twoMag2211_frontier hb hab 6 (by norm_num),
      max_eq_right (by linarith), max_eq_right (by norm_num)]

/-- **The free threshold is `4/5`, at every ratio.** -/
theorem twoMag2211_etaFree (hb : 0 < b) (hab : b < a) : etaFree (g6 a b) K5 K5_ne = 4 / 5 := by
  have hg : 0 < normMass (g6 a b) := by rw [normMass_g6 hb hab]; linarith
  have hD : 0 < 4 * a + 2 * b := by linarith
  have hc : 0 < (a - b) / (4 * a + 2 * b) := div_pos (by linarith) hD
  have hfree : Vfree (g6 a b) K5 K5_ne = (a - b) / (4 * a + 2 * b) * (2 / 5) := by
    unfold Vfree
    rw [show ((6 : ℕ) : ℝ) = 6 by norm_num, twoMag2211_frontier hb hab 6 (by norm_num),
      max_eq_right (by norm_num)]
  apply le_antisymm
  · refine (free_threshold (g6 a b) hg K5 K5_ne (4 / 5) (by norm_num)).mp ?_
    rw [hfree, twoMag2211_frontier hb hab (4 / 5) (by norm_num), max_eq_right (by norm_num)]
  · have h0 := etaFree_nonneg (g6 a b) K5 K5_ne
    have heq := (free_threshold (g6 a b) hg K5 K5_ne _ h0).mpr le_rfl
    rw [hfree, twoMag2211_frontier hb hab _ h0] at heq
    by_contra hlt
    push_neg at hlt
    have hmax : max ((2 - etaFree (g6 a b) K5 K5_ne) / 3) (2 / 5)
        = (2 - etaFree (g6 a b) K5 K5_ne) / 3 := max_eq_left (by linarith)
    rw [hmax] at heq
    have := mul_left_cancel₀ hc.ne' heq
    linarith

#print axioms base1
#print axioms base3
#print axioms base5
#print axioms per_order
#print axioms lower_band
#print axioms lower_free
#print axioms band0
#print axioms band1
#print axioms obj0_le
#print axioms obj1_le
#print axioms twoMag2211_frontier
#print axioms twoMag2211_price
#print axioms twoMag2211_etaFree

end CIGAMF.P13.PaperCTwoMag2211
