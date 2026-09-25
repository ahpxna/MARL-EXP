import «LeanPaperCFreeBandV1»

/-!
# Paper C: the two-magnitude family with one item of each type, at every ratio

`g = (a, -a, b, -b)` with `0 < b < a`, `D = ‖g‖₁ = 2(a+b)`, interior budgets `K = {1,2,3}`.

**Theorem** (`twoMag_frontier`). For every `η ≥ 0`,
`V_g(η) = ((a-b)/D) · max((1-η)/2, 1/3)`.
So the frontier has one breakpoint at `η = 1/3`, and the price `V_g(0)/V_g^free = 3/2`, whatever
the ratio `a/b`. At `a/b = 3` this is the proved `m = 4` case of `g_m` up to the order of the
items.

**The certificates.**
* Dual side:
  - the band at the first position forces an `a`-item first with probability at least
    `(1-η)/2`, and that costs `a - b` at budget `1` (`lower_band`);
  - on every order `r₁ + r₂ + r₃ ≥ (a-b)/D` (`per_order`), so the worst budget costs at least a
    third of that (`lower_free`).
* Primal side: the six-order law `lawη` has three pieces:
  - `a`-pair first, weight `(1-η)/2`;
  - `b`-pair first, weight `(1-η)/2`;
  - `(±b, ∓a, ±a, ∓b)`, weight `η`;
  - each piece is split evenly over two orientations.
  It is band-feasible for `η ∈ [0, 1/3]` (`law_feasible`) and has budget costs
  `((1-η)/2, η, (1-η)/2)·(a-b)/D` (`law_obj`).
-/

namespace CIGAMF.P13.PaperCTwoMagFour

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

/-- The two-magnitude multiset with one item of each type. -/
noncomputable def g4 (a b : ℝ) : Fin 4 → ℝ := ![a, -a, b, -b]

variable {a b : ℝ}

theorem g4_sum (a b : ℝ) : ∑ i, g4 a b i = 0 := by
  simp [g4, Fin.sum_univ_four]

theorem abs_g4 (hb : 0 < b) (hab : b < a) (i : Fin 4) :
    |g4 a b i| = if i.val < 2 then a else b := by
  have ha : 0 < a := hb.trans hab
  fin_cases i <;> simp [g4, abs_of_pos ha, abs_of_pos hb]

theorem abs_g4_ge (hb : 0 < b) (hab : b < a) (i : Fin 4) : b ≤ |g4 a b i| := by
  rw [abs_g4 hb hab]; split_ifs <;> linarith

theorem normMass_g4 (hb : 0 < b) (hab : b < a) : normMass (g4 a b) = 2 * (a + b) := by
  have ha : 0 < a := hb.trans hab
  unfold normMass
  simp [g4, Fin.sum_univ_four, abs_of_pos ha, abs_of_pos hb]
  ring

/-! ## 1. Baselines -/

theorem base_one (hb : 0 < b) (hab : b < a) : trueBaseline (g4 a b) 1 = b := by
  unfold trueBaseline baseline
  apply le_antisymm
  · refine (Finset.inf'_le _ (show ({2} : Finset (Fin 4)) ∈ _ by simp)).trans (le_of_eq ?_)
    simp [g4, abs_of_pos hb]
  · refine Finset.le_inf' _ _ fun S hS => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS
    simpa using abs_g4_ge hb hab i

theorem base_two : trueBaseline (g4 a b) 2 = 0 := by
  unfold trueBaseline baseline
  apply le_antisymm
  · refine (Finset.inf'_le _ (show ({0, 1} : Finset (Fin 4)) ∈ _ by decide)).trans (le_of_eq ?_)
    simp [g4]
  · exact Finset.le_inf' _ _ fun S _ => abs_nonneg _

theorem sum_compl_single (j : Fin 4) : ∑ i ∈ ({j}ᶜ : Finset (Fin 4)), g4 a b i = -g4 a b j := by
  have h := Finset.sum_add_sum_compl ({j} : Finset (Fin 4)) (g4 a b)
  rw [g4_sum, Finset.sum_singleton] at h
  linarith

theorem base_three (hb : 0 < b) (hab : b < a) : trueBaseline (g4 a b) 3 = b := by
  unfold trueBaseline baseline
  apply le_antisymm
  · refine (Finset.inf'_le _ (show ({3}ᶜ : Finset (Fin 4)) ∈ _ by decide)).trans (le_of_eq ?_)
    show |∑ i ∈ ({3}ᶜ : Finset (Fin 4)), g4 a b i| = b
    rw [sum_compl_single]; simp [g4, abs_of_pos hb]
  · refine Finset.le_inf' _ _ fun S hS => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have hc : Sᶜ.card = 1 := by rw [Finset.card_compl, hS]; rfl
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
    have hS' : S = {j}ᶜ := by rw [← hj, compl_compl]
    rw [hS', sum_compl_single, abs_neg]
    exact abs_g4_ge hb hab j

/-! ## 2. Prefixes -/

theorem prefix_one (σ : Equiv.Perm (Fin 4)) : prefixSet σ 1 = {σ 0} := by
  ext i
  simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    have : σ.symm i = 0 := Fin.ext (by simpa using h)
    rw [← this, Equiv.apply_symm_apply]
  · rintro rfl; simp

theorem prefix_three (σ : Equiv.Perm (Fin 4)) : prefixSet σ 3 = {σ 3}ᶜ := by
  ext i
  simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
    Finset.mem_singleton]
  constructor
  · intro h heq
    rw [heq, Equiv.symm_apply_apply] at h
    simp at h
  · intro h
    have h3 : σ.symm i ≠ 3 := fun h' => h (by rw [← h', Equiv.apply_symm_apply])
    have := (σ.symm i).isLt
    have h3' : (σ.symm i).val ≠ 3 := fun h' => h3 (Fin.ext h')
    show (σ.symm i).val < 3
    omega

theorem prefix_two (σ : Equiv.Perm (Fin 4)) : prefixSet σ 2 = {σ 0, σ 1} := by
  ext i
  simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    have h' : (σ.symm i).val < 2 := h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h' with h0 | h1
    · left
      have : σ.symm i = 0 := Fin.ext (by simpa using h0)
      rw [← this, Equiv.apply_symm_apply]
    · right
      have : σ.symm i = 1 := Fin.ext h1
      rw [← this, Equiv.apply_symm_apply]
  · rintro (rfl | rfl) <;> simp

theorem raw_one (hb : 0 < b) (hab : b < a) (σ : Equiv.Perm (Fin 4)) :
    rawRegret (g4 a b) σ 1 = |g4 a b (σ 0)| - b := by
  unfold rawRegret; rw [prefix_one, Finset.sum_singleton, base_one hb hab]

theorem raw_three (hb : 0 < b) (hab : b < a) (σ : Equiv.Perm (Fin 4)) :
    rawRegret (g4 a b) σ 3 = |g4 a b (σ 3)| - b := by
  unfold rawRegret; rw [prefix_three, sum_compl_single, abs_neg, base_three hb hab]

theorem raw_two (σ : Equiv.Perm (Fin 4)) :
    rawRegret (g4 a b) σ 2 = |g4 a b (σ 0) + g4 a b (σ 1)| := by
  unfold rawRegret
  rw [prefix_two, Finset.sum_pair (σ.injective.ne (by decide)), base_two, sub_zero]

/-! ## 3. The dual side -/

/-- **Every order pays `a - b` over the three budgets.** -/
theorem per_order (hb : 0 < b) (hab : b < a) (σ : Equiv.Perm (Fin 4)) :
    a - b ≤ rawRegret (g4 a b) σ 1 + rawRegret (g4 a b) σ 2 + rawRegret (g4 a b) σ 3 := by
  rw [raw_one hb hab, raw_two, raw_three hb hab]
  have h0 := abs_g4_ge hb hab (σ 0)
  have h3 := abs_g4_ge hb hab (σ 3)
  have h2 := abs_nonneg (g4 a b (σ 0) + g4 a b (σ 1))
  by_cases hA0 : (σ 0).val < 2
  · rw [abs_g4 hb hab (σ 0), if_pos hA0]; linarith
  by_cases hA3 : (σ 3).val < 2
  · rw [abs_g4 hb hab (σ 3), if_pos hA3]; linarith
  have h10 : (σ 1).val ≠ (σ 0).val := fun h => absurd (σ.injective (Fin.ext h)) (by decide)
  have h13 : (σ 1).val ≠ (σ 3).val := fun h => absurd (σ.injective (Fin.ext h)) (by decide)
  have h03 : (σ 0).val ≠ (σ 3).val := fun h => absurd (σ.injective (Fin.ext h)) (by decide)
  have hl0 := (σ 0).isLt
  have hl1 := (σ 1).isLt
  have hl3 := (σ 3).isLt
  have hA1 : (σ 1).val < 2 := by omega
  have e0 : |g4 a b (σ 0)| = b := by rw [abs_g4 hb hab, if_neg hA0]
  have e1 : |g4 a b (σ 1)| = a := by rw [abs_g4 hb hab, if_pos hA1]
  have htri : |g4 a b (σ 1)| - |g4 a b (σ 0)| ≤ |g4 a b (σ 0) + g4 a b (σ 1)| := by
    have := abs_sub_abs_le_abs_sub (g4 a b (σ 1)) (-g4 a b (σ 0))
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    exact this
  rw [e0, e1] at htri
  linarith

/-- The interior budgets. -/
def K3 : Finset (Fin 5) := {1, 2, 3}

theorem K3_ne : K3.Nonempty := ⟨1, by simp [K3]⟩

theorem obj_ge (P : Equiv.Perm (Fin 4) → ℝ) (k : Fin 5) (hk : k ∈ K3) :
    ∑ σ, P σ * normalizedRegret (g4 a b) σ k ≤ trueObjective (g4 a b) P K3 K3_ne :=
  Finset.le_sup' (f := fun k => ∑ σ, P σ * normalizedRegret (g4 a b) σ k) hk

theorem marg_one (P : Equiv.Perm (Fin 4) → ℝ) (i : Fin 4) :
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

/-- **The band's lower side.** -/
theorem lower_band (hb : 0 < b) (hab : b < a) (η : ℝ) (P : Equiv.Perm (Fin 4) → ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin 4) → _) η) :
    (a - b) / (2 * (a + b)) * ((1 - η) / 2) ≤ trueObjective (g4 a b) P K3 K3_ne := by
  obtain ⟨hnn, hsum, hband⟩ := hP
  refine le_trans (le_of_eq_of_le rfl ?_) (obj_ge P 1 (by simp [K3]))
  have hD : 0 < 2 * (a + b) := by linarith
  have hm : ∀ i : Fin 4, (1 - η) / 4 ≤ marg P 1 i := by
    intro i
    have h := hband 1 (by norm_num) i
    have : |marg P 1 i - 1 / 4| ≤ η / 4 := by simpa [marg] using h
    rw [abs_le] at this
    linarith
  have hsplit : ∀ σ : Equiv.Perm (Fin 4), P σ * normalizedRegret (g4 a b) σ 1
      = (a - b) / (2 * (a + b)) * (P σ * (if σ 0 = 0 then 1 else 0)
        + P σ * (if σ 0 = 1 then 1 else 0)) := by
    intro σ
    unfold normalizedRegret
    rw [raw_one hb hab, normMass_g4 hb hab, abs_g4 hb hab]
    have hv := (σ 0).isLt
    by_cases h0 : σ 0 = 0
    · rw [if_pos (by rw [h0]; decide), if_pos h0, if_neg (by rw [h0]; decide)]; ring
    by_cases h1 : σ 0 = 1
    · rw [if_pos (by rw [h1]; decide), if_neg h0, if_pos h1]; ring
    · have : ¬ (σ 0).val < 2 := by
        intro h
        have : (σ 0).val = 0 ∨ (σ 0).val = 1 := by omega
        rcases this with h' | h'
        · exact h0 (Fin.ext h')
        · exact h1 (Fin.ext h')
      rw [if_neg this, if_neg h0, if_neg h1]; ring
  rw [Finset.sum_congr rfl fun σ _ => hsplit σ, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← marg_one, ← marg_one]
  have := hm 0
  have := hm 1
  have hc : 0 ≤ (a - b) / (2 * (a + b)) := div_nonneg (by linarith) hD.le
  nlinarith

/-- **The free lower bound.** -/
theorem lower_free (hb : 0 < b) (hab : b < a) (P : Equiv.Perm (Fin 4) → ℝ)
    (hnn : ∀ σ, 0 ≤ P σ) (hsum : ∑ σ, P σ = 1) :
    (a - b) / (2 * (a + b)) * (1 / 3) ≤ trueObjective (g4 a b) P K3 K3_ne := by
  have hD : 0 < 2 * (a + b) := by linarith
  have h1 := obj_ge (a := a) (b := b) P 1 (by simp [K3])
  have h2 := obj_ge (a := a) (b := b) P 2 (by simp [K3])
  have h3 := obj_ge (a := a) (b := b) P 3 (by simp [K3])
  have hsum3 : (a - b) / (2 * (a + b)) ≤ ∑ σ, P σ * normalizedRegret (g4 a b) σ 1
      + ∑ σ, P σ * normalizedRegret (g4 a b) σ 2 + ∑ σ, P σ * normalizedRegret (g4 a b) σ 3 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc (a - b) / (2 * (a + b)) = ∑ σ, P σ * ((a - b) / (2 * (a + b))) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun σ _ => by
          unfold normalizedRegret
          rw [normMass_g4 hb hab]
          have hp := per_order hb hab σ
          have : (a - b) / (2 * (a + b)) ≤ rawRegret (g4 a b) σ 1 / (2 * (a + b))
              + rawRegret (g4 a b) σ 2 / (2 * (a + b)) + rawRegret (g4 a b) σ 3 / (2 * (a + b)) := by
            rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right hp hD.le
          have := hnn σ
          nlinarith
  linarith

/-! ## 4. The primal side -/

/-- A permutation from its table and its inverse's. -/
def mkPerm (f g : Fin 4 → Fin 4) (h1 : ∀ i, g (f i) = i) (h2 : ∀ i, f (g i) = i) :
    Equiv.Perm (Fin 4) := ⟨f, g, h1, h2⟩

/-- `b`-pair first, then the `a`-pair (two orientations). -/
def pA1 : Equiv.Perm (Fin 4) := mkPerm ![2, 3, 0, 1] ![2, 3, 0, 1] (by decide) (by decide)
def pA2 : Equiv.Perm (Fin 4) := mkPerm ![3, 2, 1, 0] ![3, 2, 1, 0] (by decide) (by decide)
/-- `a`-pair first. -/
def pB1 : Equiv.Perm (Fin 4) := mkPerm ![0, 1, 2, 3] ![0, 1, 2, 3] (by decide) (by decide)
def pB2 : Equiv.Perm (Fin 4) := mkPerm ![1, 0, 3, 2] ![1, 0, 3, 2] (by decide) (by decide)
/-- `(±b, ∓a, ±a, ∓b)`. -/
def pC1 : Equiv.Perm (Fin 4) := mkPerm ![2, 1, 0, 3] ![2, 1, 0, 3] (by decide) (by decide)
def pC2 : Equiv.Perm (Fin 4) := mkPerm ![3, 0, 1, 2] ![1, 2, 3, 0] (by decide) (by decide)

/-- **The six-order law.** -/
noncomputable def lawη (η : ℝ) (σ : Equiv.Perm (Fin 4)) : ℝ :=
  (1 - η) / 4 * ((if σ = pA1 then 1 else 0) + (if σ = pA2 then 1 else 0)
      + (if σ = pB1 then 1 else 0) + (if σ = pB2 then 1 else 0))
    + η / 2 * ((if σ = pC1 then 1 else 0) + (if σ = pC2 then 1 else 0))

theorem law_sum (η : ℝ) (f : Equiv.Perm (Fin 4) → ℝ) :
    ∑ σ, lawη η σ * f σ = (1 - η) / 4 * (f pA1 + f pA2 + f pB1 + f pB2)
      + η / 2 * (f pC1 + f pC2) := by
  unfold lawη
  simp only [add_mul, mul_add, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem law_feasible (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    lawη η ∈ FeasibleAt (id : Equiv.Perm (Fin 4) → _) η := by
  refine ⟨fun σ => ?_, ?_, fun k hk i => ?_⟩
  · unfold lawη
    have : 0 ≤ 1 - η := by linarith
    have h1 : 0 ≤ (1 - η) / 4 * ((if σ = pA1 then (1 : ℝ) else 0) + (if σ = pA2 then 1 else 0)
        + (if σ = pB1 then 1 else 0) + (if σ = pB2 then 1 else 0)) := by
      apply mul_nonneg (by positivity); split_ifs <;> norm_num
    have h2 : 0 ≤ η / 2 * ((if σ = pC1 then (1 : ℝ) else 0) + (if σ = pC2 then 1 else 0)) := by
      apply mul_nonneg (by positivity); split_ifs <;> norm_num
    linarith
  · have := law_sum η (fun _ => 1)
    simp only [mul_one] at this
    rw [this]; ring
  · have hsum := law_sum η (fun σ => inPrefixInd (id σ) k i)
    rw [hsum]
    interval_cases k <;> fin_cases i <;>
      simp [inPrefixInd, pA1, pA2, pB1, pB2, pC1, pC2, mkPerm] <;>
      (try rw [abs_le]) <;> (try constructor) <;> linarith

theorem law_nonneg (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : ∀ σ, 0 ≤ lawη η σ :=
  (law_feasible η hη0 hη1).1

example (hb : 0 < b) (hab : b < a) :
    (rawRegret (g4 a b) pA1 1 = 0 ∧ rawRegret (g4 a b) pA2 1 = 0 ∧ rawRegret (g4 a b) pB1 1 = a - b
      ∧ rawRegret (g4 a b) pB2 1 = a - b ∧ rawRegret (g4 a b) pC1 1 = 0
      ∧ rawRegret (g4 a b) pC2 1 = 0)
    ∧ (rawRegret (g4 a b) pA1 2 = 0 ∧ rawRegret (g4 a b) pA2 2 = 0 ∧ rawRegret (g4 a b) pB1 2 = 0
      ∧ rawRegret (g4 a b) pB2 2 = 0 ∧ rawRegret (g4 a b) pC1 2 = a - b
      ∧ rawRegret (g4 a b) pC2 2 = a - b)
    ∧ (rawRegret (g4 a b) pA1 3 = a - b ∧ rawRegret (g4 a b) pA2 3 = a - b
      ∧ rawRegret (g4 a b) pB1 3 = 0 ∧ rawRegret (g4 a b) pB2 3 = 0
      ∧ rawRegret (g4 a b) pC1 3 = 0 ∧ rawRegret (g4 a b) pC2 3 = 0) := by
  have ha : 0 < a := hb.trans hab
  have hab' : 0 < a - b := by linarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp only [raw_one hb hab, raw_two, raw_three hb hab] <;>
    simp [pA1, pA2, pB1, pB2, pC1, pC2, mkPerm, g4, abs_of_pos ha, abs_of_pos hb] <;>
    trace_state


end CIGAMF.P13.PaperCTwoMagFour
