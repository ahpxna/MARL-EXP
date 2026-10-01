import «LeanPaperCPathMixV1»

/-!
# Paper C: the two-magnitude family with counts `(2,2,2,2)` — objects and glue

`g = (a, a, -a, -a, b, b, -b, -b)` with `0 < b < a`, `D = ‖g‖₁ = 4(a+b)`, interior budgets
`K = {1,…,7}`. This module fixes the objects and proves the two reductions used by the
region modules.

* `g8 = typedG ty8 (wt a b)`: the multiset as a typed multiset with four types of two items.
* `base1` … `base7`: the per-budget optima. `b₁ = b₇ = b`, `b₂ = b₄ = b₆ = 0`, and
  `b₃ = b₅ = 2b - a` on `a ≤ 2b`, `a - 2b` on `2b ≤ a ≤ 3b`, `b` on `3b ≤ a`.
* `abs_sN_lo`, `abs_sN_hi`: on each side of `a = 2b` the sign of the prefix sum of a count
  state is an explicit function of the counts.
* `cert8`: **the dual side.** A certificate given by budget weights `μ`, band multipliers `ℓ`
  and a potential table `φ` on the `81` count states, all scaled by a common positive `Z` and by
  `D`, whose edge inequalities (`EdgeOK`) hold, bounds the value below by
  `(φ(0) - (η/8) Σ|ℓ|)/(Z D)`. It is `cert_lower` (weak duality) through
  `typed_flow_equivalence`.
* `value_le_mixQ`: **the primal side.** A mixture of type sequences with weights `n_j / Q`
  that meets the band and whose weighted raw costs are at most `Q W` bounds the value above by
  `W / D`. `value_le_mixQ_free` is the case `η = 8`, where the band is automatic.
-/

namespace CIGAMF.P13.PaperCTwoMag2222

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCFlowBandJoin CIGAMF.P13.PaperCVacuity CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFreeBand CIGAMF.P13.PaperCFlowCert
open CIGAMF.P13.PaperCPathMix CIGAMF.P13.PaperCFrontier CIGAMF.P13.PaperCLawPush

/-- Item types: `+a, +a, -a, -a, +b, +b, -b, -b`. -/
def ty8 : Fin 8 → Fin 4 := ![0, 0, 1, 1, 2, 2, 3, 3]

/-- Type weights. -/
noncomputable def wt (a b : ℝ) : Fin 4 → ℝ := ![a, -a, b, -b]

/-- The multiset `(a, a, -a, -a, b, b, -b, -b)`. -/
noncomputable def g8 (a b : ℝ) : Fin 8 → ℝ := typedG ty8 (wt a b)

/-- The interior budgets. -/
def K7 : Finset (Fin 9) := {1, 2, 3, 4, 5, 6, 7}

theorem K7_ne : K7.Nonempty := ⟨1, by simp [K7]⟩

theorem mult_ty8 (τ : Fin 4) : mult ty8 τ = 2 := by fin_cases τ <;> decide

theorem g8_eq (a b : ℝ) : g8 a b = ![a, a, -a, -a, b, b, -b, -b] := by
  funext i; fin_cases i <;> rfl

variable {a b : ℝ}

theorem normMass_g8 (hb : 0 < b) (hab : b < a) : normMass (g8 a b) = 4 * (a + b) := by
  have ha : 0 < a := hb.trans hab
  unfold normMass g8 typedG
  simp [ty8, wt, Fin.sum_univ_succ, abs_of_pos ha, abs_of_pos hb]
  ring

/-! ## 1. Subset sums through type counts, and the baselines -/

theorem sum_typed8 (w : Fin 4 → ℝ) (S : Finset (Fin 8)) :
    ∑ i ∈ S, typedG ty8 w i = ∑ τ, w τ * ((S.filter fun i => ty8 i = τ).card : ℝ) := by
  rw [← Finset.sum_fiberwise S ty8 (typedG ty8 w)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have : ∀ i ∈ S.filter (fun i => ty8 i = τ), typedG ty8 w i = w τ := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    unfold typedG; rw [hi.2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem baseline_ge8 (w : Fin 4 → ℝ) (k : Fin 9) (L : ℝ)
    (h : ∀ u : Fin 4 → ℕ, (∀ τ, u τ ≤ 2) → ∑ τ, u τ = k.val → L ≤ |∑ τ, w τ * (u τ : ℝ)|) :
    L ≤ trueBaseline (typedG ty8 w) k := by
  unfold trueBaseline baseline
  refine Finset.le_inf' _ _ fun S hS => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [sum_typed8]
  refine h (fun τ => (S.filter fun i => ty8 i = τ).card) (fun τ => ?_) ?_
  · rw [← mult_ty8 τ]
    unfold mult
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))
  · rw [← hS]
    exact (Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (ty8 i))).symm

theorem baseline_le8 (w : Fin 4 → ℝ) (k : Fin 9) (S : Finset (Fin 8)) (hS : S.card = k.val) :
    trueBaseline (typedG ty8 w) k ≤ |∑ i ∈ S, typedG ty8 w i| := by
  unfold trueBaseline baseline
  exact Finset.inf'_le _ (by simp [hS])

theorem sum_wt (u : Fin 4 → ℕ) :
    ∑ τ, wt a b τ * (u τ : ℝ) = a * ((u 0 : ℝ) - u 1) + b * ((u 2 : ℝ) - u 3) := by
  simp [wt, Fin.sum_univ_four]; ring

theorem lin_ge8 (k : ℕ) (L : ℝ)
    (hL : ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 2 → x1 ≤ 2 → x2 ≤ 2 → x3 ≤ 2 → x0 + x1 + x2 + x3 = k →
      L ≤ |a * ((x0 : ℝ) - x1) + b * ((x2 : ℝ) - x3)|)
    (u : Fin 4 → ℕ) (hu : ∀ τ, u τ ≤ 2) (hs : ∑ τ, u τ = k) :
    L ≤ |∑ τ, wt a b τ * (u τ : ℝ)| := by
  rw [sum_wt]
  exact hL _ _ _ _ (hu 0) (hu 1) (hu 2) (hu 3) (by rw [← hs]; simp [Fin.sum_univ_four])

theorem base1 (hb : 0 < b) (hab : b < a) : trueBaseline (g8 a b) 1 = b := by
  apply le_antisymm
  · refine (baseline_le8 (wt a b) 1 {4} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty8, wt, abs_of_pos hb]
  · refine baseline_ge8 (wt a b) 1 b (lin_ge8 1 b ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

theorem base7 (hb : 0 < b) (hab : b < a) : trueBaseline (g8 a b) 7 = b := by
  apply le_antisymm
  · refine (baseline_le8 (wt a b) 7 {0, 1, 2, 3, 4, 5, 6} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty8, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    linarith
  · refine baseline_ge8 (wt a b) 7 b (lin_ge8 7 b ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

theorem base_even (k : Fin 9) (S : Finset (Fin 8)) (hS : S.card = k.val)
    (h0 : ∑ i ∈ S, g8 a b i = 0) : trueBaseline (g8 a b) k = 0 := by
  apply le_antisymm
  · refine (baseline_le8 (wt a b) k S hS).trans (le_of_eq ?_)
    have : ∑ i ∈ S, typedG ty8 (wt a b) i = 0 := h0
    rw [this, abs_zero]
  · exact baseline_ge8 (wt a b) k 0 fun u _ _ => abs_nonneg _

theorem base2 : trueBaseline (g8 a b) 2 = 0 :=
  base_even 2 {0, 2} (by decide) (by simp [g8, typedG, ty8, wt])

theorem base4 : trueBaseline (g8 a b) 4 = 0 :=
  base_even 4 {0, 2, 4, 6} (by decide)
    (by simp [g8, typedG, ty8, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton])

theorem base6 : trueBaseline (g8 a b) 6 = 0 :=
  base_even 6 {0, 1, 2, 3, 4, 6} (by decide)
    (by simp [g8, typedG, ty8, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton])

theorem base0 : trueBaseline (g8 a b) 0 = 0 :=
  base_even 0 ∅ (by decide) (by simp)

theorem base3_lo (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    trueBaseline (g8 a b) 3 = 2 * b - a := by
  apply le_antisymm
  · refine (baseline_le8 (wt a b) 3 {0, 6, 7} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty8, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    rw [abs_of_nonpos (by linarith)]; ring
  · refine baseline_ge8 (wt a b) 3 (2 * b - a) (lin_ge8 3 _ ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

theorem base3_mid (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    trueBaseline (g8 a b) 3 = a - 2 * b := by
  apply le_antisymm
  · refine (baseline_le8 (wt a b) 3 {0, 6, 7} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty8, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    rw [abs_of_nonneg (by linarith)]; ring
  · refine baseline_ge8 (wt a b) 3 (a - 2 * b) (lin_ge8 3 _ ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

theorem base3_hi (hb : 0 < b) (h3 : 3 * b ≤ a) : trueBaseline (g8 a b) 3 = b := by
  apply le_antisymm
  · refine (baseline_le8 (wt a b) 3 {0, 2, 4} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty8, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      abs_of_pos hb]
  · refine baseline_ge8 (wt a b) 3 b (lin_ge8 3 _ ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

theorem base5_lo (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    trueBaseline (g8 a b) 5 = 2 * b - a := by
  apply le_antisymm
  · refine (baseline_le8 (wt a b) 5 {1, 2, 3, 4, 5} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty8, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    rw [abs_of_nonneg (by linarith)]; ring
  · refine baseline_ge8 (wt a b) 5 (2 * b - a) (lin_ge8 5 _ ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

theorem base5_mid (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    trueBaseline (g8 a b) 5 = a - 2 * b := by
  apply le_antisymm
  · refine (baseline_le8 (wt a b) 5 {1, 2, 3, 4, 5} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty8, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    rw [abs_of_nonpos (by linarith)]; ring
  · refine baseline_ge8 (wt a b) 5 (a - 2 * b) (lin_ge8 5 _ ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

theorem base5_hi (hb : 0 < b) (h3 : 3 * b ≤ a) : trueBaseline (g8 a b) 5 = b := by
  apply le_antisymm
  · refine (baseline_le8 (wt a b) 5 {0, 1, 2, 3, 4} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty8, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    linarith
  · refine baseline_ge8 (wt a b) 5 b (lin_ge8 5 _ ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

/-! ## 2. Count-state costs and signs -/

/-- The prefix sum of a count state `(v₀, v₁, v₂, v₃)`. -/
noncomputable def sN (a b : ℝ) (v0 v1 v2 v3 : ℕ) : ℝ := a * ((v0 : ℝ) - v1) + b * ((v2 : ℝ) - v3)

theorem sum_wt_state (v : CState 4 8) :
    ∑ τ, wt a b τ * ((v τ : ℕ) : ℝ) = sN a b (v 0) (v 1) (v 2) (v 3) := by
  simp [wt, sN, Fin.sum_univ_four]; ring

theorem typedCost_eq8 (hb : 0 < b) (hab : b < a) (k : Fin 9) (v : CState 4 8) :
    typedCost ty8 (wt a b) k v
      = (|sN a b (v 0) (v 1) (v 2) (v 3)| - trueBaseline (g8 a b) k) / (4 * (a + b)) := by
  unfold typedCost
  rw [show normMass (typedG ty8 (wt a b)) = 4 * (a + b) from normMass_g8 hb hab, sum_wt_state]
  rfl

/-- The sign of the prefix sum when `a ≥ 2b`: the sign of the `a`-part, else of the `b`-part. -/
noncomputable def sgHi (v0 v1 v2 v3 : ℕ) : ℝ :=
  if v1 < v0 then 1 else if v0 < v1 then -1 else if v3 < v2 then 1 else if v2 < v3 then -1 else 0

/-- The sign of the prefix sum when `b < a ≤ 2b`. -/
noncomputable def sgLo (v0 v1 v2 v3 : ℕ) : ℝ :=
  if v0 = v1 + 1 ∧ v3 = v2 + 2 then -1
  else if v1 = v0 + 1 ∧ v2 = v3 + 2 then 1 else sgHi v0 v1 v2 v3

theorem abs_sN_hi (hb : 0 < b) (h2 : 2 * b ≤ a) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2)
    (h2' : v2 ≤ 2) (h3 : v3 ≤ 2) :
    |sN a b v0 v1 v2 v3| = sgHi v0 v1 v2 v3 * sN a b v0 v1 v2 v3 := by
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
    simp only [sgHi, sN, Nat.reduceLT, ite_true, ite_false, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, one_mul, neg_one_mul, zero_mul] <;>
    first
      | (rw [abs_of_nonneg (by linarith)]; done)
      | (rw [abs_of_nonpos (by linarith)]; done)
      | simp

theorem abs_sN_lo (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2)
    (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3 : v3 ≤ 2) :
    |sN a b v0 v1 v2 v3| = sgLo v0 v1 v2 v3 * sN a b v0 v1 v2 v3 := by
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
    simp only [sgLo, sgHi, sN, Nat.reduceLT, Nat.reduceAdd, Nat.reduceEqDiff, and_true, true_and,
      and_false, false_and, ite_true, ite_false, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, one_mul, neg_one_mul, zero_mul] <;>
    first
      | (rw [abs_of_nonneg (by linarith)]; done)
      | (rw [abs_of_nonpos (by linarith)]; done)
      | simp

/-! ## 3. The two glue lemmas -/

theorem value_ge_of_flows (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) (L : ℝ)
    (h : ∀ F : LayeredFlow (CState 4 8), CountFeasibleH ty8 F → FlowBand ty8 F η →
      L ≤ K7.sup' K7_ne (flowObj (typedCost ty8 (wt a b)) F)) :
    L ≤ trueValue (g8 a b) η K7 K7_ne := by
  unfold trueValue
  obtain ⟨P0, hP0⟩ := allPerm_feasible_nonempty 8 η hη
  refine le_csInf ⟨_, P0, hP0, rfl⟩ ?_
  rintro _ ⟨P, hP, rfl⟩
  have hmem : (fun k => ∑ σ, P σ * normalizedRegret (typedG ty8 (wt a b)) σ k) ∈
      {y | ∃ F, CountFeasibleH ty8 F ∧ FlowBand ty8 F η ∧ flowObj (typedCost ty8 (wt a b)) F = y} := by
    rw [← typed_flow_equivalence]; exact ⟨P, hP, rfl⟩
  obtain ⟨F, hF, hB, hy⟩ := hmem
  calc L ≤ K7.sup' K7_ne (flowObj (typedCost ty8 (wt a b)) F) := h F hF hB
    _ = trueObjective (g8 a b) P K7 K7_ne := by rw [hy]; rfl

theorem value_le_of_flow (hb : 0 < b) (hab : b < a) (η : ℝ) (F : LayeredFlow (CState 4 8))
    (hF : CountFeasibleH ty8 F) (hB : FlowBand ty8 F η) (M : ℝ)
    (hM : ∀ k ∈ K7, flowObj (typedCost ty8 (wt a b)) F k ≤ M) :
    trueValue (g8 a b) η K7 K7_ne ≤ M := by
  have hmem : flowObj (typedCost ty8 (wt a b)) F ∈ {y : Fin 9 → ℝ | ∃ P ∈ FeasibleAt
      (id : Equiv.Perm (Fin 8) → _) η,
      (fun k => ∑ σ, P σ * normalizedRegret (typedG ty8 (wt a b)) σ k) = y} := by
    rw [typed_flow_equivalence]; exact ⟨F, hF, hB, rfl⟩
  obtain ⟨P, hP, hy⟩ := hmem
  have hg : 0 < normMass (g8 a b) := by rw [normMass_g8 hb hab]; linarith
  unfold trueValue
  refine (csInf_le (trueValue_bddBelow (g8 a b) hg η K7 K7_ne) ⟨P, hP, rfl⟩).trans ?_
  show K7.sup' K7_ne (fun k => ∑ σ, P σ * normalizedRegret (g8 a b) σ k) ≤ M
  have e : (fun k => ∑ σ, P σ * normalizedRegret (g8 a b) σ k)
      = flowObj (typedCost ty8 (wt a b)) F := hy
  rw [e]; exact Finset.sup'_le _ _ hM

/-! ## 4. The dual side: scaled certificates on the count states -/

/-- The scaled node cost of a certificate at the counts `(v₀, v₁, v₂, v₃)`. -/
noncomputable def nodeN (a b : ℝ) (β μ : ℕ → ℝ) (ℓ : ℕ → Fin 4 → ℝ) (v0 v1 v2 v3 : ℕ) : ℝ :=
  μ (v0 + v1 + v2 + v3) * (|sN a b v0 v1 v2 v3| - β (v0 + v1 + v2 + v3))
    + (ℓ (v0 + v1 + v2 + v3) 0 * ((v0 : ℝ) / 2 - ((v0 + v1 + v2 + v3 : ℕ) : ℝ) / 8)
      + ℓ (v0 + v1 + v2 + v3) 1 * ((v1 : ℝ) / 2 - ((v0 + v1 + v2 + v3 : ℕ) : ℝ) / 8)
      + ℓ (v0 + v1 + v2 + v3) 2 * ((v2 : ℝ) / 2 - ((v0 + v1 + v2 + v3 : ℕ) : ℝ) / 8)
      + ℓ (v0 + v1 + v2 + v3) 3 * ((v3 : ℝ) / 2 - ((v0 + v1 + v2 + v3 : ℕ) : ℝ) / 8))

/-- The edge inequalities of a potential table, on the `81` count states of the box. -/
def EdgeOK (a b : ℝ) (β μ : ℕ → ℝ) (ℓ : ℕ → Fin 4 → ℝ) (φ : ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ v0 v1 v2 v3 : ℕ, v0 ≤ 2 → v1 ≤ 2 → v2 ≤ 2 → v3 ≤ 2 →
    (v0 < 2 → φ v0 v1 v2 v3 ≤ nodeN a b β μ ℓ v0 v1 v2 v3 + φ (v0 + 1) v1 v2 v3) ∧
    (v1 < 2 → φ v0 v1 v2 v3 ≤ nodeN a b β μ ℓ v0 v1 v2 v3 + φ v0 (v1 + 1) v2 v3) ∧
    (v2 < 2 → φ v0 v1 v2 v3 ≤ nodeN a b β μ ℓ v0 v1 v2 v3 + φ v0 v1 (v2 + 1) v3) ∧
    (v3 < 2 → φ v0 v1 v2 v3 ≤ nodeN a b β μ ℓ v0 v1 v2 v3 + φ v0 v1 v2 (v3 + 1))

theorem bandTerm8 (ℓ : ℕ → Fin 4 → ℝ) (k : ℕ) (v : CState 4 8) :
    bandTerm ty8 ℓ k v
      = ℓ k 0 * (((v 0 : ℕ) : ℝ) / 2 - (k : ℝ) / 8) + ℓ k 1 * (((v 1 : ℕ) : ℝ) / 2 - (k : ℝ) / 8)
        + ℓ k 2 * (((v 2 : ℕ) : ℝ) / 2 - (k : ℝ) / 8)
        + ℓ k 3 * (((v 3 : ℕ) : ℝ) / 2 - (k : ℝ) / 8) := by
  unfold bandTerm
  simp only [Fin.sum_univ_four, mult_ty8]
  push_cast
  ring

theorem box_le (v : CState 4 8) (hv : InBox ty8 v) (τ : Fin 4) : (v τ : ℕ) ≤ 2 := by
  have := hv τ; rwa [mult_ty8] at this

theorem served_eq (v : CState 4 8) (k : ℕ) (hs : served v = k) :
    (v 0 : ℕ) + v 1 + v 2 + v 3 = k := by
  unfold served at hs; rw [Fin.sum_univ_four] at hs; exact_mod_cast hs

theorem fin4_cases (τ : Fin 4) : τ = 0 ∨ τ = 1 ∨ τ = 2 ∨ τ = 3 := by
  fin_cases τ <;> simp

/-- **Weak duality on the count states, scaled.** -/
theorem cert8 (hb : 0 < b) (hab : b < a) (Z : ℝ) (hZ : 0 < Z)
    (β μ : ℕ → ℝ) (ℓ : ℕ → Fin 4 → ℝ) (φ : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hμ0 : ∀ k, 0 ≤ μ k) (hμ00 : μ 0 = 0)
    (hμ1 : μ 1 + μ 2 + μ 3 + μ 4 + μ 5 + μ 6 + μ 7 = Z)
    (hβ : ∀ k (hk : k < 9), μ k ≠ 0 → trueBaseline (g8 a b) ⟨k, hk⟩ = β k)
    (hedge : EdgeOK a b β μ ℓ φ) (hend : φ 2 2 2 2 = 0) (η : ℝ) (hη : 0 ≤ η) :
    (φ 0 0 0 0 - η / 8 * ∑ k ∈ range 8, ∑ τ, |ℓ k τ|) / (Z * (4 * (a + b)))
      ≤ trueValue (g8 a b) η K7 K7_ne := by
  have hD : 0 < 4 * (a + b) := by linarith
  have hZD : 0 < Z * (4 * (a + b)) := mul_pos hZ hD
  apply value_ge_of_flows hb hab η hη
  intro F hF hB
  have key := cert_lower ty8 (typedCost ty8 (wt a b)) K7 K7_ne
    (fun k => if k ≤ 7 then μ k / Z else 0)
    (fun k => by
      show 0 ≤ (if k ≤ 7 then μ k / Z else 0)
      split_ifs
      · exact div_nonneg (hμ0 k) hZ.le
      · exact le_rfl)
    (fun k hk => by
      show (if (k : ℕ) ≤ 7 then μ k / Z else 0) = 0
      fin_cases k <;> simp [K7] at hk ⊢ <;> simp [hμ00])
    (fun k hk => by
      show (if k ≤ 7 then μ k / Z else 0) = 0
      rw [if_neg (by omega)])
    (by
      have e : ∀ k ∈ range 8, (if k ≤ 7 then μ k / Z else 0) = μ k / Z := fun k hk => by
        rw [if_pos (by simp at hk; omega)]
      rw [Finset.sum_congr rfl e, ← Finset.sum_div, div_eq_one_iff_eq hZ.ne']
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hμ00]
      linarith)
    (fun k τ => ℓ k τ / (Z * (4 * (a + b))))
    (fun k τ h => by rw [mult_ty8] at h; exact absurd h (by norm_num))
    (fun _ v => φ (v 0) (v 1) (v 2) (v 3) / (Z * (4 * (a + b))))
    (φ 0 0 0 0 / (Z * (4 * (a + b))))
    (by
      intro k hk v w hv hs hw hstep
      have hv' := box_le v hv
      have hw' := box_le w hw
      have hk' := served_eq v k hs
      have hnode : nodeCost ty8 (typedCost ty8 (wt a b)) (fun k => if k ≤ 7 then μ k / Z else 0)
          (fun k τ => ℓ k τ / (Z * (4 * (a + b)))) k v
          = nodeN a b β μ ℓ (v 0) (v 1) (v 2) (v 3) / (Z * (4 * (a + b))) := by
        unfold nodeCost nodeN
        rw [hk', typedCost_eq8 hb hab, bandTerm8]
        simp only [if_pos (show k ≤ 7 by omega)]
        have hofn : trueBaseline (g8 a b) (Fin.ofNat (8 + 1) k)
            = trueBaseline (g8 a b) ⟨k, by omega⟩ := by
          congr 1; ext; simp [Fin.ofNat, Nat.mod_eq_of_lt (show k < 9 by omega)]
        rw [hofn]
        by_cases hμk : μ k = 0
        · rw [hμk]; field_simp; try ring
        · rw [hβ k (by omega) hμk]; field_simp; try ring
      obtain ⟨τ, hτ, hrest⟩ := hstep
      have e := hedge (v 0) (v 1) (v 2) (v 3) (hv' 0) (hv' 1) (hv' 2) (hv' 3)
      show φ (v 0) (v 1) (v 2) (v 3) / (Z * (4 * (a + b)))
        ≤ nodeCost ty8 (typedCost ty8 (wt a b)) (fun k => if k ≤ 7 then μ k / Z else 0)
          (fun k τ => ℓ k τ / (Z * (4 * (a + b)))) k v
          + φ (w 0) (w 1) (w 2) (w 3) / (Z * (4 * (a + b)))
      rw [hnode, ← add_div]
      apply div_le_div_of_nonneg_right _ hZD.le
      rcases fin4_cases τ with rfl | rfl | rfl | rfl
      · have hlt : (v 0 : ℕ) < 2 := by
          have h1 := hw' 0
          rw [hτ] at h1
          omega
        rw [hrest 1 (by decide), hrest 2 (by decide), hrest 3 (by decide), hτ]
        exact e.1 hlt
      · have hlt : (v 1 : ℕ) < 2 := by
          have h1 := hw' 1
          rw [hτ] at h1
          omega
        rw [hrest 0 (by decide), hrest 2 (by decide), hrest 3 (by decide), hτ]
        exact e.2.1 hlt
      · have hlt : (v 2 : ℕ) < 2 := by
          have h1 := hw' 2
          rw [hτ] at h1
          omega
        rw [hrest 0 (by decide), hrest 1 (by decide), hrest 3 (by decide), hτ]
        exact e.2.2.1 hlt
      · have hlt : (v 3 : ℕ) < 2 := by
          have h1 := hw' 3
          rw [hτ] at h1
          omega
        rw [hrest 0 (by decide), hrest 1 (by decide), hrest 2 (by decide), hτ]
        exact e.2.2.2 hlt)
    (by
      intro v hv hs
      have hv' := box_le v hv
      have hk' := served_eq v 8 hs
      have b0 := hv' 0
      have b1 := hv' 1
      have b2 := hv' 2
      have b3 := hv' 3
      have e0 : (v 0 : ℕ) = 2 := by omega
      have e1 : (v 1 : ℕ) = 2 := by omega
      have e2 : (v 2 : ℕ) = 2 := by omega
      have e3 : (v 3 : ℕ) = 2 := by omega
      show φ (v 0) (v 1) (v 2) (v 3) / (Z * (4 * (a + b))) = 0
      rw [e0, e1, e2, e3, hend, zero_div])
    (by
      show φ 0 0 0 0 / (Z * (4 * (a + b)))
        ≤ φ ((0 : CState 4 8) 0) ((0 : CState 4 8) 1) ((0 : CState 4 8) 2) ((0 : CState 4 8) 3)
          / (Z * (4 * (a + b)))
      simp)
    η F hF hB
  have hsum : ∑ k ∈ range 8, ∑ τ, |ℓ k τ / (Z * (4 * (a + b)))|
      = (∑ k ∈ range 8, ∑ τ, |ℓ k τ|) / (Z * (4 * (a + b))) := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun τ _ => ?_
    rw [abs_div, abs_of_pos hZD]
  rw [hsum] at key
  have e : (φ 0 0 0 0 - η / 8 * ∑ k ∈ range 8, ∑ τ, |ℓ k τ|) / (Z * (4 * (a + b)))
      = φ 0 0 0 0 / (Z * (4 * (a + b)))
        - η / ((8 : ℕ) : ℝ) * ((∑ k ∈ range 8, ∑ τ, |ℓ k τ|) / (Z * (4 * (a + b)))) := by
    push_cast; ring
  rw [e]; exact key

/-! ## 5. The primal side: mixtures of type sequences -/

/-- The raw cost of a type sequence at budget `k`. -/
noncomputable def rc (a b : ℝ) (s : Fin 8 → Fin 4) (k : Fin 9) : ℝ :=
  |sN a b (stC s k 0) (stC s k 1) (stC s k 2) (stC s k 3)| - trueBaseline (g8 a b) k

/-- **A mixture bounds the value above.** -/
theorem value_le_mixQ (hb : 0 < b) (hab : b < a) {P : ℕ} (s : Fin P → Fin 8 → Fin 4)
    (n : Fin P → ℝ) (Q : ℝ) (hQ : 0 < Q) (hn : ∀ j, 0 ≤ n j) (hn1 : ∑ j, n j = Q)
    (hmult : ∀ j τ, mult (s j) τ = 2) (η : ℝ)
    (hband : ∀ k : ℕ, k ≤ 8 → ∀ τ : Fin 4,
      |∑ j, n j * ((stC (s j) k τ : ℕ) : ℝ) - Q * (k : ℝ) / 4| ≤ Q * η / 4)
    (W : ℝ) (hW : ∀ k ∈ K7, ∑ j, n j * rc a b (s j) k ≤ Q * W) :
    trueValue (g8 a b) η K7 K7_ne ≤ W / (4 * (a + b)) := by
  have hD : 0 < 4 * (a + b) := by linarith
  have hw : ∀ j, 0 ≤ n j / Q := fun j => div_nonneg (hn j) hQ.le
  have hw1 : ∑ j, n j / Q = 1 := by rw [← Finset.sum_div, hn1, div_self hQ.ne']
  apply value_le_of_flow hb hab η (mixFlow s (fun j => n j / Q) hw)
  · exact mixFlow_feasible ty8 s _ hw hw1 (fun j τ => by rw [hmult, mult_ty8])
  · intro k τ _
    rw [mixFlow_mean, mult_ty8]
    have h := hband k (Nat.lt_succ_iff.mp k.isLt) τ
    have e : (∑ j, n j / Q * ((stC (s j) k τ : ℕ) : ℝ)) / ((2 : ℕ) : ℝ) - ((k : ℕ) : ℝ) / ((8 : ℕ) : ℝ)
        = (∑ j, n j * ((stC (s j) k τ : ℕ) : ℝ) - Q * ((k : ℕ) : ℝ) / 4) / (2 * Q) := by
      rw [show ∑ j, n j / Q * ((stC (s j) k τ : ℕ) : ℝ)
          = (∑ j, n j * ((stC (s j) k τ : ℕ) : ℝ)) / Q by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring]
      field_simp; ring
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Q), div_le_iff₀ (by positivity)]
    push_cast
    nlinarith [h]
  · intro k hk
    rw [mixFlow_obj]
    have hc : ∀ j, typedCost ty8 (wt a b) k (stC (s j) k) = rc a b (s j) k / (4 * (a + b)) := by
      intro j; rw [typedCost_eq8 hb hab]; rfl
    simp only [hc]
    have h := hW k hk
    rw [show ∑ j, n j / Q * (rc a b (s j) k / (4 * (a + b)))
        = (∑ j, n j * rc a b (s j) k) / (Q * (4 * (a + b))) by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h hD.le]

theorem stC_le (s : Fin 8 → Fin 4) (hmult : ∀ τ, mult s τ = 2) (k : ℕ) (τ : Fin 4) :
    (stC s k τ : ℕ) ≤ 2 := by
  rw [← hmult τ]; exact cnt_le_mult s (min k 8) τ

/-- **At `η = 8` the band is automatic.** -/
theorem value_le_mixQ_free (hb : 0 < b) (hab : b < a) {P : ℕ} (s : Fin P → Fin 8 → Fin 4)
    (n : Fin P → ℝ) (Q : ℝ) (hQ : 0 < Q) (hn : ∀ j, 0 ≤ n j) (hn1 : ∑ j, n j = Q)
    (hmult : ∀ j τ, mult (s j) τ = 2)
    (W : ℝ) (hW : ∀ k ∈ K7, ∑ j, n j * rc a b (s j) k ≤ Q * W) :
    trueValue (g8 a b) 8 K7 K7_ne ≤ W / (4 * (a + b)) := by
  refine value_le_mixQ hb hab s n Q hQ hn hn1 hmult 8 (fun k hk8 τ => ?_) W hW
  have hlo : 0 ≤ ∑ j, n j * ((stC (s j) k τ : ℕ) : ℝ) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hn j) (Nat.cast_nonneg _)
  have hhi : ∑ j, n j * ((stC (s j) k τ : ℕ) : ℝ) ≤ 2 * Q := by
    rw [← hn1, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := stC_le (s j) (hmult j) k τ
    have : ((stC (s j) k τ : ℕ) : ℝ) ≤ 2 := by exact_mod_cast this
    nlinarith [hn j]
  have hk : (k : ℝ) ≤ 8 := by exact_mod_cast hk8
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> nlinarith

#print axioms base1
#print axioms base3_mid
#print axioms abs_sN_hi
#print axioms abs_sN_lo
#print axioms value_ge_of_flows
#print axioms value_le_of_flow
#print axioms cert8
#print axioms value_le_mixQ
#print axioms value_le_mixQ_free

end CIGAMF.P13.PaperCTwoMag2222
