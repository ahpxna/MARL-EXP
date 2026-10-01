import Mathlib
import «LeanMarlSubsetFrontierV1»

/-!
# T1 of MARL_FINAL_SCOPE_20260927: the revision frontier with a LEARNED score, a LEARNED
# evaluator, an imperfect search and a restricted candidate family

`LeanMarlSubsetFrontierV1.subset_frontier` says a good repair EXISTS when the prefix is top-k by
the TRUE first-order gains.  A deployed selector has none of that: its priority comes from an
estimated score `w`, it scores candidate repairs with an estimated value `fh`, it maximises
`fh` only approximately, and it searches a candidate family `C` that may omit the best reachable
set.  This module states what survives, with every error named.

## Objects

* `f : Finset (Fin m) → ℝ` — the decision value of the broadcast set (fixed controller, fixed
  state; `f` need not be monotone).
* `w : Fin m → ℝ` — ANY per-message score.  `ScoreLocal f w η` says every marginal
  `f (A ∪ {i}) − f A` is within `η` of `w i`.  `η` is the one number a certificate needs.
* `reach P k R` — the reachable family `F_R(P) = {S : |S| = k, |S \ P| ≤ R}`.

## WHAT IS PROVED

* `scoreLocal_of_gain` — true local interaction `δ` and a score within `u` of the true
  first-order gains give `ScoreLocal f w (δ + u)`.
* `value_exchange_w`, `value_exchange_w_lower` — the exchange bound with ANY reference score.
* `score_frontier` — if `P` is top-k by `w`, then for every `R` some `S ∈ F_R(P)` has
  `f T − f S ≤ 2·η·(|P \ T| − R)₊` for every k-set `T`.
* `est_frontier` — the same with `η = δ + u`: the target `2(δ+u)(d_k − R)₊`.
* `deployed_regret` — THE DEPLOYABLE BOUND.  For a selector that returns `Ŝ ∈ C` with
  `fh Ŝ ≥ fh S' − ν` for all `S' ∈ C`, with `|fh − f| ≤ ε` on `C`, and with coverage gap `ζ`
  (every reachable set is within `ζ` of some candidate):
      f T − f Ŝ ≤ 2(δ+u)(|P \ T| − R)₊ + 2ε + ν + ζ    for every k-set T.
* `deployed_regret_enum` — enumerating `C = F_R(P)` removes `ζ`.
* `score_zero_price`, `est_zero_price` — the no-repair certificate: an estimated cut margin of
  at least `2(δ_U + u)`, with `δ ≤ δ_U`, certifies the prefix optimal at that budget.  Only an
  UPPER bound `δ_U` may enter; `δ_U < δ` voids it.
* Sharpness witnesses: `score_error_sharp` (the coefficient `2` on `u` is attained, with
  `δ = 0`), `eval_error_sharp` (the `2ε` is attained by an exact argmax of `fh`).
* `hypotheses_satisfiable` — every hypothesis is met by a concrete instance with nonzero
  `u`, `ε` and a non-vacuous candidate family.

## WHAT THIS DOES NOT ESTABLISH

- That any learner achieves small `u`, `ε`, `ν`, `ζ`; these are the inputs of T2 and of the
  experiments.  A TD loss is not `ε` (it bounds a different functional).
- That a greedy swap search has `ζ = 0`; `ζ` is whatever the candidate generator leaves out.
- Anything about `δ` being known: `δ_U` must be an upper confidence bound.  `delta_pair`
  (pairwise differences) is a lower diagnostic and does not bound `η`.
-/

namespace CIGAMF.P13.MarlEstimatedRevision

open Finset CIGAMF.P13.MarlSubsetFrontier

variable {m : ℕ}

/-- Every marginal is within `η` of the score `w`. -/
def ScoreLocal (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (η : ℝ) : Prop :=
  ∀ (A : Finset (Fin m)) (i : Fin m), i ∉ A → |f (insert i A) - f A - w i| ≤ η

/-- The reachable family `F_R(P)` at budget `k`. -/
def Reach (P : Finset (Fin m)) (k R : ℕ) (S : Finset (Fin m)) : Prop :=
  S.card = k ∧ (S \ P).card ≤ R

/-- True local interaction plus a score error `u` on the first-order gains. -/
theorem scoreLocal_of_gain (f : Finset (Fin m) → ℝ) (delta u : ℝ) (w : Fin m → ℝ)
    (h : LocalInteraction f delta) (hu : ∀ i, |w i - gain f i| ≤ u) :
    ScoreLocal f w (delta + u) := by
  intro A i hi
  have h1 := h A i hi
  have h2 := hu i
  have he : f (insert i A) - f A - w i = (f (insert i A) - f A - gain f i) - (w i - gain f i) := by
    ring
  rw [he]
  calc |(f (insert i A) - f A - gain f i) - (w i - gain f i)|
      ≤ |f (insert i A) - f A - gain f i| + |w i - gain f i| := abs_sub _ _
    _ ≤ delta + u := add_le_add h1 h2

/-- The residual against the score. -/
def residW (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (S : Finset (Fin m)) : ℝ := f S - S.sum w

theorem residW_step (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (η : ℝ) (h : ScoreLocal f w η)
    (A : Finset (Fin m)) (i : Fin m) (hi : i ∉ A) :
    |residW f w (insert i A) - residW f w A| ≤ η := by
  unfold residW
  rw [Finset.sum_insert hi]
  have he : f (insert i A) - (w i + A.sum w) - (f A - A.sum w) = f (insert i A) - f A - w i := by
    ring
  rw [he]; exact h A i hi

theorem residW_union_le (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (η : ℝ) (h : ScoreLocal f w η)
    (B C : Finset (Fin m)) (hBC : Disjoint B C) :
    |residW f w (B ∪ C) - residW f w B| ≤ (C.card : ℝ) * η := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert i C hi ih =>
      have hBC' : Disjoint B C := Finset.disjoint_of_subset_right (Finset.subset_insert i C) hBC
      have hiB : i ∉ B := by
        intro hiB; exact Finset.disjoint_left.mp hBC hiB (Finset.mem_insert_self i C)
      have hiBC : i ∉ B ∪ C := by
        rw [Finset.mem_union]; push Not; exact ⟨hiB, hi⟩
      have hstep := residW_step f w η h (B ∪ C) i hiBC
      have hunion : B ∪ insert i C = insert i (B ∪ C) := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [hunion, Finset.card_insert_of_notMem hi]
      have hih := ih hBC'
      have htri : |residW f w (insert i (B ∪ C)) - residW f w B| ≤
          |residW f w (insert i (B ∪ C)) - residW f w (B ∪ C)| +
            |residW f w (B ∪ C) - residW f w B| := abs_sub_le _ _ _
      push_cast
      linarith

theorem residW_diff (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (η : ℝ) (h : ScoreLocal f w η)
    (S T : Finset (Fin m)) :
    |residW f w S - residW f w T| ≤ (((S \ T).card + (T \ S).card : ℕ) : ℝ) * η := by
  have hS : S = (S ∩ T) ∪ (S \ T) := by
    rw [Finset.union_comm]; exact (Finset.sdiff_union_inter S T).symm
  have hT : T = (S ∩ T) ∪ (T \ S) := by
    rw [Finset.inter_comm, Finset.union_comm]; exact (Finset.sdiff_union_inter T S).symm
  have h1 := residW_union_le f w η h (S ∩ T) (S \ T)
    (Finset.disjoint_of_subset_left Finset.inter_subset_right Finset.disjoint_sdiff)
  have h2 := residW_union_le f w η h (S ∩ T) (T \ S)
    (Finset.disjoint_of_subset_left Finset.inter_subset_left Finset.disjoint_sdiff)
  rw [← hS] at h1
  rw [← hT] at h2
  have htri : |residW f w S - residW f w T| ≤
      |residW f w S - residW f w (S ∩ T)| + |residW f w T - residW f w (S ∩ T)| := by
    have := abs_sub_le (residW f w S) (residW f w (S ∩ T)) (residW f w T)
    rw [abs_sub_comm (residW f w (S ∩ T)) (residW f w T)] at this
    exact this
  push_cast
  nlinarith [abs_nonneg (residW f w S - residW f w (S ∩ T)),
    abs_nonneg (residW f w T - residW f w (S ∩ T))]

/-- Exchange bound against ANY score. -/
theorem value_exchange_w (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (η : ℝ) (h : ScoreLocal f w η)
    (S T : Finset (Fin m)) :
    f T - f S ≤ (T \ S).sum w - (S \ T).sum w + (((S \ T).card + (T \ S).card : ℕ) : ℝ) * η := by
  have hd := residW_diff f w η h S T
  have hs : T.sum w - S.sum w = (T \ S).sum w - (S \ T).sum w := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
  unfold residW at hd
  have := (abs_le.mp hd).1
  linarith

theorem value_exchange_w_lower (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (η : ℝ)
    (h : ScoreLocal f w η) (S T : Finset (Fin m)) :
    (T \ S).sum w - (S \ T).sum w - (((S \ T).card + (T \ S).card : ℕ) : ℝ) * η ≤ f T - f S := by
  have hd := residW_diff f w η h S T
  have hs : T.sum w - S.sum w = (T \ S).sum w - (S \ T).sum w := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
  unfold residW at hd
  have := (abs_le.mp hd).2
  linarith

/-- **Frontier with any score.**  `P` top-k by `w`; some `S ∈ F_R(P)` is within
`2·η·(|P \ T| − R)₊` of every k-set `T`. -/
theorem score_frontier (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (η : ℝ) (h : ScoreLocal f w η)
    (P T : Finset (Fin m)) (k R : ℕ) (hP : P.card = k) (hT : T.card = k)
    (hTop : ∀ i ∈ P, ∀ j ∉ P, w j ≤ w i) :
    ∃ S : Finset (Fin m), Reach P k R S ∧
      f T - f S ≤ 2 * (((P \ T).card - R : ℕ) : ℝ) * η := by
  obtain ⟨S, hS, hSP, hSsub, hTout, hcard⟩ := exchange_path P T k R hP hT
  refine ⟨S, ⟨hS, hSP⟩, ?_⟩
  have hv := value_exchange_w f w η h S T
  have hc : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm (hS.trans hT.symm)
  have hord : ∀ i ∈ S \ T, ∀ j ∈ T \ S, w j ≤ w i :=
    fun i hi j hj => hTop i (hSsub hi) j (hTout j hj)
  have hsum := sum_le_of_pointwise (S \ T) (T \ S) w hc hord
  rw [← hc, hcard] at hv
  push_cast at hv ⊢
  linarith

/-- **The estimated-score frontier** `2(δ+u)(d − R)₊`. -/
theorem est_frontier (f : Finset (Fin m) → ℝ) (delta u : ℝ) (w : Fin m → ℝ)
    (h : LocalInteraction f delta) (hu : ∀ i, |w i - gain f i| ≤ u)
    (P T : Finset (Fin m)) (k R : ℕ) (hP : P.card = k) (hT : T.card = k)
    (hTop : ∀ i ∈ P, ∀ j ∉ P, w j ≤ w i) :
    ∃ S : Finset (Fin m), Reach P k R S ∧
      f T - f S ≤ 2 * (((P \ T).card - R : ℕ) : ℝ) * (delta + u) :=
  score_frontier f w (delta + u) (scoreLocal_of_gain f delta u w h hu) P T k R hP hT hTop

/-- **The deployable regret bound.**  `C` is the candidate family actually searched, `fh` the
learned evaluator, `Ŝ` the returned set.  The four errors enter additively and separately. -/
theorem deployed_regret (f fh : Finset (Fin m) → ℝ) (delta u eps nu zeta : ℝ) (w : Fin m → ℝ)
    (h : LocalInteraction f delta) (hu : ∀ i, |w i - gain f i| ≤ u)
    (P T : Finset (Fin m)) (k R : ℕ) (hP : P.card = k) (hT : T.card = k)
    (hTop : ∀ i ∈ P, ∀ j ∉ P, w j ≤ w i)
    (C : Finset (Finset (Fin m))) (Shat : Finset (Fin m)) (hShat : Shat ∈ C)
    (hEval : ∀ S ∈ C, |fh S - f S| ≤ eps)
    (hSearch : ∀ S ∈ C, fh S ≤ fh Shat + nu)
    (hCover : ∀ S, Reach P k R S → ∃ S' ∈ C, f S ≤ f S' + zeta) :
    f T - f Shat ≤ 2 * (((P \ T).card - R : ℕ) : ℝ) * (delta + u) + 2 * eps + nu + zeta := by
  obtain ⟨S, hS, hST⟩ := est_frontier f delta u w h hu P T k R hP hT hTop
  obtain ⟨S', hS'C, hS'⟩ := hCover S hS
  have e1 := (abs_le.mp (hEval S' hS'C)).1
  have e2 := (abs_le.mp (hEval Shat hShat)).2
  have s1 := hSearch S' hS'C
  linarith

/-- Enumerating the whole reachable family removes the coverage gap. -/
theorem deployed_regret_enum (f fh : Finset (Fin m) → ℝ) (delta u eps nu : ℝ) (w : Fin m → ℝ)
    (h : LocalInteraction f delta) (hu : ∀ i, |w i - gain f i| ≤ u)
    (P T : Finset (Fin m)) (k R : ℕ) (hP : P.card = k) (hT : T.card = k)
    (hTop : ∀ i ∈ P, ∀ j ∉ P, w j ≤ w i)
    (C : Finset (Finset (Fin m))) (hC : ∀ S, Reach P k R S → S ∈ C)
    (Shat : Finset (Fin m)) (hShat : Shat ∈ C)
    (hEval : ∀ S ∈ C, |fh S - f S| ≤ eps)
    (hSearch : ∀ S ∈ C, fh S ≤ fh Shat + nu) :
    f T - f Shat ≤ 2 * (((P \ T).card - R : ℕ) : ℝ) * (delta + u) + 2 * eps + nu := by
  have := deployed_regret f fh delta u eps nu 0 w h hu P T k R hP hT hTop C Shat hShat hEval
    hSearch (fun S hS => ⟨S, hC S hS, by linarith⟩)
  linarith

/-- Monotonicity of the hypothesis in `η`. -/
theorem scoreLocal_mono (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) {η η' : ℝ}
    (h : ScoreLocal f w η) (hle : η ≤ η') : ScoreLocal f w η' :=
  fun A i hi => (h A i hi).trans hle

/-- **No-repair certificate with any score**: a cut margin of `2η_U`, `η ≤ η_U`. -/
theorem score_zero_price (f : Finset (Fin m) → ℝ) (w : Fin m → ℝ) (η ηU : ℝ)
    (h : ScoreLocal f w η) (hU : η ≤ ηU)
    (P T : Finset (Fin m)) (hcard : T.card = P.card)
    (hMargin : ∀ i ∈ P, ∀ j ∉ P, 2 * ηU + w j ≤ w i) :
    f T ≤ f P := by
  have hv := value_exchange_w f w ηU (scoreLocal_mono f w h hU) P T
  have hc : (P \ T).card = (T \ P).card := Finset.card_sdiff_comm hcard.symm
  have hs := surplus_ge_card_mul' (P \ T) (T \ P) w (2 * ηU) hc
    (fun i hi j hj => hMargin i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2)
  rw [← hc] at hv
  push_cast at hv
  nlinarith

/-- **The certificate with an estimated score**: margin `2(δ_U + u)`, `δ ≤ δ_U`. -/
theorem est_zero_price (f : Finset (Fin m) → ℝ) (delta deltaU u : ℝ) (w : Fin m → ℝ)
    (h : LocalInteraction f delta) (hu : ∀ i, |w i - gain f i| ≤ u) (hU : delta ≤ deltaU)
    (P T : Finset (Fin m)) (hcard : T.card = P.card)
    (hMargin : ∀ i ∈ P, ∀ j ∉ P, 2 * (deltaU + u) + w j ≤ w i) :
    f T ≤ f P :=
  score_zero_price f w (delta + u) (deltaU + u) (scoreLocal_of_gain f delta u w h hu)
    (by linarith) P T hcard hMargin

/-! ## Sharpness of the two new coefficients -/

/-- Weights `(0, 2)`. -/
def wTwo (i : Fin 2) : ℝ := if i = 1 then 2 else 0

/-- A modular value on two messages: `f {1} = 2`, everything else additive. -/
def modTwo (S : Finset (Fin 2)) : ℝ := 0 + S.sum wTwo

/-- **The coefficient `2` on the score error is attained**, with `δ = 0`: gains `(0, 2)`, a
score `(1, 1)` within `u = 1` of them, the tie broken toward message `0`. -/
theorem score_error_sharp :
    ∃ (f : Finset (Fin 2) → ℝ) (w : Fin 2 → ℝ) (u : ℝ) (P T : Finset (Fin 2)),
      LocalInteraction f 0 ∧ (∀ i, |w i - gain f i| ≤ u) ∧ P.card = 1 ∧ T.card = 1 ∧
      (∀ i ∈ P, ∀ j ∉ P, w j ≤ w i) ∧ (P \ T).card = 1 ∧
      f T - f P = 2 * ((P \ T).card : ℝ) * (0 + u) := by
  have hmod : LocalInteraction modTwo 0 := modular_zero wTwo 0
  have hg0 : gain modTwo 0 = 0 := by simp [gain, modTwo, wTwo]
  have hg1 : gain modTwo 1 = 2 := by simp [gain, modTwo, wTwo]
  refine ⟨modTwo, fun _ => 1, 1, {0}, {1}, hmod, ?_, by decide, by decide, ?_, by decide, ?_⟩
  · intro i; fin_cases i
    · simp [hg0]
    · simp [hg1]; norm_num
  · intro i _ j _; exact le_refl _
  · have hc : (({0} : Finset (Fin 2)) \ {1}).card = 1 := by decide
    rw [hc]; simp [modTwo, wTwo]

/-- **The `2ε` is attained by an exact argmax of the evaluator**: two candidates whose true
values differ by `2ε`, each evaluated `ε` toward the other; the argmax may return the worse. -/
theorem eval_error_sharp (eps : ℝ) (heps : 0 ≤ eps) :
    ∃ (f fh : Finset (Fin 2) → ℝ) (C : Finset (Finset (Fin 2))) (Shat T : Finset (Fin 2)),
      Shat ∈ C ∧ T ∈ C ∧ (∀ S ∈ C, |fh S - f S| ≤ eps) ∧ (∀ S ∈ C, fh S ≤ fh Shat) ∧
      f T - f Shat = 2 * eps := by
  refine ⟨fun S => if S = {1} then 2 * eps else 0, fun S => if S = {1} then eps else eps,
    {{0}, {1}}, {0}, {1}, by simp, by simp, ?_, ?_, ?_⟩
  · intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · simp [abs_of_nonneg heps]
    · simp; rw [show eps - 2 * eps = -eps by ring, abs_neg, abs_of_nonneg heps]
  · intro S _; simp
  · simp

/-! ## Satisfiability -/

/-- All hypotheses of `deployed_regret` hold on a concrete instance with `u = 1`, `ε = 1/2`,
`ν = 0`, `ζ = 0`, a candidate family equal to `F_1(P)` and a non-prefix return. -/
theorem hypotheses_satisfiable :
    ∃ (f fh : Finset (Fin 2) → ℝ) (w : Fin 2 → ℝ) (P : Finset (Fin 2))
      (C : Finset (Finset (Fin 2))) (Shat : Finset (Fin 2)),
      LocalInteraction f 0 ∧ (∀ i, |w i - gain f i| ≤ 1) ∧ P.card = 1 ∧
      (∀ i ∈ P, ∀ j ∉ P, w j ≤ w i) ∧ (∀ S, Reach P 1 1 S → S ∈ C) ∧ Shat ∈ C ∧
      (∀ S ∈ C, |fh S - f S| ≤ 1 / 2) ∧ (∀ S ∈ C, fh S ≤ fh Shat + 0) ∧ Shat ≠ P := by
  have hmod : LocalInteraction modTwo 0 := modular_zero wTwo 0
  have hg0 : gain modTwo 0 = 0 := by simp [gain, modTwo, wTwo]
  have hg1 : gain modTwo 1 = 2 := by simp [gain, modTwo, wTwo]
  refine ⟨modTwo, fun S => modTwo S + 1 / 2, fun _ => 1, {0}, {{0}, {1}}, {1}, hmod, ?_,
    by decide, ?_, ?_, by simp, ?_, ?_, by decide⟩
  · intro i; fin_cases i
    · simp [hg0]
    · simp [hg1]; norm_num
  · intro i _ j _; exact le_refl _
  · intro S ⟨hS, _⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
    fin_cases a <;> simp
  · intro S _; norm_num [abs_of_nonneg]
  · intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl <;> simp [modTwo, wTwo]

end CIGAMF.P13.MarlEstimatedRevision

#print axioms CIGAMF.P13.MarlEstimatedRevision.scoreLocal_of_gain
#print axioms CIGAMF.P13.MarlEstimatedRevision.value_exchange_w
#print axioms CIGAMF.P13.MarlEstimatedRevision.value_exchange_w_lower
#print axioms CIGAMF.P13.MarlEstimatedRevision.score_frontier
#print axioms CIGAMF.P13.MarlEstimatedRevision.est_frontier
#print axioms CIGAMF.P13.MarlEstimatedRevision.deployed_regret
#print axioms CIGAMF.P13.MarlEstimatedRevision.deployed_regret_enum
#print axioms CIGAMF.P13.MarlEstimatedRevision.score_zero_price
#print axioms CIGAMF.P13.MarlEstimatedRevision.est_zero_price
#print axioms CIGAMF.P13.MarlEstimatedRevision.score_error_sharp
#print axioms CIGAMF.P13.MarlEstimatedRevision.eval_error_sharp
#print axioms CIGAMF.P13.MarlEstimatedRevision.hypotheses_satisfiable
