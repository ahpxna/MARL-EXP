import Mathlib
import «LeanProductSurrogateV4»

/-!
# The revision frontier for the DECISION-VALUE objective (any set function)

`f : Finset (Fin m) → ℝ` is the value of the team decision taken when the messages in `S` are
heard, evaluated at the true state.  `g i = f {i} − f ∅` is the first-order gain of message
`i`.  The single interaction hypothesis is local:

    |f (A ∪ {i}) − f A − g i| ≤ δ      for every context A ∌ i,

i.e. the i-versus-rest mixed difference at every context is at most `δ`.  `bridge_mixed`
shows that D6's `mixedDifference` bound on the Boolean cube implies it.

## WHAT IS PROVED

* `resid_diff` — the residual `f − Σ g` moves by at most `δ` per added or removed element.
* `value_exchange` — for ANY `S`, `T`:
  `f T − f S ≤ σ_g(T \ S) − σ_g(S \ T) + (|S \ T| + |T \ S|)·δ`.  `value_exchange_lower` is the
  mirror image.
* `exchange_path` — pure combinatorics: from a k-set `P` toward a k-set `T`, `R` exchanges
  reach a k-set `S` with `|S \ P| ≤ R`, `S \ T ⊆ P`, `T \ S` outside `P`, and
  `|S \ T| = |P \ T| − R` (natural subtraction).
* `subset_frontier` — THE FRONTIER.  If `P` is a top-k set by gain, then for every `R` there is
  a k-set `S` with at most `R` replacements whose value is within `2·(|P \ T| − R)₊·δ` of any
  k-set `T`, in particular of the best one.
* `subset_price_le` — no revision: price ≤ `2·|P \ T|·δ ≤ 2·min(k, m − k)·δ`.
* `subset_zero_price` — nesting is FREE when every cut margin of the gains is at least `2δ`:
  the gain-ranking prefix is optimal at that budget.
* `bridge_mixed` — D6's `|mixedDifference F i x c| ≤ δ` on `Fin m → Bool`, with
  `f S = F (1_S)`, implies the local hypothesis.
* `subset_hypotheses_satisfiable` — every set function satisfies the hypothesis with some `δ`.
* `subset_constant_sharp` — the constant `2` is attained exactly, on three messages.

## WHAT THIS DOES NOT ESTABLISH

- A family attaining the frontier at EVERY `R` for this objective.  The constant `2` itself is
  attained (`subset_constant_sharp`, three messages, all gains tied).
- Anything about expected return.  `f` is a value table; the bridge to a learned critic is an
  estimation statement that is not made here.
-/

namespace CIGAMF.P13.MarlSubsetFrontier

open Finset

variable {m : ℕ}

/-- First-order gain of message `i`. -/
def gain (f : Finset (Fin m) → ℝ) (i : Fin m) : ℝ := f {i} - f ∅

/-- The residual `f − Σ gains`. -/
def resid (f : Finset (Fin m) → ℝ) (S : Finset (Fin m)) : ℝ := f S - S.sum (gain f)

/-- The local interaction hypothesis. -/
def LocalInteraction (f : Finset (Fin m) → ℝ) (delta : ℝ) : Prop :=
  ∀ (A : Finset (Fin m)) (i : Fin m), i ∉ A → |f (insert i A) - f A - gain f i| ≤ delta

theorem resid_step (f : Finset (Fin m) → ℝ) (delta : ℝ) (h : LocalInteraction f delta)
    (A : Finset (Fin m)) (i : Fin m) (hi : i ∉ A) :
    |resid f (insert i A) - resid f A| ≤ delta := by
  unfold resid
  rw [Finset.sum_insert hi]
  have := h A i hi
  have he : f (insert i A) - (gain f i + A.sum (gain f)) - (f A - A.sum (gain f)) =
      f (insert i A) - f A - gain f i := by ring
  rw [he]; exact this

/-- Adding a disjoint block `C` moves the residual by at most `|C|·δ`. -/
theorem resid_union_le (f : Finset (Fin m) → ℝ) (delta : ℝ) (h : LocalInteraction f delta)
    (B C : Finset (Fin m)) (hBC : Disjoint B C) :
    |resid f (B ∪ C) - resid f B| ≤ (C.card : ℝ) * delta := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert i C hi ih =>
      have hBC' : Disjoint B C := Finset.disjoint_of_subset_right (Finset.subset_insert i C) hBC
      have hiB : i ∉ B := by
        intro hiB; exact Finset.disjoint_left.mp hBC hiB (Finset.mem_insert_self i C)
      have hiBC : i ∉ B ∪ C := by
        rw [Finset.mem_union]; push Not; exact ⟨hiB, hi⟩
      have hstep := resid_step f delta h (B ∪ C) i hiBC
      have hunion : B ∪ insert i C = insert i (B ∪ C) := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [hunion, Finset.card_insert_of_notMem hi]
      have hih := ih hBC'
      have htri : |resid f (insert i (B ∪ C)) - resid f B| ≤
          |resid f (insert i (B ∪ C)) - resid f (B ∪ C)| + |resid f (B ∪ C) - resid f B| :=
        abs_sub_le _ _ _
      push_cast
      linarith

/-- The residual is `δ`-Lipschitz in the symmetric difference. -/
theorem resid_diff (f : Finset (Fin m) → ℝ) (delta : ℝ) (h : LocalInteraction f delta)
    (S T : Finset (Fin m)) :
    |resid f S - resid f T| ≤ (((S \ T).card + (T \ S).card : ℕ) : ℝ) * delta := by
  have hS : S = (S ∩ T) ∪ (S \ T) := by
    rw [Finset.union_comm]; exact (Finset.sdiff_union_inter S T).symm
  have hT : T = (S ∩ T) ∪ (T \ S) := by
    rw [Finset.inter_comm, Finset.union_comm]; exact (Finset.sdiff_union_inter T S).symm
  have h1 := resid_union_le f delta h (S ∩ T) (S \ T)
    (Finset.disjoint_of_subset_left Finset.inter_subset_right Finset.disjoint_sdiff)
  have h2 := resid_union_le f delta h (S ∩ T) (T \ S)
    (Finset.disjoint_of_subset_left Finset.inter_subset_left Finset.disjoint_sdiff)
  rw [← hS] at h1
  rw [← hT] at h2
  have htri : |resid f S - resid f T| ≤
      |resid f S - resid f (S ∩ T)| + |resid f T - resid f (S ∩ T)| := by
    have := abs_sub_le (resid f S) (resid f (S ∩ T)) (resid f T)
    rw [abs_sub_comm (resid f (S ∩ T)) (resid f T)] at this
    exact this
  push_cast
  nlinarith [abs_nonneg (resid f S - resid f (S ∩ T)), abs_nonneg (resid f T - resid f (S ∩ T))]

/-- **Value exchange** for ANY two sets. -/
theorem value_exchange (f : Finset (Fin m) → ℝ) (delta : ℝ) (h : LocalInteraction f delta)
    (S T : Finset (Fin m)) :
    f T - f S ≤ (T \ S).sum (gain f) - (S \ T).sum (gain f) +
      (((S \ T).card + (T \ S).card : ℕ) : ℝ) * delta := by
  have hd := resid_diff f delta h S T
  have hs : T.sum (gain f) - S.sum (gain f) = (T \ S).sum (gain f) - (S \ T).sum (gain f) := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
  unfold resid at hd
  have := (abs_le.mp hd).1
  linarith

/-- The mirror image: a lower bound on the value difference. -/
theorem value_exchange_lower (f : Finset (Fin m) → ℝ) (delta : ℝ) (h : LocalInteraction f delta)
    (S T : Finset (Fin m)) :
    (T \ S).sum (gain f) - (S \ T).sum (gain f) -
      (((S \ T).card + (T \ S).card : ℕ) : ℝ) * delta ≤ f T - f S := by
  have hd := resid_diff f delta h S T
  have hs : T.sum (gain f) - S.sum (gain f) = (T \ S).sum (gain f) - (S \ T).sum (gain f) := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
  unfold resid at hd
  have := (abs_le.mp hd).2
  linarith

/-- Sum comparison under a pointwise order, for equal cardinalities. -/
theorem sum_le_of_pointwise {I : Type*} [DecidableEq I]
    (A B : Finset I) (score : I → ℝ) (hCard : A.card = B.card)
    (hOrder : ∀ i ∈ A, ∀ j ∈ B, score j ≤ score i) :
    B.sum score ≤ A.sum score := by
  by_cases hB : B.Nonempty
  · obtain ⟨b, hb, hmax⟩ := B.exists_max_image score hB
    have ha : (A.card : ℝ) * score b ≤ A.sum score := by
      calc (A.card : ℝ) * score b = A.sum (fun _ => score b) := by
            rw [Finset.sum_const, nsmul_eq_mul]
           _ ≤ _ := Finset.sum_le_sum (fun i hi => hOrder i hi b hb)
    have hbSum : B.sum score ≤ (A.card : ℝ) * score b := by
      calc B.sum score ≤ B.sum (fun _ => score b) :=
            Finset.sum_le_sum (fun j hj => hmax j hj)
           _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hCard]
    linarith
  · have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hAe : A = ∅ := Finset.card_eq_zero.mp (by simpa [hBe] using hCard)
    simp [hAe, hBe]

/-- Sum comparison with a common margin `mu`. -/
theorem surplus_ge_card_mul' {I : Type*} [DecidableEq I]
    (A B : Finset I) (score : I → ℝ) (mu : ℝ) (hCard : A.card = B.card)
    (hMargin : ∀ i ∈ A, ∀ j ∈ B, mu + score j ≤ score i) :
    (A.card : ℝ) * mu ≤ A.sum score - B.sum score := by
  by_cases hB : B.Nonempty
  · obtain ⟨b, hb, hmax⟩ := B.exists_max_image score hB
    have ha : (A.card : ℝ) * (mu + score b) ≤ A.sum score := by
      calc (A.card : ℝ) * (mu + score b) = A.sum (fun _ => mu + score b) := by
            rw [Finset.sum_const, nsmul_eq_mul]
           _ ≤ _ := Finset.sum_le_sum (fun i hi => hMargin i hi b hb)
    have hbSum : B.sum score ≤ (A.card : ℝ) * score b := by
      calc B.sum score ≤ B.sum (fun _ => score b) :=
            Finset.sum_le_sum (fun j hj => hmax j hj)
           _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hCard]
    nlinarith
  · have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hAe : A = ∅ := Finset.card_eq_zero.mp (by simpa [hBe] using hCard)
    simp [hAe, hBe]

/-- **Exchange path** (pure combinatorics).  From a k-set `P` toward a k-set `T`, `R` exchanges
reach a k-set `S` on the path with `|S \ T| = |P \ T| − R`. -/
theorem exchange_path (P T : Finset (Fin m)) (k R : ℕ) (hP : P.card = k) (hT : T.card = k) :
    ∃ S : Finset (Fin m), S.card = k ∧ (S \ P).card ≤ R ∧ S \ T ⊆ P ∧
      (∀ j ∈ T \ S, j ∉ P) ∧ (S \ T).card = (P \ T).card - R := by
  have hdc : (P \ T).card = (T \ P).card := Finset.card_sdiff_comm (hP.trans hT.symm)
  by_cases hR : (P \ T).card ≤ R
  · refine ⟨T, hT, ?_, by simp, by simp, by simp; omega⟩
    rw [← hdc]; exact hR
  · push Not at hR
    obtain ⟨X, hXsub, hXcard⟩ := Finset.exists_subset_card_eq (s := P \ T) (n := R) hR.le
    obtain ⟨Y, hYsub, hYcard⟩ :=
      Finset.exists_subset_card_eq (s := T \ P) (n := R) (by rw [← hdc]; exact hR.le)
    let S := (P \ X) ∪ Y
    have hYP : Disjoint (P \ X) Y := by
      rw [Finset.disjoint_left]
      intro j hj hjY
      exact (Finset.mem_sdiff.mp (hYsub hjY)).2 (Finset.mem_sdiff.mp hj).1
    have hXP : X ⊆ P := fun j hj => (Finset.mem_sdiff.mp (hXsub hj)).1
    have hScard : S.card = k := by
      have h1 : S.card = (P \ X).card + Y.card := Finset.card_union_of_disjoint hYP
      have h2 : (P \ X).card = P.card - X.card := Finset.card_sdiff_of_subset hXP
      have h3 : X.card ≤ P.card := Finset.card_le_card hXP
      omega
    have hST : S \ T = (P \ T) \ X := by
      ext j
      simp only [S, Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hj | hj, hjT⟩
        · exact ⟨⟨hj.1, hjT⟩, hj.2⟩
        · exact absurd (Finset.mem_sdiff.mp (hYsub hj)).1 hjT
      · rintro ⟨⟨hjP, hjT⟩, hjX⟩
        exact ⟨Or.inl ⟨hjP, hjX⟩, hjT⟩
    refine ⟨S, hScard, ?_, ?_, ?_, ?_⟩
    · have : S \ P ⊆ Y := by
        intro j hj
        rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hj).1 with hj' | hj'
        · exact absurd (Finset.mem_sdiff.mp hj').1 (Finset.mem_sdiff.mp hj).2
        · exact hj'
      calc (S \ P).card ≤ Y.card := Finset.card_le_card this
        _ = R := hYcard
    · rw [hST]; intro j hj
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1).1
    · intro j hj hjP
      have hjT : j ∈ T := (Finset.mem_sdiff.mp hj).1
      have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
      have hjX : j ∈ X := by
        by_contra hjX
        exact hjS (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hjP, hjX⟩)))
      exact (Finset.mem_sdiff.mp (hXsub hjX)).2 hjT
    · rw [hST, Finset.card_sdiff_of_subset hXsub, hXcard]

/-- **The decision-value frontier.**  If `P` is a top-k set by first-order gain (every member's
gain ≥ every non-member's), then for every `R` there is a k-set `S` with at most `R`
replacements with `f T − f S ≤ 2·(|P \ T| − R)₊·δ`, for any k-set `T`. -/
theorem subset_frontier (f : Finset (Fin m) → ℝ) (delta : ℝ) (h : LocalInteraction f delta)
    (P T : Finset (Fin m)) (k R : ℕ) (hP : P.card = k) (hT : T.card = k)
    (hTop : ∀ i ∈ P, ∀ j ∉ P, gain f j ≤ gain f i) :
    ∃ S : Finset (Fin m), S.card = k ∧ (S \ P).card ≤ R ∧
      f T - f S ≤ 2 * (((P \ T).card - R : ℕ) : ℝ) * delta := by
  obtain ⟨S, hS, hSP, hSsub, hTout, hcard⟩ := exchange_path P T k R hP hT
  refine ⟨S, hS, hSP, ?_⟩
  have hv := value_exchange f delta h S T
  have hc : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm (hS.trans hT.symm)
  have hord : ∀ i ∈ S \ T, ∀ j ∈ T \ S, gain f j ≤ gain f i :=
    fun i hi j hj => hTop i (hSsub hi) j (hTout j hj)
  have hsum := sum_le_of_pointwise (S \ T) (T \ S) (gain f) hc hord
  rw [← hc, hcard] at hv
  push_cast at hv ⊢
  linarith

/-- No revision: the price of the gain ranking is at most `2·|P \ T|·δ ≤ 2·min(k, m−k)·δ`. -/
theorem subset_price_le (f : Finset (Fin m) → ℝ) (delta : ℝ) (h : LocalInteraction f delta)
    (hd : 0 ≤ delta) (P T : Finset (Fin m)) (k : ℕ) (hP : P.card = k) (hT : T.card = k)
    (hTop : ∀ i ∈ P, ∀ j ∉ P, gain f j ≤ gain f i) :
    f T - f P ≤ 2 * ((P \ T).card : ℝ) * delta ∧
      2 * ((P \ T).card : ℝ) * delta ≤ 2 * ((min k (m - k) : ℕ) : ℝ) * delta := by
  constructor
  · have hv := value_exchange f delta h P T
    have hc : (P \ T).card = (T \ P).card := Finset.card_sdiff_comm (hP.trans hT.symm)
    have hord : ∀ i ∈ P \ T, ∀ j ∈ T \ P, gain f j ≤ gain f i :=
      fun i hi j hj => hTop i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2
    have hsum := sum_le_of_pointwise (P \ T) (T \ P) (gain f) hc hord
    rw [← hc] at hv
    push_cast at hv
    linarith
  · have h1 : (P \ T).card ≤ k := hP ▸ Finset.card_le_card Finset.sdiff_subset
    have h2 : (P \ T).card ≤ m - k := by
      have hsub : P \ T ⊆ Tᶜ := by
        intro j hj; exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hj).2
      have := Finset.card_le_card hsub
      rwa [Finset.card_compl, Fintype.card_fin, hT] at this
    have hmin : ((P \ T).card : ℝ) ≤ ((min k (m - k) : ℕ) : ℝ) := by exact_mod_cast le_min h1 h2
    nlinarith

/-- **Nesting is free under a `2δ` gain margin**: the gain prefix is optimal at its budget. -/
theorem subset_zero_price (f : Finset (Fin m) → ℝ) (delta : ℝ) (h : LocalInteraction f delta)
    (P T : Finset (Fin m)) (hcard : T.card = P.card)
    (hMargin : ∀ i ∈ P, ∀ j ∉ P, 2 * delta + gain f j ≤ gain f i) :
    f T ≤ f P := by
  have hv := value_exchange f delta h P T
  have hc : (P \ T).card = (T \ P).card := Finset.card_sdiff_comm hcard.symm
  have hs := surplus_ge_card_mul' (P \ T) (T \ P) (gain f) (2 * delta) hc
    (fun i hi j hj => hMargin i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2)
  rw [← hc] at hv
  push_cast at hv
  nlinarith

/-! ## Bridge to D6's mixed difference, and satisfiability -/

open CIGAMF.V4.ProductSurrogate in
/-- D6's `mixedDifference` bound on the Boolean cube implies the local hypothesis for
`f S = F (1_S)`: take `x = 1_{A ∪ {i}}` and `c = 0`. -/
theorem bridge_mixed (F : (Fin m → Bool) → ℝ) (delta : ℝ)
    (hdelta : ∀ (i : Fin m) (x c : Fin m → Bool), |mixedDifference F i x c| ≤ delta) :
    LocalInteraction (fun S => F (fun j => decide (j ∈ S))) delta := by
  intro A i hi
  have := hdelta i (fun j => decide (j ∈ insert i A)) (fun _ => false)
  unfold mixedDifference at this
  have h1 : Function.update (fun j => decide (j ∈ insert i A)) i false =
      fun j => decide (j ∈ A) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [Function.update, hj, Finset.mem_insert]
  have h2 : Function.update (fun _ : Fin m => false) i (decide (i ∈ insert i A)) =
      fun j => decide (j ∈ ({i} : Finset (Fin m))) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update, hj]
  have h3 : (fun _ : Fin m => false) = fun j => decide (j ∈ (∅ : Finset (Fin m))) := by
    funext j; simp
  rw [h1, h2, h3] at this
  unfold gain
  have he : F (fun j => decide (j ∈ insert i A)) - F (fun j => decide (j ∈ A)) -
      (F (fun j => decide (j ∈ ({i} : Finset (Fin m)))) -
        F (fun j => decide (j ∈ (∅ : Finset (Fin m))))) =
      F (fun j => decide (j ∈ insert i A)) - F (fun j => decide (j ∈ A)) -
        F (fun j => decide (j ∈ ({i} : Finset (Fin m)))) +
        F (fun j => decide (j ∈ (∅ : Finset (Fin m)))) := by ring
  simp only at this ⊢
  rw [he]; exact this

/-- Every set function satisfies the hypothesis for some `δ ≥ 0`. -/
theorem subset_hypotheses_satisfiable (f : Finset (Fin m) → ℝ) :
    ∃ delta : ℝ, 0 ≤ delta ∧ LocalInteraction f delta := by
  classical
  refine ⟨∑ t : Finset (Fin m) × Fin m, |f (insert t.2 t.1) - f t.1 - gain f t.2|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro A i _
  exact Finset.single_le_sum
    (f := fun t : Finset (Fin m) × Fin m => |f (insert t.2 t.1) - f t.1 - gain f t.2|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (A, i))

/-- A modular (additive) value has `δ = 0`: interactions vanish exactly. -/
theorem modular_zero (w : Fin m → ℝ) (c : ℝ) :
    LocalInteraction (fun S => c + S.sum w) 0 := by
  intro A i hi
  unfold gain
  simp [Finset.sum_insert hi]

/-! ## The constant `2` is sharp -/

/-- Integer witness on three messages: every first-order gain is `0`, pairs interact. -/
def sharpZ (S : Finset (Fin 3)) : ℤ :=
  if S = {0, 1} then 7 else if S = {0, 2} then 3 else if S = {1, 2} then -7 else 0

/-- The real-valued witness. -/
def sharpF (S : Finset (Fin 3)) : ℝ := (sharpZ S : ℝ)

theorem sharpZ_local :
    ∀ (A : Finset (Fin 3)) (i : Fin 3), i ∉ A →
      |sharpZ (insert i A) - sharpZ A - (sharpZ {i} - sharpZ ∅)| ≤ 7 := by
  decide

theorem sharpF_local : LocalInteraction sharpF 7 := by
  intro A i hi
  have h := sharpZ_local A i hi
  unfold gain sharpF
  have hcast : ((sharpZ (insert i A) : ℝ) - (sharpZ A : ℝ) - ((sharpZ {i} : ℝ) - (sharpZ ∅ : ℝ))) =
      ((sharpZ (insert i A) - sharpZ A - (sharpZ {i} - sharpZ ∅) : ℤ) : ℝ) := by push_cast; ring
  rw [hcast, ← Int.cast_abs]
  exact_mod_cast h

theorem sharpZ_gain_zero : ∀ i : Fin 3, sharpZ {i} - sharpZ ∅ = 0 := by decide

theorem sharpF_gain_zero : ∀ i : Fin 3, gain sharpF i = 0 := by
  intro i
  unfold gain sharpF
  have h := sharpZ_gain_zero i
  have : ((sharpZ {i} - sharpZ ∅ : ℤ) : ℝ) = 0 := by exact_mod_cast h
  push_cast at this
  exact this

theorem sharpZ_gap : sharpZ {0, 1} - sharpZ {1, 2} = 14 := by decide

/-- **Sharpness of `subset_price_le`.**  A value table, a top-k set `P` by gain (all gains
tie at `0`), and a k-set `T` with `f T − f P = 2·|P \ T|·δ` exactly: the constant `2` cannot be
lowered.  A strict-margin version approaches it as the margin tends to `0`. -/
theorem subset_constant_sharp :
    ∃ (f : Finset (Fin 3) → ℝ) (delta : ℝ) (P T : Finset (Fin 3)),
      LocalInteraction f delta ∧ P.card = 2 ∧ T.card = 2 ∧
      (∀ i ∈ P, ∀ j ∉ P, gain f j ≤ gain f i) ∧ (P \ T).card = 1 ∧
      f T - f P = 2 * ((P \ T).card : ℝ) * delta := by
  refine ⟨sharpF, 7, {1, 2}, {0, 1}, sharpF_local, by decide, by decide, ?_, by decide, ?_⟩
  · intro i _ j _; rw [sharpF_gain_zero i, sharpF_gain_zero j]
  · have hc : ({1, 2} \ {0, 1} : Finset (Fin 3)).card = 1 := by decide
    rw [hc]
    unfold sharpF
    have h : ((sharpZ {0, 1} - sharpZ {1, 2} : ℤ) : ℝ) = 14 := by exact_mod_cast sharpZ_gap
    push_cast at h
    rw [h]; norm_num

end CIGAMF.P13.MarlSubsetFrontier

#print axioms CIGAMF.P13.MarlSubsetFrontier.resid_diff
#print axioms CIGAMF.P13.MarlSubsetFrontier.value_exchange
#print axioms CIGAMF.P13.MarlSubsetFrontier.value_exchange_lower
#print axioms CIGAMF.P13.MarlSubsetFrontier.exchange_path
#print axioms CIGAMF.P13.MarlSubsetFrontier.subset_frontier
#print axioms CIGAMF.P13.MarlSubsetFrontier.subset_price_le
#print axioms CIGAMF.P13.MarlSubsetFrontier.subset_zero_price
#print axioms CIGAMF.P13.MarlSubsetFrontier.bridge_mixed
#print axioms CIGAMF.P13.MarlSubsetFrontier.subset_hypotheses_satisfiable
#print axioms CIGAMF.P13.MarlSubsetFrontier.modular_zero
#print axioms CIGAMF.P13.MarlSubsetFrontier.subset_constant_sharp
