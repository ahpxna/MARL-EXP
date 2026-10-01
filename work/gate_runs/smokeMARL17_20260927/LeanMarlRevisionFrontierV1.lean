import Mathlib
import «LeanD6H3Exchange»

/-!
# The revision frontier of a nested (universal) priority, for product-reference compression

A world `F` on a product space, a product reference `q`, first-order responses
`productResponse q F j`, the response span `osc (productResponse q F j)` of coordinate `j`,
and the compression loss `ℓ_S = productCompressionLoss F (productResponse q F) S` of
retaining `S` — the D6 objects.  `δ` bounds every mixed difference.

## WHAT IS PROVED

* `exchange_general` — for ANY two retained sets `S`, `T` (no Top-k hypothesis, no
  cardinality hypothesis):

      ℓ_S − ℓ_T ≤ |S \ T|·δ − (σ(S \ T) − σ(T \ S)) / 2,

  where `σ` sums response spans.  The existing
  `LeanD6MarginSensitiveExchangeV1.pair_loss_le_sdiff_card_sub_score_surplus` has the same
  conclusion, but it carries a Top-k hypothesis that its final step does not use.  This file
  proves the statement without that hypothesis.
* `potential_lipschitz`, `potential_two_sided` — equivalently, the potential
  `φ(S) = ℓ_S + σ(S)/2` is `δ`-Lipschitz in the one-sided Hamming distance.  So the loss
  is MODULAR (`−σ/2`) up to an interaction error that grows by at most `δ` per differing
  coordinate.
* `between_frontier` — if `P` is Top-k by span, `T` is any k-set, and `S` is a k-set with
  `S \ T ⊆ P` and `T \ S` outside `P` (i.e. `S` lies on an exchange path from `P` to `T`),
  then `ℓ_S − ℓ_T ≤ |S \ T|·δ`.
* `revision_frontier` — THE FRONTIER.  With `d = |P \ T|` and any `R`, there is a k-set `S`
  with `|S \ P| ≤ R` (at most `R` replacements after the budget is revealed) and

      ℓ_S − ℓ_T ≤ (d − R)₊ · δ.

* `price_le_min` — the commitment price of the score ranking at budget `k` is at most
  `|P \ T|·δ ≤ min(k, m − k)·δ`.
* `revision_frontier_all_budgets` — for a family of Top-k prefixes (a universal score
  ranking), simultaneously at every budget of a finite budget set, `R` replacements leave
  a regret of at most `(d_k − R)₊·δ` against any family of comparison sets.
* `exchange_lower` — the matching lower direction, for sharpness statements.
* `potential_mono`, `marginal_bracket` — NEAR-MODULARITY: `φ` is monotone, so retaining one
  more coordinate `j` lowers the loss by between `span j/2 − δ` and `span j/2`.  The loss
  is the modular function `−σ/2` plus a monotone perturbation with increments in `[0, δ]`.
* `optimal_of_cut_margin`, `zero_price_all_budgets` — NESTING IS FREE under a `2δ` cut
  margin at every budget: the universal prefix is optimal everywhere.  This is M1; it is
  derived from `exchange_general`, not from `margin_two_sufficient`.
* `delta_exists`, `uniform_weight_nonneg`, `uniform_weight_sum` — every hypothesis is
  satisfiable, for every world `F`.

## WHAT THIS DOES NOT ESTABLISH

- Tightness.  That the frontier `(d − R)₊·δ` is approached at every `R` needs a family.
  The D6 `m = 6` family `Vb s` attains the `R = 0` endpoint asymptotically
  (`LeanD6SharpnessM6V1`); the intermediate `R` are a separate file.
- Randomised ranking laws and exposure bands.  Everything here is deterministic.  A
  randomised law can only lower the price, so these are upper bounds for C-style values.
- The loss is the worst-case half-oscillation of the retained residual.  It is not an
  expected return.  The bridge to a team return is a separate (conditional) statement.
-/

namespace CIGAMF.P13.MarlRevisionFrontier

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6H3Exchange

variable {U : Type*} [Fintype U] [Nonempty U]

/-! ## Local copies of the private helper lemmas of the D6 exchange files -/

theorem point_sub_point_le_osc'
    {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (a b : A) : f a - f b ≤ osc f := by
  have ha := le_maxVal f a
  have hb := minVal_le f b
  simp only [osc]
  linarith

theorem retainedResidual_sdiff_identity' {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (S T : Finset (Fin (n + 1))) (z : Fin (n + 1) → U) :
    retainedResidual q F T z = retainedResidual q F S z +
        (S \ T).sum (fun j ↦ productResponse q F j (z j)) -
        (T \ S).sum (fun j ↦ productResponse q F j (z j)) := by
  classical
  unfold retainedResidual
  have hcancel :
      S.sum (fun j ↦ productResponse q F j (z j)) -
          T.sum (fun j ↦ productResponse q F j (z j)) =
        (S \ T).sum (fun j ↦ productResponse q F j (z j)) -
          (T \ S).sum (fun j ↦ productResponse q F j (z j)) := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
  rw [show F z - T.sum (fun j ↦ productResponse q F j (z j)) =
      (F z - S.sum (fun j ↦ productResponse q F j (z j))) +
        (S.sum (fun j ↦ productResponse q F j (z j)) -
          T.sum (fun j ↦ productResponse q F j (z j))) by ring,
    hcancel]
  ring

theorem directed_response_sum_le_spans' {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (A : Finset (Fin (n + 1))) (x y : Fin (n + 1) → U) :
    A.sum (fun j ↦ productResponse q F j (x j)) -
        A.sum (fun j ↦ productResponse q F j (y j)) ≤
      A.sum (fun j ↦ osc (productResponse q F j)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact point_sub_point_le_osc' (productResponse q F j) (x j) (y j)

theorem patched_extrema_sum' {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (A : Finset (Fin (n + 1)))
    (x y p m : Fin (n + 1) → U)
    (hp : ∀ j, productResponse q F j (p j) =
      maxVal (productResponse q F j))
    (hm : ∀ j, productResponse q F j (m j) =
      minVal (productResponse q F j)) :
    A.sum (fun j ↦ productResponse q F j
        (patchCoordinates x p A j)) -
      A.sum (fun j ↦ productResponse q F j
        (patchCoordinates y m A j)) =
      A.sum (fun j ↦ osc (productResponse q F j)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [patchCoordinates, if_pos hj, hp, hm, osc]

/-! ## Names -/

/-- The response span of coordinate `j`: the first-order score. -/
noncomputable def span {n : ℕ} (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (j : Fin (n + 1)) : ℝ :=
  osc (productResponse q F j)

/-- The compression loss of retaining `S`. -/
noncomputable def loss {n : ℕ} (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (S : Finset (Fin (n + 1))) : ℝ :=
  productCompressionLoss F (productResponse q F) S

/-- The potential `φ(S) = ℓ_S + σ(S)/2`. -/
noncomputable def potential {n : ℕ} (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (S : Finset (Fin (n + 1))) : ℝ :=
  loss q F S + S.sum (span q F) / 2

/-! ## The general exchange inequality -/

/-- **General exchange.**  For ANY retained sets `S`, `T`:
`ℓ_S − ℓ_T ≤ |S \ T|·δ − (σ(S \ T) − σ(T \ S))/2`.  No Top-k and no cardinality
hypothesis. -/
theorem exchange_general {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (S T : Finset (Fin (n + 1))) :
    loss q F S - loss q F T ≤
      ((S \ T).card : ℝ) * delta -
        ((S \ T).sum (span q F) - (T \ S).sum (span q F)) / 2 := by
  classical
  let RS := retainedResidual q F S
  let RT := retainedResidual q F T
  let A := S \ T
  let B := T \ S
  rcases exists_eq_maxVal RS with ⟨xplus, hxplus⟩
  rcases exists_eq_minVal RS with ⟨xminus, hxminus⟩
  let p : Fin (n + 1) → U := fun j ↦
    Classical.choose (exists_eq_maxVal (productResponse q F j))
  let m : Fin (n + 1) → U := fun j ↦
    Classical.choose (exists_eq_minVal (productResponse q F j))
  have hp : ∀ j, productResponse q F j (p j) =
      maxVal (productResponse q F j) := by
    intro j
    exact Classical.choose_spec (exists_eq_maxVal (productResponse q F j))
  have hm : ∀ j, productResponse q F j (m j) =
      minVal (productResponse q F j) := by
    intro j
    exact Classical.choose_spec (exists_eq_minVal (productResponse q F j))
  let u := patchCoordinates xplus p A
  let v := patchCoordinates xminus m A
  have hAsub : A ⊆ S := by
    intro j hj
    exact (Finset.mem_sdiff.mp hj).1
  have hplusAbs := retainedResidual_patch_bound q F delta hWeight hNorm
    hDeltaNonneg hdelta S A hAsub xplus p
  have hminusAbs := retainedResidual_patch_bound q F delta hWeight hNorm
    hDeltaNonneg hdelta S A hAsub xminus m
  have hplus : RS xplus - RS u ≤ (A.card : ℝ) * delta := by
    have hle : RS xplus - RS u ≤ |RS xplus - RS u| := le_abs_self _
    have habs : |RS xplus - RS u| ≤ (A.card : ℝ) * delta := by
      simpa [RS, u, abs_sub_comm] using hplusAbs
    exact le_trans hle habs
  have hminus : RS v - RS xminus ≤ (A.card : ℝ) * delta := by
    have hle : RS v - RS xminus ≤ |RS v - RS xminus| := le_abs_self _
    have habs : |RS v - RS xminus| ≤ (A.card : ℝ) * delta := by
      simpa [RS, v] using hminusAbs
    exact le_trans hle habs
  have hoscT : RT u - RT v ≤ osc RT :=
    point_sub_point_le_osc' RT u v
  have hRTu : RT u = RS u +
      A.sum (fun j ↦ productResponse q F j (u j)) -
      B.sum (fun j ↦ productResponse q F j (u j)) := by
    simpa [RS, RT, A, B] using
      retainedResidual_sdiff_identity' q F S T u
  have hRTv : RT v = RS v +
      A.sum (fun j ↦ productResponse q F j (v j)) -
      B.sum (fun j ↦ productResponse q F j (v j)) := by
    simpa [RS, RT, A, B] using
      retainedResidual_sdiff_identity' q F S T v
  have hAdiff :
      A.sum (fun j ↦ productResponse q F j (u j)) -
        A.sum (fun j ↦ productResponse q F j (v j)) =
      A.sum (fun j ↦ osc (productResponse q F j)) := by
    simpa [u, v] using patched_extrema_sum' q F A xplus xminus p m hp hm
  have hBdiff :
      B.sum (fun j ↦ productResponse q F j (u j)) -
        B.sum (fun j ↦ productResponse q F j (v j)) ≤
      B.sum (fun j ↦ osc (productResponse q F j)) :=
    directed_response_sum_le_spans' q F B u v
  have hoscS : osc RS = RS xplus - RS xminus := by
    simp only [osc, ← hxplus, ← hxminus]
  have hRaw : osc RS - osc RT ≤
      2 * (A.card : ℝ) * delta -
        (A.sum (fun j ↦ osc (productResponse q F j)) -
         B.sum (fun j ↦ osc (productResponse q F j))) := by
    rw [hoscS]
    linarith
  change osc RS / 2 - osc RT / 2 ≤ (A.card : ℝ) * delta -
    (A.sum (fun j ↦ osc (productResponse q F j)) -
     B.sum (fun j ↦ osc (productResponse q F j))) / 2
  linarith

/-- The matching lower direction: `ℓ_S − ℓ_T ≥ (σ(T \ S) − σ(S \ T))/2 − |T \ S|·δ`. -/
theorem exchange_lower {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (S T : Finset (Fin (n + 1))) :
    ((T \ S).sum (span q F) - (S \ T).sum (span q F)) / 2 -
        ((T \ S).card : ℝ) * delta ≤
      loss q F S - loss q F T := by
  have h := exchange_general q F delta hWeight hNorm hDeltaNonneg hdelta T S
  linarith

/-! ## The potential is Lipschitz: the loss is modular up to interaction -/

theorem sum_sub_sum_eq_sdiff {ι : Type*} [DecidableEq ι] (S T : Finset ι) (f : ι → ℝ) :
    S.sum f - T.sum f = (S \ T).sum f - (T \ S).sum f := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff]

/-- `φ(S) − φ(T) ≤ |S \ T|·δ` for every `S`, `T`. -/
theorem potential_lipschitz {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (S T : Finset (Fin (n + 1))) :
    potential q F S - potential q F T ≤ ((S \ T).card : ℝ) * delta := by
  classical
  have h := exchange_general q F delta hWeight hNorm hDeltaNonneg hdelta S T
  have hs := sum_sub_sum_eq_sdiff S T (span q F)
  unfold potential
  linarith

/-- For equal-size sets, `|φ(S) − φ(T)| ≤ |S \ T|·δ`. -/
theorem potential_two_sided {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (S T : Finset (Fin (n + 1))) (hcard : S.card = T.card) :
    |potential q F S - potential q F T| ≤ ((S \ T).card : ℝ) * delta := by
  classical
  have h1 := potential_lipschitz q F delta hWeight hNorm hDeltaNonneg hdelta S T
  have h2 := potential_lipschitz q F delta hWeight hNorm hDeltaNonneg hdelta T S
  have hc : (T \ S).card = (S \ T).card := (Finset.card_sdiff_comm hcard).symm
  rw [hc] at h2
  rw [abs_le]
  constructor <;> linarith

/-! ## The exchange path and the frontier -/

/-- Sum comparison under a pointwise order, for equal cardinalities. -/
theorem sum_le_sum_of_pointwise {I : Type*} [DecidableEq I]
    (A B : Finset I) (score : I → ℝ) (hCard : A.card = B.card)
    (hOrder : ∀ i ∈ A, ∀ j ∈ B, score j ≤ score i) :
    B.sum score ≤ A.sum score := by
  classical
  by_cases hB : B.Nonempty
  · obtain ⟨b, hb, hmax⟩ := B.exists_max_image score hB
    have ha : (A.card : ℝ) * score b ≤ A.sum score := by
      calc (A.card : ℝ) * score b = A.sum (fun _ => score b) := by simp
           _ ≤ _ := Finset.sum_le_sum (fun i hi => hOrder i hi b hb)
    have hbSum : B.sum score ≤ (A.card : ℝ) * score b := by
      calc B.sum score ≤ B.sum (fun _ => score b) :=
            Finset.sum_le_sum (fun j hj => hmax j hj)
           _ = _ := by simp [hCard]
    linarith
  · have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hAe : A = ∅ := Finset.card_eq_zero.mp (by simpa [hBe] using hCard)
    simp [hAe, hBe]

/-- **On an exchange path from a Top-k set `P` to a k-set `T`**, the loss gap to `T` is at
most the remaining distance times `δ`. -/
theorem between_frontier {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (P T S : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore (span q F) P k)
    (hT : T.card = k) (hS : S.card = k)
    (hSsub : S \ T ⊆ P) (hTout : ∀ j ∈ T \ S, j ∉ P) :
    loss q F S - loss q F T ≤ ((S \ T).card : ℝ) * delta := by
  classical
  have h := exchange_general q F delta hWeight hNorm hDeltaNonneg hdelta S T
  have hc : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm (hS.trans hT.symm)
  have hord : ∀ i ∈ S \ T, ∀ j ∈ T \ S, span q F j ≤ span q F i := by
    intro i hi j hj
    exact topK_pairwise_score_order (span q F) P k hTop (hSsub hi) (hTout j hj)
  have hsum := sum_le_sum_of_pointwise (S \ T) (T \ S) (span q F) hc hord
  linarith

/-- **The revision frontier.**  If `P` is Top-k by span and `T` is any k-set, then for every
number `R` of replacements there is a k-set `S` with at most `R` new elements relative to
`P` whose loss is within `(|P \ T| − R)₊·δ` of `T`'s. -/
theorem revision_frontier {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (P T : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore (span q F) P k) (hT : T.card = k) (R : ℕ) :
    ∃ S : Finset (Fin (n + 1)), S.card = k ∧ (S \ P).card ≤ R ∧
      loss q F S - loss q F T ≤ (((P \ T).card - R : ℕ) : ℝ) * delta := by
  classical
  have hP : P.card = k := hTop.1
  have hdc : (P \ T).card = (T \ P).card := Finset.card_sdiff_comm (hP.trans hT.symm)
  by_cases hR : (P \ T).card ≤ R
  · -- enough replacements: move all the way to `T`
    refine ⟨T, hT, ?_, ?_⟩
    · rw [← hdc]; exact hR
    · have hz : (P \ T).card - R = 0 := Nat.sub_eq_zero_of_le hR
      rw [hz]; simp
  · push Not at hR
    -- choose `R` elements to drop from `P \ T` and `R` to add from `T \ P`
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
    -- `S \ T = (P \ T) \ X`
    have hST : S \ T = (P \ T) \ X := by
      ext j
      simp only [S, Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hj | hj, hjT⟩
        · exact ⟨⟨hj.1, hjT⟩, hj.2⟩
        · exact absurd (Finset.mem_sdiff.mp (hYsub hj)).1 hjT
      · rintro ⟨⟨hjP, hjT⟩, hjX⟩
        exact ⟨Or.inl ⟨hjP, hjX⟩, hjT⟩
    have hSTcard : (S \ T).card = (P \ T).card - R := by
      rw [hST, Finset.card_sdiff_of_subset hXsub, hXcard]
    have hSsub : S \ T ⊆ P := by
      rw [hST]; intro j hj
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1).1
    have hTout : ∀ j ∈ T \ S, j ∉ P := by
      intro j hj hjP
      have hjT : j ∈ T := (Finset.mem_sdiff.mp hj).1
      have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
      have hjX : j ∈ X := by
        by_contra hjX
        exact hjS (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hjP, hjX⟩)))
      exact (Finset.mem_sdiff.mp (hXsub hjX)).2 hjT
    have hSP : (S \ P).card ≤ R := by
      have : S \ P ⊆ Y := by
        intro j hj
        rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hj).1 with hj' | hj'
        · exact absurd (Finset.mem_sdiff.mp hj').1 (Finset.mem_sdiff.mp hj).2
        · exact hj'
      calc (S \ P).card ≤ Y.card := Finset.card_le_card this
        _ = R := hYcard
    refine ⟨S, hScard, hSP, ?_⟩
    have hb := between_frontier q F delta hWeight hNorm hDeltaNonneg hdelta P T S k hTop hT
      hScard hSsub hTout
    rw [hSTcard] at hb
    exact hb

/-- **Price of the score ranking.**  With no revision, the regret of the Top-k set against any
k-set is at most `|P \ T|·δ ≤ min(k, m − k)·δ`, where `m = n + 1`. -/
theorem price_le_min {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (P T : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore (span q F) P k) (hT : T.card = k) :
    loss q F P - loss q F T ≤ ((P \ T).card : ℝ) * delta ∧
      ((P \ T).card : ℝ) * delta ≤ ((min k (n + 1 - k) : ℕ) : ℝ) * delta := by
  classical
  have hP : P.card = k := hTop.1
  refine ⟨?_, ?_⟩
  · have hb := between_frontier q F delta hWeight hNorm hDeltaNonneg hdelta P T P k hTop hT hP
      Finset.sdiff_subset (fun j hj => (Finset.mem_sdiff.mp hj).2)
    exact hb
  · apply mul_le_mul_of_nonneg_right _ hDeltaNonneg
    have h1 : (P \ T).card ≤ k := hP ▸ Finset.card_le_card Finset.sdiff_subset
    have h2 : (P \ T).card ≤ n + 1 - k := by
      have hsub : P \ T ⊆ Tᶜ := by
        intro j hj; exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hj).2
      have := Finset.card_le_card hsub
      rw [Finset.card_compl, Fintype.card_fin, hT] at this
      exact this
    exact_mod_cast le_min h1 h2

/-- **The frontier at every budget at once.**  For a universal score ranking — a Top-k set
`P k` at each budget `k` of a finite budget set `K` — and ANY comparison sets `T k` of size
`k`, `R` replacements after the budget is revealed leave, at every budget,
a regret of at most `(|P k \ T k| − R)₊·δ`. -/
theorem revision_frontier_all_budgets {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (K : Finset ℕ) (P T : ℕ → Finset (Fin (n + 1)))
    (hTop : ∀ k ∈ K, IsTopKByScore (span q F) (P k) k)
    (hT : ∀ k ∈ K, (T k).card = k) (R : ℕ) :
    ∀ k ∈ K, ∃ S : Finset (Fin (n + 1)), S.card = k ∧ (S \ P k).card ≤ R ∧
      loss q F S - loss q F (T k) ≤ ((((P k) \ (T k)).card - R : ℕ) : ℝ) * delta :=
  fun k hk => revision_frontier q F delta hWeight hNorm hDeltaNonneg hdelta (P k) (T k) k
    (hTop k hk) (hT k hk) R

/-- With `R ≥ min(k, m − k)` at every budget, the revised sets match every comparison set:
full recourse. -/
theorem revision_full {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (P T : Finset (Fin (n + 1))) (k R : ℕ)
    (hTop : IsTopKByScore (span q F) P k) (hT : T.card = k) (hR : min k (n + 1 - k) ≤ R) :
    ∃ S : Finset (Fin (n + 1)), S.card = k ∧ (S \ P).card ≤ R ∧
      loss q F S - loss q F T ≤ 0 := by
  classical
  obtain ⟨S, hS, hSP, hgap⟩ :=
    revision_frontier q F delta hWeight hNorm hDeltaNonneg hdelta P T k hTop hT R
  refine ⟨S, hS, hSP, ?_⟩
  have hP : P.card = k := hTop.1
  have h1 : (P \ T).card ≤ k := hP ▸ Finset.card_le_card Finset.sdiff_subset
  have h2 : (P \ T).card ≤ n + 1 - k := by
    have hsub : P \ T ⊆ Tᶜ := by
      intro j hj; exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hj).2
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, Fintype.card_fin, hT] at this
    exact this
  have hz : (P \ T).card - R = 0 := by
    have := le_min h1 h2
    omega
  rw [hz] at hgap
  simpa using hgap

/-! ## Satisfiability of the hypotheses, for every world -/

/-- A bound on every mixed difference always exists. -/
theorem delta_exists {n : ℕ} [DecidableEq U] (F : (Fin (n + 1) → U) → ℝ) :
    ∃ delta : ℝ, 0 ≤ delta ∧ ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta := by
  classical
  refine ⟨∑ t : Fin (n + 1) × (Fin (n + 1) → U) × (Fin (n + 1) → U),
      |mixedDifference F t.1 t.2.1 t.2.2|, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · intro i x c
    exact Finset.single_le_sum (f := fun t : Fin (n + 1) × (Fin (n + 1) → U) ×
        (Fin (n + 1) → U) => |mixedDifference F t.1 t.2.1 t.2.2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (i, x, c))

/-- The uniform product reference. -/
noncomputable def uniformRef (n : ℕ) (U : Type*) [Fintype U] : Fin (n + 1) → U → ℝ :=
  fun _ _ => 1 / (Fintype.card U : ℝ)

theorem uniform_weight_nonneg (n : ℕ) (c : Fin (n + 1) → U) :
    0 ≤ jointWeight (uniformRef n U) c := by
  unfold jointWeight uniformRef
  exact Finset.prod_nonneg (fun _ _ => by positivity)

theorem uniform_weight_sum (n : ℕ) [DecidableEq U] :
    ∑ c, jointWeight (uniformRef n U) c = 1 := by
  classical
  unfold jointWeight uniformRef
  have hU : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
    Fintype.card_fun, nsmul_eq_mul]
  push_cast
  rw [div_pow, one_pow, mul_one_div, div_self (pow_ne_zero _ hU.ne')]

/-- **All hypotheses hold together**, for every world on every finite product space. -/
theorem hypotheses_satisfiable (n : ℕ) [DecidableEq U] (F : (Fin (n + 1) → U) → ℝ) :
    ∃ (q : Fin (n + 1) → U → ℝ) (delta : ℝ),
      (∀ c, 0 ≤ jointWeight q c) ∧ (∑ c, jointWeight q c = 1) ∧ 0 ≤ delta ∧
      ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U), |mixedDifference F i x c| ≤ delta := by
  obtain ⟨delta, hd0, hd⟩ := delta_exists F
  exact ⟨uniformRef n U, delta, uniform_weight_nonneg n, uniform_weight_sum n, hd0, hd⟩

/-! ## Near-modularity: the potential is monotone with increments in `[0, δ]` -/

/-- `φ` is monotone: retaining more coordinates never lowers `ℓ_S + σ(S)/2`. -/
theorem potential_mono {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (S T : Finset (Fin (n + 1))) (hST : S ⊆ T) :
    potential q F S ≤ potential q F T := by
  classical
  have h := potential_lipschitz q F delta hWeight hNorm hDeltaNonneg hdelta S T
  have he : S \ T = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hST
  rw [he] at h
  simpa using h

/-- **Marginal bracket.**  Retaining one more coordinate `j` lowers the loss by at least
`span j / 2 − δ` and at most `span j / 2`:
`−span j / 2 ≤ ℓ_{S ∪ {j}} − ℓ_S ≤ −span j / 2 + δ`.  So the loss is the modular function
`−σ/2` plus a monotone perturbation whose increments lie in `[0, δ]`. -/
theorem marginal_bracket {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (S : Finset (Fin (n + 1))) (j : Fin (n + 1)) (hj : j ∉ S) :
    -(span q F j) / 2 ≤ loss q F (insert j S) - loss q F S ∧
      loss q F (insert j S) - loss q F S ≤ -(span q F j) / 2 + delta := by
  classical
  have hsub : S ⊆ insert j S := Finset.subset_insert j S
  have hmono := potential_mono q F delta hWeight hNorm hDeltaNonneg hdelta S (insert j S) hsub
  have hlip := potential_lipschitz q F delta hWeight hNorm hDeltaNonneg hdelta (insert j S) S
  have hd : insert j S \ S = {j} := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hxS⟩
      · exact hx
      · exact absurd hx hxS
    · rintro rfl; exact ⟨Or.inl rfl, hj⟩
  rw [hd, Finset.card_singleton] at hlip
  have hsum : (insert j S).sum (span q F) = span q F j + S.sum (span q F) :=
    Finset.sum_insert hj
  unfold potential at hmono hlip
  rw [hsum] at hmono hlip
  constructor <;> push_cast at hlip <;> linarith

/-! ## Zero price of nesting when every score gap dominates twice the interaction -/

/-- Sum a common separation margin across equal-size exchanged sets. -/
theorem surplus_ge_card_mul {I : Type*} [DecidableEq I]
    (A B : Finset I) (score : I → ℝ) (mu : ℝ) (hCard : A.card = B.card)
    (hMargin : ∀ i ∈ A, ∀ j ∈ B, mu + score j ≤ score i) :
    (A.card : ℝ) * mu ≤ A.sum score - B.sum score := by
  classical
  by_cases hB : B.Nonempty
  · obtain ⟨b, hb, hmax⟩ := B.exists_max_image score hB
    have ha : (A.card : ℝ) * (mu + score b) ≤ A.sum score := by
      calc (A.card : ℝ) * (mu + score b) = A.sum (fun _ => mu + score b) := by
            rw [Finset.sum_const, nsmul_eq_mul]
           _ ≤ _ := Finset.sum_le_sum (fun i hi => hMargin i hi b hb)
    have hbSum : B.sum score ≤ (A.card : ℝ) * score b := by
      calc B.sum score ≤ B.sum (fun _ => score b) :=
            Finset.sum_le_sum (fun j hj => hmax j hj)
           _ = _ := by simp [hCard]
    nlinarith
  · have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hAe : A = ∅ := Finset.card_eq_zero.mp (by simpa [hBe] using hCard)
    simp [hAe, hBe]

/-- **Nesting is free under a `2δ` cut margin.**  If every retained coordinate's span beats
every omitted coordinate's span by at least `2δ`, the retained set is optimal among all sets
of its size.  The proof is by `exchange_general`, and no Top-k hypothesis is used. -/
theorem optimal_of_cut_margin {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (P T : Finset (Fin (n + 1))) (hcard : T.card = P.card)
    (hMargin : ∀ i ∈ P, ∀ j ∉ P, 2 * delta + span q F j ≤ span q F i) :
    loss q F P ≤ loss q F T := by
  classical
  have h := exchange_general q F delta hWeight hNorm hDeltaNonneg hdelta P T
  have hc : (P \ T).card = (T \ P).card := Finset.card_sdiff_comm hcard.symm
  have hs := surplus_ge_card_mul (P \ T) (T \ P) (span q F) (2 * delta) hc
    (fun i hi j hj => hMargin i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2)
  nlinarith

/-- **Zero commitment price at every budget.**  For a universal ranking whose prefix at
every budget `k ∈ K` is separated from the rest by a `2δ` score margin, the prefix is
optimal at every budget: universal = budget-aware, and no revision is needed. -/
theorem zero_price_all_budgets {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (K : Finset ℕ) (P : ℕ → Finset (Fin (n + 1)))
    (hPcard : ∀ k ∈ K, (P k).card = k)
    (hMargin : ∀ k ∈ K, ∀ i ∈ P k, ∀ j ∉ P k, 2 * delta + span q F j ≤ span q F i) :
    ∀ k ∈ K, ∀ T : Finset (Fin (n + 1)), T.card = k → loss q F (P k) ≤ loss q F T :=
  fun k hk T hT => optimal_of_cut_margin q F delta hWeight hNorm hDeltaNonneg hdelta (P k) T
    (hT.trans (hPcard k hk).symm) (hMargin k hk)

end CIGAMF.P13.MarlRevisionFrontier

#print axioms CIGAMF.P13.MarlRevisionFrontier.exchange_general
#print axioms CIGAMF.P13.MarlRevisionFrontier.exchange_lower
#print axioms CIGAMF.P13.MarlRevisionFrontier.potential_lipschitz
#print axioms CIGAMF.P13.MarlRevisionFrontier.potential_two_sided
#print axioms CIGAMF.P13.MarlRevisionFrontier.between_frontier
#print axioms CIGAMF.P13.MarlRevisionFrontier.revision_frontier
#print axioms CIGAMF.P13.MarlRevisionFrontier.price_le_min
#print axioms CIGAMF.P13.MarlRevisionFrontier.revision_frontier_all_budgets
#print axioms CIGAMF.P13.MarlRevisionFrontier.revision_full
#print axioms CIGAMF.P13.MarlRevisionFrontier.hypotheses_satisfiable
#print axioms CIGAMF.P13.MarlRevisionFrontier.potential_mono
#print axioms CIGAMF.P13.MarlRevisionFrontier.marginal_bracket
#print axioms CIGAMF.P13.MarlRevisionFrontier.optimal_of_cut_margin
#print axioms CIGAMF.P13.MarlRevisionFrontier.zero_price_all_budgets
