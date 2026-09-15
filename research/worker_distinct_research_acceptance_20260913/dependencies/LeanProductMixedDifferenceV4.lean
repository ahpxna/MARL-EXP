import Mathlib
import «LeanProductSurrogateV4»
import «LeanSupportGeometryV4»

/-! General finite product-surrogate mixed-difference bound. -/

namespace CIGAMF.V4.ProductMixedDifference

open scoped BigOperators
open ProductSurrogate
open CIGAMF.V4.SupportGeometry

variable {U : Type*}

def hybrid {m : ℕ} (x c : Fin m → U) (k : ℕ) (j : Fin m) : U :=
  if j.val < k then c j else x j

theorem hybrid_zero {m : ℕ} (x c : Fin m → U) : hybrid x c 0 = x := by
  funext j
  simp [hybrid]

theorem hybrid_card {m : ℕ} (x c : Fin m → U) : hybrid x c m = c := by
  funext j
  simp [hybrid, j.isLt]

theorem update_hybrid_step {m : ℕ} (x c : Fin m → U)
    (i : ℕ) (hi : i < m) :
    Function.update (hybrid x c i) (⟨i, hi⟩ : Fin m) (c ⟨i, hi⟩) =
      hybrid x c (i + 1) := by
  funext j
  by_cases hj : j = (⟨i, hi⟩ : Fin m)
  · subst j
    simp [hybrid, hi]
  · have hv : j.val ≠ i := by
      intro h
      apply hj
      exact Fin.ext h
    by_cases hlt : j.val < i
    · have hlts : j.val < i + 1 := Nat.lt.step hlt
      simp [Function.update, hj, hybrid, hlt, hlts]
    · have hlts : ¬j.val < i + 1 := by omega
      simp [Function.update, hj, hybrid, hlt, hlts]

theorem update_anchor_from_hybrid {m : ℕ} (x c : Fin m → U)
    (i : ℕ) (hi : i < m) :
    Function.update c (⟨i, hi⟩ : Fin m) (hybrid x c i ⟨i, hi⟩) =
      Function.update c (⟨i, hi⟩ : Fin m) (x ⟨i, hi⟩) := by
  simp [hybrid]

theorem mixedDifference_hybrid_step {m : ℕ}
    (F : (Fin m → U) → ℝ) (x c : Fin m → U)
    (i : ℕ) (hi : i < m) :
    mixedDifference F (⟨i, hi⟩ : Fin m) (hybrid x c i) c =
      F (hybrid x c i) - F (hybrid x c (i + 1)) -
        F (Function.update c (⟨i, hi⟩ : Fin m) (x ⟨i, hi⟩)) + F c := by
  unfold mixedDifference
  rw [update_hybrid_step x c i hi, update_anchor_from_hybrid x c i hi]

theorem update_anchor_last_eq_hybrid {n : ℕ} (x c : Fin (n + 1) → U) :
    Function.update c (Fin.last n) (x (Fin.last n)) = hybrid x c n := by
  funext j
  by_cases hj : j.val < n
  · have hne : j ≠ Fin.last n := by
      intro h
      subst j
      simp at hj
    simp [Function.update, hne, hybrid, hj]
  · have heq : j = Fin.last n := by
      apply Fin.ext
      simp only [Fin.last]
      omega
    subst j
    simp [hybrid]

theorem pointwise_residual_eq_sum_mixed {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (x c : Fin (n + 1) → U) :
    F x - (∑ i : Fin (n + 1), F (Function.update c i (x i))) +
        (n : ℝ) * F c =
      ∑ i : Fin n, mixedDifference F i.castSucc (hybrid x c i.val) c := by
  classical
  have hstep : ∀ i : Fin n,
      mixedDifference F i.castSucc (hybrid x c i.val) c =
        F (hybrid x c i.val) - F (hybrid x c (i.val + 1)) -
          F (Function.update c i.castSucc (x i.castSucc)) + F c := by
    intro i
    exact mixedDifference_hybrid_step F x c i.val
      (Nat.lt_trans i.isLt (Nat.lt_succ_self n))
  simp_rw [hstep]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  have htel := Finset.sum_range_sub' (fun i => F (hybrid x c i)) n
  rw [hybrid_zero] at htel
  have htel' :
      (∑ i ∈ Finset.range n, F (hybrid x c i)) -
          (∑ i ∈ Finset.range n, F (hybrid x c (i + 1))) =
        F x - F (hybrid x c n) := by
    rw [← Finset.sum_sub_distrib]
    exact htel
  have hlast : F (Function.update c (Fin.last n) (x (Fin.last n))) =
      F (hybrid x c n) := congrArg F (update_anchor_last_eq_hybrid x c)
  rw [Fin.sum_univ_castSucc, hlast]
  rw [Fin.sum_univ_eq_sum_range (fun i => F (hybrid x c i)) n]
  rw [Fin.sum_univ_eq_sum_range (fun i => F (hybrid x c (i + 1))) n]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [htel']
  ring

theorem D2_pointwise_mixed_difference_bound {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (x c : Fin (n + 1) → U) :
    |F x - (∑ i : Fin (n + 1), F (Function.update c i (x i))) +
        (n : ℝ) * F c| ≤ (n : ℝ) * delta := by
  rw [pointwise_residual_eq_sum_mixed]
  calc
    |∑ i : Fin n, mixedDifference F i.castSucc (hybrid x c i.val) c| ≤
        ∑ i : Fin n, |mixedDifference F i.castSucc (hybrid x c i.val) c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, delta := by
      apply Finset.sum_le_sum
      intro i hi
      exact hdelta i.castSucc (hybrid x c i.val) c
    _ = (n : ℝ) * delta := by simp

section ProductExpectation

variable [Fintype U] [Nonempty U]

noncomputable def jointWeight {n : ℕ}
    (q : Fin (n + 1) → U → ℝ) (c : Fin (n + 1) → U) : ℝ :=
  ∏ i, q i (c i)

noncomputable def productExpectation {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (G : (Fin (n + 1) → U) → ℝ) : ℝ :=
  ∑ c, jointWeight q c * G c

noncomputable def productB {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) : ℝ :=
  productExpectation q F

noncomputable def productResponse {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u : U) : ℝ :=
  productExpectation q (fun c => F (Function.update c i u))

noncomputable def productA {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (x : Fin (n + 1) → U) : ℝ :=
  surrogate (productResponse q F) (productB q F) x

theorem product_residual_eq_expectation {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (x : Fin (n + 1) → U) :
    F x - productA q F x =
      productExpectation q (fun c =>
        F x - (∑ i, F (Function.update c i (x i))) + (n : ℝ) * F c) := by
  classical
  have hswap :
      (∑ i : Fin (n + 1),
          ∑ c, jointWeight q c * F (Function.update c i (x i))) =
        ∑ c, jointWeight q c *
          (∑ i : Fin (n + 1), F (Function.update c i (x i))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mul_sum]
  unfold productA surrogate productResponse productB productExpectation
  change F x -
      ((∑ i : Fin (n + 1),
          ∑ c, jointWeight q c * F (Function.update c i (x i))) -
        ((Fintype.card (Fin (n + 1)) : ℝ) - 1) *
          (∑ c, jointWeight q c * F c)) =
    ∑ c, jointWeight q c *
      (F x - (∑ i : Fin (n + 1), F (Function.update c i (x i))) +
        (n : ℝ) * F c)
  rw [hswap]
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hexpand :
      (∑ c, jointWeight q c *
        (F x - (∑ i : Fin (n + 1), F (Function.update c i (x i))) +
          (n : ℝ) * F c)) =
      (∑ c, jointWeight q c * F x) -
        (∑ c, jointWeight q c *
          (∑ i : Fin (n + 1), F (Function.update c i (x i)))) +
        (∑ c, jointWeight q c * ((n : ℝ) * F c)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  rw [hexpand]
  have hxsum : (∑ c, jointWeight q c * F x) = F x := by
    rw [← Finset.sum_mul, hNorm, one_mul]
  have hn : ((n : ℝ) + 1 - 1) = (n : ℝ) := by ring
  rw [hn]
  have hlast :
      (∑ c, jointWeight q c * ((n : ℝ) * F c)) =
        (n : ℝ) * ∑ c, jointWeight q c * F c := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  rw [hlast]
  rw [hxsum]
  ring

theorem D3_product_surrogate_mixed_difference_bound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (x : Fin (n + 1) → U) :
    |F x - productA q F x| ≤ (n : ℝ) * delta := by
  rw [product_residual_eq_expectation q F hNorm x]
  unfold productExpectation
  calc
    |∑ c, jointWeight q c *
        (F x - (∑ i, F (Function.update c i (x i))) + (n : ℝ) * F c)| ≤
      ∑ c, |jointWeight q c *
        (F x - (∑ i, F (Function.update c i (x i))) + (n : ℝ) * F c)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, jointWeight q c *
        |F x - (∑ i, F (Function.update c i (x i))) + (n : ℝ) * F c| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [abs_mul, abs_of_nonneg (hWeight c)]
    _ ≤ ∑ c, jointWeight q c * ((n : ℝ) * delta) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left
        (D2_pointwise_mixed_difference_bound F delta hdelta x c) (hWeight c)
    _ = (n : ℝ) * delta := by
      rw [← Finset.sum_mul]
      rw [hNorm]
      ring

end ProductExpectation

section DownstreamCompression

variable {R : Type*} [Fintype R] [DecidableEq R]

def cardinalityFamily (k : ℕ) : Finset (Finset R) :=
  Finset.univ.filter (fun S ↦ S.card = k)

noncomputable def finiteObjectiveMin
    (L : Finset R → ℝ) (k : ℕ) : ℝ :=
  if h : (cardinalityFamily (R := R) k).Nonempty then
    ((cardinalityFamily (R := R) k).image L).min'
      (Finset.image_nonempty.mpr h)
  else 0

theorem finiteObjectiveMin_attained
    (L : Finset R → ℝ) (k : ℕ)
    (hne : (cardinalityFamily (R := R) k).Nonempty) :
    ∃ S : Finset R, S.card = k ∧ L S = finiteObjectiveMin L k := by
  classical
  unfold finiteObjectiveMin
  rw [dif_pos hne]
  have hm := Finset.min'_mem ((cardinalityFamily (R := R) k).image L)
    (Finset.image_nonempty.mpr hne)
  rcases Finset.mem_image.mp hm with ⟨S, hS, hLS⟩
  refine ⟨S, ?_, hLS⟩
  simpa [cardinalityFamily] using hS

theorem D4_generic_uniform_objective_transfer
    (LF LA : Finset R → ℝ) (selected : Finset R) (k : ℕ) (eps : ℝ)
    (hSelectedCard : selected.card = k)
    (hSurrogateOptimal : ∀ S : Finset R, S.card = k → LA selected ≤ LA S)
    (hUniform : ∀ S : Finset R, S.card = k → |LF S - LA S| ≤ eps) :
    ∀ S : Finset R, S.card = k → LF selected ≤ LF S + 2 * eps := by
  intro S hS
  have hsel := abs_le.mp (hUniform selected hSelectedCard)
  have hcand := abs_le.mp (hUniform S hS)
  have hopt := hSurrogateOptimal S hS
  linarith

theorem D4_downstream_compression_min_corollary
    (LF LA : Finset R → ℝ) (selected : Finset R) (k n : ℕ)
    (delta : ℝ)
    (hne : (cardinalityFamily (R := R) k).Nonempty)
    (hSelectedCard : selected.card = k)
    (hSurrogateOptimal : ∀ S : Finset R, S.card = k → LA selected ≤ LA S)
    (hObjectivePerturbation : ∀ S : Finset R, S.card = k →
      |LF S - LA S| ≤ (n : ℝ) * delta) :
    LF selected ≤ finiteObjectiveMin LF k + 2 * (n : ℝ) * delta := by
  rcases finiteObjectiveMin_attained LF k hne with ⟨optimal, hOptCard, hOptValue⟩
  have h := D4_generic_uniform_objective_transfer LF LA selected k
    ((n : ℝ) * delta) hSelectedCard hSurrogateOptimal hObjectivePerturbation
    optimal hOptCard
  rw [hOptValue] at h
  linarith

/- With `n = m - 1`, the D3 pointwise product-surrogate theorem supplies the
uniform budget `(n : ℝ) * delta`.  This theorem records the exact final
decision-regret form once the downstream compression objective is known to be
1-Lipschitz with respect to that uniform world approximation. -/
theorem D4_product_route_decision_regret
    (LF LA : Finset R → ℝ) (selected : Finset R) (k n : ℕ)
    (delta : ℝ)
    (hne : (cardinalityFamily (R := R) k).Nonempty)
    (hSelectedCard : selected.card = k)
    (hSurrogateOptimal : ∀ S : Finset R, S.card = k → LA selected ≤ LA S)
    (hCompressionLipschitz : ∀ S : Finset R, S.card = k →
      |LF S - LA S| ≤ (n : ℝ) * delta) :
    LF selected ≤ finiteObjectiveMin LF k + 2 * (n : ℝ) * delta :=
  D4_downstream_compression_min_corollary LF LA selected k n delta hne
    hSelectedCard hSurrogateOptimal hCompressionLipschitz

/-! Actual compression objective for Chain D.  The same retained product-
response components are subtracted from the true world and its full additive
product surrogate.  Their residual functions therefore differ pointwise by
exactly `F - A_q`. -/

noncomputable def productCompressionLoss {n : ℕ}
    [Fintype U] [Nonempty U]
    (H : (Fin (n + 1) → U) → ℝ)
    (Q : Fin (n + 1) → U → ℝ)
    (selected : Finset (Fin (n + 1))) : ℝ :=
  osc (fun x ↦ H x - selected.sum (fun j ↦ Q j (x j))) / 2

theorem compressionLoss_uniform_world_transfer {n : ℕ}
    [Fintype U] [Nonempty U]
    (H A : (Fin (n + 1) → U) → ℝ)
    (Q : Fin (n + 1) → U → ℝ)
    (selected : Finset (Fin (n + 1))) (eps : ℝ)
    (hSup : ∀ x, |H x - A x| ≤ eps) :
    |productCompressionLoss H Q selected -
        productCompressionLoss A Q selected| ≤ eps := by
  let base : (Fin (n + 1) → U) → ℝ := fun x ↦
    A x - selected.sum (fun j ↦ Q j (x j))
  let err : (Fin (n + 1) → U) → ℝ := fun x ↦ H x - A x
  have hfun : (fun x ↦ base x + err x) =
      (fun x ↦ H x - selected.sum (fun j ↦ Q j (x j))) := by
    funext x
    dsimp [base, err]
    ring
  have hoscErr : osc err ≤ 2 * eps := by
    have hmax : maxVal err ≤ eps := by
      apply maxVal_le
      intro x
      exact (abs_le.mp (hSup x)).2
    have hmin : -eps ≤ minVal err := by
      apply le_minVal
      intro x
      exact (abs_le.mp (hSup x)).1
    simp only [osc]
    linarith
  have hosc := osc_add_deviation base err
  rw [hfun] at hosc
  unfold productCompressionLoss
  change |osc (fun x ↦ H x - selected.sum (fun j ↦ Q j (x j))) / 2 -
      osc base / 2| ≤ eps
  rw [show osc (fun x ↦ H x - selected.sum (fun j ↦ Q j (x j))) / 2 -
      osc base / 2 =
      (osc (fun x ↦ H x - selected.sum (fun j ↦ Q j (x j))) -
        osc base) / 2 by ring, abs_div]
  norm_num
  linarith

theorem D4_product_compression_objective_perturbation {n : ℕ}
    [Fintype U] [Nonempty U]
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected : Finset (Fin (n + 1))) :
    |productCompressionLoss F (productResponse q F) selected -
      productCompressionLoss (productA q F) (productResponse q F) selected| ≤
        (n : ℝ) * delta := by
  apply compressionLoss_uniform_world_transfer F (productA q F)
    (productResponse q F) selected ((n : ℝ) * delta)
  intro x
  exact D3_product_surrogate_mixed_difference_bound q F delta hWeight hNorm
    hDeltaNonneg hdelta x

theorem D5_product_compression_decision_regret {n : ℕ}
    [Fintype U] [Nonempty U]
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (hne : (cardinalityFamily (R := Fin (n + 1)) k).Nonempty)
    (hSelectedCard : selected.card = k)
    (hSurrogateOptimal : ∀ S : Finset (Fin (n + 1)), S.card = k →
      productCompressionLoss (productA q F) (productResponse q F) selected ≤
        productCompressionLoss (productA q F) (productResponse q F) S) :
    productCompressionLoss F (productResponse q F) selected ≤
      finiteObjectiveMin (fun S ↦
        productCompressionLoss F (productResponse q F) S) k +
          2 * (n : ℝ) * delta := by
  apply D4_downstream_compression_min_corollary
    (fun S ↦ productCompressionLoss F (productResponse q F) S)
    (fun S ↦ productCompressionLoss (productA q F) (productResponse q F) S)
    selected k n delta hne hSelectedCard hSurrogateOptimal
  intro S hS
  exact D4_product_compression_objective_perturbation q F delta hWeight hNorm
    hDeltaNonneg hdelta S

/-! ## Top-C connector on the full Cartesian action space -/

noncomputable def liftedProductComponent {n : ℕ}
    [Fintype U] [Nonempty U]
    (Q : Fin (n + 1) → U → ℝ)
    (j : Fin (n + 1)) (x : Fin (n + 1) → U) : ℝ := Q j (x j)

theorem maxVal_liftedProductComponent {n : ℕ}
    [Fintype U] [Nonempty U]
    (Q : Fin (n + 1) → U → ℝ) (j : Fin (n + 1)) :
    maxVal (liftedProductComponent Q j) = maxVal (Q j) := by
  apply le_antisymm
  · apply maxVal_le
    intro x
    exact le_maxVal (Q j) (x j)
  · rcases exists_eq_maxVal (Q j) with ⟨u, hu⟩
    let x : Fin (n + 1) → U :=
      Function.update (fun _ ↦ Classical.choice (inferInstance : Nonempty U)) j u
    calc
      maxVal (Q j) = Q j u := hu.symm
      _ = liftedProductComponent Q j x := by simp [liftedProductComponent, x]
      _ ≤ maxVal (liftedProductComponent Q j) :=
        le_maxVal (liftedProductComponent Q j) x

theorem minVal_liftedProductComponent {n : ℕ}
    [Fintype U] [Nonempty U]
    (Q : Fin (n + 1) → U → ℝ) (j : Fin (n + 1)) :
    minVal (liftedProductComponent Q j) = minVal (Q j) := by
  apply le_antisymm
  · rcases exists_eq_minVal (Q j) with ⟨u, hu⟩
    let x : Fin (n + 1) → U :=
      Function.update (fun _ ↦ Classical.choice (inferInstance : Nonempty U)) j u
    calc
      minVal (liftedProductComponent Q j) ≤ liftedProductComponent Q j x :=
        minVal_le (liftedProductComponent Q j) x
      _ = Q j u := by simp [liftedProductComponent, x]
      _ = minVal (Q j) := hu
  · apply le_minVal
    intro x
    exact minVal_le (Q j) (x j)

theorem componentSpan_liftedProductComponent {n : ℕ}
    [Fintype U] [Nonempty U]
    (Q : Fin (n + 1) → U → ℝ) (j : Fin (n + 1)) :
    componentSpan (liftedProductComponent Q) j = osc (Q j) := by
  simp only [componentSpan, componentMax, componentMin, osc,
    maxVal_liftedProductComponent, minVal_liftedProductComponent]

theorem fullProduct_supportOsc_modular {n : ℕ}
    [Fintype U] [Nonempty U]
    (Q : Fin (n + 1) → U → ℝ) (T : Finset (Fin (n + 1))) :
    supportOsc T (liftedProductComponent Q) = T.sum (fun j ↦ osc (Q j)) := by
  let amax : Fin (n + 1) → U := fun j ↦
    Classical.choose (exists_eq_maxVal (Q j))
  let amin : Fin (n + 1) → U := fun j ↦
    Classical.choose (exists_eq_minVal (Q j))
  have hmax : ∀ j ∈ T,
      liftedProductComponent Q j amax = componentMax (liftedProductComponent Q) j := by
    intro j hj
    have hchoice := Classical.choose_spec (exists_eq_maxVal (Q j))
    simp only [liftedProductComponent, componentMax,
      maxVal_liftedProductComponent]
    exact hchoice
  have hmin : ∀ j ∈ T,
      liftedProductComponent Q j amin = componentMin (liftedProductComponent Q) j := by
    intro j hj
    have hchoice := Classical.choose_spec (exists_eq_minVal (Q j))
    simp only [liftedProductComponent, componentMin,
      minVal_liftedProductComponent]
    exact hchoice
  rw [BH4_coextremizable_exactness T (liftedProductComponent Q) amax amin hmax hmin]
  unfold modularSpan
  apply Finset.sum_congr rfl
  intro j hj
  exact componentSpan_liftedProductComponent Q j

theorem productA_compression_loss_formula {n : ℕ}
    [Fintype U] [Nonempty U]
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1))) :
    productCompressionLoss (productA q F) (productResponse q F) selected =
      selectedᶜ.sum (fun j ↦ osc (productResponse q F j)) / 2 := by
  let Q := productResponse q F
  let c : ℝ := -(((Fintype.card (Fin (n + 1)) : ℝ) - 1) * productB q F)
  have hfun :
      (fun x ↦ productA q F x - selected.sum (fun j ↦ Q j (x j))) =
      (fun x ↦ sumComponent selectedᶜ (liftedProductComponent Q) x + c) := by
    funext x
    have hsum := Finset.sum_add_sum_compl selected (fun j ↦ Q j (x j))
    unfold productA surrogate sumComponent liftedProductComponent
    dsimp [Q, c]
    linarith
  unfold productCompressionLoss
  change osc (fun x ↦ productA q F x - selected.sum (fun j ↦ Q j (x j))) / 2 = _
  rw [hfun, osc_add_const]
  have hmod := fullProduct_supportOsc_modular Q selectedᶜ
  unfold supportOsc at hmod
  rw [hmod]

theorem productA_topC_surrogate_optimal {n : ℕ}
    [Fintype U] [Nonempty U]
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore (fun j ↦ osc (productResponse q F j)) selected k) :
    ∀ S : Finset (Fin (n + 1)), S.card = k →
      productCompressionLoss (productA q F) (productResponse q F) selected ≤
        productCompressionLoss (productA q F) (productResponse q F) S := by
  intro S hS
  rw [productA_compression_loss_formula q F selected,
    productA_compression_loss_formula q F S]
  exact div_le_div_of_nonneg_right
    (topK_implies_omitted_modular_min
      (fun j ↦ osc (productResponse q F j)) selected S k hTop hS)
    (by norm_num)

theorem D6_product_topC_compression_decision_regret {n : ℕ}
    [Fintype U] [Nonempty U]
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore (fun j ↦ osc (productResponse q F j)) selected k) :
    productCompressionLoss F (productResponse q F) selected ≤
      finiteObjectiveMin (fun S ↦
        productCompressionLoss F (productResponse q F) S) k +
          2 * (n : ℝ) * delta := by
  have hne : (cardinalityFamily (R := Fin (n + 1)) k).Nonempty := by
    exact ⟨selected, by simp [cardinalityFamily, hTop.1]⟩
  exact D5_product_compression_decision_regret q F delta hWeight hNorm
    hDeltaNonneg hdelta selected k hne hTop.1
    (productA_topC_surrogate_optimal q F selected k hTop)

end DownstreamCompression

end CIGAMF.V4.ProductMixedDifference
