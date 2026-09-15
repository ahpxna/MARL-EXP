import «LeanProductMixedDifferenceV4»
import «LeanD6InformationLimitV1»

/-! Explicit threshold worlds for the D6 bridge. All coordinates and losses
below use the existing product-response API; no distance-loss assumption. -/
namespace CIGAMF.P13.D6Threshold
open scoped BigOperators
open Finset
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry

variable {n : ℕ}
abbrev I (n : ℕ) := Fin (n + 1)

def bit (b : Bool) : ℝ := if b then 1 else 0
@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl

theorem bit_bounds (b : Bool) : 0 ≤ bit b ∧ bit b ≤ 1 := by cases b <;> norm_num

def count (B : Finset (I n)) (x : I n → Bool) : ℕ :=
  (B.filter (fun i => x i = true)).card

def others (A : Finset (I n)) (j : I n) : Finset (I n) := (univ \ A).erase j

def gate (A : Finset (I n)) (j : I n) (x : I n → Bool) : ℝ :=
  if x j then 0 else if (∃ i ∈ A, x i = true) ∨ 2 ≤ count (others A j) x then 1 else 0

def coeff (A : Finset (I n)) (j : I n) (mu : ℝ) (i : I n) : ℝ :=
  if i ∈ A then 0 else if i = j then mu - 1 else 1 - mu

def slope (A : Finset (I n)) (j : I n) (mu : ℝ) (i : I n) : ℝ :=
  if i ∈ A then 1 else if i = j then mu - 1 else 1 - mu

noncomputable def linear (c : I n → ℝ) (x : I n → Bool) : ℝ :=
  ∑ i, c i * bit (x i)

noncomputable def world (A : Finset (I n)) (j : I n) (mu : ℝ) (x : I n → Bool) : ℝ :=
  linear (coeff A j mu) x + gate A j x

def zero : I n → Bool := fun _ => false

def corner (_i : I n) (u : Bool) : ℝ := if u then 0 else 1

theorem corner_weight (c : I n → Bool) : jointWeight corner c = if c = zero then 1 else 0 := by
  classical
  unfold jointWeight corner
  by_cases h : c = zero
  · subst c; simp [zero]
  · rw [ite_eq_right h]
    have he : ∃ i, c i = true := by
      by_contra hn
      push Not at hn
      apply h
      funext i
      simpa [zero] using Bool.eq_false_iff.mpr (hn i)
    obtain ⟨i, hi⟩ := he
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

theorem corner_nonnegative (c : I n → Bool) : 0 ≤ jointWeight corner c := by
  rw [corner_weight]; split <;> norm_num

theorem corner_normalized : ∑ c : I n → Bool, jointWeight corner c = 1 := by
  classical
  simp [corner_weight]

theorem corner_response (F : (I n → Bool) → ℝ) (i : I n) (u : Bool) :
    productResponse corner F i u = F (Function.update zero i u) := by
  classical
  simp [productResponse, productExpectation, corner_weight]

theorem gate_bounds (A : Finset (I n)) (j : I n) (x : I n → Bool) :
    0 ≤ gate A j x ∧ gate A j x ≤ 1 := by
  unfold gate
  split <;> (try split) <;> norm_num

theorem count_mono (B : Finset (I n)) (x y : I n → Bool)
    (h : ∀ i, x i = true → y i = true) : count B x ≤ count B y := by
  apply card_le_card
  intro i hi
  exact mem_filter.mpr ⟨(mem_filter.mp hi).1, h i (mem_filter.mp hi).2⟩

theorem gate_update_mono (A : Finset (I n)) (j i : I n) (hij : i ≠ j)
    (x : I n → Bool) :
    gate A j (Function.update x i false) ≤ gate A j (Function.update x i true) := by
  classical
  have hm : ∀ l, Function.update x i false l = true → Function.update x i true l = true := by
    intro l hl
    by_cases hli : l = i
    · subst l; simp at hl
    · simpa [Function.update_of_ne hli] using hl
  have hc := count_mono (others A j) _ _ hm
  have he : (∃ l ∈ A, Function.update x i false l = true) →
      ∃ l ∈ A, Function.update x i true l = true := by
    rintro ⟨l, hl, ht⟩; exact ⟨l, hl, hm l ht⟩
  simp only [gate, Function.update_of_ne (Ne.symm hij)]
  split
  · rfl
  · by_cases hp : (∃ l ∈ A, Function.update x i false l = true) ∨
        2 ≤ count (others A j) (Function.update x i false)
    · have hq : (∃ l ∈ A, Function.update x i true l = true) ∨
          2 ≤ count (others A j) (Function.update x i true) := by
        rcases hp with hp | hp
        · exact Or.inl (he hp)
        · exact Or.inr (le_trans hp hc)
      simp [hp, hq]
    · simp [hp]
      split <;> norm_num

theorem linear_difference (c : I n → ℝ) (x : I n → Bool) (i : I n) (u v : Bool) :
    linear c (Function.update x i u) - linear c (Function.update x i v) =
      c i * (bit u - bit v) := by
  classical
  unfold linear
  rw [← sum_sub_distrib]
  rw [sum_eq_single i]
  · simp [mul_sub]
  · intro l _ hli
    simp [Function.update_of_ne hli]
  · simp

theorem derivative_bounds (A : Finset (I n)) (j i : I n) (mu : ℝ)
    (x : I n → Bool) :
    coeff A j mu i - (if i = j then 1 else 0) ≤
      world A j mu (Function.update x i true) - world A j mu (Function.update x i false) ∧
    world A j mu (Function.update x i true) - world A j mu (Function.update x i false) ≤
      coeff A j mu i + (if i = j then 0 else 1) := by
  have hl := linear_difference (coeff A j mu) x i true false
  simp only [bit_true, bit_false, sub_zero, mul_one] at hl
  have h0 := gate_bounds A j (Function.update x i false)
  have h1 := gate_bounds A j (Function.update x i true)
  by_cases hij : i = j
  · subst i
    have hz : gate A j (Function.update x j true) = 0 := by simp [gate]
    simp only [ite_true, world, hz]
    constructor <;> linarith
  · have hm := gate_update_mono A j i hij x
    simp only [ite_eq_right hij, sub_zero, world]
    constructor <;> linarith

theorem mixed_bound (A : Finset (I n)) (j : I n) (mu : ℝ)
    (i : I n) (x c : I n → Bool) : |mixedDifference (world A j mu) i x c| ≤ 1 := by
  have hx := derivative_bounds A j i mu x
  have hc := derivative_bounds A j i mu c
  have ex : Function.update x i (x i) = x := Function.update_eq_self i x
  have ec : Function.update c i (c i) = c := Function.update_eq_self i c
  unfold mixedDifference
  cases hxi : x i <;> cases hci : c i
  all_goals
    simp only [hxi] at ex
    simp only [hci] at ec
    simp only [ex, ec] at hx hc ⊢
    rw [abs_le]
    split_ifs at hx hc <;> constructor <;> linarith

@[simp] theorem linear_zero (c : I n → ℝ) : linear c zero = 0 := by simp [linear, zero]
@[simp] theorem gate_zero (A : Finset (I n)) (j : I n) : gate A j zero = 0 := by
  simp [gate, zero, count]

theorem gate_unit (A : Finset (I n)) (j i : I n) (hj : j ∉ A) (u : Bool) :
    gate A j (Function.update zero i u) = if i ∈ A then bit u else 0 := by
  classical
  cases u
  · have hz : Function.update (zero : I n → Bool) i false = zero :=
      Function.update_eq_self i zero
    rw [hz, gate_zero]
    simp
  · have hc : count (others A j) (Function.update zero i true) ≤ 1 := by
      apply le_trans (card_le_card (show (others A j).filter
        (fun l => Function.update zero i true l = true) ⊆ {i} from ?_)) (by simp)
      intro l hl
      by_contra hn
      have hli : l ≠ i := by simpa using hn
      simpa [Function.update_of_ne hli, zero] using (mem_filter.mp hl).2
    by_cases hi : i = j
    · subst i; simp [gate, hj]
    · have he : (∃ l ∈ A, Function.update zero i true l = true) ↔ i ∈ A := by
        constructor
        · rintro ⟨l, hl, ht⟩
          by_cases hli : l = i
          · simpa [hli] using hl
          · simp [Function.update_of_ne hli, zero] at ht
        · intro h; exact ⟨i, h, by simp⟩
      simp [gate, Function.update_of_ne (Ne.symm hi), zero, he,
        show ¬2 ≤ count (others A j) (Function.update zero i true) from by omega]

theorem world_response (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (i : I n) (u : Bool) :
    productResponse corner (world A j mu) i u = slope A j mu i * bit u := by
  rw [corner_response]
  have h := linear_difference (coeff A j mu) zero i u false
  have hz : Function.update (zero : I n → Bool) i false = zero := by
    exact Function.update_eq_self i zero
  rw [hz, linear_zero, bit_false] at h
  simp only [sub_zero] at h
  rw [world, h, gate_unit A j i hj]
  unfold coeff slope
  split_ifs <;> ring

/-- At the tie endpoint the *entire response functions* carry no A-information. -/
theorem response_independent (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (i : I n) (u : Bool) :
    productResponse corner (world A j 0) i u = (if i = j then -1 else 1) * bit u := by
  rw [world_response A j hj]
  by_cases hi : i ∈ A
  · have hij : i ≠ j := by intro h; subst i; contradiction
    simp [slope, hi, hij]
  · simp [slope, hi]

def residualCoeff (A S : Finset (I n)) (j : I n) (mu : ℝ) (i : I n) : ℝ :=
  coeff A j mu i - if i ∈ S then slope A j mu i else 0

noncomputable def residual (A S : Finset (I n)) (j : I n) (mu : ℝ)
    (x : I n → Bool) : ℝ := linear (residualCoeff A S j mu) x + gate A j x

theorem residual_is_actual (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (x : I n → Bool) :
    world A j mu x - ∑ i ∈ S, productResponse corner (world A j mu) i (x i) =
      residual A S j mu x := by
  simp_rw [world_response A j hj]
  simp [world, residual, linear, residualCoeff, sub_mul, ite_mul, sum_sub_distrib]
  ring

def lowCorner (A S : Finset (I n)) (j : I n) : I n → Bool :=
  fun i => decide (i = j ∨ i ∈ S ∩ A)

def highCorner (S : Finset (I n)) (j : I n) : I n → Bool :=
  fun i => decide (i ≠ j ∧ i ∉ S)

theorem linear_extremes (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (_hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (x : I n → Bool) :
    linear (residualCoeff A S j mu) (lowCorner A S j) ≤
      linear (residualCoeff A S j mu) x ∧
    linear (residualCoeff A S j mu) x ≤
      linear (residualCoeff A S j mu) (highCorner S j) := by
  constructor <;> apply sum_le_sum <;> intro i _
  all_goals
    by_cases hij : i = j
    · subst i
      by_cases hjS : j ∈ S <;> cases hxi : x j <;>
        simp [residualCoeff, coeff, slope, bit, lowCorner, highCorner, hj, hjS]; linarith
    · by_cases hiA : i ∈ A <;> by_cases hiS : i ∈ S <;> cases hxi : x i <;>
        simp [residualCoeff, coeff, slope, bit, lowCorner, highCorner, hiA, hiS, hij]; linarith

@[simp] theorem gate_low (A S : Finset (I n)) (j : I n) :
    gate A j (lowCorner A S j) = 0 := by simp [gate, lowCorner]

theorem gate_high (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (hcard : S.card = A.card) (hB : 2 ≤ (others A j).card) :
    gate A j (highCorner S j) = 1 := by
  classical
  have hg : (∃ i ∈ A, highCorner S j i = true) ∨
      2 ≤ count (others A j) (highCorner S j) := by
    by_cases hAS : A ⊆ S
    · have heq : A = S := eq_of_subset_of_card_le hAS (by omega)
      right
      have hf : (others A j).filter (fun i => highCorner S j i = true) = others A j := by
        apply filter_eq_self.mpr
        intro i hi
        have hm := mem_erase.mp hi
        have ha := (mem_sdiff.mp hm.2).2
        simp [highCorner, hm.1, ← heq, ha]
      simpa [count, hf] using hB
    · left
      obtain ⟨i, hiA, hiS⟩ := not_subset.mp hAS
      have hij : i ≠ j := by intro h; subst i; contradiction
      exact ⟨i, hiA, by simp [highCorner, hij, hiS]⟩
  have hz : highCorner S j j = false := by simp [highCorner]
  simp only [gate, hz, Bool.false_eq_true, ↓reduceIte, hg]

theorem residual_extremes (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcard : S.card = A.card) (hB : 2 ≤ (others A j).card) (x : I n → Bool) :
    residual A S j mu (lowCorner A S j) ≤ residual A S j mu x ∧
    residual A S j mu x ≤ residual A S j mu (highCorner S j) := by
  have hl := linear_extremes A S j hj mu hmu hmu1 x
  have hg := gate_bounds A j x
  simp only [residual, gate_low, gate_high A S j hj hcard hB, add_zero]
  constructor <;> linarith

theorem osc_of_extremes {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (lo hi : Ω) (hlo : ∀ x, f lo ≤ f x) (hhi : ∀ x, f x ≤ f hi) :
    osc f = f hi - f lo := by
  have hmax := le_antisymm (maxVal_le f hhi) (le_maxVal f hi)
  have hmin := le_antisymm (minVal_le f lo) (le_minVal f hlo)
  simp [osc, hmax, hmin]

theorem residual_range (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hcard : S.card = A.card) (hbal : Aᶜ.card = A.card)
    (hB : 2 ≤ (others A j).card) :
    residual A S j mu (highCorner S j) - residual A S j mu (lowCorner A S j) =
      1 + (2 - mu) * (S ∩ A).card := by
  classical
  have hc : (Aᶜ \ S).card = (S ∩ A).card := by
    rw [card_sdiff_comm (hbal.trans hcard.symm)]
    congr 1
    ext i; simp
  have hw : ∀ i, residualCoeff A S j mu i * bit (highCorner S j i) -
      residualCoeff A S j mu i * bit (lowCorner A S j i) =
      (if i ∈ S ∩ A then (1 : ℝ) else 0) + (if i ∈ Aᶜ \ S then 1-mu else 0) := by
    intro i
    by_cases hij : i = j
    · subst i
      by_cases hjS : j ∈ S <;>
        simp [residualCoeff, coeff, slope, bit, highCorner, lowCorner, hj, hjS]
    · by_cases hiA : i ∈ A <;> by_cases hiS : i ∈ S <;>
        simp [residualCoeff, coeff, slope, bit, highCorner, lowCorner, hiA, hiS, hij]
  simp only [residual, gate_high A S j hj hcard hB, gate_low, add_zero, linear]
  rw [add_comm _ 1, add_sub_assoc, ← sum_sub_distrib]
  simp_rw [hw]
  rw [sum_add_distrib]
  simp only [Finset.sum_ite_mem, univ_inter, sum_const, hc]
  ring

/-- The closed-form loss is derived from the actual product-response residual. -/
theorem actual_loss (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcard : S.card = A.card) (hbal : Aᶜ.card = A.card)
    (hB : 2 ≤ (others A j).card) :
    productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) S =
      (1 + (2 - mu) * (S ∩ A).card) / 2 := by
  unfold productCompressionLoss
  simp_rw [residual_is_actual A S j hj]
  rw [osc_of_extremes (residual A S j mu) (lowCorner A S j) (highCorner S j)
    (fun x => (residual_extremes A S j hj mu hmu hmu1 hcard hB x).1)
    (fun x => (residual_extremes A S j hj mu hmu hmu1 hcard hB x).2)]
  rw [residual_range A S j hj mu hcard hbal hB]


/-- The complement is a feasible optimum; the assertion uses the actual loss. -/
theorem actual_regret (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcard : S.card = A.card) (hbal : Aᶜ.card = A.card)
    (hB : 2 ≤ (others A j).card) :
    productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) S -
      productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) Aᶜ =
      (2 - mu) * (S ∩ A).card / 2 := by
  rw [actual_loss A S j hj mu hmu hmu1 hcard hbal hB,
    actual_loss A Aᶜ j hj mu hmu hmu1 hbal hbal hB]
  have he : Aᶜ ∩ A = ∅ := by ext i; simp
  rw [he]
  simp only [card_empty, Nat.cast_zero, mul_zero, add_zero]
  ring

theorem complement_optimal (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcard : S.card = A.card) (hbal : Aᶜ.card = A.card)
    (hB : 2 ≤ (others A j).card) :
    productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) Aᶜ ≤
      productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) S := by
  apply sub_nonneg.mp
  rw [actual_regret A S j hj mu hmu hmu1 hcard hbal hB]
  exact div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (by norm_num)

/-- A support-geometry realization. `none` is an always-omitted interaction
component. The feasible selections are exactly images of original selections;
allowing the interaction component to be selected would change the problem. -/
noncomputable def supportComponents (F : (I n → Bool) → ℝ)
    (Q : I n → Bool → ℝ) : Option (I n) → (I n → Bool) → ℝ
  | none, x => F x - ∑ i, Q i (x i)
  | some i, x => Q i (x i)

def liftedSelection (S : Finset (I n)) : Finset (Option (I n)) := S.image some

theorem sum_lifted (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ)
    (S : Finset (I n)) (x : I n → Bool) :
    ∑ i ∈ liftedSelection S, supportComponents F Q i x = ∑ i ∈ S, Q i (x i) := by
  rw [liftedSelection, sum_image]
  · rfl
  · intro a _ b _ h; exact Option.some.inj h

theorem sum_omitted_lift (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ)
    (S : Finset (I n)) (x : I n → Bool) :
    sumComponent (liftedSelection S)ᶜ (supportComponents F Q) x =
      F x - ∑ i ∈ S, Q i (x i) := by
  have h := (liftedSelection S).sum_add_sum_compl (fun i => supportComponents F Q i x)
  rw [sum_lifted] at h
  have hu : ∑ i : Option (I n), supportComponents F Q i x = F x := by
    rw [Fintype.sum_option]
    simp [supportComponents]
  rw [hu] at h
  unfold sumComponent
  linarith

/-- Equality with the existing support radius, not an abstract loss model. -/
theorem actual_support_bridge (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ)
    (S : Finset (I n)) :
    selectedRadius (supportComponents F Q) (liftedSelection S) =
      productCompressionLoss F Q S := by
  unfold selectedRadius supportOsc productCompressionLoss
  congr 2
  funext x
  exact sum_omitted_lift F Q S x

/-- Geometric image points use the same coordinate functions in every world. -/
noncomputable def supportPoint (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ)
    (x : I n → Bool) : Option (I n) → ℝ := fun i => supportComponents F Q i x

noncomputable def actualSupport (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ) :
    Set (Option (I n) → ℝ) := Set.range (supportPoint F Q)

theorem point_projection (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ)
    (x : I n → Bool) (i : Option (I n)) :
    supportPoint F Q x i = supportComponents F Q i x := rfl

/-- Geometry-only partial identification: all ordinary coordinate projections
agree at each indexed state; only the interaction coordinate can differ. -/
theorem support_observed_coordinates_equal (A A' : Finset (I n)) (j : I n)
    (hj : j ∉ A) (hj' : j ∉ A') (x : I n → Bool) (i : I n) :
    supportPoint (world A j 0) (productResponse corner (world A j 0)) x (some i) =
    supportPoint (world A' j 0) (productResponse corner (world A' j 0)) x (some i) := by
  simp only [supportPoint, supportComponents, response_independent A j hj,
    response_independent A' j hj']

/-- A joint measurement with the distinguished coordinate on is an exact
counting measurement of B; this establishes the measurement model from F. -/
def jointCorner (G : Finset (I n)) (j : I n) : I n → Bool :=
  fun i => decide (i = j ∨ i ∈ G)

theorem joint_measurement (A G : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) :
    world A j mu (jointCorner G j) =
      (1-mu) * ((G ∩ others A j).card : ℝ) - (1-mu) := by
  have hg : gate A j (jointCorner G j) = 0 := by simp [gate, jointCorner]
  have hw : ∀ i, coeff A j mu i * bit (jointCorner G j i) =
      (if i ∈ G ∩ others A j then 1-mu else 0) + (if i = j then mu-1 else 0) := by
    intro i
    by_cases hij : i = j
    · subst i; simp [coeff, bit, jointCorner, others, hj]
    · by_cases hiA : i ∈ A <;> by_cases hiG : i ∈ G <;>
        simp [coeff, bit, jointCorner, others, hiA, hiG, hij]
  simp only [world, hg, add_zero, linear]
  simp_rw [hw]
  rw [sum_add_distrib]
  simp only [Finset.sum_ite_mem, univ_inter, sum_const]
  simp
  ring

/-- At mu=0, the compression regret is exactly the number of mistaken retained
A-coordinates. This includes every feasible S, whether or not it contains j. -/
theorem tie_actual_regret (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (hcard : S.card = A.card) (hbal : Aᶜ.card = A.card)
    (hB : 2 ≤ (others A j).card) :
    productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) S -
      productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Aᶜ =
      (S ∩ A).card := by
  rw [actual_regret A S j hj 0 (by norm_num) (by norm_num) hcard hbal hB]
  ring


section Randomized
variable (r : ℕ) (j : I (2*r+1))

def positiveGround : Finset (I (2*r+1)) := univ.erase j
def worlds : Finset (Finset (I (2*r+1))) := (positiveGround r j).powersetCard (r+1)
def actions : Finset (Finset (I (2*r+1))) := univ.powersetCard (r+1)

@[simp] theorem positiveGround_card : (positiveGround r j).card = 2*r+1 := by
  simp [positiveGround, I]

theorem worlds_nonempty : (worlds r j).Nonempty := by
  apply powersetCard_nonempty.mpr
  rw [positiveGround_card]
  omega

theorem world_parameters (hr : 2 ≤ r) {A : Finset (I (2*r+1))}
    (hA : A ∈ worlds r j) :
    j ∉ A ∧ A.card = r+1 ∧ Aᶜ.card = A.card ∧ 2 ≤ (others A j).card := by
  have hp := mem_powersetCard.mp hA
  have hj : j ∉ A := by
    intro h; exact (mem_erase.mp (hp.1 h)).1 rfl
  have hb : Aᶜ.card = A.card := by
    rw [card_compl, hp.2]
    simp [I]
    omega
  refine ⟨hj, hp.2, hb, ?_⟩
  have hB : (others A j).card = Aᶜ.card - 1 := by
    unfold others
    rw [card_erase_of_mem (by simp [hj])]
    rfl
  rw [hB, hb, hp.2]
  omega

/-- Exact uniform-world average for any legal action. The extra +1 penalty
for omitting j is retained through the factor `(S.erase j).card`. -/
theorem average_intersection (S : Finset (I (2*r+1))) :
    (2*r+1) * (∑ A ∈ worlds r j, (S ∩ A).card) =
      (S.erase j).card * (r+1) * (worlds r j).card := by
  let P := S.erase j
  let W := worlds r j
  have hP : P ⊆ positiveGround r j := by
    intro i hi; exact mem_erase.mpr ⟨(mem_erase.mp hi).1, mem_univ i⟩
  have hdiff := CIGAMF.P13.InformationLimit.sum_sdiff_card_powersetCard
    (positiveGround r j) (r+1) P hP
  rw [positiveGround_card, Nat.add_sub_cancel] at hdiff
  have hsplit : (∑ A ∈ W, (P \ A).card) + (∑ A ∈ W, (P ∩ A).card) =
      P.card * W.card := by
    rw [← sum_add_distrib]
    simp_rw [card_sdiff_add_card_inter]
    simp [Nat.mul_comm]
  change (∑ T ∈ W, (P \ T).card) = P.card * (2*r).choose (r+1) at hdiff
  rw [hdiff] at hsplit
  have hchoose := CIGAMF.P13.InformationLimit.choose_shift r
  have hW : W.card = (2*r+1).choose (r+1) := by
    simp [W, worlds]
  rw [← hW] at hchoose
  have he : ∀ A ∈ W, P ∩ A = S ∩ A := by
    intro A hA
    have hj : j ∉ A := by
      intro h; exact (mem_erase.mp ((mem_powersetCard.mp hA).1 h)).1 rfl
    ext i
    simp only [mem_inter, P, mem_erase]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · intro h; exact ⟨⟨fun hij => hj (hij ▸ h.2), h.1⟩, h.2⟩
  have hsumEq : (∑ A ∈ W, (P ∩ A).card) = ∑ A ∈ W, (S ∩ A).card :=
    sum_congr rfl (fun A hA => congrArg Finset.card (he A hA))
  rw [hsumEq] at hsplit
  have h1 := congrArg (fun z : ℕ => (2*r+1)*z) hsplit
  have h2 := congrArg (fun z : ℕ => P.card*z) hchoose
  change (2*r+1) * (∑ A ∈ W, (S ∩ A).card) = P.card*(r+1)*W.card
  nlinarith

theorem average_intersection_lower (S : Finset (I (2*r+1))) (hS : S.card = r+1) :
    (r : ℝ)*(r+1)*(worlds r j).card ≤
      (2*r+1 : ℝ) * ∑ A ∈ worlds r j, ((S ∩ A).card : ℝ) := by
  have hp : r ≤ (S.erase j).card := by
    by_cases hj : j ∈ S
    · rw [card_erase_of_mem hj, hS]; omega
    · rw [erase_eq_of_notMem hj, hS]; omega
  have hn := average_intersection r j S
  have hl : r*(r+1)*(worlds r j).card ≤
      (2*r+1)*(∑ A ∈ worlds r j, (S ∩ A).card) := by
    rw [hn]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hp)
  exact_mod_cast hl

/-- One world defeats the *whole mixture*. The adversary is outside the sum
and does not depend on the algorithm's realized random action. -/
theorem randomized_intersection_lower (p : Finset (I (2*r+1)) → ℝ)
    (hp : ∀ S ∈ actions r, 0 ≤ p S) (hnorm : ∑ S ∈ actions r, p S = 1) :
    ∃ A ∈ worlds r j,
      (r : ℝ)*(r+1) ≤ (2*r+1 : ℝ)*∑ S ∈ actions r, p S * (S ∩ A).card := by
  let g := fun A => (2*r+1 : ℝ)*∑ S ∈ actions r, p S * (S ∩ A).card
  have havg : (r : ℝ)*(r+1)*(worlds r j).card ≤ ∑ A ∈ worlds r j, g A := by
    calc
      _ = ∑ S ∈ actions r, p S * ((r : ℝ)*(r+1)*(worlds r j).card) := by
        rw [← sum_mul, hnorm]; ring
      _ ≤ ∑ S ∈ actions r, p S * ((2*r+1 : ℝ) *
          ∑ A ∈ worlds r j, ((S ∩ A).card : ℝ)) := by
        apply sum_le_sum
        intro S hS
        exact mul_le_mul_of_nonneg_left
          (average_intersection_lower r j S (mem_powersetCard.mp hS).2) (hp S hS)
      _ = ∑ A ∈ worlds r j, g A := by
        simp only [g, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro A _
        apply sum_congr rfl
        intro S _
        ring
  obtain ⟨A, hA, hm⟩ := exists_max_image (worlds r j) g (worlds_nonempty r j)
  refine ⟨A, hA, ?_⟩
  have hupper : ∑ A' ∈ worlds r j, g A' ≤ (worlds r j).card * g A := by
    calc _ ≤ ∑ _A' ∈ worlds r j, g A := sum_le_sum (fun A' hA' => hm A' hA')
         _ = _ := by simp
  have hw : (0 : ℝ) < (worlds r j).card := by
    exact_mod_cast card_pos.mpr (worlds_nonempty r j)
  change (r : ℝ)*(r+1) ≤ g A
  nlinarith

/-- All even dimensions m=2r+2 >=6. This is an actual-product-loss lower bound
against every randomized response-only decision rule on the common profile. -/
theorem randomized_actual_lower (hr : 2 ≤ r)
    (p : Finset (I (2*r+1)) → ℝ)
    (hp : ∀ S ∈ actions r, 0 ≤ p S) (hnorm : ∑ S ∈ actions r, p S = 1) :
    ∃ A ∈ worlds r j,
      (r : ℝ)*(r+1) / (2*r+1) ≤ ∑ S ∈ actions r, p S *
        (productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) S -
          productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Aᶜ) := by
  obtain ⟨A, hA, hl⟩ := randomized_intersection_lower r j p hp hnorm
  have ha := world_parameters r j hr hA
  refine ⟨A, hA, ?_⟩
  have he : ∀ S ∈ actions r,
      productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) S -
        productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Aᶜ =
          (S ∩ A).card := by
    intro S hS
    exact tie_actual_regret A S j ha.1 ((mem_powersetCard.mp hS).2.trans ha.2.1.symm)
      ha.2.2.1 ha.2.2.2
  have hs : (∑ S ∈ actions r, p S *
      (productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) S -
       productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Aᶜ)) =
      ∑ S ∈ actions r, p S * (S ∩ A).card := by
    apply sum_congr rfl
    intro S hS
    rw [he S hS]
  rw [hs]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*r+1)).mpr
  nlinarith
end Randomized


theorem osc_bit_nonneg (c : ℝ) (hc : 0 ≤ c) : osc (fun u : Bool => c * bit u) = c := by
  rw [osc_of_extremes (fun u : Bool => c * bit u) false true
    (by intro u; cases u <;> simp [hc]) (by intro u; cases u <;> simp [hc])]
  simp

theorem osc_bit_nonpos (c : ℝ) (hc : c ≤ 0) : osc (fun u : Bool => c * bit u) = -c := by
  rw [osc_of_extremes (fun u : Bool => c * bit u) true false
    (by intro u; cases u <;> simp [hc]) (by intro u; cases u <;> simp [hc])]
  simp

theorem response_span (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu1 : mu ≤ 1) (i : I n) :
    osc (productResponse corner (world A j mu) i) = if i ∈ A then 1 else 1-mu := by
  have he : productResponse corner (world A j mu) i = fun u => slope A j mu i * bit u := by
    funext u; exact world_response A j hj mu i u
  rw [he]
  by_cases hi : i ∈ A
  · simp only [slope, hi, ↓reduceIte]
    exact osc_bit_nonneg 1 (by norm_num)
  · by_cases hij : i = j
    · subst i
      simp only [slope, hj, ↓reduceIte]
      rw [osc_bit_nonpos (mu-1) (by linarith)]
      ring
    · simp only [slope, hi, hij, ↓reduceIte]
      exact osc_bit_nonneg (1-mu) (by linarith)

theorem selected_is_top (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    IsTopKByScore (fun i => osc (productResponse corner (world A j mu) i)) A A.card := by
  have hspan : (fun i => osc (productResponse corner (world A j mu) i)) =
      fun i => if i ∈ A then 1 else 1-mu := by
    funext i; exact response_span A j hj mu hmu1 i
  rw [hspan]
  refine ⟨rfl, ?_⟩
  intro S hS
  have ha : (∑ i ∈ A, if i ∈ A then (1 : ℝ) else 1-mu) = A.card := by
    calc _ = ∑ _i ∈ A, (1 : ℝ) := sum_congr rfl (fun i hi => by rw [ite_eq_left hi])
         _ = _ := by simp
  rw [ha]
  calc _ ≤ ∑ _i ∈ S, (1 : ℝ) := by
         apply sum_le_sum; intro i _; split <;> linarith
       _ = _ := by simp [hS]

theorem exact_top_gap (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hbal : Aᶜ.card = A.card) (hB : 2 ≤ (others A j).card) :
    2 * (productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) A -
      productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) Aᶜ) =
      A.card * (2-mu) := by
  rw [actual_regret A A j hj mu hmu hmu1 rfl hbal hB]
  simp only [inter_self]
  ring

/-- The upper normalization delta=1 is attained, not merely a loose bound. -/
theorem mixed_bound_attained (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (i : I n) (hi : i ∈ A) :
    ∃ x c : I n → Bool, mixedDifference (world A j mu) i x c = 1 := by
  have hij : i ≠ j := by intro h; subst i; contradiction
  let x := Function.update (zero : I n → Bool) i true
  let c := Function.update (zero : I n → Bool) j true
  refine ⟨x, c, ?_⟩
  have hxi : x i = true := by simp [x]
  have hci : c i = false := by simp [c, Function.update_of_ne hij, zero]
  have h0 : Function.update x i (c i) = zero := by
    rw [hci]; simp only [x, Function.update_idem]
    exact Function.update_eq_self i zero
  have hc : c = jointCorner ∅ j := by
    funext l; by_cases hlj : l = j <;> simp [c, jointCorner, zero, hlj]
  have hpair : Function.update c i (x i) = jointCorner {i} j := by
    rw [hxi]
    funext l
    by_cases hli : l = i
    · subst l; simp [jointCorner]
    · rw [Function.update_of_ne hli]
      by_cases hlj : l = j
      · subst l; simp [c, jointCorner]
      · simp [c, jointCorner, zero, hli, hlj]
  have hx : world A j mu x = 1 := by
    change world A j mu (Function.update zero i true) = 1
    rw [← corner_response (world A j mu) i true, world_response A j hj]
    simp [slope, hi]
  have hother : i ∉ others A j := by simp [others, hi]
  unfold mixedDifference
  rw [h0, hpair, hx, hc, joint_measurement A {i} j hj,
    joint_measurement A ∅ j hj]
  have he : ({i} : Finset (I n)) ∩ others A j = ∅ := by simp [hother]
  simp [he, world]


/-- Matching achievable value on this explicit family. Sample X uniformly
from the world-label family and retain X-complement, a legal k-subset.
This does not assert a matching upper bound on every admissible D6 function. -/
theorem uniform_family_value (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A : Finset (I (2*r+1))) (hA : A ∈ worlds r j) :
    (∑ X ∈ worlds r j,
      (productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Xᶜ -
        productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Aᶜ)) /
      (worlds r j).card = (r : ℝ)*(r+1)/(2*r+1) := by
  have ha := world_parameters r j hr hA
  have he : ∀ X ∈ worlds r j,
      productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Xᶜ -
        productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Aᶜ =
          ((A \ X).card : ℝ) := by
    intro X hX
    have hx := world_parameters r j hr hX
    rw [tie_actual_regret A Xᶜ j ha.1 (hx.2.2.1.trans (hx.2.1.trans ha.2.1.symm))
      ha.2.2.1 ha.2.2.2]
    congr 2
    ext i; simp; tauto
  have hs : (∑ X ∈ worlds r j,
      (productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Xᶜ -
        productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Aᶜ)) =
      ∑ X ∈ worlds r j, ((A \ X).card : ℝ) := sum_congr rfl he
  rw [hs]
  have hn := CIGAMF.P13.InformationLimit.information_limit_exact (positiveGround r j) r
    (positiveGround_card r j) A (mem_powersetCard.mp hA).1 ha.2.1
  change (2*r+1)*(∑ X ∈ worlds r j, (A \ X).card) =
    (r+1)*r*(worlds r j).card at hn
  have hreal : (2*r+1 : ℝ)*(∑ X ∈ worlds r j, ((A \ X).card : ℝ)) =
      (r+1)*r*(worlds r j).card := by exact_mod_cast hn
  have hw : (0 : ℝ) < (worlds r j).card := by
    exact_mod_cast card_pos.mpr (worlds_nonempty r j)
  apply (div_eq_div_iff (ne_of_gt hw) (by positivity : (2*r+1 : ℝ) ≠ 0)).mpr
  nlinarith

/-- Common observation supplied to any response-only randomized algorithm. -/
def commonResponse (j : I n) (i : I n) (u : Bool) : ℝ :=
  (if i = j then -1 else 1)*bit u

theorem common_profile (A : Finset (I n)) (j : I n) (hj : j ∉ A) :
    productResponse corner (world A j 0) = commonResponse j := by
  funext i u
  exact response_independent A j hj i u

/-- Complete observation-to-decision bridge. A single rule is applied to the
actual response of every constructed world; its output law is therefore fixed. -/
theorem response_rule_actual_lower (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (rule : (I (2*r+1) → Bool → ℝ) → Finset (I (2*r+1)) → ℝ)
    (hp : ∀ S ∈ actions r, 0 ≤ rule (commonResponse j) S)
    (hnorm : ∑ S ∈ actions r, rule (commonResponse j) S = 1) :
    ∃ A ∈ worlds r j,
      (r : ℝ)*(r+1)/(2*r+1) ≤ ∑ S ∈ actions r,
        rule (productResponse corner (world A j 0)) S *
          (productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) S -
            productCompressionLoss (world A j 0) (productResponse corner (world A j 0)) Aᶜ) := by
  obtain ⟨A, hA, hl⟩ := randomized_actual_lower r j hr (rule (commonResponse j)) hp hnorm
  refine ⟨A, hA, ?_⟩
  rw [common_profile A j (world_parameters r j hr hA).1] at ⊢
  rw [common_profile A j (world_parameters r j hr hA).1] at hl
  exact hl

end CIGAMF.P13.D6Threshold
