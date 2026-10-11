import «LeanD6ThresholdConstructionV1»

/-! # The Bernoulli product reference, and the algebraic form of the gate.

`LeanProductMixedDifferenceV4` already carries the whole compression chain at an
ARBITRARY product reference `q`: `productResponse`, `productCompressionLoss`,
`productA_compression_loss_formula` and `D6_product_topC_compression_decision_regret`
are all stated for a general `q`. The only corner-specific step in the existing
corpus is `corner_response`, which collapses the product expectation to a single
evaluation because `corner` is the point mass at `zero`. So the reference bridge
is not blocked by the architecture; it is blocked by one missing computation.

This module supplies the reusable half of that computation:

* `bern t` is the Bernoulli(t) product reference, with `bern 0 = corner` proved,
  so every corner theorem is literally the `t = 0` instance of what follows.
* `expectation_factor` turns a product expectation of a per-coordinate product
  into a product of per-coordinate sums. This is the tool `corner_response`
  replaced by a point evaluation.
* `gate_eq` rewrites the two-level `if` of `gate` as a polynomial in the bits.
* `leOne_expand` expands the "at most one of `B` is on" indicator as an explicit
  finite sum of per-coordinate products, which is what makes the gate's
  expectation factorable.

WHAT IS NOT HERE. The three slope identities

    productResponse (bern t) (world A z mu) i true
      - productResponse (bern t) (world A z mu) i false
        = a   for i in A,   = b   for i in others A z,   = a - 1   for i = z,
    where  c = (1-t)^(2k-2),  a = c*(1+(k-2)*t),  b = c*(k-2)*t,

are the next target and are NOT proved here. They follow from the four theorems
below by arithmetic plus the binomial tail
`E[leOne B] = (1-t)^|B| + |B|*t*(1-t)^(|B|-1)`, which is itself `Finset.prod_add`
restricted to subsets of size at most one. The three identities were checked
exactly (Fraction arithmetic, k = 3,4,5 and t in {0, 1/8, 1/4, 1/3, 1/2}, all 15
cells) against this file's `gate`, so the statements are known correct; they are
simply not yet machine-proved. Do not cite them as PROVED.
-/

namespace CIGAMF.P13.D6ReferenceBridge
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

/-! ## The Bernoulli product reference -/

def bern (t : ℝ) (_i : I n) (u : Bool) : ℝ := if u then t else 1-t

/-- The published corner reference is exactly `bern 0`, so every corner theorem
in the corpus is the `t = 0` instance of the general statement. -/
theorem bern_zero : (bern 0 : I n → Bool → ℝ)=corner := by
  funext i u
  cases u <;> simp [bern, corner]

theorem bern_nonnegative (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (c : I n → Bool) :
    0 ≤ jointWeight (bern t) c := by
  unfold jointWeight
  apply Finset.prod_nonneg
  intro i _
  cases hc : c i <;> simp [bern, hc] <;> linarith

/-! ## The factorisation that replaces `corner_response` -/

/-- A product expectation of a per-coordinate product factors coordinatewise.
At `t = 0` this degenerates to `corner_response`; for `t > 0` it is the only
route, since the expectation is then supported on the whole cube. -/
theorem expectation_factor (q h : I n → Bool → ℝ) :
    productExpectation q (fun c => ∏ i : I n, h i (c i))
      = ∏ i : I n, (q i true*h i true+q i false*h i false) := by
  classical
  have key := Finset.sum_prod_piFinset (ι := I n) (Finset.univ : Finset Bool)
    (fun (i : I n) (u : Bool) => q i u*h i u)
  rw [Fintype.piFinset_univ] at key
  calc productExpectation q (fun c => ∏ i : I n, h i (c i))
      = ∑ c : I n → Bool, ∏ i : I n, (q i (c i)*h i (c i)) := by
        unfold productExpectation jointWeight
        exact Finset.sum_congr rfl (fun c _ => (Finset.prod_mul_distrib).symm)
    _ = ∏ i : I n, ∑ u : Bool, q i u*h i u := key
    _ = ∏ i : I n, (q i true*h i true+q i false*h i false) :=
        Finset.prod_congr rfl (fun i _ => Fintype.sum_bool _)

theorem bern_col (t : ℝ) (i : I n) : bern t i true+bern t i false=1 := by
  unfold bern
  simp <;> ring

theorem bern_normalized (t : ℝ) :
    ∑ c : I n → Bool, jointWeight (bern t) c = 1 := by
  classical
  have key := Finset.sum_prod_piFinset (ι := I n) (Finset.univ : Finset Bool)
    (fun (i : I n) (u : Bool) => bern t i u)
  rw [Fintype.piFinset_univ] at key
  have hj : ∀ c : I n → Bool, jointWeight (bern t) c=∏ i : I n, bern t i (c i) :=
    fun c => rfl
  simp_rw [hj]
  rw [key]
  refine Finset.prod_eq_one (fun i _ => ?_)
  rw [Fintype.sum_bool]
  exact bern_col t i

/-! ## The gate as a polynomial in the bits -/

/-- `1` exactly when every coordinate of `B` is off. -/
def offProd (B : Finset (I n)) (x : I n → Bool) : ℝ := ∏ i ∈ B, (1-bit (x i))

/-- `1` exactly when at most one coordinate of `B` is on. -/
def leOne (B : Finset (I n)) (x : I n → Bool) : ℝ :=
  if count B x ≤ 1 then 1 else 0

theorem offProd_eq_one_iff (B : Finset (I n)) (x : I n → Bool) :
    offProd B x=(if count B x = 0 then 1 else 0) := by
  classical
  unfold offProd count
  by_cases hz : ∀ i ∈ B, x i = false
  · have h1 : ∏ i ∈ B, (1-bit (x i))=1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [hz i hi, bit]
    have h2 : (B.filter (fun i => x i = true))=(∅ : Finset (I n)) := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi
      simp [hz i hi]
    rw [h1, h2]
    simp
  · push_neg at hz
    obtain ⟨i, hiB, hi⟩ := hz
    have hit : x i = true := by cases hx : x i <;> simp [hx] at hi ⊢
    have h1 : ∏ l ∈ B, (1-bit (x l))=0 :=
      Finset.prod_eq_zero hiB (by simp [hit, bit])
    have h2 : (B.filter (fun l => x l = true)).card ≠ 0 := by
      have : i ∈ B.filter (fun l => x l = true) := mem_filter.mpr ⟨hiB, hit⟩
      exact Finset.card_ne_zero_of_mem this
    rw [h1]
    simp [h2]

/-- The two-level `if` of `gate` is this polynomial. Everything downstream uses
this form, because only a polynomial in the bits has a factorable expectation. -/
theorem gate_eq (A : Finset (I n)) (j : I n) (x : I n → Bool) :
    gate A j x=(1-bit (x j))*(1-offProd A x*leOne (others A j) x) := by
  classical
  by_cases hj : x j = true
  · simp [gate, hj, bit]
  · have hjf : x j = false := by cases hx : x j <;> simp_all
    have hbj : bit (x j)=0 := by simp [bit, hjf]
    by_cases hA : ∃ i ∈ A, x i = true
    · obtain ⟨i, hiA, hi⟩ := hA
      have h0 : offProd A x=0 := by
        unfold offProd
        exact Finset.prod_eq_zero hiA (by simp [hi, bit])
      have hdis : (∃ l ∈ A, x l = true) ∨ 2 ≤ count (others A j) x := Or.inl ⟨i, hiA, hi⟩
      rw [hbj, h0]
      simp [gate, hjf, hdis]
    · have h1 : offProd A x=1 := by
        unfold offProd
        apply Finset.prod_eq_one
        intro i hiA
        cases hxi : x i with
        | true => exact absurd ⟨i, hiA, hxi⟩ hA
        | false => simp [hxi, bit]
      rw [hbj, h1]
      by_cases hB : 2 ≤ count (others A j) x
      · have hl : leOne (others A j) x=0 := by unfold leOne; rw [if_neg (by omega)]
        rw [hl]
        simp [gate, hjf, hB]
      · have hl : leOne (others A j) x=1 := by unfold leOne; rw [if_pos (by omega)]
        rw [hl]
        have hnd : ¬((∃ l ∈ A, x l = true) ∨ 2 ≤ count (others A j) x) := by
          rintro (hc|hc)
          · exact hA hc
          · exact hB hc
        simp [gate, hjf, hnd]

/-! ## The indicator expansion that makes the gate's expectation factorable -/

/-- "At most one of `B` is on" is an explicit finite sum of per-coordinate
products: the all-off term plus one term per possible single on-coordinate.
Each summand factors under any product reference, which is what `expectation_factor`
then consumes. This replaces any appeal to a binomial identity taken on faith. -/
theorem leOne_expand (B : Finset (I n)) (x : I n → Bool) :
    leOne B x=offProd B x+∑ l ∈ B, bit (x l)*offProd (B.erase l) x := by
  classical
  unfold leOne
  rcases Nat.lt_or_ge (count B x) 2 with hlt|hge
  · interval_cases h : count B x
    · have hcard : (B.filter (fun l => x l = true)).card=0 := by
        simpa [count] using h
      have hall : ∀ i ∈ B, x i = false := by
        intro i hi
        cases hxi : x i with
        | false => rfl
        | true =>
            exact absurd hcard (Finset.card_ne_zero_of_mem
              (Finset.mem_filter.mpr ⟨hi, hxi⟩))
      have h1 : offProd B x=1 := by
        unfold offProd
        exact Finset.prod_eq_one (fun i hi => by simp [hall i hi, bit])
      have h2 : ∑ l ∈ B, bit (x l)*offProd (B.erase l) x=0 :=
        Finset.sum_eq_zero (fun l hl => by simp [hall l hl, bit])
      rw [h1, h2]
      simp [h]
    · have hcard : (B.filter (fun l => x l = true)).card=1 := by
        simpa [count] using h
      obtain ⟨l0, hl0⟩ := Finset.card_eq_one.mp hcard
      have hmem : l0 ∈ B.filter (fun l => x l = true) := by
        rw [hl0]; exact Finset.mem_singleton_self l0
      have hl0B : l0 ∈ B := (Finset.mem_filter.mp hmem).1
      have hl0t : x l0 = true := (Finset.mem_filter.mp hmem).2
      have hoff : ∀ i ∈ B, i ≠ l0 → x i = false := by
        intro i hi hne
        cases hxi : x i with
        | false => rfl
        | true =>
            have : i ∈ B.filter (fun l => x l = true) :=
              Finset.mem_filter.mpr ⟨hi, hxi⟩
            rw [hl0] at this
            exact absurd (Finset.mem_singleton.mp this) hne
      have h1 : offProd B x=0 := by
        unfold offProd
        exact Finset.prod_eq_zero hl0B (by simp [hl0t, bit])
      have h2 : ∑ l ∈ B, bit (x l)*offProd (B.erase l) x=1 := by
        rw [Finset.sum_eq_single l0]
        · have he : offProd (B.erase l0) x=1 := by
            unfold offProd
            refine Finset.prod_eq_one (fun i hi => ?_)
            have hiB : i ∈ B := Finset.mem_of_mem_erase hi
            have hine : i ≠ l0 := Finset.ne_of_mem_erase hi
            simp [hoff i hiB hine, bit]
          rw [he, hl0t]
          simp [bit]
        · intro l hl hlne
          simp [hoff l hl hlne, bit]
        · intro hcon
          exact absurd hl0B hcon
      rw [h1, h2]
      simp [h]
  · have hnot : ¬ count B x ≤ 1 := by omega
    have hcard : 2 ≤ (B.filter (fun l => x l = true)).card := by
      simpa [count] using hge
    have h1 : offProd B x=0 := by
      have hex : ∃ l ∈ B, x l = true := by
        by_contra hc
        push_neg at hc
        have hemp : B.filter (fun l => x l = true)=(∅ : Finset (I n)) :=
          Finset.filter_eq_empty_iff.mpr (fun i hi => by simp [hc i hi])
        rw [hemp] at hcard
        simp at hcard
      obtain ⟨l, hlB, hlt⟩ := hex
      unfold offProd
      exact Finset.prod_eq_zero hlB (by simp [hlt, bit])
    have h2 : ∑ l ∈ B, bit (x l)*offProd (B.erase l) x=0 := by
      refine Finset.sum_eq_zero (fun l hl => ?_)
      cases hlt : x l with
      | false => simp [hlt, bit]
      | true =>
          have hex : ∃ i ∈ B.erase l, x i = true := by
            by_contra hc
            push_neg at hc
            have hsub : B.filter (fun i => x i = true) ⊆ {l} := by
              intro i hi
              rcases Finset.mem_filter.mp hi with ⟨hiB, hit⟩
              by_contra hne
              have : i ∈ B.erase l :=
                Finset.mem_erase.mpr ⟨fun hh => hne (by simp [hh]), hiB⟩
              exact absurd hit (by simpa using hc i this)
            have hle := Finset.card_le_card hsub
            simp only [Finset.card_singleton] at hle
            omega
          obtain ⟨i, hi, hit⟩ := hex
          have hz : offProd (B.erase l) x=0 := by
            unfold offProd
            exact Finset.prod_eq_zero hi (by simp [hit, bit])
          rw [hz]
          ring
    rw [h1, h2]
    simp [hnot]

#print axioms bern_zero
#print axioms bern_col
#print axioms bern_nonnegative
#print axioms bern_normalized
#print axioms expectation_factor
#print axioms offProd_eq_one_iff
#print axioms gate_eq
#print axioms leOne_expand

end
end CIGAMF.P13.D6ReferenceBridge
