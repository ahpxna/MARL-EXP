import «LeanD6BernoulliReferenceBridgeV1»

/-! # The binomial tail under a Bernoulli product reference.

This is the one genuine computation named as missing in
`LeanD6BernoulliReferenceBridgeV1`: the expectation of the "at most one of `B`
is on" indicator, and the mixed shape `offProd S * leOne B` on disjoint blocks
that all three slope identities consume.

The route avoids any binomial identity taken on faith. `leOne_expand` already
writes the indicator as an explicit finite sum of per-coordinate products;
`sing_eq` collapses each singleton term to a DIFFERENCE of two `offProd`s, so
the whole tail is built from `expect_offProd` alone, which is one application of
`expectation_factor`. No induction on `B`, no powerset sum, no `Nat.choose`.

`expect_offProd_mul_leOne` is the shape the three slopes need, because in the
gate the blocks `{z}`, `A` and `others A z` are pairwise disjoint.
-/

namespace CIGAMF.P13.D6ReferenceTail
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

/-! ## Linearity of the product expectation -/

theorem expect_add (q : I n → Bool → ℝ) (f g : (I n → Bool) → ℝ) :
    productExpectation q (fun c => f c+g c)
      = productExpectation q f+productExpectation q g := by
  unfold productExpectation
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => by ring)

theorem expect_sub (q : I n → Bool → ℝ) (f g : (I n → Bool) → ℝ) :
    productExpectation q (fun c => f c-g c)
      = productExpectation q f-productExpectation q g := by
  unfold productExpectation
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun c _ => by ring)

theorem expect_sum (q : I n → Bool → ℝ) (s : Finset (I n))
    (F : I n → (I n → Bool) → ℝ) :
    productExpectation q (fun c => ∑ l ∈ s, F l c)
      = ∑ l ∈ s, productExpectation q (F l) := by
  unfold productExpectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ## `offProd` as a per-coordinate product, and its expectation -/

def hOff (B : Finset (I n)) (i : I n) (u : Bool) : ℝ := if i ∈ B then 1-bit u else 1

theorem offProd_as_prod (B : Finset (I n)) (x : I n → Bool) :
    offProd B x=∏ i : I n, hOff B i (x i) := by
  classical
  unfold offProd hOff
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- One application of `expectation_factor`. Every later expectation in this
file reduces to this single identity. -/
theorem expect_offProd (t : ℝ) (B : Finset (I n)) :
    productExpectation (bern t) (offProd B)=(1-t)^B.card := by
  classical
  have hfun : (offProd B : (I n → Bool) → ℝ)=fun c => ∏ i : I n, hOff B i (c i) := by
    funext x; exact offProd_as_prod B x
  rw [hfun, expectation_factor]
  have hfac : ∀ i : I n,
      (bern t i true*hOff B i true+bern t i false*hOff B i false)
        = if i ∈ B then 1-t else 1 := by
    intro i
    by_cases hi : i ∈ B <;> simp [bern, hOff, hi, bit] <;> ring
  simp_rw [hfac]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem offProd_union (S B : Finset (I n)) (hd : Disjoint S B) (x : I n → Bool) :
    offProd S x*offProd B x=offProd (S ∪ B) x := by
  classical
  unfold offProd
  rw [Finset.prod_union hd]

/-- The singleton term of `leOne_expand` is a difference of two `offProd`s.
This is what removes the need for any binomial coefficient. -/
theorem sing_eq (B : Finset (I n)) (l : I n) (hl : l ∈ B) (x : I n → Bool) :
    bit (x l)*offProd (B.erase l) x=offProd (B.erase l) x-offProd B x := by
  classical
  have h : offProd B x=(1-bit (x l))*offProd (B.erase l) x := by
    unfold offProd
    rw [← Finset.mul_prod_erase B (fun i => 1-bit (x i)) hl]
  rw [h]; ring

/-! ## The tail -/

theorem leOne_as_diff (B : Finset (I n)) (x : I n → Bool) :
    leOne B x=offProd B x+∑ l ∈ B, (offProd (B.erase l) x-offProd B x) := by
  rw [leOne_expand B x]
  congr 1
  exact Finset.sum_congr rfl (fun l hl => sing_eq B l hl x)

theorem expect_leOne (t : ℝ) (B : Finset (I n)) :
    productExpectation (bern t) (leOne B)
      = (1-t)^B.card+(B.card:ℝ)*((1-t)^(B.card-1)-(1-t)^B.card) := by
  classical
  have hfun : (leOne B : (I n → Bool) → ℝ)
      = fun c => offProd B c+∑ l ∈ B, (offProd (B.erase l) c-offProd B c) := by
    funext x; exact leOne_as_diff B x
  rw [hfun, expect_add (bern t) (offProd B)
    (fun c => ∑ l ∈ B, (offProd (B.erase l) c-offProd B c))]
  rw [expect_sum (bern t) B (fun l c => offProd (B.erase l) c-offProd B c)]
  have hterm : ∀ l ∈ B,
      productExpectation (bern t) (fun c => offProd (B.erase l) c-offProd B c)
        = (1-t)^(B.card-1)-(1-t)^B.card := by
    intro l hl
    rw [expect_sub (bern t) (offProd (B.erase l)) (offProd B),
      expect_offProd, expect_offProd, Finset.card_erase_of_mem hl]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, expect_offProd, nsmul_eq_mul]

/-- The standard binomial-tail form. -/
theorem expect_leOne_binomial (t : ℝ) (B : Finset (I n)) (hB : 1 ≤ B.card) :
    productExpectation (bern t) (leOne B)
      = (1-t)^B.card+(B.card:ℝ)*t*(1-t)^(B.card-1) := by
  rw [expect_leOne]
  obtain ⟨m, hm⟩ : ∃ m, B.card=m+1 := ⟨B.card-1, by omega⟩
  rw [hm]
  simp only [Nat.add_sub_cancel, pow_succ]
  push_cast
  ring

/-! ## The shape the three slopes consume -/

/-- On disjoint blocks the off-mass of `S` and the tail of `B` multiply.
In the gate, `S` is `{z}` together with a subset of `A`, and `B` is `others A z`;
these are disjoint by construction, which is exactly why the three slopes are
products of elementary factors. -/
theorem expect_offProd_mul_leOne (t : ℝ) (S B : Finset (I n))
    (hd : Disjoint S B) (hB : 1 ≤ B.card) :
    productExpectation (bern t) (fun c => offProd S c*leOne B c)
      = (1-t)^S.card*((1-t)^B.card+(B.card:ℝ)*t*(1-t)^(B.card-1)) := by
  classical
  have hcard : (S ∪ B).card=S.card+B.card :=
    Finset.card_union_of_disjoint hd
  have hfun : (fun c => offProd S c*leOne B c)
      = fun c => offProd (S ∪ B) c
          +∑ l ∈ B, (offProd (S ∪ B.erase l) c-offProd (S ∪ B) c) := by
    funext x
    rw [leOne_as_diff B x, mul_add, Finset.mul_sum]
    congr 1
    · exact offProd_union S B hd x
    · refine Finset.sum_congr rfl (fun l hl => ?_)
      have hdl : Disjoint S (B.erase l) :=
        Finset.disjoint_of_subset_right (Finset.erase_subset l B) hd
      rw [mul_sub, offProd_union S (B.erase l) hdl x, offProd_union S B hd x]
  rw [hfun, expect_add (bern t) (offProd (S ∪ B))
    (fun c => ∑ l ∈ B, (offProd (S ∪ B.erase l) c-offProd (S ∪ B) c))]
  rw [expect_sum (bern t) B (fun l c => offProd (S ∪ B.erase l) c-offProd (S ∪ B) c)]
  have hterm : ∀ l ∈ B,
      productExpectation (bern t)
          (fun c => offProd (S ∪ B.erase l) c-offProd (S ∪ B) c)
        = (1-t)^(S.card+B.card-1)-(1-t)^(S.card+B.card) := by
    intro l hl
    have hdl : Disjoint S (B.erase l) :=
      Finset.disjoint_of_subset_right (Finset.erase_subset l B) hd
    have hc : (S ∪ B.erase l).card=S.card+B.card-1 := by
      rw [Finset.card_union_of_disjoint hdl, Finset.card_erase_of_mem hl]
      omega
    rw [expect_sub (bern t) (offProd (S ∪ B.erase l)) (offProd (S ∪ B)),
      expect_offProd, expect_offProd, hc, hcard]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, expect_offProd, hcard, nsmul_eq_mul]
  obtain ⟨m, hm⟩ : ∃ m, B.card=m+1 := ⟨B.card-1, by omega⟩
  rw [hm]
  simp only [show S.card+(m+1)-1=S.card+m by omega, pow_succ, pow_add]
  push_cast
  ring

#print axioms expect_add
#print axioms expect_sub
#print axioms expect_sum
#print axioms offProd_as_prod
#print axioms expect_offProd
#print axioms offProd_union
#print axioms sing_eq
#print axioms leOne_as_diff
#print axioms expect_leOne
#print axioms expect_leOne_binomial
#print axioms expect_offProd_mul_leOne

end
end CIGAMF.P13.D6ReferenceTail
