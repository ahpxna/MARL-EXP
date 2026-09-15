import «LeanD6ReferenceResponseJoinV1»

/-! # D04a: the CENTERED COMPENSATED world at a general Bernoulli reference.

`LeanD6SameResponseMarginLossV1.common_response` pins the whole corner response
of an actual binary world to `rho * 1_T`, independently of the hidden set `A`.
That is the engine of the whole same-response programme, and it is available
ONLY at the corner `t = 0`.

`LeanD6ReferenceResponseJoinV1` (D03) went one step towards the general
reference: it proves both response LEVELS of the gate at every coordinate under
`bern t`, and it builds a `compensator` that transports a SLOPE from one
reference to another. A slope is not enough: `common_response` is a statement
about the two VALUES, and `productCompressionLoss` subtracts values.

This module closes that gap. For any retained set `T` and any `rho` it builds

    centeredWorld A T j rho t x
      = gate A j x + linear (compensation A T j rho t) x - shift A T j rho t

and proves

    productResponse (bern t) (centeredWorld A T j rho t) i u
      = (if i ∈ T then rho else 0) * (bit u - t)          -- BOTH levels

for EVERY coordinate `i` and BOTH `u`. The right-hand side does not mention `A`
at all, so two different hidden sets produce literally the same response
function (`response_independent_of_hidden`). At `t = 0` the right-hand side is
`(if i ∈ T then rho else 0) * bit u`, which is exactly the right-hand side of
`common_response`; the corner statement is the `t = 0` instance of this one.

The mechanism is the two-line fact that a product reference forces:

    t * Q i true + (1-t) * Q i false = E[F]   (law of total expectation), and
    Q i true - Q i false = slope,

so once the world is CENTERED (`expect_centeredWorld` : `E[F] = 0`) the slope
determines both levels. Here that is obtained without a general total-expectation
lemma: `gate_centered_response` computes the centered gate level at each of the
three coordinate classes directly from D03's six level theorems, and
`expect_gate` computes the gate's expectation in closed form.

EVIDENCE. Every identity below was checked with exact `Fraction` arithmetic
against this corpus's own `gate`, `linear` and `productResponse` before being
written: `expect_gate` 1589 cells, `gate_centered_response` 17850 cells,
`centered_response` 42176 cells (N = 4,5,6; |A| from 0 to N-2; t in
{0, 1/8, 1/4, 1/3, 1/2, 2/3, 3/4, 1}; rho in {1, 5/4, 3/2, 2}); 0 failures.
Numerical agreement is NOT a proof and is recorded only as a pre-check; the
`#print axioms` block at the bottom is what licenses the word PROVED.

NOT proved here, deliberately: anything about the oscillation, the loss, or the
minimax value. Those are D04b (`LeanD6ReferenceRetainedOscillationV1`).
-/

namespace CIGAMF.P13.D6ReferenceCenteredCompensated
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge CIGAMF.P13.D6ReferenceTail
open CIGAMF.P13.D6ReferenceSlope CIGAMF.P13.D6ReferenceSlopeB
open CIGAMF.P13.D6ReferenceResponseJoin
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

/-! ## The gate's reference slope, by coordinate class -/

/-- The `others A j` class slope. In the `2k`-coordinate instance
(`|A| = k`, `|others A j| = k - 1`) this is `c * (k-2) * t` with
`c = (1-t)^(2k-2)`: the `b` of the reference phase law. -/
def slopeBval (t : ℝ) (A : Finset (I n)) (j : I n) : ℝ :=
  (((others A j).card:ℝ)-1)*t*(1-t)^(A.card+(others A j).card-1)

/-- The gate's slope at every coordinate. `gateMass` is the `A`-class value and,
in the `2k`-coordinate instance, equals `c * (1 + (k-2)*t)`: the `a` of the
reference phase law. -/
def gateSlope (t : ℝ) (A : Finset (I n)) (j : I n) (i : I n) : ℝ :=
  if i = j then gateMass t A j-1 else if i ∈ A then gateMass t A j else slopeBval t A j

theorem gateSlope_at_j (t : ℝ) (A : Finset (I n)) (j : I n) :
    gateSlope t A j j = gateMass t A j-1 := by simp [gateSlope]

theorem gateSlope_mem_A (t : ℝ) (A : Finset (I n)) (j : I n) (i : I n)
    (hij : i ≠ j) (hiA : i ∈ A) : gateSlope t A j i = gateMass t A j := by
  simp [gateSlope, hij, hiA]

theorem gateSlope_others (t : ℝ) (A : Finset (I n)) (j : I n) (i : I n)
    (hij : i ≠ j) (hiA : i ∉ A) : gateSlope t A j i = slopeBval t A j := by
  simp [gateSlope, hij, hiA]

/-! ## The compensated world -/

def target (T : Finset (I n)) (rho : ℝ) (i : I n) : ℝ := if i ∈ T then rho else 0

/-- World-dependent modular compensation: install the target slope `rho * 1_T`
by cancelling the gate's own reference slope coordinate by coordinate. -/
def compensation (A T : Finset (I n)) (j : I n) (rho t : ℝ) (i : I n) : ℝ :=
  target T rho i-gateSlope t A j i

/-- The centering constant. `expect_centeredWorld` proves it is the expectation
of `gate + linear (compensation ...)`, so subtracting it centers the world. -/
def shift (A T : Finset (I n)) (j : I n) (rho t : ℝ) : ℝ :=
  (1-t)*(1-gateMass t A j)+t*(∑ l, compensation A T j rho t l)

/-- `F_{A,t}` : the centered compensated world. -/
def centeredWorld (A T : Finset (I n)) (j : I n) (rho t : ℝ) (x : I n → Bool) : ℝ :=
  gate A j x+linear (compensation A T j rho t) x-shift A T j rho t

/-! ## Two expectations in closed form -/

/-- The gate fires with probability `gateMass` on the `x j = false` half, so its
expectation is `(1-t) * (1 - gateMass)`. Derived from `gate_eq` and the tail
computation, not assumed. -/
theorem expect_gate (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB1 : 1 ≤ (others A j).card) :
    productExpectation (bern t) (gate A j) = (1-t)*(1-gateMass t A j) := by
  classical
  have hsing : ∀ c : I n → Bool, (1-bit (c j))=offProd ({j} : Finset (I n)) c := by
    intro c; unfold offProd; simp
  have hdjA : Disjoint ({j} : Finset (I n)) A := by
    rw [Finset.disjoint_left]
    intro y hy hyA
    rw [Finset.mem_singleton] at hy
    subst hy
    exact hjA hyA
  have hjoin : ∀ c : I n → Bool, (1-bit (c j))*offProd A c=offProd (insert j A) c := by
    intro c
    rw [hsing c, offProd_union ({j} : Finset (I n)) A hdjA c]
    congr 1
  have hSB : Disjoint (insert j A) (others A j) := by
    rw [Finset.disjoint_left]
    intro y hy hyo
    rcases Finset.mem_insert.mp hy with h|h
    · subst y; exact (j_not_mem_others A j) hyo
    · exact (others_not_mem_A A j y hyo) h
  have hcard : (insert j A).card = A.card+1 := Finset.card_insert_of_notMem hjA
  have hfun : (gate A j : (I n → Bool) → ℝ)
      = fun c => (1-bit (c j))-offProd (insert j A) c*leOne (others A j) c := by
    funext x
    rw [gate_eq A j x, ← hjoin x]
    ring
  rw [hfun, expect_sub (bern t) (fun c => 1-bit (c j))
      (fun c => offProd (insert j A) c*leOne (others A j) c)]
  rw [show (fun c : I n → Bool => 1-bit (c j))
      = (offProd ({j} : Finset (I n)) : (I n → Bool) → ℝ) from funext hsing]
  rw [expect_offProd, expect_offProd_mul_leOne t (insert j A) (others A j) hSB hB1, hcard]
  unfold gateMass tailFactor
  simp only [Finset.card_singleton, pow_one, pow_succ]
  ring

/-- Every coordinate is on with probability `t`, so a modular part has
expectation `t * (sum of its coefficients)`. -/
theorem expect_linear (t : ℝ) (c' : I n → ℝ) :
    productExpectation (bern t) (linear c') = t*(∑ l, c' l) := by
  classical
  unfold linear
  rw [expect_sum (bern t) (Finset.univ : Finset (I n))
    (fun l c => c' l*bit (c l))]
  have h : ∀ l ∈ (Finset.univ : Finset (I n)),
      productExpectation (bern t) (fun c : I n → Bool => c' l*bit (c l)) = c' l*t := by
    intro l _
    rw [expect_smul (bern t) (c' l) (fun c : I n → Bool => bit (c l)), expect_bit]
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul]
  ring

theorem expect_centeredWorld (t : ℝ) (A T : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB1 : 1 ≤ (others A j).card) (rho : ℝ) :
    productExpectation (bern t) (centeredWorld A T j rho t) = 0 := by
  classical
  have hfun : (centeredWorld A T j rho t : (I n → Bool) → ℝ)
      = fun x => (gate A j x+linear (compensation A T j rho t) x)
          -(fun _ : I n → Bool => shift A T j rho t) x := by
    funext x; rfl
  rw [hfun, expect_sub (bern t) (fun x => gate A j x+linear (compensation A T j rho t) x)
      (fun _ : I n → Bool => shift A T j rho t),
    expect_add (bern t) (gate A j) (linear (compensation A T j rho t)),
    expect_const, expect_gate t A j hjA hB1, expect_linear t (compensation A T j rho t)]
  unfold shift
  ring

/-! ## The centered gate level, at every coordinate and both values -/

/-- The whole content of D04a in one line: once the gate's expectation is
subtracted, its response at every coordinate is its SLOPE times `(bit u - t)`.
Proved class by class from the six level theorems of D03. -/
theorem gate_centered_response (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB2 : 2 ≤ (others A j).card) (i : I n) (u : Bool) :
    productResponse (bern t) (gate A j) i u-(1-t)*(1-gateMass t A j)
      = gateSlope t A j i*(bit u-t) := by
  classical
  have hB1 : 1 ≤ (others A j).card := by omega
  rcases coordinate_trichotomy A j i with h|h|h
  · subst i
    rw [gateSlope_at_j]
    cases u
    · rw [response_gate_j_false t A j hjA hB1]
      simp only [bit_false]
      ring
    · rw [response_gate_j_true t A j]
      simp only [bit_true]
      ring
  · have hij : i ≠ j := by rintro rfl; exact hjA h
    rw [gateSlope_mem_A t A j i hij h]
    cases u
    · rw [response_gate_A_false t A j hjA i h hB1]
      simp only [bit_false]
      ring
    · rw [response_gate_A_true t A j hjA i h]
      simp only [bit_true]
      ring
  · have hij : i ≠ j := others_ne_j A j i h
    have hiA : i ∉ A := others_not_mem_A A j i h
    obtain ⟨m, hm⟩ : ∃ m, (others A j).card = m+2 := ⟨(others A j).card-2, by omega⟩
    have hce : ((others A j).erase i).card = m+1 := by
      rw [Finset.card_erase_of_mem h, hm]
      omega
    rw [gateSlope_others t A j i hij hiA]
    cases u
    · rw [response_gate_B_false t A j hjA i h hB2]
      unfold slopeBval gateMass tailFactor
      rw [hce, hm]
      simp only [bit_false, Nat.add_sub_cancel,
        show A.card+(m+2)-1 = A.card+m+1 by omega, pow_succ, pow_add]
      push_cast
      ring
    · rw [response_gate_B_true t A j hjA i h hB2]
      unfold slopeBval gateMass tailFactor
      rw [hm]
      simp only [bit_true, show m+2-1 = m+1 by omega,
        show A.card+(m+2)-1 = A.card+m+1 by omega, pow_succ, pow_add]
      push_cast
      ring

/-- The additive form, convenient for rewriting. -/
theorem gate_response_levels (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB2 : 2 ≤ (others A j).card) (i : I n) (u : Bool) :
    productResponse (bern t) (gate A j) i u
      = (1-t)*(1-gateMass t A j)+gateSlope t A j i*(bit u-t) := by
  have h := gate_centered_response t A j hjA hB2 i u
  linarith

/-! ## Both levels of the compensated world -/

theorem response_split (t : ℝ) (A T : Finset (I n)) (j : I n) (rho : ℝ)
    (i : I n) (u : Bool) :
    productResponse (bern t) (centeredWorld A T j rho t) i u
      = productResponse (bern t) (gate A j) i u
        +productResponse (bern t) (linear (compensation A T j rho t)) i u
        -shift A T j rho t := by
  classical
  have hconst : (∑ c : I n → Bool, jointWeight (bern t) c*shift A T j rho t)
      = shift A T j rho t := by
    rw [← Finset.sum_mul, bern_normalized, one_mul]
  have key : ∀ c : I n → Bool,
      jointWeight (bern t) c*centeredWorld A T j rho t (Function.update c i u)
        = jointWeight (bern t) c*gate A j (Function.update c i u)
          +jointWeight (bern t) c*linear (compensation A T j rho t) (Function.update c i u)
          -jointWeight (bern t) c*shift A T j rho t := by
    intro c
    unfold centeredWorld
    ring
  unfold productResponse productExpectation
  rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hconst]

/-- **D04a.** Both response levels of the actual centered compensated world, at
every coordinate. The right-hand side does not mention the hidden set `A`. -/
theorem centered_response (t : ℝ) (A T : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB2 : 2 ≤ (others A j).card) (rho : ℝ) (i : I n) (u : Bool) :
    productResponse (bern t) (centeredWorld A T j rho t) i u
      = target T rho i*(bit u-t) := by
  rw [response_split t A T j rho i u, gate_response_levels t A j hjA hB2 i u,
    response_linear t (compensation A T j rho t) i u]
  have hci : compensation A T j rho t i = target T rho i-gateSlope t A j i := rfl
  unfold shift
  rw [hci]
  ring

/-- The same response function for two different hidden sets: the learner
cannot separate `A` from `A'` by any coordinate query at this reference. -/
theorem response_independent_of_hidden (t : ℝ) (A A' T : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hjA' : j ∉ A') (hB2 : 2 ≤ (others A j).card)
    (hB2' : 2 ≤ (others A' j).card) (rho : ℝ) (i : I n) (u : Bool) :
    productResponse (bern t) (centeredWorld A T j rho t) i u
      = productResponse (bern t) (centeredWorld A' T j rho t) i u := by
  rw [centered_response t A T j hjA hB2 rho i u,
    centered_response t A' T j hjA' hB2' rho i u]

/-- The installed slope is exactly the target. -/
theorem centered_slope (t : ℝ) (A T : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB2 : 2 ≤ (others A j).card) (rho : ℝ) (i : I n) :
    productResponse (bern t) (centeredWorld A T j rho t) i true
      -productResponse (bern t) (centeredWorld A T j rho t) i false
      = target T rho i := by
  rw [centered_response t A T j hjA hB2 rho i true,
    centered_response t A T j hjA hB2 rho i false]
  simp only [bit_true, bit_false]
  ring

/-- At `t = 0` this is literally the right-hand side of
`D6SameResponseMarginLoss.common_response`: the published corner statement is
the `t = 0` instance of `centered_response`. -/
theorem corner_specialisation (A T : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB2 : 2 ≤ (others A j).card) (rho : ℝ) (i : I n) (u : Bool) :
    productResponse corner (centeredWorld A T j rho 0) i u
      = (if i ∈ T then rho else 0)*bit u := by
  rw [← bern_zero, centered_response 0 A T j hjA hB2 rho i u]
  unfold target
  ring

/-- The compensation is modular and the centering is a constant, so every mixed
difference of the compensated world is a mixed difference of the bare gate. The
interaction content is untouched by the construction. -/
theorem mixed_unchanged (t : ℝ) (A T : Finset (I n)) (j : I n) (rho : ℝ) (i : I n)
    (x c : I n → Bool) :
    mixedDifference (centeredWorld A T j rho t) i x c = mixedDifference (gate A j) i x c := by
  have hx := linear_difference (compensation A T j rho t) x i (x i) (c i)
  have hc := linear_difference (compensation A T j rho t) c i (x i) (c i)
  rw [Function.update_eq_self] at hx
  rw [Function.update_eq_self] at hc
  unfold mixedDifference centeredWorld
  linarith

#print axioms gateSlope_at_j
#print axioms gateSlope_mem_A
#print axioms gateSlope_others
#print axioms expect_gate
#print axioms expect_linear
#print axioms expect_centeredWorld
#print axioms gate_centered_response
#print axioms gate_response_levels
#print axioms response_split
#print axioms centered_response
#print axioms response_independent_of_hidden
#print axioms centered_slope
#print axioms corner_specialisation
#print axioms mixed_unchanged

end
end CIGAMF.P13.D6ReferenceCenteredCompensated
