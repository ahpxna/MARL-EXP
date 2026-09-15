import «LeanD6BernoulliSlopeBV1»

/-! # D03: both response LEVELS of the actual world, at every coordinate,
at a general Bernoulli product reference.

`LeanD6BernoulliSlopeV1` and `LeanD6BernoulliSlopeBV1` prove the three SLOPES
(the differences `response i true - response i false`). A slope is not enough
for the D6 objects: `productCompressionLoss` is built from `osc` of the response
and `retainedResidual` subtracts the response VALUE, not the difference. This
module supplies the missing halves — each level separately, for each of the
three coordinate classes — and then checks that the levels reproduce the three
already-proved slopes.

The index set splits into exactly three classes when `j ∉ A`
(`coordinate_trichotomy`): the distinguished coordinate `j`, the hidden set `A`,
and the block `others A j`. Nothing else can occur, so the six level theorems
below are a complete response table for every hidden `A`.

## What is proved

    i = j      response true  = (mu-1)*1 + t*(Sc-(mu-1)) + 0
               response false = (mu-1)*0 + t*(Sc-(mu-1)) + (1 - gateMass)
    i ∈ A      response true  = t*Sc + (1-t)
               response false = t*Sc + ((1-t) - gateMass)
    i ∈ B      response true  = (1-mu) + t*(Sc-(1-mu)) + ((1-t) - (1-t)^(|A|+|B|))
               response false = (1-mu)*0 + t*(Sc-(1-mu))
                                  + ((1-t) - (1-t)^(|A|+1) * tailFactor (B.erase i))

with `Sc = ∑ coeff = (mu-1) + (1-mu)*|B|` and
`gateMass t A j = (1-t)^|A| * ((1-t)^|B| + |B|*t*(1-t)^(|B|-1))`.

## What is NOT proved here

This is the response table only. It is NOT the general-reference minimax
bridge (D04/D05): the reduction of the actual residual oscillation and the
optimal retained set to the count-based game, symmetry averaging/WLOG, and the
primal/dual certificate for the whole class all remain open. It is also not a
phase diagram — the domain conditions of D06 are not touched here.

## Modular compensation

`compensated_slope_eq` is the exact sense in which the reference dependence is
modular: a linear (additive-separable) part contributes its own coefficient as
its slope at EVERY product reference (`linear_slope`, no `t` in it), so the
entire reference dependence of `world` sits in the gate and can be cancelled
coordinatewise by a modular correction. This is the algebraic content behind
"compensated `F_t` keeping the same `Q`"; it is not a claim that the compensated
world is in the same model class.
-/

namespace CIGAMF.P13.D6ReferenceResponseJoin
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge CIGAMF.P13.D6ReferenceTail
open CIGAMF.P13.D6ReferenceSlope CIGAMF.P13.D6ReferenceSlopeB
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

/-! ## Abbreviations for the two closed-form factors -/

/-- `E[leOne B]` under `bern t`: the binomial tail of the block. -/
def tailFactor (t : ℝ) (B : Finset (I n)) : ℝ :=
  (1-t)^B.card+(B.card:ℝ)*t*(1-t)^(B.card-1)

/-- The probability that the gate would fire: all of `A` off and at most one of
`others A j` on. -/
def gateMass (t : ℝ) (A : Finset (I n)) (j : I n) : ℝ :=
  (1-t)^A.card*tailFactor t (others A j)

/-! ## Elementary expectations -/

theorem expect_const (t : ℝ) (a : ℝ) :
    productExpectation (bern t) (fun _ : I n → Bool => a) = a := by
  unfold productExpectation
  rw [← Finset.sum_mul, bern_normalized, one_mul]

theorem expect_smul (q : I n → Bool → ℝ) (a : ℝ) (f : (I n → Bool) → ℝ) :
    productExpectation q (fun c => a*f c) = a*productExpectation q f := by
  unfold productExpectation
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => by ring)

/-- Each coordinate is on with probability `t`. Derived from `expect_offProd`
at a singleton block, not assumed. -/
theorem expect_bit (t : ℝ) (l : I n) :
    productExpectation (bern t) (fun c : I n → Bool => bit (c l)) = t := by
  classical
  have hsing : (fun c : I n → Bool => bit (c l))
      = fun c : I n → Bool => (1:ℝ)-offProd {l} c := by
    funext c
    unfold offProd
    simp
  rw [hsing, expect_sub (bern t) (fun _ : I n → Bool => (1:ℝ)) (offProd ({l} : Finset (I n))),
    expect_const, expect_offProd]
  simp

/-! ## The three coordinate classes are exhaustive and disjoint -/

theorem coordinate_trichotomy (A : Finset (I n)) (j : I n) (i : I n) :
    i = j ∨ i ∈ A ∨ i ∈ others A j := by
  classical
  by_cases hij : i = j
  · exact Or.inl hij
  · by_cases hiA : i ∈ A
    · exact Or.inr (Or.inl hiA)
    · exact Or.inr (Or.inr (by simp [others, hij, hiA]))

theorem others_not_mem_A (A : Finset (I n)) (j : I n) (i : I n)
    (hi : i ∈ others A j) : i ∉ A :=
  (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hi)).2

theorem others_ne_j (A : Finset (I n)) (j : I n) (i : I n)
    (hi : i ∈ others A j) : i ≠ j :=
  Finset.ne_of_mem_erase hi

theorem j_not_mem_others (A : Finset (I n)) (j : I n) : j ∉ others A j := by
  simp [others]

theorem disjoint_A_others (A : Finset (I n)) (j : I n) :
    Disjoint A (others A j) := by
  rw [Finset.disjoint_left]
  intro a haA haO
  exact (others_not_mem_A A j a haO) haA

/-! ## The modular part, at both levels -/

theorem response_linear_erase (t : ℝ) (c' : I n → ℝ) (i : I n) (u : Bool) :
    productResponse (bern t) (linear c') i u
      = c' i*bit u+t*∑ l ∈ Finset.univ.erase i, c' l := by
  classical
  unfold productResponse
  have hsplit : ∀ c : I n → Bool,
      linear c' (Function.update c i u)
        = c' i*bit u+∑ l ∈ Finset.univ.erase i, c' l*bit (c l) := by
    intro c
    unfold linear
    rw [← Finset.add_sum_erase Finset.univ
      (fun l => c' l*bit (Function.update c i u l)) (Finset.mem_univ i)]
    congr 1
    · simp
    · refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  simp_rw [hsplit]
  rw [expect_add (bern t) (fun _ : I n → Bool => c' i*bit u)
      (fun c => ∑ l ∈ Finset.univ.erase i, c' l*bit (c l)),
    expect_const,
    expect_sum (bern t) (Finset.univ.erase i) (fun l c => c' l*bit (c l))]
  have hterm : ∀ l ∈ Finset.univ.erase i,
      productExpectation (bern t) (fun c : I n → Bool => c' l*bit (c l)) = c' l*t := by
    intro l _
    rw [expect_smul (bern t) (c' l) (fun c : I n → Bool => bit (c l)), expect_bit]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  ring

theorem response_linear (t : ℝ) (c' : I n → ℝ) (i : I n) (u : Bool) :
    productResponse (bern t) (linear c') i u
      = c' i*bit u+t*((∑ l, c' l)-c' i) := by
  classical
  rw [response_linear_erase t c' i u,
    Finset.sum_erase_eq_sub (Finset.mem_univ i)]

/-- The modular coefficients of the threshold world sum to `(mu-1)+(1-mu)*|B|`. -/
theorem coeff_sum (A : Finset (I n)) (j : I n) (mu : ℝ) (hjA : j ∉ A) :
    (∑ l, coeff A j mu l) = (mu-1)+(1-mu)*((others A j).card:ℝ) := by
  classical
  have hjU : j ∈ (Finset.univ : Finset (I n)) \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjA⟩
  have hA0 : ∑ l ∈ A, coeff A j mu l = 0 :=
    Finset.sum_eq_zero (fun l hl => by simp [coeff, hl])
  have hsplit :
      (∑ l ∈ (Finset.univ : Finset (I n)) \ A, coeff A j mu l)+∑ l ∈ A, coeff A j mu l
        = ∑ l, coeff A j mu l :=
    Finset.sum_sdiff (Finset.subset_univ A)
  have houter :
      ∑ l ∈ (Finset.univ : Finset (I n)) \ A, coeff A j mu l
        = coeff A j mu j+∑ l ∈ others A j, coeff A j mu l := by
    rw [← Finset.add_sum_erase ((Finset.univ : Finset (I n)) \ A) (coeff A j mu) hjU]
    rfl
  have hj : coeff A j mu j = mu-1 := by simp [coeff, hjA]
  have hB : ∑ l ∈ others A j, coeff A j mu l = (1-mu)*((others A j).card:ℝ) := by
    calc
      (∑ l ∈ others A j, coeff A j mu l) = ∑ _l ∈ others A j, (1-mu) :=
        Finset.sum_congr rfl (fun l hl => by
          simp [coeff, others_not_mem_A A j l hl, others_ne_j A j l hl])
      _ = (1-mu)*((others A j).card:ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  rw [← hsplit, houter, hA0, hj, hB]
  ring

/-! ## The gate, at both levels, on each of the three classes -/

theorem response_gate_j_true (t : ℝ) (A : Finset (I n)) (j : I n) :
    productResponse (bern t) (gate A j) j true = 0 := by
  classical
  rw [gate_response]
  rw [show (fun c : I n → Bool =>
      (1-bit (Function.update c j true j))
        *(1-offProd A (Function.update c j true)*leOne (others A j) (Function.update c j true)))
      = (fun _ : I n → Bool => (0:ℝ)) from funext (fun c => by simp [bit])]
  unfold productExpectation
  simp

theorem response_gate_j_false (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) j false = 1-gateMass t A j := by
  classical
  rw [gate_response]
  rw [show (fun c : I n → Bool =>
      (1-bit (Function.update c j false j))
        *(1-offProd A (Function.update c j false)*leOne (others A j) (Function.update c j false)))
      = (fun c : I n → Bool => 1-offProd A c*leOne (others A j) c) from
      funext (fun c => by
        rw [offProd_update_not_mem A j hjA false c,
          leOne_update_not_mem (others A j) j (j_not_mem_others A j) false c]
        simp [bit])]
  rw [expect_sub (bern t) (fun _ : I n → Bool => (1:ℝ))
      (fun c => offProd A c*leOne (others A j) c),
    expect_const,
    expect_offProd_mul_leOne t A (others A j) (disjoint_A_others A j) hB]
  rfl

theorem response_gate_A_true (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (i : I n) (hiA : i ∈ A) :
    productResponse (bern t) (gate A j) i true = 1-t := by
  classical
  have hij : i ≠ j := by rintro rfl; exact hjA hiA
  have hiB : i ∉ others A j := fun hc => (others_not_mem_A A j i hc) hiA
  rw [gate_response]
  rw [show (fun c : I n → Bool =>
      (1-bit (Function.update c i true j))
        *(1-offProd A (Function.update c i true)*leOne (others A j) (Function.update c i true)))
      = (offProd ({j} : Finset (I n)) : (I n → Bool) → ℝ) from
      funext (fun c => by
        rw [Function.update_of_ne (Ne.symm hij), offProd_update_mem A i hiA true c,
          leOne_update_not_mem (others A j) i hiB true c]
        unfold offProd
        simp [bit])]
  rw [expect_offProd]
  simp

theorem response_gate_A_false (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (i : I n) (hiA : i ∈ A) (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) i false = (1-t)-gateMass t A j := by
  classical
  have hij : i ≠ j := by rintro rfl; exact hjA hiA
  have hiB : i ∉ others A j := fun hc => (others_not_mem_A A j i hc) hiA
  have hsing : ∀ c : I n → Bool, (1-bit (c j))=offProd ({j} : Finset (I n)) c := by
    intro c; unfold offProd; simp
  have hdj : Disjoint ({j} : Finset (I n)) (A.erase i) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    subst ha
    exact hjA (Finset.mem_of_mem_erase hb)
  have hprod : ∀ c : I n → Bool,
      (1-bit (c j))*offProd (A.erase i) c=offProd (insert j (A.erase i)) c := by
    intro c
    rw [hsing c, offProd_union ({j} : Finset (I n)) (A.erase i) hdj c]
    congr 1
  have hcard : (insert j (A.erase i)).card=A.card := by
    rw [Finset.card_insert_of_notMem (fun hc => hjA (Finset.mem_of_mem_erase hc)),
      Finset.card_erase_of_mem hiA]
    have h1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨i, hiA⟩
    omega
  have hdisj : Disjoint (insert j (A.erase i)) (others A j) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rcases Finset.mem_insert.mp ha with h|h
    · exact (others_ne_j A j a hb) h
    · exact (others_not_mem_A A j a hb) (Finset.mem_of_mem_erase h)
  rw [gate_response]
  rw [show (fun c : I n → Bool =>
      (1-bit (Function.update c i false j))
        *(1-offProd A (Function.update c i false)*leOne (others A j) (Function.update c i false)))
      = (fun c : I n → Bool =>
          offProd ({j} : Finset (I n)) c
            -(1-bit (c j))*offProd (A.erase i) c*leOne (others A j) c) from
      funext (fun c => by
        rw [Function.update_of_ne (Ne.symm hij), offProd_update_mem A i hiA false c,
          leOne_update_not_mem (others A j) i hiB false c, ← hsing c]
        simp [bit]
        ring)]
  rw [expect_sub (bern t) (offProd ({j} : Finset (I n)))
      (fun c => (1-bit (c j))*offProd (A.erase i) c*leOne (others A j) c)]
  simp_rw [hprod]
  rw [expect_offProd, expect_offProd_mul_leOne t (insert j (A.erase i)) (others A j) hdisj hB,
    hcard]
  simp [gateMass, tailFactor]

theorem response_gate_B_true (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (i : I n) (hiB : i ∈ others A j) (hB2 : 2 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) i true
      = (1-t)-(1-t)^(A.card+(others A j).card) := by
  classical
  set B := others A j with hBdef
  have hij : i ≠ j := others_ne_j A j i hiB
  have hiA : i ∉ A := others_not_mem_A A j i hiB
  have hjB : j ∉ B := by rw [hBdef]; exact j_not_mem_others A j
  have hsing : ∀ c : I n → Bool, (1-bit (c j))=offProd ({j} : Finset (I n)) c := by
    intro c; unfold offProd; simp
  have hdjA : Disjoint ({j} : Finset (I n)) A := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    subst ha
    exact hjA hb
  have hjoin : ∀ c : I n → Bool,
      (1-bit (c j))*offProd A c=offProd (insert j A) c := by
    intro c
    rw [hsing c, offProd_union ({j} : Finset (I n)) A hdjA c]
    congr 1
  have hSB : Disjoint (insert j A) (B.erase i) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have haB : a ∈ B := Finset.mem_of_mem_erase hb
    rcases Finset.mem_insert.mp ha with h|h
    · subst h; exact hjB haB
    · rw [hBdef] at haB; exact (others_not_mem_A A j a haB) h
  have hcardS : (insert j A).card=A.card+1 := Finset.card_insert_of_notMem hjA
  have hcardE : (B.erase i).card=B.card-1 := Finset.card_erase_of_mem hiB
  rw [gate_response, ← hBdef]
  rw [show (fun c : I n → Bool =>
      (1-bit (Function.update c i true j))
        *(1-offProd A (Function.update c i true)*leOne B (Function.update c i true)))
      = (fun c : I n → Bool =>
          offProd ({j} : Finset (I n)) c
            -(1-bit (c j))*offProd A c*offProd (B.erase i) c) from
      funext (fun c => by
        rw [Function.update_of_ne (Ne.symm hij), offProd_update_not_mem A i hiA true c,
          leOne_update_true_mem B i hiB c, ← hsing c]
        ring)]
  rw [expect_sub (bern t) (offProd ({j} : Finset (I n)))
      (fun c => (1-bit (c j))*offProd A c*offProd (B.erase i) c)]
  simp_rw [hjoin]
  rw [show (fun c : I n → Bool => offProd (insert j A) c*offProd (B.erase i) c)
      = (offProd ((insert j A) ∪ (B.erase i)) : (I n → Bool) → ℝ) from
      funext (fun c => offProd_union (insert j A) (B.erase i) hSB c)]
  rw [expect_offProd, expect_offProd, Finset.card_union_of_disjoint hSB, hcardS, hcardE]
  have hcard : A.card+1+(B.card-1)=A.card+B.card := by omega
  rw [hcard]
  simp

theorem response_gate_B_false (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (i : I n) (hiB : i ∈ others A j) (hB2 : 2 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) i false
      = (1-t)-(1-t)^(A.card+1)*tailFactor t ((others A j).erase i) := by
  classical
  set B := others A j with hBdef
  have hij : i ≠ j := others_ne_j A j i hiB
  have hiA : i ∉ A := others_not_mem_A A j i hiB
  have hjB : j ∉ B := by rw [hBdef]; exact j_not_mem_others A j
  have hsing : ∀ c : I n → Bool, (1-bit (c j))=offProd ({j} : Finset (I n)) c := by
    intro c; unfold offProd; simp
  have hdjA : Disjoint ({j} : Finset (I n)) A := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    subst ha
    exact hjA hb
  have hjoin : ∀ c : I n → Bool,
      (1-bit (c j))*offProd A c=offProd (insert j A) c := by
    intro c
    rw [hsing c, offProd_union ({j} : Finset (I n)) A hdjA c]
    congr 1
  have hSB : Disjoint (insert j A) (B.erase i) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have haB : a ∈ B := Finset.mem_of_mem_erase hb
    rcases Finset.mem_insert.mp ha with h|h
    · subst h; exact hjB haB
    · rw [hBdef] at haB; exact (others_not_mem_A A j a haB) h
  have hcardS : (insert j A).card=A.card+1 := Finset.card_insert_of_notMem hjA
  have hcardE : (B.erase i).card=B.card-1 := Finset.card_erase_of_mem hiB
  have hB1 : 1 ≤ (B.erase i).card := by rw [hcardE]; omega
  rw [gate_response, ← hBdef]
  rw [show (fun c : I n → Bool =>
      (1-bit (Function.update c i false j))
        *(1-offProd A (Function.update c i false)*leOne B (Function.update c i false)))
      = (fun c : I n → Bool =>
          offProd ({j} : Finset (I n)) c
            -(1-bit (c j))*offProd A c*leOne (B.erase i) c) from
      funext (fun c => by
        rw [Function.update_of_ne (Ne.symm hij), offProd_update_not_mem A i hiA false c,
          leOne_update_false_mem B i hiB c, ← hsing c]
        ring)]
  rw [expect_sub (bern t) (offProd ({j} : Finset (I n)))
      (fun c => (1-bit (c j))*offProd A c*leOne (B.erase i) c)]
  simp_rw [hjoin]
  rw [expect_offProd,
    expect_offProd_mul_leOne t (insert j A) (B.erase i) hSB hB1, hcardS]
  simp [tailFactor]

/-! ## The world: both levels, all three classes -/

theorem world_eq_add (A : Finset (I n)) (j : I n) (mu : ℝ) :
    world A j mu = fun x => linear (coeff A j mu) x+gate A j x := rfl

theorem response_world_split (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (i : I n) (u : Bool) :
    productResponse (bern t) (world A j mu) i u
      = productResponse (bern t) (linear (coeff A j mu)) i u
        +productResponse (bern t) (gate A j) i u := by
  rw [world_eq_add]
  exact productResponse_add (bern t) (linear (coeff A j mu)) (gate A j) i u

/-- The modular offset carried by every level at every coordinate. -/
def modularPart (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ) (i : I n) (u : Bool) : ℝ :=
  coeff A j mu i*bit u+t*(((mu-1)+(1-mu)*((others A j).card:ℝ))-coeff A j mu i)

theorem response_world_modular (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) (i : I n) (u : Bool) :
    productResponse (bern t) (linear (coeff A j mu)) i u
      = modularPart t A j mu i u := by
  rw [response_linear t (coeff A j mu) i u, coeff_sum A j mu hjA]
  rfl

theorem response_world_at_j_true (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) :
    productResponse (bern t) (world A j mu) j true
      = modularPart t A j mu j true := by
  rw [response_world_split, response_world_modular t A j mu hjA,
    response_gate_j_true t A j]
  ring

theorem response_world_at_j_false (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (world A j mu) j false
      = modularPart t A j mu j false+(1-gateMass t A j) := by
  rw [response_world_split, response_world_modular t A j mu hjA,
    response_gate_j_false t A j hjA hB]

theorem response_world_at_A_true (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) (i : I n) (hiA : i ∈ A) :
    productResponse (bern t) (world A j mu) i true
      = modularPart t A j mu i true+(1-t) := by
  rw [response_world_split, response_world_modular t A j mu hjA,
    response_gate_A_true t A j hjA i hiA]

theorem response_world_at_A_false (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) (i : I n) (hiA : i ∈ A) (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (world A j mu) i false
      = modularPart t A j mu i false+((1-t)-gateMass t A j) := by
  rw [response_world_split, response_world_modular t A j mu hjA,
    response_gate_A_false t A j hjA i hiA hB]

theorem response_world_at_B_true (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) (i : I n) (hiB : i ∈ others A j) (hB2 : 2 ≤ (others A j).card) :
    productResponse (bern t) (world A j mu) i true
      = modularPart t A j mu i true
        +((1-t)-(1-t)^(A.card+(others A j).card)) := by
  rw [response_world_split, response_world_modular t A j mu hjA,
    response_gate_B_true t A j hjA i hiB hB2]

theorem response_world_at_B_false (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) (i : I n) (hiB : i ∈ others A j) (hB2 : 2 ≤ (others A j).card) :
    productResponse (bern t) (world A j mu) i false
      = modularPart t A j mu i false
        +((1-t)-(1-t)^(A.card+1)*tailFactor t ((others A j).erase i)) := by
  rw [response_world_split, response_world_modular t A j mu hjA,
    response_gate_B_false t A j hjA i hiB hB2]

/-! ## The levels reproduce the three already-proved slopes

This is the actual join obligation: the six level theorems above must be
consistent with `slope_at_j`, `slope_at_A` and `slope_at_B`, which were proved
independently. Each check below is `level true - level false`, with the modular
parts cancelling to exactly `coeff`, as `linear_slope` requires. -/

theorem gate_slope_j_from_levels (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) j true
        -productResponse (bern t) (gate A j) j false
      = gateMass t A j-1 := by
  rw [response_gate_j_true t A j, response_gate_j_false t A j hjA hB]
  ring

theorem gate_slope_A_from_levels (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (i : I n) (hiA : i ∈ A) (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) i true
        -productResponse (bern t) (gate A j) i false
      = gateMass t A j := by
  rw [response_gate_A_true t A j hjA i hiA, response_gate_A_false t A j hjA i hiA hB]
  ring

/-- Consistency with `slope_at_j`: the two levels give back the proved slope. -/
theorem levels_agree_with_slope_at_j (t : ℝ) (A : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) j true
        -productResponse (bern t) (gate A j) j false
      = (1-t)^A.card*((1-t)^(others A j).card
          +((others A j).card:ℝ)*t*(1-t)^((others A j).card-1))-1 :=
  slope_at_j t A j hjA hB

/-- Consistency with `slope_at_A`. -/
theorem levels_agree_with_slope_at_A (t : ℝ) (A : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (i : I n) (hiA : i ∈ A) (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) i true
        -productResponse (bern t) (gate A j) i false
      = (1-t)^A.card*((1-t)^(others A j).card
          +((others A j).card:ℝ)*t*(1-t)^((others A j).card-1)) :=
  slope_at_A t A j hjA i hiA hB

/-- Consistency with `slope_at_B`. -/
theorem levels_agree_with_slope_at_B (t : ℝ) (A : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (i : I n) (hiB : i ∈ others A j) (hB2 : 2 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) i true
        -productResponse (bern t) (gate A j) i false
      = (((others A j).card:ℝ)-1)*t*(1-t)^(A.card+(others A j).card-1) :=
  slope_at_B t A j hjA i hiB hB2

/-- `gateMass` IS the slope constant of `slope_at_A`; the level route and the
slope route name the same quantity. -/
theorem gateMass_eq_slope_at_A (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (i : I n) (hiA : i ∈ A) (hB : 1 ≤ (others A j).card) :
    gateMass t A j
      = productResponse (bern t) (gate A j) i true
          -productResponse (bern t) (gate A j) i false := by
  rw [gate_slope_A_from_levels t A j hjA i hiA hB]

/-! ## The world slope at every coordinate, from the levels -/

theorem world_slope_at_j (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (world A j mu) j true
        -productResponse (bern t) (world A j mu) j false
      = (mu-1)+(gateMass t A j-1) := by
  rw [response_world_at_j_true t A j mu hjA, response_world_at_j_false t A j mu hjA hB]
  unfold modularPart
  have hj : coeff A j mu j = mu-1 := by simp [coeff, hjA]
  rw [hj]
  simp [bit]
  ring

theorem world_slope_at_A (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) (i : I n) (hiA : i ∈ A) (hB : 1 ≤ (others A j).card) :
    productResponse (bern t) (world A j mu) i true
        -productResponse (bern t) (world A j mu) i false
      = gateMass t A j := by
  rw [response_world_at_A_true t A j mu hjA i hiA,
    response_world_at_A_false t A j mu hjA i hiA hB]
  unfold modularPart
  have hi : coeff A j mu i = 0 := by simp [coeff, hiA]
  rw [hi]
  simp [bit]

theorem world_slope_at_B (t : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (hjA : j ∉ A) (i : I n) (hiB : i ∈ others A j) (hB2 : 2 ≤ (others A j).card) :
    productResponse (bern t) (world A j mu) i true
        -productResponse (bern t) (world A j mu) i false
      = (1-mu)
        +(((1-t)-(1-t)^(A.card+(others A j).card))
          -((1-t)-(1-t)^(A.card+1)*tailFactor t ((others A j).erase i))) := by
  rw [response_world_at_B_true t A j mu hjA i hiB hB2,
    response_world_at_B_false t A j mu hjA i hiB hB2]
  unfold modularPart
  have hi : coeff A j mu i = 1-mu := by
    simp [coeff, others_not_mem_A A j i hiB, others_ne_j A j i hiB]
  rw [hi]
  simp [bit]
  ring

/-! ## Modular compensation

The reference dependence of `world` sits entirely in the gate. A modular part
contributes its own coefficient as its slope at EVERY product reference, so the
gate's reference dependence can be cancelled coordinatewise. -/

def compensator (t0 t1 : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ) (i : I n) : ℝ :=
  coeff A j mu i
    +(productResponse (bern t0) (gate A j) i true
      -productResponse (bern t0) (gate A j) i false)
    -(productResponse (bern t1) (gate A j) i true
      -productResponse (bern t1) (gate A j) i false)

/-- The compensated world at reference `t1` has exactly the slope of the original
world at reference `t0`, at every coordinate simultaneously. No condition on
`t0`, `t1`, `A`, `j` or `mu` is needed: this is the modular structure alone. -/
theorem compensated_slope_eq (t0 t1 : ℝ) (A : Finset (I n)) (j : I n) (mu : ℝ)
    (i : I n) :
    productResponse (bern t1)
        (fun x => linear (compensator t0 t1 A j mu) x+gate A j x) i true
      -productResponse (bern t1)
        (fun x => linear (compensator t0 t1 A j mu) x+gate A j x) i false
    = productResponse (bern t0) (world A j mu) i true
      -productResponse (bern t0) (world A j mu) i false := by
  rw [productResponse_add (bern t1) (linear (compensator t0 t1 A j mu)) (gate A j) i true,
    productResponse_add (bern t1) (linear (compensator t0 t1 A j mu)) (gate A j) i false,
    world_eq_add,
    productResponse_add (bern t0) (linear (coeff A j mu)) (gate A j) i true,
    productResponse_add (bern t0) (linear (coeff A j mu)) (gate A j) i false]
  have h1 : productResponse (bern t1) (linear (compensator t0 t1 A j mu)) i true
      -productResponse (bern t1) (linear (compensator t0 t1 A j mu)) i false
      = compensator t0 t1 A j mu i :=
    linear_slope (bern t1) (bern_normalized t1) (compensator t0 t1 A j mu) i
  have h0 : productResponse (bern t0) (linear (coeff A j mu)) i true
      -productResponse (bern t0) (linear (coeff A j mu)) i false
      = coeff A j mu i :=
    linear_slope (bern t0) (bern_normalized t0) (coeff A j mu) i
  unfold compensator at h1 ⊢
  linarith

#print axioms expect_const
#print axioms expect_smul
#print axioms expect_bit
#print axioms coordinate_trichotomy
#print axioms disjoint_A_others
#print axioms response_linear_erase
#print axioms response_linear
#print axioms coeff_sum
#print axioms response_gate_j_true
#print axioms response_gate_j_false
#print axioms response_gate_A_true
#print axioms response_gate_A_false
#print axioms response_gate_B_true
#print axioms response_gate_B_false
#print axioms response_world_split
#print axioms response_world_modular
#print axioms response_world_at_j_true
#print axioms response_world_at_j_false
#print axioms response_world_at_A_true
#print axioms response_world_at_A_false
#print axioms response_world_at_B_true
#print axioms response_world_at_B_false
#print axioms gate_slope_j_from_levels
#print axioms gate_slope_A_from_levels
#print axioms gateMass_eq_slope_at_A
#print axioms world_slope_at_j
#print axioms world_slope_at_A
#print axioms world_slope_at_B
#print axioms compensated_slope_eq

end
end CIGAMF.P13.D6ReferenceResponseJoin
