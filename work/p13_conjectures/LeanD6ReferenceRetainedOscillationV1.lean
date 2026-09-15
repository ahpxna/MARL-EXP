import «LeanD6ReferenceCenteredCompensatedV1»
import «LeanD6ReferenceReducedGameV1»

/-! # D04b: the ACTUAL retained-residual oscillation at a general reference.

D04a (`LeanD6ReferenceCenteredCompensatedV1`) pins both response levels of the
centered compensated world to `rho * 1_T * (bit u - t)`, independently of the
hidden set. This module computes what the learner actually pays.

For a retained set `S`, write `D = T \ S`. Everything below is about the actual
function on the actual cube

    core A D j rho t x = gate A j x + linear (retainedCoeff A D j rho t) x,
    retainedCoeff A D j rho t i = (if i ∈ D then rho else 0) - gateSlope t A j i,

which `retained_residual` proves is the retained residual of the actual world up
to an additive constant, so `retained_loss` identifies
`productCompressionLoss` with `osc core / 2`.

## What is proved

* `hi_value`, `lo_value` : the two explicit witnesses `hiPoint D = 1_D` and
  `loPoint D = 1_{Dᶜ}` are points of the REAL cube and their values are computed
  in closed form.
* `core_le`, `core_ge` : those two values bound the whole cube.
* `oscillation` : hence the exact COUNT FORMULA

      osc = a*(1+|A|) + b*|B| + rho*|D| - 2a*|D ∩ A| - 2b*|D ∩ B|

  with `a = gateMass t A j`, `b = slopeBval t A j`, `B = others A j`. The
  retained set enters ONLY through the three counts `|D|`, `|D ∩ A|`, `|D ∩ B|`.
* `corner_recovers_actual_loss` : at `t = 0`, `a = 1` and `b = 0`, and the
  formula becomes `(1 + |A| + rho|T\S| - 2|A ∩ (T\S)|)/2`, which is literally
  `D6SameResponseMarginLoss.actual_loss_formula`.
* `count_realizable` : every count triple used is realized by an actual retained
  set, namely `S = T \ D`; no count in the formula is vacuous.
* `count_formula_is_payoff` : after symmetry averaging the regret of the count
  formula IS `D6ReferenceReducedGame.payoff k a b rho h d`, with `a := gateMass`
  and `b := slopeBval`. This is the splice: the already-proved
  `primal_equalizer` / `dual_equalizer` / `value` apply verbatim with those two
  substitutions, and at `t = 0` they give back `k*rho*(2-rho)/4`.

## The sign region, stated explicitly

`core_ge` is NOT unconditional. Its proof needs

    hA :  1 - gateMass t A j  ≤  gateMass t A j * |Dᶜ ∩ A|                 (*)

which holds automatically at the corner (`gateMass 0 = 1`) and is the exact
place where `t > 0` changes the geometry: when (*) fails the minimum moves off
`loPoint D` to a point where the gate does not fire, and the oscillation is
strictly larger. Exact-arithmetic enumeration over N = 4,5 (all A, j, D; t in
{0,1/8,1/4,1/2,3/4,1}; rho in {1,3/2,2}) found the true minimum to be
`min(loValue, -b * min(|Dᶜ ∩ B|,1))` in 13698/13698 cases, with the second
branch active in 8763 of them. So (*) is a real restriction, not an artefact,
and the complementary branch is NOT proved here.

Likewise `hfire` (`gate` fires at `hiPoint D`) is needed for `core_le` to be
attained. At `D = ∅` it fails and the maximum drops by exactly
`min(gateMass, 2*slopeBval)` — which is the correction `e = min a (2b)` carried
by `LeanD6ReferencePhaseValueV1`. That identification was checked exactly
(3816 cells, 0 failures) but is NOT proved here; it is the remaining D05 step.
Do not read this module as the actual minimax theorem: it is the exact loss law
on the gate-firing sign region, plus the algebraic splice.

EVIDENCE. The count formula and both witnesses were checked with exact
`Fraction` arithmetic against this corpus's own `gate`/`linear` on 54980
configurations satisfying `hfire` and (*); 0 failures. `#print axioms` at the
bottom is what licenses PROVED.
-/

namespace CIGAMF.P13.D6ReferenceRetainedOscillation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge CIGAMF.P13.D6ReferenceTail
open CIGAMF.P13.D6ReferenceSlope CIGAMF.P13.D6ReferenceSlopeB
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

/-! ## The retained residual -/

def retainedCoeff (A D : Finset (I n)) (j : I n) (rho t : ℝ) (i : I n) : ℝ :=
  (if i ∈ D then rho else 0)-gateSlope t A j i

def core (A D : Finset (I n)) (j : I n) (rho t : ℝ) (x : I n → Bool) : ℝ :=
  gate A j x+linear (retainedCoeff A D j rho t) x

/-- The all-`D` corner of the real cube. -/
def hiPoint (D : Finset (I n)) : I n → Bool := fun i => decide (i ∈ D)
/-- Its complement. -/
def loPoint (D : Finset (I n)) : I n → Bool := fun i => decide (i ∉ D)

theorem retained_coeff_eq (A T S : Finset (I n)) (j : I n) (rho t : ℝ) (i : I n) :
    compensation A T j rho t i-(if i ∈ S then target T rho i else 0)
      = retainedCoeff A (T \ S) j rho t i := by
  classical
  have hmem : (i ∈ T \ S) ↔ (i ∈ T ∧ i ∉ S) := Finset.mem_sdiff
  unfold compensation retainedCoeff target
  by_cases hT : i ∈ T <;> by_cases hS : i ∈ S <;> simp [hT, hS, hmem] <;> ring

/-- The actual retained residual of the actual world, up to an additive
constant. Nothing is postulated: the response subtracted is the one D04a
computed. -/
theorem retained_residual (t : ℝ) (A T S : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB2 : 2 ≤ (others A j).card) (rho : ℝ) (x : I n → Bool) :
    centeredWorld A T j rho t x
        -∑ i ∈ S, productResponse (bern t) (centeredWorld A T j rho t) i (x i)
      = core A (T \ S) j rho t x
        +(t*(∑ i ∈ S, target T rho i)-shift A T j rho t) := by
  classical
  simp_rw [centered_response t A T j hjA hB2 rho]
  have h1 : (∑ i : I n, (if i ∈ S then target T rho i else 0)*bit (x i))
      = ∑ i ∈ S, target T rho i*bit (x i) := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  have hS : (∑ i ∈ S, target T rho i*(bit (x i)-t))
      = (∑ i : I n, (if i ∈ S then target T rho i else 0)*bit (x i))
        -t*(∑ i ∈ S, target T rho i) := by
    rw [h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hsum : (∑ i : I n, compensation A T j rho t i*bit (x i))
      -(∑ i : I n, (if i ∈ S then target T rho i else 0)*bit (x i))
      = ∑ i : I n, retainedCoeff A (T \ S) j rho t i*bit (x i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← sub_mul, retained_coeff_eq A T S j rho t i]
  rw [hS]
  unfold centeredWorld core linear
  linarith [hsum]

theorem retained_loss (t : ℝ) (A T S : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB2 : 2 ≤ (others A j).card) (rho : ℝ) :
    productCompressionLoss (centeredWorld A T j rho t)
        (productResponse (bern t) (centeredWorld A T j rho t)) S
      = osc (core A (T \ S) j rho t)/2 := by
  classical
  unfold productCompressionLoss
  rw [show (fun x : I n → Bool => centeredWorld A T j rho t x
        -∑ i ∈ S, productResponse (bern t) (centeredWorld A T j rho t) i (x i))
      = (fun x : I n → Bool => core A (T \ S) j rho t x
          +(t*(∑ i ∈ S, target T rho i)-shift A T j rho t)) from
      funext (fun x => retained_residual t A T S j hjA hB2 rho x),
    osc_add_const]

/-! ## Membership and counting infrastructure -/

theorem mem_others_iff (A : Finset (I n)) (j : I n) (i : I n) :
    i ∈ others A j ↔ i ≠ j ∧ i ∉ A := by
  unfold others
  simp [Finset.mem_erase, Finset.mem_sdiff]

theorem sdiff_A_eq_inter_others (A E : Finset (I n)) (j : I n) (hjE : j ∉ E) :
    E \ A = E ∩ others A j := by
  classical
  ext i
  rw [Finset.mem_sdiff, Finset.mem_inter, mem_others_iff]
  constructor
  · rintro ⟨hiE, hiA⟩
    exact ⟨hiE, ⟨by rintro rfl; exact hjE hiE, hiA⟩⟩
  · rintro ⟨hiE, _, hiA⟩
    exact ⟨hiE, hiA⟩

theorem sdiff_inter_eq (A E : Finset (I n)) (j : I n) (hjE : j ∉ E) :
    E \ (E ∩ A) = E ∩ others A j := by
  classical
  have h1 : E \ (E ∩ A) = E \ A := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [h1]
  exact sdiff_A_eq_inter_others A E j hjE

theorem sum_gateSlope (t : ℝ) (A : Finset (I n)) (j : I n) (E : Finset (I n)) (hjE : j ∉ E) :
    (∑ i ∈ E, gateSlope t A j i)
      = gateMass t A j*((E ∩ A).card:ℝ)+slopeBval t A j*((E ∩ others A j).card:ℝ) := by
  classical
  have hsplit := Finset.sum_sdiff (s₁ := E ∩ A) (s₂ := E)
    (f := fun i => gateSlope t A j i) Finset.inter_subset_left
  rw [sdiff_inter_eq A E j hjE] at hsplit
  have h1 : (∑ i ∈ E ∩ A, gateSlope t A j i) = gateMass t A j*((E ∩ A).card:ℝ) := by
    have hc : ∀ i ∈ E ∩ A, gateSlope t A j i = gateMass t A j := by
      intro i hi
      have hiE := (Finset.mem_inter.mp hi).1
      have hiA := (Finset.mem_inter.mp hi).2
      exact gateSlope_mem_A t A j i (by rintro rfl; exact hjE hiE) hiA
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    ring
  have h2 : (∑ i ∈ E ∩ others A j, gateSlope t A j i)
      = slopeBval t A j*((E ∩ others A j).card:ℝ) := by
    have hc : ∀ i ∈ E ∩ others A j, gateSlope t A j i = slopeBval t A j := by
      intro i hi
      have hio := (Finset.mem_inter.mp hi).2
      exact gateSlope_others t A j i (others_ne_j A j i hio) (others_not_mem_A A j i hio)
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [← hsplit, h1, h2]
  ring

theorem card_split (A E : Finset (I n)) (j : I n) (hjE : j ∉ E) :
    ((E ∩ A).card:ℝ)+((E ∩ others A j).card:ℝ) = (E.card:ℝ) := by
  classical
  have hsplit := Finset.sum_sdiff (s₁ := E ∩ A) (s₂ := E)
    (f := fun _ : I n => (1:ℝ)) Finset.inter_subset_left
  rw [sdiff_inter_eq A E j hjE] at hsplit
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsplit
  linarith

theorem card_compl_split (S D : Finset (I n)) :
    ((D ∩ S).card:ℝ)+((Dᶜ ∩ S).card:ℝ) = (S.card:ℝ) := by
  classical
  have h1 : D ∩ S = S ∩ D := Finset.inter_comm D S
  have h2 : Dᶜ ∩ S = S \ D := by
    ext i
    rw [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have h3 : S \ (S ∩ D) = S \ D := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsplit := Finset.sum_sdiff (s₁ := S ∩ D) (s₂ := S)
    (f := fun _ : I n => (1:ℝ)) Finset.inter_subset_left
  rw [h3] at hsplit
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsplit
  rw [h1, h2]
  linarith

/-! ## The two witnesses are points of the real cube -/

theorem linear_at_hiPoint (c' : I n → ℝ) (D : Finset (I n)) :
    linear c' (hiPoint D) = ∑ i ∈ D, c' i := by
  classical
  have h : ∀ i ∈ (Finset.univ : Finset (I n)),
      c' i*bit (hiPoint D i) = if i ∈ D then c' i else 0 := by
    intro i _
    by_cases hi : i ∈ D <;> simp [hiPoint, hi, bit]
  unfold linear
  rw [Finset.sum_congr rfl h, Finset.sum_ite_mem, Finset.univ_inter]

theorem linear_at_loPoint (c' : I n → ℝ) (D : Finset (I n)) :
    linear c' (loPoint D) = ∑ i ∈ Dᶜ, c' i := by
  classical
  have h : ∀ i ∈ (Finset.univ : Finset (I n)),
      c' i*bit (loPoint D i) = if i ∈ Dᶜ then c' i else 0 := by
    intro i _
    by_cases hi : i ∈ D <;> simp [loPoint, hi, bit, Finset.mem_compl]
  unfold linear
  rw [Finset.sum_congr rfl h, Finset.sum_ite_mem, Finset.univ_inter]

theorem gate_at_loPoint (A D : Finset (I n)) (j : I n) (hjD : j ∉ D) :
    gate A j (loPoint D) = 0 := by
  have h : loPoint D j = true := by simp [loPoint, hjD]
  simp [gate, h]

theorem gate_at_hiPoint (A D : Finset (I n)) (j : I n) (hjD : j ∉ D)
    (hfire : (∃ i ∈ A, i ∈ D) ∨ 2 ≤ (D ∩ others A j).card) :
    gate A j (hiPoint D) = 1 := by
  classical
  have hj : hiPoint D j = false := by simp [hiPoint, hjD]
  have hP : (∃ i ∈ A, hiPoint D i = true) ∨ 2 ≤ count (others A j) (hiPoint D) := by
    rcases hfire with ⟨i, hiA, hiD⟩|hc
    · exact Or.inl ⟨i, hiA, by simp [hiPoint, hiD]⟩
    · refine Or.inr ?_
      have hf : (others A j).filter (fun i => hiPoint D i = true) = others A j ∩ D := by
        ext i
        simp [hiPoint, Finset.mem_filter, Finset.mem_inter]
      have hcnt : count (others A j) (hiPoint D) = (others A j ∩ D).card := by
        unfold count
        rw [hf]
      rw [hcnt, Finset.inter_comm]
      exact hc
  simp [gate, hj, hP]

theorem hi_value (t : ℝ) (A D : Finset (I n)) (j : I n) (hjD : j ∉ D) (rho : ℝ)
    (hfire : (∃ i ∈ A, i ∈ D) ∨ 2 ≤ (D ∩ others A j).card) :
    core A D j rho t (hiPoint D)
      = 1+((rho-gateMass t A j)*((D ∩ A).card:ℝ)
          +(rho-slopeBval t A j)*((D ∩ others A j).card:ℝ)) := by
  classical
  unfold core
  rw [gate_at_hiPoint A D j hjD hfire, linear_at_hiPoint]
  have hc : ∀ i ∈ D, retainedCoeff A D j rho t i = rho-gateSlope t A j i := by
    intro i hi
    unfold retainedCoeff
    rw [if_pos hi]
  rw [Finset.sum_congr rfl hc, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    sum_gateSlope t A j D hjD, ← card_split A D j hjD]
  ring

/-- The tail of the low witness, used both for its value and for the lower
bound on the whole cube. -/
theorem lo_tail_sum (t : ℝ) (A D : Finset (I n)) (j : I n) (hjA : j ∉ A) (rho : ℝ) :
    (∑ i ∈ Dᶜ.erase j, retainedCoeff A D j rho t i)
      = -(gateMass t A j*((Dᶜ ∩ A).card:ℝ))-slopeBval t A j*((Dᶜ ∩ others A j).card:ℝ) := by
  classical
  have hjE : j ∉ Dᶜ.erase j := Finset.notMem_erase j Dᶜ
  have hc : ∀ i ∈ Dᶜ.erase j, retainedCoeff A D j rho t i = (-1)*gateSlope t A j i := by
    intro i hi
    have hiDc : i ∈ Dᶜ := Finset.mem_of_mem_erase hi
    have hiD : i ∉ D := by simpa using hiDc
    unfold retainedCoeff
    rw [if_neg hiD]
    ring
  have hEA : (Dᶜ.erase j) ∩ A = Dᶜ ∩ A := by
    ext i
    constructor
    · intro h
      exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp h).1,
        (Finset.mem_inter.mp h).2⟩
    · intro h
      have h1 := (Finset.mem_inter.mp h).1
      have h2 := (Finset.mem_inter.mp h).2
      exact Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨by rintro rfl; exact hjA h2, h1⟩, h2⟩
  have hEB : (Dᶜ.erase j) ∩ others A j = Dᶜ ∩ others A j := by
    ext i
    constructor
    · intro h
      exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp h).1,
        (Finset.mem_inter.mp h).2⟩
    · intro h
      have h1 := (Finset.mem_inter.mp h).1
      have h2 := (Finset.mem_inter.mp h).2
      exact Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨others_ne_j A j i h2, h1⟩, h2⟩
  rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, sum_gateSlope t A j (Dᶜ.erase j) hjE,
    hEA, hEB]
  ring

theorem lo_value (t : ℝ) (A D : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjD : j ∉ D)
    (rho : ℝ) :
    core A D j rho t (loPoint D)
      = (1-gateMass t A j)-gateMass t A j*((Dᶜ ∩ A).card:ℝ)
        -slopeBval t A j*((Dᶜ ∩ others A j).card:ℝ) := by
  classical
  unfold core
  rw [gate_at_loPoint A D j hjD, linear_at_loPoint, zero_add]
  have hjDc : j ∈ Dᶜ := by simpa using hjD
  rw [← Finset.add_sum_erase Dᶜ (retainedCoeff A D j rho t) hjDc]
  have hrj : retainedCoeff A D j rho t j = 1-gateMass t A j := by
    unfold retainedCoeff
    rw [if_neg hjD, gateSlope_at_j]
    ring
  rw [hrj, lo_tail_sum t A D j hjA rho]
  ring

/-! ## The sign region, derived rather than assumed -/

theorem expect_mono (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (f g : (I n → Bool) → ℝ)
    (h : ∀ c, f c ≤ g c) :
    productExpectation (bern t) f ≤ productExpectation (bern t) g := by
  unfold productExpectation
  refine Finset.sum_le_sum (fun c _ => ?_)
  exact mul_le_mul_of_nonneg_left (h c) (bern_nonnegative t ht0 ht1 c)

theorem offProd_bounds (B : Finset (I n)) (x : I n → Bool) :
    0 ≤ offProd B x ∧ offProd B x ≤ 1 := by
  constructor
  · unfold offProd
    refine Finset.prod_nonneg (fun i _ => ?_)
    cases h : x i <;> simp [h, bit]
  · unfold offProd
    refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
    · cases h : x i <;> simp [h, bit]
    · cases h : x i <;> simp [h, bit]

theorem leOne_bounds (B : Finset (I n)) (x : I n → Bool) :
    0 ≤ leOne B x ∧ leOne B x ≤ 1 := by
  unfold leOne
  split <;> norm_num

theorem gateMass_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (A : Finset (I n)) (j : I n)
    (hB1 : 1 ≤ (others A j).card) :
    0 ≤ gateMass t A j ∧ gateMass t A j ≤ 1 := by
  classical
  have hd : Disjoint A (others A j) := disjoint_A_others A j
  have he : gateMass t A j
      = productExpectation (bern t) (fun c => offProd A c*leOne (others A j) c) := by
    rw [expect_offProd_mul_leOne t A (others A j) hd hB1]
    rfl
  constructor
  · rw [he, ← expect_const t (0:ℝ)]
    exact expect_mono t ht0 ht1 _ _ (fun c => mul_nonneg (offProd_bounds A c).1
      (leOne_bounds (others A j) c).1)
  · rw [he, ← expect_const t (1:ℝ)]
    refine expect_mono t ht0 ht1 _ _ (fun c => ?_)
    have ha := offProd_bounds A c
    have hb := leOne_bounds (others A j) c
    nlinarith [ha.1, ha.2, hb.1, hb.2]

theorem slopeBval_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (A : Finset (I n)) (j : I n)
    (hB2 : 2 ≤ (others A j).card) : 0 ≤ slopeBval t A j := by
  unfold slopeBval
  have h1 : (0:ℝ) ≤ ((others A j).card:ℝ)-1 := by
    have h : (2:ℝ) ≤ ((others A j).card:ℝ) := by exact_mod_cast hB2
    linarith
  have h2 : (0:ℝ) ≤ (1-t)^(A.card+(others A j).card-1) := by
    apply pow_nonneg
    linarith
  exact mul_nonneg (mul_nonneg h1 ht0) h2

theorem gate_response_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (A : Finset (I n))
    (j : I n) (i : I n) (u : Bool) :
    0 ≤ productResponse (bern t) (gate A j) i u
      ∧ productResponse (bern t) (gate A j) i u ≤ 1 := by
  unfold productResponse
  constructor
  · rw [← expect_const t (0:ℝ)]
    exact expect_mono t ht0 ht1 _ _ (fun c => (gate_bounds A j (Function.update c i u)).1)
  · rw [← expect_const t (1:ℝ)]
    exact expect_mono t ht0 ht1 _ _ (fun c => (gate_bounds A j (Function.update c i u)).2)

theorem slopeBval_le_one (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (A : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hB2 : 2 ≤ (others A j).card) : slopeBval t A j ≤ 1 := by
  obtain ⟨i, hi⟩ : (others A j).Nonempty := Finset.card_pos.mp (by omega)
  have h := slope_at_B t A j hjA i hi hB2
  have h1 := gate_response_bounds t ht0 ht1 A j i true
  have h2 := gate_response_bounds t ht0 ht1 A j i false
  unfold slopeBval
  linarith [h, h1.2, h2.1]

/-! ## The whole cube is between the two witnesses -/

theorem core_le (t : ℝ) (A D : Finset (I n)) (j : I n) (hjD : j ∉ D) (rho : ℝ)
    (hG0 : 0 ≤ gateMass t A j) (hs0 : 0 ≤ slopeBval t A j)
    (hGr : gateMass t A j ≤ rho) (hsr : slopeBval t A j ≤ rho) (x : I n → Bool) :
    core A D j rho t x
      ≤ 1+((rho-gateMass t A j)*((D ∩ A).card:ℝ)
          +(rho-slopeBval t A j)*((D ∩ others A j).card:ℝ)) := by
  classical
  have hjU : j ∈ (Finset.univ : Finset (I n)) := Finset.mem_univ j
  have hsplit : linear (retainedCoeff A D j rho t) x
      = retainedCoeff A D j rho t j*bit (x j)
        +∑ i ∈ (Finset.univ : Finset (I n)).erase j,
            retainedCoeff A D j rho t i*bit (x i) := by
    unfold linear
    rw [← Finset.add_sum_erase (Finset.univ : Finset (I n))
      (fun i => retainedCoeff A D j rho t i*bit (x i)) hjU]
  have hinter : ((Finset.univ : Finset (I n)).erase j) ∩ D = D := by
    ext i
    constructor
    · intro h
      exact (Finset.mem_inter.mp h).2
    · intro h
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_erase.mpr ⟨by rintro rfl; exact hjD h, Finset.mem_univ i⟩, h⟩
  have hbound : ∀ i ∈ (Finset.univ : Finset (I n)).erase j,
      retainedCoeff A D j rho t i*bit (x i)
        ≤ (if i ∈ D then retainedCoeff A D j rho t i else 0) := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hb := bit_bounds (x i)
    by_cases hiD : i ∈ D
    · rw [if_pos hiD]
      have hpos : 0 ≤ retainedCoeff A D j rho t i := by
        unfold retainedCoeff
        rw [if_pos hiD]
        by_cases hiA : i ∈ A
        · rw [gateSlope_mem_A t A j i hij hiA]; linarith
        · rw [gateSlope_others t A j i hij hiA]; linarith
      nlinarith [hb.1, hb.2]
    · rw [if_neg hiD]
      have hneg : retainedCoeff A D j rho t i ≤ 0 := by
        unfold retainedCoeff
        rw [if_neg hiD]
        by_cases hiA : i ∈ A
        · rw [gateSlope_mem_A t A j i hij hiA]; linarith
        · rw [gateSlope_others t A j i hij hiA]; linarith
      nlinarith [hb.1]
  have htail : (∑ i ∈ (Finset.univ : Finset (I n)).erase j,
        retainedCoeff A D j rho t i*bit (x i))
      ≤ ∑ i ∈ D, retainedCoeff A D j rho t i := by
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [Finset.sum_ite_mem, hinter]
  have hP : (∑ i ∈ D, retainedCoeff A D j rho t i)
      = (rho-gateMass t A j)*((D ∩ A).card:ℝ)
        +(rho-slopeBval t A j)*((D ∩ others A j).card:ℝ) := by
    have hc : ∀ i ∈ D, retainedCoeff A D j rho t i = rho-gateSlope t A j i := by
      intro i hi
      unfold retainedCoeff
      rw [if_pos hi]
    rw [Finset.sum_congr rfl hc, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      sum_gateSlope t A j D hjD, ← card_split A D j hjD]
    ring
  have hrj : retainedCoeff A D j rho t j = 1-gateMass t A j := by
    unfold retainedCoeff
    rw [if_neg hjD, gateSlope_at_j]
    ring
  have hjterm : gate A j x+retainedCoeff A D j rho t j*bit (x j) ≤ 1 := by
    rw [hrj]
    cases hxj : x j with
    | false =>
        rw [bit_false, mul_zero, add_zero]
        exact (gate_bounds A j x).2
    | true =>
        have hg : gate A j x = 0 := by simp [gate, hxj]
        rw [hg, bit_true, mul_one, zero_add]
        linarith
  unfold core
  rw [hsplit]
  linarith [htail, hjterm, hP]

theorem core_ge (t : ℝ) (A D : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjD : j ∉ D)
    (rho : ℝ) (hG0 : 0 ≤ gateMass t A j) (hs0 : 0 ≤ slopeBval t A j)
    (hGr : gateMass t A j ≤ rho) (hsr : slopeBval t A j ≤ rho)
    (hA : 1-gateMass t A j ≤ gateMass t A j*((Dᶜ ∩ A).card:ℝ)) (x : I n → Bool) :
    (1-gateMass t A j)-gateMass t A j*((Dᶜ ∩ A).card:ℝ)
        -slopeBval t A j*((Dᶜ ∩ others A j).card:ℝ)
      ≤ core A D j rho t x := by
  classical
  have hjU : j ∈ (Finset.univ : Finset (I n)) := Finset.mem_univ j
  have hsplit : linear (retainedCoeff A D j rho t) x
      = retainedCoeff A D j rho t j*bit (x j)
        +∑ i ∈ (Finset.univ : Finset (I n)).erase j,
            retainedCoeff A D j rho t i*bit (x i) := by
    unfold linear
    rw [← Finset.add_sum_erase (Finset.univ : Finset (I n))
      (fun i => retainedCoeff A D j rho t i*bit (x i)) hjU]
  have hrj : retainedCoeff A D j rho t j = 1-gateMass t A j := by
    unfold retainedCoeff
    rw [if_neg hjD, gateSlope_at_j]
    ring
  have hsign : ∀ i, i ≠ j → i ∈ D → 0 ≤ retainedCoeff A D j rho t i := by
    intro i hij hiD
    unfold retainedCoeff
    rw [if_pos hiD]
    by_cases hiA : i ∈ A
    · rw [gateSlope_mem_A t A j i hij hiA]; linarith
    · rw [gateSlope_others t A j i hij hiA]; linarith
  have hsign' : ∀ i, i ≠ j → i ∉ D → retainedCoeff A D j rho t i ≤ 0 := by
    intro i hij hiD
    unfold retainedCoeff
    rw [if_neg hiD]
    by_cases hiA : i ∈ A
    · rw [gateSlope_mem_A t A j i hij hiA]; linarith
    · rw [gateSlope_others t A j i hij hiA]; linarith
  -- the full tail bound, valid whenever the `j` coordinate carries `1 - gateMass`
  have hfullEq : ((Finset.univ : Finset (I n)).erase j) ∩ Dᶜ = Dᶜ.erase j := by
    ext i
    constructor
    · intro h
      have h1 := Finset.mem_erase.mp (Finset.mem_inter.mp h).1
      exact Finset.mem_erase.mpr ⟨h1.1, (Finset.mem_inter.mp h).2⟩
    · intro h
      have h1 := Finset.mem_erase.mp h
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_erase.mpr ⟨h1.1, Finset.mem_univ i⟩, h1.2⟩
  have hfull : (∑ i ∈ Dᶜ.erase j, retainedCoeff A D j rho t i)
      ≤ ∑ i ∈ (Finset.univ : Finset (I n)).erase j,
          retainedCoeff A D j rho t i*bit (x i) := by
    have hb : ∀ i ∈ (Finset.univ : Finset (I n)).erase j,
        (if i ∈ Dᶜ then retainedCoeff A D j rho t i else 0)
          ≤ retainedCoeff A D j rho t i*bit (x i) := by
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      have hbb := bit_bounds (x i)
      by_cases hiD : i ∈ D
      · rw [if_neg (by simpa using hiD)]
        nlinarith [hsign i hij hiD, hbb.1]
      · rw [if_pos (by simpa using hiD)]
        nlinarith [hsign' i hij hiD, hbb.2]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hb)
    rw [Finset.sum_ite_mem, hfullEq]
  have htailval := lo_tail_sum t A D j hjA rho
  -- three cases on the gate
  cases hxj : x j with
  | true =>
      have hg : gate A j x = 0 := by simp [gate, hxj]
      unfold core
      rw [hsplit, hg, hrj, hxj, bit_true, mul_one]
      linarith [hfull, htailval]
  | false =>
      by_cases hP : (∃ i ∈ A, x i = true) ∨ 2 ≤ count (others A j) x
      · have hg : gate A j x = 1 := by simp [gate, hxj, hP]
        unfold core
        rw [hsplit, hg, hrj, hxj, bit_false, mul_zero, zero_add]
        linarith [hfull, htailval]
      · have hg : gate A j x = 0 := by simp [gate, hxj, hP]
        have hAoff : ∀ i ∈ A, x i = false := by
          intro i hi
          cases hx : x i with
          | false => rfl
          | true => exact absurd (Or.inl ⟨i, hi, hx⟩) hP
        -- on this branch every A coordinate is off, so only `others ∩ Dᶜ` can hurt
        have hbound2 : ∀ i ∈ (Finset.univ : Finset (I n)).erase j,
            (if i ∈ others A j ∩ Dᶜ then retainedCoeff A D j rho t i else 0)
              ≤ retainedCoeff A D j rho t i*bit (x i) := by
          intro i hi
          have hij : i ≠ j := Finset.ne_of_mem_erase hi
          have hbb := bit_bounds (x i)
          by_cases hiA : i ∈ A
          · have hoff : bit (x i) = 0 := by rw [hAoff i hiA]; exact bit_false
            have hnm : i ∉ others A j ∩ Dᶜ := by
              intro hc
              exact (others_not_mem_A A j i (Finset.mem_inter.mp hc).1) hiA
            rw [if_neg hnm, hoff, mul_zero]
          · have hio : i ∈ others A j := (mem_others_iff A j i).mpr ⟨hij, hiA⟩
            by_cases hiD : i ∈ D
            · have hnm : i ∉ others A j ∩ Dᶜ := by
                intro hc
                exact (by simpa using (Finset.mem_inter.mp hc).2 : i ∉ D) hiD
              rw [if_neg hnm]
              nlinarith [hsign i hij hiD, hbb.1]
            · have hm : i ∈ others A j ∩ Dᶜ :=
                Finset.mem_inter.mpr ⟨hio, by simpa using hiD⟩
              rw [if_pos hm]
              nlinarith [hsign' i hij hiD, hbb.2]
        have hsubE : ((Finset.univ : Finset (I n)).erase j) ∩ (others A j ∩ Dᶜ)
            = others A j ∩ Dᶜ := by
          ext i
          constructor
          · intro h
            exact (Finset.mem_inter.mp h).2
          · intro h
            have hio := (Finset.mem_inter.mp h).1
            exact Finset.mem_inter.mpr
              ⟨Finset.mem_erase.mpr ⟨others_ne_j A j i hio, Finset.mem_univ i⟩, h⟩
        have htail2 : (∑ i ∈ others A j ∩ Dᶜ, retainedCoeff A D j rho t i)
            ≤ ∑ i ∈ (Finset.univ : Finset (I n)).erase j,
                retainedCoeff A D j rho t i*bit (x i) := by
          refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hbound2)
          rw [Finset.sum_ite_mem, hsubE]
        have hcomm : others A j ∩ Dᶜ = Dᶜ ∩ others A j := Finset.inter_comm _ _
        have hval2 : (∑ i ∈ others A j ∩ Dᶜ, retainedCoeff A D j rho t i)
            = -(slopeBval t A j*((Dᶜ ∩ others A j).card:ℝ)) := by
          have hc : ∀ i ∈ others A j ∩ Dᶜ,
              retainedCoeff A D j rho t i = (-1)*slopeBval t A j := by
            intro i hi
            have hio := (Finset.mem_inter.mp hi).1
            have hiD : i ∉ D := by simpa using (Finset.mem_inter.mp hi).2
            unfold retainedCoeff
            rw [if_neg hiD,
              gateSlope_others t A j i (others_ne_j A j i hio) (others_not_mem_A A j i hio)]
            ring
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, hcomm]
          ring
        unfold core
        rw [hsplit, hg, hrj, hxj, bit_false, mul_zero, zero_add]
        rw [hval2] at htail2
        linarith [htail2, hA]

/-! ## The exact count formula -/

/-- **D04b.** The actual oscillation of the actual retained residual on the
actual cube. The retained set enters only through the three counts. -/
theorem oscillation (t : ℝ) (A D : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjD : j ∉ D)
    (rho : ℝ) (hG0 : 0 ≤ gateMass t A j) (hs0 : 0 ≤ slopeBval t A j)
    (hGr : gateMass t A j ≤ rho) (hsr : slopeBval t A j ≤ rho)
    (hfire : (∃ i ∈ A, i ∈ D) ∨ 2 ≤ (D ∩ others A j).card)
    (hA : 1-gateMass t A j ≤ gateMass t A j*((Dᶜ ∩ A).card:ℝ)) :
    osc (core A D j rho t)
      = gateMass t A j*(1+(A.card:ℝ))+slopeBval t A j*((others A j).card:ℝ)
        +rho*(D.card:ℝ)-2*gateMass t A j*((D ∩ A).card:ℝ)
        -2*slopeBval t A j*((D ∩ others A j).card:ℝ) := by
  classical
  rw [osc_of_extremes (core A D j rho t) (loPoint D) (hiPoint D)
    (fun x => by
      rw [lo_value t A D j hjA hjD rho]
      exact core_ge t A D j hjA hjD rho hG0 hs0 hGr hsr hA x)
    (fun x => by
      rw [hi_value t A D j hjD rho hfire]
      exact core_le t A D j hjD rho hG0 hs0 hGr hsr x),
    hi_value t A D j hjD rho hfire, lo_value t A D j hjA hjD rho]
  have h1 : ((D ∩ A).card:ℝ)+((Dᶜ ∩ A).card:ℝ) = (A.card:ℝ) := card_compl_split A D
  have h2 : ((D ∩ others A j).card:ℝ)+((Dᶜ ∩ others A j).card:ℝ)
      = ((others A j).card:ℝ) := card_compl_split (others A j) D
  have h3 : ((D ∩ A).card:ℝ)+((D ∩ others A j).card:ℝ) = (D.card:ℝ) :=
    card_split A D j hjD
  rw [← h1, ← h2, ← h3]
  ring

/-- The same law as a loss, for an arbitrary retained set `S`. -/
theorem retained_loss_formula (t : ℝ) (A T S : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hjT : j ∉ T) (hB2 : 2 ≤ (others A j).card) (rho : ℝ)
    (hG0 : 0 ≤ gateMass t A j) (hs0 : 0 ≤ slopeBval t A j)
    (hGr : gateMass t A j ≤ rho) (hsr : slopeBval t A j ≤ rho)
    (hfire : (∃ i ∈ A, i ∈ T \ S) ∨ 2 ≤ ((T \ S) ∩ others A j).card)
    (hA : 1-gateMass t A j ≤ gateMass t A j*(((T \ S)ᶜ ∩ A).card:ℝ)) :
    productCompressionLoss (centeredWorld A T j rho t)
        (productResponse (bern t) (centeredWorld A T j rho t)) S
      = (gateMass t A j*(1+(A.card:ℝ))+slopeBval t A j*((others A j).card:ℝ)
          +rho*((T \ S).card:ℝ)-2*gateMass t A j*(((T \ S) ∩ A).card:ℝ)
          -2*slopeBval t A j*(((T \ S) ∩ others A j).card:ℝ))/2 := by
  have hjD : j ∉ T \ S := by
    intro hc
    exact hjT (Finset.mem_sdiff.mp hc).1
  rw [retained_loss t A T S j hjA hB2 rho,
    oscillation t A (T \ S) j hjA hjD rho hG0 hs0 hGr hsr hfire hA]

/-! ## The corner is the `t = 0` instance -/

theorem gateMass_zero (A : Finset (I n)) (j : I n) : gateMass (0:ℝ) A j = 1 := by
  unfold gateMass tailFactor
  simp

theorem slopeBval_zero (A : Finset (I n)) (j : I n) : slopeBval (0:ℝ) A j = 0 := by
  unfold slopeBval
  simp

/-- At `t = 0` the count formula collapses to
`D6SameResponseMarginLoss.actual_loss_formula`. -/
theorem corner_recovers_actual_loss (A T S : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hjT : j ∉ T) (hB2 : 2 ≤ (others A j).card) (rho : ℝ) (hr : 1 ≤ rho)
    (hfire : (∃ i ∈ A, i ∈ T \ S) ∨ 2 ≤ ((T \ S) ∩ others A j).card) :
    productCompressionLoss (centeredWorld A T j rho 0)
        (productResponse (bern 0) (centeredWorld A T j rho 0)) S
      = (1+(A.card:ℝ)+rho*((T \ S).card:ℝ)-2*(((T \ S) ∩ A).card:ℝ))/2 := by
  have hA : 1-gateMass (0:ℝ) A j ≤ gateMass (0:ℝ) A j*((((T \ S))ᶜ ∩ A).card:ℝ) := by
    rw [gateMass_zero]
    have : (0:ℝ) ≤ ((((T \ S))ᶜ ∩ A).card:ℝ) := Nat.cast_nonneg _
    linarith
  rw [retained_loss_formula 0 A T S j hjA hjT hB2 rho
    (by rw [gateMass_zero]; norm_num) (by rw [slopeBval_zero])
    (by rw [gateMass_zero]; linarith) (by rw [slopeBval_zero]; linarith) hfire hA,
    gateMass_zero, slopeBval_zero]
  ring

/-! ## Realizability of every count that the formula uses -/

/-- Every omitted set `D ⊆ T` is `T \ S` for an actual retained set, namely
`S = T \ D`, of size `|T| - |D|`. No count appearing in the loss law is
vacuous. -/
theorem count_realizable (T D : Finset (I n)) (hD : D ⊆ T) :
    T \ (T \ D) = D ∧ (T \ D).card = T.card-D.card := by
  classical
  exact ⟨Finset.sdiff_sdiff_eq_self hD, Finset.card_sdiff_of_subset hD⟩

/-- Every omitted subset has a retained set of the ORIGINAL budget, by
filling from outside T. The older `count_realizable` alone changes the budget. -/
theorem legal_count_realizable (T D : Finset (I n)) (hD : D ⊆ T)
    (hroom : 2*T.card ≤ Fintype.card (I n)) :
    ∃ S : Finset (I n), S.card=T.card ∧ T \ S=D := by
  classical
  have hdcard := Finset.card_le_card hD
  have hDc : D.card ≤ Tᶜ.card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨E,hE,hEc⟩ := (Tᶜ).exists_subset_card_eq hDc
  have hdis : Disjoint (T \ D) E := by
    rw [Finset.disjoint_left]
    intro i hi hiE
    exact (Finset.mem_compl.mp (hE hiE)) (Finset.mem_sdiff.mp hi).1
  refine ⟨(T \ D) ∪ E, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdis,Finset.card_sdiff_of_subset hD,hEc]
    omega
  · ext i
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨hiT,hn⟩
      by_contra hiD
      exact hn (Or.inl ⟨hiT,hiD⟩)
    · intro hiD
      refine ⟨hD hiD,?_⟩
      rintro (⟨_,hn⟩ | hiE)
      · exact hn hiD
      · exact (Finset.mem_compl.mp (hE hiE)) (hD hiD)

/-! ## The splice into the already-proved reduced reference game -/

/-- After symmetry averaging (`|D ∩ A| = h*d/k`, hence `|D ∩ B| = d - h*d/k`)
the regret of the count formula against the complement action is EXACTLY
`D6ReferenceReducedGame.payoff` with `a := gateMass t A j` and
`b := slopeBval t A j`. The `A`-free constant `C` cancels, which is why the
already-proved `primal_equalizer`, `dual_equalizer` and `value` transfer
verbatim; at `t = 0` (`a = 1`, `b = 0`) they give back `k*rho*(2-rho)/4`. -/
theorem count_formula_is_payoff (k h d a b rho C : ℝ) (hk : k ≠ 0) :
    (C+rho*d-2*a*(h*d/k)-2*b*(d-h*d/k))/2-(C+rho*h-2*a*h)/2
      = CIGAMF.P13.D6ReferenceReducedGame.payoff k a b rho h d := by
  unfold CIGAMF.P13.D6ReferenceReducedGame.payoff
  field_simp
  ring

/-- The two reference slopes satisfy the phase law's structural identity
`p + r = 2c` with `p = rho - 2b`, `r = 2a - rho`, `c = a - b`, which is the
hypothesis `denom_eq` of `LeanD6ReferencePhaseValueV1` needs. -/
theorem phase_law_denominator (a b rho : ℝ) :
    (rho-2*b)+(2*a-rho) = 2*(a-b) := by ring

#print axioms retained_coeff_eq
#print axioms retained_residual
#print axioms retained_loss
#print axioms mem_others_iff
#print axioms sdiff_A_eq_inter_others
#print axioms sdiff_inter_eq
#print axioms sum_gateSlope
#print axioms card_split
#print axioms card_compl_split
#print axioms linear_at_hiPoint
#print axioms linear_at_loPoint
#print axioms gate_at_loPoint
#print axioms gate_at_hiPoint
#print axioms hi_value
#print axioms lo_tail_sum
#print axioms lo_value
#print axioms expect_mono
#print axioms offProd_bounds
#print axioms leOne_bounds
#print axioms gateMass_bounds
#print axioms slopeBval_nonneg
#print axioms gate_response_bounds
#print axioms slopeBval_le_one
#print axioms core_le
#print axioms core_ge
#print axioms oscillation
#print axioms retained_loss_formula
#print axioms gateMass_zero
#print axioms slopeBval_zero
#print axioms corner_recovers_actual_loss
#print axioms count_realizable
#print axioms legal_count_realizable
#print axioms count_formula_is_payoff
#print axioms phase_law_denominator

end
end CIGAMF.P13.D6ReferenceRetainedOscillation
