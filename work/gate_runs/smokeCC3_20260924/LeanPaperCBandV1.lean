import «LeanPaperCBreakpointV1»

/-!
# Paper C: the marginal band, discharged from the constraint the paper actually imposes

`O2_strict_odd` and `O2_strict_even` of `LeanPaperCBreakpointV1` each take an aggregate
band bound as a hypothesis.  This module derives both from Paper C's own constraint.

TWO CORRECTIONS TO AN EARLIER VERSION OF THIS FILE, BOTH MATERIAL.

*The constraint is the RETAINED-PREFIX band, not a position band.*  Paper C imposes

    |Pr(i in prefix_k) - k/m| <= eta/m   for every item i and every budget k,

which is not equivalent to a position band of the same width once `eta > 0`.  The endpoint
probabilities are recovered from it rather than assumed:

    Pr(pi_1 = i) = Pr(i in prefix_1)                  >= (1 - eta)/m,
    Pr(pi_m = i) = 1 - Pr(i in prefix_{m-1})          >= (1 - eta)/m,

the second because the band's UPPER side at `k = m-1` gives `<= (m-1)/m + eta/m`.

*The four heavy-endpoint events are NOT mutually exclusive.*  Both heavy items can sit at
the two ends of the same ranking, so `big` reaches `2` and an exclusivity argument is
simply false there.  It is also unnecessary: `big` is by definition the SUM of the four
indicators, and expectation is additive, so the four lower bounds add with no disjointness
at all.  Exclusivity is still used on the odd side, where it is true: one item occupies the
last position.
-/

namespace CIGAMF.P13.PaperCBand

open Finset
open CIGAMF.P13.PaperCBreakpoint

/-! ## The prefix band, and the endpoint probabilities it forces -/

/-- **The first position is the budget-one prefix.**  Lower side of the band at `k = 1`. -/
theorem first_position_lower {R : Type*} [Fintype R] (P : R → ℝ) (inPrefix first : R → ℝ)
    (m η : ℝ) (hm : 0 < m)
    (hfirst : ∀ x, first x = inPrefix x)
    (hband : 1 / m - η / m ≤ ∑ x, P x * inPrefix x) :
    (1 - η) / m ≤ ∑ x, P x * first x := by
  have hrw : ∑ x, P x * first x = ∑ x, P x * inPrefix x :=
    Finset.sum_congr rfl fun x _ => by rw [hfirst x]
  have hid : (1 - η) / m = 1 / m - η / m := by ring
  rw [hrw, hid]
  exact hband

/-- **The last position is the complement of the budget-`(m-1)` prefix.**  This uses the
UPPER side of the band, which is why a one-sided band would not do. -/
theorem last_position_lower {R : Type*} [Fintype R] (P : R → ℝ) (inPrefix last : R → ℝ)
    (m η : ℝ) (hm : 0 < m)
    (hsum : ∑ x, P x = 1)
    (hlast : ∀ x, last x = 1 - inPrefix x)
    (hband : ∑ x, P x * inPrefix x ≤ (m - 1) / m + η / m) :
    (1 - η) / m ≤ ∑ x, P x * last x := by
  have hrw : ∑ x, P x * last x = (∑ x, P x) - ∑ x, P x * inPrefix x := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [hlast x]; ring
  rw [hrw, hsum]
  have hid : (m - 1) / m = 1 - 1 / m := by field_simp
  have : (1 - η) / m = 1 - ((m - 1) / m + η / m) := by
    rw [hid]
    field_simp
    ring
  rw [this]
  linarith

/-! ## Summing the band over items -/

/-- Summing a per-item lower bound over a set of items. -/
theorem band_sum_lower {R I : Type*} [Fintype R] (P : R → ℝ) (occ : I → R → ℝ)
    (S : Finset I) (c lo : ℝ)
    (hband : ∀ i ∈ S, lo ≤ ∑ x, P x * occ i x)
    (hcard : (S.card : ℝ) = c) :
    c * lo ≤ ∑ i ∈ S, ∑ x, P x * occ i x := by
  have h := Finset.sum_le_sum hband
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at h
  exact h

theorem band_aggregate {R I : Type*} [Fintype R] (P : R → ℝ) (hP : ∀ x, 0 ≤ P x)
    (occ : I → R → ℝ) (agg : R → ℝ) (S : Finset I) (c lo : ℝ)
    (hband : ∀ i ∈ S, lo ≤ ∑ x, P x * occ i x)
    (hcard : (S.card : ℝ) = c)
    (hdom : ∀ x, ∑ i ∈ S, occ i x ≤ agg x) :
    c * lo ≤ ∑ x, P x * agg x := by
  classical
  have hswap : ∑ i ∈ S, ∑ x, P x * occ i x = ∑ x, P x * ∑ i ∈ S, occ i x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
  have hmono : ∑ x, P x * ∑ i ∈ S, occ i x ≤ ∑ x, P x * agg x :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hdom x) (hP x)
  have hlow := band_sum_lower P occ S c lo hband hcard
  rw [hswap] at hlow
  linarith

/-- Exactly one item occupies a given position, so those indicators ARE exclusive.  Used
on the odd side only. -/
theorem exclusive_sum_le {R I : Type*} [DecidableEq I] (occ : I → R → ℝ) (agg : R → ℝ)
    (S : Finset I) (sel : R → I)
    (hocc : ∀ i x, occ i x = if i = sel x then 1 else 0)
    (hagg : ∀ x, (if sel x ∈ S then (1 : ℝ) else 0) ≤ agg x) :
    ∀ x, ∑ i ∈ S, occ i x ≤ agg x := by
  intro x
  have h : ∑ i ∈ S, occ i x = if sel x ∈ S then (1 : ℝ) else 0 := by
    rw [Finset.sum_congr rfl fun i _ => hocc i x]
    exact Finset.sum_ite_eq' S (sel x) (fun _ => (1 : ℝ))
  rw [h]
  exact hagg x

/-! ## The two aggregate hypotheses (O2) consumes -/

/-- **The odd side.**  `(m-1)/2` positive items, each at the last position with probability
at least `(1-eta)/m`, and only one of them can be there. -/
theorem hband_odd_of_prefix_band {R I : Type*} [Fintype R] [DecidableEq I]
    (P : R → ℝ) (hP : ∀ x, 0 ≤ P x) (occ : I → R → ℝ) (lastPos : R → ℝ)
    (pos : Finset I) (lastItem : R → I) (m η : ℝ) (hm : 0 < m)
    (hocc : ∀ i x, occ i x = if i = lastItem x then 1 else 0)
    (hlastPos : ∀ x, (if lastItem x ∈ pos then (1 : ℝ) else 0) ≤ lastPos x)
    (hcard : (pos.card : ℝ) = (m - 1) / 2)
    (hitem : ∀ i ∈ pos, (1 - η) / m ≤ ∑ x, P x * occ i x) :
    (m - 1) * (1 - η) / (2 * m) ≤ ∑ x, P x * lastPos x := by
  have hdom := exclusive_sum_le occ lastPos pos lastItem hocc hlastPos
  have h := band_aggregate P hP occ lastPos pos ((m - 1) / 2) ((1 - η) / m)
    hitem hcard hdom
  have hid : (m - 1) / 2 * ((1 - η) / m) = (m - 1) * (1 - η) / (2 * m) := by
    field_simp
  rwa [hid] at h

/-- **The even side, with no exclusivity claim.**  `big` is BY DEFINITION the sum of the
four endpoint indicators of the two heavy items, and it does reach `2` when both sit at the
ends.  Expectation is additive, so the four bounds add. -/
theorem hband_even_of_endpoint_band {R I : Type*} [Fintype R]
    (P : R → ℝ) (first last : I → R → ℝ) (big : R → ℝ)
    (heavy : Finset I) (m η : ℝ) (hm : 0 < m)
    (hcard : (heavy.card : ℝ) = 2)
    (hbig : ∀ x, big x = ∑ i ∈ heavy, (first i x + last i x))
    (hfirst : ∀ i ∈ heavy, (1 - η) / m ≤ ∑ x, P x * first i x)
    (hlast : ∀ i ∈ heavy, (1 - η) / m ≤ ∑ x, P x * last i x) :
    4 * (1 - η) / m ≤ ∑ x, P x * big x := by
  classical
  have hexpand : ∑ x, P x * big x
      = ∑ i ∈ heavy, ((∑ x, P x * first i x) + ∑ x, P x * last i x) := by
    have h1 : ∑ x, P x * big x = ∑ x, ∑ i ∈ heavy, P x * (first i x + last i x) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hbig x, Finset.mul_sum]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hterm : ∀ i ∈ heavy,
      2 * ((1 - η) / m) ≤ (∑ x, P x * first i x) + ∑ x, P x * last i x := by
    intro i hi
    have := hfirst i hi
    have := hlast i hi
    linarith [hfirst i hi, hlast i hi]
  have h := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at h
  rw [hexpand]
  have hid : (2 : ℝ) * (2 * ((1 - η) / m)) = 4 * (1 - η) / m := by ring
  linarith [h, hid.le, hid.ge]

/-! ## (O2), with the band discharged -/

theorem O2_odd_from_prefix_band {R I : Type*} [Fintype R] [DecidableEq I]
    (P tot lastPos : R → ℝ) (occ : I → R → ℝ) (pos : Finset I) (lastItem : R → I)
    (m η D : ℝ) (hm : 1 < m) (hD : 0 < D)
    (hineq : ∀ x, 2 + 2 * lastPos x ≤ tot x)
    (hPpos : ∀ x, 0 ≤ P x) (hsum : ∑ x, P x = 1)
    (hocc : ∀ i x, occ i x = if i = lastItem x then 1 else 0)
    (hlastPos : ∀ x, (if lastItem x ∈ pos then (1 : ℝ) else 0) ≤ lastPos x)
    (hcard : (pos.card : ℝ) = (m - 1) / 2)
    (hitem : ∀ i ∈ pos, (1 - η) / m ≤ ∑ x, P x * occ i x) :
    2 / (D * (m - 1)) + (1 - η) / (D * m)
      ≤ (∑ x, P x * tot x) / (D * (m - 1)) :=
  O2_strict_odd P tot lastPos m η D hm hD hineq hPpos hsum
    (hband_odd_of_prefix_band P hPpos occ lastPos pos lastItem m η (by linarith)
      hocc hlastPos hcard hitem)

theorem O2_even_from_endpoint_band {R I : Type*} [Fintype R]
    (P r1 rm big : R → ℝ) (first last : I → R → ℝ) (heavy : Finset I)
    (m D η : ℝ) (hm : 2 < m) (hD : 0 < D)
    (hη : η < (m - 2) / (2 * (m - 1)))
    (hid : ∀ x, r1 x + rm x = 2 / D * big x)
    (hcard : (heavy.card : ℝ) = 2)
    (hbig : ∀ x, big x = ∑ i ∈ heavy, (first i x + last i x))
    (hfirst : ∀ i ∈ heavy, (1 - η) / m ≤ ∑ x, P x * first i x)
    (hlast : ∀ i ∈ heavy, (1 - η) / m ≤ ∑ x, P x * last i x) :
    2 / (D * (m - 1)) < (∑ x, P x * (r1 x + rm x)) / 2 :=
  O2_strict_even P r1 rm big m D η hm hD hη hid
    (hband_even_of_endpoint_band P first last big heavy m η (by linarith)
      hcard hbig hfirst hlast)

/-! ## The band's lower side is satisfiable -/

theorem uniform_item_band {I : Type*} [Fintype I] [DecidableEq I] (m η : ℝ)
    (hm : 0 < m) (hη : 0 ≤ η) (sel : I → I) (hsel : Function.Bijective sel)
    (hcard : (Fintype.card I : ℝ) = m) :
    ∀ i : I, (1 - η) / m ≤ ∑ x : I, (1 / m) * (if i = sel x then (1 : ℝ) else 0) := by
  classical
  intro i
  obtain ⟨x₀, hx₀⟩ := hsel.surjective i
  have hone : ∑ x : I, (1 / m) * (if i = sel x then (1 : ℝ) else 0) = 1 / m := by
    have hterm : ∀ x : I, (1 / m) * (if i = sel x then (1 : ℝ) else 0)
        = if x = x₀ then 1 / m else 0 := by
      intro x
      by_cases hx : x = x₀
      · subst hx
        rw [if_pos hx₀.symm, if_pos rfl, mul_one]
      · have hne : i ≠ sel x := by
          intro h
          exact hx (hsel.injective (by rw [← h, hx₀]))
        rw [if_neg hne, if_neg hx, mul_zero]
    rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_ite_eq' Finset.univ x₀
      (fun _ => 1 / m), if_pos (Finset.mem_univ x₀)]
  rw [hone]
  have hη1 : (1 : ℝ) - η ≤ 1 := by linarith
  exact div_le_div_of_nonneg_right hη1 hm.le

/-! ## Audit -/

#print axioms first_position_lower
#print axioms last_position_lower
#print axioms band_sum_lower
#print axioms band_aggregate
#print axioms exclusive_sum_le
#print axioms hband_odd_of_prefix_band
#print axioms hband_even_of_endpoint_band
#print axioms O2_odd_from_prefix_band
#print axioms O2_even_from_endpoint_band
#print axioms uniform_item_band

end CIGAMF.P13.PaperCBand
