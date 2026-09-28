import «LeanD6ScalarWidthSharpV1»

/-! # R2: the assembly — every legal design is capped by one swap alternative.

`WIDTH_SCALAR_REGION_PROOF.md` ends with a prose step: since every query's
adjacent-swap mixture per unit cost is at most `mu^2/(2q)`, and the B-scalar
design attains `mu^2/(2q)` against every wrong label, the scalar design is
optimal. The two halves were Lean theorems; the step joining them was not. This
file supplies it.

The joining step is an averaging argument, not an optimisation. For a legal
design `(E, w)` with cost mass summing to one:

  * per measurement, the swap mixture is bounded — `scalar_adjacent_mixture_bound`
    for a scalar (unconditionally, with charge 1) and
    `joint_mixture_scalar_bound_sharp` for a joint query (under the sharp charge
    condition `(1-mu)^2 * width <= mu^2 * charge`);
  * multiplying by `w e / charge e` and summing over `E`, then exchanging the two
    finite sums, bounds the TOTAL over the `q(q+1)` adjacent swaps;
  * a sum of `q(q+1)` terms bounded by `q(q+1) * mu^2/(2q)` has a term at most
    `mu^2/(2q)`.

So `exists_swap_capping_design`: for every legal design there EXISTS an adjacent
swap alternative against which that design collects at most `mu^2/(2q)` per unit
cost. Since `uniform_B_lower` shows the B-scalar design collects at least
`mu^2/(2q)` against every wrong label and every nuisance, no design beats the
scalar design on this alternative family.

The `mu >= 1/2` restriction is gone: the sharp charge condition covers `mu < 1/2`
too (see `LeanD6ScalarWidthSharpV1`), so this assembly holds on the whole region.

WHAT THIS DOES NOT ESTABLISH.

- The alternative produced is an ADJACENT SWAP at the true margin (`nu = mu`).
  This caps every design by the swap family; it does not compute the value of the
  full game over all alternatives `(A', nu)`.
- Therefore this is still the UPPER half. It does not prove the scalar design is
  strictly suboptimal when the sharp condition fails — that converse needs a
  lower bound on a mixed design over the two-parameter alternative family and is
  not proved anywhere.
- Scalars are charged `1`. That is the model's convention, supplied as a
  hypothesis (`hscalar`), not derived.
- Nothing here concerns adaptivity, stopping, or the expected-`Gamma` rate.
-/

namespace CIGAMF.P13.D6ScalarOptimalAssembly
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6AllocationMargin
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6QueryWidthInformation
open CIGAMF.P13.D6WidthCostInformation CIGAMF.P13.D6ScalarWidthRegion
open CIGAMF.P13.D6ScalarWidthSharp
noncomputable section
variable {n : ℕ}

/-- Per-measurement swap mixture bound, both constructors at once. -/
theorem measurement_mixture_bound (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 0<q) (hj : j ∉ A) (hA : (A.card:ℝ)=q+1) (hB : ((others A j).card:ℝ)=q)
    (charge width : Measurement n → ℝ) (e : Measurement n) (hch : 0 < charge e)
    (hscalar : ∀ i : I n, charge (.inl i) = 1)
    (hjoint : ∀ G : Finset (I n), ∀ h : Bool, e = .inr (G,h) →
      j ∉ G ∧ (h=false → 2 ≤ G.card) ∧ (G.card:ℝ) ≤ width e ∧
        (1-mu)^2*width e ≤ mu^2*charge e) :
    (∑ a ∈ A, ∑ b ∈ others A j, information A (swapped A a b) j mu mu e)
      ≤ q*(q+1)*charge e*(mu^2/(2*q)) := by
  have hq1 : (0:ℝ) < q*(q+1) := by nlinarith
  match e, hch, hjoint with
  | .inl i, hch, _ =>
      have hc1 : charge (Sum.inl i) = 1 := hscalar i
      have hmix := scalar_adjacent_mixture_bound A j i q mu hq hj hA hB
      have hstep := (div_le_iff₀ hq1).mp hmix
      rw [hc1]
      exact hstep.trans (le_of_eq (by ring))
  | .inr (G,h), hch, hjoint =>
      obtain ⟨hjG, hG, hwidth, hsharp⟩ := hjoint G h rfl
      have hmix := joint_mixture_scalar_bound_sharp A G j h q mu 1 (charge (.inr (G,h)))
        (width (.inr (G,h))) hq one_pos hch hj hA hB hjG hG hwidth (by simpa using hsharp)
      simp only [mul_one, one_mul] at hmix
      have hpos : (0:ℝ) < q*(q+1)*charge (Sum.inr (G,h)) := by positivity
      have hstep := (div_le_iff₀ hpos).mp hmix
      exact hstep.trans (le_of_eq (by ring))

/-- The assembly: one adjacent swap caps the whole design, per unit cost. -/
theorem exists_swap_capping_design (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 0<q) (hj : j ∉ A) (hA : (A.card:ℝ)=q+1) (hB : ((others A j).card:ℝ)=q)
    (E : Finset (Measurement n)) (w charge width : Measurement n → ℝ)
    (hch : ∀ e ∈ E, 0 < charge e)
    (hscalar : ∀ i : I n, charge (.inl i) = 1)
    (hjoint : ∀ e ∈ E, ∀ G : Finset (I n), ∀ h : Bool, e = .inr (G,h) →
      j ∉ G ∧ (h=false → 2 ≤ G.card) ∧ (G.card:ℝ) ≤ width e ∧
        (1-mu)^2*width e ≤ mu^2*charge e)
    (hw : ∀ e ∈ E, 0 ≤ w e) (hnorm : ∑ e ∈ E, w e = 1) :
    ∃ a ∈ A, ∃ b ∈ others A j,
      (∑ e ∈ E, w e*(information A (swapped A a b) j mu mu e/charge e)) ≤ mu^2/(2*q) := by
  classical
  set V : ℝ := mu^2/(2*q) with hV
  set F : I n → I n → Measurement n → ℝ :=
    fun a b e => w e*(information A (swapped A a b) j mu mu e/charge e) with hF
  have hper : ∀ e ∈ E, (∑ a ∈ A, ∑ b ∈ others A j, F a b e) ≤ w e*(q*(q+1)*V) := by
    intro e he
    have hce : 0 < charge e := hch e he
    have hb := measurement_mixture_bound A j q mu hq hj hA hB charge width e hce
      hscalar (fun G h hEq => hjoint e he G h hEq)
    have hfac : (∑ a ∈ A, ∑ b ∈ others A j, F a b e)
        = (w e/charge e)*(∑ a ∈ A, ∑ b ∈ others A j,
            information A (swapped A a b) j mu mu e) := by
      rw [Finset.mul_sum]
      refine sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
      exact sum_congr rfl (fun b _ => by simp only [hF]; field_simp)
    rw [hfac]
    have hmul := mul_le_mul_of_nonneg_left hb (div_nonneg (hw e he) hce.le)
    refine hmul.trans (le_of_eq ?_)
    rw [hV]
    field_simp
  have hswap : (∑ a ∈ A, ∑ b ∈ others A j, ∑ e ∈ E, F a b e)
      = ∑ e ∈ E, ∑ a ∈ A, ∑ b ∈ others A j, F a b e := by
    rw [sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
  have htot : (∑ a ∈ A, ∑ b ∈ others A j, ∑ e ∈ E, F a b e) ≤ q*(q+1)*V := by
    rw [hswap]
    have hsum := Finset.sum_le_sum hper
    rw [← Finset.sum_mul, hnorm, one_mul] at hsum
    exact hsum
  by_contra hcon
  push_neg at hcon
  have hA0 : A.Nonempty := by
    rw [← Finset.card_pos]
    have h : (0:ℝ) < (A.card:ℝ) := by rw [hA]; linarith
    exact_mod_cast h
  have hB0 : (others A j).Nonempty := by
    rw [← Finset.card_pos]
    have h : (0:ℝ) < ((others A j).card:ℝ) := by rw [hB]; linarith
    exact_mod_cast h
  have hinner : ∀ a ∈ A, q*V < ∑ b ∈ others A j, ∑ e ∈ E, F a b e := by
    intro a ha
    have hlt := Finset.sum_lt_sum_of_nonempty hB0 (fun b hb => hcon a ha b hb)
    rw [Finset.sum_const, nsmul_eq_mul, hB] at hlt
    exact hlt
  have hout := Finset.sum_lt_sum_of_nonempty hA0 hinner
  rw [Finset.sum_const, nsmul_eq_mul, hA] at hout
  have : q*(q+1)*V < ∑ a ∈ A, ∑ b ∈ others A j, ∑ e ∈ E, F a b e := by
    refine lt_of_le_of_lt (le_of_eq ?_) hout
    ring
  linarith

#print axioms measurement_mixture_bound
#print axioms exists_swap_capping_design

end
end CIGAMF.P13.D6ScalarOptimalAssembly
