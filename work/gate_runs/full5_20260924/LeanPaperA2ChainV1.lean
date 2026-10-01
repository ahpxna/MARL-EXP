import «LeanPaperA7TailV1»
import «LeanPaperARPairV1»

/-!
# Paper A, the A2 chain: cumulative exploration, with the two missing links

The `Omega(log^2(1/alpha))` claim was never a consequence of
`J_true(w*_proxy) = 0`: an algorithm may add linear exploration, or an approximate oracle
may hand mass to cells the surrogate ignores, and the rate turns on exactly that.  The
honest object is a law in the CUMULATIVE EXPLORATION, with `log^2` as the corollary at
exponent `a = 1/2`.

Four links are needed.  Two were already in the corpus:

  * **Step 1**, a neighbourhood of the true world on which every proxy optimum has the
    same extrema and the same starved support --- `starvation_on_a_neighbourhood` and
    `starvation_neighbourhood_nonvacuous` in `LeanPaperARPairV1`;
  * **Step 4**, the accounting that telescopes the movable-cell count into
    `#bad rounds + sum (rho_s + eps_s)` --- `movable_count_accounting` in
    `LeanPaperA7TailV1`.

This module adds the other two and assembles them.

  * **Step 2**: a summable per-round failure mass bounds the expected number of rounds on
    which the estimate leaves that neighbourhood, uniformly in the horizon.
  * **Step 3**: an oracle that is only `eps`-optimal FOR THE SURROGATE leaves at most
    `eps/kappa` of its mass off the surrogate's own support --- so the mass available to
    the true alternatives is `O(eps)` and not merely "some".

The assembly gives `N_mov(t) <= C_r + 2 sqrt t + epsBar * t`.  The exponent Jensen then
inverts is `a = 1/2` exactly while the square-root term dominates, and `a = 1` after the
linear term takes over; the crossover is at `t = (2/epsBar)^2`.  At the measured leakage
that is past `1.5e13` rounds, so on any horizon this experiment runs the exponent is
`1/2` and the corollary is `Omega(log^2(1/alpha))`.  That is a statement about the
schedule, not an assumption about it.
-/

namespace CIGAMF.P13.PaperA2Chain

open Finset
open CIGAMF.P13.PaperA7Tail
open CIGAMF.P13.PaperARPair

/-! ## Step 2: the estimate leaves the neighbourhood on boundedly many rounds -/

/-- A telescoping bound for the inverse-square tail. -/
theorem inv_sq_shift_sum_le (t : ℕ) :
    ∑ s ∈ Finset.range t, 1 / ((s : ℝ) + 2) ^ 2 ≤ 1 := by
  have key : ∀ s : ℕ, 1 / ((s : ℝ) + 2) ^ 2 ≤ 1 / ((s : ℝ) + 1) - 1 / ((s : ℝ) + 2) := by
    intro s
    have h1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
    have heq : 1 / ((s : ℝ) + 1) - 1 / ((s : ℝ) + 2)
        = 1 / (((s : ℝ) + 1) * ((s : ℝ) + 2)) := by
      field_simp
      ring
    rw [heq]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hstep : ∑ s ∈ Finset.range t, (1 / ((s : ℝ) + 1) - 1 / ((s : ℝ) + 2))
      = 1 - 1 / ((t : ℝ) + 1) := by
    induction t with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        field_simp
        ring
  calc ∑ s ∈ Finset.range t, 1 / ((s : ℝ) + 2) ^ 2
      ≤ ∑ s ∈ Finset.range t, (1 / ((s : ℝ) + 1) - 1 / ((s : ℝ) + 2)) :=
        Finset.sum_le_sum (fun s _ => key s)
    _ = 1 - 1 / ((t : ℝ) + 1) := hstep
    _ ≤ 1 := by
        have hpos : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
        linarith

/-- **Step 2.**  If the per-round probability of leaving the good neighbourhood decays at
the inverse-square rate the confidence sequence already supplies, the expected number of
such rounds is bounded by a constant, uniformly in the horizon.  This is the `C_r` of the
cumulative law, and it does not grow with `t`. -/
theorem expected_bad_rounds_bounded (bad : ℕ → ℝ) (hbad0 : 0 ≤ bad 0) (hbad1 : 0 ≤ bad 1)
    (hrate : ∀ s, bad (s + 2) ≤ 1 / ((s : ℝ) + 2) ^ 2) (t : ℕ) :
    ∑ s ∈ Finset.range t, bad s ≤ bad 0 + bad 1 + 1 := by
  rcases Nat.lt_or_ge t 2 with h | h
  · interval_cases t
    · simp; linarith
    · simp; linarith
  · obtain ⟨k, rfl⟩ : ∃ k, t = 2 + k := ⟨t - 2, by omega⟩
    have hsplit : ∑ s ∈ Finset.range (2 + k), bad s
        = (∑ s ∈ Finset.range 2, bad s) + ∑ i ∈ Finset.range k, bad (2 + i) :=
      Finset.sum_range_add _ 2 k
    have htwo : ∑ s ∈ Finset.range 2, bad s = bad 0 + bad 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
    have htail : ∑ i ∈ Finset.range k, bad (2 + i)
        ≤ ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 2) ^ 2 := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      have := hrate i
      rwa [add_comm 2 i]
    have hone : ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 2) ^ 2 ≤ 1 := inv_sq_shift_sum_le k
    rw [hsplit, htwo]
    linarith

/-! ## Step 3: an `eps`-optimal design for the WRONG objective leaks only `O(eps)` -/

variable {r : ℕ}

/-- A quantitative `AnchorMonotone`: sweeping the pair mass onto an anchor gains at least
`kappa` per unit of pair mass.  `AnchorMonotone` alone gives a strict inequality with no
modulus, which cannot turn near-optimality into a mass bound. -/
def AnchorGain (Jp : (Cell r → ℝ) → ℝ) (κ : ℝ) : Prop :=
  ∀ w : Cell r → ℝ, IsAlloc w →
    κ * (∑ p : Fin r × Bool, w (Sum.inr p)) ≤ Jp (sweepToAnchor w) - Jp w

/-- **Step 3.**  A design that is within `eps` of the surrogate's optimum carries at most
`eps/kappa` of mass off the anchors.  So an approximate oracle for the wrong objective
does not accidentally rescue the true task: the mass it leaves where the true
alternatives live is `O(eps)`, with an explicit constant. -/
theorem offsupport_mass_le (Jp : (Cell r → ℝ) → ℝ) (κ ε : ℝ)
    (hgain : AnchorGain Jp κ) (w : Cell r → ℝ) (hw : IsAlloc w)
    (hsub : ∀ w', IsAlloc w' → Jp w' ≤ Jp w + ε) :
    κ * (∑ p : Fin r × Bool, w (Sum.inr p)) ≤ ε := by
  have h1 := hgain w hw
  have h2 := hsub (sweepToAnchor w) (sweepToAnchor_isAlloc w hw)
  linarith

/-- `AnchorGain` is satisfiable, so Step 3 is not vacuous: total anchor mass has gain
exactly one, and it is `AnchorOnly` and `AnchorMonotone` as well. -/
theorem anchorTotal_gain :
    AnchorGain (r := r) (fun w => ∑ i : Fin 4, w (Sum.inl i)) 1 := by
  intro w hw
  have hsweep : ∑ i : Fin 4, sweepToAnchor w (Sum.inl i)
      = (∑ i : Fin 4, w (Sum.inl i)) + ∑ p : Fin r × Bool, w (Sum.inr p) := by
    unfold sweepToAnchor
    simp only [Sum.elim_inl]
    rw [Fin.sum_cons]
    rw [show (∑ i : Fin 4, w (Sum.inl i))
        = w (Sum.inl 0) + ∑ i : Fin 3, w (Sum.inl i.succ) from Fin.sum_univ_succ _]
    ring
  show (1 : ℝ) * (∑ p : Fin r × Bool, w (Sum.inr p))
      ≤ (∑ i : Fin 4, sweepToAnchor w (Sum.inl i)) - ∑ i : Fin 4, w (Sum.inl i)
  rw [hsweep]
  linarith

/-! ## The assembly -/

/-- **The cumulative-exploration law.**  Steps 2, 3 and 4 combined: the movable-cell count
is a constant, plus the forced exploration's own `2 sqrt t`, plus the oracle's leakage
`epsBar` per round. -/
theorem cumulative_exploration_bound (Nmov bad rho eps : ℕ → ℝ) (epsBar Cr : ℝ)
    (h0 : Nmov 0 = 0)
    (hstep : ∀ s, Nmov (s + 1) - Nmov s ≤ bad s + rho s + eps s)
    (hbad : ∀ t, ∑ s ∈ Finset.range t, bad s ≤ Cr)
    (hrho : ∀ s, rho s = 1 / Real.sqrt (s + 1))
    (heps : ∀ s, eps s ≤ epsBar) (t : ℕ) :
    Nmov t ≤ Cr + 2 * Real.sqrt t + epsBar * (t : ℝ) := by
  have hacc := movable_count_accounting Nmov bad rho eps h0 hstep t
  have hsplit : ∑ s ∈ Finset.range t, (bad s + rho s + eps s)
      = (∑ s ∈ Finset.range t, bad s) + (∑ s ∈ Finset.range t, rho s)
        + ∑ s ∈ Finset.range t, eps s := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hr : ∑ s ∈ Finset.range t, rho s ≤ 2 * Real.sqrt t := by
    have hcongr : ∑ s ∈ Finset.range t, rho s
        = ∑ s ∈ Finset.range t, 1 / Real.sqrt ((s : ℝ) + 1) :=
      Finset.sum_congr rfl (fun s _ => hrho s)
    rw [hcongr]
    exact sum_inv_sqrt_le t
  have he : ∑ s ∈ Finset.range t, eps s ≤ epsBar * (t : ℝ) := by
    calc ∑ s ∈ Finset.range t, eps s ≤ ∑ _s ∈ Finset.range t, epsBar :=
          Finset.sum_le_sum (fun s _ => heps s)
      _ = epsBar * (t : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  rw [hsplit] at hacc
  linarith [hbad t]

/-- **Where the exponent changes.**  While `epsBar * t <= 2 sqrt t` the square-root term
dominates and the Jensen inversion runs at `a = 1/2`, giving `Omega(log^2(1/alpha))`;
beyond it the linear term takes over and only `Omega(log(1/alpha))` follows. -/
theorem sqrt_dominates_until (epsBar t : ℝ) (hε : 0 < epsBar) (ht : 0 ≤ t)
    (hle : t ≤ (2 / epsBar) ^ 2) : epsBar * t ≤ 2 * Real.sqrt t := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h]; simp
  · have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr h
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
    have hd : (0 : ℝ) < 2 / epsBar := by positivity
    have hb : Real.sqrt t ≤ 2 / epsBar := by
      nlinarith [hs.le, hd.le, hsq, hle]
    have h3 : epsBar * Real.sqrt t ≤ 2 := by
      rw [le_div_iff₀ hε] at hb
      linarith
    have hmul : epsBar * Real.sqrt t * Real.sqrt t = epsBar * t := by
      rw [mul_assoc, ← pow_two, hsq]
    calc epsBar * t = epsBar * Real.sqrt t * Real.sqrt t := hmul.symm
      _ ≤ 2 * Real.sqrt t := mul_le_mul_of_nonneg_right h3 hs.le

/-- At the leakage measured after the bracket was corrected, `epsBar = 5.043e-7`, the
crossover sits past `1.5e13` rounds --- far outside any horizon run here, so the operating
exponent is `a = 1/2`. -/
theorem measured_crossover_is_far :
    (15000000000000 : ℝ) ≤ (2 / ((5043 : ℝ) / 10000000000)) ^ 2 := by
  norm_num

/-! ## Audit -/

#print axioms inv_sq_shift_sum_le
#print axioms expected_bad_rounds_bounded
#print axioms offsupport_mass_le
#print axioms anchorTotal_gain
#print axioms cumulative_exploration_bound
#print axioms sqrt_dominates_until
#print axioms measured_crossover_is_far

end CIGAMF.P13.PaperA2Chain
