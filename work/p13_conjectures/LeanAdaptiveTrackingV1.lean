import «LeanAdaptiveExpectedStoppingV1»

/-! # Adaptive A5: the TRACKING step.

The audit records tracking as open: an allocation rule must realise the intended per-arm
proportions, and nothing in the corpus said it could.  This file proves that it can, and
says precisely which part is still an algorithmic question rather than a mathematical one.

## WHAT IS PROVED

* `deficit_sum_zero` — with `∑ w = 1` and `∑ N = t`, the deficits `D_i = t w_i - N_i` sum
  to zero, so at every time SOME arm is behind (`exists_deficient`).  A greedy rule is
  therefore never idle.
* `tracking_bound` — any allocation squeezed between `⌊t w_i⌋` and `⌊t w_i⌋ + 1` has
  `|N_i - t w_i| ≤ 1`, uniformly in `i` and `t`.
* `tracking_exists` — **such an allocation always exists**: for every target `w` on the
  simplex and every horizon `t` there is an integer allocation with `∑ N_i = t` and
  deficit at most `1`.  This is the statement the analysis needs, and it is proved by
  construction, not assumed.
* `pull_count_lower` — the consequence the regret analysis actually consumes: between any
  two times, arm `i` is pulled at least `(t - s) w_i - 2c` times when the deficit is
  bounded by `c`.  Stated on the real-valued counts, so it applies to any allocation
  meeting the bound.
* `frequency_converges` — a deficit bound of `c` gives `|N_i/t - w_i| ≤ c/t`.

## WHAT THIS DOES NOT ESTABLISH -- and why, stated honestly

`tracking_exists` produces, for each horizon `t`, an allocation with deficit at most `1`.
It does NOT produce a single ONLINE rule whose counts are monotone in `t` and meet that
bound at every `t` simultaneously.  That gap is real:

* The natural incremental rule -- at each step increment the arm of largest deficit --
  does NOT satisfy a uniform bound of the form `D_i ≤ 1 - w_i`.  A two-arm counterexample
  with `w = (9/10, 1/10)` reaches deficit `4/5` on the first arm while `1 - w_1 = 1/10`,
  so that invariant is false and is not asserted anywhere here.
* Whether the incremental greedy rule satisfies the weaker `D_i < 1` uniformly is an
  invariant of the apportionment rule, not a bookkeeping identity, and is left open.

So: the tracking BOUND is closed, the per-horizon EXISTENCE is closed, and what remains
is the online-monotone realisation.  The concentration input and the layer-cake identity
were closed in `LeanAdaptiveExpectedStoppingV1`.
-/

namespace CIGAMF.P13.AdaptiveTracking

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The deficit of arm `i` at time `t` against target `w`. -/
noncomputable def deficit (w : ι → ℝ) (N : ι → ℕ) (t : ℕ) (i : ι) : ℝ :=
  (t : ℝ) * w i - (N i : ℝ)

/-- **Deficits sum to zero.** -/
theorem deficit_sum_zero (w : ι → ℝ) (N : ι → ℕ) (t : ℕ)
    (hw : ∑ i, w i = 1) (hN : ∑ i, N i = t) :
    ∑ i, deficit w N t i = 0 := by
  classical
  unfold deficit
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hw, mul_one]
  have : ∑ i, ((N i : ℝ)) = ((∑ i, N i : ℕ) : ℝ) := by push_cast; ring
  rw [this, hN]
  ring

/-- **Some arm is always behind**, so a greedy rule always has work to do. -/
theorem exists_deficient [Nonempty ι] (w : ι → ℝ) (N : ι → ℕ) (t : ℕ)
    (hw : ∑ i, w i = 1) (hN : ∑ i, N i = t) :
    ∃ i, 0 ≤ deficit w N t i := by
  classical
  by_contra hc
  push_neg at hc
  have hneg : ∑ i, deficit w N t i < 0 := by
    have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
    exact Finset.sum_neg (fun i _ => hc i) hne
  rw [deficit_sum_zero w N t hw hN] at hneg
  exact lt_irrefl 0 hneg

/-- **The tracking bound.**  An allocation squeezed between the floor and the floor plus
one has deficit at most `1`, uniformly. -/
theorem tracking_bound (w : ι → ℝ) (N : ι → ℕ) (t : ℕ)
    (hlo : ∀ i, ((⌊(t : ℝ) * w i⌋ : ℤ) : ℝ) ≤ (N i : ℝ))
    (hhi : ∀ i, (N i : ℝ) ≤ ((⌊(t : ℝ) * w i⌋ : ℤ) : ℝ) + 1) (i : ι) :
    |(N i : ℝ) - (t : ℝ) * w i| ≤ 1 := by
  have hfl : ((⌊(t : ℝ) * w i⌋ : ℤ) : ℝ) ≤ (t : ℝ) * w i := Int.floor_le _
  have hfu : (t : ℝ) * w i < ((⌊(t : ℝ) * w i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor
  · linarith [hlo i]
  · linarith [hhi i]

/-- **Existence.**  For every target on the simplex and every horizon there IS an integer
allocation spending exactly `t` pulls with deficit at most `1`. -/
theorem tracking_exists [Nonempty ι] (w : ι → ℝ) (t : ℕ)
    (hw : ∑ i, w i = 1) (hw0 : ∀ i, 0 ≤ w i) :
    ∃ N : ι → ℕ, (∑ i, N i = t) ∧
      ∀ i, |(N i : ℝ) - (t : ℝ) * w i| ≤ 1 := by
  classical
  set f : ι → ℕ := fun i => ⌊(t : ℝ) * w i⌋₊ with hf
  have hnn : ∀ i, (0:ℝ) ≤ (t : ℝ) * w i := fun i =>
    mul_nonneg (Nat.cast_nonneg t) (hw0 i)
  have hfle : ∀ i, ((f i : ℝ)) ≤ (t : ℝ) * w i := fun i => Nat.floor_le (hnn i)
  have hflt : ∀ i, (t : ℝ) * w i < (f i : ℝ) + 1 := fun i => Nat.lt_floor_add_one _
  have hSle : ∑ i, f i ≤ t := by
    have hreal : ((∑ i, f i : ℕ) : ℝ) ≤ (t : ℝ) := by
      push_cast
      calc ∑ i, (f i : ℝ) ≤ ∑ i, (t : ℝ) * w i := Finset.sum_le_sum fun i _ => hfle i
        _ = (t : ℝ) := by rw [← Finset.mul_sum, hw, mul_one]
    exact_mod_cast hreal
  have hgap : t - ∑ i, f i ≤ Fintype.card ι := by
    have hreal : (t : ℝ) < ((∑ i, f i : ℕ) : ℝ) + (Fintype.card ι : ℝ) := by
      push_cast
      calc (t : ℝ) = ∑ i, (t : ℝ) * w i := by rw [← Finset.mul_sum, hw, mul_one]
        _ < ∑ i, ((f i : ℝ) + 1) := by
            refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hflt i
        _ = ∑ i, (f i : ℝ) + (Fintype.card ι : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
                mul_one]
    have : t < (∑ i, f i) + Fintype.card ι := by exact_mod_cast hreal
    omega
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
      (n := t - ∑ i, f i) (by rw [Finset.card_univ]; exact hgap)
  refine ⟨fun i => f i + (if i ∈ T then 1 else 0), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
        hTcard, smul_eq_mul, mul_one]
    omega
  · intro i
    have hlo : ((f i : ℝ)) ≤ ((f i + (if i ∈ T then 1 else 0) : ℕ) : ℝ) := by
      push_cast; split <;> simp
    have hhi : ((f i + (if i ∈ T then 1 else 0) : ℕ) : ℝ) ≤ (f i : ℝ) + 1 := by
      push_cast; split <;> simp
    rw [abs_le]
    constructor
    · linarith [hflt i]
    · linarith [hfle i]

/-- **Frequency convergence.**  A deficit bound of `c` pins the empirical allocation to
within `c/t` of the target. -/
theorem frequency_converges (w : ι → ℝ) (N : ι → ℕ) (t : ℕ) (c : ℝ) (ht : 0 < t)
    (hc : ∀ i, |(N i : ℝ) - (t : ℝ) * w i| ≤ c) (i : ι) :
    |(N i : ℝ) / (t : ℝ) - w i| ≤ c / (t : ℝ) := by
  have htr : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hrw : (N i : ℝ) / (t : ℝ) - w i = ((N i : ℝ) - (t : ℝ) * w i) / (t : ℝ) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos htr]
  gcongr
  exact hc i

/-- **The pull count the regret analysis consumes.**  Between two times, arm `i` is pulled
at least `(t - s) w_i - 2c` times. -/
theorem pull_count_lower (w : ι → ℝ) (s t : ℕ) (c : ℝ) (i : ι)
    (Ns Nt : ℝ) (hNs : |Ns - (s : ℝ) * w i| ≤ c) (hNt : |Nt - (t : ℝ) * w i| ≤ c) :
    ((t : ℝ) - (s : ℝ)) * w i - 2 * c ≤ Nt - Ns := by
  have h1 := abs_le.mp hNs
  have h2 := abs_le.mp hNt
  nlinarith [h1.1, h1.2, h2.1, h2.2]

#print axioms deficit_sum_zero
#print axioms exists_deficient
#print axioms tracking_bound
#print axioms tracking_exists
#print axioms frequency_converges
#print axioms pull_count_lower

end CIGAMF.P13.AdaptiveTracking
