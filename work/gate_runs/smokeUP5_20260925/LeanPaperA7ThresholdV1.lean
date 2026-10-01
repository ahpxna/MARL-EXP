import «LeanPaperA7ChainV1»
import «LeanPaperA7TrackingV1»

/-!
# Paper A: the code's threshold really is unbounded, and the chain survives it

`a7_chain_rate` assumes

    hthr : forall alpha omega n,  thr_n(alpha) <= log(1/alpha) + s(alpha),

a threshold bounded uniformly in `n`.  The threshold the learner actually computes is

    thr_n(alpha) = log(1/alpha) + (1/2) sum_e log(1 + N_e(n)/a),

and the second term GROWS WITHOUT BOUND in `n`.  So the theorem could not be applied to the
algorithm by renaming variables, and saying otherwise would have been wrong.

The repair is a shift, and it costs an arbitrarily small amount of information rate.

1. `code_threshold_sublinear`: the threshold term is sublinear.  For every slope `kappa > 0`
   there is an explicit intercept `thrIntercept` with

       (1/2) sum_e log(1 + N_e(n)/a)  <=  kappa * n + thrIntercept.

   The only analytic input is `log y <= c y - log c - 1`, itself `log x <= x - 1`.

2. `a7_chain_rate_code_threshold`: run the chain on the shifted process
   `Z'_n = Z_n - kappa n`, `thr'_n = thr_n - kappa n`.  The crossing event is untouched --
   the same `kappa n` is subtracted from both sides -- so the stopping time is the same
   random variable.  What changes is the per-round information: the head worsens from
   `-Gamma` to `-(Gamma + kappa)` and the good-round gain drops from `G` to `G - kappa`.
   The conclusion is the same rate law with `G - kappa` in place of `G`.

3. `rate_limit_as_kappa_to_zero`: the loss is arbitrarily small.  For every `eta > 0` some
   `kappa` makes `1/((1-eps)(G-kappa))` within `eta` of `1/((1-eps)G)`.

The three together are the honest form of A-H4: the learner attains `1/((1-eps)G)` up to an
arbitrarily small slack, with the threshold the code computes, not a bounded stand-in.
-/

namespace CIGAMF.P13.PaperA7Threshold

open scoped BigOperators
open CIGAMF.P13.PaperA7Chain
open CIGAMF.P13.PaperA7Tracking

/-! ## The threshold term is sublinear -/

/-- `log y <= c y - log c - 1`, for every positive slope `c`: the tangent-line bound with a
free slope.  At `c = 1` it is `log y <= y - 1`. -/
theorem log_le_linear (c y : ℝ) (hc : 0 < c) (hy : 0 < y) :
    Real.log y ≤ c * y - Real.log c - 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < c * y by positivity)
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hy)] at h
  linarith

/-- The intercept that buys slope `kappa`. -/
noncomputable def thrIntercept (nE a κ : ℝ) : ℝ :=
  (nE / 2) * (2 * a * κ / nE - Real.log (2 * a * κ / nE) - 1)

/-- **The intercept is nonnegative**, which is what `hs` in the chain asks of `s(alpha)`. -/
theorem thrIntercept_nonneg (nE a κ : ℝ) (hnE : 0 < nE) (ha : 0 < a) (hκ : 0 < κ) :
    0 ≤ thrIntercept nE a κ := by
  have hc : (0 : ℝ) < 2 * a * κ / nE := by positivity
  have h := Real.log_le_sub_one_of_pos hc
  unfold thrIntercept
  have : 0 ≤ 2 * a * κ / nE - Real.log (2 * a * κ / nE) - 1 := by linarith
  positivity

/-- **Each count is at most the horizon.** -/
theorem count_le_horizon {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] (T : Tracking E)
    (t : ℕ) (e : E) (hnn : ∀ (s : ℕ) (f : E), 0 ≤ T.N s f) : T.N t e ≤ (t : ℝ) := by
  classical
  have hsum := T.N_sum t
  have hrest : 0 ≤ ∑ f ∈ Finset.univ.erase e, T.N t f :=
    Finset.sum_nonneg (fun f _ => hnn t f)
  have hsplit : T.N t e + ∑ f ∈ Finset.univ.erase e, T.N t f = ∑ f, T.N t f :=
    Finset.add_sum_erase _ (fun f => T.N t f) (Finset.mem_univ e)
  linarith [hsum, hsplit, hrest]

/-- **The counts are nonnegative**, by the recursion the code performs. -/
theorem N_nonneg {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] (T : Tracking E)
    (t : ℕ) (e : E) : 0 ≤ T.N t e := by
  induction t with
  | zero => rw [T.N0]
  | succ t ih =>
      rw [T.Nstep t e]
      have : (0 : ℝ) ≤ (if e = T.pick (t + 1) then (1:ℝ) else 0) := by
        by_cases h : e = T.pick (t + 1) <;> simp [h]
      linarith

/-- **The threshold term is bounded by the horizon's**, since no count exceeds the
horizon. -/
theorem threshold_term_le_card {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] (T : Tracking E)
    (a : ℝ) (ha : 0 < a) (t : ℕ) :
    (1 / 2 : ℝ) * ∑ e, Real.log (1 + T.N t e / a)
      ≤ ((Fintype.card E : ℝ) / 2) * Real.log (1 + (t : ℝ) / a) := by
  have hterm : ∀ e : E, Real.log (1 + T.N t e / a) ≤ Real.log (1 + (t : ℝ) / a) := by
    intro e
    have hle : 1 + T.N t e / a ≤ 1 + (t : ℝ) / a := by
      have := count_le_horizon T t e (fun s f => N_nonneg T s f)
      have hdiv : T.N t e / a ≤ (t : ℝ) / a := by
        rw [div_le_div_iff_of_pos_right ha]
        exact this
      linarith
    have hpos : (0 : ℝ) < 1 + T.N t e / a := by
      have := N_nonneg T t e
      positivity
    exact Real.log_le_log hpos hle
  have hsum : ∑ e, Real.log (1 + T.N t e / a)
      ≤ ∑ _e : E, Real.log (1 + (t : ℝ) / a) := Finset.sum_le_sum (fun e _ => hterm e)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  linarith

/-- **The code's threshold term is sublinear**: any slope, at an explicit intercept. -/
theorem code_threshold_sublinear {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] (T : Tracking E)
    (a κ : ℝ) (ha : 0 < a) (hκ : 0 < κ) (hE : 0 < Fintype.card E) (t : ℕ) :
    (1 / 2 : ℝ) * ∑ e, Real.log (1 + T.N t e / a)
      ≤ κ * (t : ℝ) + thrIntercept (Fintype.card E : ℝ) a κ := by
  have hnE : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast hE
  have hc : (0 : ℝ) < 2 * a * κ / (Fintype.card E : ℝ) := by positivity
  have hy : (0 : ℝ) < 1 + (t : ℝ) / a := by positivity
  have hlin := log_le_linear (2 * a * κ / (Fintype.card E : ℝ)) (1 + (t : ℝ) / a) hc hy
  have hcard := threshold_term_le_card T a ha t
  have hexp : ((Fintype.card E : ℝ) / 2)
      * ((2 * a * κ / (Fintype.card E : ℝ)) * (1 + (t : ℝ) / a)
          - Real.log (2 * a * κ / (Fintype.card E : ℝ)) - 1)
      = κ * (t : ℝ) + thrIntercept (Fintype.card E : ℝ) a κ := by
    unfold thrIntercept
    field_simp
    ring
  have hscale : ((Fintype.card E : ℝ) / 2) * Real.log (1 + (t : ℝ) / a)
      ≤ ((Fintype.card E : ℝ) / 2)
        * ((2 * a * κ / (Fintype.card E : ℝ)) * (1 + (t : ℝ) / a)
            - Real.log (2 * a * κ / (Fintype.card E : ℝ)) - 1) :=
    mul_le_mul_of_nonneg_left hlin (by positivity)
  linarith [hcard, hscale, hexp.le, hexp.ge]

/-! ## The chain with the code's threshold -/

/-- **A-H4 with the threshold the code computes.**  The process is run on `Z_n - kappa n`
against `thr_n - kappa n`; the crossing event is unchanged, so the stopping time is the same
random variable, and the price is that the per-round information drops from `G` to
`G - kappa`. -/
theorem a7_chain_rate_code_threshold {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (good : ℝ → ℕ → Set Ω) (z Z thr : ℝ → Ω → ℕ → ℝ) (τ : ℝ → Ω → ℕ)
    (Esum : ℝ → ℕ → ℝ) (Eτ s : ℝ → ℝ)
    (Γ G C ε κ : ℝ) (hG : 0 < G) (hε : 0 < ε) (hε1 : ε < 1)
    (hΓ : 0 ≤ Γ) (hGΓ : G ≤ Γ) (hC : 0 ≤ C)
    (hκ : 0 < κ) (hκG : κ < G)
    (hs : ∀ α, 0 ≤ s α)
    (hstep : ∀ α n, (μ (good α n)ᶜ).toReal ≤ 1 / (n : ℝ) ^ 4)
    (hτ : ∀ α ω n, thr α ω n < Z α ω n → τ α ω ≤ n)
    (hhead : ∀ α ω n, -Γ ≤ z α ω n)
    (hgood : ∀ α ω n, ω ∈ good α n → G ≤ z α ω n)
    (hinit : ∀ α ω n, (∑ r ∈ Finset.range n, z α ω r) - C ≤ Z α ω n)
    -- the code's threshold: a bounded part plus an unbounded but SUBLINEAR part
    (hthr : ∀ α ω n, thr α ω n ≤ Real.log (1 / α) + s α + κ * (n : ℝ))
    (hEsumα : ∀ α M, Esum α M
        ≤ ((⌈(Real.log (1 / α) + s α + winBudget (Γ + κ) (G - κ) C ε)
              / ((1 - ε) * (G - κ))⌉₊ + 2 : ℕ) : ℝ)
          + ∑ t ∈ Finset.Ico
              (⌈(Real.log (1 / α) + s α + winBudget (Γ + κ) (G - κ) C ε)
                / ((1 - ε) * (G - κ))⌉₊ + 2) M,
              (μ {ω | t < τ α ω}).toReal)
    (hsup : ∀ α y, (∀ M, Esum α M ≤ y) → Eτ α ≤ y)
    (εr α0 : ℝ) (hα0 : 0 < α0) (hα01 : α0 < 1)
    (hsmall : ∀ α, 0 < α → α < α0 →
        0 < Real.log (1 / α) ∧
        (s α + winBudget (Γ + κ) (G - κ) C ε) + 19 * ((1 - ε) * (G - κ))
          ≤ εr * ((1 - ε) * (G - κ)) * Real.log (1 / α)) :
    ∀ α, 0 < α → α < α0 → Eτ α / Real.log (1 / α) ≤ 1 / ((1 - ε) * (G - κ)) + εr := by
  refine a7_chain_rate μ good (fun α ω n => z α ω n - κ)
    (fun α ω n => Z α ω n - κ * (n : ℝ)) (fun α ω n => thr α ω n - κ * (n : ℝ)) τ Esum Eτ s
    (Γ + κ) (G - κ) C ε (by linarith) hε hε1 (by linarith) (by linarith) hC hs hstep
    ?_ ?_ ?_ ?_ ?_ hEsumα hsup εr α0 hα0 hα01 hsmall
  · intro α ω n hcross
    exact hτ α ω n (by linarith)
  · intro α ω n
    linarith [hhead α ω n]
  · intro α ω n hω
    linarith [hgood α ω n hω]
  · intro α ω n
    have hconst : ∑ _r ∈ Finset.range n, κ = (n : ℝ) * κ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsplit : ∑ r ∈ Finset.range n, (z α ω r - κ)
        = (∑ r ∈ Finset.range n, z α ω r) - (n : ℝ) * κ := by
      rw [Finset.sum_sub_distrib, hconst]
    rw [hsplit]
    have := hinit α ω n
    linarith
  · intro α ω n
    linarith [hthr α ω n]

/-! ## The price of the shift goes to zero -/

/-- **The information lost by the shift is arbitrarily small.**  For every tolerance there
is a slope small enough that the shifted rate is within it of the unshifted one. -/
theorem rate_limit_as_kappa_to_zero (ε G η : ℝ) (hε1 : ε < 1) (hG : 0 < G) (hη : 0 < η) :
    ∃ κ : ℝ, 0 < κ ∧ κ < G ∧
      1 / ((1 - ε) * (G - κ)) ≤ 1 / ((1 - ε) * G) + η := by
  have he : (0 : ℝ) < 1 - ε := by linarith
  refine ⟨min (G / 2) (η * (1 - ε) * G ^ 2 / 2), ?_, ?_, ?_⟩
  · have h1 : (0 : ℝ) < G / 2 := by linarith
    have h2 : (0 : ℝ) < η * (1 - ε) * G ^ 2 / 2 := by positivity
    exact lt_min h1 h2
  · have h1 : min (G / 2) (η * (1 - ε) * G ^ 2 / 2) ≤ G / 2 := min_le_left _ _
    linarith
  · set κ := min (G / 2) (η * (1 - ε) * G ^ 2 / 2) with hκdef
    have hκ0 : 0 < κ := by
      have h1 : (0 : ℝ) < G / 2 := by linarith
      have h2 : (0 : ℝ) < η * (1 - ε) * G ^ 2 / 2 := by positivity
      exact lt_min h1 h2
    have hκhalf : κ ≤ G / 2 := min_le_left _ _
    have hκbd : κ ≤ η * (1 - ε) * G ^ 2 / 2 := min_le_right _ _
    have hGκ : G / 2 ≤ G - κ := by linarith
    have hGκpos : (0 : ℝ) < G - κ := by linarith
    have hd1 : (0 : ℝ) < (1 - ε) * G := by positivity
    have hd2 : (0 : ℝ) < (1 - ε) * (G - κ) := by positivity
    have hid : 1 / ((1 - ε) * (G - κ)) - 1 / ((1 - ε) * G)
        = κ / ((1 - ε) * G * (G - κ)) := by
      field_simp
      ring
    have hden : (0 : ℝ) < (1 - ε) * G * (G - κ) := by positivity
    have hle : κ / ((1 - ε) * G * (G - κ)) ≤ η := by
      rw [div_le_iff₀ hden]
      nlinarith [hκbd, hGκ, he, hG]
    linarith [hid.le, hid.ge, hle]

/-! ## Audit -/

#print axioms log_le_linear
#print axioms thrIntercept_nonneg
#print axioms count_le_horizon
#print axioms N_nonneg
#print axioms threshold_term_le_card
#print axioms code_threshold_sublinear
#print axioms a7_chain_rate_code_threshold
#print axioms rate_limit_as_kappa_to_zero

end CIGAMF.P13.PaperA7Threshold
