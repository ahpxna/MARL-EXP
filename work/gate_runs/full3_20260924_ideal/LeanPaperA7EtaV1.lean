import «LeanPaperA7TailV1»

/-!
# Paper A, A-END at rate `Gamma - eta`

`a7_rate_limsup` assumed `E tau_alpha <= log(1/alpha)/Gamma + 19`: both the rate `Gamma`
and the additive constant were inputs, and the threshold the code actually uses carries
more than `log(1/alpha)` -- it carries `(1/2) sum_e log(1 + N_e/a)` plus estimation,
oracle and tracking error.

This module proves the form the audit asked for instead.  For each `eta` with
`0 < eta < Gamma`:

  * the accumulation runs at rate `Gamma - eta` whenever the per-round increment does
    (`increment_deficit_gives_eta`);
  * the expected stopping time obeys `b/(Gamma - eta) + 19` for ANY non-negative budget
    `b`, so the extra threshold terms are carried rather than dropped
    (`expected_stopping_bound_general`);
  * with `b = log(1/alpha) + s(alpha)` and `s(alpha) = o(log(1/alpha))` the ratio is
    eventually within `eps` of `1/(Gamma - eta)` (`rate_limsup_eta`);
  * and `1/(Gamma - eta) -> 1/Gamma` as `eta` falls to zero (`eta_to_zero`).

What this does NOT prove is the clean rate `1/Gamma`.  That needs `eta` to be sent to
zero, `eta` is bounded below by the oracle's own error, and `rate_floor_of_eps_floor`
records the consequence: an error floor `epsFloor > 0` leaves a strictly worse rate
`1/(Gamma - c*epsFloor)`.

How large that shortfall is, is a measurement, and the measurement was redone.  The
bracket as originally shipped floored at `8.038e-3` against `Gamma_comp ~ 2.3256e-2`, and
an earlier version of this file read that as the duality gap between an LP relaxation
above and a weak-duality certificate below.  THAT READING WAS WRONG.  The plateau was the
cutting plane's own oscillation together with a loose dual tolerance: taking the running
minimum of the relaxation values, damping the step toward the relaxation's vertex, and
solving the regional dual to tolerance moves it to `5.043e-7`, flat in both the
cutting-plane count and the dual budget.  Flatness in both axes rules out the iteration
budget and the dual solve as the binding constraint; it does NOT by itself identify the
residual as floating-point round-off, since the weight floor `EPS_W` and the subtracted
floor correction are also candidates and the current checks do not separate them.  What is
established is the ordering of magnitudes, not the cause.  `shipped_floor_material` and
`damped_floor_negligible` record both numbers so the correction is visible rather than
silently applied.

Two further cautions, both of which an earlier version of this file got wrong.  First, a
bracket of width `eps` bounds `Gamma - J(w)` from ABOVE, not below, so a positive gap does
not show the learner is slow --- only that the bound is weak.  Second, `eta = 0` is not
proved and no floating-point bracket can prove it.
-/

namespace CIGAMF.P13.PaperA7Eta

open CIGAMF.P13.PaperA7Tail

/-- **The accumulation at a deficient rate.**  If every round of the window gains at least
`Gamma - c*eps`, the window gains at least `n (Gamma - c*eps)`.  This is the only place the
oracle's error enters the rate, and it enters linearly. -/
theorem increment_deficit_gives_eta (inc : ℕ → ℝ) (Γ c epsv : ℝ) (n : ℕ)
    (h : ∀ t, Γ - c * epsv ≤ inc t) :
    (n : ℝ) * (Γ - c * epsv) ≤ ∑ t ∈ Finset.range n, inc t := by
  have hc : ∑ _t ∈ Finset.range n, (Γ - c * epsv) ≤ ∑ t ∈ Finset.range n, inc t :=
    Finset.sum_le_sum (fun t _ => h t)
  rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hc

/-- **The expected stopping bound for ANY budget.**  `expected_stopping_bound_at_level`
fixed the budget at `log(1/alpha)`; here it is an arbitrary non-negative `b`, so the
threshold's extra terms can be carried inside it instead of being dropped. -/
theorem expected_stopping_bound_general
    (Esum p : ℕ → ℝ) (G b : ℝ) (hG : 0 < G) (hb : 0 ≤ b)
    (hp : ∀ t, p t ≤ 8 / (Real.sqrt t) ^ 3)
    (hEsum : ∀ M, Esum M ≤ ((⌈b / G⌉₊ + 2 : ℕ) : ℝ)
        + ∑ t ∈ Finset.Ico (⌈b / G⌉₊ + 2) M, p t) :
    ∀ M, Esum M ≤ b / G + 19 := by
  intro M
  set t0 : ℕ := ⌈b / G⌉₊ + 2 with ht0
  have ht02 : 2 ≤ t0 := by omega
  have hdiv : 0 ≤ b / G := div_nonneg hb (le_of_lt hG)
  have hceil : (⌈b / G⌉₊ : ℝ) ≤ b / G + 1 := le_of_lt (Nat.ceil_lt_add_one hdiv)
  have ht0R : (t0 : ℝ) ≤ b / G + 3 := by rw [ht0]; push_cast; linarith
  have hsum : ∑ t ∈ Finset.Ico t0 M, p t ≤ 16 / Real.sqrt ((t0 : ℝ) - 1) :=
    le_trans (Finset.sum_le_sum (fun t _ => hp t)) (sqrt_tail_sum_le t0 M ht02)
  have ht01 : (1 : ℝ) ≤ (t0 : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (t0 : ℝ) := by exact_mod_cast ht02
    linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((t0 : ℝ) - 1) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((t0 : ℝ) - 1) := Real.sqrt_le_sqrt ht01
    rwa [Real.sqrt_one] at h1
  have h16 : 16 / Real.sqrt ((t0 : ℝ) - 1) ≤ 16 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith [hEsum M, hsum, ht0R, h16]

/-- **The rate at a deficient `G`, with an `o(log(1/alpha))` slack carried.**  The slack
`s` absorbs `(1/2) sum_e log(1 + N_e/a)` and the estimation and tracking terms; it is not
required to be bounded, only to be small against `log(1/alpha)` eventually. -/
theorem rate_limsup_eta (Eτ s : ℝ → ℝ) (G C : ℝ) (hG : 0 < G)
    (hbound : ∀ α, 0 < α → α < 1 → Eτ α ≤ (Real.log (1 / α) + s α) / G + C)
    (ε α0 : ℝ) (hα0 : 0 < α0) (hα01 : α0 < 1)
    (hsmall : ∀ α, 0 < α → α < α0 →
        0 < Real.log (1 / α) ∧ s α + C * G ≤ ε * G * Real.log (1 / α)) :
    ∀ α, 0 < α → α < α0 → Eτ α / Real.log (1 / α) ≤ 1 / G + ε := by
  intro α hα hαlt
  obtain ⟨hlog, hs⟩ := hsmall α hα hαlt
  have h1 := hbound α hα (lt_trans hαlt hα01)
  rw [div_le_iff₀ hlog]
  have hexp : (1 / G + ε) * Real.log (1 / α) - ((Real.log (1 / α) + s α) / G + C)
      = (ε * G * Real.log (1 / α) - (s α + C * G)) / G := by
    field_simp; ring
  have hnn : 0 ≤ (ε * G * Real.log (1 / α) - (s α + C * G)) / G :=
    div_nonneg (by linarith) hG.le
  linarith

/-- **The `eta` step, made explicit.**  `1/(Gamma - eta)` can be brought within any `eps`
of `1/Gamma`, so the clean rate follows from the family above the moment `eta` may be
taken arbitrarily small -- and only then. -/
theorem eta_to_zero (Γ ε : ℝ) (hΓ : 0 < Γ) (hε : 0 < ε) :
    ∃ η, 0 < η ∧ η < Γ ∧ 1 / (Γ - η) ≤ 1 / Γ + ε := by
  have h1 : 0 < min (Γ / 2) (ε * Γ ^ 2 / 2) := lt_min (by linarith) (by positivity)
  have h2 : min (Γ / 2) (ε * Γ ^ 2 / 2) ≤ Γ / 2 := min_le_left _ _
  have h3 : min (Γ / 2) (ε * Γ ^ 2 / 2) ≤ ε * Γ ^ 2 / 2 := min_le_right _ _
  refine ⟨min (Γ / 2) (ε * Γ ^ 2 / 2), h1, by linarith, ?_⟩
  have h4 : 0 < Γ - min (Γ / 2) (ε * Γ ^ 2 / 2) := by linarith
  rw [div_le_iff₀ h4]
  have hexp : (1 / Γ + ε) * (Γ - min (Γ / 2) (ε * Γ ^ 2 / 2)) - 1
      = ε * (Γ - min (Γ / 2) (ε * Γ ^ 2 / 2))
        - min (Γ / 2) (ε * Γ ^ 2 / 2) / Γ := by
    field_simp; ring
  have hhalf : (0 : ℝ) ≤ Γ - min (Γ / 2) (ε * Γ ^ 2 / 2) - Γ / 2 := by linarith
  have hprod : 0 ≤ (ε * Γ) * (Γ - min (Γ / 2) (ε * Γ ^ 2 / 2) - Γ / 2) :=
    mul_nonneg (mul_pos hε hΓ).le hhalf
  have hkey : min (Γ / 2) (ε * Γ ^ 2 / 2) / Γ
      ≤ ε * (Γ - min (Γ / 2) (ε * Γ ^ 2 / 2)) := by
    rw [div_le_iff₀ hΓ]
    nlinarith [hprod, h3]
  linarith

/-- **What an error floor costs THE CERTIFICATE.**

Read this carefully, because an earlier version of this file read it wrongly.  A bracket
of width `eps` gives `0 <= Gamma - J(w) <= eps`.  It does NOT give `Gamma - J(w) >= eps`:
the design may well be exactly optimal, with the slack living entirely in a loose upper
certificate.  So a positive bracket gap does **not** show that the learner is slower.

What it does show is that the rate this chain can *certify* degrades: the best bound
obtainable from a bracket of width `eps` is `1/(Gamma - c*eps)`, which is strictly larger
than `1/Gamma`.  The statement below is about the bound, not about the algorithm. -/
theorem rate_floor_of_eps_floor (Γ c epsFloor : ℝ) (hΓ : 0 < Γ) (hc : 0 < c)
    (hε : 0 < epsFloor) (hlt : c * epsFloor < Γ) :
    1 / Γ < 1 / (Γ - c * epsFloor) := by
  have h1 : 0 < Γ - c * epsFloor := by linarith
  have hcp : 0 < c * epsFloor := mul_pos hc hε
  rw [div_lt_div_iff₀ hΓ h1]
  linarith

/-- **The certified shortfall, before and after the method was corrected.**  Both are
instances of `rate_floor_of_eps_floor`, so both are statements about the *certifiable*
bound and not about the learner's actual speed.  With the bracket as shipped,
`Gamma = 2.3256e-2` and a bracket width of `8.038e-3` left a certified bound more than a
third worse than `1/Gamma`. -/
theorem shipped_floor_material :
    1 / ((23256 : ℝ) / 1000000) < 1 / ((15218 : ℝ) / 1000000)
      ∧ (13 : ℝ) / 10 * (1 / ((23256 : ℝ) / 1000000)) < 1 / ((15218 : ℝ) / 1000000) := by
  constructor <;> norm_num

/-- With the running minimum, the damped step and the dual solved to tolerance the bracket
width is `5.043e-7`: the certified bound is still worse than `1/Gamma` --- it must be, for
any positive width --- but by under `1e-4` in relative terms. -/
theorem damped_floor_negligible :
    1 / ((23256 : ℝ) / 1000000) < 1 / ((232554957 : ℝ) / 10000000000)
      ∧ 1 / ((232554957 : ℝ) / 10000000000)
          < (10001 : ℝ) / 10000 * (1 / ((23256 : ℝ) / 1000000)) := by
  constructor <;> norm_num

/-! ## Audit -/

#print axioms increment_deficit_gives_eta
#print axioms expected_stopping_bound_general
#print axioms rate_limsup_eta
#print axioms eta_to_zero
#print axioms rate_floor_of_eps_floor
#print axioms shipped_floor_material
#print axioms damped_floor_negligible

end CIGAMF.P13.PaperA7Eta
