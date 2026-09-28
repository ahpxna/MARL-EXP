import «LeanPaperBParityV1»

/-!
# Paper B: a concrete adaptive policy, with its likelihood ratio written down

`LeanPaperBChangeV1` proves the transcript bound for an abstract `L_t` on a filtration: it
assumes a density of `P|F_t` with respect to `Q|F_t` exists and is a martingale.  What it
does NOT do is produce one.  The residual recorded in `THEOREM_MAP.md` was exactly that: a
concrete adaptive policy whose transcript admits such an `L_t`.

This module writes that policy down and proves the three facts about it.  A history is the
list of observations so far, most recent first; a policy is ANY function

    pi : List Y -> K

from the history to the next query.  Nothing restricts how the query depends on the past, so
the policy is fully adaptive -- this is the general adaptive policy on the paper's channel,
not a special case.  The per-step laws are `p (pi h) .` under `P` and `q (pi h) .` under `Q`;
the paper's channel has `Y = Bool`, the parity mask's two letters.

* `Lr` is the likelihood ratio along a realised history: the product of the per-step ratios
  at the queries the policy actually issued.
* `martingale_step` is the martingale property in the only form a finite alphabet needs:
  averaging `Lr` one step forward under `Q` returns `Lr`.
* `change_of_measure` is the transport identity: a `Q`-expectation of `Lr * f` over `t`
  further steps equals `Lr` times the `P`-expectation of `f`.  At `f = 1` and the empty
  history this is `E_Q[L_t] = 1`.
* `kl_chain_le_horizon` is the divergence decomposition: the transcript divergence over `t`
  steps is the sum of the per-step divergences at the queries issued, and is therefore at
  most `t` times any bound uniform over the query class.  Composed with
  `kl_uniform_over_queries` that bound is `C h^{2r}`, so the transcript divergence is at
  most `t C h^{2r}` for EVERY adaptive policy.

The one modelling input is that the alphabet is finite and `q` is strictly positive, which
the parity channel supplies.
-/

namespace CIGAMF.P13.PaperBTranscript

open Finset

variable {K Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## The construction -/

/-- The likelihood ratio along a realised history (most recent observation first). -/
noncomputable def Lr (π : List Y → K) (p q : K → Y → ℝ) : List Y → ℝ
  | [] => 1
  | (y :: h) => Lr π p q h * (p (π h) y / q (π h) y)

/-- The `t`-step expectation under a per-step law `r`, from a history. -/
noncomputable def expect (π : List Y → K) (r : K → Y → ℝ) :
    ℕ → List Y → (List Y → ℝ) → ℝ
  | 0, h, f => f h
  | (t + 1), h, f => ∑ y, r (π h) y * expect π r t (y :: h) f

/-- The per-step divergence at a query. -/
noncomputable def klStep (p q : K → Y → ℝ) (k : K) : ℝ :=
  ∑ y, p k y * Real.log (p k y / q k y)

/-- The transcript divergence of an adaptive policy, by the chain rule. -/
noncomputable def klChain (π : List Y → K) (p q : K → Y → ℝ) : ℕ → List Y → ℝ
  | 0, _ => 0
  | (t + 1), h => klStep p q (π h) + ∑ y, p (π h) y * klChain π p q t (y :: h)

/-! ## The ratio is a martingale -/

theorem Lr_nil (π : List Y → K) (p q : K → Y → ℝ) : Lr π p q [] = 1 := rfl

theorem Lr_cons (π : List Y → K) (p q : K → Y → ℝ) (y : Y) (h : List Y) :
    Lr π p q (y :: h) = Lr π p q h * (p (π h) y / q (π h) y) := rfl

/-- **The martingale property.**  One step of `Q`-averaging returns the ratio unchanged.
This is `E_Q[L_{t+1} | F_t] = L_t` on a finite alphabet, where the conditional expectation
given the past IS the average over the next letter under the issued query's law. -/
theorem martingale_step (π : List Y → K) (p q : K → Y → ℝ)
    (hq : ∀ k y, q k y ≠ 0) (hp : ∀ k, ∑ y, p k y = 1) (h : List Y) :
    ∑ y, q (π h) y * Lr π p q (y :: h) = Lr π p q h := by
  have hterm : ∀ y : Y, q (π h) y * Lr π p q (y :: h) = Lr π p q h * p (π h) y := by
    intro y
    have hqy : q (π h) y ≠ 0 := hq _ _
    rw [Lr_cons]
    field_simp
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum, hp (π h), mul_one]

/-! ## The change of measure -/

theorem expect_zero (π : List Y → K) (r : K → Y → ℝ) (h : List Y) (f : List Y → ℝ) :
    expect π r 0 h f = f h := rfl

theorem expect_succ (π : List Y → K) (r : K → Y → ℝ) (t : ℕ) (h : List Y)
    (f : List Y → ℝ) :
    expect π r (t + 1) h f = ∑ y, r (π h) y * expect π r t (y :: h) f := rfl

/-- **The transcript is a probability**: the total mass over `t` further steps is one. -/
theorem expect_one (π : List Y → K) (p : K → Y → ℝ) (hp : ∀ k, ∑ y, p k y = 1) :
    ∀ (t : ℕ) (h : List Y), expect π p t h (fun _ => (1 : ℝ)) = 1 := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [expect_succ]
      rw [Finset.sum_congr rfl (fun y _ => by rw [ih (y :: h)])]
      simpa using hp (π h)

/-- **Expectation is additive.** -/
theorem expect_add (π : List Y → K) (r : K → Y → ℝ) (f g : List Y → ℝ) :
    ∀ (t : ℕ) (h : List Y),
      expect π r t h (fun h' => f h' + g h') = expect π r t h f + expect π r t h g := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [expect_succ, expect_succ, expect_succ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [ih (y :: h)]
      ring

/-- **Expectation preserves nonnegativity.** -/
theorem expect_nonneg (π : List Y → K) (r : K → Y → ℝ) (hr : ∀ k y, 0 ≤ r k y)
    (f : List Y → ℝ) (hf : ∀ h', 0 ≤ f h') :
    ∀ (t : ℕ) (h : List Y), 0 ≤ expect π r t h f := by
  intro t
  induction t with
  | zero => intro h; exact hf h
  | succ t ih =>
      intro h
      rw [expect_succ]
      exact Finset.sum_nonneg (fun y _ => mul_nonneg (hr _ _) (ih (y :: h)))

/-- **The change of measure for an adaptive transcript.**  Every `P`-expectation over the
next `t` steps is a `Q`-expectation against the likelihood ratio, and the ratio is the
explicit product along the realised history.  No filtration, no Radon--Nikodym theorem: the
density is constructed. -/
theorem change_of_measure (π : List Y → K) (p q : K → Y → ℝ)
    (hq : ∀ k y, q k y ≠ 0) (f : List Y → ℝ) :
    ∀ (t : ℕ) (h : List Y),
      expect π q t h (fun h' => Lr π p q h' * f h')
        = Lr π p q h * expect π p t h f := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [expect_succ, expect_succ]
      have hterm : ∀ y : Y,
          q (π h) y * expect π q t (y :: h) (fun h' => Lr π p q h' * f h')
            = Lr π p q h * (p (π h) y * expect π p t (y :: h) f) := by
        intro y
        have hqy : q (π h) y ≠ 0 := hq _ _
        rw [ih (y :: h), Lr_cons]
        field_simp
      rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum]

/-- **`E_Q[L_t] = 1`.**  The specialisation at `f = 1`: the ratio is a genuine density, so
the transport identity has no defect. -/
theorem expect_Lr_eq_one (π : List Y → K) (p q : K → Y → ℝ)
    (hq : ∀ k y, q k y ≠ 0) (hp : ∀ k, ∑ y, p k y = 1) (t : ℕ) (h : List Y) :
    expect π q t h (fun h' => Lr π p q h') = Lr π p q h := by
  have hmass : ∀ (s : ℕ) (h' : List Y), expect π p s h' (fun _ => (1 : ℝ)) = 1 := by
    intro s
    induction s with
    | zero => intro h'; rfl
    | succ s ih =>
        intro h'
        rw [expect_succ]
        rw [Finset.sum_congr rfl (fun y _ => by rw [ih (y :: h')])]
        simpa using hp (π h')
  have h1 := change_of_measure π p q hq (fun _ => (1 : ℝ)) t h
  simp only [mul_one] at h1
  rw [h1, hmass t h, mul_one]

/-! ## The divergence over the horizon -/

theorem klChain_zero (π : List Y → K) (p q : K → Y → ℝ) (h : List Y) :
    klChain π p q 0 h = 0 := rfl

theorem klChain_succ (π : List Y → K) (p q : K → Y → ℝ) (t : ℕ) (h : List Y) :
    klChain π p q (t + 1) h
      = klStep p q (π h) + ∑ y, p (π h) y * klChain π p q t (y :: h) := rfl

/-- **The transcript bound for EVERY adaptive policy.**  If the per-step divergence is at
most `C` at every query in the class -- which `kl_uniform_over_queries` supplies with
`C = C_0 h^{2r}` -- then the divergence of the whole `t`-step transcript is at most `t C`,
whatever the policy does with the past. -/
theorem kl_chain_le_horizon (π : List Y → K) (p q : K → Y → ℝ) (C : ℝ)
    (hpnn : ∀ k y, 0 ≤ p k y) (hp : ∀ k, ∑ y, p k y = 1)
    (hstep : ∀ k, klStep p q k ≤ C) :
    ∀ (t : ℕ) (h : List Y), klChain π p q t h ≤ (t : ℝ) * C := by
  intro t
  induction t with
  | zero => intro h; rw [klChain_zero]; norm_num
  | succ t ih =>
      intro h
      rw [klChain_succ]
      have hsum : ∑ y, p (π h) y * klChain π p q t (y :: h)
          ≤ ∑ y, p (π h) y * ((t : ℝ) * C) := by
        refine Finset.sum_le_sum (fun y _ => ?_)
        exact mul_le_mul_of_nonneg_left (ih (y :: h)) (hpnn (π h) y)
      have hcollapse : ∑ y, p (π h) y * ((t : ℝ) * C) = (t : ℝ) * C := by
        rw [← Finset.sum_mul, hp (π h), one_mul]
      have hkey := hstep (π h)
      push_cast
      linarith [hsum, hcollapse.le, hcollapse.ge]

/-- **The transcript bound at the perturbation scale.**  With the uniform per-step bound of
`kl_uniform_over_queries` the whole transcript costs `t C_0 h^{2r}`, for every adaptive
policy on the channel. -/
theorem kl_chain_at_scale (π : List Y → K) (p q : K → Y → ℝ) (C₀ hh : ℝ) (r : ℕ)
    (hpnn : ∀ k y, 0 ≤ p k y) (hp : ∀ k, ∑ y, p k y = 1)
    (hstep : ∀ k, klStep p q k ≤ C₀ * hh ^ (2 * r)) (t : ℕ) (h : List Y) :
    klChain π p q t h ≤ (t : ℝ) * (C₀ * hh ^ (2 * r)) :=
  kl_chain_le_horizon π p q (C₀ * hh ^ (2 * r)) hpnn hp hstep t h

/-! ## The paper's channel

The parity-mask channel records a two-letter observation, so `Y = Bool` and the statements
above apply verbatim with `K = Fin m` the query index. -/

/-- **The channel instance.**  Every adaptive querying rule on the parity-mask channel has a
likelihood ratio, it is a martingale, and its transcript divergence is at most the horizon
times the uniform per-step bound. -/
theorem parity_channel_transcript (m : ℕ) (π : List Bool → Fin m) (p q : Fin m → Bool → ℝ)
    (hq : ∀ k y, q k y ≠ 0) (hpnn : ∀ k y, 0 ≤ p k y) (hp : ∀ k, ∑ y, p k y = 1)
    (C : ℝ) (hstep : ∀ k, klStep p q k ≤ C) (t : ℕ) :
    (∀ h : List Bool, ∑ y, q (π h) y * Lr π p q (y :: h) = Lr π p q h)
      ∧ expect π q t [] (fun h' => Lr π p q h') = 1
      ∧ klChain π p q t [] ≤ (t : ℝ) * C := by
  refine ⟨fun h => martingale_step π p q hq hp h, ?_, kl_chain_le_horizon π p q C hpnn hp hstep t []⟩
  rw [expect_Lr_eq_one π p q hq hp t [], Lr_nil]

/-! ## Audit -/

#print axioms expect_one
#print axioms expect_add
#print axioms expect_nonneg
#print axioms Lr_cons
#print axioms martingale_step
#print axioms change_of_measure
#print axioms expect_Lr_eq_one
#print axioms kl_chain_le_horizon
#print axioms kl_chain_at_scale
#print axioms parity_channel_transcript

end CIGAMF.P13.PaperBTranscript
