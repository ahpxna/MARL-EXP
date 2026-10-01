import Mathlib

/-!
# Skipping a transmission without changing any decision (MARL E3, direction (b))

A closed loop with a physical state `x t`, receiver caches `c t` and receivers `i : ι` that act by an argmax rule
`pick` on logits `ℓ` of their input `enc i (x t) (c t)`.  The physical transition `step` depends on the physical
state and the joint action only (in E3: CityFlow advances on the signal phases; the caches never enter the physics).
A reference run `(xr, cr)` (the prefix protocol) and an actual run `(x, c)` (the same system, fewer transmissions,
so different caches) start from the same physical state.

## WHAT IS PROVED
* `states_agree` / `cost_sum_agree` — if the joint actions of two runs agree at every step before `T`, their
  physical states agree up to `T` and so does any state cost summed over the steps (waiting, queue): whatever the
  caches did.  (The exact, simulated certificate of `MARL_e3_zero_loss_truncation.py` with `H = end` is this.)
* `argmax_stable` — if every logit moves by at most `ε` and the chosen action leads every other by more than
  `2ε`, it stays the unique maximiser.  `argmax_stable_lipschitz`: the same with `ε = L · dist` for `L`-Lipschitz
  logits.  `margin_threshold_sharp`: for every lead `g ≤ 2ε` a move of size `ε` makes another action tie or win,
  so `2ε` cannot be lowered.
* `certified_skip_keeps_trajectory` — the LIFETIME certificate: if at EVERY step `t < T` and for EVERY receiver
  the reference logits' lead exceeds `2 L · dist(input with the ACTUAL cache, input with the reference cache)`,
  both evaluated at the REFERENCE physical state, then the actual run's physical states equal the reference's
  up to `T`.  `certified_skip_keeps_cost` gives the equal cost.  The condition is on the actual future caches,
  not only on the step where a packet is skipped.
* `lifetime_from_drift_rate` — if the input distance grows at most as `κ + h ν` over the lifetime and
  `2 L (κ + H ν) < g`, the per-step condition holds for all `h ≤ H` (a certificate length from a drift rate).
* `current_step_invariance_insufficient` — a concrete instance: a stale cache value gives the SAME action as the
  fresh one at the skip step and a DIFFERENT one a step later, after the physical state moved.  So "the current
  action is unchanged" does not certify a skip.
* `skip_hypotheses_satisfiable`, `skip_instance` — every hypothesis of `certified_skip_keeps_trajectory` holds in a
  concrete instance with a stale cache (`c ≠ cr`), and the theorem is applied to it: the certificate is not vacuous.

## WHAT THIS DOES NOT ESTABLISH
- A Lipschitz constant, margins or drift rates for the E3 actor (none is computed; the per-sender `fresh` flag is
  a unit jump in its input coordinate, so its contribution to `dist` is not small).
- That certified savings are large (that is data: `MARL_e3_zero_loss_truncation.py`).
- That CityFlow is deterministic (checked empirically by that script's self-checks, not proved).
- Anything about the value of a transmission that DOES change a decision.
-/

namespace CIGAMF.P13.MarlDecisionCertificate

section Trajectory

variable {S Act : Type*}

theorem states_agree (step : S → Act → S) (x x' : ℕ → S) (a a' : ℕ → Act) (T : ℕ)
    (hx : ∀ t, x (t + 1) = step (x t) (a t)) (hx' : ∀ t, x' (t + 1) = step (x' t) (a' t))
    (h0 : x 0 = x' 0) (ha : ∀ t < T, a t = a' t) : ∀ t ≤ T, x t = x' t := by
  intro t ht
  induction t with
  | zero => exact h0
  | succ n ih => rw [hx n, hx' n, ih (by omega), ha n (by omega)]

theorem cost_sum_agree (step : S → Act → S) (x x' : ℕ → S) (a a' : ℕ → Act) (T : ℕ) (cost : S → ℝ)
    (hx : ∀ t, x (t + 1) = step (x t) (a t)) (hx' : ∀ t, x' (t + 1) = step (x' t) (a' t))
    (h0 : x 0 = x' 0) (ha : ∀ t < T, a t = a' t) :
    ∑ t ∈ Finset.range (T + 1), cost (x t) = ∑ t ∈ Finset.range (T + 1), cost (x' t) := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [states_agree step x x' a a' T hx hx' h0 ha t (by have := Finset.mem_range.mp ht; omega)]

end Trajectory

section Margin

variable {A : Type*}

theorem argmax_stable (ℓ ℓ' : A → ℝ) (a0 : A) (ε : ℝ)
    (hmove : ∀ a, |ℓ' a - ℓ a| ≤ ε) (hgap : ∀ b, b ≠ a0 → ℓ a0 - ℓ b > 2 * ε) :
    ∀ b, b ≠ a0 → ℓ' b < ℓ' a0 := by
  intro b hb
  have h1 := hmove b
  have h2 := hmove a0
  have h3 := hgap b hb
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

theorem argmax_stable_lipschitz {X : Type*} [PseudoMetricSpace X] (ℓ : X → A → ℝ) (L : ℝ) (y y' : X) (a0 : A)
    (hLip : ∀ (a : A) (u v : X), |ℓ u a - ℓ v a| ≤ L * dist u v)
    (hgap : ∀ b, b ≠ a0 → ℓ y a0 - ℓ y b > 2 * (L * dist y' y)) :
    ∀ b, b ≠ a0 → ℓ y' b < ℓ y' a0 :=
  argmax_stable (ℓ y) (ℓ y') a0 (L * dist y' y) (fun a => hLip a y' y) hgap

/-- For a lead `g ≤ 2ε` of action 0 over action 1, moves of size `ε` make action 1 tie or win. -/
theorem margin_threshold_sharp (ε g : ℝ) (hε : 0 ≤ ε) (hg : g ≤ 2 * ε) :
    ∃ l0 l1 l0' l1' : ℝ, l0 - l1 = g ∧ |l0' - l0| ≤ ε ∧ |l1' - l1| ≤ ε ∧ l0' ≤ l1' := by
  refine ⟨g / 2, -(g / 2), g / 2 - ε, -(g / 2) + ε, by ring, ?_, ?_, by linarith⟩
  · rw [show g / 2 - ε - g / 2 = -ε by ring, abs_neg, abs_of_nonneg hε]
  · rw [show -(g / 2) + ε - -(g / 2) = ε by ring, abs_of_nonneg hε]

end Margin

section Lifetime

variable {ι S C X A : Type*} [PseudoMetricSpace X]

/-- The lifetime certificate: the lead of the REFERENCE logits exceeds `2 L` times the distance between the input
built with the ACTUAL cache and with the reference cache, at the reference physical state, at every step before
`T` and for every receiver.  Then the actual run keeps the reference's physical trajectory up to `T`. -/
theorem certified_skip_keeps_trajectory
    (ℓ : X → A → ℝ) (L : ℝ) (pick : (A → ℝ) → A)
    (hpick : ∀ (f : A → ℝ) (a : A), (∀ b, b ≠ a → f b < f a) → pick f = a)
    (hLip : ∀ (a : A) (u v : X), |ℓ u a - ℓ v a| ≤ L * dist u v)
    (enc : ι → S → C → X) (step : S → (ι → A) → S)
    (x xr : ℕ → S) (c cr : ℕ → C) (T : ℕ)
    (hx : ∀ t, x (t + 1) = step (x t) (fun i => pick (ℓ (enc i (x t) (c t)))))
    (hxr : ∀ t, xr (t + 1) = step (xr t) (fun i => pick (ℓ (enc i (xr t) (cr t)))))
    (h0 : x 0 = xr 0)
    (hcert : ∀ t < T, ∀ i, ∀ b, b ≠ pick (ℓ (enc i (xr t) (cr t))) →
        ℓ (enc i (xr t) (cr t)) (pick (ℓ (enc i (xr t) (cr t)))) - ℓ (enc i (xr t) (cr t)) b
          > 2 * (L * dist (enc i (xr t) (c t)) (enc i (xr t) (cr t)))) :
    ∀ t ≤ T, x t = xr t := by
  intro t ht
  induction t with
  | zero => exact h0
  | succ n ih =>
    have hn : x n = xr n := ih (by omega)
    have hact : (fun i => pick (ℓ (enc i (x n) (c n)))) = (fun i => pick (ℓ (enc i (xr n) (cr n)))) := by
      funext i
      rw [hn]
      apply hpick
      exact argmax_stable (ℓ (enc i (xr n) (cr n))) (ℓ (enc i (xr n) (c n))) _ _
        (fun a => hLip a _ _) (hcert n (by omega) i)
    rw [hx n, hxr n, hact, hn]

theorem certified_skip_keeps_cost
    (ℓ : X → A → ℝ) (L : ℝ) (pick : (A → ℝ) → A)
    (hpick : ∀ (f : A → ℝ) (a : A), (∀ b, b ≠ a → f b < f a) → pick f = a)
    (hLip : ∀ (a : A) (u v : X), |ℓ u a - ℓ v a| ≤ L * dist u v)
    (enc : ι → S → C → X) (step : S → (ι → A) → S)
    (x xr : ℕ → S) (c cr : ℕ → C) (T : ℕ) (cost : S → ℝ)
    (hx : ∀ t, x (t + 1) = step (x t) (fun i => pick (ℓ (enc i (x t) (c t)))))
    (hxr : ∀ t, xr (t + 1) = step (xr t) (fun i => pick (ℓ (enc i (xr t) (cr t)))))
    (h0 : x 0 = xr 0)
    (hcert : ∀ t < T, ∀ i, ∀ b, b ≠ pick (ℓ (enc i (xr t) (cr t))) →
        ℓ (enc i (xr t) (cr t)) (pick (ℓ (enc i (xr t) (cr t)))) - ℓ (enc i (xr t) (cr t)) b
          > 2 * (L * dist (enc i (xr t) (c t)) (enc i (xr t) (cr t)))) :
    ∑ t ∈ Finset.range (T + 1), cost (x t) = ∑ t ∈ Finset.range (T + 1), cost (xr t) := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [certified_skip_keeps_trajectory ℓ L pick hpick hLip enc step x xr c cr T hx hxr h0 hcert t
    (by have := Finset.mem_range.mp ht; omega)]

end Lifetime

theorem lifetime_from_drift_rate (L κ ν g : ℝ) (H : ℕ) (d : ℕ → ℝ) (hL : 0 ≤ L) (hν : 0 ≤ ν)
    (hd : ∀ h ≤ H, d h ≤ κ + h * ν) (hmargin : 2 * (L * (κ + H * ν)) < g) :
    ∀ h ≤ H, 2 * (L * d h) < g := by
  intro h hh
  have hcast : (h : ℝ) ≤ H := by exact_mod_cast hh
  have h1 : d h ≤ κ + H * ν := le_trans (hd h hh) (by nlinarith)
  have h2 : L * d h ≤ L * (κ + H * ν) := mul_le_mul_of_nonneg_left h1 hL
  linarith

/-- Receiver input = physical state + cached value; action = "the input is positive".  Stale cache `u = 1`,
fresh value `v = 2`: same action at the skip step (`x = 0`), different action one step later (`x = -3/2`). -/
theorem current_step_invariance_insufficient :
    ((0 : ℝ) + 1 > 0 ↔ (0 : ℝ) + 2 > 0) ∧ ¬ ((-3 / 2 : ℝ) + 1 > 0 ↔ (-3 / 2 : ℝ) + 2 > 0) := by
  norm_num

/-- Example logits: `ℓ y true = y`, `ℓ y false = -y` (2-Lipschitz in `y`). -/
def exLogit (y : ℝ) (b : Bool) : ℝ := if b then y else -y

/-- Example argmax rule on two actions. -/
noncomputable def exPick (f : Bool → ℝ) : Bool := if f false < f true then true else false

theorem exPick_rule : ∀ (f : Bool → ℝ) (a : Bool), (∀ b, b ≠ a → f b < f a) → exPick f = a := by
  intro f a h
  cases a with
  | false =>
    have hlt := h true (by decide)
    unfold exPick
    rw [if_neg (not_lt.mpr (le_of_lt hlt))]
  | true =>
    have hlt := h false (by decide)
    unfold exPick
    rw [if_pos hlt]

theorem exLogit_lipschitz : ∀ (a : Bool) (u w : ℝ), |exLogit u a - exLogit w a| ≤ 2 * dist u w := by
  intro a u w
  rw [Real.dist_eq]
  cases a with
  | false =>
    unfold exLogit
    rw [if_neg (by decide), if_neg (by decide), show -u - -w = -(u - w) by ring, abs_neg]
    linarith [abs_nonneg (u - w)]
  | true =>
    unfold exLogit
    rw [if_pos rfl, if_pos rfl]
    linarith [abs_nonneg (u - w)]

/-- The certificate condition of `certified_skip_keeps_trajectory` in the example with a STALE cache (actual `2`,
reference `3`): the reference lead `6` exceeds `2 · 2 · |2 - 3| = 4`. -/
theorem skip_hypotheses_satisfiable (T : ℕ) :
    (∀ t < T, ∀ (_ : Unit), ∀ b, b ≠ exPick (exLogit 3) →
        exLogit 3 (exPick (exLogit 3)) - exLogit 3 b > 2 * (2 * dist (2 : ℝ) 3)) ∧ (2 : ℝ) ≠ 3 := by
  have hp : exPick (exLogit 3) = true := by
    apply exPick_rule
    intro b hb
    cases b with
    | false => unfold exLogit; norm_num
    | true => exact absurd rfl hb
  refine ⟨?_, by norm_num⟩
  intro t _ _ b hb
  rw [hp] at hb ⊢
  cases b with
  | false =>
    rw [Real.dist_eq, show (2 : ℝ) - 3 = -1 by norm_num, abs_neg, abs_one]
    unfold exLogit; norm_num
  | true => exact absurd rfl hb

/-- Every hypothesis of `certified_skip_keeps_trajectory` instantiated at once (one receiver, physical state = a
step counter, actual cache `2` ≠ reference cache `3`): the theorem applies, so its hypotheses are consistent. -/
theorem skip_instance (T : ℕ) : ∀ t ≤ T, (fun t : ℕ => t) t = (fun t : ℕ => t) t :=
  certified_skip_keeps_trajectory (ι := Unit) (S := ℕ) (C := ℝ) (X := ℝ) (A := Bool)
    exLogit 2 exPick exPick_rule exLogit_lipschitz (fun _ _ c => c) (fun s _ => s + 1)
    (fun t => t) (fun t => t) (fun _ => 2) (fun _ => 3) T (fun _ => rfl) (fun _ => rfl) rfl
    (skip_hypotheses_satisfiable T).1

end CIGAMF.P13.MarlDecisionCertificate

#print axioms CIGAMF.P13.MarlDecisionCertificate.states_agree
#print axioms CIGAMF.P13.MarlDecisionCertificate.cost_sum_agree
#print axioms CIGAMF.P13.MarlDecisionCertificate.argmax_stable
#print axioms CIGAMF.P13.MarlDecisionCertificate.argmax_stable_lipschitz
#print axioms CIGAMF.P13.MarlDecisionCertificate.margin_threshold_sharp
#print axioms CIGAMF.P13.MarlDecisionCertificate.certified_skip_keeps_trajectory
#print axioms CIGAMF.P13.MarlDecisionCertificate.certified_skip_keeps_cost
#print axioms CIGAMF.P13.MarlDecisionCertificate.lifetime_from_drift_rate
#print axioms CIGAMF.P13.MarlDecisionCertificate.current_step_invariance_insufficient
#print axioms CIGAMF.P13.MarlDecisionCertificate.exPick_rule
#print axioms CIGAMF.P13.MarlDecisionCertificate.exLogit_lipschitz
#print axioms CIGAMF.P13.MarlDecisionCertificate.skip_hypotheses_satisfiable
#print axioms CIGAMF.P13.MarlDecisionCertificate.skip_instance
