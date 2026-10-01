import Mathlib
import LeanMarlDecisionCertificateV1

/-!
# Decision lifetime of a relay view (paper_marl_v2, Claim "Decision lifetime")

`q_f` are an actor's logits on the fresh complete view and `q_r` on its relay view.  Logits matter only up to a common
shift (the argmax and the softmax are shift-invariant), so the perturbation is measured in the gauge-invariant
sup-norm `inf_c max_a |q_r a - q_f a - c|`.  This module reuses `LeanMarlDecisionCertificateV1.argmax_stable` (PROVED)
and adds the shift and the age composition.

## WHAT IS PROVED
* `argmax_stable_gauge` — if `|q_r a - q_f a - c| ≤ ε` for every action and one constant `c`, and the fresh margin of
  `a0` exceeds `2ε`, then `a0` is still the strict maximiser of `q_r`.
* `relay_action_equals_fresh` — if the gauge perturbation of a view whose relayed copies are at most `h` steps old is at
  most `e0 + ν h`, and the fresh margin exceeds `2 (e0 + ν H)` with `h ≤ H` and `ν ≥ 0`, the relay action equals the
  fresh action.
* `lifetime_witness` — a two-action instance with a strictly positive drift rate satisfies every hypothesis.

## WHAT THIS DOES NOT ESTABLISH
- Values of `e0` and `ν` for the E3 actor: they are measured (V-F), not derived.
- An age bound `h ≤ H` at every receiver under age-first ordering: not proved (`LeanMarlAgeFirstInjectionV1` bounds
  injection only; `LeanMarlRelayOneHopV1` bounds ages relative to injection under a covering head).
-/

namespace CIGAMF.P13.MarlDecisionLifetime

open CIGAMF.P13.MarlDecisionCertificate

variable {A : Type*}

/-- **Argmax stability up to a common shift.** -/
theorem argmax_stable_gauge (qf qr : A → ℝ) (a0 : A) (ε c : ℝ)
    (hmove : ∀ a, |qr a - qf a - c| ≤ ε) (hgap : ∀ b, b ≠ a0 → qf a0 - qf b > 2 * ε) :
    ∀ b, b ≠ a0 → qr b < qr a0 := by
  have h := argmax_stable qf (fun a => qr a - c) a0 ε
    (fun a => by
      have := hmove a
      rwa [show qr a - c - qf a = qr a - qf a - c by ring]) hgap
  intro b hb
  have h2 : qr b - c < qr a0 - c := h b hb
  linarith

/-- **The relay action equals the fresh action** when the fresh margin covers the age-dependent perturbation. -/
theorem relay_action_equals_fresh (qf qr : A → ℝ) (a0 : A) (e0 ν c : ℝ) (h H : ℕ) (hν : 0 ≤ ν) (hh : h ≤ H)
    (hmove : ∀ a, |qr a - qf a - c| ≤ e0 + ν * h)
    (hgap : ∀ b, b ≠ a0 → qf a0 - qf b > 2 * (e0 + ν * H)) :
    ∀ b, b ≠ a0 → qr b < qr a0 := by
  have hH : (h : ℝ) ≤ H := by exact_mod_cast hh
  have hmono : e0 + ν * h ≤ e0 + ν * H := by nlinarith
  refine argmax_stable_gauge qf qr a0 (e0 + ν * h) c hmove fun b hb => ?_
  have := hgap b hb
  linarith

/-- The hypotheses are satisfiable with a strictly positive drift rate and a nonzero shift. -/
theorem lifetime_witness :
    ∃ (qf qr : Bool → ℝ) (c : ℝ), (∀ a, |qr a - qf a - c| ≤ (1 / 4 : ℝ) + (1 / 8 : ℝ) * (2 : ℕ)) ∧
      (∀ b, b ≠ true → qf true - qf b > 2 * ((1 / 4 : ℝ) + (1 / 8 : ℝ) * (3 : ℕ))) ∧ qr false < qr true := by
  refine ⟨fun b => if b then 3 else 0, fun b => if b then 13 else 10.4, 10, ?_, ?_, ?_⟩
  · intro a; cases a <;> norm_num [abs_le]
  · intro b hb; cases b
    · norm_num
    · exact absurd rfl hb
  · norm_num

end CIGAMF.P13.MarlDecisionLifetime

#print axioms CIGAMF.P13.MarlDecisionLifetime.argmax_stable_gauge
#print axioms CIGAMF.P13.MarlDecisionLifetime.relay_action_equals_fresh
#print axioms CIGAMF.P13.MarlDecisionLifetime.lifetime_witness
