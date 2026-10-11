import Mathlib

/-!
# When is the light-side adapter needed?  A threshold signal fed by a partly gliding arrival stream (city track, 05/10/2026 21:3x EDT)

Extends `LeanCityTwoSidedV1` (one car, one decision) to an arrival stream.  Paper: research/papers/_tex/paper_two_population.tex
(Formal Verification); measured counterparts: green lengthening under the service (RL-H 15.0 -> 17.1 s, C-118; spider 18.9 -> 28.7 s),
none under MaxPressure (18.1 -> 18.0 s, C-145), TSI back to baseline (15.0 s).

Model (fluid, or expectations of a Poisson stream thinned independently).  Vehicles arrive on the red approach at rate `lam > 0`.  A share
`ρ ∈ [0, 1)` belongs to the fleet and, given a forecast, glides instead of halting.  The frozen signal perceives demand as halted vehicles
plus `A` times gliding ones (`A = 0`: a halting count; `A = 1`: a count at every speed, as MaxPressure's; TSI: a calibrated `A`), and
serves the approach once perceived demand reaches its trained threshold `θ > 0`.  Perceived demand grows at rate `eff ρ A * lam` with
`eff ρ A = 1 - ρ + A ρ`, so the approach is served after `serveTime = θ / (eff * lam)`.  A forecast learned from logs without the fleet
predicts `T0 = θ / lam`; its error once the fleet acts on it is `bias = serveTime - T0`.

## WHAT IS PROVED (θ, lam > 0, 0 ≤ A)
* `bias_mul` — closed form: `bias * eff = T0 * ρ (1 - A)`, i.e. `bias = T0 ρ (1 - A) / (1 - ρ (1 - A))`.
* `consistent_iff` — for a fleet share `0 < ρ < 1`, the no-fleet forecast stays correct iff `A = 1`: the light-side adapter is needed
  exactly when the signal's input weights gliding vehicles differently from halted ones.
* `lengthening_iff`, `shortening_iff` — the served approach waits longer than forecast iff `A < 1` (the self-defeating case: the forecast
  is early, and the signal holds the other green), and shorter iff `A > 1`.
* `allspeed_consistent` — `A = 1` (all-speed counts) is consistent for every share `ρ`.
* `bias_mono` — for `A < 1` the error grows strictly with the fleet share.
* Finite stochastic version (`n` vehicles, each gliding independently with probability `p`): `prob_total` (the weights form a probability
  distribution), `miss_lower` (with a halting count, the signal misses a served demand of `n ≥ θ ≥ 1` with probability at least `p ^ n`),
  `never_miss` (with `A ≥ 1` the perceived demand is never below the true demand, so no miss).
* `hyps_satisfiable` — θ = 10, lam = 1/2, ρ = 1/2: bias 20 (A = 0), 0 (A = 1), -20/3 (A = 2).

## WHAT THIS DOES NOT ESTABLISH
- That the learned signals implement a threshold rule (RL-H is a DQN; the model fixes the sign of its predicted change, not its size).
- Expected-time equality under Poisson arrivals is the standard thinning fact, used as motivation and not proved here.
- Anything about holding of followers on one-lane roads (W10-3), which the model omits.
-/

namespace CIGAMF.P13.CityThresholdQueueV1

noncomputable section

/-- Effective weight of the arrival stream in the perceived demand. -/
def eff (ρ A : ℝ) : ℝ := 1 - ρ + A * ρ

/-- Time for perceived demand to reach the threshold. -/
def serveTime (θ lam ρ A : ℝ) : ℝ := θ / (eff ρ A * lam)

/-- The no-fleet serve time, predicted by a forecast learned without the fleet. -/
def T0 (θ lam : ℝ) : ℝ := θ / lam

/-- Error of that forecast once the fleet acts on it. -/
def bias (θ lam ρ A : ℝ) : ℝ := serveTime θ lam ρ A - T0 θ lam

theorem eff_pos {ρ A : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hA : 0 ≤ A) : 0 < eff ρ A := by
  unfold eff; nlinarith

theorem T0_pos {θ lam : ℝ} (hθ : 0 < θ) (hl : 0 < lam) : 0 < T0 θ lam := div_pos hθ hl

theorem bias_mul {θ lam ρ A : ℝ} (hl : 0 < lam) (he : 0 < eff ρ A) :
    bias θ lam ρ A * eff ρ A = T0 θ lam * (ρ * (1 - A)) := by
  have hl' : lam ≠ 0 := ne_of_gt hl
  have he' : eff ρ A ≠ 0 := ne_of_gt he
  unfold bias serveTime T0
  field_simp
  unfold eff
  ring

theorem consistent_iff {θ lam ρ A : ℝ} (hθ : 0 < θ) (hl : 0 < lam) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) :
    bias θ lam ρ A = 0 ↔ A = 1 := by
  have he := eff_pos hρ.le hρ1 hA
  have hm := bias_mul (θ := θ) hl he
  have hT := T0_pos hθ hl
  constructor
  · intro h
    rw [h, zero_mul] at hm
    have h2 : ρ * (1 - A) = 0 := by
      rcases mul_eq_zero.mp hm.symm with h' | h'
      · exact absurd h' (ne_of_gt hT)
      · exact h'
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' (ne_of_gt hρ)
    · linarith
  · intro h
    subst h
    have h3 : bias θ lam ρ 1 * eff ρ 1 = 0 := by rw [hm]; ring
    rcases mul_eq_zero.mp h3 with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt he)

theorem lengthening_iff {θ lam ρ A : ℝ} (hθ : 0 < θ) (hl : 0 < lam) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) :
    0 < bias θ lam ρ A ↔ A < 1 := by
  have he := eff_pos hρ.le hρ1 hA
  have hm := bias_mul (θ := θ) hl he
  have hT := T0_pos hθ hl
  have hTρ : 0 < T0 θ lam * ρ := mul_pos hT hρ
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : 0 < bias θ lam ρ A * eff ρ A := mul_pos h he
    nlinarith
  · intro h
    have h2 : 0 < T0 θ lam * (ρ * (1 - A)) := mul_pos hT (mul_pos hρ (by linarith))
    rw [← hm] at h2
    by_contra hc
    push_neg at hc
    nlinarith

theorem shortening_iff {θ lam ρ A : ℝ} (hθ : 0 < θ) (hl : 0 < lam) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) :
    bias θ lam ρ A < 0 ↔ 1 < A := by
  have he := eff_pos hρ.le hρ1 hA
  have hm := bias_mul (θ := θ) hl he
  have hT := T0_pos hθ hl
  have hTρ : 0 < T0 θ lam * ρ := mul_pos hT hρ
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : bias θ lam ρ A * eff ρ A < 0 := mul_neg_of_neg_of_pos h he
    nlinarith
  · intro h
    have h2 : T0 θ lam * (ρ * (1 - A)) < 0 := by nlinarith
    rw [← hm] at h2
    by_contra hc
    push_neg at hc
    nlinarith

theorem allspeed_consistent {θ lam ρ : ℝ} (hl : 0 < lam) (h0 : 0 ≤ ρ) (h1 : ρ < 1) : bias θ lam ρ 1 = 0 := by
  have he := eff_pos h0 h1 zero_le_one
  have hm := bias_mul (θ := θ) hl he
  have h3 : bias θ lam ρ 1 * eff ρ 1 = 0 := by rw [hm]; ring
  rcases mul_eq_zero.mp h3 with h' | h'
  · exact h'
  · exact absurd h' (ne_of_gt he)

theorem bias_mono {θ lam A ρ₁ ρ₂ : ℝ} (hθ : 0 < θ) (hl : 0 < lam) (hA0 : 0 ≤ A) (hA1 : A < 1)
    (h1 : 0 ≤ ρ₁) (h12 : ρ₁ < ρ₂) (h2 : ρ₂ < 1) : bias θ lam ρ₁ A < bias θ lam ρ₂ A := by
  have he1 := eff_pos h1 (by linarith) hA0
  have he2 := eff_pos (by linarith) h2 hA0
  have bm1 := bias_mul (θ := θ) hl he1
  have bm2 := bias_mul (θ := θ) hl he2
  have hT := T0_pos hθ hl
  have key : (bias θ lam ρ₂ A - bias θ lam ρ₁ A) * (eff ρ₁ A * eff ρ₂ A) = T0 θ lam * (1 - A) * (ρ₂ - ρ₁) := by
    unfold eff at bm1 bm2 ⊢
    linear_combination (1 - ρ₁ + A * ρ₁) * bm2 - (1 - ρ₂ + A * ρ₂) * bm1
  have hpos : 0 < T0 θ lam * (1 - A) * (ρ₂ - ρ₁) := mul_pos (mul_pos hT (by linarith)) (by linarith)
  have hee : 0 < eff ρ₁ A * eff ρ₂ A := mul_pos he1 he2
  by_contra hc
  push_neg at hc
  nlinarith

/-! ### Finite stochastic version: `n` vehicles, each gliding independently with probability `p` -/

/-- Probability that the set of gliding vehicles satisfies `E`. -/
def prob (n : ℕ) (p : ℝ) (E : Finset (Fin n) → Prop) [DecidablePred E] : ℝ :=
  ∑ s : Finset (Fin n), if E s then p ^ s.card * (1 - p) ^ (n - s.card) else 0

theorem prob_total (n : ℕ) (p : ℝ) : (∑ s : Finset (Fin n), p ^ s.card * (1 - p) ^ (n - s.card)) = 1 := by
  rw [Fin.sum_pow_mul_eq_add_pow]; simp

/-- With a halting count, the signal misses a demand of `n ≥ θ ≥ 1` whenever too few vehicles halt; this has probability at least `p ^ n`
(every vehicle glides). -/
theorem miss_lower (n θ : ℕ) (hθ : 1 ≤ θ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ n ≤ prob n p (fun s => n - s.card < θ) := by
  unfold prob
  have hf : ∀ s ∈ (Finset.univ : Finset (Finset (Fin n))),
      0 ≤ (if n - s.card < θ then p ^ s.card * (1 - p) ^ (n - s.card) else 0) := by
    intro s _
    split_ifs
    · exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    · exact le_refl 0
  have h := Finset.single_le_sum hf (Finset.mem_univ (Finset.univ : Finset (Fin n)))
  have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hθ0 : 0 < θ := by omega
  rw [hc] at h
  simpa [hθ0] using h

/-- With adapter weight `A ≥ 1`, perceived demand (halted + A · gliding) is never below the true count. -/
theorem never_miss {n g : ℕ} {A : ℝ} (hA : 1 ≤ A) : (n : ℝ) ≤ ((n : ℝ) - g) + A * g := by
  have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  nlinarith

theorem hyps_satisfiable :
    bias 10 (1 / 2) (1 / 2) 0 = 20 ∧ bias 10 (1 / 2) (1 / 2) 1 = 0 ∧ bias 10 (1 / 2) (1 / 2) 2 = -20 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [bias, serveTime, T0, eff]

end

end CIGAMF.P13.CityThresholdQueueV1

#print axioms CIGAMF.P13.CityThresholdQueueV1.eff_pos
#print axioms CIGAMF.P13.CityThresholdQueueV1.bias_mul
#print axioms CIGAMF.P13.CityThresholdQueueV1.consistent_iff
#print axioms CIGAMF.P13.CityThresholdQueueV1.lengthening_iff
#print axioms CIGAMF.P13.CityThresholdQueueV1.shortening_iff
#print axioms CIGAMF.P13.CityThresholdQueueV1.allspeed_consistent
#print axioms CIGAMF.P13.CityThresholdQueueV1.bias_mono
#print axioms CIGAMF.P13.CityThresholdQueueV1.prob_total
#print axioms CIGAMF.P13.CityThresholdQueueV1.miss_lower
#print axioms CIGAMF.P13.CityThresholdQueueV1.never_miss
#print axioms CIGAMF.P13.CityThresholdQueueV1.hyps_satisfiable
