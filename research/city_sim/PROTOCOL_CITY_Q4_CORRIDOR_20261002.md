# PROTOCOL Q4 — staggered corridor upgrades: per-light compatibility is not corridor compatibility (written 02/10/2026 19:1x EDT,
# before any run)

Plan: research/city_sim/PLAN_CITY_IDEAS_20261002.md (idea 4).  Reuses the C0 v3 testbed (scripts/CITY_c0_testbed.py: privileged
DP regret, exact Bayes tables, students, DAgger) through a new driver, scripts/CITY_q4_corridor.py.

## Model
* Two consecutive fixed-time lights, 30 s green / 30 s red each (cycle 60).  A car passes light 1 at a time s ~ U{0..29} into
  light 1's green; the C0 episode then starts at distance L0 ~ U{150..250} m from light 2 with v0 ~ U{8..12} m/s.  Light 2's
  green starts O s after light 1's: at the start, light 2 is at cycle position (s − O) mod 60.
* Training corridor OLD: O = 15 (a green wave).  Upgraded corridors (light 2 alone re-timed; its OWN timing law unchanged):
  O ∈ {20, 25, 30, 35, 45} and RANDOM (O ~ U{0..59} per episode).
* By construction light 2's own log is the same fixed-time 30/30 in every corridor: the single-light certificate of Addendum C0b
  is K = 0 for all.  The corridor certificate is the total-variation distance between the distributions of light 2's
  (colour, time in phase) at the car's start under OLD and under the new corridor — computable from the two lights' logs and
  light 1's release window, with no car policy.
* Because light 2 is deterministic, the exact Bayes table Z*_FT is the privileged optimum on every corridor (regret 0): any harm
  is the learned receiver's training-state support, not the light's semantics.
* Students: Z and M (C0 v3 recipe: Bayes-table labels, ε-noisy table driver, 2 DAgger rounds) trained on OLD-corridor episodes;
  specialists trained on each new corridor; seeds 0–2; 3 000 training and 3 000 evaluation episodes per corridor (evaluation
  seeds 9 400 + index).  Monitors on Z_OLD: the range monitor (τ above the training maximum) and a density monitor (share of
  decision steps whose (colour, τ, 10 m distance bin, speed) cell was visited < 5 times per 10⁵ training states).
## Predictions (fixed now)
* Q4-1 Δ(RANDOM) = regret(Z_OLD on RANDOM) − regret(Z_RANDOM on RANDOM) > 0 (bootstrap lower bound > 0), while Z*_FT has regret
  0 on every corridor (exact).
* Q4-2 over the six new corridors, Spearman(corridor TV, Δ) ≥ 0.8; the single-light K = 0 everywhere (reported).
* Q4-3 (reported) the range monitor fires on 0 % of steps in every corridor; Spearman(density-monitor share, Δ).
* Q4-4 (derived, reported) staggered rollout on a long corridor where upgraded lights are coordinated among themselves (O = 15)
  but not with old ones: per approach the boundary pairs carry Δ(RANDOM), all others 0, so the expected harm is 2f(1 − f)·Δ(RANDOM)
  at rollout fraction f — largest at f = ½, zero at f = 0 and f = 1.
Kill rule: if Q4-1 fails (no harm from the offset change alone), idea 4 is reduced to the conditional-shift case already in C0.

## Outputs
research/city_sim/q4_corridor_20261002/ (cells, report.txt); smoke first.
