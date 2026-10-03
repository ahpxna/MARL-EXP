# PROTOCOL Q6 — rule A in a V2I domain: a prospective cross-domain test of the provisioning law (written 02/10/2026 19:3x EDT,
# before any run)

Plan: research/city_sim/PLAN_CITY_IDEAS_20261002.md (idea 2).  Theory used as is (not re-proved): LeanMarlReceiverFloorV1 / V2
(every scheduler), LeanMarlNetFloorV1, LeanMarlProvisioningV1 (net ≤ K(τ + 2) − (m − 1); K_min = (1 + θ)(m − 1)/(τ + 2)).  The
empirical sign rule of E3 (gain over compiled silence > 0 iff net / (m − 1) > θ, θ = −0.08 frozen on the 3×3 cells, prospective
on 4×4: C-rel 3/3, L-270) is tested here on a different receiver, task and channel, with every parameter frozen now.

## Model
* A car at a decision point chooses one of m = 8 routes; route i crosses one light at distance d_i ~ U[100, 400] m (known), cruise
  12 m/s; the light runs the C0 renewal law ACT = U{20..40} s per phase, independent across routes.  Route cost = d_i / 12 + the
  red wait at arrival.  Teacher (privileged) knows the realised schedules.
* Channel: each light's SPaT record (colour, time in phase) reaches the car through an age-first broadcast of K records per second
  (the scheduler that attains the floor); at the decision the car holds, per route, the record with its age.  Training channels
  K_train ∈ {1, 2, 4, 8} and IID (K ~ U{1..8} per second); deployment K ∈ {1, 2, 3, 4, 8}.
* Compiled silence: the exact no-message optimum (argmin of the expected cost given d_i alone under the stationary light: the
  shortest route).  Learned message car: an MLP (shared over routes, input d_i, colour, time in phase, age) regressing the
  realised route cost; argmin over routes.  200 000 training and 50 000 evaluation decisions per cell; seeds 0–2.
* Gain(K_train, K) = 1 − regret(message car) / regret(compiled silence) (regret against the privileged choice).
* Count (channel only): at the decision, fresh = records of age 0, stale_τ = records older than τ (τ = the training channel's
  maximum record age); net = fresh − stale_τ; with m senders, the rule reads gain > 0 iff net / m > θ = −0.08 (the receiver is
  not a sender here, so m replaces m − 1).
## Predictions (fixed now)
* V1 sign rule: the sign of the mean net / m − θ (deployment channel, mean over decisions) predicts the sign of the mean gain in
  ≥ 80 % of the (training, deployment) cells with a measured gain outside ± 0.02.
* V2 provisioning: for each constant training channel, no deployment K ≤ K_min = (1 + θ) m / (τ + 2) has a gain > + 0.02.
* V3 (reported) IID-trained receiver: gain at every deployment K (the mixture repair); the upgrade direction (K_train = 1 deployed
  at K = 8).
Kill rule: if V1 < 60 %, rule A does not transfer to this domain and is reported as E3-specific.

## Outputs
research/city_sim/q6_v2i_floor_20261002/ (cells.json, report.txt); scripts/CITY_q6_v2i_floor.py; smoke first.
