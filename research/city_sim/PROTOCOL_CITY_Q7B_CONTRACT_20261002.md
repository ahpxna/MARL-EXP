# PROTOCOL Q7b — Q7 across training seeds, the compatible-mode frontier, and a receiver-contract certificate
# (written 02/10/2026 23:0x EDT, before any Q7b run; after two external reviews verified in
#  research/papers/audits/CITY_TWO_POPULATION_NOVELTY_20261002.md §7)

## Why
Q7 (ledger C-7) trained ONE network per component (DQN seeds fixed at 11 / 13): its intervals cover evaluation traffic only.
The reviews propose that compatibility is receiver-relative and that a sound certificate needs a minimal receiver CONTRACT; Q7-3
(a receiver-free light statistic, 4.4 %) failed while the receiver-side τ out-of-support mass was 18.6 %.  Q7b asks: (1) does
Q7 replicate across training seeds; (2) what does the price-of-compatibility frontier look like over the forced-switch cap;
(3) does a certificate computed from the UPGRADER's own logs plus the receiver's published contract predict the regression,
where the receiver-free statistic does not; (4) where does the support contract fail (FT, the in-support conditional shift)?

## What this is NOT
SUMO grid4 with components we train; no real controllers, no J2735 traces, no independent vehicle stack, no real cross-version data.

## Setup (as Q7 unless stated; scripts/CITY_q7b_contract.py, which imports the Q7 classes unchanged)
* Training seeds t ∈ {1, 2, 3} (t = 0 is the Q7 run, re-evaluated, not retrained): for each t, RL-H_t (light, human traffic),
  L-ACT_t (fleet vs ACT), RL-J_t (light with L-ACT_t present); DQN init / exploration seeds 11 + 100 t and 13 + 100 t.
  L-RLH is not retrained (only needed for Q7-2's specialist reference; Q7b measures REGRESSION instead).
* Regression of the deployed fleet under a light U: r(U) = cost(L-ACT_t | U) − cost(L-ACT_t | ACT) (approach cost, the
  fleet's training objective), paired over evaluation seeds 100–104; the light's own gain g(U) = TL_ACT − TL_U with human traffic.
* Frontier: RL-C(c) = RL-H_t with a forced switch at c ∈ {30, 40, 50, 60, 80, 120} s, and c = ∞ (RL-H_t itself).
* Contract of the fleet (published by the receiver, no weights): its accepted time-in-phase region [0, τ_max] from its own
  training logs (the checkpoint's tmax) and its decision process (every agent car within 200 m decides once per second).
* Certificates, computed from the LIGHT's own human-traffic evaluation logs only (no cross-play):
  - K_free = share of green-seconds whose time in phase exceeds 50 s (Q7-3's receiver-free statistic);
  - K_contract = Σ_t Σ_approaches n(t) · 1[τ(t) > τ_max] / Σ n(t), n(t) = vehicles within 200 m of that approach's stop line
    (the contract's exposure model applied to the light's own logs).
  The cross-play reference: the fleet's measured out-of-support share of decision-time τ under U (Q7's tau_oos_mass).
## Predictions (fixed now)
* B1 (replication) for every t: RL-H_t beats ACT by ≥ 5 % with human traffic AND r(RL-H_t) > 0 with paired lower bound > 0.
* B2 (frontier) across c, g(RL-C(c)) is non-decreasing and r(RL-C(c)) non-decreasing in c (mean over t, one violation of size
  ≤ 1 s allowed per curve); some c ≤ 60 keeps ≥ 80 % of g(RL-H) with r ≤ ½ r(RL-H) (mean over t).
* B3 (contract beats receiver-free) over all evaluated lights except FT (RL-H_t, RL-C(c)_t, RL-J_t, ACT; all t): Spearman
  (K_contract, r) ≥ 0.7 and > Spearman(K_free, r); K_contract within a factor 2 of the cross-play out-of-support share for every
  light with share ≥ 5 %.
* B4 (the support contract is insufficient: registered exception) under FT, K_contract ≤ 0.02 while r(FT) ≥ 10 (approach-cost
  units): an in-support regression, i.e. a contract cell without a common safe action — the case a semantic / intent field must
  cover (T2 of §7).
Kill rules: B1 failing for any t means Q7's single-seed result is not robust and Q7 is downgraded to an illustration; B3 failing
means the receiver contract (region + exposure) is not the decision-sufficient object either.

## Outputs
research/city_sim/q7b_contract_20261002/ (checkpoints per t, eval rows, light logs, report.txt); smoke first; queued after the
fallback queue (CPU), via a detached queue script.

## Amendment 1 (02/10/2026 23:0x EDT; after the pipeline smoke only — no production Q7b run exists)
* Deconfounding FT (H4 of research/papers/audits/FAILURE_SYNTHESIS_20261002.md): a fleet L-FT_t trained against the static FT
  program (DQN seed 13 + 100 t; t ∈ {0, 1, 2, 3}, t = 0 trained new) is evaluated under FT only.  B4' replaces B4's harm
  reference: the mismatch m(FT) = cost(L-ACT_t | FT) − cost(L-FT_t | FT) (paired) ≥ 10 for the mean over t, with K_contract(FT)
  ≤ 0.02.  B4' → an in-support, decision-relevant conditional shift exists in SUMO; B4' failing → FT is simply a worse light and
  the semantics half stays unsupported (as in C0's CUT).  B4 is kept and reported.
* B5 (H5: a producer-side contract is cheap iff it removes only behaviour OUTSIDE the receiver's support): with the price
  p(c) = 1 − g(RL-C(c)) / g(RL-H) (mean over t), p(50) ≤ 0.15 and p(60) ≤ 0.15 (caps at or above the fleet's τ_max = 50 cost
  little), p(30) ≥ 2 p(50) (constraining in-support freedom is expensive), and r(30) ≥ 0.5 r(50) (going below τ_max buys little
  more compatibility).

## Note (23:1x, before the production run): what the pipeline smoke revealed
The smoke evaluated the REAL t = 0 (Q7) checkpoints for 900 s on seed 100: RL-H K_free 0.046, K_contract 0.036 (human traffic),
K_contract 0.131 with the fleet, cross-play out-of-support 0.19.  Predictions B1–B5 are unchanged; t = 0's B3 is no longer
blind (disclosed).  Added as a REPORTED quantity (no rule): K_contract computed from the light's logs WITH the frozen fleet
present (the closed-loop certificate of H2b) vs the cross-play out-of-support share.
