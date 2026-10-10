# PROTOCOL — M3: upgrading the light while keeping the deployed fleet's benefit (04/10/2026 17:18; DRAFT, registered before any M3 run)

Milestone M3 of `TWO_POPULATION_PAPER_FINISH_LINE_20261004.md`. It follows the user's choice of candidate E (17:05) and the corrections of `…/catchup/M3_E_VS_COMMITMENT_AND_ORACLE_AUDIT_20261004.md` and `M3_BEFORE_LAUNCH_REVIEW_20261004.md` (ledger C-60…C-63).

E is a **pilot candidate**:
- no novelty claim, and no claim that it beats B;
- it becomes a method contribution only if it passes the gate in §7 against ordinary fine-tuning (E0) and the same-rights comparators.

## 0. Question and the result we would accept

Setting: the light is upgraded to a learned controller (RL-H, a large upgrade: city TL −33.7 s/veh vs FT). The deployed fleet (R10, PPO, FROZEN) loses its own benefit: no SPaT gives 0; a program-derived or empirical forecast harms it (C-59, C-62).

**Target claim, if confirmed:** a light update that keeps a measured part of the frozen fleet's fuel benefit, within locked time-loss limits for agents, humans and the city, at a lower system cost than:
- plain fine-tuning;
- forecast-only service;
- fixed-window or ETA commitment.

Not targeted: recovering the full FT-era premium (the opportunity changed with the light, C-63 (1)).

## 1. Populations, rights and seeds

| Item | Specification |
|---|---|
| Fleet (receiver) | R10 PPO residual on GLOSA-L∘σ\*, weights FROZEN; base driver σ\* = 0.3; lane-aware release. Development fleets: L11_s13, L11_s113 (M1 pilot seeds). Confirmation fleets: L11_s213 / s313 / s413 / s513, never used in M3 development. Transfer checks (development only, descriptive): R9 θ_s1 and the R8 rule GLOSA-L∘σ\*. |
| Light (producer) | Initial checkpoint RL-H:k (DQN keep/switch, 7-dim observation, decision every DT_L = 5 s after MIN_G = 5 s, yellow 3 s). Development light seeds k = 0, 1; confirmation light seeds k = 2, 3. |
| Rights | All E arms may update the LIGHT's weights (same budget). No arm may update the fleet. Commitment arms may constrain the light's actions but not retrain it. Forecast arms may neither retrain nor constrain the light. |
| Traffic | Training: TRAIN 0–7. Development (DEV) evaluation: SELECT 100–104 plus 200–209 (C-32 VALIDATION, already used for older lights only; declared). Confirmation: FRESH 510–529, generated after this protocol is frozen. 300–319 stay reserved. |
| Pairing in confirmation | CROSSED: 2 light seeds (fine-tuned from RL-H:2 and RL-H:3) × 4 fleet seeds × 20 traffic. The bootstrap resamples light seed, fleet seed and traffic separately (R.draws over a 3-axis cube). This is not 8 independent pairs. |

## 2. Message semantics (every arm logs every message)

Each published message carries:
- a movement (intersection, link);
- an event: the next green onset, or the end of green;
- an issue time and a horizon;
- a TYPE.

| TYPE | Meaning | Validity rule |
|---|---|---|
| `forecast:q` | the q-quantile of a CALIBRATED causal forecast of the event time | refit and calibrated with the identical procedure in every arm (§4); calibration reported (coverage, MAE at the fleet's actual query times) |
| `commitment` | the light WILL produce the event at the stated time; issued W s ahead; no cancellation | violations must be 0 by construction (self-check S5) |
| `unavailable` | no information; the fleet falls back to σ\* | — |

No arm may publish a number that is not one of these (no "advisory" times tuned to steer the receiver while labelled as SPaT; audit §5). The fleet consumes `ttg` and `ttr` only, as frozen: a forecast or commitment gives its point value; `unavailable` gives `valid = False`.

## 3. Arms

### 3a. Light-update arms (candidate E and its controls)

Common to all four:
- same initial checkpoint RL-H:k;
- same DQN fine-tuning recipe: buffer empty at start; ε = 0.05 constant; γ 0.9; 200 updates per episode; target soft update 0.01; Adam 1e-3, as in the original recipe;
- **60 episodes** on TRAIN 0–7 in rotation, 3 600 s;
- the frozen DEVELOPMENT fleet L11_s13 in the loop, receiving the RL-H:k forecast `forecast:0.5` (§4);
- same base reward r_base = −(halting vehicles on the incoming lanes)/10 at each decision (the RL-H reward);
- the LAST checkpoint is the result.

The arms differ only in the penalty added at each decision:

| Arm | Reward |
|---|---|
| **E0** | r_base. Ordinary fine-tuning / best response to the frozen fleet. |
| **E-uniform** | r_base − λ·1·dev |
| **E-ETA** | r_base − λ·w_ETA·dev |
| **E-receiver** | r_base − λ·w_rec·dev |

λ ∈ {1, 4} for the three penalised arms. The grid is FIXED here. 7 arms × 2 development light seeds = 14 runs.

**Deviation `dev` (anti-gaming, audit §4.3).**
- At every decision of light j in green g, the reference is the forecast published L = 10 s earlier for the end of this green: T̂ = t_issue + r̂_0.5(spent at t_issue), from the FIXED RL-H:k forecast table.
- If a = switch at time t < T̂ − τ: dev = (T̂ − t)/10 (early switch).
- If a = keep at time t > T̂ + τ: dev = DT_L/10 (late, per decision). τ = 2 s.
- Otherwise dev = 0.
- Publishing is mandatory and the table is fixed during training, so dev cannot be avoided by not publishing or by revising the message.

**Weights** (at decision time, from the light's own sensors plus the fleet's V2I telemetry; declared):
- **w_ETA:** the number of FLEET vehicles approaching j whose ETA = dist / max(speed, 1 m/s) is in [5, 25] s, on ANY movement of j. Distance, speed and membership only.
- **w_rec:** Σ over fleet vehicles v approaching j on a link served by the OTHER green g′ (red now, so the vehicle's frozen policy is ACTIVE and consumes ttg) of |cmd_v(ttg_v + 1) − cmd_v(ttg_v − 1)| / 2.
  - This is the frozen receiver's command sensitivity to the time-to-green it is being told, computed by evaluating the frozen fleet policy (rule + residual network, deterministic mean) at two ttg values.
  - Receivers that are released (green, wrong lane, outside 200 m) contribute 0.
  - This is a PROXY for dependence on SPaT, not a physical regret (audit §4.2). It uses fleet telemetry at decision time (state, distance, speed) plus the published policy of the deployed fleet. Known to the infrastructure by assumption: the operator has the fleet's frozen policy, which is a declared information right.

**Cost of information:** both weights need fleet V2I telemetry; w_rec also needs the fleet policy. Reported as an information right, not counted as free.

### 3b. Comparators without light retraining (same evaluation)

| Code | Arm | Notes |
|---|---|---|
| F-none | RL-H:k + `unavailable` | Fleet = σ\*. The REFERENCE system. |
| F-50 / F-q\* | RL-H:k + `forecast:q` | Empirical forecast (C-62). q\* chosen on DEV from {0.1, 0.2, 0.3, 0.5} (forecast-quantile adapter: honest, a forecast quantile). |
| D | RL-H:k + policy-aware forecast `forecast:D` | Adaptation of HONEST-CAV §III-B to keep/switch: at time t, for h = 5, 10, …, 60 s, evaluate the light's own Q-network on the CURRENT queue features with spent advanced by h. Predicted remaining green = the first h with Q(switch) > Q(keep); if none, fall back to the empirical median. No queue rollout (declared limitation: queues are held constant). Calibrated with the same procedure. |
| W-c | Fixed-W commitment, W ∈ {5, 10, 15} s | RL-H:k decides as usual, but a switch decided at t is EXECUTED at t + W. The green continues meanwhile; a new decision is not taken while a switch is pending. `commitment` for the switch is published at t; before a switch is decided, `forecast:0.5`. |
| B-ETA | ETA commitment (B, small) | When RL-H:k decides to switch, it executes immediately unless a fleet vehicle with ETA ∈ [5, 20] s is approaching on the red movement. In that case the switch is delayed and committed W_B s ahead, W_B ∈ {10, 15}. |
| P-cyc | Tuned predictable schedule | A fixed-time 2-phase cycle with green G per phase, G ∈ {10, 15, 20, 25, 30} s, tuned on DEV for city TL with σ\* cars. SPaT exact (`commitment` of the whole cycle). |
| Refs (other rights) | FT rollback; R10 under FT | Reported separately, not same-rights competitors. |

## 4. Forecast refit and calibration (identical across arms; audit §4.4)

Every arm that publishes `forecast:*` uses a table refitted to ITS OWN deployed light with one procedure:
- record phase traces on TRAIN 0–7 with σ\* cars (8 episodes);
- fit with `CITY_spat_forecast.fit` (code unchanged);
- calibrate on DEV traces;
- report MAE, bias and [q10, q90] coverage at the fleet's ACTUAL query times (a logger in the evaluation records forecast and realised event per query).

E arms deploy `forecast:0.5` from their refitted table. Same refit budget for E0 and every E arm.

## 5. Endpoints (fuel primary; locked before any run)

Reference system R = (RL-H:k + `unavailable`) with the frozen fleet, i.e. RL-H:k with σ\* agents.

| Endpoint | Content |
|---|---|
| **M3-1 (primary)** | Absolute agent fuel % of (arm, fleet) vs R. |
| M3-2 constraint (ALL required) | City TL vs R: upper < +0.5 s/veh (the locked city-TL budget). Agent TL upper < +0.5. Human TL upper < +0.5. Teleports ≤ R + 1 per run. Unfinished ≤ R. |
| M3-3 (fleet contribution) | (arm, fleet) vs (arm, σ\* cars). |
| M3-4 (light-side cost) | (arm, σ\* cars) vs (RL-H:k, σ\* cars): city TL, city fuel. For E arms trained with the fleet, the light is evaluated with σ\* cars as declared. B-ETA with σ\* cars has no requests, so its cost is measured WITH the fleet and reported as such. |
| M3-5 (message quality) | Forecast MAE at query times; commitment violations (must be 0); coverage and lead time of messages; commanded vehicle-seconds. |

## 6. Development screen (DEV) and selection rule

Every E arm (14 runs) and every comparator setting is evaluated on DEV traffic with development fleets L11_s13 and L11_s113 (crossed with light seeds 0 and 1).

Selection, mechanical, written now:
- Among the arms that pass M3-2 on DEV, the best M3-1 point estimate within each family is selected:
  - E-receiver (λ);
  - E-uniform (λ);
  - E-ETA (λ);
  - E0;
  - the best comparator overall (F-q\*, D, W-c (W), B-ETA (W_B), P-cyc (G)).
- If no arm of a family passes M3-2, the family's best M3-1 is still carried, marked infeasible.
- The selected E-receiver λ, and the best feasible comparator, are FROZEN before generating 510–529.

## 7. Confirmation and the method gate

On fresh 510–529, crossed (2 light seeds k = 2, 3, each fine-tuned with the FROZEN selected recipe) × (4 confirmation fleets) × 20 traffic.

**E-receiver is accepted as a method only if all of the following hold:**
- **(G1)** it passes M3-1 superiority (upper < 0) and all M3-2 constraints vs R;
- **(G2)** E-receiver − E0 on agent fuel: upper < 0, with M3-2 constraints for both;
- **(G3)** E-receiver − E-ETA: upper < 0;
- **(G4)** E-receiver − best comparator: upper < 0, or equal agent fuel (|Δ| < 0.5 %) at a lower city-TL cost (upper of Δ city TL < 0).

Reading the outcomes:

| Outcome | Reading |
|---|---|
| G1 holds, G2 fails | Plain fine-tuning suffices. No evidence for the new penalty. |
| G2 holds, G3 fails | The cheap ETA proxy is as good. The receiver-model part is not worth it. |
| The best comparator wins | Report it as the method candidate (forecast or commitment), whatever was preferred. |
| Nothing feasible | M3 not met. No threshold is changed after TEST. |

## 8. Self-checks (exit 1; before the DEV screen)

| Check | Content |
|---|---|
| S1 | E fine-tuner with 0 episodes ≡ RL-H:k (rows bit-identical, traffic 0). |
| S2 | W-c with W = 0 ≡ RL-H:k. B-ETA with no fleet ≡ RL-H:k. |
| S3 | `dev` and both weights recomputed offline from a logged decision trace equal the online values. w_rec = 0 when no fleet vehicle is active. |
| S4 | The forecast refit procedure reproduces the M2b table for RL-H:k exactly (same traces → same JSON hash). |
| S5 | Commitment violations = 0 over a full episode (log of every commitment and its realised event). |
| S6 | No future access in any control path. The KM2b-1-style probe confirms that the online inputs equal the recorded trace. |
| S7 | The runner exits non-zero on any missing row or seed, and the report refuses incomplete files. |
| S8 | Checkpoint hashes (fleet and light files, not only scripts) are recorded in every row's provenance. |

## 9. Pseudocode

```
finetune_E(k, arm, lam):                          # arm in {E0, uniform, ETA, receiver}
  net <- RL-H:k weights; tgt <- net; buffer <- empty; table0 <- forecast table of RL-H:k (fixed)
  for ep in 0..59: seed = TRAIN[ep % 8]
    run 3600 s: light = LightRL(policy = eps-greedy(net, 0.05)); fleet = frozen L11_s13 with SPaT = forecast(table0, 0.5)
      at each light decision (t, j, g, spent):
        r_base = -halting_j / 10
        That   = issue(t - 10) + rhat_0.5(spent at t - 10)          # logged publication, table0
        dev    = (That - t)/10 if a == switch and t < That - 2 else (0.5 if a == keep and t > That + 2 else 0)
        w      = {E0: 0, uniform: 1, ETA: w_ETA(j), receiver: w_rec(j)}
        r      = r_base - lam * w * dev
    add transitions; 200 DQN updates
  return net (last)

w_rec(j): sum over fleet v approaching j, on a link served by the other green, rule ACTIVE:
            |cmd_v(ttg_v + 1) - cmd_v(ttg_v - 1)| / 2      (frozen R10: rule + residual mean)
```

## 10. Predictions (registered; priors are honest, not targets)

| # | Prediction |
|---|---|
| P-M3-1 | E0 does not reach M3-1 (agent fuel vs R ≥ −1 %): ordinary fine-tuning does not target the receiver's information. |
| P-M3-2 | E-uniform improves forecast MAE at query times vs E0, with a light-side cost (city TL ≥ +0.3). |
| P-M3-3 | On DEV, E-receiver ≥ E-ETA ≥ E-uniform in M3-1 at feasible λ. |
| P-M3-4 | W-c recovers agent fuel but at a larger city-TL cost than E-receiver at matched agent fuel. |
| P-M3-5 | Prior that E-receiver passes all of G1–G4 on confirmation: low-to-moderate, recorded so that a failure is not a surprise. |

## 11. Not in M3

Retraining the fleet; a learned L0 (not on the critical path; audit §6); new Lean modules; a second network (M4, after M3).

---

## Amendment A1 (17:56, before any M3 code or run; responds to `…/catchup/M3_PROTOCOL_D1D76226_PRE_SCREEN_REVIEW_20261004.md`; supersedes the conflicting lines of d1d76226)

**B1. Common PHYSICAL base reward for every E arm; E0 = λ 0.**

All E arms optimise the same physical reward. The queue reward of RL-H is used by none of them. For light j, over the interval [t, t′) between its consecutive decisions:

r_phys = − Σ_{seconds in [t, t′)} Σ_{vehicles on j's incoming lanes} c / (10 · DT_L), with c = max(0, 1 − v / v_lane) + 0.5 · fuel[mg/s] / 1000

- v is the REALISED speed (`getSpeed`) and fuel is `getFuelConsumption`. No commanded speed enters.
- All vehicles count (agents and humans). Invalid readings are skipped and counted.
- The constants are fixed here, with no reward tuning.
- E0 is the same trainer with λ = 0. There is no separate E0-queue arm.

**B2 + B3. Event tickets and action-local credit.**

Event = the END of green occurrence o of light j (the decision to switch; yellow onset).

*Tickets.* At every decision tick during o, the light publishes a ticket k = (j, o, issue time t_k, promised end T̂_k, weights w_k):
- T̂_k = t_k + r̂_0.5(spent) from the provider of the current block (B6);
- w_k holds the uniform / ETA / active / receiver weights, all measured AT ISSUE.
- Tickets are never replaced or deleted before the event.

*Open tickets at decision t* are those of the current occurrence with t − 20 ≤ t_k ≤ t − 5: old enough to have been acted on, and recent enough to matter.

*Penalty of the CURRENT action a_t*, using the arm's weight w:
- **keep:** pen = Σ_k w_k · max(0, (t + DT_L) − max(t, T̂_k + τ)) / 10. These are the late seconds this keep creates, so a long keep across a deadline is integrated.
- **switch:** pen = Σ_k w_k · max(0, T̂_k − τ − t) / 10. These are the early seconds.
- τ = 2 s.
- No open ticket (a startup or a green shorter than 5 s): pen = 0, counted.
- An occurrence still open at the end of the episode is censored: no further penalty, counted.

*Credit.* At decision t the trainer stores PENDING (o_t, a_t, pen_t). At the light's next decision t′ it closes:

(o_t, a_t, r_phys[t, t′) − λ · pen_t, o_t′)

The penalty is therefore attached to the action it scores. A switch's interval spans yellow + MIN_G. The last pending transition of an episode is dropped, as in LightRL. Self-check **S9** verifies this.

**B4. Weights on a common scale; a new active-count control; the policy SEES the ticket state.**
- *Weight types:*
  - uniform = 1;
  - ETA-any = the number of fleet vehicles approaching j with ETA in [5, 25] s, on any movement;
  - **active-count** (NEW control) = the number of fleet vehicles in the receiver's eligible set (approaching on the red movement, rule active), i.e. the same mask as the receiver arm with weight 1 per vehicle;
  - receiver = Σ |∂cmd/∂ttg| over the eligible set (B5).
- *Scale.* Each raw weight is divided by its MEAN over all tickets of ONE fixed pre-fine-tune trace: RL-H:k with the dev fleet L11_s13 and the RL-H:k provider, TRAIN 0–7, one pass. The normalised weights then have mean 1 on that trace. They are clipped at 10.
  - Reported per type: zero share, mean, p95, max, and the penalty / base-reward ratio on that trace.
  - A type whose mean is 0 is disabled and reported.
  - The scale is never re-estimated from a policy's own results.
- *Arms:* E0 (λ 0); E-uniform, E-ETA, E-active, E-receiver, each with λ ∈ {1, 4}. That is 9 runs per light seed. The number of tuning configurations is equal across penalised arms.
- *Visibility (the review's option 2).* EVERY E arm, E0 included, gets the same 5 extra inputs at its decisions:
  - the number of open tickets / 4;
  - the mean (T̂_k − t) over open tickets / 30;
  - the open tickets' receiver, active and ETA weight sums, each / 4 after normalisation.
  - The first layer is widened with ZERO-initialised columns for the new inputs, so the widened RL-H:k reproduces RL-H:k exactly (**S12**).
  - All arms have the same information; only the penalty weight differs.

**B5. Receiver sensitivity = the actual frozen fleet command.**
- `cmd(ttg′)` is computed by a PURE probe on a snapshot. The same ttg′ is substituted in BOTH places where R10 uses it:
  - the rule speed min(v_allowed, d / ttg′);
  - observation feature 10 (`V8.build_obs` calls spat, which is rebound for the probe).
- Lane release, the speed clamp and the valid mask are kept as in v11. The policy mean is used (no RNG). The probe makes no `setSpeed` call and touches no fleet counters (a dummy stats dict).
- Central difference with h = min(1, ttg / 2): |cmd(ttg + h) − cmd(ttg − h)| / (2h).
- Weights are stored WITH the ticket at issue (B2).
- **S11** checks: the probe's cmd(ttg) equals the command R10 actually sends that second (evaluation mode); perturbing ttg changes BOTH rule and observation; zero side effects.

**B6. Forecast provider lineage, the same for every arm.**
- Training is run in three blocks of 20 episodes, and the provider is frozen within a block:
  - block 1 uses the RL-H:k provider;
  - after blocks 1 and 2, the provider is REFITTED from 8 TRAIN episodes of the current checkpoint, with the dev fleet in the loop (closed loop), using `CITY_spat_forecast.fit` unchanged;
  - block 3 trains with the FINAL provider, which is also the one deployed, so train and deploy use the same provider.
- **No separate calibration step.** The forecast is the empirical conditional quantile of the fitting data. "Calibrate on DEV" (d1d76226 §4) is withdrawn. DEV coverage and MAE are reported as in-sample diagnostics; final quality is measured on the confirmation panel at the fleet's query times.
- F-q\* uses a provider for RL-H:k refitted by the SAME closed-loop procedure (8 TRAIN episodes, dev fleet).
- **D** outputs a point forecast. It is NOT called a quantile, and its error is reported. h starts at the light's next decision tick (the fleet steps after the light in the same second); h = 0 is the case "a switch is decided now", already visible to the fleet as yellow.
- W-c publishes both the green end T_s = t + W and the movement's green onset T_s + 3 + OBS.
- **S13** checks provider lineage: the checkpoint, table and runtime hashes match, and no confirmation-panel label is read.

**C1. Gate (replaces §7).**

Primary method gate on confirmation: **superiority on agent fuel** (upper < 0) of E-receiver vs each of:
- R (G1, together with all M3-2 constraints);
- E0 (G2);
- E-uniform (G3);
- E-ETA (G4);
- E-active (G5);
- the best DEV comparator (G6).

G2–G6 also require E-receiver to satisfy M3-2. Reading:
- A failure of any of G2–G6 means "advantage over X not shown". It is NOT "equal".
- An equivalence statement needs TOST with bounds ±0.5 % agent fuel, using a 90 % CI inside the bounds. TOST is a SECONDARY analysis and never a route through the gate.
- If a comparator is infeasible under M3-2 while E-receiver is feasible, this is reported as a feasibility advantage (secondary).
- Every selected λ, provider and comparator setting is frozen before 510–529 is generated.

**C2. Light seeds.**
- DEV: RL-H:0 and RL-H:1.
- Confirmation: **five NEW independent light seeds**, RL-H_t for t = 4…8, trained now with the frozen Q7b recipe (`CITY_q7b_contract.py --train-light RL-H --t T --episodes 120`, DQN seed 11 + 100 t) into a new directory. This happens before any M3 result and is not inspected beyond the training log.
- Crossed with the 4 confirmation fleets × 20 traffic. The bootstrap is over light seed, fleet seed and traffic.
- If a confirmation light checkpoint is not beneficial over FT (city TL), it is still used, and this is reported.

**C3. Constraints, B's label and P-cyc.**
- *Teleports.* The d1d76226 rule "≤ R + 1 per run" is REPLACED by: the arm's MEAN teleports per run ≤ R's mean + 0.1, with the bootstrap upper bound reported.
  - The worker's 17:20 message said "no increase". That wording was wrong. A 0.1 margin is now explicit.
  - Unfinished: the total is ≤ R's total.
- *B-ETA.* Fleet-on vs fleet-off is labelled the JOINT system effect (the controller changes when requests exist). It is not attributed to the fleet.
- *P-cyc.* Each G in {10, …, 30} is evaluated WITH the fleet on DEV and selected by the common rule (§6). The TL-optimal cycle under σ\* is reported separately as a reference.

**Added self-checks.**

| Check | Content |
|---|---|
| S9 | Credit trace on synthetic sequences (early switch, long keep, through yellow, episode end): every (o, a, r, o′) is assembled with the penalty of a, never of the previous action. |
| S10 | Event tickets on toy traces: green < 5 s, early switch, repeated issues, multi-cycle; no ticket lost at a phase change; censoring at the end. |
| S11 | Command parity of the sensitivity probe (B5). |
| S12 | Scale table on the common trace, and zero-init widened input ≡ RL-H:k. |
| S13 | Provider lineage (B6). |
| S14 | Reporter logic on synthetic inputs: point-close values never PASS equivalence; missing seed → error; infeasible handled; NI uncertainty used. |

**Unchanged:** E as the candidate; 60 episodes (as 3 × 20); L = 10 is replaced by the [5, 20] s open-ticket window above; τ = 2; LAST checkpoint; DEV / confirmation split; message types; M3-1 and the other M3-2 limits.

### Amendment A1b (18:02, before any M3 run; after the user's question on E0-queue)

**Two E0 arms (cost: +1 run per DEV light seed, 10 per seed in total):**

- **E0-physical** = the λ = 0 arm of A1 B1 (physical base reward). It is the task-targeted competitor in gate G2.
- **E0-queue** = the same trainer with λ = 0 and the ORIGINAL RL-H reward −(halting vehicles at the decision)/10. It is credited exactly as in LightRL: the reward observed at the next decision is attached to the previous action.
  - It is a reward-shaping / base-reward control: does fine-tuning on the physical reward make the light better or worse than fine-tuning on its own reward?
  - It is NOT in the gate, and it is reported beside E0-physical.

Penalised arms keep the physical base (A1 B1), so that E-x vs E0-physical isolates the penalty.

Physical-reward lock, restated:
- c per vehicle-second = max(0, 1 − v / v_lane) + 0.5 · fuel[mg/s] / 1000, with realised `getSpeed` and `getFuelConsumption` only (never a commanded speed: the C-13 / C-17 lesson);
- every vehicle on the light's incoming lanes (each lane feeds exactly one light, so nothing is double-counted);
- summed over the seconds of the decision interval and scaled by 1 / (10 · DT_L);
- no reward tuning.

**Pending, not adopted:** a two-tier gate, proposed by the worker and awaiting the user's decision.
- Tier 1, the "method helps" claim: E-receiver vs R, E0-physical and the best comparator.
- Tier 2, the "receiver-awareness helps" claim: vs E-uniform, E-ETA and E-active.

Until it is adopted, the A1 C1 gate stands.

### Addendum A2 (20:08, post-DEV corrective measurement; registered before it runs; C-69 / C-70)

**Why.** The DEV quantities M3-3 (fleet contribution) and M3-4 (light-side cost) are NOT clean for E arms. With σ\* cars the E light's receiver / active inputs are 0, a regime it never saw (C-70).

**Clean measurement: a SHADOW fleet.**
- The R10 dev fleet's policy net is present for the light's input computation: tickets and weights are computed from the R10 policy on the actual vehicle states, with the deployed provider. So the input FUNCTION is exactly the deployment one.
- The member cars DRIVE as σ\* = 0.3 (setImperfection at departure). No command is ever applied.

**Rows** (each E checkpoint, 20 in total; shadow nets of L11_s13 and L11_s113; DEV traffic 15 seeds):
- **M3-4clean** = (E light + shadow) − (RL-H:k + σ\* cars), i.e. the light-side cost with deployment-equivalent inputs. The light's realised inputs still follow the σ\* traffic state.
- **M3-3clean** = (E light + R10 driving) − (E light + shadow), i.e. the fleet's contribution under an identical input definition.
- Reported per arm with the crossed bootstrap (k × shadow fleet × traffic). These are DESCRIPTIVE, M3 is closed (C-69), and no selection or gate uses them.
- Also reported: whether the C-68 σ\*-condition gridlocks recur.

**Checks (exit 1):**
- SH-1: RL-H:k with the shadow fleet ≡ RL-H:k with σ\* cars (bit-identical; the shadow never commands).
- SH-2: under the shadow, the E light's receiver and active ticket weights are non-zero. Reported: their mean vs the fleet-driving run.
