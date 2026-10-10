# PROTOCOL WAVE 12: stronger comparators and causal diagnostics (registered 06/10/2026 05:5x, before any wave-12 code ran)

**Why:** the user, 05:4x, pasted a plan with four steps (DCA-task, PPO-0/FoRL control, spider oracle replay S1, follower intervention S2) and wrote "làm các việc này thử đi, m coi có cách nào tốt hơn ko?".
- Nothing here changes a registered verdict of waves 1–11.
- Every result below is a follow-up study, chosen after DCA3 and W11 were read, and is labelled as such in the paper.

**Order:** by cost and by how much each step decides the next. W12-1 (minutes) → W12-2 diagnosis (minutes) → W12-4 DCA-task (hours) → W12-3.
- Each step's detailed specification is registered here, or as an amendment, before its code runs.

**Common to all steps:** PYTHONHASHSEED=0, OMP_NUM_THREADS=1, smoke run through the report first, the queue spool, disk guard 15 GB. Nothing is selected on a confirmation panel.

## W12-1 FoRL control: PPO-0 (fully specified)

**Question:** is the minimum-green collapse of the W11 FoRL signals caused by the forecasting penalty, or by the shared PPO recipe and reward of the port?

**Arm PPO-0:** `scripts/CITY_forl.py` with `--kappa 0`. Same architecture (256-256, MultiDiscrete L = 5), same observation (RL-H's 7 inputs plus the previous forecast), same environment reward, same seeds 1–5 (hence the same initialisation), same 200 episodes. Only the forecast-mismatch penalty is removed (λ is 0 in both).
- Code change: a `--kappa` option only, default −0.25. With the default the trainer is unchanged; the checkpoint records kappa.

**Evaluation, fresh grid4 traffic 860–879, which W11 already generated** (nothing is tuned on it; R, TSI2, R_F, FORL, HUM_F and HUM_R exist from W11):
- R_P0_s{s}_{fleet}: the PPO-0 signal, no SPaT, frozen R10 fleets s213–s513.
- HUM_P0_s{s}: SUMO drivers only.
- Evaluator: `scripts/CITY_eval_forl.py --forl-spat off --light FORL:<ckpt>` (it loads any CITY_forl checkpoint).

**Readings (registered, descriptive, one-sided 95 %):**
- **(a) Collapse.** Mean green of each PPO-0 signal over its HUM_P0 runs. "PPO-0 collapses too" iff the mean green is ≤ 7.0 s for ≥ 4 of 5 seeds (the FoRL signals: 6.0 s; RL-H: 15.2 s).
- **(b) Signal quality.** City time loss with SUMO drivers: HUM_P0 − HUM_R and HUM_P0 − HUM_F (unpaired light sets, shared traffic; `V.unpaired`, timeloss).
- **(c) Decision for the next step:**
  - If (a) holds: the W11 failure is attributed to the shared recipe of this port, not to the penalty. The paper states this, and the next FoRL step is a recipe repair, registered separately before it runs. PPO-0 + TSI is not run.
  - If (a) fails and PPO-0's city time loss is below FoRL's (upper bound of HUM_P0 − HUM_F < 0): the penalty causes the trade-off in this setting. PPO-0 + TSI against FoRL + provider is then registered as W12-1b.

**Self-check KP0-1:** a PPO-0 smoke checkpoint must record kappa 0, and its training log must show forecast_miss counted but r_pred = 0, i.e. the penalty is absent. The trainer prints r_pred via the stats.

## W12-2 Spider oracle replay (S1): diagnosis first, then registered arms

**Step 1, diagnosis (development, TUNE 1100–1103, no verdict):** find why the W8-1 open-loop replay on one-lane spider failed its fidelity check KH-1 ("replay == recorded R": False). The grid4 replay passed (C-72, delta 0).
- Step 2 is registered as an amendment only after KH-1 passes on spider.

**Step 2 design, intended (finalised in the amendment):**
- Arms R (σ*), Forecast (the TSIK provider) and Oracle (exact future switches from the trace) on recorded schedules from both R and TSIK runs, with fleet and demand identical.
- KH-1 must pass per cell.
- Readings:
  - Oracle − R agent time loss ≤ 0 (upper bound) → forecast error is an important cause.
  - Oracle still costs agent time → a harm beyond forecast error exists. This does **not** establish holding.
- Open-loop diagnostic only.

## W12-3 Follower intervention (S2): closed loop first, branching second

**Proposed improvement on the pasted plan.** First a closed-loop targeted-release test, which answers the decision-relevant question directly and reuses the existing release code:
- The agent hands control to its base driver σ* while a human follower is within 50 m.
- Control: release at a matched rate at random times.

The state-branching micro test (save/load state at matched events; follower time loss) follows only if the closed-loop test shows a targeted effect.
- Full specification is registered as an amendment before its code runs.
- Readings:
  - Targeted release improves agent time loss more than matched random release and keeps the fuel benefit → evidence that following events drive the residual cost.
  - Otherwise, not.

## W12-4 DCA-task: a stronger DC-Ada comparator (specified in an amendment before its code runs)

**Elements from the pasted plan, all to be fixed before running:**
- The DC-Ada search algorithm is kept, with the task mapping disclosed.
- An information arm gets the same speed-binned counts as TSI, alongside a raw-input arm.
- Horizon suited to the full-trip endpoint, plus a performance-versus-budget curve.
- Feasibility-first selection; penalty coefficients and checkpoint choice tuned on DEV with their cost counted.
- Confirmation on fresh traffic with the same signal and fleet checkpoints across arms.
- Win conditions registered in advance: TSI meets every limit and has lower fuel than a feasible competitor, **or** fuel within a pre-registered margin with clearly lower time loss.

**Zero-cost addition:** re-select the TSI grid with DC-Ada's soft-penalty selection rule on the existing TSI-2 tuning rows. This separates the selection rule from the information.

DCA3 remains the historical row.

## Amendment A1 (06:07, 06/10, after reading W12-1; before any A1 code ran): the FoRL port's reward scale, and a fair rerun (W12-1c)

**W12-1 result (job 078):**
- **PPO-0 does not collapse:** mean green 9.2–15.0 s, against FoRL's 6.0 s.
- **PPO-0 is better than FoRL with SUMO drivers:** HUM_P0 − HUM_F city time loss −3.71 s/veh [−4.70, −2.98].
- **PPO-0 is worse than RL-H:** +1.99 s/veh [+0.98, +2.73].
- **Registered decision (c):** the penalty causes the trade-off in this setting.

**Found when checking the cause against the authors' code** (`tls_rl/SUMO_gym/state.py` `get_reward`; `tls_rl/configs/train.ini` `[RL-Reward] waiting_reward = 1`; the FoRL env generator passes `benchmark_reward=None`, so there is no rescaling):
- The authors' environment reward is −1 per waiting (< 0.1 m/s) approaching vehicle **per simulation second**, summed over the action interval.
- Our port used −(halting at the next decision)/10: about 50× smaller per decision (about 10 from the /10 and about 5 from the 5-s summation).
- The penalty κ = −0.25 is therefore about 50× stronger relative to the environment reward than in the authors' setting.
- **Consequence:** the W11 result is a property of the port's reward scale, not a fair test of FoRL. W11's verdict is kept as recorded, with this disclosed.

**W12-1c (registered here):**
- **Code:** `CITY_forl.py --reward authors` accumulates, every simulation second during training, the halting count on each controller's incoming lanes. The previous decision's environment reward is minus that sum of halting vehicle-seconds since the last decision. The default `--reward port` is unchanged.
- **Arms, everything else as W11 / W12-1:**
  - FORLA: κ = −0.25, β = 0.95, λ = 0.
  - PPO0A: κ = 0.
  - Seeds 1–5, 200 episodes each, authors' reward.
- **Evaluation on 860–879,** with W11's R, TSI2 and HUM_R reused:
  - R_FA: FoRL-A signal without SPaT.
  - FORLA_SP: FoRL-A signal with its own forecast through provider v2.
  - HUM_FA.
  - R_P0A.
  - HUM_P0A.
- **Readings:**
  - **(a) registered, α 0.05:** FORLA_SP meets every M3 limit against R_FA.
  - **(a′) collapse:** mean green of each signal, collapse iff ≤ 7.0 s on ≥ 4 of 5 seeds, for both arms.
  - **(b) signal quality,** city time loss with SUMO drivers: HUM_FA − HUM_R, HUM_P0A − HUM_R, HUM_FA − HUM_P0A.
  - **(c) systems, descriptive:** FORLA_SP against TSI2 (unpaired).
  - **Provider counters:** share of answers from the forecast branch.
- **Self-check KA-1:** on a smoke episode, the mean per-decision environment reward under `authors` must exceed the `port` reward by a factor between 10 and 200 in magnitude. Both are logged; this guards a silent no-op.
- **Decision rule for the paper:**
  - If FORLA_SP passes (a), the paper states that a faithfully scaled FoRL protects the frozen fleet in this setting. TSI against FoRL then rests on (c) and on rights (FoRL retrains the signal).
  - If it fails, the failure is reported with the scale fix and its cause analysed from (a′) and (b).

## Amendment A2 (06:12, 06/10, after the step-1 diagnosis; before any step-2 run): W12-2 S1 spider oracle replay, fully specified

**Step-1 result (C-163):** CITY_eval4.Replay missed green phase 4 of the three-green spider signals. ReplayK (`scripts/CITY_w12_replayk.py`, greens from NetInfoK) reproduces the recorded runs bit for bit: KH-1 8/8 on the W8-1 TUNE recordings, time loss and fuel identical. The old replay deviated by up to +4.95 s/veh.

**Panel:** one-lane spider, traffic 1170–1189 (the attempt-4 confirmation panel; nothing is selected on it), signals RLK 11 and 111, rule fleet GLOSAL:0.3.

**Recorded schedules (closed loop, `--record`):**
- REC_R_k: R, no SPaT.
- REC_T_k: TSIK attempt-4 configuration (W10-5 refit provider n2k1, adapter (2, 0.5) for 11 and (1, 0.5) for 111).

**Open-loop replays on each schedule (ReplayK wrapper), the light forced, fleet and demand identical:**
- SIG: σ*, no SPaT.
- FC: the attempt-4 forecast provider.
- ORC: exact future switches from the trace (CITY_m3_headroom, as W8-1 D3).

**Self-checks (each can fail):**
- KH-1: SIG on REC_R reproduces REC_R exactly (time loss and fuel) for every seed.
- KH-1b: FC on REC_T reproduces REC_T exactly. The provider is the same; the adapter only changed light decisions, which are forced.
- If KH-1b fails, the FC_T arm is reported as approximate.

**Readings (descriptive, paired over 2 signals × 20 seeds, crossed bootstrap):** agent time loss, agent fuel and human time loss for ORC − SIG, FC − SIG and ORC − FC, on each schedule.
- ORC − SIG agent time loss upper ≤ 0 together with FC − SIG upper > 0 on the TSI schedule → forecast error is an important cause of the residual agent cost.
- ORC − SIG lower > 0 → a harm beyond forecast error exists (the fleet's use of exact timing, or physical interaction). This does **not** establish following/holding.
- Otherwise: no attribution.
- Open-loop diagnostic only, not a deployable result.

## Amendment A3 (06:17, 06/10, before any W12-4 code ran): W12-4 DCA-task, fully specified

**Zero-cost step (C-164):** DCA3's soft-penalty selection rule, applied to TSI-2's own tuning grid, picks the same adapter as TSI on 4 of 5 lights. The remaining difference therefore lies mainly in the transform class and the input information.

**Arms.** DC-Ada's search is kept exactly as in DCA3: per-robot perturbation, M 5, σ 0.05, τ 0, step 1, robots in sorted order, common random numbers per round, rounds cycling over TUNE 660–663, objective J = Δfuel% + 4[ΔTL_agent + 0.25]₊ + 4[ΔTL_city]₊ + 4[ΔTL_human]₊ against R on the same seed and horizon. Same lights t4–t8, same fleet-side service as TSI (hybrid provider), development fleet L11_s13.
- **DCAS (information arm):**
  - Input: the RL-H input (7) plus the speed-binned counts TSI uses, n[0.1,2) and n[2,5) on each green's served lanes, divided by 10 (4 inputs).
  - Transform: DC-Ada's residual MLP 11 → 32 → 32 → 7, output added to the 7 RL-H inputs, zero-initialised to the identity, nan_to_num and the [−10, 10] bound.
  - It can represent TSI's adapter.
- **DCAR (raw arm):** DCA3's 7 → 7 transform.
- **Horizon:** the full 5 400-s episode for references and candidates (the full-trip endpoint). This departs from the authors' 0.25 T truncation and is disclosed.
- **Budget:** 352 full rollouts per light, including references (8× TSI's 44 full rollouts). Parameters are saved at 88, 176 and 352 rollouts (2×, 4×, 8×) for the performance-versus-budget curve.
- **Penalty weight:** fixed at DCA3's 4; not tuned, disclosed.

**Selection on DEV (fresh to these arms; cost counted):**
- Each saved checkpoint (2 arms × 3 budgets × 5 lights) and R are run on DEV 600–611 with the development fleet L11_s13, full horizon.
- Per light and arm, TSI's own feasibility-first rule: among checkpoints meeting every limit against R on DEV (one-sided 95 % over seeds), the lowest fuel; otherwise the lowest agent time loss.
- The chosen checkpoint goes to confirmation.

**Confirmation** on fresh grid4 traffic 880–899, generated after a non-existence check: lights t4–t8 × fleets s213–s513 × 20; arms R, TSI2 (unchanged), DCAS*, DCAR*.

**Decisions (one-sided α 0.05; registered):**
- (a) each DCA arm meets every M3 limit against R;
- (b) TSI2 against each arm:
  - **W1:** TSI2 − DCAx fuel upper < 0 against a feasible DCAx;
  - **W2:** fuel upper < +0.5 pp with TSI2 − DCAx agent time loss upper < 0;
  - otherwise "no ordering". If DCAx is infeasible, (a) records it, and (b) is still reported.
- (c) descriptive: the budget curve on DEV.

This is a follow-up study after DCA3. DCA3's verdict is unchanged.

## Amendment A4 (06:39, 06/10, after reading S1, C-166; before any W12-3 code ran): W12-3 S2a closed-loop targeted release, fully specified

**S1 (C-166):** a harm beyond forecast error exists. Exact timing on R's own schedule costs agents +1.89 s/veh. The TSI cost decomposes into a schedule effect of +3.55 and an information effect of −2.07. So S2 runs, as planned.

**Panel:** one-lane spider 1170–1189, signals 11 / 111, TSIK attempt-4 configuration (W10-5 refit provider; adapter (2, 0.5) / (1, 0.5)), rule fleet GLOSAL:0.3.

**Arms (closed loop, all via `scripts/CITY_w12_release.py`, which patches CarGlosaL.step):**
- **R:** no SPaT.
- **TSIK:** baseline, rerun.
- **TREL:** TSIK, but whenever the fleet rule would command a glide and a human vehicle follows within 50 m (`getFollower(v, 50)`), the agent is released to its base driver for that second.
- **RREL:** TSIK with release at random glide-seconds (deterministic hash of seed, vehicle and second). The probability per signal equals TREL's released share of glide-seconds on the same seeds, so the release rate is matched.

**Counters per run:** glide-seconds, releases.

**Readings (descriptive, paired over 2 signals × 20 seeds):**
- TREL − RREL agent TL upper < 0, TREL − R fuel upper < 0, and TREL − TSIK agent TL upper < 0 → evidence that following events drive part of the residual cost.
- Otherwise: no evidence.
- Also reported: mean green, and the release shares.

**Self-check KR-1:** with the release disabled (mode none), the wrapper reproduces TSIK bit for bit on one cell.

The state-branching micro test is not run unless TREL shows a targeted effect.
