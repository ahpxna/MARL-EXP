# PROTOCOL WAVE 11: FoRL, a published anticipatable-signal method, ported as a comparator with more rights (registered 05/10 ~21:5x, before any wave-11 code was run)

**Why:**
- The user, 21:4x: "làm luôn cái FoRL, cho queue chạy sau cái DCA3 đang chạy luôn đi".
- FoRL (Gerner, Bogenberger, Schmidtner, XAI@IJCAI 2026; code github.com/urbanAIthi/26_FORL_IJCAIXAI, MIT) trains a reinforcement-learning signal to emit multi-step forecasts of its own actions and publishes them to GLOSA.
- It **retrains the signal**, which TSI's rights exclude. It is therefore a published comparator with more rights, the light-side analogue of fleet retraining.

## The port (from the authors' code: `forecasting_rl/forl/wrappers.py`, `ppo_with_forecastloss.py`, `config.yaml` (tls), read 21:4x)

**Model:** PPO with a MultiDiscrete action of length L (one keep / switch per future decision of the controller); only the first is executed.

**Reward conditioning:** every earlier forecast of the current decision that differs from the executed action adds κ · β^index, where index = k − 1 for the forecast made k decisions earlier.

**Loss conditioning:** λ × cross-entropy of the forecast heads 1 … L − 1 against the actions actually executed 1 … L − 1 decisions later, added to the PPO loss.

**Observation augmentation:** the controller's previous forecast (L − 1 entries) is appended to the observation.

**Settings:**

| Setting | Value | Source |
|---|---|---|
| L | 5 | tls config |
| Policy and value networks | separate, 256-256, tanh (SB3 MlpPolicy default) | tls config |
| γ | 0.99 | tls config |
| GAE λ | 0.95 | SB3 default |
| clip | 0.2 | SB3 default |
| epochs | 10 | SB3 default |
| minibatch | 256 | |
| Adam learning rate | 3e-4 | |
| entropy coefficient | 0 | SB3 default |
| value coefficient | 0.5 | SB3 default |
| advantage normalisation | on | SB3 default |
| κ | −0.5 | middle of the authors' sweep {0, −0.1, −0.5, −1} |
| λ | 10 | middle of {0, 0.5, 10, 100} |
| β | 0.9 | not published; disclosed |

**Signal environment, as RL-H:**
- Shared policy for the 16 grid4 controllers; decisions every 5 s outside yellows after the 5-s minimum green; inputs as RL-H (7) + the previous forecast (4).
- Environment reward −(halting on incoming lanes)/10, observed at the controller's next decision.
- SUMO drivers only during training (as RL-H).
- 200 episodes of 3600 s on TRAIN 0–7 in rotation. About 2 M controller decisions, comparable to the authors' 2.5 M TSC steps.
- Seeds 1–5, giving lights FORL_s1–s5. Execution at evaluation: argmax per head.

**Publication to the fleet**, the FoRL GLOSA case study ported to SPaT:
- At every second, for a link served by the current green: ttr = (t_d + k·5 − t) + o, where t_d is the controller's last decision time and k the first forecast index (1 … 4) that says switch.
- A link served by the other green: ttg = that time + Y.
- During a yellow whose next green serves the link: ttg = (Y − τ) + o, exact.
- Otherwise (no switch within the horizon, or no decision yet): **valid = False**, so the fleet falls back to σ*.
- o = 1 s, the convention of every provider.

**Self-check KF11-1:** every answer from the yellow branch must equal the realized time to green on the phase trace (W10-2 matcher, served-answer log, one smoke run). The convention can fail.

## Panel and arms

Fresh grid4 traffic **860–879**, generated after a non-existence check; R10 fleets s213–s513.

| Arm | Light | SPaT | Fleet |
|---|---|---|---|
| R_F | FoRL lights s1–s5 | none, i.e. σ* | |
| FORL | FoRL lights | the light's own forecast | |
| R | RL-H t4–t8 | none | |
| TSI2 | RL-H t4–t8 | TSI-2 configuration | |
| HUM_F / HUM_R | FoRL / RL-H | | SUMO drivers only (the signals' own quality) |

## Readings

- **(a) Registered, α 0.05:** FORL meets every M3 limit vs R_F, i.e. the anticipatable signal and its own forecast protect the frozen fleet.
- **(b) Descriptive:** the cost of anticipatability, city TL of HUM_F vs HUM_R (unpaired light sets, traffic shared).
- **(c) Descriptive:** the two systems compared, TSI2 (RL-H + TSI) vs FORL (FoRL light + its forecast): agent fuel and the three time losses as absolute levels (unpaired light sets; fleets and traffic shared).
- **Also reported:** the FoRL forecast's served-answer MAE and publication shift (W10-2 matcher; TUNE 660–661, lights s1 / s2, fleet s213).

## Queue

- **Job:** 077_W11_FORL.sh. It waits for job 072e (DCA3) to finish before starting, as the user asked.
- **Directory:** `research/city_sim/w11_20261005/forl/`.

## Amendment A1 (21:5x, before any wave-11 code ran): the authors' own committed TSC settings replace the values chosen above

The repository was cloned on the user's instruction to `external_assets/FORL_26_IJCAIXAI` (commit c7acfc56, MIT; outside git).

**FoRL settings** (`forecasting_rl/forl/config.yaml`, section `tls`):

| Setting | Value |
|---|---|
| forecast_horizon L | 5 |
| forecasting_penalty κ | −0.25 |
| forecasting_penalty_decay β | 0.95 |
| forecasting_loss_weight λ | 0, i.e. reward conditioning only |
| direct_penalty | true |
| add_predictions_to_state | true |
| net_arch | 256-256 (separate pi / vf) |
| γ | 0.99 |

**PPO defaults of the same file:** batch 256, learning rate 3e-4, GAE 0.95, entropy coefficient 0, 10 epochs, clip 0.2.

**Reward conditioning, as in `wrappers.py` `_get_prediction_reward`:** the forecast made `index + 1` decisions earlier, at position `index + 1`, is compared with the executed action. A mismatch adds κ · β^index to this decision's reward.

**Publication:**
- The authors' GLOSA default uses a separately trained action predictor ("deterministic_sap").
- We publish the policy's own deterministic forecast, their "deterministic" option, because a separate predictor would be a forecaster on the fleet side, which TSI's comparison already covers.

These values supersede κ −0.5, λ 10, β 0.9 above. Everything else is unchanged.

## Amendment A2 (22:06, 05/10): provider fix and KF11-2, before any confirmatory data

**Found by a new self-check, before FoRL training or the confirmation started.** Job 077 is still waiting for 072e; no `CITY_forl.py` process has run since the smoke. The smoke's FoRL light (2 × 300 s) switched at every first decision (mean green 6 s), so the forecast branch was never exercised (`forl` 0 of 14 799 queries). KF11-1 checks only the yellow branch.

**KF11-2** (`scripts/CITY_w11_stubcheck.py`):
- A consistent stub policy replaces the network: it switches at the first decision with green spent ≥ SW, and forecast entry i = 1 iff spent + 5i ≥ SW. Every published forecast is therefore honoured.
- Forecast-branch answers must match the realized phase trace exactly, with offset 0 as for every provider; so must yellow-branch answers.
- Thresholds: SW 15 and 25 s.

**Result on provider v1:** FAIL. The other-green ttg answers were exact (7 893). Every current-green ttr answer was +1 s (2 904 of 2 904; MAE 0.27 s). v1 told the fleet the green lasted one second longer than it did. This bias works against FoRL.

**Fix (v2):** ttr = rem instead of rem + 1. This is a one-line change in `make_spat_forl`; v1 is archived as `legacy/forl/CITY_forl_v1_ttr_plus1_*.py`. Training does not use SPaT and is unaffected.

**KF11-2 on v2:** PASS at both thresholds. Forecast-branch MAE 0.00 s (n 10 797 and 15 164); yellow branch exact (n 3 536 and 2 808).

**Provenance:** `CITY_forl.py` sha256 prefix e3bef62e…; `CITY_w11_stubcheck.py` df627101…. Outputs are in `research/city_sim/w11_20261005/kf11_2/`.

**Unchanged:** registered decisions, arms, seeds and settings. The job script (running/waiting) is not edited.
