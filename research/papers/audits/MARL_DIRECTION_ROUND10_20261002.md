# Round 10: re-reading nine rounds of research against the results — is there a better direction? (02/10/2026 11:5x EDT)

User 11:4x: after nine research rounds, re-read the results and the sources; is there a direction that is more novel, more
practical, more of a breakthrough, more interesting?  Re-read: MARL_NOVELTY_CHECK_20260927, MARL_DIRECTIONS_AB_20260929, the
novelty-map memory (30/09), MARL_NOVELTY_CHECK_DIRECTIONS_20261001 (rounds 1–8), MARL_DIRECTION_BRAINSTORM_20261001,
MARL_EXIT_PLAN_20261001, MARL_RESULTS_VS_LITERATURE_20261002, MARL_COMPAT_MECHANISM_20261002.  Sources re-read today (full
HTML unless noted): Shisher–Sun 2404.16281 (training section), Moeller–Krishnamachari 2609.06351 (§8), arXiv 2512.03528,
"When freshness is not enough" 2606.04361 (new), Chauhan–Bera 2609.34373 (abstract page), DEFLECT 2605.19294 (abstract),
Decoupled Delay Compensation 2605.26286 (abstract), freshness-aware beam prediction 2609.01225 (abstract).  No subagents.

## 1. What nine rounds say, in one table
| Neighbourhood | Verdict over the rounds | Why |
|---|---|---|
| Value-of-communication prediction, byte budgets, whom-to-listen-to, nested messages, implicit channels, compiled silence as a bar, LLM evaluation, A/B stopping | collided (rounds 1–5) | ≥ 4 directly relevant papers in Sep 2026 alone; crowded |
| Freshness / floor theory | supporting, incremental (rounds 1, 6) | Kaul–Yates–Gruteser 2011; Farazi–Klein–Brown 2019; ours adds prefix / heterogeneous decoding |
| Operating envelope F(κ) ∩ R_θ | F and R known as objects; the scheduler-impossibility split not found (round 7) | |
| Count coordinate, training-relative band, provisioning rule | ingredients known, combination not found (round 8) | |
| W1 law, mixture fix | W1-Lipschitz bounds standard; mixture = domain randomisation (round 9) | ours: a POLICY-FREE CHANNEL histogram with a stable measured slope; the upgrade direction |
The pattern: everything framed as "a MARL communication method / measure" collides; what survives is about a LEARNED RECEIVER
whose input is information of some AGE, and what happens when the age distribution at deployment differs from training.

## 2. The re-read finds a sharper target outside MARL
* Shisher–Sun (2404.16281, full text): the learned predictor is trained either per AoI value or as ONE network "using a
  larger dataset that encompasses a variety of AoI values"; the analysis assumes the AoI process is independent of the data
  and that the training and deployment AoI distributions coincide; mismatch and extrapolation are not discussed.  The whole
  remote-inference scheduling line (2308.10094, 2509.01926, 2311.11143, 2508.07555) optimises the schedule for a FIXED
  error function e(δ).
* "When freshness is not enough" (2606.04361, full HTML): two schedules with the same mean AoI give different LQR costs; a
  LOWER update rate can lower the cost — but the controller is model-based and fixed; no learned controller, no
  train/deploy distribution, no distance.
* Moeller–Krishnamachari (2609.06351 §8): optimal (not learned) rules; non-stationarity and endogenous observations open.
* 2512.03528: matched training priors help; only equal-or-harsher test channels; no transfer metric.
* DEFLECT, Decoupled Delay Compensation: plug-in fixes for delay; the shorter-than-training direction not addressed.
Gap common to all: for a LEARNED receiver, the error function is a property of the TRAINING age distribution, so changing
the schedule or the network changes e(δ) itself.  The "optimise the schedule for a given e(δ)" separation fails, and a
fresher schedule or a network upgrade can hurt.  Our results measure exactly this (P-UP2, E1, L-258); no source read in the ten
rounds measures it (a search result, not a priority claim).

## 3. Candidate direction (recommended): "Fresher is not safer" — age-distribution shift for learned receivers
Claim: the value a learned receiver extracts from aged information is governed by the Wasserstein distance between the
deployment and the training age distributions — a quantity computable from the channel alone before deployment — so
scheduling and learning are not separable; upgrades can regress; and the repairs split by DIRECTION:
| Direction of shift | Network-side (scheduler / throttle) | Interface-side (age remap, training-free) | Training-side |
|---|---|---|---|
| Upgrade (deployment fresher than training) | ALWAYS possible: a richer channel can emulate any poorer channel's exposure (decode fewer / hold) — an emulation lemma | predicted FULL repair: relabel ages by the monotone transport map F_train⁻¹ ∘ F_deploy (fresh content shown as older = conservative) | mixture (E4) |
| Downgrade (deployment staler) | IMPOSSIBLE below the floor for every scheduler (proved, LeanMarlReceiverFloor / NetFloor) | predicted PARTIAL repair only (stale content shown as fresh = over-trust); the age clip, a crude version, recovered ≈ half (+0.79 %, prospective) | matched (TM1) or mixture (E4) |
Why this is better than the current framing:
* Novelty: attacks a stated modelling assumption of an active theory line (remote-inference AoI) with a measured law,
  replicated with frozen parameters; the direction asymmetry (+ theorem) was not found in any source of the ten rounds.
* Practical: network upgrades, scheduler changes and sampling-rate changes are routine; the paper gives a pre-deployment
  check (W1 from the channel), a regression warning, and a training-free fix (age remap) or a cheap one (throttle).
* Breadth: any learned consumer of aged data (remote inference, collaborative perception / V2X, multi-agent RL, sensor
  fusion, LLM agents reading shared memory); our MARL results become ONE of two domains.
* Assets reused: the W1 law (L-249, L-258), the band (L-250), the floor (proved), E4, Lean W1 module (smoke PASS).
Risks: OT for covariate shift is classical (Courty et al.) — the remap is an instance, the contribution is the direction
asymmetry and the law; the mixture fix is domain randomisation (Shisher–Sun's "variety of AoI values" training is itself a
mixture); "distribution-aware AoI" (2606.04361) must be cited and distinguished (mechanism: training support of a learned
receiver vs moments of a model-based LQR cost).

## 4. Cheapest decisive experiments (in order)
1. Age-remap evaluation on the 3×3 CityFlow students (EVAL-ONLY, ≈ 20 evaluations): relayCK1 at iid with the quantile map
   to its K = 1 training histogram (prediction: ≥ its K = 1 gain, ≫ the plain +0.17 %); relay6Cage at K = 1 with the map to
   its iid histogram (prediction: partial, ≤ the clip's +0.79 % improvement).  The fresh flag is part of the age (age 0) and
   is remapped jointly.  Needs a protocol and an evaluator variant (small code).
2. A controlled remote-inference testbed (the second domain, CPU-light): a Gauss–Markov / nonlinear time series, a learned
   predictor ŷ = f(X_{t−δ}, δ) trained under one AoI distribution (e.g. a slow scheduler), deployed under faster / slower
   schedulers; measure the error vs W1, the upgrade regression, the remap and the mixture.  Directly in Shisher–Sun's model.
3. The W1 prospective test (armed; relayCK2, panel 3901–3964) — the law's prospective test on a new training channel.
4. The emulation lemma in Lean (a richer budget can reproduce any poorer budget's exposure: decode a subset), paired with
   the floor (downgrade side) — the asymmetry theorem.

## Update 12:4x (02/10) — results of steps 1, 2, 4 and the age-role follow-up (ledger L-261 … L-266)
* Step 1 (MARL age remap, PROTOCOL_E3_AGE_REMAP): REFUTED.  Relabelling ages by the exact monotone transport (W1 → 0) puts
  both receivers below compiled silence in BOTH directions (−4 … −7 %); the minimal projection (clip of out-of-support ages to
  the support edge) helps (+0.69 %, replicating +0.79 %).  The table cell "remap predicted FULL repair" is withdrawn.
* Step 2 (remote inference, PROTOCOL_RI_AOI_SHIFT): the upgrade regression reproduces (5/5 seeds) but only for the part of the
  deployment outside the training support; emulation exact; mixture covers.  Follow-up (PROTOCOL_RI_AGE_ROLE): the upgrade
  regression and the relabel's harm both require age to be a PROPAGATION horizon (drift λ): without drift a fresher channel
  helps (+0.27), with strong drift it falls below silence (−1.14); minimal emulation beats full emulation everywhere.
* Step 4 (Lean): LeanMarlEmulationV1 (upgrade emulation, downgrade strictness), LeanMarlAgeRoleV1 (conservative relabel safe
  for a pure reliability weight, unsafe with propagation / over-trust); plus Provisioning, Support, HoldFloor, Mixture — all
  smoke-gated.
Revised repair taxonomy:
| Shift | Network / receiver side | Interface side | Training side |
|---|---|---|---|
| Upgrade | emulation to the EDGE of the training support (always possible; Lean) | projection, not transport (transport refuted) | mixture |
| Downgrade | impossible below the floor (Lean) | projection = clip, partial (+0.7 %) | matched or mixture |
The direction's core claims stand (W1 law as a predictor, upgrade hazard, scheduling/learning non-separability, asymmetry
theorem); the new, more specific claim: the hazard of an upgrade lives in the receiver's PROPAGATION use of age, and the
right interface/network repair is the minimal move into the training support.

## Update 13:1x — the interface row narrowed again (L-274)
The minimal joint projection "onefresh" (only the prefix head's entry stays fresh) hurt the K = 1-trained receiver even more
than transport (−2.9 / −7.4 / −11.4 % at K2 / K3 / iid).  Interface rule now: clip only per-entry values outside the trained
range; never relabel in-range values (transport or joint-statistic projection), because a receiver that uses age as a
propagation horizon mis-extrapolates.  Upgrade repairs for MARL: emulation (throttle) or mixture training — not the interface.

