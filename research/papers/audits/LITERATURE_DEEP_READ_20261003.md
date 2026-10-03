# Deep literature read (W3) — wake 1, 03/10/2026 03:1x EDT

Source: subagent A (a5e043f5fc399c33b, resumed from the roster), method / experiments / discussion sections read through
WebFetch summaries of the arXiv HTML (NOT verbatim text — numbers and quotes must be re-checked against the PDF before any
manuscript use).  Not read: CGDC App. E.4 numbers, Bansal et al. AAAI-2019 long version, SIL-C §3 definitions, contract
shielding beyond §5.3.  My verification is marked **[checked]**; corrections to the subagent are marked **[corrected]**.

## Per paper (what they do → what their results say → how we differ → what a reviewer will expect)
1. **CGDC (2604.03785).**  Delayed-communication POMG; Thm 3.3 bounds the delay-induced return loss by (2R_max/(1−γ))·E[Σγ^t
   √(½Δ_info)], Δ_info = KL between action distributions under a timely reference message and the delayed one; a learned
   score (critic gain with vs without sender j's message − λ·delay KL) drives request / prediction / attention modules.  MPE +
   SMAC, delays 1–5 steps, 4 seeds, mean ± sd, no tests.  Transfer only easy → harder delay (degradation 0.23 vs 0.51–0.91 for
   baselines).  **Differs:** no frozen receiver deployed on a FRESHER channel; their "no message" reference is the same policy
   with masked messages, ours is a separately distilled silent student Z.  **Expected:** report Δ_info (receiver's action KL
   between fresh and stale views) as a diagnostic; add the masked-message same-receiver reference beside Z.
2. **Decoupled DC (2605.26286).**  Synchronously (zero-delay) trained policies + an execution-time wrapper (residual-GRU
   transition model + Kalman layer) that rebuilds a current-state belief; 6 benchmarks, 8 seeds × 50 episodes.  Downgrade
   direction only ("policies trained under idealized synchronous conditions … degradation").  **Differs:** the mirror of our
   case; its repair moves inputs BACK into the policy's training support (the current state) — consistent with our support
   reading; for a stale-trained receiver the analogue is garbling the fresh channel into the trained range (our G2 test).
   **Expected:** an input-side estimator baseline, or an explicit direction argument.
3. **CALF (2603.12543).**  **Single-agent** RL (CartPole, MiniGrid DoorKey) with network middleware (latency, jitter, loss),
   three training regimes (Baseline zero latency / Delay-Only fixed 50 ms / Full Net-Aware), deployed on a Raspberry Pi over
   Ethernet and Wi-Fi; 10 seeds, paired t-tests; network-aware training shrinks the sim-to-real gap ≈ 4× / 3×.
   **[checked]** Tables 4–5 (CartPole return): Baseline 495 / 310 / 288 / 173 / 92; Delay-Only 482 / 468 / 425 / 348 / 218;
   Full Net-Aware 476 / 472 / 458 / 442 / 378 (Sim-Clean, Sim+Net, Real-Eth, Wi-Fi-N, Wi-Fi-D).
   **[corrected]** The subagent read 476 vs 495 as "the upgrade direction in their matrix".  It is not: that compares two
   DIFFERENT policies (a robustness premium, our MX3 / mixture premium).  Every CALF policy does BETTER as its channel
   improves (Full Net-Aware 378 → 476; even Delay-Only, whose zero-delay condition is outside its fixed-50-ms training, 218 →
   482).  So CALF shows **no upgrade hazard** — and that is informative: an out-of-support FRESHER input did not hurt there,
   presumably because fresher state is simply more accurate for a smooth single-agent controller (decision-irrelevant support
   exit, our H4 / G3), whereas our relay receivers decode a joint age configuration.  **Expected:** name our mixture as the
   CALF-style randomised-channel baseline, show the full train × deploy matrix with paired tests, and explain why the hazard
   appears in E3 but not in CALF.
4. **Shisher & Sun (2208.06948v2; 2404.16281).**  Supervised remote inference; Thm 2 (smaller training AoI → lower training
   error), Thm 3(b) (monotone in δ under ε-Markov + mismatch condition), **Lemma 3 §III-B**: if χ²(inference conditional ‖
   training conditional) ≤ β² **for all x**, inference cross-entropy = H_L(Y_t | X_{t−δ}) + O(β).  2404.16281 trains one network
   per AoI (or one with AoI input).  Non-monotone error curves (robot, CartPole minimum near AoI ≈ 25).  **Differs:** no
   stale-trained → fresh-deployed test; their per-AoI curves are MATCHED-training curves = our information term; Lemma 3
   presumes full covariate support and is silent off-support, where our receivers fail.  **Expected:** cite Lemma 3 and
   Thm 3(b); report the information term separately from the excess; optionally show β is undefined / unbounded off-support.
5. **Bansal et al. (1906.01148, ICML-HILL 2019 workshop).**  Compatibility C(h1, h2) = share of h1's correct cases kept by h2;
   human users' trust model of the old AI; dissonance-penalised retraining traces an accuracy / compatibility curve; user study
   shows "a more accurate but incompatible classifier results in lower team performance".  **Differs:** the frozen receiver is
   a human mental model of where the AI errs; their update changes the error set, ours adds information (4×4 information
   +0.22, excess −9.57); our prediction is channel-side.  **Anticipates** the general upgrade-hazard principle and city C3.
   **Expected:** a compatibility / negative-flip metric against the receiver's own pre-upgrade decisions, and a compatibility-
   regularised update baseline (dissonance-penalised light; dissonance-penalised receiver fine-tune).
6. **SIL-C (2509.20612)** — backward skill compatibility for frozen high-level policies; a Mahalanobis / χ²-quantile
   validation gate + "hooking" with fallback; backward transfer −14 … −37 % without, +18.6 … +42.5 % with.  Anticipates a
   support-validated interface with fallback for frozen users after an upgrade (our #3 fallback, the city compatible mode).
   **Contract shielding (2606.14130)** — fixed LTL assume-guarantee contracts as action masks, a bandit over certified
   contracts (§5.3); not partner-relative, no upgrades.  **Expected:** a standard χ²-quantile support gate baseline against
   rule A / FB; a shield / action-mask safety baseline on the city track.

## Threats (ranked) and the defence
1. **Bansal 2019** — the principle.  Defence: information-increasing upgrade (G1 split), learned closed-loop receiver whose
   "mental model" is its training support, channel-side prediction (rule A), silent bar.
2. **Shisher–Sun** — "fresher can be worse" + a conditional-mismatch bound.  Defence: never stale → fresh; their curves are
   our information term; Lemma 3 assumes full support.
3. **SIL-C** — support-gated fallback for frozen users after an upgrade (closer than CALF after the correction above).
   CALF is now a CONTRAST case (no hazard), not a threat.

## Baselines / metrics to add (W5 candidates)
1. Compatibility / negative-flip rate vs the receiver's own pre-upgrade decisions; a dissonance-penalised receiver fine-tune.
2. Full train × deploy matrix with paired tests (≥ 10 seeds); the mixture named CALF-style; one regime "K1 + occasional
   higher capacity"; an age-aware (CoDe / CGDC-style gated attention) receiver trained at K1, deployed at iid.
3. Masked-message same-receiver reference π^(−0) beside Z; Δ_info diagnostic; a χ²-quantile (Mahalanobis) support gate as the
   standard fallback baseline that rule A and FB must beat.

## Wake 2 additions (subagent A; PDFs read for Yan 2021, Shen 2020, Srivastava 2020, Lee 2019, Lu 2020; summaries only for
## Wang 2021, Lazaridou 2020, MUSCLE 2024)
* **Shen et al. 2020 BCT (2003.11942)** — an independently trained better embedding scores 0.0 % against the frozen old
  gallery; BCT's influence loss restores compatibility.  **Their "update gain" (M(new, old) − M(old, old)) / (M(new*, new*) −
  M(old, old)) is the normalised form of our information / excess split** (4×4: −9.35 / +0.22 ≈ −42) — must be cited as the
  precedent of the decomposition; their producer changes semantics, our channel upgrade does not.
* **Yan et al. 2021 PCT (2011.09161)** — negative flip rate (NFR) and relative NFR; focal distillation cuts NFR 6.44 → 2.35 at
  ≈ equal error.  Import: NFR of the frozen receiver across the channel upgrade on matched states; a positive-congruent receiver
  fine-tune baseline.
* **Srivastava et al. 2020 (2008.04572)** — BTC / BEC; a +14 % more accurate OCR model raises a frozen downstream blacklist's
  error 55 → 86.4 %; their limitation: incompatibility "may not translate to a drop in performance".  Import BTC / BEC.
* **Lee et al. 2019 (1909.04499), Lu et al. 2020 SIL (2003.12694)** — language drift under joint fine-tuning; in SIL a frozen
  pretrained image ranker's R1 drops ≈ 0.22 → 0.09 as the producer improves at its task (read from a plot).  Frozen learned
  receivers as evaluation instruments, not deployed receivers.
* **Wang et al. 2021 "Calibrate your listeners!" (2110.05422; summary only)** — a speaker optimised against one listener: 98 %
  with it, 37 % with a held-out listener, because listeners are over-confident outside their training domain (our support
  mechanism, producer-optimised direction); a population of listeners recovers ≈ 80 %.
* No paper on communication-protocol VERSIONING between learned agents found (3 searches, not exhaustive).
**Novelty consequence:** "an updated component breaks a frozen consumer" is established (Bansal, BCT, PCT, Srivastava, MUSCLE,
Calibrate-your-listeners).  Our distinct points must be explicit: (1) the upgrade is a CHANNEL REFINEMENT with unchanged message
semantics — Blackwell-dominant (Lean `upgrade_emulation`), so the Bayes value cannot fall, unlike every cited update; (2) a
closed-loop multi-agent decision receiver against a compiled-silent bar; (3) the split, cited as BCT's update-gain form;
(4) channel-side prediction (rule A) with Lean knowledge floors.  To add: NFR / BTC / BEC and BCT update gain for the frozen
receiver; positive-congruent / dissonance receiver fine-tune and a receiver population as baselines; cross-play with held-out
independently trained receivers; ensemble confidence as a support gate.

## Wake 3 (07:5x) — benchmark survey (subagent A) and an anticipation found
* **Rainbow Delay Compensation (2505.03586v4, NeurIPS 2025)** — per-agent, per-entity observation delays (fixed or random), MPE
  + SMAC/SMACv2 on pymarl3 / EPyMARL (repo linkjoker1006/RDC-pymarl; licence NOT visible).  Figs 8–9 test fixed delays 0–12 for
  Oracle (trained delay-free), Base (trained under delay) and Base+DR (delay randomisation): text (verified) — Base and Base+DR
  "drop … at delays of 0-2 … inability to generalize to unseen delay conditions".  → prior observation of the upgrade direction
  (NOVELTY_POSITION Addendum 3).  Numbers in the plot only (not verified).
* **Recommended standard benchmark for universality (A):** MPE with RDC-style aged per-entity copies (EPyMARL + MPE2 wrapper, or
  RDC-pymarl once its licence is confirmed): simple_tag (moving entities — hazard predicted) vs simple_reference (static goal —
  negative control); regimes d = 4, d = 0 (matched), d ~ U{0..6} (mixture), no-information (silent analogue); deploy d′ ∈
  {0, 2, 4, 6}; 5 seeds; ≈ 40 runs, ≈ 80–240 CPU-h (not verified).  Runner-up for learned messages: Traffic Junction (IC3Net /
  MAGIC repos, MIT; CommNet, IC3Net, TarMAC-IC3Net, MAGIC runnable; ≈ 400–1 400 CPU-h).  SMAC too costly on this Mac.  Requires
  downloads (repos, packages) → needs the user's explicit permission.
