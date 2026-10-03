# PROTOCOL C0 — learned cars under a light upgrade: the stylised testbed (written 02/10/2026 18:0x EDT, before any run)

Direction: research/papers/audits/CITY_TWO_POPULATION_NOVELTY_20261002.md (N1, "a better partner is a different partner").
C0 isolates the CAR side of H1 / H2 / H3 / H4 / H5 / H6 in the smallest model where the light's policy is the car's input
channel.  The light's own benefit from its upgrade is NOT modelled here (C1 measures it); C0 asks only what the upgrade does to
cars that learned against the old light.

## Model
* One approach, one stop line at x = 0.  Car starts at x0 = −L0, L0 ~ U{150..250} m, speed v0 ~ U{8..12} m/s; step 1 s;
  actions a ∈ {−3, −2, −1, 0, +1, +2} m/s²; v' = clip(v + a, 0, 14); x' = x + v' (integers).
* Light: green and red alternate; every phase duration is drawn i.i.d. from the light policy; the first phase is green with
  probability ½ and has already run u ~ U{0..d₀−1} s at t = 0.  Policies (durations in s, both colours):
  FT = 30 (fixed-time, deterministic); ACT = U{20..40} (today's actuated light; the TRAINING partner);
  EXT = U{20..70} (an upgrade that EXTENDS phases: time in phase leaves the trained range);
  CUT = U{5..40} (an upgrade that switches EARLIER inside the trained range: same input range, different meaning).
* Crossing: if x' ≥ 0 and the light is green at t + 1 the car passes (episode ends).  If x' ≥ 0 and red, the car is stopped at
  the line (x' = −1, v' = 0) and pays a violation penalty 20.  Stage cost 1 + 0.05 a² + 1·[v' = 0, not passed]; timeout at
  150 s costs 50.
* Teacher: exact dynamic programming with the WHOLE future schedule (privileged).  Its cost is the per-episode optimum;
  REGRET = cost − teacher cost (≥ 0) is the primary metric.
* Students: MLP 64–64 (ReLU), cross-entropy on the teacher's argmin action at visited states.  States are visited by the
  teacher with ε-random actions, ε ∈ {0, 0.1, 0.3, 0.5}, four rollouts per episode (noise injection, a DART-style substitute for
  DAgger; stated as such).  Inputs: Z (compiled silence) = [x/200, v/14, green, τ/60], τ = time in current phase;
  M (message, SPaT) = Z + [r/60], r = residual time of the current phase.  3 000 training episodes per light, 8 epochs,
  Adam 1e-3, batch 2 048, one thread.  Trained on FT, ACT, EXT, CUT and MIX (equal thirds of ACT, EXT, CUT, same total size),
  seeds 0–4: 10 students per seed.
* Rule car (non-learned reference): drive at 12 m/s; brake when red and the stopping distance is near; never uses r.
* Evaluation panel: 3 000 episodes per light (seed 9 000 + light index), shared by every student; teacher cost computed per
  episode.  Variants of Z_ACT on EXT and CUT: CLIP (τ → min(τ, τ_max) per colour, τ_max from the training data);
  MONITOR + FALLBACK (if τ > τ_max for the current colour, take the rule car's action); RELABEL (quantile transport of τ from the
  deployment light's decision-step distribution to ACT's, per colour, fitted on 1 000 separate calibration episodes).

## Predictions (fixed now)
* C0-1 (H1, both kinds of upgrade hurt the trained car).  Mismatch penalty Δ(P) = regret(Z_ACT on P) − regret(Z_P on P) > 0 for
  P = EXT and P = CUT, with the bootstrap 95 % lower bound > 0 (resampling seeds and episodes).
* C0-2 (H2, input support sees only one of them).  Out-of-support mass (fraction of Z_ACT decision steps with τ > τ_max) ≥ 10 %
  on EXT and 0 on CUT.  MONITOR + FALLBACK recovers ≥ 50 % of Δ(EXT): regret(Z_ACT+FB on EXT) ≤ regret(Z_ACT on EXT) − ½Δ(EXT).
  On CUT the monitor cannot fire, so the harm of CUT is invisible to an input-support monitor (reported, not a test).
* C0-3 (H4, the message is insurance; compiled silence suffices for a deterministic light).  Δ_M(P) = regret(M_ACT on P) −
  regret(M_P on P) ≤ ¼ Δ(P) for P = EXT and CUT.  On FT: |regret(Z_FT) − regret(M_FT)| ≤ 0.05 × regret(rule car on FT).
* C0-4 (H5, mixture is minimax).  max over P ∈ {ACT, EXT, CUT} of regret(Z_MIX on P) ≤ the same maximum for each of Z_ACT,
  Z_EXT, Z_CUT.
* C0-5 (H6, relabelling hurts).  regret(Z_ACT+RELABEL on EXT) > regret(Z_ACT on EXT) and the same on CUT.
* Reported without a threshold: CLIP on EXT and CUT; W1 between the deployment and training τ distributions at decision steps
  against Δ; the rule car's regret on every light; stops and violations.

## Kill rules
* If C0-1 fails for both EXT and CUT, the car side of H1 does not exist in the cleanest model: C1 is redesigned before it runs.
* If C0-2's fallback does not recover half of Δ(EXT), the input-support monitor is not a repair for partner upgrades.
* If C0-3 fails, "the message is compatibility insurance" is withdrawn from the direction.

## Outputs
research/city_sim/c0_testbed_20261002/result.json (every cell per seed, the source sha256) and report.txt; produced by
scripts/CITY_c0_testbed.py; smoke run (--smoke, tiny sizes) first, through the report.

## Deviation 1 (written 02/10/2026 18:1x EDT, after the smoke run and ONE development run at 600/600 episodes, seed 0, before any full run)
* What the development run showed: silent students trained on random-duration lights (Z_ACT, Z_CUT, Z_MIX) locked up after a
  forced stop at the line (timeouts = violations = 44–49 % of episodes, regret ≈ 140–160 on their OWN light) while Z_FT, Z_EXT and
  every message student did not.  A behaviour-cloning covariate-shift artefact (the state "stopped at the line on green" is rare
  in the teacher's data), not the phenomenon under test.
* Change: after the noise-injected cloning, every student gets 2 DAgger rounds (NTR/3 fresh episodes per round from its own
  training light(s); the current student drives; every visited state is labelled with the teacher's action from the exact DP
  value table; aggregate; 4 more epochs, warm start).  This is the on-policy distillation the E3 students use.
* Unchanged: the model, the lights, the panels, the metrics, every prediction and every threshold of the protocol.  The development
  run's numbers are not results (archived at legacy/city_sim_c0_dev_noDAgger_20261002).

## Addendum C0b — a partner-side compatibility certificate (EXPLORATORY; written 02/10/2026 18:20 EDT, after the user pasted an
## external collision audit, BEFORE the full C0 run and before reading the output of the DAgger development run)
Motivation (audit 18:1x): an input-support monitor can see EXT (support expansion) but not CUT (same views, changed meaning:
P(switch | colour, τ) differs).  The practical object is a certificate computed from the NEW LIGHT'S OWN LOGS, before any car
meets it.  The registered C0-1 … C0-5 are unchanged and are reported as registered, including a failure of the support thesis.
* Logs: the light alone (no car), 20 000 phases per policy from the C0 schedule generator (seed 7 000 + light index).
* S_exit(P) = fraction of light-seconds whose time in phase exceeds ACT's logged maximum for that colour.
* h_P(c, τ) = empirical Pr(the phase ends at the next second | colour c, time in phase τ).
* D_haz(P) = mean over P's light-seconds INSIDE ACT's range of |h_P(c, τ) − h_ACT(c, τ)|  (P's own state distribution).
* Certificate K(P) = D_haz(P) + S_exit(P).  Comparators: S_exit alone; W1 between P's and ACT's time-in-phase distributions.
* Lights: the four of the protocol plus six evaluation-only variants, all durations U{lo..hi} for both colours:
  A1 = U{10..40}, A2 = U{15..35}, A3 = U{20..50}, A4 = U{25..45}, A5 = U{30..60}, A6 = U{20..30}.  For each of the nine lights
  other than ACT, the target is Δ(P) = regret(Z_ACT on P) − regret(Z_P on P) (and Δ_M with M students), seeds 0–2, the C0
  training recipe (Deviation 1 included) for every specialist, 3 000-episode panels (seed 9 100 + index for A1–A6).
* Predictions (exploratory, fixed now): C0b-1 Spearman(K, Δ) ≥ 0.7 over the nine lights; C0b-2 Spearman(K, Δ) exceeds both
  Spearman(S_exit, Δ) and Spearman(W1, Δ); C0b-3 among the lights with S_exit = 0, Spearman(D_haz, Δ) ≥ 0.6 (few points:
  reported, weak).  Δ_M is reported against the same predictors.
* Interpretation rule: if C0-2 holds for EXT but CUT still harms (C0-1 on CUT), the thesis is restated as "a partner upgrade
  breaks a learned receiver by changing the SUPPORT or the SEMANTICS (conditional law) of its interface"; C0b tests whether a
  partner-side statistic of both predicts the harm.
* Note on C0-3: the message is the CURRENT residual only, while the teacher knows the whole future schedule; a C0-3 failure
  would say the current residual is insufficient as an intent contract, not that intent messages cannot insure compatibility.

## Deviation 2 (written 02/10/2026 18:3x EDT, after the DAgger development run (seed 0, 600 episodes), before any full run)
* What the development run showed: with cross-entropy cloning the students were WORSE than the non-learned rule car on their own
  light (e.g. Z_ACT on ACT regret 16.2 vs rule 12.4; M_ACT 15.3), with frequent forced stops.  Cloning the ARGMIN of a privileged
  teacher picks the action the teacher takes most often for a view (majority vote over the hidden schedule) and pays for the
  minority cases — the imitation gap of asymmetric (privileged) imitation, not the phenomenon under test.  A weak student would
  make every compatibility comparison noise-dominated and would not be the "compiled silence" of a strong teacher.
* Change: students REGRESS the teacher's action values (cost-to-go Q of all six actions, scaled by 1/10, mean squared error) at
  visited states and act by argmin (AggreVaTe-style cost-sensitive imitation); same data recipe (noise-injected teacher rollouts
  + 2 DAgger rounds), same sizes, same seeds.  The Bayes-optimal action of a view under the teacher's continuation is what the
  regression targets.  Implementation only: seeds run as separate processes; evaluation panels computed once and shared;
  the batched DP is checked against the scalar DP and the teacher replay in the panel step.
* Unchanged: model, lights, panels, metrics, every prediction and threshold of the protocol and of Addendum C0b.

## Addendum C0c — a TWO-SIDED, privacy-preserving compatibility predictor (EXPLORATORY; written 02/10/2026 18:4x EDT, before any
## full-run seed is trained and before the Q-regression development run has reported)
Origin: the E3 evidence that harm has a partner/channel-side part (rule A, support exit, prospective on two networks) AND a
receiver-side part shared across conditions (artifact-subagent H1: one per-student fragility axis, ρ −0.818; H5: a cheap K = 1
probe ranks students' fragility elsewhere, ρ +0.58 … +0.72).  In a city neither party holds the other's policy: the city can
compute K(L) from its own light logs (Addendum C0b); the carmaker can run its legacy fleet against a STANDARD PROBE light.
* PROBE light: U{12..48} (both colours; not among the nine targets), 3 000-episode panel, seed 9 300.
* Receiver fragility φ(s) = regret(Z_ACT_s on PROBE) − regret(Z_ACT_s on ACT)  (the fleet's own policy, its own training light,
  the probe; no specialist, no target light).  Same for M_ACT (φ_M).
* Cells: (s, L) with a specialist available — s = 0–4 for L ∈ {EXT, CUT}, s = 0–2 for L ∈ {FT, A1 … A6}; target Δ(s, L) =
  regret(Z_ACT_s on L) − regret(Z_L_s on L).
* Predictions (exploratory, fixed now): C0c-1 Spearman over the cells between the product φ(s)·K(L) and Δ(s, L) ≥ 0.6;
  C0c-2 that Spearman exceeds the one of K(L) alone over the same cells (the receiver side adds information); C0c-3 within each
  light with ≥ 3 seeds, the seed ordering of φ(s) matches the ordering of Δ(s, L) in at least half of the lights (reported).
* If φ barely varies across seeds (all seeds equally robust), C0c is uninformative and is reported as such, not as a failure
  of the product model.

## Deviation 3 (written 02/10/2026 18:5x EDT, after the Q-regression development run (seed 0, 600 episodes), before any full run)
* What the development run showed: regressing the PRIVILEGED teacher's values still left the students worse than the rule car
  on their own light (Z_ACT on ACT 19.4 vs rule 13.7) and one message student diverged (M_ACT 31.6 on ACT).  The privileged
  teacher's values assume the future schedule is known after the current action, so they are optimistic for a car that will
  never know it.  In this testbed the information sets are small enough to compute the EXACT Bayes-optimal policy of each:
  Z sees (x, v, colour, τ) and the light is a renewal process, so (colour, τ) is Markov with the hazard of the duration law;
  M sees the residual r, so (colour, r) is Markov with the next duration drawn from the law.  Both are finite stationary MDPs,
  solved by value iteration.
* A defect found while deriving them: the episode generator drew the FIRST phase's duration from the law and its elapsed time
  uniformly, which is not what a car arriving at a random time sees (it meets a LENGTH-BIASED phase).  With the old draw the
  hazard a car could infer from τ in the first phase differs from the law's, and the distribution of views a car meets differs
  from the light's own time-average log (the object of Addendum C0b).  Fix: the first phase is drawn length-biased
  (P(d) ∝ d·p(d)), elapsed time uniform on 0..d−1 (a stationary renewal process).  All panels are recomputed under the fixed
  generator (the v2 panels stay on disk, superseded, not deleted); the privileged DP teacher, the regret metric and every
  prediction and threshold are unchanged.
* Change to the students: they regress the exact Bayes-optimal action values of THEIR OWN information set (Z: the Z table; M:
  the M table) under the episode's light law, at states visited by the ε-noisy Bayes-optimal driver and by the student (2 DAgger
  rounds); MIX students are labelled with the table of the episode's own law (mode-aware labels).  The Bayes tables themselves
  are also evaluated on every panel as an exact reference ("Z*", "M*"; outside a table's range τ or r is clipped to its edge).
* Consequence for C0-3 (FT): under the deterministic light r = 30 − τ, so Z* and M* must coincide exactly — a self-check.
