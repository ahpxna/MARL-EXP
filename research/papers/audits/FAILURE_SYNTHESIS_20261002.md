# What the failed predictions say (written 02/10/2026 23:0x EDT; user 22:5x "tất cả những chỗ test fail … học được gì,
# kết hợp được với kết quả nào, đã dự đoán trước chưa, fail vì sao, giả thuyết mới là gì?")

Scope: every registered prediction scored NOT SUPPORTED in the reports listed in research/dashboard/registry.json (E3 and the
city track, 01/10 – 02/10: 38 failures, 4 void, 2 with caveats), plus the readings recorded in the MARL ledger
(research/papers/audits/MARL_SELF_AUDIT_LEDGER_20260928.md) and the city ledger (research/city_sim/CITY_LEDGER_20261002.md).
The earlier E3 items (to 01/10 13:00) were already grouped in L-276 into four patterns; they reappear below.  Failures of a
DESIGN (not of a hypothesis) are kept apart (F6).  "Predicted?" = whether a failure was written down BEFORE the result.

## F1 — editing the receiver's INPUT (relabel / projection / clip) does not repair, with one exception
| Failed | Result | Predicted? |
|---|---|---|
| RM1, RM2, RM3, RM5 (L-266) age remap = transport of the age marginal | remapped receivers fall BELOW Z (−2.6 … −5.4 %) | no — RM1 was predicted to SUCCEED (and the probe's cross-domain PR3 predicted it too) |
| SP1–SP3 (L-274) onefresh projection | −2.9 / −7.4 / −11.4 % vs plain | no (predicted repair) |
| GTM5 (L-286) onefresh on 4×4 | −17.8 % | no (written 12:54, before SP's result at 13:1x) |
| TP1 (L-279) time projection on 4×4 | −2.2 % vs plain, 10/10 seeds | **yes**: L-274's rule, recorded before the result, predicted this failure |
| G4 (L-270) the 3×3 age clip on 4×4 | +0.18 %, CI over 0 | no |
| A2, GT1 (L-211, L-221) clip / freshness gate "never worse than Z" | both repair only half (+0.79 / +0.78 %) | no |
| CL1 (L-285) clip on a downgrade in the RI testbed | below plain everywhere | no |
| AR2 (L-263) driftless remap harm ≤ 0.02 | 0.026 | no (marginal) |

Why: each edit changes what an IN-RANGE value means to a receiver that uses it — age as a propagation horizon (L-263, L-274),
the decision step carrying the demand phase (L-279).  Matching the marginal (W1 → 0 after the remap) is not matching the
meaning (LeanMarlProjectionV1 `transport_harms_optimal`).  The clip works only on values outside the trained range AND only if
the receiver's response there is erratic (3×3 yes, RI MLP no: L-285); the gate only acts where its trigger fires (half).
**The exception:** C0-5 — quantile relabelling of time-in-phase HELPED the car under the phase-extending light (29.3 → 11.4).
What works instead: switching the ACTOR (C0 fallback 29.3 → 15.8; the 01/10 gate +0.78; #3 running), constraining the
PRODUCER (Q7 compatible mode: 91 % of the light's gain kept, car harm 30.2 → 6.4), or changing the receiver's support (matched
or mixture training, L-250, L-256, L-286).
**H1 (new):** an input edit repairs iff it preserves the CONDITIONAL law of the decision-relevant hidden quantity given the
edited input (decision sufficiency), not its marginal.  C0's quantile map sends "τ seconds into a long EXT phase" to "the same
fraction of an ACT phase", which roughly preserves the law of the time to the switch; E3's remap labels CURRENT entries as old,
which inverts it.  Test (computation only, C0's exact model + E3 composition tables): the conditional TV before vs after the
edit must fall where the edit helped (C0-5 EXT) and rise where it hurt (RM, SP).

## F2 — scalar, receiver-free predictors rank but do not measure
| Failed | Result |
|---|---|
| W1b, W1c (L-282) W1 law magnitude / shape on a new training channel | ordering right (W1a), magnitudes off by up to 1.75 points |
| ML3 (L-249) crossing location | at K ≈ 2, not between 1 and 2 |
| R2, R4, R5b (L-270) N_s law, margin, dev net_Z at low on 4×4 | the 3×3 law does not transfer (Spearman 0.24) |
| BF1 (01/10) fresh-witness rate | 0.074 vs 0.065 (need 1.2×) |
| PR1, PR2 (L-265) the age-role probe as a dose meter | a classifier, not a dose |
| I2 (C-2) Q3 closed form per link | Pearson 0.70 / 0.75: right on average only (platoons are not Poisson) |
| C0b-2, C0b-3, C0c-2 (C-3) composite certificate, hazard term, φ·K | support exit alone 0.91 beats K 0.78; φ·K 0.71 < K 0.73 |
| Q7-3 (C-7) the light's own log statistic | 4.4 % of green-seconds vs 18.6 % of the cars' decisions out of support |
Predicted? None (all registered as successes).  What survived in the same experiments: every ORDERING (W1a, ML1, ML4, C0b-1
with exact tables 1.00, Q4-2 1.00, E6, BF2's teacher-need ranking 0.98).  The 4×4 W1 slope is 2.21 vs 1.25 on 3×3 (GTM4).
Why: each statistic is a property of the shift alone; the receiver supplies three things the shift does not contain — its
support region, its exposure (where it actually samples inputs: cars decide every second while queued, so long phases weigh
4× more in Q7) and its sensitivity there.  LeanMarlSupportV1 `upgrade_hazard` (+ the new corollary
`no_receiver_free_certificate`) proves that no function of the two laws alone can be right for every training-optimal receiver.
**H2:** within one family of shifts any monotone shift statistic ranks the harm; magnitudes (and cross-receiver, cross-network
transfer) need receiver-side terms: support + exposure (+ sensitivity).  Tests registered: Q7b B3 (receiver contract with
exposure beats the receiver-free statistic and matches the cross-play out-of-support share within ×2); #3 FB6.

## F3 — mixing training regimes is not the same as covering the deployment
| Failed | Result |
|---|---|
| MX3 (L-256) mixture = specialist everywhere | −1.05 at K1 (0/5): a premium of about 1 point |
| C1, C2 (L-287) two extreme channels cover the middle and keep the extremes | −0.5 / −0.6 at K2 / K3; −0.55 vs the iid specialist |
| C0-4 (C-3) mixture is minimax | the broadest specialist (EXT) wins: 9.8 vs 14.5 |
Why: support is JOINT over view configurations (test C; the double dissociation L-272); a fixed-capacity receiver pays a
premium per extra regime (≈ 0.5–1 point); and when one regime's support CONTAINS the others' (EXT ⊃ ACT in time-in-phase),
training on it beats mixing.  Combines with: SW1–SW2 (the mixture identifies and tracks regimes it has seen), L-277 (covering
supports recover 92 % at equal W1), the RI mixture (UR3), LeanMarlMixtureV1 (only an ((N − 1)/N) D bound).
**H3:** protection = INCLUSION of the deployment's joint configurations in the training support; mixtures help exactly to the
extent their union contains them, at a premium growing with the number of regimes.  Test registered: FB6 (the out-of-support
share of the generic support monitor ranks the relay's loss within each network).

## F4 — a change of meaning inside the trained range did not hurt (C0) — yet
| Failed | Result |
|---|---|
| C0-1, C0-3 on CUT (C-3) | Δ +0.23 [−0.29, 0.75]; exact tables +0.7 only |
| C0b-3 hazard term inside lights | −0.3 |
Why: CUT changes the meaning of time-in-phase but barely changes the car's optimal action — decision-irrelevant.  Q7 has a
candidate decision-relevant case (the ACT-trained fleet under FT: 0 % out of support, cost 57.7 vs 21.8), confounded with FT
being a worse light (no FT-specialist fleet).  LeanCityConditionalShiftV1 `monitor_blind` says such a shift is invisible to
every input monitor.
**H4:** a semantic shift harms in proportion to how much it moves the optimal action on the receiver's support.  Test
registered: Q7b B4' (fleet L-FT trained under FT; mismatch ≥ 10 with the contract certificate ≤ 0.02).

## F5 — producer-side fixes that constrain the wrong thing are expensive
| Failed | Result |
|---|---|
| P5-1, P5-2 (C-6) honest windows / one revision at the undersaturated demand | +12 % light delay for a window of 10 s, +31 % for REVISE1 |
| B3 (C-4) a light-side sensing fix halves the eco harm | best (delay-based) 77 → 53 only |
| E3 (C-1) vehicle-count sensing removes more than half | removes about half (23.7 vs 23.5 bound) |
Why: the windows constrain in-support freedom on every cycle; the sensing tweaks cannot sense what slow eco cars hide (the
information is not in the detectors).  The one cheap producer-side constraint (Q7's cap at 50 s) removes only behaviour
OUTSIDE the receiver's support (its τ_max is 50).
**H5:** a producer-side contract is cheap iff it removes only out-of-support behaviour.  Test registered: Q7b B5 (knee of the
compatibility frontier at the receiver's τ_max).  H5b (Q2): the missing quantity must be supplied by the partner (V2I) — Q8,
not coded.

## F6 — failures of design or procedure (lessons, not science)
Q5's two higher demands saturated (void; check regimes before registering); Q3's top levels gridlock (teleport artefacts);
#3's first statistic counted 8 slots instead of m − 1 and its 4×4 key was too fine (both caught by smoke / training-episode
calibration before any panel run); run_in_background jobs died with the session (now nohup); a running script was edited
(smoke only).  The 01/10 gate (L-214/L-221) was not cited in #3's protocol at first (Addendum 2).

## The common reading
The failures are not scattered: each one removes a RECEIVER-FREE or MARGINAL shortcut — editing the input's marginal (F1),
summarising the shift by one number (F2), mixing instead of covering (F3), an input-invisible meaning change that the decision
ignores (F4), constraining the producer where the receiver does not care (F5).  What remains standing is one object:
**compatibility of an upgraded producer U with a frozen receiver R is decided by whether R's decision stays sufficient on
the views U now produces** — support INCLUSION in R's joint view space (E3, test C, Q4), weighted by R's exposure (Q7-3's
gap), and, inside the support, by whether the decision-relevant conditional law moved (CUT no, FT ?).  This is the
"receiver-relative, decision-sufficient compatibility contract" of the two external reviews (CITY_TWO_POPULATION_NOVELTY §7),
reached here from our own failures.  Formal side: `no_receiver_free_certificate` (T1) and the parity witnesses (T3) in
work/p13_conjectures/LeanCityReceiverContractV1.lean (compiling).
Registered tests of the new hypotheses (all before their results): FB6 (#3, H3), Q7b B3 (H2), B4' (H4), B5 (H5).  H1 needs only
a computation (C0 exact model + the E3 composition tables).

## Correction (23:1x, after the Q7b pipeline smoke) — F2's Q7-3 explanation was stated too strongly
F2 said the 4.4 % vs 18.6 % gap is EXPOSURE (cars deciding every second while queued).  The Q7b smoke (900 s, one seed, the
real Q7 checkpoints, NOT evidence) gives, for RL-H: receiver-free 0.046, contract-with-exposure 0.036 from its HUMAN-traffic
logs, but 0.131 from its logs WITH the L-ACT fleet present, and a cross-play out-of-support share 0.19.  So exposure explains
little; most of the gap is the LIGHT CHANGING ITS OWN BEHAVIOUR when the frozen fleet is present (the fleet's driving changes
the queues the light reacts to).  **H2b:** between mutually adaptive partners the compatibility shift is closed-loop — a
certificate computed from the upgrader's logs without the receiver's BEHAVIOUR underestimates it; a sufficient contract must
carry a behaviour model (or a simulator stub) of the receiver, not only its accepted region and exposure.  Q7b B3 (registered
before this smoke; t = 0's smoke rows were seen, so B3 at t = 0 is no longer blind) is kept as written; its expected failure
mode is now H2b.
