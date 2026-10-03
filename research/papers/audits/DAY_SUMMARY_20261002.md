# What was found and verified on 02/10/2026 (written 19:5x EDT)

Sources: MARL ledger research/papers/audits/MARL_SELF_AUDIT_LEDGER_20260928.md (rows L-249 … L-285), city ledger
research/city_sim/CITY_LEDGER_20261002.md (C-1 … C-3), the protocols named in each row.  "Supported" = a prediction registered in
a protocol BEFORE its run held; development looks are not results.

## A. MARL / E3 (relay communication vs the zero-byte distilled student Z)
| Ledger | Result |
|---|---|
| L-249 E1 | ML1, ML2, ML4 supported, ML3 not |
| L-250 train-match (5 seeds) | training at the deployment channel rescues the receiver (TM1, TM2, TM4); a FRESHER channel hurts a receiver trained on a staler one (P-UP1, P-UP2) |
| L-252 architecture control | the failure is generic: it holds for attention pooling and per-slot concatenation (AC1) |
| L-256 E4 mixture | mixture training repairs (MX1, MX2, MX4); it is not the union of specialists (MX3 not); specialist premium ≈ 1 point |
| L-258 W1 replication | the W1 mismatch law replicates with frozen parameters |
| L-270 second network (4×4) | relay beats Z (+6.26 / +5.78 / +2.93 %); the K = 1 reversal replicates (−2.41 %, G1–G3); the N_s law fails (R2); the 3×3 clip does not transfer (G4); rule A in the training-relative coordinate holds prospectively (C-rel 3/3) |
| L-261, L-263 remote-inference testbeds | the upgrade regression reproduces (5/5) and needs age to act as a PROPAGATION horizon (drift); remap harm grows with drift |
| L-265 age-role probe | classifies the age role, does not grade the dose |
| L-266, L-274, L-279 interface repairs | age transport, onefresh projection and time projection all hurt: never relabel in-range inputs |
| L-268, L-272 support diagnostics | double dissociation: max age is out of support on 3×3, late low coverage on 4×4 |
| L-277 equal-W1 test | at equal distance the covering receivers reach 0.978 / 0.979 vs 0.899 for the disjoint one: SUPPORT, not distance |
| L-278 H-RID | the mixture receiver identifies the regime it is in |
| L-282 W1 prospective | the W1 ordering holds (W1a); its magnitude and shape do not (W1b, W1c); the out-of-support stale count explains the sign flips (−0.853 vs W1 −0.825) |
| L-283 | teacher quality drives the per-student fragility axis (ρ −0.83) |
| L-285 A, B | the clip rule is receiver-specific (worse than plain in the testbed); a mixture receiver tracks channels that switch within an episode (SW1, SW2) |
Lean (compiled clean, standard axioms, smoke-gated): MismatchW1V1, EmulationV1, ProvisioningV1, SupportV1, HoldFloorV1,
MixtureV1, AgeRoleV1, ProjectionV1, ProvisioningInstancesV1 (all in verify_all.sh MODS; the full gate was stopped at 33/315 on the
user's instruction and is still to be re-run).
Thesis these support: "support, not freshness" — what decides whether communication helps a learned receiver is whether the
deployment view lies in its TRAINING SUPPORT; the network can predict where support breaks (floor, provisioning, rule A), can
emulate the support after an upgrade but not after a downgrade below the floor; the robust fix changes the support (matched or
mixture training), not the input.

## B. City track: lights and cars that both learn (new today)
Infrastructure: SUMO 1.27.1 in a separate venv; Midtown Manhattan from OpenStreetMap (248 lights) and a live browser viewer;
NYC 16×3 CityFlow data (CoLight; same structure as the E3 grids; for the E3 third network, queued after test D); a 4 × 4 SUMO grid
with fixed, actuated, actuated-variant and delay-based lights.
Direction (research/papers/audits/CITY_TWO_POPULATION_NOVELTY_20261002.md, §6, narrowed after an external collision audit whose
citations were verified through Crossref / OpenAlex / Semantic Scholar): backward-compatible upgrades of independently updated
learned partners — an upgrade can break an already-deployed learned receiver; whether it does is predictable from the upgraded
side's own logs before cross-play; repairs on either side; intent messages valued against compiled silence.  Not claimed:
"lights and cars both learn", "joint beats separate", "OOD signal timing hurts", "SPaT helps", "mixture is robust", "a better
component can hurt the team" (all taken in the literature).
| Ledger | Result |
|---|---|
| C-1 Q2 | eco-driving that is good alone (fixed-time lights: −6 % fuel, −24 % stops, +2.5 % time loss) makes sensing lights worse: +47 points of time loss under halting-count lights, +70 under SUMO actuated (fuel +10 %); the halting metric reports an improvement that does not exist; the hidden-queue mass from fleet-only logs ranks the harm; vehicle-count sensing removes about half (E3 failed by 0.2 points) |
| C-2 Q3 | vehicle-carried neighbour information is stale at BOTH ends of demand (110 s at 450 veh/h, 14 s at 7 200, 172 s at 14 400): a U shape; 24–40 % of light-seconds at the extremes are older than anything seen at the training demand; the closed form L/u + 1/q is right only on average (per-link r 0.70–0.75) |
| C-4 Q2b | the harm survives every eco design (+41 … +128 points under actuated); SPaT-aware GLOSA is the WORST because the actuated light's own prediction is wrong; under fixed-time lights GLOSA works (+2.9 % time loss, −33 % stops); no light-side fix halves the harm (best: delay-based sensing, 128 → 72) |
| C-5 Q4 | re-timing ONE light of a green wave (its own timing law unchanged, so every per-light certificate is 0) harms the car trained on the old corridor (Δ +8.7 [6.5, 10.6]; up to +30.5 at the opposite offset) while the exact table is unharmed; the corridor (joint-log) certificate ranks the harm perfectly (Spearman 1.00); a range monitor is blind, a density monitor sees it (1.00) |
| C-3 C0 | a light upgrade that extends phases breaks the legacy learned car (Δ +19.8 [7.1, 40.3]; exact Bayes tables 135 vs 4.5); one that switches earlier inside the trained range does not (Δ +0.23, CI contains 0); an input-support monitor sees the first (29 % out of support) and its fallback recovers more than half; the SPaT residual makes the car nearly immune (ΔM 2.8; exact M* 0.01); a certificate from the light's own logs ranks the harm (Spearman 0.78 for students, 1.00 for exact tables) but the support-exit term alone does best (0.91): the hazard (semantics) term and the receiver-side factor add nothing here; mixture is not minimax (the broadest specialist wins); quantile relabelling HELPS here, unlike E3 |
Lean (compiled, 0 errors, standard axioms; not yet in the frozen gate): LeanCityConditionalShiftV1 (an upgrade with the same view
distribution but a new meaning is invisible to every input monitor; the message rule is optimal under both lights — a formal
witness of a standard fact), LeanCityInfoFundamentalV1 (minimal age (√(a+b)+√b)² at ρ* = √b/(√b+√(a+b)); the age exceeds any
training ceiling at both ends of density).
Net reading: the city direction stands on its SUPPORT half (hazard in both directions, a partner-only certificate, a monitor
repair, message insurance); the semantics half and the two-sided predictor are not supported by the experiments.  The decisive
missing piece is an upgrade that is a LEARNED controller, genuinely better on its own objective, that breaks a LEARNED partner (Q7).

## C. Running / queued at 19:5x
* MARL: 4×4 train-match at K = 1 (round 2), then test C (3×3 mixture of K1 + iid), test D (4×4 mixture), NYC 16×3.
* City: Q5 (honest commitment windows) running since 19:41; Q4 finished (C-5).  Q6 (rule A in
  V2I) needs a student-quality fix before it is queued; Q7 / Q8 not coded.
