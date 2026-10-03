# Paper 1 (E3) — outline and claim → evidence map, v1 (03/10/2026 03:5x EDT, wake 2)
Target: ICML 2027 (estimated abstract ≈ 16 Jan, paper ≈ 22 Jan 2027).  Replaces the stale paper_marl_v2.tex ("Fresh
Coverage …"), which predates every result below.  Nothing here is a theorem claim beyond what has compiled Lean (scope: G7).

## Working title
"Better Channels, Broken Receivers: Training Support Decides the Compatibility of Learned Communication" (alt.: "When
Fresher Messages Hurt: the upgrade hazard of frozen learned receivers").

## Correction 07:5x (NOVELTY_POSITION Addendum 3)
RDC (NeurIPS 2025, Figs 8–9) already observed delay-trained MARL policies dropping at delays 0–2 (read as a generalisation failure).
The story must NOT claim discovery of the phenomenon; it claims its measurement against silence, its decomposition, its
support (joint-configuration) mechanism with a prospective channel-side prediction, decision-level flips, and which repairs
work.  Related work: cite RDC first among the delay papers.

## One-paragraph story
Multi-agent controllers that learn to use messages are trained on one channel and deployed while the channel keeps changing.
The usual worry is degradation (delay, loss).  We show the reverse: UPGRADING the channel — fresher, higher-capacity relays —
can push a frozen learned receiver below a zero-byte silent student of the same teacher.  The loss is not an information
loss: matched receivers gain information from the upgrade, the deployed one loses through its own excess risk (RI testbed:
exactly, Bayes risk falls at every drift while the frozen MSE rises ×4.7; E3: information ≥ 0, excess < 0 in 20/20 seed pairs).
The excess is organised by the receiver's TRAINING SUPPORT, not by freshness or distribution distance: support exits predict
it channel-side (rule A), matched or covering training removes it, relabelling inputs makes it worse, and a support monitor
can fall back to the silent student.  Lean formalises the floors and the support hazard.

## Contributions (and what they rest on)
| # | Claim | Evidence (ledger) | Status |
|---|---|---|---|
| C1 | Runtime communication must clear a same-teacher compiled-silent student Z; relay + age-first does under capacity limits | L-105…, 10-seed reserved panel; 4×4 L-270 | done |
| C2 | Upgrade hazard both directions: a K1-trained receiver loses on iid (4×4 +5.80 → −3.55 vs Z, 10/10), an iid-trained one on K1 | L-250, L-286 (GTM3), L-256 | done (3×3 + 4×4); NYC pending (paused) |
| C3 | Information vs excess split: RI exact Bayes (λ 0.4: Bayes 0.619 → 0.223, frozen 0.634 → 2.982); E3 matched-receiver proxy (4×4 +0.22 / −9.57; 3×3 +0.83 / −2.94; excess < 0 in 20/20 pairs both directions); C0 exact (excess rises on 8/9 lights) | NOVELTY_POSITION Add. 1–2 | done (proxy caveat: Spearman 0.33 vs exact floor in C0); cite BCT's update gain (Shen 2020) as the precedent of the normalised split |
| C4 | Support, not freshness / distance: equal-W1 receivers differ (RI L-277), double dissociation (L-272), W1 ranks but magnitude does not transfer (L-282), prospective channel-side rule A (C-rel 3/3, L-270) | L-249, L-258, L-270, L-272, L-277, L-282 | done; NYC N-predictions pending |
| C5 | Repairs: matched training (L-250, L-286), mixture with a premium ≈ 0.5–1 pt (L-256, L-287), support fallback to Z (#3), input relabels FAIL (L-266, L-274, L-279) while coupled emulation is the direction-correct input edit (G2) | L-250, L-256, L-266, L-274, L-279, L-286, L-287 | DONE: fallback L-293 (4×4 FB1–FB6 all supported; FB3 support 100 % vs freshness 0 %; conservative at K2/K3), mixture L-294 (minimax on 4×4, premium ≈ 0.5 pt), emulation L-295 (beats relabel, not a repair: joint support) |
| C6 | Lean: receiver floor, net floor, support hazard, mixture bound, emulation monotonicity, no receiver-free certificate | L-241, L-262, L-264, LeanCityReceiverContractV1 | compiled, smoke-gated (full gate stopped 33/315); wording per G7_FLOORS_SCOPE: 'knowledge floors', not decision floors; add City/DecisionDepth/CommValue to verify_all.sh |

## Figures / tables (drafts in research/papers/_figures/paper1_draft_20261003/, 08:0x 03/10)
1. Train × deploy matrix (3×3, 4×4; receivers × K) with the diagonal marked — agent B assembling (wake 2).
2. Split bars: information vs excess (RI exact, C0 exact, E3 proxy) — data ready.
3. Rule A: predicted K_min vs observed crossing (3×3, 4×4, NYC).
4. Repairs: matched / mixture / fallback / relabel / emulation, gain vs Z at the upgraded channel.
5. Support diagnostics: out-of-support share vs loss within each network (FB6 when the fallback report lands).

## Baselines a reviewer will ask for (LITERATURE_DEEP_READ_20261003) — status
| Baseline / metric | Source | Status |
|---|---|---|
| Randomised-channel training in a full train × deploy matrix | CALF | ≈ relayMIX done; matrix being assembled |
| Compatibility / negative-flip rate (NFR, BTC/BEC) vs own pre-upgrade decisions on IDENTICAL states | Bansal 2019, PCT, Srivastava 2020, SIL-C | DONE (L-292): CK1 K1→iid net −0.067 (3×3, 5/5) / −0.084 (4×4, 10/10), BTC 0.86 vs MIX 0.95; iid-trained iid→K1 −0.089; FL1–FL4 supported |
| Positive-congruent / dissonance receiver fine-tune; receiver population (ensemble) | PCT, Bansal, Calibrate-your-listeners | not run |
| Train × deploy matrix | CALF | DONE: e3_train_deploy_matrix_20261003 (diagonal best 30/30; CK1 monotone down; MIX CALF-like with ≈ 1 pt K1 premium) |
| Masked-message same-receiver reference π^(−0) beside Z; Δ_info diagnostic | CGDC | not run (eval-only; do not edit MARL_e3_ageclip_eval.py while test D uses it) |
| χ²-quantile (Mahalanobis) support gate as the standard fallback baseline | SIL-C | not run (after #3) |
| Age-aware receiver (CoDe / CGDC-style gated attention) trained at K1, deployed at iid | CoDe, CGDC | not run (training cost) |
| Current-state estimator wrapper | Decoupled DC | argued off-direction; emulation is the analogue (queued) |
| Standard comm-MARL (CommNet / TarMAC / IC3Net) on 3×3 | — | not run |
| Universality on a standard benchmark | RDC framework (MPE simple_tag vs simple_reference control) | recommended by survey (≈ 40 runs, ≈ 1–2 days CPU, not verified); needs downloads → user permission |

## Related work positioning (one line each)
Bansal 2019 (principle, human receiver) · Shisher–Sun 2022/2024 (fresher-can-be-worse at the information level; Lemma 3 mismatch
bound assumes full support) · CALF / Rainbow DC / DACOM / CoDe / CGDC (delay robustness, downgrade direction; CALF shows no
upgrade hazard) · Decoupled DC (input repair for fresh-trained policies) · CTDS / PTDE / KD-MARL (silent students as methods) ·
SIL-C (support-gated compatibility for frozen skill users) · Johansson et al. 2019 (support in domain adaptation).

## Limitations to state
Simulation only (CityFlow grids + one real-topology NYC grid with taxi-derived routes); our own trained receivers; no real
controller logs, no J2735 traces, no independently developed vehicle stack, no real cross-version data; the E3 information term
is a matched-trained proxy; single training recipe family (distillation from one teacher per seed).
