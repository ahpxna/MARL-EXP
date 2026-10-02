# Verification of the pasted external analysis ("Decision-Certificate Communication"), 01/10/2026 10:3x–10:5x EDT

The user pasted an external analysis and asked: which numbers are right, what is wrong, which directions are worth
trying, feasibility and novelty.  Everything below was recomputed from the artifacts (read-only).

## Numbers
| § | Claim | Recomputed | Verdict |
|---|---|---|---|
| 2 | ρ(N_s, reserved relay gain) = 0.685; ρ(D_s, ·) = −0.152 | 0.685; −0.152 | ✓ |
| 3 | ρ(N, BYTEBUDGET) ≈ 0.663 | 0.673 (dev BB vs Z, 10 seeds) | ≈ |
| 3 | ρ(N, zero-byte gain) ≈ 0.794 | 0.794 (Z vs set_none); the V-D10 primary vs dev relay gain is also 0.794 | ✓ |
| 3 | ρ(N, full-delivery gain) ≈ 0.866 | 0.758 (full vs Z) / 0.879 (full vs set_none) | ≈ / unclear which |
| 3 | ρ(relay, BYTEBUDGET) ≈ 0.857 | 0.842; **0.818 with the replicate zero-byte students** (no shared comparator) | ≈, robust |
| 3 | ρ(zero-byte gain, full-delivery gain) ≈ 0.945 | 0.939 only when BOTH are normalised by the same set_none_s (0.758 otherwise) | **inflated by a shared denominator** |
| 4 | reserved −2.29 / −2.04 / −1.26 %, s2 −4.64, s5 −0.17, s8 −0.36 | equal | ✓ |
| 4 | "exactly those seeds have low message need" | s8 has the lowest N (0.118) ✓; **s5 is rank 6 of 10 (N 0.316, above the median)** ✗ | partly wrong |
| 5 | BB vs Z −2.3 % [−3.4, −1.1] 9/10; BB vs set_none −4.7 % [−7.1, −2.3]; full vs set_none −4.6 % [−7.0, −2.2] | equal (`scripts/MARL_e3_ten_seed_synthesis.py`) | ✓ |
| 6 | P(zero-message sufficient) 0.689 (s0) / 0.539 (s1); nesting gap 0.267 (20.8 %) / 0.304 (23.7 %) | equal (`e3_decision_depth_report_20261001.txt`) | ✓ but see caveats |
| 20 | `LeanMarlRelayRevisionV1.relay_zero_price` | exists: uniform-linear actor ⇒ age-first prefix optimal, no revision helps | ✓ |
| 23 | `LeanMarlProxyBlindnessV1` | exists: worlds equal on all first-order values, different 2-sets; one pair query suffices; ONE exact 3-message witness | ✓ |
| 24 | hindsight ranking ρ 0.77–0.81; ρ(g3, g_full) 0.44–0.61; forced best-of-N ≈ best 1-action message | 0.77 / 0.80; **0.39–0.61** (11 actors); +11.27 vs +11.02 | ✓ / range slightly off |
| 18 | V-F: under age-first agreement falls with age; under the congestion order it does not | age-first iid/low: non-increasing on both seeds; congestion: non-monotone in all 6 runs | ✓ (its explanation unverified) |
| refs | arXiv 2605.10031 (GMSSC 4.509), 2607.09587 (CoDiMAD), 2604.03785 (CGDC), 2609.26757 (certificate complexity), 2408.05112, 2606.29126 (HiComm); Javdani AISTATS 2014 | all exist with the stated content | ✓ |

## What the analysis gets wrong or leaves out
1. The 0.945 correlation (and the "architecture is not the latent variable" reading built on it) uses two gains divided by
   the same set_none_s: a weak set_none for a seed inflates both.  The relay–BYTEBUDGET correlation does survive a
   change of zero-byte comparator (0.818), so the latent "headroom per seed" reading is supported by THAT number only.
2. §4's "the null seeds are the low-need seeds" holds for s8, not for s5.  ρ = 0.685 leaves much unexplained.
3. §6 numbers come from the V-D v1 probe on the CACHE base (ledger L-194): "zero message" = no FRESH sender, stale
   cached copies kept.  The minimal set was searched only up to size 2 (`minset` ∈ {0,1,2,≥3}); 21.6 % of s1 iid steps
   are ≥ 3 (unmeasured), and the nesting gap = min(depth, 3) − minset is a truncated LOWER bound.
4. §5/§17: BYTEBUDGET changes the channel: under its byte channel every sender gets through (5850 B = full delivery).
   Inside the packet channel no design passed both seeds, and the raw teacher under the prefix is worse than the
   zero-byte student (+3.24 %).
5. §25: "the 12-level codebook is less robust than the 8-level one" is out of date: with five seeds the 8-level one is
   order-robust on 2/5 (L-203), the 12-level on 1/2.
6. §36: the internal novelty audit's verdict on direction A was written before the reserved result (08:30–08:45 vs
   08:46) and not revisited — correct criticism.  But the result supports an EMPIRICAL law; it does not change the
   theory-novelty verdict (EVPI/Blackwell, I2C).
7. §41/§29 (whole-fibre test): interventions on the remote network give the SUPPORT of a fibre, not its probability;
   obstruction MASS needs p(w | o).  Existence of obstructions can be tested by interventions; mass needs a natural
   sampling scheme (logged states with matching local views) or a declared prior.
8. CoDiMAD (2607.09587) already states the fibre problem in MARL words ("the same local observation may correspond to
   multiple global configurations requiring qualitatively different cooperative actions") and fixes mode-averaging
   with diffusion students; our `obstruction_mass_floor` (gated today) says no randomised student beats the obstruction
   mass — a counterpoint to cite, and a narrowing of what "obstruction" can claim as new.

## Directions (feasibility, novelty) — my assessment
| Direction | Feasible now? | Novelty after checks | Pick |
|---|---|---|---|
| Decision-demand predicts communication headroom (flagship): Q(k) curve vs capacity frontier, whole-fibre obstruction test, second network | Q(k): cheap (V-D probes + const-K evaluations for 10 seeds, eval-only); whole-fibre: feasible (CityFlow snapshot/load/push_vehicle/set_tl_phase, clone_state exists), cost driven by rollout length (short horizons are bad labels, ρ 0.39–0.61); second network: 4×4 needs training (seed 0 only exists) | the prospective predictive law was NOT found in the literature (searches: DCMAC, demand-aware comm, I2C, MAGIC, belief-KL gating all use demand to gate, none predicts realised gain across independently trained policies); "obstruction / fibre" itself is not new (Javdani HEC, CoDiMAD, certificate complexity) | **YES — first** |
| Universal-order price + recourse (nesting gap ↔ revision headroom) | data partly exist (V-D nesting gap); revision headroom under relay needs new oracle runs | combinatorics = GMSSC (4.509-approx, 2026); new only as the measured link | as a section of the flagship |
| Freshness-surrogate adequacy + bounded repair (Paper 1 revival) | needs oracle revision headroom + interaction measure | relay_zero_price + ProxyBlindness give a clean kill/go theorem; VIL2C, DFT, I2C crowd the method side | second, only if the flagship's gap ↔ headroom link holds |
| Decision-TTL scheduling | yes | low (AoII, VIL2C, CGDC, DFT) | no |
| Decision-safe successive refinement | engineering-heavy | low–medium (semantic successive refinement, AH-VIB) | no |
