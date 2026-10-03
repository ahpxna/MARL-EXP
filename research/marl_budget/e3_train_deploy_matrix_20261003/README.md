# E3 train × deploy matrix (03/10/2026 03:5x EDT, wake 2; subagent B, read-only recomputation; spot-verified)

Recomputed from rows.json of 17 FINISHED panels (13 on 3×3, 4 on 4×4); gain vs Z = −(ΣR/ΣZ − 1)·100 per seed over 128
episodes; 95 % two-level bootstrap (seeds, traffic seeds).  Point estimates equal the stored reports on all 16 panels compared
(spot-checked here: 3901 relayCK2 −2.66 / +2.86 / +2.50 / +0.61 = e3_w1_prospective report; 3801 MIX K1 +0.97 and premium −1.05 =
L-256).  Scripts: inventory.py, matrix.py (→ matrix.json, sha256 ecd6265b…), analysis.py, pooled.py, flips.py; g1_g3_wake1/ holds
the wake-1 G1 / G3 scripts and outputs.  Excluded (pending or not opened): test D panel 4601, fallback, 4×4 MIX, age emulation,
NYC.  Provenance: 896 manifests COMPLETE + PASS; 632 record a checkpoint sha, all equal to the current files; no sha in any Z
manifest nor in the relay manifests of panels 2801 (CKPT_SHA256.txt matches 10/10), 3001, 3601, 2901; evaluator mix (ageclip /
projection none / switch; relay_v6 / satrot on 2801, 3001, 3601, 2901 — equivalence asserted in L-204, not re-verified).

## Pooled (per seed over panels; seed bootstrap; cells mix seed sets)
| Receiver (trained on) | K1 | K2 | K3 | iid |
|---|---|---|---|---|
| 3×3 6Cage (iid) | −1.53 [−2.62, −0.60] | +1.10 | +1.76 | **+2.14** |
| 3×3 CK1 (K1) | **+2.33** [+1.30, +3.35] | +1.79 | +1.27 | +0.17 [−1.84, +2.12] |
| 3×3 CK2 (K2; one panel) | −2.66 | **+2.86** | +2.50 | +0.61 |
| 3×3 MIX (all four) | +1.05 [+0.46, +1.67] | +1.97 | +2.18 | +2.24 |
| 3×3 MIX2 (iid + K1; one panel) | +1.99 | +2.34 | +2.67 | +2.73 |
| 4×4 Cage (iid) | −2.49 | +2.34 | +5.20 | **+6.20** |
| 4×4 CK1 (K1) | **+5.80** | +2.15 | +2.00 | −3.55 |

## Findings
1. The diagonal (deploy = train channel) is the best cell in 30 / 30 receiver × panel rows that contain it.
2. Shapes: iid-trained receivers rise monotonically with channel quality (ρ > 0 on every seed) — their failure is the
   DOWNGRADE (3×3 iid → K1 −4.74, 4×4 −8.66); K1-trained receivers fall monotonically (iid < K1 on 28/29 seeds 3×3, 10/10
   4×4); the K2-trained receiver is PEAKED at K2 (both directions hurt: K2 → K1 −5.52, K2 → iid −2.25); mixtures rise and
   saturate (CALF-like) — the hazard belongs to receivers trained on a single non-best channel.
3. Mixture premium on the specialist's own channel: MIX vs CK1 at K1 −1.05 / −0.95 / −1.14 (0/5 seeds each, three panels);
   MIX vs 6Cage at iid ≈ 0; MIX2 splits the cost (−0.40 at K1, −0.57 at iid).
4. Decision level (age-response probes, development episodes 901–904): accuracy vs the teacher-acceptable set — 6Cage K1 0.848
   → iid 0.950; CK1 0.930 → 0.865 (4/4 seeds lower); MIX 0.903 → 0.946.  Negative-flip vs Z exists only for some cells
   (6Cage all K, CK1 at K1, 4×4 Cage).
5. Missing for a Bansal-style cross-channel compatibility rate: the same receiver's actions on IDENTICAL states under two
   channels.  Cheapest fix (B): extend MARL_e3_staleness_meaning_probe.py (already builds several channels' views at identical
   states with Z driving) to record each receiver's argmax and A_0.25 — {6Cage, CK1, CK2, MIX, MIX2} × {K1, K2, iid}, seconds
   per cell, development episodes only.
Reconciling with CALF (LITERATURE_DEEP_READ): CALF's Full Net-Aware is a mixture and its Baseline is the best-channel
specialist — both rise with channel quality, as ours do; CALF's Delay-Only (single degraded channel) also rose on clean
deployment, unlike our CK1 — the contrast to explain (decision relevance of the support exit: H4 / G3).
