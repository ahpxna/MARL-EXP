# Destination (W1 of the one-hour wakes) — first version 03/10/2026 02:5x EDT, wake 1

## 1. The destination in one sentence
**Paper 1 (primary, ICML 2027, abstract ≈ 16 Jan, paper ≈ 22 Jan 2027 — estimated dates, CfP not yet out; fallback NeurIPS
2027 or TMLR):** *Upgrading a channel can break the learned receivers that use it — even when the upgrade adds information —
because the deployed receiver's excess risk, governed by its training support, grows faster than the information gain; the
hazard is predictable from the channel side and repairable by changing the receiver's support or garbling the new channel
back into it.*
**Paper 2 (city, later):** independently updated learned traffic agents need receiver-relative, behaviour-carrying
compatibility contracts; a producer-side compatible mode is cheap; region + exposure alone is not sufficient.  Target after the
benchmark tier (IEEE T-ITS / TR-C, or an AAMAS 2028 / NeurIPS 2027 D&B angle).
Passed or unusable: ICLR 2027 (paper 25 Sep 2026), AAMAS 2027 (abstract 1 Oct, paper 8 Oct 2026).  AAAI fast track to AAMAS
(11 Dec 2026) is only for AAAI-reviewed papers.

## 2. Why the story is interesting, novel and practical (current honest version)
* Interesting: the counter-intuitive direction — a BETTER channel hurts; the RI testbed shows it even when the Bayes risk
  falls at every λ (0.619 → 0.223) while the frozen receiver's MSE rises 0.634 → 2.982 (λ 0.4).
* Novel core (after the 03/10 search; NOVELTY_POSITION Addendum 1): the upgrade direction for learned closed-loop receivers,
  the information-vs-excess split measured in MARL (4×4: −9.35 = +0.22 information − 9.57 excess), support (not freshness /
  distance) as the organising variable with a prospective channel-side rule, under a compiled-silence bar.  NOT ours: train/
  inference conditional mismatch bounds (Shisher–Sun Lemma 3), delay-robust training (CALF, Rainbow DC), current-state
  compensation for fresh-trained policies (Decoupled DC), update-compatibility trade-offs (Bansal 2019).
* Practical: connected-vehicle / V2X stacks are upgraded piecewise (DSRC → C-V2X, message-set revisions, RSU firmware) while
  deployed learned controllers stay frozen; operators need a pre-deployment test and a cheap repair.  We have NO real
  controller logs, J2735 traces, independent vehicle stack or real cross-version data — the paper must say so and claim
  simulation evidence only.

## 3. Publish checklist (status at wake 1)
| Item | Status | Gap |
|---|---|---|
| Central phenomenon, ≥ 2 networks, ≥ 10 seeds | 3×3 (many panels), 4×4 10/10 seeds | NYC 16×3 paused (moves after #3 or to the other machine) |
| Information-vs-excess split (G1) | RI exact Bayes; E3 matched-receiver proxy from report means | paired per-seed recomputation (agent B, wake 1) |
| Mechanism: support | train-match rescue, mixture, support diagnostics, double dissociation | relayMIX 4×4 (test D finishing), C0 / G3 weighting |
| Prospective prediction | rule A (C-rel) 3/3; W1 law ordering only | NYC N-predictions |
| Repairs | train-match, mixture; fallback #3 (3×3 102/105, 4×4 37/110) | emulation / garbling adapter in E3 (G2, protocol to write) |
| Published baselines | none run | (LITERATURE_DEEP_READ_20261003) compatibility / negative-flip rate vs the receiver's own pre-upgrade decisions (Bansal 2019, SIL-C backward transfer); a dissonance-penalised receiver fine-tune; CALF-style randomised-channel training (≈ relayMIX) in a full train × deploy matrix with paired tests; an age-aware (CoDe / CGDC-style) receiver trained at K1; the masked-message same-receiver reference beside Z and the Δ_info diagnostic (CGDC); a χ²-quantile (Mahalanobis) support gate as the standard fallback baseline (SIL-C); the receiver-side emulation (G2, queued) as the direction-correct answer to Decoupled DC |
| Theory | Lean floors / support hazard / mixture bound compiled; T1 / T3 | scope fix (G7: reconstruction vs task vs frozen-receiver floor); full gate re-run |
| Statistics | paired CIs, sign counts, pre-registration | multiple-comparison note; effect sizes in one table |
| Manuscript | paper_marl_v2.tex is stale ("Fresh Coverage …") | rewrite around §1 |
| Reproducibility | scripts + protocols + manifests | commit (user decision), env pins, data licence note (CoLight NYC not redistributable) |

## 3b. Update 07:5x (wake at 07:41)
Done since v1: G1 split (L-292 area, NOVELTY Add. 2), train × deploy matrix, flips (L-292), fallback (L-293), mixture (L-294),
emulation (L-295), G7 scope.  Novelty narrowed: RDC (NeurIPS 2025) observed the upgrade-direction drop (Add. 3).  The single
largest remaining gap for an ICML submission is UNIVERSALITY on a standard benchmark: MPE with RDC-style aged copies
(simple_tag vs simple_reference control), ≈ 40 runs — requires the user's permission to download EPyMARL / MPE2 (or RDC-pymarl).

## 4. What remains, in order (to be revised every wake)
1. Finish the running evidence: test D report (D1–D3), fallback report (FB1–FB6), then NYC.
2. G1 paired split for E3 (agent B) → the central figure (RI Bayes + E3 matched proxy, both directions).
3. G2: protocol + smoke + queue for the E3 emulation / garbling adapter (eval-only on existing checkpoints).
4. G3 on C0 tables; Q7b's B4/B4' says in-support harm is real — weight OOS by decision disadvantage.
5. Published-baseline tier for E3 (randomised-channel training; estimator wrapper; one standard comm-MARL baseline).
6. Rewrite paper 1; Lean scope fix (G7); full gate.
7. City: after Q7b (B1 failed as robustness, B2 held, B3 failed, B4 held, B5 failed) — G4 (closed-loop contract with a
   receiver behaviour stub) and G5 (receiver-specific cap) before any benchmark tier.
