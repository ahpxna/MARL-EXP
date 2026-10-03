# What the dropped results say, what the literature says about the same situations, and the story they make (02/10/2026 13:2x)

User 13:1x: "với tất cả những chỗ bị bỏ, bài học là gì? … có câu chuyện gì cho nó ko? research … có mảnh ghép nào … tạo ra 1
paper novelty hơn, câu chuyện hay hơn?"  Sources: ledger L-200 … L-275; reads today (full text where marked).

## 1. Everything that was dropped or refuted, grouped by what it says
| Pattern | Dropped / refuted items | What they say together |
|---|---|---|
| P1. Outside fixes that change what the receiver SEES fail unless they keep meaning | age transport remap (−4…−7 %, L-266); onefresh projection (−3…−11 %, L-274); relabel in the testbed (−0.50, L-261/263); silence-fallback gate GT1; SafeEdit gate (withdrawn); count-deadline scheduler (zero room, L-240); the 4×4 clip (G4) | Only genuine data from the training regime (emulation / throttle), clipping values that are truly out of range (3×3 only), or retraining (matched, mixture) worked. Relabelling in-range inputs changes their meaning for a receiver that also uses age to extrapolate. |
| P2. Fine-grained proxies of value do not transfer | N_s law (R2 fails on 4×4); teacher margin (R4); per-seed net_Z ranking (R5b, H6); witness-weighted D; volatility weighting (E2); the age-role probe as a dose meter (PR1, PR2) and across domains (PR3) | What survives is coarse and CHANNEL-side (floor, count, W1, provisioning) at the CELL level; per-student behaviour off the training support is not predictable from in-distribution quantities (seed 3 is weak everywhere — a shared per-student axis, ρ −0.818). |
| P3. "Staleness" is not one quantity | absolute-age provisioning (C-abs 1/3 on 4×4); H-A "meaning shift" (SM2, SM3); burden B_3 (beaten by the count); the clip's transfer to 4×4 | The harmful statistic is network-specific (max age on 3×3, coverage persisting late on 4×4: a double dissociation, L-272); the training-relative version of every staleness measure beats the absolute one. |
| P4. Distance is a symptom, not a lever | W1 → 0 by transport made things worse; mixture ≠ union of specialists (MX3; pooled-W1 fit only partial, L-258); the probe's thresholds did not transfer | W1 PREDICTS harm (replicated with frozen parameters) but minimising it is not a repair; what a repair must restore is SUPPORT coverage of the joint view. |

## 2. The same situations elsewhere (read today)
| Our pattern | Closest prior | What it already says | What we add |
|---|---|---|---|
| P4, P1 | Johansson, Sontag, Ranganath, "Support and invertibility in domain-invariant representations" (AISTATS 2019) | penalising distribution distance is wasteful; what matters is whether the SOURCE SUPPORT COVERS the target | the same law for learned receivers of networked information, with the support predicted CHANNEL-side before deployment (floor, provisioning, diagnostics) |
| P1 (transport) | Zhao, Tachet des Combes, Zhang, Gordon, "On learning invariant representations for domain adaptation" (ICML 2019) | matching marginals with small source error is not sufficient; a lower bound on the joint error under conditional shift | input-space version (LeanMarlProjectionV1: any marginal-matching map moves in-support inputs; it can push an optimal receiver below silence) and three measured instances |
| P1 (clip works) | ReAct (Sun, Guo, Li, NeurIPS 2021): truncate activations above an in-distribution percentile | clipping only extreme values is a cheap, effective robustification | the same at the input of a communicating receiver; works only where the out-of-range statistic is per-entry (3×3) |
| P2 | D'Amour et al., "Underspecification presents challenges for credibility in modern ML" (JMLR 2022; full text) | pipelines return many predictors with equal held-out performance and different behaviour under shift; the difference is driven by the seed; recommends stress tests | the channel is a stress test whose LOCATION is predictable by theorem (where every scheduler forces off-support exposure); per-student variation under channel shift is underspecification |
| P2, P3 (shortcuts) | Geirhos et al., "Shortcut learning in deep neural networks" (2020) | decision rules that work in training and fail under slightly different conditions | the receivers' shortcut is the CHANNEL STRUCTURE itself (the fresh flag as a congestion cue, L-90; "exactly one fresh entry" at K = 1, L-274) |
| upgrade hazard | Wi-Fi motion recognition under variable traffic (arXiv 2605.08308): the network's traffic sets the CSI sampling rate; fixed-rate models fail at other rates; fix = rate augmentation; ML-sensor "data cascades" (2206.03266) | infrastructure changes are distribution shifts for learned consumers, both directions | a theory of WHEN (floor / emulation asymmetry) and a measured law of HOW MUCH (W1), with return-level evidence in closed loop |
| systems | Sculley et al., "Hidden technical debt in ML systems" (NeurIPS 2015): CACE — changing anything changes everything; undeclared consumers | upstream changes silently break ML consumers | the network is the upstream; a better network is a data change |
| AoI theory | Shisher–Sun (2404.16281, full text): one predictor over "a variety of AoI values", train and deploy AoI distributions assumed equal; "freshness is not enough" (2606.04361): distribution of updates matters for a fixed LQR | AoI / freshness as the currency of timely inference | for LEARNED receivers the currency is training support; fresher can hurt; the age role (reliability vs propagation) decides the repair |
| mixture | domain randomisation theory (Chen et al. ICLR 2022); "Mixture data for training cannot ensure OOD generalization" (2312.16243) | randomisation is near-minimax; mixtures do not guarantee OOD | the measured specialist premium (≈ 1 point) and the minimax theorem for the channel mixture |

## 3. The story the pieces make: "support, not freshness"
Thesis.  For a learned receiver of networked information, what decides whether communication helps is not how FRESH the
information is but whether the deployment view lies in the receiver's TRAINING SUPPORT; freshness metrics are proxies that
work only when they happen to coincide with support violation.  Consequences, each measured or proved:
1. Fresher can hurt (P-UP2 on 5 panels; remote inference with drift); staler can be harmless (iid-trained at K3).
2. The right staleness threshold is the training range (C-rel 3/3 vs C-abs 1/3 prospectively on the second network; rule A).
3. Which statistic breaks is network-specific (double dissociation: max age on 3×3, late coverage on 4×4).
4. The network can PREDICT where support breaks for every scheduler (receiver floor, net floor, provisioning; Lean) and can
   EMULATE the training support after an upgrade (emulation theorem; throttle +2.3 %), but cannot restore it after a
   downgrade below the floor (proved) — an asymmetry.
5. Outside fixes that move in-support inputs fail (transport, joint projections; Lean: they must move in-support inputs and
   can push an optimal receiver below silence); only clipping truly out-of-range values or genuinely older data help.
6. Equal-in-distribution receivers (seeds) differ off support (underspecification); the channel is a stress test whose
   location the theory predicts.
7. The robust fix is to change the support, not the input: matched or mixture training (minimax theorem; E4).
The dropped results are not noise: items 3, 5 and 6 ARE the refutations (clip on 4×4, transport, onefresh, N_s, margin,
probe) read through the thesis.

## 4. Novelty
Neighbours exist for each ingredient (support vs distance in domain adaptation; underspecification; shortcut learning;
infrastructure-induced shift in sensing; AoI-aware inference).  Not found anywhere read: (i) the CHANNEL-SIDE prediction of
support violation for every scheduler, validated prospectively on a second network; (ii) the upgrade/downgrade asymmetry of
network-side repair with a theorem; (iii) return-level evidence that fresher information hurts learned receivers and that
freshness metrics are proxies for support; (iv) the catalogue of interface repairs that fail, explained by one principle.
The thesis moves the paper from "a MARL communication result" (crowded) to a claim that speaks to three communities at once:
AoI / networking (their currency is wrong for learned receivers), ML robustness (support, underspecification, stress tests),
and ML systems (infrastructure changes are data changes).

## 5. The missing piece, and the cheapest decisive test
The thesis says SUPPORT beats DISTANCE.  None of our results holds distance fixed while varying support.  Testbed experiment
(minutes): deployment δ ~ U{0..3}; receiver A trained on δ ~ U{4..7} (W1 = 4, support disjoint); receiver B trained on an
even mixture of U{0..3} and U{8..11} (W1 = 4 too, but its support covers the deployment); and the converse (equal support
coverage, different W1).  Prediction: B ≫ A although their distances are equal.  Then a channel-side support-violation score
scored prospectively on the pending 4×4 train-match cells.

## Addendum 15:0x — results that arrived after §1–5 (ledger L-277 … L-282)
| Result | Reading under the thesis |
|---|---|
| Equal-distance test (L-277): at W1 = 4 the covering receivers B, C reach 0.978 / 0.979, the disjoint A 0.899 (5/5) | the decisive support-vs-distance contrast — support wins |
| H-RID (L-278): the mixture receiver's age response is regime-conditional (K1-like on K1 views, iid-like on iid views) | its support is the union of the regimes and it locates itself in it; why pooled W1 under-describes it |
| Time projection on 4×4 (L-279): −2.21 % at K1, identity at iid | third failed relabelling of an in-range input; predicted by the refined interface rule BEFORE the result |
| W1 prospective (L-282): ordering holds (W1a), magnitude and shape fail (W1b, W1c); the K2-trained receiver is not rescued at K1 | W1 is a ranking regularity, not a law; the sign flips follow the training-relative STALE COUNT leaving the support (Spearman −0.853 vs W1 −0.825 on the 12 cells, post hoc), i.e. the count coordinate of rule A |
Net: the paper's quantitative laws are the CHANNEL-side ones (floor, net floor, provisioning — proved; rule A — prospective on
two networks); the receiver-side regularity is a support statement (out-of-support stale count), not a distance law.

