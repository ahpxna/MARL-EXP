# Lights and cars that both learn: novelty research for a two-population system (02/10/2026, started 17:51 EDT)

User 17:5x: "NYC xếp hàng sau D, tập trung dồn toàn lực để research novelty riêng cho hệ đèn và xe học đi, dựa trên tất cả
những gì đã có so far, những gì có ở các paper cũ, functional, d6, master, support, … paper A, B, C, marl v1, marl v2 và nhất
là hướng hiện tại!"  Earlier (17:1x): lights and cars both as agents, trained together or separately, then dropped into a real
map to play.  No subagents (the message does not say "fetch").  Read for this note: MARL_OLD_PAPERS_REREAD_20260929 (full),
MARL_LESSONS_AND_STORY_20261002 (full), MARL_DIRECTION_ROUND10_20261002 (full), the abstracts of paper_a/b/c, unified,
paper_marl (v1) and paper_marl_v2, the poster text of FUNCTIONAL / D6 / MASTER / SUPPORT, the Lean module list
(work/p13_conjectures).  NYC 16×3 (signals only, the E3 third network) is queued after test D; nothing is launched by this note.

## 1. What each piece of our corpus says about a city where both sides learn
The organising fact: in a two-population system, EACH POPULATION'S POLICY IS THE OTHER'S INPUT CHANNEL.  A car's view of the
light (phase, time in phase, residual green, queue ahead) is produced by the light's policy; a light's view of the traffic
(arrivals, queues, turning ratios, connected-vehicle reports) is produced by the cars' policies.  When one side learns or is
upgraded, the other side's input distribution moves.  Our corpus is, almost entirely, about learned or designed decisions under
a moved or restricted input.

| Source | Result we own | What it becomes for lights + cars |
|---|---|---|
| Current direction (support, not freshness; L-249 … L-285) | a learned receiver is harmed when the deployment view leaves its TRAINING SUPPORT, not by distance or freshness; W1 predicts but is not a lever; the out-of-support statistic is network-specific; interface relabelling fails; matched or mixture training repairs | a car trained against one kind of light (or a light trained with one kind of traffic) is a learned receiver of the other population's behaviour; a partner UPGRADE is a channel change |
| Emulation asymmetry (LeanMarlEmulationV1: upgrade_emulation, downgrade_strict) | a richer channel can emulate any poorer one; below the floor nothing can | a smarter light can run a COMPATIBLE MODE that keeps its interface inside the cars' training support; the reverse (a poorer partner) cannot be repaired from the partner's side |
| Upgrade hazard (LeanMarlSupportV1: upgrade_hazard; P-UP2 on five panels; RI age role) | fresher / richer input can hurt a receiver that uses age as a PROPAGATION horizon | time-in-phase is an age: a car that extrapolates "green ends at about the trained phase length" is hurt when an adaptive light extends or cuts phases |
| Mixture (LeanMarlMixtureV1: mixture_minimax; E4, SW1/SW2) | training on a mixture of channels is minimax, specialist premium ≈ 1 point, tracks switching | train cars against a population of light policies (fixed, actuated, learned versions) and lights against a population of fleets |
| MARL v2 (compiled silence bar) | runtime communication must beat a zero-byte student distilled from the same full-information teacher | V2I (SPaT to cars, CV reports to lights) must beat a car / light distilled from a teacher that saw the message; most V2X MARL baselines are co-trained silent agents, which is the weaker bar (X2 in the old-papers reread) |
| MARL v1 (committed priorities, bounded revision, paid bids) | the price of committing to one order before budgets are known; R post-reveal revisions reduce it | a light that ANNOUNCES its next plan (commitment, predictable for cars) and may revise it R times |
| Paper C / STRUCTURAL (one order for every budget; one exchange after the reveal recovers the whole gain; menus) | exact frontiers; one exchange suffices on the families | announce a plan, allow ONE revision per cycle: a candidate rule with a proved analogue on C's families |
| MASTER (calibration query: value EXACTLY zero without it when the decision is not invariant to the nuisance; exact price) | necessity dichotomy, price law Δ²/(2K(√(vm)+√(νκ))²) | the light's intent/SPaT message is the cars' calibration query: needed exactly when the light's policy is not inferable from the car's own view (adaptive / learned lights), worthless under fixed-time lights |
| Paper B / UNIFIED (obstruction: worlds with no common safe answer; randomised floor 1/|H|) | deciding needs the obstruction order, not identification | a car does not need to identify the light's policy; it needs one action safe for every light policy in the deployed set — if those policies form an obstruction, no silent car is safe and a message (or a compatible mode) is necessary |
| Paper A (frozen surrogate starves the decision cells; repair by sacrificing surrogate value at an exact rate) | training on a frozen surrogate gives zero information on the alternatives that matter | training cars against a FROZEN light (separate training) starves exactly the light behaviours an upgrade will produce; the repair is to sacrifice in-distribution fit (mix partner behaviours) |
| FUNCTIONAL (a proxy at the current extrema fails when they move; certificate lifetime) | proxies valid now fail when the relevant quantity moves | the current SPaT residual is a proxy that an adaptive light invalidates; certificate lifetime = how long an announced plan stays valid |
| SUPPORT paper (deciding without identifying; decide cost flat in K) | naming one safe answer is cheaper than recovering the world, independently of the number of classes | a car choosing a route needs one uncongested option, not the network state: the V2I payload a car needs does not grow with the network |
| QUERY (the admissible measurement sets the order) | which summary is legal sets the difficulty | WHICH message the light sends (phase, residual, intent, queue) matters more than how many bytes |
| D6 (fitted weights are evidence, not derivation; sharp margin 2δ) | a threshold proved sharp | any compatibility threshold we report must be derived, not fitted |
| ADAPTIVE (quota apportionment) | the largest-deficit rule violates quota; a quota method does not | per-approach refresh of CV reports with a provable staleness bound |
| E3 floor / provisioning (rule A, prospective on two networks) | the network predicts where support breaks for every scheduler | CV penetration and V2I capacity predict where a learned light's support breaks |

## 2. The neighbourhood (searched 17:3x–17:5x, standard and extended web search; abstracts unless noted)
| Neighbour | What it already establishes | What it leaves open |
|---|---|---|
| CoTV, Guo–Cheng–Wang, IEEE Access 2023 (arXiv 2201.13143) | joint DRL control of lights and the nearest CAV per approach; SUMO grids and Dublin; up to 30 % travel-time reduction | trained and tested together; no partner change, no compatibility, no message-value bar |
| Joint signal control + vehicle routing MADRL (arXiv 2310.10856) | signal agents + routing agents, MA2C, shared observations / rewards; joint beats either alone (modified Sioux Falls) | joint training only; no separately trained pairings, no upgrade, no support |
| Bazzan and co-workers (co-adaptation of drivers and lights; "To adapt or not to adapt", TU Berlin; Bazzan & Klügl) | simultaneous learning of lights and route choice is coupled, non-stationary, loses convergence guarantees; can interfere | descriptive simulation of co-learning; no deploy-time pairing of independently trained populations, no prediction of failure |
| Smith 1979–1995 (responsive control policy P0 vs drivers re-routing) | a locally responsive signal policy combined with re-routing can REDUCE network capacity; P0 is the policy compatible with equilibrium routing | analytic, non-learned; the learned version (failure through the receiver's training support) is not addressed |
| Mixed autonomy (Vinitsky et al., arXiv 2011.00120, TCPS 2023; Berkeley theses) | AV controllers face penetration-rate shift; RL can find a strategy robust across rates; feedback controllers degrade | AVs only, no learned lights; penetration changes the dynamics, not a partner's policy |
| CV-data signal control (CVLight; partial detection, arXiv 2109.14337) | learned lights work from CV data alone above roughly 20 % penetration; thresholds of acceptable / optimal performance | trained and tested per rate; no theory of when, no compiled-silent (detector-only, distilled) bar |
| SPaT uncertainty for actuated / adaptive lights (eco-driving under uncertain SPaT, arXiv 2208.13709; SPaT prediction ensembles) | adaptive lights make SPaT uncertain; eco-driving designed for fixed-time timing degrades; remedy = predict SPaT with confidence | model-based cars; the learned-car version, the cause (support), and the light-side repair (compatible mode) are not addressed |
| Delayed route information (arXiv 2105.11790) | delayed travel-time information destabilises traffic (Hopf bifurcation); obscuring information prevents delay-induced congestion | non-learned drivers; supports "less information can be better" |
| Human–AI update compatibility (Bansal et al., AAAI 2019; arXiv 1906.01148); backward-compatible representations (Shen et al., CVPR 2020) | a more accurate model update can lower TEAM performance; penalise new errors to make updates compatible; performance/compatibility tradeoff | one model and a human mental model, offline decisions; not closed-loop multi-agent, not predicted from the partner's interface |
| Cross-play / zero-shot coordination (Hu et al. 2020; Carroll et al. 2019) | independently trained partners fail when paired (arbitrary conventions); cross-play matrices | symmetric games, seed conventions; not infrastructure-vs-fleet upgrades, no channel-side prediction |
| Privileged information "safe if reconstructible at test time" (robotics distillation, arXiv 2602.04942 and the LUPI line) | a teacher's privileged input is harmless if the student can reconstruct it from its own view | informal; our MASTER/B dichotomy is the exact version; not applied to V2I |
| Simplex / runtime assurance (Neural Simplex, arXiv 1908.00528); box monitors (Henzinger et al., ECAI 2020) | a monitored learned controller with a fallback; support monitors on activations | not for partner shift, not with a compiled-silent fallback |

## 3. Candidate directions and verdicts
| # | Direction | Verdict | Reason |
|---|---|---|---|
| N1 | COMPATIBLE UPGRADES: an upgrade of one learned population (smarter lights, or a fleet with learned routing / eco-approach) degrades the other population's learned policy; the degradation is predicted BEFORE deployment by the support of the interface the upgraded partner produces; a compatible mode (emulation) and partner-mixture training repair it; the asymmetry holds | NOT FOUND as a whole; strongest | ingredients exist (Bansal's compatibility, cross-play, Smith, co-adaptation, SPaT uncertainty) but not the closed-loop, two-population, infrastructure-vs-fleet version with a channel-side prediction and a repair theorem; the search for "smarter lights make learned cars worse" found the opposite framing (upgrades improve) |
| N2 | WHEN MUST LIGHTS TALK TO CARS: V2I value is zero against a compiled-silent car when the light's policy is inferable from the car's own view, positive otherwise (MASTER dichotomy, B obstruction) | PARTIAL; fold into N1 | the bare statement is decision-theoretic folklore (value of information is zero iff the decision is invariant) — the V-U tautology lesson applies; the content is the measured prediction "fixed-time → SPaT worthless vs compiled silence; learned lights → SPaT necessary" and SPaT as compatibility insurance |
| N3 | ANNOUNCE THEN REVISE ONCE: a learned light commits to a plan the cars can use and revises it at most once per cycle (C's one-exchange, MARL v1's bounded revision) | PARTIAL; fold into N1 as the compatible mode | SPaT-commitment for CAV trajectory planning is studied in optimisation; our addition is the learned-agent frontier and the one-revision sufficiency, which needs its own proof outside C's families |
| N4 | PENETRATION IS COVERAGE: CV penetration as channel coverage for learned lights; floor gives a minimum penetration; emulation (subsample reports) repairs upgrades | COLLIDED on the headline | mixed-autonomy penetration shift and robust controllers (Vinitsky), CVLight / partial-detection thresholds; keep only as one axis of N1 (a penetration increase is a partner upgrade) |
| N5 | THE CHANNEL IS THE TRAFFIC: cars carry information between lights (store-carry-forward), so congestion makes information stale exactly when it is needed ("information gridlock") | OPEN but heavy | data mules and delayed route information exist (2105.11790) but not learned lights fed by vehicle-carried relays; good second paper / demo, needs a new channel implementation |

## 4. Recommended direction (N1, absorbing N2–N4): "A better partner is a different partner"
Thesis.  In a city where both lights and cars learn, each population's policy is the other's information channel.  Whether a
learned agent keeps working after the other side changes is decided by whether the new partner keeps the interface inside the
agent's TRAINING SUPPORT — not by how much better the partner is in isolation.  The current paper's "support, not freshness"
becomes "support, not improvement", in a setting where the shift is caused by someone else's progress.

Hypotheses (to be frozen in a protocol before any run):
* H1 cross-population upgrade hazard.  Cars trained against the deployed lights (fixed-time / actuated) lose when the lights
  are upgraded to a learned controller that is better in isolation; lights trained with static-routed traffic lose when the
  fleet is upgraded to learned routing.  System-level: there are pairings where the city is worse after the upgrade than before
  ("better component, worse city"), measured against the compiled-silent bar, not only against the old pairing.
* H2 support predicts compatibility; distance does not decide it.  From LOGS of the new partner alone (no joint run), the
  out-of-support mass of the interface statistic (cars: phase × time-in-phase × queue-ahead at decision points; lights: arrival
  and turning patterns per approach, CV-report coverage) predicts the sign of the change; W1 of the same statistic predicts
  less well (extends L-277 / L-282 to partner shift).
* H3 compatible mode (emulation asymmetry).  An upgraded light constrained to keep its interface in the cars' training
  support (phase order kept, phase durations clipped to the old range, or announce-and-revise-once) recovers the cars at a
  bounded cost to its own gain; an upgrade can always be made compatible, a partner that is poorer than training cannot be
  compensated from the partner side.  The measured object is a compatibility frontier (own gain vs partner harm), Bansal's
  trade-off in closed loop.
* H4 the message is compatibility insurance.  A car receiving the light's intent (next phase, residual green) is robust to the
  light's upgrade where a compiled-silent car is not; under fixed-time lights the message adds nothing over compiled silence.
* H5 partner-population training is minimax.  Cars trained against a mixture of light policies (and lights against a mixture
  of fleets) are minimax across upgrades with a small specialist premium (E4's ≈ 1 point as the reference).
* H6 interface relabelling fails (control).  Remapping the new partner's interface statistic onto the old distribution (for
  example rescaling time-in-phase) hurts, as the three relabellings did in E3 (L-266, L-274, L-279).

Theory, honestly scoped:
* Transfers by analogy, not by theorem: LeanMarlEmulationV1 and LeanMarlSupportV1 are about a prefix channel and a fixed
  receiver; for a partner-induced channel the analogous statements must be proved again.  New Lean targets, each small:
  (i) risk invariance when the new partner's interface law agrees with the old on the receiver's support (risk_eq_of_agree_on_support
  instantiated with a policy-induced law); (ii) a two-route, one-light WITNESS of "better component, worse system" with a
  learned (support-limited) route chooser — the learned analogue of Smith's example; (iii) compatible-mode existence (the
  upgraded class contains a policy whose interface law equals the old one) plus a strict-loss witness for the reverse
  direction; (iv) the MASTER dichotomy instantiated for intent messages (decision not invariant to the light's policy ⇒ a
  silent car's value is exactly zero on the witness).
* The one-revision rule (N3) is a conjecture until proved outside C's families.

Why it is novel and practical:
* The deployment reality is staggered: cities replace signal controllers on their own schedule; carmakers ship learned
  driving / routing updates on theirs.  Each update is evaluated against the other side as it is today.  N1 says that is the
  wrong evaluation and gives (a) a pre-deployment check from logs, (b) a cheap repair on the upgrading side, (c) the training
  recipe, (d) when V2I messages are worth deploying.
* It speaks to three communities with one mechanism: traffic control (Smith's compatibility, co-adaptation), ML deployment
  (update compatibility, CACE, underspecification) and MARL (cross-play, zero-shot coordination).
* It reuses our assets: the support diagnostics, the compiled-silence bar, the mixture and switching results, the emulation /
  floor logic, the relabel controls, and the monitor-with-fallback idea (a car falling back to a compiled-silent policy when the
  light's interface leaves its support).

What would kill it:
* K1: learned cars trained against fixed-time lights are NOT hurt by a learned-light upgrade (no H1) — then the paper is a
  robustness negative, still reportable but not the thesis.
* K2: the out-of-support score does not predict the sign better than chance or than W1 (H2 fails).
* K3: the compatible mode costs the light its whole gain (the frontier is degenerate).
* K4: the effect exists only through gridlock artefacts of the OSM import (teleports) — controlled by a clean synthetic grid
  first and by reporting teleports.

## 5. Experiments, cheapest decisive first
| Step | What | Cost | Decides |
|---|---|---|---|
| C0 | stylised testbed (Python, minutes): one approach, a car choosing arrival speed from (phase, time in phase) trained against fixed cycles; lights fixed vs adaptive (phase lengths outside the trained range) vs compatible mode; plus a two-route one-light route-choice witness | CPU-light | H1, H3, H6 in the cleanest form; whether time-in-phase behaves as a propagation age (the RI age-role result predicts yes) |
| C1 | SUMO synthetic grid (clean, no OSM artefacts): learned cars (route choice at junctions, optionally eco-approach speed) trained against fixed-time lights; learned lights trained with default routing; all 2×2 pairings plus joint training; compiled-silent cars and lights; compatible-mode lights | hours, after test D or at low priority | H1, H2 (prospective from logs), H3, H4, H5 |
| C2 | SUMO Midtown (real map, demand ≤ 6 000 veh/h) and the live viewer: the same pairings dropped into the real map ("tự chơi"); the viewer shows the out-of-support lamp per light and per car class | after C1 | external validity; the demo of problem → solution |
| C3 | NYC 16×3 in CityFlow (queued after D): the E3 signal-side claims on a real network (relay vs compiled silence, K = 1 reversal, rule A, support culprits, monitor + fallback) | after D | the current paper's third network |

The live viewer (scripts/CITY_live_viewer.py) already renders the Midtown map, signal heads and vehicles; for C2 it needs
per-agent overlays (support lamp, message arcs) and a side-by-side mode.

## Sources
CoTV https://arxiv.org/abs/2201.13143v2 · joint TSC + routing https://arxiv.org/abs/2310.10856 · Bazzan co-adaptation
https://depositonce.tu-berlin.de/items/0f68cbf3-7cf8-4c1d-aca8-44a7e26f3365 · Smith P0
https://pure.york.ac.uk/portal/en/publications/traffic-control-and-route-choice-capacity-maximization-and-stabil/ ·
mixed autonomy https://arxiv.org/pdf/2011.00120 · partial detection https://arxiv.org/pdf/2109.14337 · SPaT uncertainty
https://arxiv.org/pdf/2208.13709 · delayed route information https://arxiv.org/pdf/2105.11790 · Bansal et al.
https://arxiv.org/pdf/1906.01148 · Neural Simplex https://arxiv.org/pdf/1908.00528 · box monitors
https://arxiv.org/pdf/1911.09032 · cross-play / ZSC https://arxiv.org/pdf/2302.05063 · privileged information
https://arxiv.org/html/2602.04942v1

## 6. External collision audit (user-pasted 18:1x) — verified 18:2x, and the claim narrowed
Each paper the audit cited was checked through Crossref / OpenAlex / Semantic Scholar (publisher pages return 403 to every
fetch, including the in-app browser).  "Abstract read" means the abstract text was retrieved.
| Audit claim | Paper found | Status |
|---|---|---|
| 2025 Stackelberg MARL signal + CAV | Zhang, He, Zhu, Huang, Physica A (2025), 10.1016/j.physa.2024.130289 | VERIFIED (metadata; leader-follower SGMRL from search snippets) |
| 2026 TRC cooperative signal-vehicle RL | Han et al., TRC 186 (2026) 105590, 10.1016/j.trc.2026.105590 | VERIFIED (metadata; eco-driving + signal agents from the search abstract); "integrated SPaT to vehicles" NOT checked |
| 2026 arterial MARL signal + CAV | Zhang G. et al., Accident Analysis & Prevention (2026), 10.1016/j.aap.2026.108483 | VERIFIED, abstract read (MARL TSC + CAV speed advisories, Changsha arterial, robust as penetration grows) |
| 2026 hierarchical PPO signal + trajectory | Wu et al., IET ITS (2026), 10.1049/itr2.70147 | VERIFIED, abstract read (SVCC-HPPO, joint) |
| Liu et al. 2026 truck eco-driving across adaptive patterns incl. extension / skipping | the linked paper is Fan, Lu, Liu, J. Transp. Eng. A (2026), 10.1061/JTEPBS.TEENG-9621 | MISDESCRIBED: abstract read — joint MADQN CAV trajectories + queue-pressure adaptive phases; no truck, no extension / skipping robustness |
| Li–Wu–He 2026 Energy: DRL eco-driving loses reliability under unseen signal timings; refine with evaluation trajectories | Li, Wu, He, Energy (2026), 10.1016/j.energy.2026.141837, "Closed-loop offline policy improvement for eco-driving at signalized intersections via evaluation-trajectory recycling" | PARTLY VERIFIED: title / authors / date consistent with the audit; abstract not retrievable here |
| ETSC-HD (ID / OOD SPaT, domain randomisation) | not found in four searches | UNVERIFIED |
| Jayawardana multi-task eco-driving | IntersectionZoo, ICLR 2025 (arXiv 2410.15221); also 2204.12561, 2408.05609 | VERIFIED |
| UPD (ICML 2026) | Ruhdorfer et al., "Unsupervised Partner Design Enables Robust Ad-hoc Teamwork" | VERIFIED |
| Bazzan 2007; Smith; Bansal; de Haan (causal confusion, NeurIPS 2019) | Bazzan "To adapt or not to adapt"; Smith P0; Bansal AAAI 2019 | VERIFIED (de Haan from prior knowledge, not re-fetched) |
Verdict: the audit is right on every point that matters, even with the one misdescription and the two unverified items.  "Lights
and cars both learn", "joint beats separate", "a policy trained on one signal timing fails on unseen timings", "mixture /
randomisation helps", "SPaT helps under adaptive lights", "a better component can hurt the team" and "in-support values with a
new meaning" (concept shift) are all taken.  None of the six abstracts read or retrieved addresses independently updated
partners, backward compatibility, a partner-side prediction, or a compiled-silent communication bar.

Research beyond the audit (18:2x):
* SAE J2735 SPaT already carries an intent contract — minEndTime, maxEndTime, likelyTime, confidence — but deployments of
  adaptive controllers fill minEndTime = now and maxEndTime = now + 3600 s (Drive Sweden J2735 interpretation; patent
  literature): the bounds exist and carry nothing.  "How much intent must be exposed" becomes concrete and standard-compatible:
  how tight an HONEST [minEnd, maxEnd] window a learned light can commit to, and at what cost to its own gain (MARL v1's price of
  commitment; C's one exchange after the reveal).
* Under RL signal control the next cycle's SPaT is not determined in advance; one line predicts it by executing the trained
  policy on current states (found in the SPaT-prediction search) — prediction, not commitment.
* The certificate must be partner-only for a practical reason: the city does not hold the carmaker's policy and vice versa, so
  "just simulate the cross-pairing" is not available; the predictor may use only the new partner's logs and the logs of the
  partner the legacy agent was trained with.
* Neighbours to cite and distinguish: agreement-on-the-line (Baek et al. NeurIPS 2022: predicts a frozen model's OOD accuracy
  from unlabeled data — receiver-side, open-loop); LIPO (Charakorn et al. ICLR 2023) uses "policy compatibility" for cross-play
  return — a terminology collision; Jayawardana et al. (2408.05609) note that signal timing must be re-tuned as eco-driving is
  adopted — the fleet-to-light direction has a hint in the literature.

Narrowed claim (replaces §4's thesis sentence): "A partner upgrade can break an already-deployed learned receiver by changing the
SUPPORT or the SEMANTICS (the conditional law) of the interface; whether it does can be predicted from the upgraded partner's
own logs before cross-play; an upgrade can be constrained to stay compatible at a measured cost to its own gain; and runtime
intent communication is valued against a same-teacher compiled-silent receiver."  The paper needs the four pieces together:
(1) a cross-version matrix in which the upgrade is better on its own objective yet breaks the frozen partner; (2) the
partner-only certificate (support exit + hazard shift, C0b) validated prospectively; (3) the compatible-upgrade frontier
max G_L s.t. H_C ≤ ε; (4) the communication bar.  C0 is a mechanism / witness test only; C1 (SUMO) must show (1) and (3) with a
light that is genuinely better in isolation.  Lean: LeanCityConditionalShiftV1 (compiled 18:2x, 0 errors, standard axioms) is
the formal witness of the semantics half — standard concept shift, not a contribution by itself.

## 7. Two external reviews (user-pasted 22:4x and 22:5x): "decision-sufficient backward compatibility" — verified 22:5x
Every corpus statement in the two reviews was checked against our files; every external citation through web search.
**Corpus claims — all correct.** Paper A `sacrifice_cost_law` (N·sacrifice(w̄) ≥ 8rM·D, ROADMAP A-SAC); SUPPORT's three-world
witness (pairwise safe sets intersect, the triple is empty; SUPPORT main.tex §"obstruction that pairwise reasoning cannot
see"); MASTER's dichotomy is a witness (`hidden_shift_witness`); QUERY's leakage order depends on the query family; Functional's
separability step is unproved (main.tex l. 1446); Q7 numbers (21.96 / 24.59 / 55.85; Δ_car 30.16 [22.11, 38.93]; keep 0.907;
Δ_compat 6.37); Q7-3 4.4 % vs 18.6 %; SP1–SP3 and RM1–RM5 all NOT SUPPORTED; GTM5 −17.76; C0 S_exit 0.913 > K 0.783, φK 0.713 < K
0.735; CUT 0.234 with CI over 0; Q5 at the undersaturated demand: no window, REVISE1 fails.
**External citations — all exist and are described correctly:** SIL-C, "Policy Compatible Skill Incremental Learning via Lazy
Learning Interface" (NeurIPS 2025; backward skill compatibility: frozen downstream policies keep using updated skills, mapping by
trajectory-distribution similarity) — the CLOSEST neighbour for "backward compatibility of a frozen learned policy", to be cited;
Kazemi et al., Assume-Guarantee RL (AAAI 2024, 38(19) 21223–21231; contracts as regular languages, composed satisfaction bounds);
Dewes & Dimitrova, quantitative assume-guarantee contracts for MAS (AAAI 2025, doi 10.1609/aaai.v39i22.34480); Adalat,
Hamel-De le Court & Belardinelli, contract-based compositional shielding for safe MARL (arXiv 2606.14130, June 2026; the pasted
link pointed to an unrelated domain); Yu et al., ICAPS (ZSC score linear in training/test partner similarity, Pearson 0.874–0.905);
Träuble et al., backward-compatible prediction updates (NeurIPS 2021, negative flips).  Added collision for "interaction order":
combinatorial t-way interaction testing (Kuhn & Wallace, NIST: software failures triggered by t-way parameter interactions;
covering arrays) and Helly-type intersection numbers.
**What the reviews add (accepted):** (i) the framing — compatibility is DIRECTED (U ⇝ R), receiver-relative and
decision-relative, not a scalar property of the upgraded component nor a universal distance; our negative results (Q7-3, C0b-2,
C0c-2, W1 law L-282, receiver-specific clip L-285) become evidence for it rather than failures; (ii) three theorem targets:
(T1) no receiver-free certificate — ALREADY in our Lean: LeanMarlSupportV1.upgrade_hazard has two training-optimal receivers f, g
(risk 0 on Ptrain) with deployment risks 0 and 1 under the same Qdeploy (silent 1/2), so any K(Ptrain, Qdeploy) answers both
the same; only a one-line corollary is missing; (T2) obstruction / common-safe-action characterisation per contract cell — this
is SUPPORT / Paper B's decide-without-identifying applied to the cells of a receiver contract (re-instantiation, not new math);
(T3) local-to-joint hierarchy s_compat (an order-s contract may be needed; Q4 is a witness with s = 2) — the genuinely new
object, provable by a parity construction, to be positioned against t-way testing and k-wise independence; (iii) the two dual
repairs — receiver-side (C0 fallback, #3 support fallback) and producer-side (Q7 compatible mode: a constraint in POLICY space,
whereas E3's input projections failed); (iv) the price-of-compatibility frontier (Q7 gives one point: 90.7 % of the light's gain
kept, car harm −79 %), with Bansal 2019's performance/compatibility tradeoff as prior art and Paper A as the rate template.
**Corrections to the reviews:** (a) Q7 trained ONE network per component (DQN seeds fixed at 11 / 13 in
scripts/CITY_q7_cross_version.py); its intervals cover evaluation traffic only, so Q7 is not yet central evidence — it needs a
training-seed replication; (b) Q7-3's light statistic (share of green-seconds beyond 50 s) is not the receiver's exposure: cars
decide every second while queued, so long phases are over-weighted at decision points (4.4 % of phase time vs 18.6 % of
decisions) — the gap is itself receiver-relative (supports the framing) and is measurable from the upgrader's logs only if the
receiver publishes its decision process / accepted region (a contract); (c) "input projection usually fails" holds on E3 but not
in C0, where quantile relabelling HELPED (C0-5: 11.4 vs 29.3) — input-side repair is receiver/testbed-specific, not refuted in
general; (d) the asymmetry "car → light only +13 %" compares a different fleet (L-RLH) and is one pair — not yet a directed-
compatibility result; (e) Layer B's sufficiency condition is SUPPORT's own; the novelty is the receiver-contract scope and s_compat;
(f) Q5's two saturated demands are void, as recorded (C-6).
**Verdict:** adopt the framing for the CITY paper ("receiver-relative, decision-sufficient, possibly higher-order compatibility
contracts between independently updated learned agents"), keep the MARL E3 paper's thesis "support, not freshness" (its support
region is exactly a receiver contract).  Next, cheapest decisive first: Q7b (training-seed replication of Q7; the compatible-mode
frontier over the forced-switch cap; the contract certificate = the receiver's published τ region weighted by its decision
exposure, computed from the upgrader's own logs, registered before computing); Lean T1 corollary; Lean T3 parity witness.

**Correction to §7 (b) (23:1x):** the exposure explanation of Q7-3 is a hypothesis that the Q7b smoke does not support
(RL-H contract-with-exposure 0.036 from human-traffic logs vs 0.131 with the fleet present vs 0.19 cross-play): most of the gap
is closed-loop — the upgraded light behaves differently when the frozen fleet drives (FAILURE_SYNTHESIS correction, H2b).  This
strengthens "receiver-relative" further: the contract must include the receiver's behaviour, not only its region.
