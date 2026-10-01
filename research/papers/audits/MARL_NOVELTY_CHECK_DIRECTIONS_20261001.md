# Novelty check of every open MARL direction (01/10/2026, 08:30–08:45 EDT)

User 08:3x: "đã đủ novelty chưa? research kiểm tra chưa? nếu ko novelty thì làm làm gì?? hướng đó đủ hay câu chuyện đủ hay
thì mới bắt tay vào làm chứ?"  Self-criticism: the Lean for directions A, D and H2 (L-192 … L-199 and the FreshnessFrontier
module of 08:30) was written BEFORE a systematic collision search.  This file is that search.  The sources were read
(full text for the four closest; abstracts for the others).  It is not exhaustive: 15 searches, one afternoon-hour.

## Closest prior work found (read)
| Work | What it already has | What it does not have |
|---|---|---|
| Kaul, Yates, Gruteser, "On piggybacking in vehicular networks", GLOBECOM 2011 (winlab.rutgers.edu/~sanjit/Papers/kaul_yates_gruteser_benefits_of_piggybacking.pdf) | Every node is a source and a monitor; system age = mean over N(N−1) pairs; round-robin broadcast; nodes PIGGYBACK other nodes' states; packet length grows with the number piggybacked; the term **"relay age"** d_uv | Prefix decoding with heterogeneous capacity; several senders decoded per slot; an exact freshness–injection frontier; decisions |
| Farazi, Klein, Brown, "Fundamental bounds on the age of information in multi-hop global status update networks", JCN 2019 (aspectlab.github.io/papers/jcn2019.pdf); and the general-interference version (par.nsf.gov/servlets/purl/10112751) | All-to-all multi-source multi-hop AoI; lower bounds via the connected domination number / feasible activation sets; periodic schedules that attain the peak bound exactly | **Each transmission carries ONE status** (their assumption 3); no tables, no capacity heterogeneity |
| Moeller, Krishnamachari, "A theory of information architecture for networked decisions: freshness, locality, and coordination", arXiv 2609.06351 (6 Sep 2026) | Scope-versus-freshness trade-off for a team; architecture = what / from where / at what delay; regret against complete current information; **"performance is governed by the predictability of the optimal decision rather than of the raw state"**; lists as future work heterogeneous radii, long-range shortcuts, low-dimensional global summaries, budget-constrained acquisition | Exogenous state (actions do not affect the environment), static team, quadratic cost, **no charge for communication**, delay GIVEN by a scope–latency relation τ(r) (not produced by a channel schedule), no learning |
| Ding, Huang, Lu, I2C, NeurIPS 2020 (arXiv 2006.06455) | Necessity of communication labelled by the causal effect (KL of the action distribution with and without another agent's information) from a joint Q; a learned prior on whom to talk to | No across-seed prediction of the realised gain |
| Liu, Zhang, "Partially observable MARL with information sharing", arXiv 2308.08705 | Information sharing (incl. delayed sharing) makes POSGs quasi-polynomially solvable; hopes to DESIGN information structures | Sharing is free: no channel, no capacity |
| Mrani-Zentar, Yüksel, arXiv 2408.13828 | One-step delayed and K-step periodic sharing reduce to a centralised MDP | Sharing is free |
| (cited by Moeller–K.) Summers, Li, Kamgarpour, "Information structure design in team decision problems", IFAC 2017; Afshari, Mahajan, CDC 2018 ("sufficiently old measurements constitute common information" over communication graphs with delays) | Information-structure design; delay graph → common information | Not read in full yet — MUST be read before any claim about the cost of an information structure |
| Mostaani et al., arXiv 2005.14220 and 2301.01628 | Task-oriented quantisation of observations over bit-budgeted channels | — |
| Two-hop AoI with a relay's own status vs forwarding (e.g. arXiv 2007.02531) | A relay's slot is shared between forwarding and its own update | — |
| Buyukates, Soysal, Ulukus, multihop multicast AoI (arXiv 1812.10455); Yates "age of gossip" (2021) and Kaswan–Ulukus follow-ups | Single source; gossip version age | — |

## Verdicts
| Direction | Verdict | Reason |
|---|---|---|
| Core freshness theory (H1–H6, H2 frontier) | **Incremental.** Keep as supporting theory; never sell as the contribution | The mechanism (table piggybacking in round-robin broadcast, relay age) is Kaul–Yates–Gruteser 2011; all-to-all AoI bounds are Farazi 2019.  New: the prefix-capacity channel, the exact one-step-freshness/injection frontier, the rich-receiver collapse, Lean.  Must cite KYG 2011 and Farazi 2019 (paper_marl_v2 cites only Yates 2021 and Selen 2013 today) |
| A — predicting the value of communication | **Not a direction.** One analysis paragraph at most | Theory = EVPI / Blackwell (the easy direction); the per-step label = I2C's necessity label |
| B — byte budget sender × resolution | **Stop** | Mostaani et al.; dynamic VQ bottlenecks |
| C — decision-weighted quota | Stopped earlier | Tijdeman 1980 |
| D — decision depth | **One section at most** | Azar–Gamzu–Yin 2009, Feige–Lovász–Tetali 2004, PET, Jackson; "decision not state" is now also Moeller–Krishnamachari 2026 |
| E — learning whom to listen to | **Stop** | I2C, HiComm (arXiv 2606.29126), collaborative bandits |
| New candidate — the channel price of an information structure | **Collided (08:50)** | Liu, You, Zhang, "Principled learning-to-communicate with quasi-classical information structures", arXiv 2603.03664 (Mar 2026): LTC in Dec-POMDPs with a communication cost κ_h = α·|z_h| on additional sharing over a one-step-delayed-sharing baseline; Matni, "Communication delay co-design in H2-distributed control", IEEE TCNS 2015: delay patterns co-designed with the controller at a cost; Summers–Li–Kamgarpour 2017 (arXiv 1706.05572): greedy design of information links (no channel); Afshari–Mahajan (arXiv 1903.12018): delayed sharing over a GIVEN graph. Left over: only the prefix-capacity channel and its exact combinatorial frontier (incremental) |

## What is left of the story (my assessment)
The only parts without a found precedent are (i) the closed-loop, learned, byte-charged setting in which the scope–age
relation is CHOSEN by the broadcast order and relay (exactly the boundary Moeller–Krishnamachari name as theirs), and
(ii) the empirical claim that relay beats compiled silence (a distilled zero-byte student), which rests on the reserved
ten-seed panel running now (PROTOCOL_E3_TEN_SEEDS_20260930.md).  If that panel fails, the core story fails with it.

## Addendum 08:50 — conclusion
No direction examined passes as a standalone novel contribution.  The defensible paper is the closed-loop empirical
result (relay vs compiled silence, pre-registered reserved panel) with the prefix-channel theory as SUPPORT, positioned
against Kaul–Yates–Gruteser 2011, Farazi et al. 2019, Moeller–Krishnamachari 2026, Liu–You–Zhang 2026, Matni 2015, I2C.
The decision whether that story is worth finishing is the user's.

## Rounds 2–3 (08:50–09:05; user chose "brainstorm new directions, novelty first", no building)
| Candidate | Closest prior work (read) | Verdict |
|---|---|---|
| C1 — reliance on communication is a property of the learned convention; choose / train teachers that need fewer messages | Li, Xie, Lu, GPO, arXiv 2505.15418 (guider kept inside the learner's imitable region); Messikommer et al., Student-Informed Teacher Training, arXiv 2412.09149; Weihs et al., ADVISOR, arXiv 2007.12173 (imitation gap); Chauhan–Bera cross-play idiosyncrasy | Collided (the controllable part); the across-seed predictability (L-201) is a small empirical addition |
| C2 — the environment as an implicit channel; explicit value = what the plant does not carry in time | Chen, Gündüz, "The control plant as a communication channel", arXiv 2605.01903 (May 2026); Chauhan, Bera, arXiv 2609.34373 (28 Sep 2026): "communication value is governed by coupling", closing a physical side channel creates the discriminating regime; Grupen et al. 2021 implicit signalling | Collided |
| C8 — compiled silence (distilled zero-byte student) as the missing baseline | Wojtala et al., "Communication-enhanced tutoring", arXiv 2508.13661 (share latents in training, distil into local-only counterparts); Chauhan–Bera (silence beats every channel under rigid coupling, matched rate, 25 seeds) | Collided |
| R1 — Matryoshka / nested messages decodable at any prefix for heterogeneous capacities | "Attention-based hierarchical VIB for robust multi-agent communication under variable bandwidth" (AH-VIB), arXiv 2609.34860 (Sep 2026): prefix truncation of message dimensions, nested dropout / MRL | Collided |
| R6 — a headroom law for protocol discovery (learning signal ∝ zero-byte Bayes risk) | Chauhan–Bera §4.3: discovery failure = joint exploration (Eccles et al. 2019); their data contradict R6 (the only regime with headroom is the one where learning fails) | Rejected on evidence |

Meta-finding: MARL communication (value, limits, bandwidth, prefix truncation, implicit channels, distillation,
information structures) received at least four directly relevant papers in Sep 2026 alone.  Brainstorming inside this
niche has low expected yield.  The one coherent positioning left for paper_marl_v2: it sits on every item of
Moeller–Krishnamachari's own open list (endogenous closed-loop state, communication charged in bytes, heterogeneous
radii = capacities, long-range shortcuts = relay, low-dimensional summaries = byte packets), with an exact channel
frontier and a pre-registered reserved-panel result (L-201) — an empirical/systems contribution, not new theory.
