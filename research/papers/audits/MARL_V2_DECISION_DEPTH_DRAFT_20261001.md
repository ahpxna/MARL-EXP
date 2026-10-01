# Draft: "Decision depth under prefix decoding" for paper_marl_v2 (01/10/2026, 01:0x EDT)

STATUS: draft text, NOT in the manuscript.  Rule: nothing enters `paper_marl_v2.tex` as a claim before its Lean module
compiles AND passes the frozen gate.  Modules (work/p13_conjectures): `LeanMarlDecisionDepthV1` (compiled clean 00:53),
`LeanMarlPrefixEDFV1` (compiled clean 01:03), `LeanMarlObstructionMassV1`, `LeanMarlRelayDecisionV1`,
`LeanMarlAdaptiveDepthV1` (compiling).  Ledger L-192.

## Why this section (the selling point)
The paper's channel theory so far is about FRESHNESS (injection, one-hop relay ages, memory).  It says how old a
receiver's copies are, not how much of the broadcast a receiver NEEDS in order to act.  The corpus' obstruction law
(paper B; UNIFIED) answers exactly that question once it is read on the prefix channel, and it gives the paper a second,
decision-side axis that a "relay + distillation" reading does not contain:
- how many decoded senders a receiver needs = a hitting set of the obstructions hidden in its own observation;
- on a prefix broadcast, the least sufficient capacity is paper B's safe order with a separation order read off the
  stream positions (proved equal, not analogous);
- one committed order cannot serve receivers of different capacities in general (price of nesting), and with forced
  senders the exact condition is an earliest-deadline counting condition;
- one relayed packet replaces the whole nested condition by one inclusion at the head;
- acting needs far fewer senders than identifying (1 versus m−1 on an explicit geometry);
- compiled silence has a quantitative floor: the obstruction mass of its observation.

## Proposed text (claims carry Lean names; to be switched from \LEANC to \PROVED after the gate)

**Definition (acceptable sets, obstructions).**  For receiver i, let safe(F) be the actions acceptable in world F
(e.g. within ε of the team optimum).  A set H of worlds is an obstruction when no action is acceptable in all of H; it is
local when i's own observation does not separate its worlds.

**Claim D1 (hitting law).**  A policy on the view of a decoded set D is acceptable in every world iff every local
obstruction is split by a sender of D.  `LeanMarlDecisionDepthV1.decode_safe_iff` (from
`LeanUnifiedObstructionOrderV1.classes_resolve_iff`).

**Claim D2 (decision depth = paper B's safe order).**  On a broadcast with positions pos, let sepPos(F,G) = 0 if i's
observation separates F,G, else 1 + the earliest position of a sender whose records differ (T if none).  Capacity K < T
suffices iff SafeAt sepPos safe K; the least such K is s* = max over obstructions of min over pairs of sepPos.
`prefix_safe_iff_safeAt` (with `LeanPaperBSafeOrderV1.safeAt_iff`).

**Claim D3 (anytime decoding).**  sepPos is ultrametric; a receiver that decodes in stream order and stops as soon as
its view admits an action acceptable throughout stops at paper B's per-world decision order, whose maximum is s*.
`LeanMarlAdaptiveDepthV1.sepPos_ultrametric, near_iff_view, worst_anytime_depth_iff` (from
`LeanPaperBDecisionOrderV1.max_order_iff`).

**Claim D4 (price of nesting; EDF).**  Two receivers of capacities 1 and 2 can each be served by a decode set of their
own size while no nested pair serves both (`nesting_price`).  When every requirement is a forced sender, one order
serves every receiver iff for every k at most k senders are forced by receivers of capacity ≤ k, and the order by
earliest deadline attains it (`LeanMarlPrefixEDFV1.serves_iff_counting`; Jackson's rule read on the broadcast).  For
general requirements the decision is a hitting-set problem (`hitting_embeds_decode`; NP-hard, Karp 1972, cited).

**Claim D5 (relay).**  If every receiver decodes the head and the head forwards the records R it decoded one hop
earlier, every receiver is served iff all requirements lie in {head} ∪ R (`relay_serves_iff`, `relay_closes_nesting`).
With freshness: under StrongHeads every relayed copy is at most one step older than the injection
(`LeanMarlRelayDecisionV1.relay_age_le_inj`), so with an injection bound Φ and a margin larger than 2(e0 + ν(Φ+1)) the
relay action equals the fresh action (`relay_action_fresh`, composing `LeanMarlStrongOneHopV1` and
`LeanMarlDecisionLifetimeV1`).

**Claim D6 (acting is not identifying).**  With indicator records and answers "any world but the true one", one decoded
sender suffices to act, while identification fails whenever two senders are undecoded
(`decide_one_sender`, `identify_needs_all_but_one`).

**Claim D7 (compiled silence, quantitatively).**  Every randomised policy on an observation is unacceptable with
probability at least Σ_H min_{F∈H} p(F) over any disjoint family of obstructions inside its observation classes; the
bound is attained on a two-world instance (`LeanMarlObstructionMassV1.obstruction_mass_floor, floor_witness`).

## Positioning (verified 01/10 by web search; must go into Related work)
- Javdani et al. 2014 (decision region determination, hyperedge cutting): adaptive, noise-free, Bayesian; their
  hyperedges are our obstructions.  We add the prefix-broadcast structure, capacities, nesting and relay.
- Messias, Spaan, Lima, NIPS 2011: local beliefs often identify the optimal action, so communication can be skipped
  (qualitative, unique optimal action); our D1/D7 are the acceptable-set, exact and quantitative versions.
- SeqComm-DFL (Amoh, Parker, Marrero, arXiv 2604.08944, Apr 2026): priority-ordered sequential messages; Thm 5.1
  lower-bounds the value of communication by a Fano term in I(s; a*|o) scaled by the smallest advantage gap.  Fano
  charges for identifying a unique a*; the obstruction law charges only for obstructions.
- Local shields for Dec-POMDPs (Oxford): per-agent safe action sets from observation-consistent state subsets
  (safety filters, no communication).
- Mostaani, Vu, Chatzinotas, Ottersten, "Task-Oriented Data Compression for Multi-Agent Communications Over
  Bit-Budgeted Channels", IEEE OJ-COMS 3 (2022) 1867–1886 (SAIC state aggregation, arXiv 2005.14220, verified):
  task-relevant quantisation of observations; our D1 is the zero-distortion, acceptable-set form on a prefix channel.
- Ranking with multiple intents / generalized min-sum set cover (Azar, Gamzu, Yin 2009; min-sum set cover Feige,
  Lovász, Tetali 2004; constant-factor algorithms Bansal–Gupta–Krishnaswamy, Skutella–Williamson, Im–Sviridenko–van der
  Zwaan): ONE ranking serving users with different covering requirements, objective = average cover time.  Our D4 is
  its FEASIBILITY-with-deadlines version (receiver i's local obstructions must be hit by position K_i), reached from
  decision safety through the obstruction law; with forced singletons it is EDF; in general NP-hard.  Cite as the
  combinatorial home of the nesting price; do not claim the ordering problem.
- Priority Encoding Transmission (Albanese et al.), degraded message sets, functional index coding: nested decoding /
  function demands at the CODING level; our objects are orders of senders and decision demands (relations).

## Experiment V-D (running; results to be filled from `research/marl_budget/e3_decision_depth_report_20261001.txt`)
Teacher-defined acceptable sets (labelled proxy).  Predictions written before the runs (probe docstring, P1–P4).

## Collision note on the "two axes" (freshness vs decision relevance), 01/10 01:2x
The trade-off between freshness (AoI) and relevance (VoI / goal-oriented / semantic metrics) is ESTABLISHED in networking:
goal-oriented scheduling with AoI and VoI (e.g. arXiv 2512.12758 survey "From Information Freshness to Semantics of
Information and Goal-oriented Communications"; VoI-aware scheduling for multi-agent formation control; weighted AoI with
estimation-error weights; Age upon Decisions; Age of Actuation / Age of Actuated Information, arXiv 2601.15496).  So the
paper must NOT claim the two-axis idea.  What is specific here: (i) a measured, paired, within-state contrast on a learned
MARL teacher showing that the freshness-optimal (age-first) order is decision-ANTI-aligned while the congestion order is
decision-aligned (V-D); (ii) the formal decision-depth law on the nested prefix channel and the theorem that one relayed
packet (or one revision) replaces the nested condition by one inclusion at the head — the mechanism by which relay
decouples the axes.  Position against the goal-oriented literature in Related work, one paragraph.
