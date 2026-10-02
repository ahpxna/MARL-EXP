# Direction brainstorm: can the current story be lifted? (01/10/2026 21:1x EDT, `date` 21:13:27)

User 21:0x: brainstorm from all assets (Lean, artifacts, results) and from the literature whether a direction with more
novelty, practicality and impact exists; check whether the problem is practical and what the field says is unsolved.
No subagents (no "fetch").  Reading was mostly abstracts plus one full text (Farazi–Klein–Brown) and one HTML read
(Shisher–Sun); this is a map, not an exhaustive review.

## 1. Is the problem practical, and what does the field say is open?
| Source | What it shows | What it leaves open |
|---|---|---|
| Collaborative perception with latency (SyncNet/Latency-aware CP, ECCV 2022; CoBEVFlow, NeurIPS 2023; CoDynTrust 2502.08169; V2X survey 2308.16714) | Without compensation, collaborative perception can fall BELOW single-agent perception under latency; remedies: compensation modules, trust gating, training with latency sampled 0–500 ms | No prediction of when harm is forced by the channel; remedies are empirical |
| CAIC (UAI 2026) | Shared channel as a queue with state-dependent service; ablation: stale messages under delay can be worse than no communication | Same |
| AgentComm-Bench (2603.20285) | Stale memory / bandwidth collapse: > 96 % drops (navigation); corrupted data −85 % F1 | Recommends reporting several impairment conditions |
| Decoupled Delay Compensation (2605.26286) | Policies trained synchronous degrade under deployment delay; plug-in state estimator | No account of which deployments need it |
| Gong et al. (2609.36855, LLM agents) | A wrong upstream message flips a correct receiver in up to 32 % of cases; "communication should be selective" | Learned-RL receivers not studied |
| Surveys 2511.11393, 2601.12886 | Open: robustness under realistic channels; theory–practice gap; co-design of communication, learning and robustness | Generic |
| Shisher & Sun, "Timely communications for remote inference" (2404.16281) | Inference error as a function of AoI may be NON-monotone (non-Markov data); scheduling for general AoI penalties | ASSUMES the AoI process is independent of the data and that the learned error function transfers to deployment "regardless of the actual AoI distribution"; training/inference AoI mismatch and extrapolation are not discussed |
| Event-triggered remote estimation (Noack et al., KIT) | The ABSENCE of a message is informative ("negative information") under state-dependent triggers | Model-based estimators; learned receivers whose implicit use of this information shifts with capacity not studied |
| Farazi–Klein–Brown (JCN 2019; general interference version) | Lower bounds on peak/average AoI for every schedule, ≤ ν transmitters per slot, one status per packet | Prefix / heterogeneous decoding, full-table relay (our floor's new part) |
Verdict: the problem is practical (V2X, shared-channel MARL, LLM agents) and harm is documented; what is missing in every
source read is (i) a channel-level prediction of WHEN the learned receiver is forced off its training support and (ii) WHICH
kind of repair can work.

## 2. Candidate lifts, ranked
### H-A (top): two kinds of channel shift — support shift vs meaning shift
- Claim: with a STATE-INDEPENDENT stream order (age-first, round-robin, TDMA) a capacity change shifts only the SUPPORT of
  the receiver's view (ages / composition out of the training range) — repairable by coverage (age interface, augmentation),
  and predicted by the floor.  With a STATE-DEPENDENT order (congestion priority, event-triggered or confidence-based
  selection as in Where2comm / ETCNet, V2X priority under DCC) staleness is INFORMATIVE ("stale ⇒ uncongested"), and a
  capacity change changes what a stale copy MEANS (concept shift) — coverage cannot repair it; only matched training or
  capacity-conditioning can.
- Assets that point here: age-response intervention (support shift, L-227); the floor's classification of congestion-order
  failures as scheduler-induced (L-225); burden over-predicts congestion harm (B_3 29.7 → −0.15 %): stale copies under that
  order belong to unimportant senders, i.e. staleness carries information; v2's congestion-order relay loses at low capacity.
- Counter-evidence to keep: shared per-student fragility across K = 1 and congestion shifts (ρ −0.818) — a common learner
  factor coexists with any mechanism split.
- Theory (small, Lean-able): (a) open loop, a schedule that is a function of the capacity trace only ⇒ p(sender state |
  copy, age) is capacity-invariant; (b) a two-sender witness where a state-dependent order makes it capacity-dependent.
  Caveat: closed loop couples the world to the channel through actions; (a) is open-loop.
- Cheapest test (no training): with a fixed driving policy, measure E[true current state − copy | age] (and its spread) by
  capacity, under age-first vs congestion order.  Prediction: capacity-invariant under age-first, capacity-dependent under
  congestion.  Decisive test (training): an age-augmented student fixes age-first K = 1 but not congestion low capacity;
  matched training fixes both.
- Novelty: implicit information is classical in estimation; its role in the deployment shift of LEARNED receivers and the
  remedy classification were not found (two searches).  Practicality: predicts a failure mode of popular selection-based
  communication when bandwidth changes.

### H-B: a fixed learned receiver's value of communication is not monotone in capacity ("upgrades can hurt")
- Bayes value is information-monotone (bayes_refine, team nesting); the imitation optimum is not (LeanMarlImitationGapV1).
- Evidence pending: TM3 (prediction P-UP1 / P-UP2 registered in PROTOCOL_E3_FRAMING_DECISION Addendum 1 before reading).
- A train-capacity × deploy-capacity matrix would be the figure; no search hit for "trained at low bandwidth, worse at
  high bandwidth" in MARL communication.

### H-C (positioning, not a direction): learned-receiver AoI
- Shisher–Sun's independence assumption fails for learned receivers: the error function e(δ) depends on the TRAINING AoI
  distribution (the age-response probe measures it: peak at the training ages, worse at unseen younger and older ages).
  Gives a networking-venue framing and a precise gap statement.

### Not recommended now
Compiled silence as a field-wide evaluation bar (needs other benchmarks; CTDS, MUTE 2607.03473 nearby); SafeEdit (L-229);
more gates; an LLM-agent port.
