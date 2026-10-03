# G7 — three floors, what the Lean covers, what the E3 paper may claim (wake 2, 03/10/2026 04:0x EDT)
Source: subagent A (read the full sources of LeanMarlReceiverFloorV1/V2, NetFloorV1, ProvisioningV1, SupportV1, EmulationV1,
LeanCityReceiverContractV1, the act-vs-identify part of DecisionDepthV1; paper_b.tex l. 198, 506; support.tex l. 657, 719).
Verified by me: the theorem names exist (EmulationV1 l. 37 / 63 / 77; DecisionDepthV1 l. 468 / 481); gate list
work/p13_conjectures/verify_all.sh contains SupportV1, EmulationV1, ReceiverFloorV1 but NOT LeanCityReceiverContractV1,
LeanMarlDecisionDepthV1, LeanMarlCommValueV1.

| Object | Definition | Covered by | Properties |
|---|---|---|---|
| R reconstruction floor | least channel resource with which SOME decoder recovers the fresh view / world | dynamic: ReceiverFloor V1/V2, NetFloor, HoldFloor, PrefixInstance (`receiver_floor` ≤ K·n, `timed_forced_stale`, `net_floor`); static: `identify_needs_all_but_one`, B's s_id rate, SUPPORT recovery | channel-only, monotone, sharp (witnesses) |
| T task floor | least resource with which SOME decision-adaptive policy is acceptable / meets a Bayes target | STATIC only: `decode_safe_iff`, `prefix_safe_iff` (= s*), `decide_one_sender`, `bayes_refine`, `floor_le_bayes`, B safe law + rates, SUPPORT decide side | T ≤ R; strict gap proved only statically (1 vs m − 1 senders; h⁻² vs h^{−2(m−1)}); no dynamic bridge |
| F frozen-receiver floor | least resource with which a FIXED trained receiver keeps its level (≥ silent) | instance level: `upgrade_hazard`, T1 `no_receiver_free_certificate`, `upgrade_emulation` / `downgrade_strict` (knowledge level); Provisioning = proved cap on an R-type count parameterised by the receiver's τ | NOT monotone; can exceed T; depends on the receiver |

## Candidate Lean (not written yet; hypotheses checked satisfiable by A with witnesses)
* L1 `identify_implies_decide` + `task_lt_reconstruction` (DecisionDepthV1): identifiability ⇒ decidability; same family with
  T = 1, R = m − 1 (witness m = 3, indMsg).
* L2 `task_upward_closed` + `frozen_floor_not_monotone` (SupportV1 instance, Fin 2 × Fin 2): the feasible-task set is
  upward-closed, the frozen-adequate set is not, and becomes so through emulation (g ∘ γ repairs).  This is the formal
  counterpart of the G2 emulation experiment.
* L3 `fresh_task_floor` (ReceiverFloorV1 + DecisionDepthV1): for a time-iid world, the dynamic task floor is K ≥ h*(task)
  (hitting number of local obstructions); R is the case h*(idSafe) = m − 1 at τ = 0 (witness Fin 3, K = 1).  Caveat: E3
  traffic is time-correlated (stale copies informative) — not covered.

## What the E3 paper MAY / MAY NOT claim from current Lean
MAY: channel-only sharp floors on FRESH-VIEW KNOWLEDGE (call them knowledge floors); rule A's channel cap (no scheduler raises net
above θ(m − 1) when K ≤ K_min); upgrades emulable / downgrades below the floor not (knowledge level); statically, deciding can
need strictly less than identifying and the Bayes optimum is information-monotone; in explicit instances, training risk is blind
off-support, a training-optimal frozen receiver can fall below silence after an information-preserving upgrade, no channel-only
certificate is universal.
MAY NOT: that the receiver floor bounds decisions / value / return; that forced staleness CAUSES the frozen receiver's failure
(SupportV1 shows possibility only); that rule A predicts the gain's sign or suffices; that B's rates or SUPPORT's separation hold
on the E3 dynamic relay channel; that emulation recovers more than training-channel performance; that mixtures have the
mixture's age response.  Gate wording: "compiled, smoke-gated" (full gate stopped at 33/315 on 02/10, L-280); add
CityReceiverContractV1, DecisionDepthV1, CommValueV1 to verify_all.sh before citing them.
