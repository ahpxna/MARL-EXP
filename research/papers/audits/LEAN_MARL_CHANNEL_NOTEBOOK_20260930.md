# Lean notebook: the prefix-broadcast channel (paper_marl_v2 Section 3)

Started 30/09/2026 19:5x EDT (user 19:4x).
- Purpose: list every statement of paper_marl_v2.tex that needs Lean; mark what the existing corpus can reuse (from the
  survey of `work/p13_conjectures/*.lean`); track writing and compile status.
- Rule: nothing enters the manuscript as a theorem before compiled, gated Lean.
  - Gate: `GATE_ONLY="<mods>" bash verify_all.sh` in `work/p13_conjectures`.
  - Acceptance: exit 0, 0 errors, no `sorry`/`sorryAx`, no `native_decide`, axioms ⊆ {propext, Classical.choice, Quot.sound}.
  - Every hypothesis set gets a satisfiability witness.

Priority = 2·need + 1·weight (user 19:3x: "most needed first, then heaviest").

| id | statement (paper label) | need | weight | score | module | reuse | status |
|---|---|---|---|---|---|---|---|
| L1 | One-step freshness with a covering head (Claim cl:onehop), with the head-table lemma | 5 | 4 | 14 | LeanMarlRelayOneHopV1 | none found (new model) | to write |
| L2 | Invariants: table ≤ last transmission, cache ≤ last transmission (used by L1, L4) | 5 | 1 | 11 | LeanMarlRelayOneHopV1 | — | to write |
| L3 | Covering receiver exists under the threshold form (Lemma lem:cover) + head decoded by all (K ≥ 1) | 5 | 2 | 12 | LeanMarlRelayOneHopV1 | Finset.exists_max_image (Mathlib) | to write |
| L4 | Satisfiability witness for L1 (m = 3 periodic schedule) + application of L1 to it | 5 | 2 | 12 | LeanMarlRelayOneHopV1 | style of LeanMarlDecisionCertificateV1.skip_hypotheses_satisfiable | to write |
| L5 | Injection floor: #{j : f_t(j) ≤ s} ≤ (s+1)L and the sum bound F(m, L) (Claim cl:floor, part 1) | 4 | 3 | 11 | LeanMarlInjectionFloorV1 | layer-cake idea of LeanAdaptiveExpectedStoppingV1 (measure-theoretic; the finite version is written anew) | to write |
| L6 | Floor attained by a round-robin / age-first schedule with constant L (Claim cl:floor, part 2) | 3 | 4 | 10 | LeanMarlInjectionFloorV1 | — | to write |
| L7 | Injection bound under age-first ordering (Claim cl:inj) | 4 | 3 | 11 | LeanMarlAgeFirstInjectionV1 | apportionment style of LeanAdaptive* (rank / deficit arguments) | to write |
| L8 | Threshold form of prefix decoding (Lemma lem:thr): "first K others" = {j ≠ i : pos j < r i} | 4 | 3 | 11 | LeanMarlRelayOneHopV1 or separate | — | to write |
| L9 | Monotonicity in capacity for a fixed order sequence (Claim cl:mono) | 3 | 1 | 7 | LeanMarlRelayOneHopV1 | Finset.sup_mono | to write |
| L10 | Decision lifetime composition (Claim cl:life) | 2 | 1 | 5 | reuse | LeanMarlDecisionCertificateV1.argmax_stable, lifetime_from_drift_rate (PROVED) | reuse; maybe a 10-line corollary |
| L11 | Phase-lock witness m = 9, K = 2 (Remark rem:lock): a never-covered pair under age-first, index ties | 2 | 4 | 8 | LeanMarlPhaseLockV1 | decide-on-integer-dynamics template of LeanAdaptiveGreedyTraceV1 | to write |
| L12 | Phase-lock formula for L divides m (general) | 1 | 5 | 7 | — | — | optional |
| L13 | Sticky order: a sender outside every decoded prefix is never transmitted (starvation) | 2 | 1 | 5 | LeanMarlAgeFirstInjectionV1 | — | to write |
| L14 | The hub trade-off: a covering head can raise the injection age (a witness) | 1 | 3 | 5 | — | — | optional |
| L15 | Compiled silence (pillar 2): a zero-byte policy suffices iff no obstruction hides in a local class; it fails on such an obstruction; messages keep safety (instances of the UNIFIED law); the agreement-split identity and the tautology of the Z-split; the excess over a same-information null can be negative | 4 | 2 | 10 | LeanMarlCompiledSilenceV1 | **LeanUnifiedObstructionOrderV1** (classes_resolve_iff, resolution_refines, obstruction_error_floor_*; PROVED, olean in lib) | written, compiling |
| L16 | Failure anatomy (pillar 3) | — | — | — | not Lean: empirical (ledger L-132…L-184) | — | — |
| L17 | The six-cell rule is an intersection–union test: under any null in the union, P(all six reject) ≤ α (Berger 1982), used in Experiments/Statistics | 3 | 2 | 8 | LeanMarlIntersectionUnionV1 | — | to write |
| L18 | Byte layout: the relay packet 17 + (m−1)·21 bits fits 200 bits iff m ≤ 9; 185 bits at m = 9 (the scalability limitation) | 3 | 1 | 7 | LeanMarlRelayLayoutV1 | — | to write |
| L19 | Round-robin keeps every sender within 1 of quota (uniform targets), used in V-Q | 2 | 2 | 6 | LeanMarlRoundRobinQuotaV1 | LeanAdaptiveTrackingV1.tracking_bound (deficit ≤ 1 for floor-squeezed allocations) | to write |
| L20 | Memory buys at most one step under a covering head: a persistent (gossip) merge is fresher than the transient one, but by at most one step for every receiver other than the head | 3 | 2 | 8 | LeanMarlRelayMemoryV1 | LeanMarlRelayOneHopV1.one_hop | to write |
| L21 | The threshold r = K + [pos i < K] is monotone in K, so L9 gives monotonicity in capacity | 3 | 1 | 7 | LeanMarlPrefixThresholdV1 (v2) or bridge | — | to write |
| L22 | Cap rule: decoded sets restricted to the first c positions keep the threshold form with min(r, c), so covering heads and one-hop apply under cap4 | 3 | 2 | 8 | LeanMarlChannelBridgeV1 (v2) | LeanMarlRelayOneHopV1.prefixDecoded | to write |
| L23 | Reuse, cited, no new Lean: V-Q witness (LeanAdaptiveOnlineQuotaFailsV1.online_quota_fails, LeanAdaptiveGreedyTraceV1.greedy_reaches_witness); V-A source (LeanPaperARepairLawV1.two_arm_starvation, no_threshold, linear_repair); V-η (LeanMarlBlockFrontierV1.block_frontier, LeanMarlE1bUniformV1) | 2 | 0 | 4 | — | existing PROVED modules | cite in paper |
| L24 | Channel bridge: the head at position 0 is transmitted on the prefix channel (m ≥ 2, thresholds ≥ 1), so the injection bound holds there | 4 | 1 | 9 | LeanMarlChannelBridgeV1 | L1, L7 | written |

Order of writing (score, ties to the heavier): L1 (+L2, L3, L4 in the same module) → L5 → L7, L8 → L15 → L6 → L24 → L11 → L17, L20, L22 → L9 → L18, L21 → L19 → L13 → L10 → L14 → L12.
(20:1x: L17–L24 added after the user asked why the list was so short. The first list covered only Section 3's claims; this one covers every mathematical statement the paper relies on.)

## Survey of the existing corpus (reuse marks)

Survey method (19:5x):
- A catalogue of all 777 `*.lean` in `work/p13_conjectures`: docstring, theorem and def names.
- The modules ranked by relevance keywords; the full docstrings of the top ~95 read; the reusable ones read in source.

Families:
- LeanD* (261, D6: Gaussian/design);
- LeanPaper* (228, Papers A/B/C);
- LeanStructural*, LeanFunctional*, LeanSupport*, LeanAdaptive*, LeanMarl* (22), LeanQuery*, LeanMaster*;
- AxiomAudit*.

Conclusion: NO module models relay tables, age dynamics or the threshold form of prefix decoding.  L1–L9, L11 and L13
are new models.  Reuse:

| target | reusable object | where | use |
|---|---|---|---|
| L8 | `IsRanking pos := Injective pos ∧ ∀ i, pos i < card`, `prefixSet pos k`, `card_prefixSet` (a length-k prefix has min k n items) | LeanStructuralRetainedMarginalV1 (olean present) | the rank count #{k : pos k < pos j} = pos j |
| L8 | `prefixSet_mono`, `prefix_realises` | LeanMarlMenuRevisionV1 | nestedness of prefixes |
| L6 | `rotation_hits_once` (each item occupies each position exactly once over the m rotations), `cyclicPos`, `zmod_val_isRanking` | LeanPaperCCyclicV1, LeanStructuralRetainedMarginalV1 | round-robin / cyclic windows |
| L10 | `argmax_stable`, `argmax_stable_lipschitz`, `lifetime_from_drift_rate`, `margin_threshold_sharp` | LeanMarlDecisionCertificateV1 (PROVED, olean present) | decision lifetime: direct reuse |
| L10 alt | LIFE1–LIFE5 | LeanFunctionalCertificateLifetimeV1 | gauge-invariant form |
| L11 | integer dynamics computed by `decide`, `maxRecDepth`, no `native_decide` | LeanAdaptiveGreedyTraceV1 | template for the phase-lock trace |
| L7 (idea) | minimum and deficit arguments | LeanAdaptiveTrackingV1 (`exists_deficient`) | the potential argument is written anew |
| context | Paper A `two_arm_starvation`, `no_threshold`, `linear_repair` | LeanPaperARepairLawV1 | the SOURCE shapes cited by V-A (not E3 Lean) |
| context | commitment bound `block_frontier`, `score_frontier` | LeanMarlBlockFrontierV1, LeanMarlEstimatedRevisionV1 | the V-η hypothesis (already proved) |

## Writing / compile log

- 20:0x LeanMarlRelayOneHopV1 (L1, L2, L3, L4): compiled with `lake env lean`, exit 0, 0 errors, no sorry.
  - Audited: table_le_lastTx, head_table_fresh, one_hop, one_hop_age, prefix_cover_exists, prefix_head_decoded,
    witness_hyps, witness_one_hop.  All axioms are {propext, Classical.choice, Quot.sound}.
  - First try: the witness used a ℕ → Fin 3 cast that does not exist, fixed with `⟨t % 3, _⟩`.
  - Warnings: `if_pos`/`if_neg` are deprecated, harmless.
  - Gate: pending.
- 20:0x–20:1x written and compiling in parallel (`lake env lean`; the machine is loaded, about 3–8 min each):
  - LeanMarlInjectionFloorV1 (L5 + an L6 example);
  - LeanMarlAgeFirstInjectionV1 (L7, L13);
  - LeanMarlPrefixThresholdV1 (L8; the card argument of card_prefixSet, restated on Fin m);
  - LeanMarlCompiledSilenceV1 (L15; imports LeanUnifiedObstructionOrderV1);
  - LeanMarlRelayMonotoneV1 (L9; imports LeanMarlRelayOneHopV1, whose olean was built into .lake/build/lib/lean);
  - LeanMarlDecisionLifetimeV1 (L10; imports LeanMarlDecisionCertificateV1, olean being built into lib);
  - LeanMarlPhaseLockV1 (L11; the order dynamics `next(π) = drop 3 π ++ sort(take 3 π)`, periodic, decide).

- 20:1x–20:4x second and third rounds.  Fixes were API only, no mathematics changed:
  - renamed lemmas `le_or_lt`→`le_or_gt`, `range_succ`→`range_add_one`, `not_mem_empty`→`notMem_empty`,
    `filter_card_add_filter_neg_card_eq_card` replaced by an explicit union argument;
  - a `simp` that did not unfold `injAge`;
  - a missing `DecidableEq R`;
  - a commutativity mismatch in `argmax_stable_gauge`;
  - a `sorry` I had left in a WRONG IUT witness (its region `univ` has measure 1 > α), replaced by a correct witness
    BEFORE compiling.
- **Compiled clean** (`lake env lean`, exit 0, 0 errors, no sorry, axioms ⊆ {propext, Classical.choice, Quot.sound}),
  12 modules:

| module | targets | key theorems |
|---|---|---|
| LeanMarlRelayOneHopV1 | L1–L4 | one_hop, head_table_fresh, prefix_cover_exists, prefix_head_decoded, witness_one_hop |
| LeanMarlAgeFirstInjectionV1 | L7, L13 | injection_bound, ahead_shrinks, sticky_starvation, ageFirst_witness |
| LeanMarlRelayMonotoneV1 | L9 | table_mono_sets, freshness_mono_capacity |
| LeanMarlPhaseLockV1 | L11 | orders_periodic, transmitted_is_prefix, never_covered_count (18/72), never_covered_forever (kernel decide) |
| LeanMarlPrefixThresholdV1 | L8 | firstK_eq_threshold, rankOthers_eq, nested |
| LeanMarlCompiledSilenceV1 | L15 | zero_byte_safe_iff, zero_byte_fails_on_obstruction, messages_keep_safety, agreement_split, split_is_tautological, excess_can_be_negative |
| LeanMarlStatLayoutV1 | L17, L18 | intersection_union_test, iut_witness, relay_layout_bits, relay_layout_nine |
| LeanMarlRelayMemoryV1 | L20 | memory_redundant (relay memory is EXACTLY redundant under a covering head), table_le_ptable |
| LeanMarlInjectionFloorV1 | L5 (+L6 example) | injection_floor, count_recent, sum_injAge_layer, floor_attained_example |
| LeanMarlDecisionLifetimeV1 | L10 | argmax_stable_gauge, relay_action_equals_fresh (reuses LeanMarlDecisionCertificateV1.argmax_stable) |
| LeanMarlRoundRobinQuotaV1 | L19 | rr_count, rr_within_one |
| LeanMarlChannelBridgeV1 | L21, L22, L24 | injection_bound_prefix, head_transmitted, threshold_mono, capped_eq, capped_cover_exists |

- 20:2x frozen gate `smokeMARLCH_20260930` (the 12 modules + 2 rebuilt dependencies, from scratch): running.
- 20:4x LeanMarlFloorAttainV1 (L6, general): written, compiling.
  - Content: age-first with exactly L transmissions per step attains the floor with EQUALITY at every step.
  - Lemmas: no_repeat, layer_exact, recent_within, floor_attained; non-degenerate witness alt_hyps / alt_floor.
- Remaining optional:
  - L12, the general phase-lock formula: the m = 9, K = 2 instance is proved; the general case is numerical only;
  - L14, the hub trade-off witness (numerical in the replica).
- Not formalisable here: L16 (failure anatomy) is empirical.
