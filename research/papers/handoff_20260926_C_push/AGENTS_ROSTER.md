# Agent roster (session f9537975), Paper C push started 2026-09-26

Resume any of them with SendMessage(to=<id>) — context is kept; a new Agent call starts fresh.

| id | task | scratch dir | Lean file(s) |
|---|---|---|---|
| a703197028406baeb | C region law counts (1,1,2,2), g=(a,-a,b,b,-b,-b); owns LeanPaperCTwoMagSixV1 | scratchpad/c1122 | LeanPaperCTwoMag1122V1 (or TwoMagSix) |
| ac26b6bf68578cbe8 | C region law counts (2,2,1,1) | scratchpad/c2211 | LeanPaperCTwoMag2211V1 |
| a72b3d0c96e74a6e7 | C region law counts (2,2,2,2) | scratchpad/c2222 | LeanPaperCTwoMag2222V1 |
| a0db44ab5e4e4a69e | C sharpness of zero-value ranges on g_m + one exchange suffices | scratchpad/csharp | LeanPaperCBudgetSharpV1 |
| a921a4a63a3f96047 | C count=item reduction, transport lift, subset->order realisation | scratchpad/ccount | LeanPaperCCountReductionV1 |
| a1b4a28f58cceafad | READ-ONLY fidelity audit of paper C statements vs Lean | scratchpad/caudit | — |

Budget rule (user): when ~30% of session tokens remain, message every running agent to stop and
report in detail (done / not done, files), then verify their work.
LeanPaperCTwoMag2211V1 VERIFIED 2026-09-26 sha eee35aa7 13/13 std axioms; in MODS; smoke gate pending
LeanPaperCBudgetSymV1 + LeanPaperCBudgetSharpV1 AUDITED 2026-09-26 line-by-line; B formulas match LP data at 847 pts (7e-17); in MODS; smoke gate pending
LeanPaperCCountReductionV1 + LeanPaperCCountRecourseV1 AUDITED 2026-09-26 line-by-line; CountLayerFeasible/CountTransport/countRecourseSet match script aware_value/recourse_value; in MODS

## Assignments 2026-09-26 ~11:30 (after C closure round)
| id | new task | scratch / output |
|---|---|---|
| a0db44ab5e4e4a69e | C: odd-m one exchange (recourse_one_odd), explore + Lean LeanPaperCBudgetExchangeOddV1 | scratchpad/csharp/PROGRESS.md |
| a921a4a63a3f96047 | C: count-model LP data for odd m (feeds a0db) | scratchpad/codd_B/FINDINGS.md |
| a703197028406baeb | B T1: parity per-world law, LeanPaperBParityWorldV1 | scratchpad/c1122/PROGRESS_B.md |
| ac26b6bf68578cbe8 | B T4: decision probe E[Y^2], LeanPaperBDecisionMomentV1 | scratchpad/c2211/PROGRESS_B.md |
| a72b3d0c96e74a6e7 | B T5/T7/T8: LeanPaperBAssemblyV1 | scratchpad/c2222/PROGRESS_B.md |
| a1b4a28f58cceafad | idle (C fidelity audit, read-only) — use for B/A audits next | — |

NOTE: agents launched inside a Workflow (fidelity audit wv2n4a527, 33 agents; odd-exchange
explore w2kqmyf7u, 3 agents) CANNOT be resumed with SendMessage ("No transcript found").
Their results are only in the workflow journals:
- ~/.claude/projects/-Users-phanan-cig-amf-main/f9537975-549f-4276-ad79-40f2fa3240e3/subagents/workflows/wf_c6de22ec-21b/journal.jsonl
- tasks/wv2n4a527.output (full audit result JSON, 26 verified findings, all fixed)
Do not use Workflow for work an old agent can own (memory: feedback_reuse_old_subagents.md).
