# Handoff a1b4 (read-only auditor): G1 gate, and C1 state — 2026-09-27

## G1 — smoke gate of the seven older papers (+ unified): RUNNING

- Run: `smokeOLD7_20260927`, pid **63390** (`verify_all.frozen.sh`), started 10:58:04 -0400, J=2.
  Frozen directory: `work/gate_runs/smokeOLD7_20260927/`. Log: `work/run_logs/smokeOLD7_20260927.log`.
- At 11:55: 86/251 modules exited, 0 failed, 0 error lines, 0 sorryAx. 57 of the 120 cited
  modules are done. Rate is about 1.5 modules/min, so the finish is roughly 13:45–14:30.
- A waiter `caffeinate -w 63390` (my background task) is still attached. It only prints
  SUMMARY.txt on exit and does nothing else.
- **Known artefact:** `LeanD6AllocationFiniteBridgeV1` has `import Aesop`, which the script
  classifies as outside the gate, so `imports_closed=0`. The verdict will read SMOKE FAIL even if
  every module builds. Treat this separately from genuine failures.
- Partial report: `research/papers/audits/GATE_OLD7_20260927.md`. Its last section says exactly
  how to finish it. The parser is
  `/private/tmp/claude-502/-Users-phanan-cig-amf-main/f9537975-549f-4276-ad79-40f2fa3240e3/scratchpad/caudit/g1/report.py`;
  the inputs are `list.json`, `GATE_ONLY.txt` and `unresolved_all.json` in the same directory.
- Do not start another gate while pid 63390 is alive (one gate at a time).

## C1 — odd one exchange: NOT compiled, handed back

I followed the order not to start C1 as work. Before that order arrived I had written a design
and an **uncompiled draft**:

- `work/p13_conjectures/LeanPaperCBudgetExchangeOddV2.lean` (new file, own namespace
  `CIGAMF.P13.PaperCBudgetExchangeOddV2`, imports only `LeanPaperCBudgetExchangeOddV1`, nothing
  imports it). It has **never been compiled**. It must not be cited or put in a gate until it
  compiles. Archive it or hand it on, as you prefer.
- `LeanPaperCBudgetExchangeOddV1.lean` has **no olean** in `.lake/build`. Whoever takes C1 must
  first compile V1 by itself, after the gate ends. Its imports' oleans (BudgetExchangeV1,
  BudgetSharpV1, BudgetSymV1, BudgetGmV1) are fresh.
- The design, which the draft implements:
  - `corr = if p<k then cB else cA`. Sum over positions with `sum_pos_split`, and over slots with
    `PaperCBudgetExchange.slot_sum` plus a new `slot2_sum`.
  - The closed form is `sigmaVal`. For odd k: `(m−k)(−[1=w]+[−3=w]−[−1=w]+[3=w])`. For even k:
    `k(−(h+2)[−1=w]+[−3=w]+h[1=w]+[3=w])`.
  - `oddT_band` gives a class-average deviation of at most `etaOne h / m`, where
    `etaOne = h(h+2)/(h+1)^2`. The division by m is required, and the bound is tight at even
    k = 2h for class −1.
  - `etaOne ≤ η_t`.
  - `recourse_one_odd`:
    - For `η ≤ etaOne`, use `recourse_eq_aware_odd`.
    - Otherwise commit `oddLaw`. Draw the end budgets from `indepPlan` with near-optimal
      subset laws. Use `planJ` / `sym_plan` with `oddT` at the middle budgets, which costs 0.
    - This mirrors `recourse_one_even`.
  - For m = 3, use `recourse_full`, since every interior budget is an end budget.
  - Satisfiability witness: m = 5, η = 1.
- Numerics cited by the coordinator: V^(1) = B at every band for m = 5, 7, 9
  (`research/unified_20260919/paperC_budget_recourse.json`).

## Other state

- Paper B fidelity audit: partial (findings B1–B12 sent earlier; the not-reached list is in my compact
  summary `scratchpad/caudit/COMPACT_20260927.md`).
- Progress log: `scratchpad/caudit/PROGRESS_20260927.md`.
