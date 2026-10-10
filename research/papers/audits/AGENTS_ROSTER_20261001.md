# Subagent roster (user rule 01/10/2026 19:1x: on "fetch", reuse these; spawn new only if none was ever fetched)

| id | role | launched | status | brief (summary) |
|---|---|---|---|---|
| a5e043f5fc399c33b | (A) Lean / papers / old-directions miner — read-only | 01/10 18:3x | resumed 03/10 02:4x (wake 1: deep literature read, done 02:5x); finished 19:1x (report: forced-tail predicate H1, schedule-dose H2, cap corollary H4; key numbers re-checked); resumed 05/10 09:1x for the TSI manuscript TEXT audit → FAILED 09:1x (session limit, HTTP 429), no findings; transcript ≈ 30 MB, so every resumed step reloads a very large context | Read work/p13_conjectures LeanMarl* (and older related) module docstrings, research/papers/_tex/paper_*.tex, ROADMAP / OPEN_MATH / THEOREM_MAP (read only), audits 0924–1001, memory notes; find hypotheses linking proved theory to the compatibility findings (channel-predictable age distribution / sign reversal; why matched acceptability ≠ return; anything more novel than shift + fallback); ≤ 8 ranked with sources, proved vs missing, cheapest test, kill criterion, novelty (web search allowed). |
| acae5606e7dd259e7 | (B) experimental-artifact miner — read-only, light numpy only | 01/10 18:3x | resumed 03/10 02:4x (wake 1: G1/G3, done 02:5x); finished 19:1x (report verified: H1 ρ −0.818, H5 ρ +0.721); resumed 05/10 09:1x for the TSI RESULT-TO-ALGORITHM audit → FAILED (stalled 600 s, watchdog), no findings; transcript ≈ 9.5 MB | Mine research/marl_budget reports / flags (not the pending target panels: train_match R_*, gate_prospective, g4 R_/Z_) for hypotheses: congestion-order vs K = 1 signature, headroom × compatibility, gate keys, natural experiments, census patterns; ≤ 8 ranked. |

Reuse: SendMessage(to=<id>) with the new task and file paths.  Do not open pending pre-registered target outputs in briefs.

**05/10 10:0x (user asked why the fetch was so costly):** both roster agents carry their full history since 01/10 (transcripts 30 MB / 9.5 MB). A resume is therefore NOT cheap. Before the next "fetch", tell the user the cost and ask whether to resume these two or to make one fresh, narrowly briefed agent.

**05/10 10:18 (user: "fetch lại 2 con đó … tầm 40 % token"):** A and B resumed for the second audit round. A: text audit of the 10:07 manuscript. B: result-to-algorithm audit of the TSI chain. Shared budget: stop when the session counter falls below 9.3 M. Findings are written incrementally to scratchpad `audit_A_text.md` / `audit_B_results.md`.

**05/10 10:4x (user: "bỏ hết exp vào queue … sau đó research chung vs 2 thằng kia"):** after both audits returned (A about 843 k tokens, 34 findings; B about 220 k, 7 findings; all checked and applied, C-128):
- B now reviews the wave-6 code before jobs 052–055 run (audit_B_wave6.md);
- A researches DC-Ada fidelity, DHCP / HONEST-CAV, multiplayer performative prediction and a refreshed collision search (audit_A_research.md).

Shared stop: counter < 10 M.

**06/10 05:42 (user: "cho fetch subagents như workflow đó, nhưng giới hạn ở 3-4 agents, nếu có thể dùng lại 2 thằng cũ thì tốt"):** publication-readiness research for the TSI paper, shared brief `scratchpad/research_pub/BRIEF_SHARED.md`.
- A resumed: collision / novelty for C1–C5 → `research_pub/A_collision.md`.
- B resumed: reviewer norms and evidence gaps → `research_pub/B_norms.md`.

| id | role | launched | status | brief |
|---|---|---|---|---|
| ac281cdf03c552d0f | (C) practicality / deployment researcher (web), read-only | 06/10 05:42 | running | premise realism, SPaT standards / latency, speed-binned sensing, emission-model evidence → `research_pub/C_practice.md` |
| ade12cdf2252f9af3 | (D) venue fit / submission logistics researcher (web), read-only | 06/10 05:42 | running | venues, deadlines, length, policies, formal-proof reception → `research_pub/D_venues.md` |
**06/10 05:52–05:55: all four returned** (A about 957 k tokens; B about 338 k; C about 131 k; D about 130 k). Reports are in `scratchpad/research_pub/{A_collision,B_norms,C_practice,D_venues}.md`. The main agent re-verified MATES 2609.26010, EP3985636, Paine 2025, ITSC 2027 (Boston, 1 Mar 2027) and Maadi 2022. C's WebFetch auto-saved one 3.3 MB PDF from an energy.gov redirect into tool-results (not opened, not deleted). B also delivered its pending wave-6 notes on job 052 (C-161).
