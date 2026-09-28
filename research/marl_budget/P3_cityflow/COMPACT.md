# P3 CityFlow — compact summary of prior context (2026-09-27)

My earlier context (2026-09-26) was a READ-ONLY audit of Paper C closed forms against the stored
LP JSONs (paperC_typed_frontier/transition/budget_recourse). It is history now, and I own nothing
from it. Facts still worth keeping:
- The stored LP values match thm:twomag1122, thm:twomagprice, thm:twomag2211 and thm:awareexact
  to <= 1e-15. The source hashes in the JSONs match the current scripts.
- C's recourse evidence has R* <= 1 at every computed cell (audit §18). That is why the MARL
  story needs a non-degenerate revision frontier (P1/P2); P3 does not decide it.
- Wording findings were sent (240 = 60 count vectors x 4 ratios; the (1,1,2,2) price is not
  monotone on [2,5/2]). I do not edit .tex.

Why P3 exists (MARL_STORY_VERDICT, FULL_CORPUS_AUDIT §19, §21):
- models/core_behavior.py:474-495 reads obs_j and action_j of EVERY candidate neighbour at every
  step. So the existing "budget" saves compute, not communication.
- models/policy_value.py has an actor and a scalar value only, with no set-valued critic Q(s,S).
  So δ□ (the max mixed difference) and the score margins cannot be measured.
- The theory prediction to test: nesting is free when every consecutive score gap is >= 2δ□ (D6
  margin_two_sufficient); revision should help where δ□/margin is large.

Assignment (coordinator "main"):
1. research/marl_budget/PROTOCOL_v0.md: the executable contract. It covers agents =
   intersections, the message content and its bytes, budget traces (fixed/drops/bursty), rank
   before the reveal, R replacements after it, paid messages, the actor, absent messages as a
   cached value with its age or a local prediction, costs, the Q(s,S) interface, baselines,
   metrics, paired seeds, and negative results.
2. NEW envs/external/cityflow_budgeted.py, which enforces the budget at information access, and
   a NEW unit test that can FAIL if a fresh observation of a non-transmitted neighbour leaks.
3. A smoke episode on a tiny grid in the isolated runtime, run with python -u, logging to
   work/run_logs/cityflow_smoke_20260927.log. No training. If CityFlow cannot run: report the
   command and the error.

Rules:
- New files only; never overwrite or delete (archive to legacy/).
- No edits to .tex, ROADMAP or verify_all.sh. No Lean compiles.
- RAM is shared with a Lean gate and two Lean agents: keep the jobs tiny.
- Long jobs use run_in_background, with no sleep-polling.
- Report to main via SendMessage, and end with SubagentHandback.
