# P1 D6 frontier — compact summary of prior context (2026-09-27)

Prior context (2026-09-26) was a READ-ONLY fidelity audit of Paper C thm:twomag1122
(paper_c.tex:562-599, supplement:582-600) against LeanPaperCTwoMag1122{Frontier,CertV2,Kink,Flow}V1.
It is history; nothing there is owned by me. Still-true facts worth keeping:

- The (1,1,2,2) frontier Lean matches the manuscript formulas, regions, strict/closed endpoints,
  kink values, orbit proportions (K1, K2, K3) and the two cross-multiplied differences
  6(13b-5a)(15ab-3a^2-16b^2), 6(a-b)(13b-5a)(3b-a) (exact Fraction check).
- Minor wording findings reported (not fixed; I do not edit .tex): the r<=2 kink eta=1 is missing
  from the kink list; "last three kinks coincide at 13/5" is ambiguous; the "275 grid points"
  exact-LP check has no archived artifact (only session scratch c1122f/ident.py).
- On C's objective every computed cell has R* <= 1 (audit §18): the reason P1 exists.

Pitfalls learned (Lean/tooling):
- One Lean compile at a time (16 GB RAM, ~2.7 GB each). Build with
  `cd work/p13_conjectures && lake env lean -o .lake/build/lib/lean/X.olean X.lean`.
- No sorry / native_decide; axioms only propext, Classical.choice, Quot.sound; print them.
- Exact rational checks: python Fraction; beware variable shadowing in loops (a bug I hit once).
- Never overwrite: check existence before writing; archive to legacy/.

Current assignment (P1, coordinator main, amended):
- STEP 1 exact frontier computation on D6 m=6 family Vb s (and other D6 witnesses), JSON output
  research/marl_budget/P1_d6_frontier/d6_frontier_exact.json; send table to main at once.
- STEP 2 M1: work/p13_conjectures/LeanMarlScorePriceV1.lean.
- Family-level m=6 frontier: work/p13_conjectures/LeanMarlRevisionFamilyM6V1.lean.
- Do NOT create LeanMarlRevisionFrontierV1.lean (main owns the general M2 theorem).
- Send main the exact Lean names/signatures of the D6 loss, response-span score, delta-box, Top-k.
