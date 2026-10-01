# P1 progress log

- 2026-09-27: read MARL_STORY_VERDICT, FULL_CORPUS_AUDIT §6 §12 §15 §18 §21, TASKS rules+corrections.
  Wrote COMPACT.md. Amendment received: do not create LeanMarlRevisionFrontierV1.lean; own
  LeanMarlScorePriceV1.lean and LeanMarlRevisionFamilyM6V1.lean.
- Step 1 done: d6_frontier_exact.py (sha 8ee52bad...) -> d6_frontier_exact.json + .log, 1702 self-checks OK.
  Vb s: F_k(R) = (d_k - R)_+ * 2s, d_k = min(k,6-k), delta = 2s+2; R*=3 at k=3 for the SCORE prefix.
  G(R)=0 for all R (ranking [1,2,3,0,4,5] optimal at every k): nesting itself is free on Vb.
  Table + Lean names + M2 hint (surplus bound holds for arbitrary S,T; hTop unused) sent to main.
  Counterexample-module read was denied by the permission classifier: not computed.
- Combinatorial (scratch comb.py, comb_brute.py; to be archived in d6_nesting_search.json part A):
  m<=6, R=1: every one-set-per-budget system has a chain within 1 exchange (m=5: 0/100 bad, m=6: 0/4500
  bad, two independent scripts) => G(1)=0 for EVERY set loss at m<=6. m=7,R=1: 519/15435 bad (O3 fixed);
  witness O2={0,1},O3={4,5,6},O4={0,1,2,3},O5={0,1,2,3,4}. R=2: m=7 0/35, m=8 0/3136 bad. Sent to main.
- main owns: LeanMarlRevisionFrontierV1 (general M2, done), general nesting lower bound + Theta(m) family.
- My order now: (1) LeanMarlNestingDegreeV1.lean: m=7 witness (no chain within 1), m=6 all systems
  (chains C1..C5); (2) m=9 R=2 run in background; (3) m=7 D6-world hill-climb d6_nesting_search.py
  (written, not yet run); (4) LeanMarlRevisionFamilyM6V1; (5) LeanMarlScorePriceV1 (M1).
- nesting_degree_comb.py ran: m6R1 0/225, m7R1 519/15435, m7R2 0/35, m8R2 0/3136 (JSONs written).
- WRAP-UP order received: stopped. No Lean file created, m=9 not run, hill-climb not run.
  HANDOFF.md written with all files, hashes, next steps. No background processes.
