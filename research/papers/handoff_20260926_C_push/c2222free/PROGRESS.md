# c2222free: FREE value of g=(a,a,-a,-a,b,b,-b,-b), K={1..7}, D=4(a+b), eta=8
Target W=V_free*D: r<=2: 2(a-b)/3; [2,3]: max(2b(3b-a)/(5b-a), 2a(3b-a)/(17b-5a), 4b/7); r>=3: 2(a-b)/7.
Plan: lower via cert_lower potentials (reflection or direct), upper via mixFlow + value_le_flow.

## Discovery/verification (2026-09-26)
- freelp.py: LP free value vs target at 305 ratios in (1,4] + {5,7,10,100,1000}: max gap 5.7e-14.
- certs.py: exact DP potentials for 5 certs (R1 A: 1/3 on k=3,4,5; R2 U 1/7, F1, F2; R3 uniform) in region
  bases (R1 s=a-b,t=2b-a; R2 s=a-2b,t=3b-a; R3 s=a-3b,t=b): ALL edge slacks have nonneg coefficients
  in (s,t); psi(0) = W exactly; all abs signs fixed on closed regions.
- flows.py: R1 flow aAbBbBaA 2/3, BaBaAbAb 1/3; R3 flow 5 paths (1/7,1/7,2/7,2/7,1/7).
- verify_r2.py: R2 flows F1 (3 paths), F2 (8), F47 (9) from c2222 notes: weights sum 1; F2,F47 zero slack
  at all budgets; F1 zero slack at k=3,4,5, slack at k=1,2,6,7 = q(r)(r-5)^2/(..), q=r^2-10r+17.
- In R2 basis: q_ab = a^2-10ab+17b^2 = t^2-4st-4s^2; 17b-5a = 2s+7t; 7a-17b = 4s-3t; 5b-a = 2s+3t.
## Lean plan: reflection (P2 integer polys in s,t, edgesOK decided) + cert_lower wiring; flows via mixFlow.
- T1 test (foreground, 2m08): `decide` on edgesOK (F1, match tables) PASSED; `simp [kapR2]` on an 81-arm match table
  TIMED OUT (whnf) -> redesign: cost linear forms computed by a formula (kap R) + absOK decide + generic kap_link.
- RULE: runs > 2 min detached via nohup; log recorded here.
