# c1122 progress log (counts (1,1,2,2), g=(a,-a,b,b,-b,-b))
- [start] read TwoMagFour, TypedFlow, FlowCert, PathMix, TwoMagSix, FreeBand; K = {1..5}.
- [scan] grid scan done (scan.log): r<=2: T=(r-1)max(2/3-eta/6,1/2); r>=3: T=(r-1)max((1-eta)/3,1/5);
  2.6<=r<=3: T=max((1-eta)(r-1)/3, 2/5); middle 2<r<2.6 complex (rational in r). T = D*V (b=1).
- [reduction] duals only use A-band (types 0,1 equal); symmetric reduction: LP over sequences with features
  u1=(c1+c5)/2,u2=(c2+c4)/2,u3=c3, alpha1=(#A pos1+#A pos6)/2, alpha2=(#A first2+#A last2)/2,
  band |E a1-1/3|<=eta/3, |E a2-2/3|<=eta/3.
- [exact] xlp.py (exact simplex), red.py (reduced LP, matches HiGHS), pieces.py (exact eta-breakpoints per r).
  Region map (rho=r-1): L r<=2: T=(r-1)max(2/3-eta/6,1/2). M1 [2,7/3]: max((4-r)/3-eta*rho/6, rho(2-rho)/2+(1-eta)(2-rho)^2/6, rho(2-rho)/2).
  M2 [7/3,5/2]: max((4-r)/3-eta*rho/6, L2', Tf) with Tf=2rho(2-rho)/(8-3rho), eta_free=4(5-3rho)/(8-3rho).
  M3 [5/2,13/5]: max(rho(1-eta)/3, (4-r)/3-eta*rho/6, L2', Tf). M4 [13/5,3]: max(rho(1-eta)/3, 2/5). H r>=3: rho*max((1-eta)/3,1/5).
- [lean] compiled LeanPaperCTwoMagSixV1.lean unchanged (olean now exists, warnings only, 2:17 wall).
  No new project Lean module written yet. TestSt.lean (scratch test of decide vs simp for stC evaluation) was killed on STOP.
- [step1 verified in Fractions, full 36-state model: step1.py] (rho=r-1, b=1; T = D*V, D=2a+4b)
  eta=0 values: T0 = 2rho/3 (r<=2), (3-rho)/3 (2<=r<=5/2), rho/3 (r>=5/2).
  free values : Tf = rho/2 (r<=2), rho(2-rho)/2 (2..7/3), 2rho(2-rho)/(8-3rho) (7/3..13/5), 2/5 (13/5..3), rho/5 (r>=3).
  eta_free    : 1 (r<=7/3), 4(5-3rho)/(8-3rho) (7/3..13/5), 1-6/(5rho) (13/5..3), 2/5 (r>=3).
  Duals (reduced mu=(mu1 on (c1+c5)/2, mu2 on (c2+c4)/2, mu3 on c3), lam1 on (a1-1/3), lam2 on (a2-2/3); LB = DP - eta/3(|lam1|+|lam2|)):
    A   : mu=(0,1/2,1/2), lam2=+rho/2  -> line (r-1)(2/3-eta/6) on L; (4-r)/3 - eta*rho/6 on 2<=r<=5/2
    band: mu=(1,0,0), lam1=-rho        -> rho(1-eta)/3, all r
    Lf  : mu=(0,1/2,1/2) -> rho/2 (L);  M1f: (0,(2-rho)/2,rho/2);  M23f: (t/rho,t/rho,rho/(8-3rho)), t=Tf;  M4Hf: (2/5,2/5,1/5)
  Full-lattice lift: mu_1=mu_5=mu1/2, mu_2=mu_4=mu2/2, mu_3=mu3; l_{k,tau} (tau=A+,A-) : L1=lam1/2, L5=-lam1/2, L2=lam2/2, L4=-lam2/2.
  Primal (orbit-symmetrised mixtures; orbit = {s, flip, rev, flip.rev}):
    L0 : 2/3 AbaBBb + 1/3 BaBbAb (r<=2, band 0)
    M0 : x AbaBBb + x BaAbBb + (2/3-x) AaBbBb + (1/3-x) BBaAbb, x=(rho-1)/(3(2-rho)) (2<=r<=5/2, band 0)
    H0 : 2/3 AaBbBb + 1/4 BBaAbb + 1/12 BbAaBb (r>=5/2, band 0)
    Lf : 1/2 BaBbAb + 1/2 AaBbBb (dev 1);  M1f: (2-rho)/2 BaBbAb + rho/2 AaBbBb (dev 1)
    M23f: (8-5rho)/(8-3rho) BaBbAb + (6rho-8)/(8-3rho) BaAbBb + 4(2-rho)/(8-3rho) AaBbBb (dev = eta_free)
    M4f: (1-8/(5rho)) BbAaBb + 4/(5rho) BaAbBb + 4/(5rho) AaBbBb (dev 1-6/(5rho));  Hf: 1/5 BbAaBb + 2/5 BaAbBb + 2/5 AaBbBb (dev 2/5)
- [open] L2' line on [7/3,13/5] (middle piece): exact per-r data in fitL2.py output; closed form not yet fitted.
  M1 middle line: rho(2-rho)/2 + (1-eta)(2-rho)^2/6, breakpoint eta1 = 2(rho-1)/(4-rho).
  M3 first breakpoint eta0 = 2(2r-5)/(r-1).
- [STOPPED by coordinator] before writing LeanPaperCTwoMag1122BaseV1.lean. Plan: see report.
- [correction] TestSt.lean had already FINISHED before the pkill (nothing was killed). Result: `decide` (maxRecDepth 4000)
  proves `stC ![0,1,2,3,2,3] 3 = st 1 1 1 0` and `mult sX 2 = 2`; the funext/fin_cases/simp variant fails (leftover
  goal at tau=3). Use decide for stC state lemmas. Wall 2:14, mostly import load.
- [lean] LeanPaperCTwoMag1122BaseV1.lean COMPILES (45s), all #print axioms standard: base_bl cost_coord rawC_L/M/H rawC_off3 value_le_flow value_ge cert6 mix_cost mix_band.
- [status 1] compiled: LeanPaperCTwoMag1122BaseV1 (cert6, value_ge, value_le_flow, mix_cost, mix_band, base_bl, rawC_L/M/H/off3).
  writing: LeanPaperCTwoMag1122CertV1 (8 certificates AL AM Band Lf M1f M23f M4f Hf, all verified exactly in Python;
  first compile: edge lemmas hit 200k heartbeats -> raising maxHeartbeats per edge lemma), then FlowV1 (18 sequences,
  8 flows verified exactly), then PriceV1 (V(0), V_free all ratios, price law, frontier on a<=2b, [13/5,3], a>=3b).
  Not blocking: L2' closed form only needed for the full eta-frontier on 2b<a<13b/5 (after price).
- [lean] LeanPaperCTwoMag1122CertV1.lean COMPILES (1:34), 0 errors; edge_*/cert_* for AL AM Band Lf M1f M23f M4f Hf standard axioms.
- [bg run] 2026-09-26 01:10:31 nohup: cd work/p13_conjectures && lake env lean -o .lake/build/lib/lean/LeanPaperCTwoMag1122FlowV1.olean LeanPaperCTwoMag1122FlowV1.lean ; log scratchpad/c1122/build_flow2.log (first try: flow_* theorems timed out at 200k heartbeats -> now maxHeartbeats 0 per flow theorem)
- [L2' FOUND, exact rational fit verified at 13 rational ratios in [7/3,13/5] (fitL2b.py)]
  rho=a/b-1. Middle line on 7/3<=r<=13/5:  D*V >= L2'(eta) = rho(2-rho)[2(rho+1) - eta(2-rho)] / (3(9rho-3rho^2-4))
  In (a,b): L2'(eta) = (a-b)(3b-a)(2a - eta(3b-a)) / (3(15ab - 3a^2 - 16b^2))   [denominator > 0 on the range]
  dual: mu_red = (2(rho-1)(2-rho), rho(2-rho), rho)/(9rho-3rho^2-4); lam2 (a2-upper) = rho(2-rho)^2/(9rho-3rho^2-4)
  (slope S = lam2/3). Not yet turned into a Lean certificate (quadratic/rational -> use cert6 with q=(15ab-3a^2-16b^2)-type scaling).
