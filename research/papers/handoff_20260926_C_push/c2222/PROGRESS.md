# c2222 progress (counts (2,2,2,2) two-magnitude frontier)
- [ ] discovery LP (python)
- [ ] regions + exact breakpoints
- [ ] exact certificates (Fraction)
- [ ] Lean modules

## Discovery results (floating, b=1, r=a/b, W = V*D, D=4(a+b))
- V0*D: 3(a-b)/4 (r<=2); (5b-a)/4 (2<=r<=7/3); (a-b)/2 (r>=7/3)
- Vfree*D: 2(a-b)/3 (r<=2); 2b(3b-a)/(5b-a) (2<=r<=5-2sqrt2); 2ab(3b-a)... i.e. 2r(3-r)/(17-5r) (5-2sqrt2<=r<=17/7); 4b/7 (17/7<=r<=3); 2(a-b)/7 (r>=3)
- price max (1+sqrt2)/2 at r=5-2sqrt2 (irrational breakpoint!)
- duals: L2 mu=(0,1/8,1/4,1/4,1/4,1/8,0) + band at layers 2,6; F1 mu=(b,3b-a,b)/(5b-a) on k=3,4,5; F2 mu=(3b-a,3b-a,b,3b-a,b,3b-a,3b-a)/(17b-5a); uniform mu for 4/7 and r>=3; mu=1/3 on 3,4,5 for r<=2
- coordinator: priority (1) exact price law eta=0 & free, all ratios; (2) full eta frontier
- Hand-designed flows (b=1,u=r-1,d=3-r): see flowsdesign in notes below
  V0: I (1,2] 7-orbit const; II [2,7/3] Pa,Pg,Ph,Pf' alpha=(r-1)/(8(3-r)), Z,P1 pi=(7-3r)/(4(3-r)); [7/3,inf) Pd,T2,Pe,Pi 1/4 each
  Vf: I 3 paths 1/3; [2,rA] P1 1/2, Pc (r-1)/(2(5-r)), P3 (3-r)/(5-r); [rA,17/7] 8 paths; [17/7,3] 9 paths; [3,inf) 5 paths
- Certs: L1 generic; L2/L2' mu=(0,1/8,1/4,1/4,1/4,1/8,0) band lam(#A2-1)-lam(#A6-3), lam=(a-b)/8; free certs F1,F2,U valid on all [2,3]
- Vfree on [2,3] = max(F1,F2,4b/7) (all three certs valid on [2,3])

## STATUS at coordinator STOP (2026-09-26)
- NO Lean module written yet (nothing to compile; no repo files touched).
- Scripts (scratch): lp.py (81-state flow LP, HiGHS), t2/t3 (scans), fit.py (exact rational fit),
  paths.py (flip-symmetric path-orbit LP), ilp.py (constant-weight interval LP), dp.py (exact Fraction DP
  for lower certs), sym.py (homogeneous poly helper for Lean certificate generation), flows.py.
- Exact formulas found (b=1, r=a/b, W=V*D, D=4(a+b)); breakpoints exact:
  eta-frontier pieces: L1=(r-1)(1-eta)/2 [all r]; L2'=(r-1)(3/4-eta/8) [r<=2]; L2=(5-r)/4-(r-1)eta/8 [2<=r<=~2.52];
  L3 slope -(3-r)^2/(2(10-3r)) [2<=r<=17/7?], intercept NOT yet exact; flat pieces = Vfree.
  r-regions: (1,2] ; [2,5-2sqrt2] ; [5-2sqrt2,7/3] ; [7/3,17/7] ; [17/7,53/21] ; [53/21,3] ; [3,inf).
  r>=3: W=(r-1)max((1-eta)/2,2/7). r<=2: W=(r-1)max(3/4-eta/8,2/3). [53/21,3]: max(L1,4/7).
- Path names (type seqs 0=A+,1=A-,2=B+,3=B-) & cost vectors in (u=r-1,d=3-r) valid on (2,3):
  P1=A+A-B+B-B+B-A+A-(u,0,d,0,d,0,u) Pa=A+A-B+B-B+A-A+B-(u,0,d,0,d,u,0) Pb=B+A-A+B-B+B-A+A-(0,u,d,0,d,0,u)
  Pc=B+A-A+B-B+A-A+B-(0,u,d,0,d,u,0) P3=B-A+B-A-A+B+A-B+(0,u,0,2,0,u,0) Z=B+B+A-A+A-A+B-B-(0,2,0,2,0,2,0)
  Pd=A+A-B+A-A+B-B+B-(u,0,d,u,d,0,0) Pe=B+B-B+A-A+B-A+A-(0,0,d,u,d,0,u) Pf=B+B-B+A-A+A-A+B-(0,0,d,u,d,u,0)
  Pg=B+A-A+A-A+B-B+B-(0,u,d,u,d,0,0) Ph=A+B-A-B+B+B-A+A-(u,u,d,0,d,0,u) Pf'=B+B-B+A-A+A-B-A+(0,0,d,u,d,u,u)
  Pj=A+A-B+B-A+A-B+B-(u,0,d,0,2,0,0) Pk=B+B-A+A-B+B-A+A-(0,0,2,0,d,0,u) T2=A+B-A-B+B+A-A+B-(u,u,d,0,d,u,0)
  Pi=B+A-A+B-B+A-B-A+(0,u,d,0,d,u,u)
- Flows (weights): F1 [2,rA]: P1 1/2, Pc (r-1)/(2(5-r)), P3 (3-r)/(5-r).
  F2 [rA,17/7]: Pa,Pb x=(11r^2-46r+51)/(2(r-1)(17-5r)); Pd,Pe,Pf,Pg sigma/2, sigma=-(r^2-10r+17)/((r-1)(17-5r)); P3,P1 z=(17-7r)/(17-5r).
  4/7 [17/7,3]: Pa,Pb,Pd,Pe (3-r)/(2(r-1)); Pf,Pg (7r-17)/(14(r-1)); Pj,Pk (7r-17)/(7(r-1)); Pc 2/(7(r-1)).
  V0 II [2,7/3]: Pa,Pg,Ph,Pf' (r-1)/(8(3-r)); Z,P1 (7-3r)/(4(3-r)) (+flips for eta=0 band).
  V0 [7/3,inf): Pd,T2,Pe,Pi 1/4 each (+flips). Vf I: 3 paths 1/3 (see notes); Vf IV: 5 paths (2/7,2/7,1/7,1/7,1/7).
  V0 I: 7-orbit constant flow from ilp.py.
- NEXT: exact Fraction verification of every flow/cert (dp.py + sym.py), then Lean modules:
  Base (defs, baselines per region, glue value>=cert via typed_flow_equivalence+cert_lower, value<=mixFlow),
  then V0 law, then Vfree law, then eta-frontier (L3 intercept + breakpoint flows still to derive).

## 2026-09-26 resumed
- Coordinator split: ANOTHER agent writes V_free in LeanPaperCTwoMag2222FreeV1.lean (do not edit). I do Base, V(0), price law, eta-frontier.
- EXACT (Fraction, symbolic) verification done via gen.py/t12.py: certs L1 (lo/mid/hi), L2' lo, L2 mid [2,3], 345 lo, U mid, U hi, F1 mid [2,3], F2 mid [2,3] -- all edge inequalities hold on the whole region; Phi' values:
  L1 (a-b)/2, sum|ell'|=4(a-b); L2' 3(a-b)/4, sum|ell'|=a-b; L2 (5b-a)/4, sum|ell'|=a-b; 345 2(a-b)/3; U mid 4b/7; U hi 2(a-b)/7;
  F1 Phi'=2b(3b-a) with Z=5b-a; F2 Phi'=2a(3b-a) with Z=17b-5a.
- LeanPaperCTwoMag2222BaseV1.lean COMPILED (olean built), axioms clean [propext, Classical.choice, Quot.sound]. API (namespace CIGAMF.P13.PaperCTwoMag2222):
  ty8 = ![0,0,1,1,2,2,3,3]; wt a b = ![a,-a,b,-b]; g8 a b = typedG ty8 (wt a b); K7 = {1..7}; K7_ne; mult_ty8; g8_eq; normMass_g8
  base0/2/4/6 (=0), base1/base7 (=b), base3_lo/base5_lo (a<=2b: 2b-a), base3_mid/base5_mid (2b<=a<=3b: a-2b), base3_hi/base5_hi (3b<=a: b)
  sN a b v0 v1 v2 v3 = a(v0-v1)+b(v2-v3); sgHi/sgLo sign functions; abs_sN_hi (2b<=a), abs_sN_lo (b<a<=2b): |sN| = sg * sN on the box
  value_ge_of_flows, value_le_of_flow (glue through typed_flow_equivalence)
  nodeN, EdgeOK, cert8: (phi 0 0 0 0 - eta/8 * sum_{k<8} sum_tau |ell k tau|)/(Z*(4(a+b))) <= trueValue (g8 a b) eta K7 K7_ne
     given mu>=0, mu 0 = 0, mu1+..+mu7 = Z, hbeta (only where mu k != 0), EdgeOK, phi 2 2 2 2 = 0
  rc a b s k = |sN (stC s k ...)| - trueBaseline (g8 a b) k; value_le_mixQ (weights n j / Q, band in cleared form); value_le_mixQ_free (eta = 8, no band needed)

## HANDOVER (coordinator STOP, 2026-09-26 ~01:15)
- No background runs active. (Future rule: runs > 2 min must be nohup-detached, logged here.)
- LeanPaperCTwoMag2222BaseV1.lean: COMPILED, olean built (00:59), 0 errors, axioms clean. (compile ~55-90 s wall)
- LeanPaperCTwoMag2222CertV1.lean: COMPILED, olean built (01:10), 0 errors, axioms clean. Compile 5m49s wall (1301 s CPU).
  Generated by mkcertmod.py (uses gen.py/sym.py/mkcert.py). Headlines:
   lower_L1 (hb : 0<b) (hab : b<a) (η) (hη : 0≤η) : (a-b)*(1-η)/2/(4*(a+b)) ≤ trueValue (g8 a b) η K7 K7_ne
   lower_L2lo (hb) (hab) (h2 : a ≤ 2*b) η hη : (3*(a-b)/4 - η*(a-b)/8)/(4*(a+b)) ≤ trueValue ...
   lower_L2mid (hb) (h2 : 2*b ≤ a) (h3 : a ≤ 3*b) η hη : ((5*b-a)/4 - η*(a-b)/8)/(4*(a+b)) ≤ trueValue ...
   also βlo_eq/βmid_eq/βhi_eq, base8, μL1/ℓL1/φL1, μL2/ℓL2/φL2lo/φL2mid, edge_* lemmas.
  Pitfall fixed: a single 216-case EdgeOK proof exceeds maxHeartbeats 200000 -> split into 4 direction lemmas
  (edge_X_0..3, 54 cases each) with `set_option maxHeartbeats 2000000 in`; combine lemma edge_X.
  Pitfall: simp normal form |b - a| (not |a - b|) -> give both abs_of_pos (sub_pos.mpr hab) and abs_of_neg (sub_neg.mpr hab).
- NOT DONE: ZeroV1 (V(0) flows + headline), price law, eta-frontier.
