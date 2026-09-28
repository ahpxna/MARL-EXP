# Paper B fidelity audit (partial, 2026-09-26, read-only agent; not yet applied)

Answer to review point: visibility is only partly connected to the parity channel. Connected:
`par_vis_iff` on the channel's `maskR`; `parChan_chi_le` gives blind chi^2 = 0 and visible chi^2 <=
parC h^{2q}. Missing: `decision_order_visible` never instantiated on parity; its per-query lower
hypothesis `hlo` is proved for no divergence (only best-query Hellinger at the separating query,
`parity_hel_sep`). So Prop. dorder's D_h(w) ~ h^{2d(w)} on parity is NOT a Lean theorem.

Findings (tex = paper_b.tex, supp = paper_b_supplement.tex):
- B1 Thm attain tex:579-581: moment gaps are CERT, not Lean (`decision_moment_gap` is arithmetic;
  `identification_moment_gap` takes the gap as hypothesis). Tag \CERT or prove E[Y^2] of famLaw.
- B2 tex:771-778 "parity channel is of this kind": say visibility/cover/orders + blind chi^2=0 +
  visible upper bound are proved; per-query lower bound and parity instance not formalized (or prove).
- B3 sep numbering: tex:782 and supp:1312 say min(u,v)+1; Lean sepP=min(w+1,v+1) on 0-based = min(w,w')
  in paper numbering (as tex:499,527,775). Fix tex:782, supp:1312.
- B4 Thm upper tex:369-381: `tournament_law` needs kappa symmetric and t>0; display them.
- B5 Thm unif tex:597-599: `kl_uniform_over_queries` needs hkl, henv, hint and hmass (int(P-Q)=0);
  `chi2_uniform` bounds int(P-Q)^2/envLo; supp:476-477 says "two" hypotheses (three + mass). Display.
- B6 tex:608-611: `channel_kl_uniform` is about the constructed pair, not two parity worlds; cite
  `parChan_chi_le`/`parity_chiSq_le` for the channel's own bound.
- B7 stale supplement remarks contradicted by compiled modules: supp:302-306, 472-477, 610-615,
  632-643(iii), 802-806, 812-822, 855-862 (update: order = graded chi^2 upper + Hellinger lower, via
  `channel_sep_is_read_off`, `query_separates_iff`, `parity_gap_order`, `parChan_chi_le`,
  `parity_hel_sep`), 888-893, 928-932, 977 (one cell vs three cells at supp:1027), 1104-1108; and
  pointers needed at supp:224-228, 483-493, 620-624, 564-568.
- B8 bibitem wangyou2026 differs between tex:1091 and supp:1485 (same arXiv id) — one is wrong.
- B9 build record supp:1440-1457 omits gate coverage for many cited modules (ShareTournament,
  ChiStar, PrivateQuery, Visible, StoppedLaw, Family*).
- B10 composed claims without single declaration (safelaw formula, order general Theta,
  endpoint stopped-class c log(1/delta) conversion) — cosmetic.
Checked fine: safelaw iff, coSafe/id cases, lower, lowerstop, certchannel, chistar, hellupper,
sharedtests, privatequery, order, endpoint (finite), parlaw, vanish, paritymoment.
Not reached: famrates (r>0 vs paper r>=2; check famSafe_derived), tight family half, crossover,
headline, dorder, critical, sameorder, hitting, hittingembed, TipV1, FamilySafeV1, supplement envs.
Audit agent context intact (roster: a1b4a28f58cceafad).
