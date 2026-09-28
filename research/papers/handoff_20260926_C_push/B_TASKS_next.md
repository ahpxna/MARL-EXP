# Paper B — open math, ready to assign (compiled 2026-09-26 after a full read + audit)

State: manuscripts fixed and recompiled (paper_b 11 pp, supplement 15 pp); 616/616 citations
resolve to gated source (40 modules full7, 11 in smokeR2/UP1/UP2/UP4). Fixes applied: B1 attain
(tail gap -> `identification_moment_gap_computed`, decision 2nd moment marked CERT), B2 parity
per-world instance marked not formalized, B3 sep numbering, B4 kappa symmetric + t>0, B5 KL
conditions displayed, B6 channel's own bound cited, B7 eleven stale NOTEPARs given status lines,
B8 wangyou2026 bibitem (verified on arXiv: Q. Wang, W. You), B9 build record rewritten.

## Tasks (in order of value / tractability)
T1 (medium, high value) Parity per-world law, formal. Prove a per-query chi^2 LOWER bound on the
   parity channel for EVERY visible query (query j sees pair (w,w') iff j names one of them):
   chi^2_j(w,w') >= c h^{2j}. Route: characteristic-function gap at query j (as in
   `parity_gap_order`, `parity_hel_sep`) -> feature gap -> TV -> H^2 -> chi^2 >= H^2. Then
   instantiate `decision_order_visible` (LeanPaperBVisibleV1) with kappa = chi^2 using
   `parChan_chi_le` (upper, blind = 0) -> Prop. dorder's D_h(w) ~ h^{2d(w)} on parity, and remove
   the "not formalized" sentence (paper_b.tex, two-layer section, and Limitation 5).
T4 (easy-medium) Decision probe second moment on the latent family: E[Y^2] = 18+sigma^2+6uh+h^2
   for famLaw (currently hand-computed, CERT) -> Lean; then Thm attain is fully PROVED.
T5 (easy) One declaration: chi^2(P,Q) <= bound from `chi2_uniform` via `worldQ_floor` monotonicity.
T7 (easy) Thm endpoint stopped class: the conversion of the level-2delta lower bounds to
   c log(1/delta) with explicit c, delta0 (currently arithmetic in prose).
T8 (easy) Thm order general Theta as one declaration (compose `graded_lower_chi`,
   `hellinger_upper_star`, `resolved_le_scale`) for fixed |W| under kappa <= K kappa_H.
T2 (hard) Parity critical constants: KL_j(h)/h^{2j} -> c_j = (1/2) int a_j^2/p0, with
   p+ - p- = h^j a_j + O(h^{j+1}) (Taylor remainder, dominated convergence, KL ~ chi^2/2),
   then G* = c_w (w <= m-1), c_{m-1} (w = m) via `critical_limit`/`expansion_hyps`.
   Numerical c_j: research/unified_20260919/paperB_parity_constants.json.
T3 (hard) Latent family critical constants (not computed at all yet): numerics first, then as T2.
T6 (hard, optional) Crossover g_eta: leading-order expansion and a two-sided bound on the
   information over the degree-capped class (paper says not proved; moments/cross term/shape are).

Checked fine (no change needed): safelaw, lower, lowerstop, certchannel, chistar, hellupper,
sharedtests, privatequery, order, endpoint (finite), parlaw, vanish, paritymoment, critical,
sameorder, dorder (general), hitting, hittingembed; famrates (Lean needs r>0, paper r>=2: fine).
