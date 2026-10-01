# P1 (D6 revision frontier) — handoff, 2026-09-27

Owner until now: subagent aa10ead. Stopped on the coordinator's wrap-up order.
No Lean file was created by me. No background process is running.

## 1. Files I created (all new, nothing edited or overwritten)

All under `research/marl_budget/P1_d6_frontier/`.

| file | sha256 | status |
|---|---|---|
| `COMPACT.md` | 25c3047a…d8a5 | step-0 summary of my old context |
| `PROGRESS.md` | 6e9c7036…e7ee | running log |
| `d6_frontier_exact.py` | 8ee52bad…0cad | producer of step 1; ran; this sha equals `producer_sha256` in its JSON |
| `d6_frontier_exact.json` | d33f1246…a40a | step-1 artifact (below) |
| `d6_frontier_exact.log` | e7a472bd…afefa | stdout of that run |
| `nesting_degree_comb.py` | 0f4e4c6d…f0 | exact combinatorics producer; ran for (6,1), (7,1), (7,2), (8,2) |
| `nesting_degree_m6_R1.json` | 74d88b25…dc09 | 0/225 systems not 1-coverable |
| `nesting_degree_m7_R1.json` | 1428077e…56bb7 | 519/15435 not 1-coverable; 10 examples |
| `nesting_degree_m7_R2.json` | b5709b89…b916db0 | 0/35 not 2-coverable |
| `nesting_degree_m8_R2.json` | 56977d42…73699a | 0/3136 not 2-coverable |
| `d6_nesting_search.py` | 56b0eaf2…375a | WRITTEN, NEVER RUN (m = 7 hill-climb); see §4 |
| `__pycache__/` | — | created by a scratch import of `d6_frontier_exact.py`; harmless; archive rather than delete |

Scratch only (session scratchpad, not in the repo): `scratchpad/p1/comb.py` and `comb_brute.py`, the
first two implementations of the combinatorial check. `comb_brute.py` enumerates all m! rankings
with no symmetry reduction; it confirmed m = 5: 0/100 and m = 6: 0/4500. `arb_pair.py` is the
arbitrary-(S,T) check of the surplus bound. Copy them into the repo if you want them archived.

## 2. Artifacts and what they show

### `d6_frontier_exact.json` (EXACT, Fraction arithmetic; 1702 self-checks, all pass)

Transcription of the Lean definitions:
- `productResponse` / `productExpectation` / `jointWeight` (LeanProductMixedDifferenceV4);
- `retainedResidual` (LeanD6H3Exchange);
- `productCompressionLoss` = osc(residual)/2 (LeanProductMixedDifferenceV4, LeanSupportGeometryV4.osc);
- `mixedDifference` (LeanProductSurrogateV4); δ□ = its max absolute value;
- score = osc(productResponse j);
- Top-k = `IsTopKByScore` (LeanSupportGeometryV4).

The reference is the corner reference `cornerQ2` (LeanD6BinaryBridgeV1). `Ib` and `Db` are parsed
from `LeanD6SharpnessM6V1.lean`, not retyped. The JSON records the sha256 of the 10 Lean sources.

The self-checks can fail, and the script refuses to write if any does. They are:
- δ□ = 2s+2, 2D = 12s, spans (2s±1), unique Top-3 = {0,4,5}, margin 2;
- the residual extremes, the attained mixed difference, and 2D/δ□ = 6s/(s+1);
- `pair_loss_le_sdiff_card` and the `…_sub_score_surplus` bound on every (Top-k, competitor) pair;
- monotonicity of F and G, and F_k(min(k, 6−k)) = 0.

Result for s ∈ {1, 2, 6, 20, 100}:
- 2ℓ_S = s(8 + 4|S∩{0,4,5}| − 2|S|) + |S|. The loss is exactly MODULAR in S.
- F_k(R) = (d_k − R)_+ · 2s with d_k = min(k, 6−k), for every tie-broken Top-k prefix.
- δ□ = 2s+2, so F_k(R) = (d_k − R)_+ δ□ · s/(s+1). This is strictly decreasing, with R* = 3 at k = 3.
- ℓ*_k is attained by the {1,2,3}-first sets.
- G(R) = 0 for R = 0..3 at every s. The ranking [1,2,3,0,4,5], the reverse of the score order, is
  optimal at every budget.
- So on Vb the price is the price of the first-order SCORE priority, not of nesting.

### `nesting_degree_m*_R*.json` (EXACT enumeration; not a proof)

- A system is one set O_k per budget. It is R-coverable if some chain C_1 ⊂ … ⊂ C_{m−1} has
  |C_k \ O_k| ≤ R at every k.
- m ≤ 6, R = 1: every system is coverable. So G(1) = 0 for EVERY set loss at m ≤ 6 (a
  loss-independent degeneracy).
- m = 7, R = 1: 519 of 15435 systems are not coverable (with O_3 fixed to {0,1,2}).
  - The scratch example, used in `d6_nesting_search.py`: O_2 = {0,1}, O_3 = {4,5,6},
    O_4 = {0,1,2,3}, O_5 = {0,1,2,3,4}.
  - The JSON lists 10 examples in the fixed-O_3 = {0,1,2} normal form.
- R = 2: m = 7 and m = 8 are always coverable, so R* ≥ 3 needs m ≥ 9. m = 9 is NOT run.

## 3. Background processes

None.

## 4. Unfinished items: exact next steps

1. **LeanMarlNestingDegreeV1.lean (not started).**
   - m = 7 witness first. Define the four sets as `Finset (Fin 7)`.
   - Theorem: ¬∃ chain C_2 ⊂ C_3 ⊂ C_4 ⊂ C_5 (|C_k| = k) with |C_k \ O_k| ≤ 1 for all four.
   - A cheap kernel route: enumerate chains as rankings restricted to their first 5 entries,
     `Fin 7` injections. Alternatively enumerate C_5 (21 sets), then its subsets.
   - There are 21 · 5 · 4 · 3 = 1260 chains of sizes 2..5: C_5 has 21 choices, then C_4 ⊂ C_5,
     C_3 ⊂ C_4 and C_2 ⊂ C_3.
   - `decide` over `Finset (Fin 7)` membership is fine at that size. Avoid `Finset.univ` of
     `Finset (Fin 7)` (128 sets) under `decide` unless tested.
   - Then m = 6: "every system (O_2, O_3, O_4) has a chain within 1". 4500 systems × chain search
     is heavy for the kernel. Reduce by symmetry (fix O_3 = {0,1,2}: 225 systems), prove a
     relabelling lemma, or use the structural argument:
     - choose C_3 within 1 of O_3 meeting O_2 and O_4 suitably;
     - binding levels are only k = 2, 3, 4, since k = 1 and k = 5 never bind at R = 1.
2. **m = 9, R = 2 enumeration (not run).** Run
   `python3 -u research/marl_budget/P1_d6_frontier/nesting_degree_comb.py 9 2 > …/nesting_degree_m9_R2.log`
   in the background. It covers 84·126·84 = 889,056 systems, prints progress every 100k, and
   writes `nesting_degree_m9_R2.json`. Estimate: minutes to about an hour. It refuses to
   overwrite.
3. **m = 7 D6-world hill-climb (`d6_nesting_search.py`, written, never run).**
   - Part A repeats the small combinatorics. Part B hill-climbs integer worlds F on {0,1}^7
     (corner reference) to make an uncoverable system (from part A's examples) the UNIQUE
     optima at k = 2..5 with positive margin. Every hit is re-evaluated exactly: 2G(R) by prefix
     DP, δ□, and the score frontier.
   - Smoke first: `P1_SEEDS=1 P1_STEPS=200 P1_OUT=<scratch>.json python3 -u d6_nesting_search.py`.
     The default output path refuses to overwrite.
   - Caveats:
     - the margin objective may plateau at a negative value; if so, vary the bound, the
       target system and the step sizes before calling it structural;
     - `search` breaks only on `t % 50 == 0` after success, which is intended;
     - part B uses only the first 5 examples of m = 7.
4. **LeanMarlRevisionFamilyM6V1.lean (not started).** On Vb s, s ≥ 1, prove:
   - the doubled losses 2ℓ_S = s·A_S + B_S for the 20 3-sets (A_S = 2 + 4|S∩{0,4,5}|,
     B_S = 3), and for the prefix sets of [1,2,3,0,4,5] at every k;
   - then (a) F_3(R) = (3−R)·2s for R = 0..3, and (b) the reverse ranking is optimal at every k.
   Route, as in `LeanD6SharpnessM6V1`:
   - integer residual tables respI/respD and fixed extremal points per set;
   - `affine_le` with two `decide` facts per extreme;
   - the bridge to the real `productCompressionLoss` via `cornerQ2_response` and an
     osc-of-extremes lemma. `osc_of_extremes` is private in the M6 bridge, so re-prove it.
   Extremal points are s-independent for s ≥ 1 because the losses are affine at the 5 sampled
   s. The JSON only shows affinity at those points, so `decide` must confirm it.
5. **LeanMarlScorePriceV1.lean (M1, not started).**
   - (a) All-cuts zero price: if every consecutive score gap is ≥ 2δ, then at every k the
     prefix is `IsTopKByScore` with margin ≥ 2δ, so `margin_two_sufficient` applies. Or use
     main's `exchange_general`: surplus ≥ |P\T|·2δ.
   - (b) ℓ_P − ℓ_T ≤ |P\T|·δ ≤ min(k, m−k)·δ from `pair_loss_le_sdiff_card`, plus
     |P\T| ≤ min(k, m−k).
   - Satisfiability witness: use `cornerQ2` and Vb, or main's `hypotheses_satisfiable`.
   - `I n` in `margin_two_sufficient` comes from D6Threshold; I did not read its definition.

## 5. Open questions

- The step-1 Vb result: is the MARL paper's claim "price of first-order-score nesting" (sharp
  frontier, Vb) or "price of nesting" (needs m ≥ 7, and a D6 world realizing an uncoverable
  system is not yet found)?
- Can D6 losses (osc-of-residual form) realise every set system, or only a restricted class?
  If restricted, the m = 7 combinatorial witnesses may not transfer to D6 worlds.
- My read of the D6 counterexample modules (BalancedLaw, StrictMarginTernary, BinaryInteger,
  NormalizedBalancedTernary) was DENIED by the permission classifier. Those witnesses are not
  computed, and I did not work around the denial. The user must decide.
- The (1,1,2,2) Paper C audit from my old context has its three minor findings in COMPACT.md;
  none is fixed (I do not edit .tex).
