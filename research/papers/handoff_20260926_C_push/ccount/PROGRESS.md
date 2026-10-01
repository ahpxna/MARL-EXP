# Paper C count reduction — progress

## Plan
Module A: LeanPaperCCountReductionV1.lean (ns CIGAMF.P13.PaperCCountReduction)
 - cstate ty S : CState d m (type counts of a subset); subCost (typedG) = typedCost ∘ cstate
 - symSub ty Q (average over WPerm (typeLabel ty)); marginal = type average; cost/counts unchanged
 - CountLayerFeasible (script's layer LP), countLayerValue; image sets equal -> layerValue = countLayerValue
 - realisation: Q ∈ SubFeasible k η -> ∃ P ∈ FeasibleAt id η, pushK P k = Q
   (P = Σ_S Q S · symLaw (tyS S) δ_{σ_S}); layerValue = trueValue {k}
Module B (maybe split): recourse count model; recourseSet = countRecourseSet.

## Algebra check (task 3)
 j ≤ k, k>0: q j/k - j/m = (j/k)(q-k/m)  -> |.| ≤ η/m
 j ≥ k, k<m: q + (1-q)(j-k)/(m-k) - j/m = (q-k/m)(m-j)/(m-k) -> |.| ≤ η/m   [verified by hand]

## Status
- 2026-09-26: scratch T3.lean (realisation part 1) COMPILES clean (1 unused-var warning), no sorry.
  Proved: band_low, band_high (algebra of task 3, both regimes incl. k=0,k=m edges), card_le_m, cardIdx,
  card_filter_lt, exists_prefix_perm, secPerm, secPerm_prefix, inTy, inTy_eq_zero, ty_act, prefixSet_mul,
  map_inTy, pointLaw(+_ranking,+_expect), uniLaw(+_ranking), uniLaw_prefix, sum_inPrefix_prefix,
  sum_inPrefix_all, mult_inTy_in, mult_inTy_out, uniLaw_marginal.
- STOPPED by coordinator before: realiseLaw + realise theorem (mixture Σ_S Q S·uniLaw S), layer_eq_single_budget,
  task 1 (cstate/symSub/CountLayerFeasible/layer_costs_eq), task 2 (count recourse set equality).
- No file written in work/p13_conjectures yet (nothing to clean up there).
