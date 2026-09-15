# B3 strict-Top-C gate — runbook (2026-09-04)

## Why this run exists

`B3fiber_rankone_m6_corner0_KILLED.json` is an exact rational counterexample to

    AllCoordinatesInteractionContrastRankOne(q, F)  =>  2D <= (m-1) delta_square

at m=6, K=3, corner reference.  Independently rechecked with
`scripts/run_d6_rankone_falsification.evaluate_candidate`: rank-one at every
coordinate, delta_square = 74893163/443037408 > 0, 2D = 428014165/443037408,
(m-1)delta = 374465815/443037408, ratio = 85602833/74893163 ~ 1.1430.

BUT the six coordinate scores are all exactly 13/37.  Top-C selects nothing on
its own; the set [0,1,2] comes from the index-order tie-break inside
`evaluate_candidate`.  Enumerating all 20 admissible tie-breaks (see
`...KILLED.tiebreak_analysis.json`): **1 of 20 violates**, the other 19 give a
doubled gap of 0.6418 or less.  So the kill lands on the NON-STRICT form of the
claim, i.e. on the tie-break convention, not on the geometry.

`StrictTopC` (`LeanD6ContrastRankPhaseDefinitionsV2`) requires every selected
coordinate to have strictly larger response oscillation than every unselected
one.  This witness fails it.  The strict form of the claim is therefore still
open, and these runs decide it.

## The gate

`--min-topc-margin X` requires

    (min selected score - max unselected score) / delta_square  >=  X

Below that the world is reported UNDEFINED — never a violation.  The threshold
is relative to `delta_square` because the whole objective is scale invariant.

The gate acts in TWO places, and both matter:
1. the float objective (all optimizers: Nelder-Mead, Powell, DE, LP), so the
   search stops steering toward ties;
2. the exact leg, where a lead whose rational snap lands back on a tie is
   marked `SKIPPED_NON_STRICT_TOPC` and can never be reported as a kill.

**Read `best_exact_ratio_admissible`, NOT `best_exact_ratio`, when the gate is
on.**  `best_exact_ratio` still reports the unrestricted maximum over leads,
including ones the gate rejected.  `gate_note` in every artifact says this.

Observed at m=6 corner 0 with `--min-topc-margin 1e-3`: float reached 1.1975 and
the ungated exact best was 6/5, but that lead snapped onto a tie and was
correctly skipped; the best ADMISSIBLE strict ratio was ~0.799.  A threshold of
1e-3 is too small to survive rationalization — sweep upward.

## Commands

Margin sweep at the corner that killed the non-strict form (decisive):

    for MARGIN in 0.01 0.03 0.05 0.1 0.2; do
      python3 scripts/run_d6_direct_rankone_linear_fiber_search.py \
        --m 6 --alphabet 3 --reference corners --corner-range 0:1 \
        --corner-fibers 24 --corner-starts 2 --corner-exact-leads 8 \
        --corner-maxiter 1200 --optimizer both+lp \
        --min-topc-margin $MARGIN --denominator-ladder 4 --snap both \
        --seed 20260904 \
        --out research/d6_contrast_rank_falsification/B3strict_m6_c0_margin$MARGIN.json
    done

Same at m=4 (cheap, and m=4 is where the tied extremum sat exactly at ratio 1):

    for MARGIN in 0.01 0.03 0.05 0.1 0.2; do
      python3 scripts/run_d6_direct_rankone_linear_fiber_search.py \
        --m 4 --alphabet 3 --reference corners --corner-range 0:1 \
        --corner-fibers 32 --corner-starts 3 --corner-exact-leads 8 \
        --corner-maxiter 1500 --optimizer de+both+lp \
        --min-topc-margin $MARGIN --denominator-ladder 4 --snap both \
        --seed 20260904 \
        --out research/d6_contrast_rank_falsification/B3strict_m4_c0_margin$MARGIN.json
    done

Read the outcome:

    python3 - <<'PY'
    import json, glob
    from fractions import Fraction
    for f in sorted(glob.glob('research/d6_contrast_rank_falsification/B3strict_*.json')):
        if f.endswith('.manifest.json'): continue
        d = json.load(open(f))
        adm = d.get('best_exact_ratio_admissible')
        print(f"{f.split('/')[-1]:42s} status={d['status']:36s} "
              f"margin={d.get('min_topc_margin')} "
              f"admissible={adm} "
              f"({float(Fraction(adm)):.6f})" if adm else
              f"{f.split('/')[-1]:42s} status={d['status']} admissible=None")
    PY

## How to read the result

- `status == "KILLED"` with the gate on  =>  a STRICT counterexample.  The
  rank-one law is dead in its strict form.  Formalize the exact witness in Lean
  as `exists F, AllCoordinatesRankOne F /\ 2D > (m-1) delta_square`; the witness
  world, the reference and the full exact certificate are in `counterexample`.
- `best_exact_ratio_admissible` stays below 1 across every margin  =>  the
  strict form survives, and the correct statement of the theorem carries a
  StrictTopC hypothesis.  The existing m=6 artifact then becomes the evidence
  that the non-strict statement is FALSE, which is itself a result: it says the
  hypothesis cannot be dropped.
- `best_exact_ratio_admissible` rising toward 1 as the margin shrinks, without
  ever exceeding it, is the sharpness picture already seen at m=4 (strict best
  0.999982 at margin 1.5e-6; tied extremum exactly 1, with 2D = 9/7 = 3*(3/7)).

Nothing here is a proof either way.  The lambda sweep is a finite seeded sample
of a continuum and every per-fiber ratio is a lower bound.
