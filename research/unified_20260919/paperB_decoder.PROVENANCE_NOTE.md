# `paperB_decoder.json`, `paperB_decoder_grid_v2_20260923.json` — which decoder the counts measure

Recorded 2026-09-24. **The raw counts are valid and were not resampled.** This note fixes how
the identification counts may be described relative to the decoder proved correct in Lean.
It complements `paperB_decoder.SUPERSEDED_FIELDS.md`, which concerns the budget brackets.

## The difference

`scripts/EXP_paperB_decoder.py`, `id_decoder_wrong`:

    named = [j for j in range(1, m) if query_decides_named(...)]
    guess = named[0] if len(named) == 1 else (m if len(named) == 0 else -1)

A guess of `-1` (two or more tests fire) is always counted as an error.

The formalized decoder (`LeanPaperBParityDecoderV1.idCode`, via `decodeB`) returns the world
the outcome vector points to, and a DEFAULT world (world 1 in the script's 1-based indexing)
when two or more tests fire. On that ambiguous event the formalized decoder may be right; the
script's rule never is. Everywhere else the two rules coincide, test by test:

- the observation model, the feature `cos(Y)`/`sin(Y)` (`T0 = 1`, `SIGMA = 1`), and the
  per-query sample size match `parChan`, `feat`, `schedI`;
- the midpoint test `x < thr` (or `x > thr`) is the nearest-mean test `saysMinus`, strict on
  both sides, with ties falling to "not named"; the two candidate means differ for every
  `h > 0` used in the runs (`feature_gap_lower`);
- the safe decoder (`safe_decoder_unsafe`, `safeCode`) has no ambiguous branch; its rule is
  identical.

## What is proved about it

`LeanPaperBDecoderMatchV1` states the script's rule in Lean (`pyGuess`, `none` for `-1`) and
proves `lean_wrong_imp_py_wrong`: on every outcome vector and at every world, a wrong
formalized guess implies a wrong script guess. Hence, on the same samples, the formalized
decoder's error count is at most the recorded count.

## How the identification counts may be described

- As a **conservative upper bound** on the error of the decoder of `id_correct`, and hence as
  upper-certified achieved budgets for that decoder, in the sense of the existing
  Clopper–Pearson upper bounds.
- **Not** as a measurement of the formalized decoder's error. Lower confidence bounds on the
  recorded error (`cp_lower`) are lower bounds for the SCRIPT's rule only. They do not bound
  the formalized decoder's error from below, so "the first successful tested budget" brackets
  refer to the script's rule.

The safe-task counts measure the formalized safe decoder exactly.

## Addendum (2026-09-24, afternoon): the paired rerun with the formalized fallback (deviation B-1)

`scripts/EXP_paperB_decoder_leanfallback.py` (sha256 `e558349bfe65e939…`) is
`EXP_paperB_decoder.py` with one change: when two or more identification tests fire, the guess
is the default world 1, as in `decodeB`/`idCode`. It uses the same seed and the same order of
draws. Output: `paperB_decoder_leanfallback.json` (sha256 `20dda063c3d5d527…`), 10/10
self-checks, two of which are new and can fail:

- **Pairing**: the same 616 cells, and every one of the 308 safe counts equals the stored one
  exactly. So the draws are the stored run's draws, even though the current producer's bytes
  differ from the launch source (`bb8d6f14…` is in no commit).
- **`lean_wrong_imp_py_wrong` on data**: every identification count of the formalized decoder
  is at most the script's. The fallback removes 13,831 identification errors in total.

At the corrected family-wise level (per tail `0.05/(2·616)`, the level of the current
producer; see `SUPERSEDED_FIELDS.md`), the fallback moves NO certified budget. The old counts
and the new counts give the same smallest certified rung in every panel. So the certified
identification budgets ARE measurements of the formalized decoder. The lower (CP) brackets of
the new artifact refer to the formalized decoder; those drawn in `paperB_decoder.pdf` refer to
the script's rule and are the conservative side. The stored `paperB_decoder.json` is unchanged.
