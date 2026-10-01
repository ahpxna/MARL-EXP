# `paperA_certified_separation.json` — certified Gamma_true on the centred family (A-F1)

Recorded 2026-09-24. Resolves deviation A-6.

| item | value |
|---|---|
| producer | `scripts/EXP_paperA_certified_separation.py`, sha256 `4537a5d3d4657d57…` (recorded as `source_sha256`) |
| artifact | `research/unified_20260919/paperA_certified_separation.json`, sha256 `e53d7c69036a39f2…` |
| interpreter | `.venv/bin/python` (numpy, scipy 1.18.1: `linprog` HiGHS for the cutting-plane LP) |
| model | `thetaC` of `LeanPaperACentredV1`, `M = 1`, `r ∈ {1,2,4,8}`, centred class, closed alternatives |
| seeds | `default_rng(20260924)`, used only to sample worlds for the cover check |
| wall time | 24 s; 25 cutting-plane rounds per `r`; no region and no LP failed |
| self-checks | 6/6 |
| figure | `research/papers/_figures/paperA_certified.pdf` (`scripts/FIG_paperA_certified.py`, sha256 `3efb22bfb08c79ff…`, 3/3) |

**What is certified, and how.** Every number is exact rational.

- *Upper bound.* The dual `ν` of the LP over a finite set of alternatives gives
  `U = max_e Σ_l ν_l c_{e l} ≥ Γ_true`. Each alternative is checked exactly to lie in `Alt`,
  both the region inequalities and the two centring equalities.
- *Lower bound.* The design is the final LP design mixed with 0.1% uniform, so every
  `w_e > 0`. Each region's centred QP is bounded from below by the rational value of its
  Lagrangian dual at `μ ≥ 0` (weak duality), and `L` is the minimum over all
  `|B|(|B|−1)` regions.
- *Γ_proxy = 9/512.* This is the theorem `frozenGameC0_eq`, not a computation.

**Results, as ratios Γ_true / Γ_proxy.** r = 1: [0.83719, 0.83736]; r = 2: [0.72139, 0.72161];
r = 4: [0.56643, 0.56665]; r = 8: [0.39821, 0.39824]. All lie inside the proved bracket
`4/(4+2r) ≤ ratio ≤ 64/(9r)`. At the variance-proportional design the certified lower
value equals the theorem's `9/(128(4+2r))`, so that bound is tight at that design.

**Scope.** The panel covers r = 1, 2, 4, 8 at M = 1; the all-r statement is the theorem.
The older eight-cell separation JSON (`paperA_separation_games.json`) is a different family
and is not relabelled.
