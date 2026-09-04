# What to run, in order of value

Everything below runs from the repo root. Use your own interpreter; the code
needs **numpy** only, with **scipy** optional (it unlocks the LP lower-bound
route — without it those rows are written as `skipped`, never as failures).

```bash
cd ~/cig-amf-main
PY=.venv/bin/python3          # or: PY=python3
$PY -c "import numpy, sys; print(sys.version); import scipy; print('scipy ok')"
# if that fails:  $PY -m pip install numpy scipy pytest
$PY -m pytest tests/test_observatory.py -q        # 30 tests, ~1s
```

---

## 1. Rank-one ladder — the only run that can close the open hole today

This is the ledger's own kill gate for D6. Worlds are generated **rank-one by
construction** in four nested classes (pairwise, pure product, pairwise+product,
full multiaffine), and the doubled decision gap is compared against `m-1` in
exact rational arithmetic on normalized balanced cells.

```bash
$PY -m observatory.campaigns --which A --scale 20 --budget 5400 \
    --out research/observatory/campaigns
```

Roughly 90 minutes. Read the banner it prints:

- **`*** CONJECTURE KILLED ***`** — an exact rational violation exists. The
  witness world is saved verbatim in `summary_*.json`; it is immediately
  formalizable, and the rank-one sufficiency conjecture is dead.
- **no violation** — then `max_kappa_over_bound` is the number that matters. It
  is the strongest positive evidence the conjecture has, and the margin
  distribution is what a proof attempt needs in order to know where the binding
  cases are.

Both outcomes are publishable. That is why this one goes first.

## 2. Is the Structural headline exotic?

`chi_prefix = Theta(m)` is proved on a *constructed* staircase. Nobody has
measured chi off that family. If random supportOsc worlds are almost always
`chi = 1`, the paper has to say the staircase is a corner case; if chi grows
there too, the result is much stronger.

```bash
$PY -m observatory.campaigns --which B --scale 8 --budget 3600 \
    --out research/observatory/campaigns
```

About an hour. Look at `distribution` in the summary: the share of worlds with
`chi >= 2` and `chi >= 3`, per `m`.

## 3. The Support family-level law

Measures `Q*_eps`, the greedy size, the maximum edge size `r` and the classical
`ceil(2(n-1)/(r+1))` lower bound as the support family grows. This turns "a
family-level complexity law is missing" into a measured curve.

```bash
$PY -m observatory.campaigns --which C --scale 6 --budget 2400 \
    --out research/observatory/campaigns
```

## 4. Honest check on typed completion

If greedy tracks the optimum, minimum-cost typed completion is not
algorithmically interesting and should be demoted again. Built to be able to
say that.

```bash
$PY -m observatory.campaigns --which D --scale 10 --budget 900 \
    --out research/observatory/campaigns
```

---

## Broad sweep (background, if you want the wide store too)

```bash
$PY -m observatory.run --profile screening --out research/observatory
```

## Mining — run this after any of the above

```bash
$PY -m observatory.mine research/observatory research/observatory/campaigns \
    --out research/observatory/analysis --top 30
less research/observatory/analysis/REPORT.md
```

Mining is single-pass over the whole store and takes a few minutes per ~250k
rows. The sections to read, in order: **Violations**, **Sharpest instances**,
then **Candidate inequalities**.

---

## One-shot: everything, unattended

```bash
cd ~/cig-amf-main && PY=.venv/bin/python3
nohup sh -c "
  $PY -m observatory.campaigns --which ABCD --scale 12 --budget 3600 \
      --out research/observatory/campaigns &&
  $PY -m observatory.run --profile screening --out research/observatory &&
  $PY -m observatory.mine research/observatory research/observatory/campaigns \
      --out research/observatory/analysis --top 30
" > research/observatory/pipeline.log 2>&1 &
```

Expect four to six hours. When it finishes, `research/observatory/analysis/REPORT.md`
plus `campaigns/summary_*.json` are the two files worth reading.

## Notes

- `--scale` multiplies sample counts; `--budget` is a per-campaign wall-clock
  cap in seconds. A campaign stops cleanly at the cap and reports what it saw.
- Store size: roughly 110 MB per 250k rows. Delete old `obs_*.jsonl` freely —
  every file is self-describing and independent.
- Nothing here writes to `research_chains/` or `scripts/`; the historical labs
  and their provenance are untouched.
