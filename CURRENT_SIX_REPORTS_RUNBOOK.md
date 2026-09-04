# Current Six-Report Validation Runbook (2026-09-03)

This is the current development entry point for the six CIG-AMF reports.  It
supersedes historical two-paper / unrestricted-D6 runners for current claim
validation.

## Scientific state encoded by the runner

1. **MASTER** — Active Certificate Acquisition / Reference → Support → Decision.
2. **FUNCTIONAL** — certificate acquisition, lifetime, and selective refresh.
3. **SUPPORT** — active decision-critical joint-support discovery.
4. **STRUCTURAL** — K-Prefix / Prefix-Cover menu complexity; exact finite
   staircase discovery is tested directly.
5. **D6** — the unrestricted normalized `m-1` law is historical/falsified.
   Current live target is the *rank-one restricted* replacement conjecture,
   which is adversarially falsified rather than assumed true.
6. **QUERY** — semantic query transfer + identifiability/abstention.

Scientific counterexamples are findings, not test-runner errors.  Hard gates
cover implementation/theorem-sanity contracts such as false-safe counts,
rank-one construction validity, exact DP/MILP agreement, and typed status
contracts.

## One-command validation

Quick development validation (source compile + full pytest + all six report
jobs):

```bash
python scripts/run_current_six_report_validation.py \
  --profile quick \
  --out-root research/current_six_reports_validation_quick
```

Larger local screening:

```bash
python scripts/run_current_six_report_validation.py \
  --profile screening \
  --out-root research/current_six_reports_validation_screening
```

The command exits non-zero if source compilation, pytest, orchestration, or a
hard scientific sanity gate fails.

## Individual high-information targets

### Structural: exact staircase law discovery

```bash
python -m scripts.run_structural_staircase_exact_lab \
  --r-values 1 2 3 4 5 6 \
  --out research/current_six_reports_targeted/structural_staircase_exact_r1_6.json
```

This is exact finite computation.  Observing `chi(F_r)=r` on tested `r` is
proof-discovery evidence for the next Lean upper construction, **not** a
parametric proof.

### D6: adversarial rank-one falsification

```bash
python -m scripts.run_d6_contrast_rank_falsification \
  --instances 900 \
  --m-values 4 6 \
  --actions 3 \
  --b2-adv-restarts 4 \
  --b2-adv-steps 250 \
  --b3-restarts 4 \
  --b3-steps 180 \
  --out research/current_six_reports_targeted/d6_contrast_rank_screening.json
```

The generated B1, single-product, and full-multiaffine classes are rank-one by
construction.  B2-adversarial remains inside the scalar-latent multiaffine
class.  B3 is a direct full-table heuristic with a numerical rank-one
post-check.  Any `2D > (m-1) delta_square` candidate must be exact/rationalized
and then formalized; survival is never promoted to proof.

## What this local suite does NOT fake

The test plan (`config/CURRENT_SIX_REPORT_TEST_PLAN.json`) records open
external/confirmatory obligations.  In particular, local synthetic success is
not substituted for:

- disjoint-seed Functional confirmatory runs;
- learned-policy drift validation;
- external calibrated MASTER intervals and real acquisition costs;
- a real pre-execution joint-feasibility oracle for Support;
- external real-method Query transfer providers;
- exact formal closure of any still-conjectural D6 or Structural parametric
  statement.

These remain fail-closed until the corresponding capability/data is actually
available.

## Historical warning

Do not use historical `D6.S2`, half-factor optimizer, or unrestricted
normalized `m-1` runners as evidence for the current D6 theorem.  The general
law is falsified, including under a strict Top-C ternary witness.  Historical
registry entries are retained only for provenance and are marked accordingly.
