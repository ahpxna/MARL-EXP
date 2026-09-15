# Line-by-line code audit, 12 September 2026

Scope of the corpus, measured rather than assumed:
scripts/*.py 169 files / 37,627 lines; research_chains/ 32 files / ~5,600 lines;
*.lean outside mathlib 445 files / 69,626 lines; research/**/*.json 1,620 files / 236 MB.
Reading order is by evidence load, not alphabetical.

---

## [1/N] scripts/run_functional_variance_stopping_lab_v4.py -- 583 lines, READ IN FULL

Produces the Functional evidence now in play. Findings, most serious first.

### F1. The script on disk no longer matches the artifact it produced. REPRODUCIBILITY
`DEPLOYABLE` now contains `C_lucb`, implemented at lines 205 and 264, and the module
docstring calls it the baseline the claim depends on ("uniform alone is too weak to
defend a claim against the unknown-variance allocation literature"). The confirmatory
panel does not contain it: `deployable_variants` in both artifacts is the five without
`C_lucb`. Backup timestamps date the addition: `.bak_prelucb` at 22:10:07 has
`C_lucb=0`; the cellv1 jobs started at 21:58 and Python reads the source at process
start, so they ran the pre-lucb code and finished at 01:01 against a file that had
already changed. Re-running the recorded command today yields eight variants, not seven.
ACTION: either rerun the panel with `C_lucb`, or pin the script by content hash in the
artifact so the mismatch is detectable.

### F2. `evidence_class` is hard-coded, exactly like `development_only` was
`write_artifact_with_provenance(..., evidence_class="DEVELOPMENT_EMPIRICAL", ...)`.
The 12 September repair computed `development_only` and `admissibility` inside the
payload but left the provenance stamp a literal. The provenance record -- the thing an
external reader trusts -- still says DEVELOPMENT for a confirmatory panel.
ACTION: derive it from `admissibility_record(...)["class"]`.

### F3. The provenance protocol fingerprint omits the seeds and the instance count
`protocol={relations, actions, topk, alpha, max_n, batch, pilot_fraction, rng_protocol,
permute, random_extrema, extrema_shift}`. A 2-instance smoke and the 1000-instance
confirmatory panel at the same shape produce the SAME protocol fingerprint.
ACTION: add `seeds` and `instances`.

### F4. Hyperparameters fixed by fiat: hard-coded, never CLI-exposed, never swept
* `explore = ceil(0.2 * n_add)` -- the exploration reserve of EVERY adaptive policy.
  With `batch=16` this is 4/16 = 25%, not 20%.
* `pooled = sqrt(0.5*sigma^2 + 0.5*mean(sigma^2))` -- the 0.5/0.5 shrinkage weight IS
  the whole identity of `C_shrink`, and it was never varied.
* `initial = 2*R*K`; `_balanced_counts(minimum=2)`.
* `boundary = order[:k+1]` -- the fixed-driver window width.
* `capacities -= arange(R)*1e-3` -- the separation nudge, which also sets a floor on
  `true_topk_gap` and therefore on the difficulty of the easiest instances.
* floors `1e-12` (scale) and `1e-15` (Bonferroni tail).
Only `alpha`, `batch`, `pilot_fraction`, `max_n` are CLI-exposed, and of those only
`pilot_fraction` is range-validated ([0.10, 0.20]). None were swept in any panel.

### F5. The pilot cost scales with the HORIZON, not with the problem
`pilot_total = max(2*R*K, ceil(pilot_fraction * max_n))`. At `max_n=131072` that charges
`C_pilot`/`C_shrink`/`C_split` 19,661 samples before they adapt; at `max_n=4096`, 614.
Doubling the experimental horizon doubles their handicap although nothing about the
problem changed. Their observed deficit to `C_anytime` (39,413 vs 29,884, i.e. 9,529)
is SMALLER than the head-start difference (19,601), so on this panel the pilot family
is being charged more than it loses by.
ACTION: define the pilot from the problem (a target relative standard error, say), or
sweep `pilot_fraction` and report sensitivity, before any claim ranks these policies.

### F6. `N_certificate` is not comparable across horizons, though the artifact pairs them
`looks = max_n`, so the Bonferroni tail is `alpha/(2*cells*max_n)`. Raising `max_n`
makes every interval strictly wider and the certificate strictly harder. The artifact
advertises `cross_horizon_common_world_and_cell_prefixes: true`, which matches the noise
streams across horizons but NOT the contract. Cross-horizon comparisons of
`N_certificate` therefore confound horizon with difficulty.

### F7. The noise scale is indexed by action only
`sigma = rng.uniform(.15,.85,size=actions)` -- one profile shared by every relation, and
unaffected by the relation permutation. A policy that learns which actions are noisy
gets that for all relations at once. This makes the instance easier than a per-cell
heteroscedastic one and should be stated as a modelling choice.

### F8. `--extrema-shift` redraws whole relations, not just their extrema
The shift branch re-draws `truth[r]` from scratch (keeping `capacities[r]` and
`centers[r]`), then picks a new extrema pair. So the shifted panel's worlds differ from
the base panel's on the shifted relations: the two panels are a REPLICATION at matched
seeds, not a paired perturbation of one world. Report 2 Section 87 says "resamples the
extrema of half the relations", which understates what changed.

### F9. Latent crash when `R == k`
`final_certificate_margin` takes `np.max` over the complement of `chosen`; that list is
empty when `relations == topk`. `run()` validates `topk < relations`, so it is
unreachable today, but the guard lives in a different function from the risk.

### What the file DOES cover, and covers correctly
Bonferroni union over every possible per-cell size (not realized looks); common random
streams verified by `world_sha256`; the `_prefix_stats` assert that catches a short
stream read before it can shrink a radius; the censoring-aware winner rule; the
`zero_information_accuracy` guard against the v3 confound; and `_instance_data`'s
per-cell `SeedSequence([seed, instance_id, 1, r, a])`, which is what makes cross-horizon
prefix matching real rather than nominal.

---

## [2/N] research_chains/provenance.py -- 136 lines, READ IN FULL

Imported by 66 scripts; the single most load-bearing library file in the corpus.

### P1. `build_manifest` cannot produce a confirmatory manifest, by construction
`if not development_only: raise ValueError(...)`, and then it writes the literal
`"development_only": True` regardless. It is currently DEAD CODE -- no call site exists
outside its own definition -- so it has damaged nothing, but it encodes the assumption
that made `development_only` a hard-coded literal in both labs.

### P2. The source fingerprint DOES capture the lab script, which makes F1 detectable
`source_sha` on the confirmatory panel is `418204a7...+dirty:1215739e...`, i.e. the git
branch of `source_fingerprint`, not the tree fallback. The v4 lab script is untracked,
so `git ls-files --others --exclude-standard` puts its BYTES into the dirty digest.
Recomputing the fingerprint now and comparing to the manifest therefore proves whether
the source changed after the run. This is the check that should be run before citing
any artifact.

### P3. The tree fallback walks vendored dependencies
`excluded_parts` is `{.git, __pycache__, .pytest_cache, .mypy_cache, .ruff_cache,
research, results, outputs, compile_logs, wandb}`. It does NOT exclude `.lake`, `.venv`,
`node_modules` or `addenda_pdf`. The git branch avoids them through `--exclude-standard`,
but the docstring states the fallback exists precisely because "research artifacts are
often exchanged as ZIPs without `.git`" -- the one workflow it is written for is the one
where it will hash 34,539+ files including all of mathlib and the virtualenv.

### P4. MY OWN DEFECT: the two scripts I added bypass this module entirely
`run_master_reference_phase_certificates.py` and `run_d6_reference_query_exchange.py`
hand-roll a manifest `{protocol_version, artifact, sha256, bytes, counts}` instead of
calling `write_artifact_with_provenance`. Their artifacts therefore carry no
`source_sha`, no `protocol_sha`, no `evidence_class`, and no `manifest_sha`, and cannot
be checked the way P2 allows for the lab artifacts. This is inconsistent provenance that
I introduced on 12 September and it must be repaired before either artifact is cited.

---

## [3/N] scripts/run_functional_variance_stopping_lab_v3.py -- 416 lines
Read as the diff against v4 (583 lines read in full), plus a per-function SHA over the
AST spans, plus an empirical equivalence run.

### V1. The certificate machinery is provably unchanged between v3 and v4
Byte-identical function bodies: `_prefix_stats`, `_intervals` (confidence intervals AND
the Bonferroni contract), `_capacity_intervals`, `_balanced_counts`, `_driver_cells`.
Changed: `_certificate`, `_allocate_batch`, `_one_variant` (all three only by added
branches for the new variants) and `_draw_world` (the intended generator change).

### V2. v4 reduces EXACTLY to v3 -- verified by running both
`--no-permute --fixed-extrema --rng-protocol legacy_sequential`, seeds 201/202, 8
instances, max_n 2048: all six shared variants agree on every run in N_certificate,
censored_N_certificate, certificate_emitted, false_safe, final width, minimum cell
samples AND the full `counts` matrix. 0 of 96 runs differ. The v3-to-v4 comparison
(2.5445 -> 2.4847) is therefore legitimate.
CAVEAT: at max_n=2048 every run censors, so equivalence is established in the regime
where no certificate fires. `counts` and widths still vary run-to-run and still match,
which is what makes the test meaningful, but an equivalence check at a certifying
horizon has not been run.

### V3. v3 records no per-instance `worlds`
The v3 confound was undetectable from a v3 artifact alone; only reading the generator
could find it. v4 added `worlds` and `world_audit`.

---

## [4-8/N] research_chains/: certificates.py (167), contracts.py (90),
## finite_world.py (98), support.py (84), estimation.py (26) -- ALL READ IN FULL

### C1. `certificates.exact_optimum` enumerates all C(m,k) subsets
Exponential in m, hard-coded `1e-12` optimality tolerance, ties collected not broken.
A scaling wall, not a bug.

### C2. The same low-index tie-break lives in the certificate layer
`topk_indices` sorts by `(-scores[j], j)`: ties go to the LOWER index, the same rule
whose interaction with an index-sorted generator produced the v3 confound. Audit it
wherever it meets generated data.

### C3. `lp_lower_bound` fails closed
Raises on any non-success scipy status rather than returning a silent zero. Correct.

### C4. The typed-contract layer exists and is NOT wired to the labs
`contracts.CertificateLevel` documents exactly the hazard this project keeps hitting --
"Do not silently promote oracle/diagnostic quantities to certificates" -- with
ORACLE_EXACT / DETERMINISTIC_BOUND / HIGH_PROBABILITY_BOUND / ESTIMATED_DIAGNOSTIC /
UNAVAILABLE. Measured usage: `CertificateLevel` appears in no script outside
`research_chains/__init__.py`'s re-export; the Functional lab references it 0 times and
separates DEPLOYABLE from DIAGNOSTIC with two plain string tuples and a convention.
`SupportBracket`, by contrast, is used in 20 files -- so the library is used, this
particular guard is not. Wiring the lab's variants to the enum would make
`C_known_sigma` and `C_extrema_oracle` structurally unable to enter a deployable
comparison instead of conventionally excluded.

### C5. `support.py` and `finite_world.py` are clean
Frozen dataclasses, alphabet/dimension/finiteness validation in `__post_init__`,
`SupportBracket` enforcing lower subset-of upper and `validates()` checking the truth
lies between them. No findings.

---

## [9-32/N] research_chains/ COMPLETE -- all 32 files, ~5,600 lines, read in full

d6_active_cell_lp 815, experimental_extensions 802, d6_contrast_rank 456,
novelty_completion 455, functionals 446, kprefix 340, reference 225, oracle 245,
h1_fixed_panel 198, certificates 167, query_contracts 144, structural_staircase 139,
kprefix_deep 107, pairwise 101, finite_world 98, contracts 90, support 84, f3 84,
structural 71, proposal_registry 56, query_baselines 29, query_oracles 27,
estimation 26, __init__ 26, query_method_registry 4, query_methods/* 51.

### R1. `development_only: True` is hard-coded at a THIRD site
`d6_active_cell_lp.discover_active_cells` returns a literal `"development_only": True`.
With v3 line 324 and v4 line 479 that is three independent hard-codings of the same
field. It is a corpus-wide habit, not a slip.

### R2. Evidence-class discipline is strong in prose and weak in mechanism
Every discovery module carries an explicit `scope` string that refuses to call survival
a proof -- "sampled active cells are not an exhaustive proof", "survival is
falsification evidence, not proof", "heuristic direct full-table optimization ...
survival is not proof". `contracts.CertificateLevel` exists to make that structural.
Nothing imports it. The discipline lives in strings a reader must notice, not in types
a run must satisfy.

### R3. Where the code IS careful, and it is worth preserving
* `oracle.trusted_execution_receipt` refuses to treat requested actions as executed
  unless the environment opts in, and `JointOracleRecord` separates the
  ceteris-paribus `execution_verified` from the weaker `execution_verified_sources`.
  The docstring records the historical bug this prevents: iterating a `last_actions`
  dict yields KEYS, so `tuple(last_actions)` silently returned `(0,1,2,...)`.
* `kprefix.exact_cover_layers` cross-checks its DP against a SciPy MILP and raises
  `AssertionError("DP/MILP exact cover disagreement")`.
* `d6_active_cell_lp.solve_active_cell_lp` refuses to solve a frozen cell under a
  different reference; `exact_verify_binary_solution` re-derives everything in exact
  `Fraction` arithmetic independently of SciPy's own diagnostics, and
  `counterexample_found` was redefined to mean the exact check, not a float excess.
* `novelty_completion._require_unique_evidence_keys` fails closed because duplicate
  keys would make a reported selection unreproducible.
* `pairwise.compose_same_target_score_error` refuses to add radii across estimands.
* `proposal_registry` states that a clean suite is not evidence that every registered
  proposal ran.

### R4. Hard-coded tolerances are everywhere and none are swept
`1e-12` (optimality, ties, gauge), `1e-15` (Bonferroni floor, tie candidates), `1e-8`
(LP dual, rank), `1e-9`/`1e-7`/`1e-5` (rank-one), `1e-10`, `limit_denominator(100000)`
in the rational check, `penalty=1e8` and `lr=2e-4` in the B3 search. Several of these
decide a VERDICT: `rank_tol` decides whether a candidate counts as rank-one, and
`limit_denominator` decides whether the exact check reproduces the float solution.
They are arguments with defaults, never varied in any recorded run.

### R5. Two import-time fragilities
`kprefix_deep` imports `torch` and `models.kprefix_net` at module scope, so importing it
fails hard where torch is absent. `d6_contrast_rank` and the B3 search instead wrap
torch in `try/except` and return `{'available': False}`. The two conventions disagree
inside one package.

### R6. `h1_fixed_panel` stores panels as pickle
`save_fixed_panel`/`load_fixed_panel` use `pickle.dump`/`pickle.load` inside gzip, with
a sha256 sidecar and a step-hash ledger that IS verified on load. The integrity checking
is good; the format means a panel file is executable content, which matters if a panel
is ever exchanged the way the provenance docstring says artifacts are exchanged.

---

## [36-40/N] scripts/ audit+provenance cluster -- read in full
audit_novelty_chain_artifacts 96, audit_completed_experiment_evidence 122,
audit_post_p13_results 119, validate_ieee_benchmark_protocol 39,
run_adapter_capability_audit 41.

### S1. The axiom gate is a hard-coded list of 55 and the corpus has 321 modules
`audit_novelty_chain_artifacts.MODULES` is a literal list. Everything outside it is
never gated. Measured state of the whole tree, applying that script's OWN criteria
(`': error' not in log`, no `sorryAx`, axioms subset of {propext, Classical.choice,
Quot.sound}, `olean.mtime >= source.mtime`):

    CLEAN        161
    NO_LOG       156   (compiled as an import; no individual log is produced)
    ERRORS         4
    sorryAx        0
    non-standard   0
    stale olean    0

So the corpus is in good shape; the gate simply does not assert it. The four error
modules are `LeanD6RecordGapDecompositionV1` and `LeanD6ScalarExplorationSeparationV1`
-- the two Report 5 Section 189 already declares as carrying `sorryAx` with nothing
depending on them -- plus `LeanD6BernoulliSlopeV1`/`SlopeBV1`, in flight on 12 September.

A first framing of this finding as "249 compiled modules are unchecked" was wrong and is
retracted here: `#print axioms` is transitive, so a clean downstream audit does cover the
imports for the theorems actually used. The correct statement is that 55 modules are
gated automatically and the remaining coverage is incidental rather than asserted.

ACTION: derive `MODULES` from `work/p13_conjectures/*.lean` and allow an explicit
declared-exception list, so a new module is gated by default instead of by remembering
to add it. Six modules added on 11-12 September (`LeanD6ReferenceReducedGameV1`,
`LeanMinimaxRiskBridgeV1`, `LeanD6ReferencePhaseValueV1`, `LeanD6ReferencePhaseThresholdV1`,
`LeanD6BernoulliReferenceBridgeV1`, `LeanD6BernoulliTailV1`) are outside the gate today.

### S2. The `closed`/`open` ledger is prose, not computation
`audit_novelty_chain_artifacts` writes 25 hand-written "closed" sentences and 4 "open"
ones into `chain_closure_manifest.json`. Nothing derives them from the modules it just
verified. The manifest therefore asserts closure; it does not demonstrate it.

### S3. `validate_ieee_benchmark_protocol` validates the protocol FILE, not compliance
It checks seed count/uniqueness, that a false-safe rate is required, that tiers A/B/C
exist and that three named ablations are present. Nothing in the corpus checks that a
given artifact actually USED the frozen seeds, horizon or rng protocol. That check is
what the 12 September `admissibility_record` now makes possible, and it is not yet
wired into any validator.

### S4. `audit_post_p13_results` is the strongest audit in the corpus
It detects STALE_ANALYSIS, INCOMPLETE, STALE_SUMMARY, MISSING_PLANNED_EVIDENCE and
STALE_MACHINE_STATE, never mutates an artifact, and explicitly reasons that a historical
decision stays valid for its own generation while ceasing to describe current state. It
already contains the exact censored-median-winner detector for the bug class that the
Functional v1 analysis hit.

### S5. `audit_completed_experiment_evidence` recomputes rather than re-reads
Exact `Fraction` reconstruction of frontier witnesses from the stored world classes,
independent permutation enumeration for the structural cover, and for the integer-block
Monte Carlo a chi-square simultaneous envelope for the MSE ratio plus a binomial test
with Bonferroni across pooled cells. It also refuses to overwrite its output. This is
the model the rest of the corpus should follow.
