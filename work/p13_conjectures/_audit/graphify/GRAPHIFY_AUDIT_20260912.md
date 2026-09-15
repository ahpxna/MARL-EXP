# Graphify structural audit — CIG-AMF corpus
**Date:** 2026-09-12 · **Tool:** graphify 0.9.58 + a purpose-written Lean 4 extractor
**LLM calls:** 0 · **Build time:** ~23 s · **Append-only:** new artifact, nothing edited or deleted

---

## 0. Evidence class of everything below

This document contains **NO proofs and NO numerical results.** Every statement is a
**STRUCTURAL FACT**: something read literally out of the source text by a deterministic
parser. It sits strictly below COMPILED ARTIFACT on the ladder:

> PROVED ≻ COMPILED ARTIFACT ≻ NUMERICAL EVIDENCE ≻ **STRUCTURAL FACT** ≻ CONJECTURE

A structural fact answers *"is this token present in this file, and which file imports
which"* — never *"is this theorem true"*. It is used here only to locate where the
audit surface has holes, not to fill them.

### The extractor has two layers, and they are not equally trustworthy

| Layer | How it is obtained | Trust |
|---|---|---|
| **module / import / flag** | literal match on the source **after comments and string literals are blanked out** (nested `/- -/`, `--`, `"…"`) | **exact** — a token counted here is really in the code, not in a docstring |
| **declaration → declaration `uses`** | identifier match against the declared-symbol table, resolved through the enclosing `namespace` and `open` | **heuristic** — tagged `INFERRED`, or `AMBIGUOUS` when >1 declaration matches |

**Every finding in §2–§5 rests only on the exact layer.** The heuristic `uses` layer is in
`graph.json` for navigation and is not cited as evidence anywhere in this document.

### One correction made during this build, and why it is reported here

The first pass resolved **every** bare identifier in a declaration body against the
declared-symbol table. That is wrong: `(j : I n)` binds a local `j`, it does not reference
some top-level `j`. The first `god-nodes` output was consequently `j, I, A, S, hi` — binder
letters, not concepts. Local binders (header groups, `∀`/`∃`/`fun`, `intro`/`rintro`/`obtain`/
`rcases`/`set`/`let`/`use`, `⟨…⟩` patterns) are now excluded, which removed **4,589 false
`uses` edges (19% of the Lean edge set)** and made the hub list read as the corpus actually
reads: `productResponse · selectedRadius · osc · others · productCompressionLoss ·
Measurement · jointWeight · mixedDifference · ActiveDecisionCell · Legal`.

**The exact layer did not move by a single count across that fix:**

```
BEFORE binder fix: modules=329 imports=510 sorry=1 native_decide=3 audited=175 uncovered=92
AFTER  binder fix: modules=329 imports=510 sorry=1 native_decide=3 audited=175 uncovered=92
                   (Lean edges 24,393 -> 19,804: all of the change is in the heuristic layer)
```

That invariance is the point. A 19% change in the heuristic layer moved **none** of the
numbers cited in §2-§5, which is what "the findings rest only on the exact layer" means
operationally rather than as a promise.

### What the extractor does NOT model
`open … in` scoped to a single declaration · `variable` binders · macro-generated names ·
`mutual` blocks as a unit · `where` clauses as separate declarations · elaborated terms
(it reads surface syntax, never the elaborator's output). None of these affect the
import graph or the flag counts.

---

## 1. Why a custom extractor was needed

Graphify out of the box **cannot see Lean at all**. Verified in source, not inferred from
behaviour:

- `graphify/detect.py` → `CODE_EXTENSIONS` holds 100+ suffixes; `.lean` is not among them.
- `DOC_EXTENSIONS` = `{.md .mdx .qmd .skill .txt .rst .html .yaml .yml}`; `.lean` is not there either.
- `pyproject.toml` declares 31 `tree-sitter-*` grammars; there is no `tree-sitter-lean`.

So a plain `/graphify .` on this repo would have silently dropped **447 of 447 project
Lean files** and reported a confident graph of the Python half only. That failure mode is
invisible: the tool reports success, and the count of files it skipped is not shown.

`lean_extract.py` (in this directory) closes that gap by emitting graphify's documented
extraction schema — `{nodes:[{id,label,source_file,source_location}], edges:[{source,target,relation,confidence}]}` —
which `build_from_json()` consumes directly.

---

## 2. Corpus shape (structural fact)

| | |
|---|---|
| Repo on disk | 12 GB, 252,267 files — **dominated by build artefacts** (61,544 `.hash`, 48,021 `.pyc`, 9,222 `.olean`, 8,835 `.trace`, 8,793 `.ilean`) and a vendored `.venv` + `external_envs/` |
| Project Python | **352 files** (`scripts/ utils/ models/ envs/ research_chains/ observatory/ tests/ work/p13_conjectures/`) — everything else under `.venv`, `site-packages`, `external_envs` is third-party |
| Project Lean | **445 files** → **329 distinct modules** |
| Merged graph | **8,735 nodes · 30,210 edges · 297 communities** |
| Lean half | 329 modules · 2,482 theorems · 210 lemmas · 966 defs · 21 abbrevs · 17 instances · 16 structures · 11 inductives · 5 examples |

**`work/p12` is a byte-identical subset of `work/p13_conjectures`.** 116 filenames appear in
both trees; 115 were compared pairwise with `cmp` and **all 115 are byte-identical, 0 divergent**
(the 116th is the nested `work/p13_conjectures/work/p13_conjectures/` copy). The frozen P12
corpus has therefore **not drifted** from the active tree. Collapsing the two into one module
node is correct, not a loss.

**The Lean import graph is acyclic** (329 nodes, 510 project-local import edges,
`nx.is_directed_acyclic_graph` = True, `simple_cycles` = ∅). Expected — Lean enforces it —
but now checked rather than assumed.

---

## 3. `sorry` — contained, and now verified contained

| | |
|---|---|
| Modules containing a live `sorry` token | **1** — `LeanD6DecisionHalfFactorConjecture` (`work/p12/`, and its identical `p13` copy) |
| Modules that transitively import it | **0** |

The file's own docstring claims *"QUARANTINED / OPEN. Not part of the active build."*
That claim is now **independently confirmed by the import graph**, rather than believed
because the comment says so: nothing in the corpus can reach it, so `sorryAx` cannot leak
into any other module's axiom set.

`sorryAx` as a token: 0 occurrences outside that module.
`axiom` declarations: **0** across all 329 modules.

---

## 4. `native_decide` — 3 seeds, promotion discipline holds

`native_decide` routes the answer through `Lean.ofReduceBool`, which is the rejected
trust hole. Seeds (exact match on masked source):

| Module | Location |
|---|---|
| `LeanD6PairContractionCounterexample` | `work/p12/` |
| `LeanStructuralActualChi4WitnessV1` | `work/p12/` |
| `LeanStructuralScalarChi5WitnessV1` | `work/p12/` |

**7 modules transitively import one of these three**, but the promotion discipline is
intact — checked by reading the audit files, not inferred:

- `LeanD6PairContractionKernelV1`, `LeanStructuralActualChi4KernelV1`,
  `LeanStructuralScalarChi5KernelV1`, `LeanStructuralScalarChi5GeometryKernelV1`
  are **kernel replacements**: they re-prove the same facts with kernel `decide`.
- `AxiomAuditNoveltyChainsV1` audits the `…_kernel` names, not the native ones
  (lines 51–52: `…StructuralActualChi4Kernel.…_kernel`, `…D6PairContractionKernel.pair_contraction_route_killed_exact_kernel`).
- `AxiomAuditStructuralScalarChi5KernelV1` audits all 10 `…_kernel` names, and says so
  explicitly: *"If any reports `Lean.ofReduceBool`, the promotion failed."*
- `LeanStructuralIntegerToleranceV1` imports the **geometry kernel**, not the native
  witness, and carries `#print axioms` on all 3 of its own theorems.

**Residual exposure:** the original native-decide theorems still exist in the environment.
Any downstream citation that names the ORIGINAL (`pair_contraction_route_killed_exact`,
without `_kernel`) rather than the promoted one is still a COMPILED ARTIFACT, not PROVED.
The graph cannot tell which name a *paper* cites — only which name the *Lean* cites.
**That check remains manual.**

---

## 5. The actual audit gap: 92 modules under no `#print axioms` at all

`#print axioms` is **transitive** — auditing a downstream theorem covers everything its
proof depends on. So "module has no `#print axioms`" is the wrong metric, and the naive
count (154/329 missing) overstates the problem. The right question is: *is this module
reachable, through the import graph, from any module that does run an axiom audit?*

| | |
|---|---|
| Modules carrying `#print axioms` | 175 / 329 |
| Covered (self-audited, **or** imported by an audited module) | **237 / 329** |
| **Covered by NO axiom audit whatsoever** | **92** |

These 92 are the real gap. The load-bearing ones — pieces with dependents, not scratch files:

```
LeanD6HalfFactorCore                 LeanD6PAECExistence
LeanD6HalfFactorSharpness            LeanD6PAECFin4 / LeanD6PAECFin6
LeanD6PAECCanonical                  LeanD6PAECCanonicalWitnessesV1
LeanD6PAECAtomicNormV1               LeanD6PAECAtomicMassDegeneracyV1
LeanD6PAECCostAwareAdapterV1         LeanD6BalancedCycleCertificate
LeanD6ResidualAPI                    LeanD6ResidualOrthogonality
LeanD6CanonicalUniformDecisionCertificateV1                 LeanD6ProductCyclePathV1
```

The whole **PAEC branch — the D6 headline route — is unaudited end to end.** Note what this
does and does not say: it does **not** say those modules use a bad axiom. It says **nobody has
run the check that would license calling them PROVED.** Under the discipline
"`#print axioms` is what licenses PROVED, not absence of `sorry`", all 92 are currently
COMPILED ARTIFACT at best.

Full list: `axiom_audit_gap.txt` in this directory.

**Suggested fix** (one new file, append-only, nothing edited): an
`AxiomAuditPAECBranchV1.lean` importing the PAEC modules and running `#print axioms` on
each public theorem. ~30 lines, and it collapses the gap from 92 to roughly 60.

---

## 6. Other structural observations

**89 orphan modules** — no project-local module imports them. 15 are `AxiomAudit*` files,
which are correctly leaves (nothing should import an audit). The rest are terminal results
or abandoned branches; the graph cannot distinguish those two, so this is a list to triage,
not a verdict.

**Highest-degree declarations** (`graphify god-nodes`, Lean subgraph) — the concepts the
corpus is actually built out of: `productResponse` (384) · `selectedRadius` (274) ·
`osc` (209) · `others` (203) · `productCompressionLoss` (159) · `Measurement` (142) ·
`jointWeight` (116) · `mixedDifference` (108) · `ActiveDecisionCell` (79) · `Legal` (87).
`I` (637) is the index-type def and is genuinely ubiquitous; read it as background, not signal.

**Most-imported modules** (the real foundations, by in-degree):
`LeanFunctionalRankingV6` (13) · `LeanProductMixedDifferenceV4` (12) ·
`LeanSupportGeometryV4` (11) · `LeanD6CycleDual` (9) · `LeanD6AllocationMarginV1` (8) ·
`LeanD6GaussianQueryDominanceV1` (8) · `LeanD6InteractionContrastRankOneV1` (7) ·
`LeanD6PolyhedralActiveCellV1` (7).

**`LeanD6BinaryBridgePartAV1` is a verbatim prefix of `LeanD6BinaryBridgeV1`** — same
namespace `CIGAMF.P13.D6BinaryBridgeV1`, same declarations. Both are in the tree and both
are unaudited. Nothing is deleted here; flagged so the duplication is on the record.

**Graphify's fuzzy dedup was disabled on purpose.** With `dedup=True` it merges **272 nodes,
269 of them Lean declarations** — e.g. it would fuse
`D6AllocationPhaseThreeDual.actual_joint_bound` with `D6PhaseThreeDual.actual_joint_bound`,
which are **different theorems in different modules**. Silently fusing distinct declarations
is exactly the failure this corpus's discipline forbids, so the merge was recorded and not
applied: see `dedup_would_merge.json`.

**Known distortion:** the 9 flag nodes (`⚑ sorry`, `⚑ decide`, `⚑ print_axioms`, …) are
high-degree by construction and surface as community hubs in `GRAPH_REPORT.md`. They are
queryable markers, not concepts — discount them when reading the community structure.

---

## 7. What this does NOT do

**This is not a substitute for reading every line.** The graph answers *where things are
and what depends on what*. It cannot tell whether a proof is correct, whether a bound is
sharp, whether a formula is novel, or whether a hypothesis is doing real work. The
line-by-line read stays the source of truth for all of those; this is the index over it.

Specifically not covered: the `.md` / `.tsv` / `.csv` result files (graphify's semantic
pass over docs needs an LLM backend and was deliberately not configured — every number in
those files would have arrived as a model's paraphrase rather than a parse); the Python
half's runtime behaviour; and any claim about what a *paper* cites.

---

## 8. Reproduce

```bash
uv tool install 'graphifyy[leiden,svg,pdf,office,watch]'
GRAPHIFY_VIZ_NODE_LIMIT=20000 python3 build_cigamf_graph.py <repo-root> <out-dir>
```

Deterministic: same input bytes → same graph. No network, no model, no API key.
`_audit/` is excluded from its own scan, so re-running does not index the previous output.

Query the installed graph (the CLI accepts an explicit `--graph`):

```bash
graphify explain "LeanD6PAECExistence"       --graph <this-dir>/graph_lean.json
graphify affected "LeanD6PairContractionCounterexample" --graph <this-dir>/graph_lean.json --depth 3
graphify god-nodes --top 20                  --graph <this-dir>/graph_lean.json
graphify path "A" "B" --undirected           --graph <this-dir>/graph_lean.json
```

| File | What it is |
|---|---|
| `lean_extract.py` | the Lean 4 extractor (this is the new part) |
| `build_cigamf_graph.py` | driver: Python AST + Lean → one graph |
| `graph.json` / `graph.html` | merged graph, 8,777 nodes |
| `graph_lean.json` / `graph_lean.html` | Lean-only subgraph, 4,068 nodes |
| `GRAPH_REPORT.md` | graphify's own report |
| `extraction_lean.json` / `extraction_python.json` | raw extractions |
| `axiom_audit_gap.txt` | the 92 uncovered modules |
| `dedup_would_merge.json` | the 272 merges that were rejected |
| `import_cycles.json` | empty — the import graph is acyclic |
