# PACKAGE 0 (Z1) — Is the multi-tip support geometry more than a re-encoding of a
# general finite decision-region problem?

Worker chain: SUPPORT / QUERY / MASTER. Date: 2026-09-13/14.

Artefacts
- Lean: `work/p13_conjectures/LeanSupportGeometryReductionV1.lean`
  — compile receipt `LeanSupportGeometryReductionV1.compile.receipt.json`:
  `lean_exit=0`, `errors=0`, **19 audited names**, `nonstandard_axioms=0`,
  `accepted=true` (axioms only `{propext, Classical.choice, Quot.sound}`).
- Probe: `scripts/Z1_geometry_reduction_check.py`
  — artefact `research/worker_geometry_reduction_20260913/Z1_geometry_reduction_check.json`.
  Exact `fractions.Fraction` throughout; raises on any mismatch.

---

## 1. VERDICT

**The reduction HOLDS, and it is exactly cost-preserving — but only under a
restriction that the geometry does not itself supply.**

Precisely (all three statements are Lean receipts):

1. **`cost_preserving` (PROVED).** For every finite decision-region problem
   `P` (arbitrary worlds `Fin nW`, arbitrary decisions `Fin nD`, arbitrary binary
   tests `Fin nE`, arbitrary unsafe table, arbitrary test table), the encoding
   `W_θ = {d : d unsafe at θ} ∪ {nD + e : test e answers 1 at θ}` into
   `Finset (Fin (nD+nE))` satisfies

   ```
   dCost P = { depth t | t a membership-query tree on the encoded geometry,
                         t queries ONLY test coordinates,
                         t outputs ONLY decision coordinates,
                         t correct in every world }
   ```

   as an equality of **sets of achievable depths**, in both directions, with no
   slack: `embed` is a depth-preserving bijection between the two strategy
   classes (`embed_restricted` + `exists_embed_of_restricted`), and correctness
   corresponds exactly (`correct_iff`), through the REAL geometry —
   `safety_faithful` is stated with `selectedRadius (components (encode P θ))`
   and `query_faithful` with the physical membership oracle of
   `LeanSupportCardinalityQueryLawV1`.

2. **`decision_restriction_necessary` (PROVED).** The restriction of the ALLOWED
   DECISION SET cannot be dropped. Explicit two-world instance `badDecision`:
   abstract cost 1, restricted-geometry cost 1, **unrestricted-geometry cost 0** —
   the learner selects the auxiliary coordinate of a constantly-`0` test, which is
   absent from every encoded world and therefore has `selectedRadius = 0` in all
   of them.

3. **`query_restriction_necessary` (PROVED).** The restriction of the ALLOWED
   QUERY SET cannot be dropped either. Explicit two-world instance `noTest` with
   no tests at all: **no correct abstract strategy exists at any depth**, while the
   unrestricted encoded geometry solves it in **one** query — because the physical
   membership query at a DECISION coordinate is literally the safety oracle of that
   decision.

So the answer to the supervisor's question "which restriction is needed" is exact:
**the allowed decision set and the allowed query set must be disjoint coordinate
blocks — decisions in the low block, queries in the high block.** Neither
restriction can be weakened; each one alone is already violated by an explicit
2-world counterexample.

### Consequence, stated plainly

Under that restriction, `{multi-tip support geometry + physical membership queries
+ a restricted decision/query set}` is **the same class, at the same query cost**,
as `{finite decision-region determination}`. Adding one more witness to
`selectedRadius` is therefore mostly a *realization* of an already-known problem
and confers **no theoretical advantage from the geometry**.

If instead the restriction is dropped — i.e. if the geometry is used as the corpus
actually uses it, with every coordinate both selectable and queryable — then the
geometry is **not** the general problem: it is **strictly easier**, and its exact
complexity is already pinned in the corpus. `unrestricted_exact_cost` (re-export of
`CardinalityQueryLaw.adaptive_cardinality_attained` / `adaptive_cardinality_lower`)
gives the exact zero-error worst-case adaptive cost `s` for the promise
`W.card ≤ s`, matched above and below. The probe reproduces this independently
(check Z6: cost `= s` for every `m = 2..6`, `s = 0..m-1`). There is no residual
hardness there to discover.

**Either way the geometry confers no theoretical advantage.** That is a negative
result and it is the point of this package.

## 2. Comparison with Javdani, Chen, Karbasi, Krause, Bagnell, Srinivasa,
## "Near Optimal Bayesian Active Learning for Decision Making", AISTATS 2014

That paper's *Decision Region Determination* (DRD) problem is: a hypothesis set, a
set of tests with observable outcomes, and a collection of decision regions
(subsets of hypotheses on which a common decision is valid); the goal is to run
tests until the version space is contained in some region, minimising expected
cost. They give `HEC` (Hyperedge Cutting), a greedy surrogate with an
`O(log(...))`-factor near-optimality guarantee via adaptive submodularity, and
position it against `EC2` (Golovin, Krause, Ray 2010, equivalence-class
determination) and `GBS`/generalised binary search.

The correspondence with the geometry under the restriction is exact and
structure-for-structure:

| DRD (Javdani et al. 2014)          | multi-tip support geometry                       |
|------------------------------------|--------------------------------------------------|
| hypothesis `θ`                     | world `W ⊆ Fin m`                                |
| test with binary outcome           | physical membership query `j ∈ W`                |
| decision region for decision `d`   | `{W : selectedRadius (components W) {d} = 0}` = `{W : d ∉ W}` |
| "version space inside some region" | "some allowed decision is safe in all survivors" |
| expected/worst-case number of tests| `depth` of the membership-query tree             |

Differences that are real but do **not** rescue a novelty claim:
- They optimise **expected** cost under a prior with an approximation guarantee;
  `cost_preserving` here is about **exact worst-case zero-error depth**. The
  reduction is not claimed to preserve approximation ratios or expected cost.
- Their decision regions are arbitrary subsets of hypotheses; here the region of
  decision `d` is always `{W : d ∉ W}`, i.e. a *coordinate* region. That is a
  restriction on the geometry side, and it is exactly the restriction that makes
  the unrestricted geometry trivial (Section 1, point 3) rather than hard.

So: nothing in the geometry escapes DRD, and the coordinate structure that the
geometry *does* impose makes the problem easier, not harder.

## 3. SECOND PART — what a genuinely restricted geometry would have to look like

The supervisor's instruction was: "geometry plus queries" is not enough; exhibit
WHICH hard problems the geometry excludes. Here is the honest answer.

**Finding (PROVED + NUMERICAL): in terms of query COST, the unrestricted geometry
excludes nothing hard, because it is already easy; and the restricted geometry
excludes nothing at all, because the reduction is onto.** The encoding
`encode : DRProblem → (Fin nW → Finset (Fin (nD+nE)))` is onto every possible world
table: with `nE = 0` and `nW = 1`, `encode` realises every `W ⊆ Fin nD`. So no
proper world family can be characterised as "the image of the reduction".

The only thing the geometry genuinely fixes is the **query primitive**: there are
exactly `m` possible queries (one per coordinate), not an arbitrary test set. Two
receipts quantify what that is worth:

- `outputs_card_le` (PROVED): a depth-`k` tree has at most `2^k` distinct outputs.
- `incompatible_worlds_lower` (PROVED): if every two distinct worlds of a family
  share no safe decision (`W ∪ V = univ`), then a correct tree must output a
  different decision on each, so `|family| ≤ 2^depth`.
- `dense_counting_bound` (PROVED): at the dense family `{univ.erase w}` this gives
  only `m ≤ 2^depth`, i.e. `depth ≥ log2 m`.

But the membership primitive actually forces `depth ≥ m-1` there
(`AdaptiveQuerySeparation.dense_query_depth_lower`,
`CardinalityQueryLaw.adaptive_cardinality_lower`). The gap between `log2 m` and
`m-1` is entirely a statement about the query set, and the probe makes it concrete
(check Z7, `m = 2..7`): the **same** decision problem (dense family: decision `j` is
safe iff `j = w`) costs

| `m` | cost with the `m` membership coordinates | `ceil(log2 m)` bit-test coordinates added | cost then |
|-----|------------------------------------------|-------------------------------------------|-----------|
| 4   | 3                                        | 2                                         | 2         |
| 5   | 4                                        | 3                                         | 3         |
| 6   | 5                                        | 3                                         | 3         |
| 7   | 6                                        | 3                                         | 3         |

i.e. the cost is a property of the **allowed query set**, not of the geometry or of
the decision problem. Adding `ceil(log2 m)` auxiliary coordinates (which the
reduction of Section 1 does automatically) collapses `m-1` to `ceil(log2 m)`.

### What would actually be needed

For a genuinely restricted geometry to earn a complexity statement better than
general DRD, the restriction has to bite on the WORLD FAMILY, not on the ambient
space, and the query primitive has to stay fixed. The corpus already contains one
instance of exactly this shape, and it is the model for what "restricted geometry"
should mean:

- **interval / cyclic-window support** (`LeanSupportIntervalHittingV1`,
  `LeanSupportCyclicWindowV1`, `LeanSupportNonadaptiveExactV1`): worlds are `s`
  cyclic windows of length `L` in `ZMod m`, and `nonadaptive_exact` proves
  `IsLeast (depths s L) (s*L)` — an EXACT non-adaptive query complexity for a
  restricted family, with the fixed membership primitive. That is a real
  geometry-driven complexity result, and it is already in the repo.

Of the three candidate restrictions the supervisor listed, this assessment
(SKETCH, not proved here) is:
- *components affine on a common low-dimensional space*: for the multi-tip
  geometry the components are already determined by the indicator of `W`
  (`radius_formula`), so "affine on a low-dimensional space" is equivalent to
  restricting `W` to a low-dimensional family of indicators — i.e. it is a world
  family restriction, and the payoff is the counting bound `|family| ≤ 2^depth`.
  With the FIXED membership primitive that bound is generally far from tight
  (dense family: `log2 m` vs `m-1`), so a *matching* algorithm has to be
  constructed by hand per family. Nothing generic follows.
- *support with a specific convex/interval structure*: this is the cyclic-window
  family, which already has an exact law (`nonadaptive_exact`). This is the one
  direction of the three that has actually delivered.
- *a fixed query primitive that does not add one coordinate per test*: the physical
  membership query already IS such a primitive. Its consequence is negative, not
  positive: it makes the unrestricted geometry easy (`unrestricted_exact_cost`) and
  it is the sole source of the `m-1` vs `log2 m` gap.

**No hard problem is excluded by the geometry.** The honest summary is that the
multi-tip geometry is a presentation layer; the only object in this chain with
genuine complexity content is the restricted world family (windows), and that
already exists.

## 4. THIRD PART — the Query chain against Bshouty & Feldman 2002

Reference: N. H. Bshouty and V. Feldman, "On Using Extended Statistical Queries to
Avoid Membership Queries", JMLR 2 (2002) 359-395. That paper defines statistical
query models in which the learner **chooses the product distribution** the queries
are answered against, analyses the Fourier picture of product distributions, and
shows what this buys — including that parity, which is not weakly SQ-learnable at a
fixed distribution, becomes learnable once the learner may move the product
distribution. This is a **direct collision** with any claim of the form "changing
the product reference is a new way to see interactions".

Audit of the existing Query modules against it:

| Module / claim | status |
|---|---|
| `LeanQuerySufficiencyV4` `E1_same_pairwise_response`, `E2`, `E3`, `E4_xor_synergy_witness`: at one fixed product reference the two marginal response functions coincide for `zeroWorld` and the XOR `interactionWorld`, yet `interactionQuery` differs by 4 | **TRUE and compiled, but MUST BE NARROWED.** This is the 2-variable instance of the elementary Fourier fact that a degree-2 coefficient is invisible to degree-≤1 statistics at a fixed product reference, and that moving the reference exposes it. That mechanism is precisely Bshouty-Feldman's. Keep as a *witness*; delete any wording that presents "reference control reveals interactions" as new. |
| the narrative "change the product reference to learn interactions" (Query/MASTER reference-control line, `LeanD6Reference*`, `scripts/QUERY_*`) | **DOES NOT SURVIVE as novelty.** Must be restated as: a known mechanism, re-instantiated inside the corpus's compensated-world construction. |
| `LeanQuerySufficiencyQuantitativeV1` `E5_response_only_minimax_lower_bound` (`|T m1 - T m2|/2 ≤ max(...)` under a summary collision) | **SURVIVES as stated**, but it is the standard two-point (Le Cam) argument. It is a correct deterministic minimax lower bound; the module's own docstring already disclaims novelty. No collision with Bshouty-Feldman (that paper is about learnability, not about a decision-theoretic regret floor). |
| `LeanQueryRepresentationNecessityV1` `QN1_same_summary_rule_implies_common_good` | **SURVIVES.** "Same summary ⇒ any summary-measurable rule must be good for both worlds" is a definitional decision-theoretic statement, orthogonal to Bshouty-Feldman. Not a novelty claim either. |
| `LeanQueryIdentifiabilityVerifierV1` (`Identifiable`, `badPairs`) | **SURVIVES.** Finite identifiability bookkeeping; no collision. |

What could still be genuinely distinct from Bshouty-Feldman, and should be the
only thing the Query chain claims:
1. **Constrained references.** Bshouty-Feldman let the learner choose freely inside
   a class of product distributions. If the corpus's references are *physically
   constrained* (a legal/feasible set of `t_0`, as the `LeanD6Reference*Legal*`
   modules suggest), then "which interactions are reachable from the feasible
   reference set" is a different question. This must be stated as the claim.
2. **Decision-theoretic rather than learning-theoretic conclusion**: a regret floor
   for a safe decision, not a sample-complexity bound for identifying the function.
3. **Exact minimax constants** instead of polynomial bounds.
None of these three is established by the modules audited above; they are the
narrowed claims that remain available.

## 5. NUMERICAL RECEIPT (probe `Z1_geometry_reduction_check.py`)

All checks raise on mismatch; the run completed with exit 0.

- **Z0** — 640 checks: `selectedRadius` recomputed **from its definition** on the
  actual support points (`Option {w // w ∈ W}`, anchor plus tips) equals
  `((m-1)/2)·[j ∈ W]` and the physical membership query equals set membership, for
  `m = 2..6` and all `2^m` worlds. (This numerically validates `radius_formula`.)
- **Z1/Z2/Z3** — **9112 instances** (8512 of them from exhaustive table
  enumeration at shapes `(2,2,1)`, `(2,2,2)`, `(3,2,2)`; 200 random tables each at
  `(3,3,2)`, `(2,3,3)`, `(4,3,2)`, `(3,3,3)`, seed 20260913). On every one:
  safety faithfulness, query faithfulness, and
  `abstract cost == restricted-geometry cost` — including the **4142 infeasible**
  instances where both are `None`, and the **4970 feasible** ones. The
  unrestricted-geometry cost was never larger than the abstract cost.
- **Z4** — `badDecision`: abstract 1, restricted 1, unrestricted **0**.
- **Z5** — `noTest`: abstract INFEASIBLE, restricted INFEASIBLE, unrestricted **1**.
- **Z6** — unrestricted geometry with promise `|W| ≤ s`: cost `= s` exactly for
  every `m = 2..6`, `s = 0..m-1` (30 configurations).
- **Z7** — dense family `m = 2..7`: pairwise incompatibility verified, geometry cost
  `= m-1` verified, counting bound `|family| ≤ 2^depth` verified, and the
  cost-preservation of the bit-test encoding verified, giving the `m-1` vs
  `ceil(log2 m)` gap tabulated in Section 3.

## 6. LIST OF REPO CLAIMS THAT MUST BE NARROWED (the reduction holds)

1. Any claim that the multi-tip support geometry + physical membership queries is
   a **new** problem class. It is finite decision-region determination
   (Javdani et al. 2014 / Golovin-Krause-Ray 2010) under a decision/query-set
   restriction, at identical worst-case zero-error cost (`cost_preserving`).
2. Any claim that "adding a witness to `selectedRadius`" yields a theoretical
   advantage. It is a realization of the known problem; add the sentence
   "no theoretical advantage from the geometry" wherever this is presented.
3. `LeanSupportUnboundedObstructionV1` / `LeanSupportObstructionQueryOrderV1`
   claims about "unbounded obstruction order": these remain true as stated about
   obstruction ORDER, but **must not** be read as difficulty claims. The zero-error
   adaptive query cost of the unrestricted geometry is exactly `W.card`
   (`unrestricted_exact_cost`), so obstruction order does not control cost — which
   `obstruction_order_determines_neither_bound` in that module already says, and
   which should be quoted whenever the obstruction order is mentioned.
4. `LeanSupportAdaptiveQuerySeparationV1.adaptive_depth_lower/attained` (`m-1` for
   the dense family): true, but must be stated as a bound **for the fixed
   membership primitive on `m` coordinates**, not as intrinsic difficulty of the
   decision problem — Z7 shows the same decision problem falls to `ceil(log2 m)`
   once `ceil(log2 m)` coordinates are added.
5. `LeanSupportQueryErrorTradeoffV1` (and the Goi-5 package below): the counting
   argument there is an auxiliary theorem, not a headline novelty. Header and
   report must say so (done in the Goi-5 package).
6. The Query-chain "reference control learns interactions" narrative: see Section 4
   — direct collision with Bshouty-Feldman 2002; must be restated as constrained
   references / decision-theoretic conclusion / exact constants, or dropped.

## 7. WHAT THIS PACKAGE DOES NOT ESTABLISH

- Zero-error worst-case DETERMINISTIC depth only. No prior, no expected cost, no
  randomized trees, no approximation ratios, no noise, no many-valued tests.
- `cost_preserving` is an equality of sets of achievable depths, not an `IsLeast`
  statement; the sets may be empty (that is exactly `query_restriction_necessary`).
- The encoding inflates the coordinate count from `nD` to `nD+nE`. No
  dimension-preserving reduction is claimed.
- `incompatible_worlds_lower` assumes PAIRWISE incompatibility; nothing is claimed
  for families that merely lack a single common safe decision.
- Section 3's assessment of the three candidate restricted geometries is a SKETCH
  except for the counting bounds, which are Lean receipts, and for the cyclic-window
  exact law, which is a pre-existing receipt (`nonadaptive_exact`).
- Section 4 is a literature audit, not a theorem. No Lean receipt asserts anything
  about Bshouty-Feldman.
- The probe's sweeps are exhaustive only at shapes `(2,2,1)`, `(2,2,2)`, `(3,2,2)`;
  the other four shapes are random samples of 200 tables each. Nothing is claimed
  for larger shapes. `m > 7` was NOT checked for the dense-family gap (the
  version-space DP is exponential in the number of worlds).
