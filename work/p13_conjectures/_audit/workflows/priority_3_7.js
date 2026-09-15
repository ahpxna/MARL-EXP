export const meta = {
  name: 'cigamf-priority-3-7',
  description: 'Derive + adversarially verify the six assigned research packages (D07 limit, k-scaling, A07 sharpness, Structural, Support, Query, MASTER)',
  phases: [
    { title: 'Derive', detail: 'one agent per assigned package' },
    { title: 'Refute', detail: 'two independent skeptics per package' },
  ],
}

const REPO = '/Users/phanan/cig-amf-main'

const RULES = `
You are a worker on a formal-research project at ${REPO}. A supervisor audit has documented NINE prior incidents where a worker stated a claim BROADER than what was actually checked. That is the failure mode you must avoid above all else.

HARD RULES
- Lean modules live in work/p13_conjectures/*.lean with compile receipts *.compile.receipt.json. A claim counts as PROVED only if a module compiles exit 0 AND every '#print axioms' line shows only {propext, Classical.choice, Quot.sound}. Anything else is at best NUMERICAL EVIDENCE or SKETCH.
- Do NOT edit any existing .lean file. Do NOT run lean/lake compiles (slow; the main session owns the toolchain). You MAY read .lean files freely.
- You MAY write NEW python probes. Put them at ${REPO}/scripts/<tag>_*.py where <tag> is your dimension tag. Use python3. Prefer fractions.Fraction or mpmath for anything where floating point could decide the answer; if you use floats, report the residual.
- Write your findings file to ${REPO}/research/high_risk_20260910/<TAG>_FINDINGS_20260912.md and include a section titled "What this does NOT establish".
- Keep each probe under ~5 minutes of compute. If a sweep would be slower, shrink the grid and SAY SO in the artifact (no silent truncation).
- Before you attribute a phenomenon to a cause, check whether your filter could have removed the true cause. A check that can never return False is not a check.

NAVIGATION - this repo is mapped into a knowledge graph. Query it FIRST, grep only as a fallback. All commands are run from ${REPO}:
    python3 work/p13_conjectures/_audit/graphify/gq.py find <substr> [--type lean_theorem] [--file-substr X]
    python3 work/p13_conjectures/_audit/graphify/gq.py module <LeanModuleNameV1>   # imports, imported-by, every declaration with its line number
    python3 work/p13_conjectures/_audit/graphify/gq.py node <name>                # attributes + every in/out edge grouped by relation
    python3 work/p13_conjectures/_audit/graphify/gq.py deps <name> --depth 2       # what it depends on
    python3 work/p13_conjectures/_audit/graphify/gq.py rdeps <name> --depth 2      # who depends on it (use this before claiming something is unused)
    python3 work/p13_conjectures/_audit/graphify/gq.py file <path-substr>          # declarations in a file, in line order
    python3 work/p13_conjectures/_audit/graphify/gq.py path <a> <b>                # shortest connection between two declarations
  The Lean half (343 files, 4286 declarations, 21904 edges) is re-extracted deterministically today by lean_extract.py - no LLM. The Python half comes from graph.json (tree-sitter AST, built 2026-09-12 01:12). Every edge carries confidence EXTRACTED (written literally in the source), INFERRED (a short name resolved through exactly one namespace match) or AMBIGUOUS (several matches, deliberately never resolved to a guess). An INFERRED or AMBIGUOUS edge is a lead, not a fact. Use the graph to FIND things fast; then READ the actual source before you rely on any statement.

DELIVERABLE: exactly six things - statement, assumptions, nearest prior work, proof or counterexample, evidence with a certificate (the exact re-run command), and a keep/fix/drop decision. Report via the structured output tool.
`

const DIMENSIONS = [
  {
    tag: 'D07',
    label: 'D07 limit law t=tau/k',
    prompt: `${RULES}

YOUR PACKAGE: D07 - the quantitative t = tau/k limit of the D6 reference phase value.

WHAT IS ALREADY ESTABLISHED (do not redo). In the D6 reference instance (files LeanD6ReferenceResponseJoinV1.lean, LeanD6ReferenceCenteredCompensatedV1.lean, LeanD6ReferenceEndpointWorldsV1.lean, LeanD6ReferencePhaseValueV1.lean) with q >= 2, k = q+1, |A| = k, |others A j| = q, the physical parameters are exactly:
  b = slopeBval t A j = (q-1) * t * (1-t)^(2q)
  a = gateMass  t A j = (1-t)^(2q+1) + q * t * (1-t)^(2q)
  c = a - b = (1-t)^(2q)          <- exact algebraic identity, verify it
  p = rho - 2b,  r = 2a - rho,  e = min(a, 2b)
  phaseValueFull k p c e r = max(0, k*r - e) * (p*(k-1) + max(0, e-r)) / (4 * c * (k-1))
Region additionally assumes 0 <= t <= 1, 1 <= rho <= 2, and the strong condition 1 <= (q-1)*b.

MY CONJECTURED D07 STATEMENT (test it, do not assume it):
  With t = tau/k,  phaseValueFull / k  ->  Gamma(tau,rho) = (2(1+tau)e^(-2tau) - rho) * (rho - 2 tau e^(-2tau)) * e^(2tau) / 4,
  with an O(1/k) remainder that is UNIFORM for tau in [tau_min, tau_max] as long as the limit stays strictly inside the active phase (r_infinity = 2(1+tau)e^(-2tau) - rho bounded away from 0).
  Sanity anchor: at tau = 0 this must reduce to the already-proved corner law phaseValueFull k rho 1 0 (2-rho) = k*rho*(2-rho)/4 (theorem corner_value in LeanD6ReferencePhaseValueV1.lean).

WHAT I NEED FROM YOU
1. Confirm or refute c = (1-t)^(2q) exactly (symbolically, e.g. sympy or by hand-checked Fraction arithmetic at many (q,t)).
2. Verify the rate law numerically at high precision (mpmath, >= 30 digits) over a grid of k (say 10..5000, geometric) x tau x rho. Report k * |phaseValueFull/k - Gamma| and check it stabilises to a constant (that is the O(1/k) claim). Estimate C(tau_max) empirically.
3. Find exactly WHERE the uniformity degrades as r_infinity -> 0 (approach the phase boundary rho -> 2(1+tau)e^(-2tau)). Give the observed blow-up law of the constant in terms of the margin.
4. The strong domain. Under t = tau/k, is 1 <= (q-1)*b eventually satisfied, and for which (k, tau)? Give the admissible tau window as a function of k and say whether it converges to a limit window. Remember: earlier grid scans found the FULL region (strong + c>0 + some admissible rho) is empty for q <= 7 and first inhabited at q = 8, t ~ 0.037818 - check whether that is consistent with tau = t*k ~ 0.34.
5. State the precise constants that a Lean proof would need: I intend to prove |(1-x)^n - exp(-n x)| <= n * (3/4) * x^2 for x in [0,1] (from |exp(z) - (1+z)| <= (3/4) z^2 for |z| <= 1 plus |A^n - B^n| <= n max(|A|,|B|)^(n-1) |A-B|), then compose. Check numerically that this chain actually yields a correct uniform O(1/k) bound with explicit constants for a, b, c and then for the value; report the composed constant and any step where the chain is too lossy.

Deliver the six things. Tag your files D07.`,
  },
  {
    tag: 'D06ALPHA',
    label: 'D06 scaling t=tau/k^alpha',
    prompt: `${RULES}

YOUR PACKAGE: does the D6 reference construction have more than one scale? Test t = tau / k^alpha for alpha in {1/2, 1, 3/2, 2, 5/2}.

CONTEXT. Same closed forms as the D07 package (derive/verify them yourself from work/p13_conjectures/LeanD6ReferenceResponseJoinV1.lean and LeanD6ReferenceCenteredCompensatedV1.lean):
  b = (q-1) t (1-t)^(2q),  a = (1-t)^(2q+1) + q t (1-t)^(2q),  c = a - b,  p = rho - 2b,  r = 2a - rho,  e = min(a,2b),
  k = q+1,  phaseValueFull k p c e r = max(0, k r - e)(p(k-1) + max(0, e-r))/(4 c (k-1)).
Heuristic from the slopes: with alpha > 1 one expects b ~ tau k^(1-alpha) and (k-2) b ~ tau k^(2-alpha), suggesting alpha = 1 is where reference mass changes law and alpha = 2 is where the SUFFICIENT condition strong: 1 <= (q-1) b can fail.

THE TRAP YOU MUST NOT FALL INTO. The supervisor has explicitly warned: if only the sufficient condition 'strong' fails while the actual minimax value is unchanged, that is NOT a phase transition and must NOT be described as one. So:
1. For each alpha, compute the limit law of a, b, c, p, r, e and of phaseValueFull (or of phaseValueFull/k, or whatever the right normalisation is - find it, do not assume it is k).
2. For each alpha, determine for which (k, tau, rho) the region hypotheses actually hold.
3. CRUCIAL: outside the strong domain, compute the ACTUAL minimax value directly from the full count loss rather than from the closed-form phaseValueFull. The relevant definitions are in work/p13_conjectures/LeanD6ReferenceFullCountLossV1.lean, LeanD6ReferenceLegalCountMinimumV1.lean, LeanD6ReferencePhaseRegretBridgeV1.lean and LeanD6ReferenceEndpointWorldsV1.lean (regret M A S = actualLoss A T S j rho t - legalMinimum A T j rho t; worlds q j = (positiveGround q j).powersetCard (q+1)). Build a small exact LP/enumeration minimax for small q (q = 2..5 say, where the world family is enumerable) and compare against the closed form INSIDE the strong domain (as a control, they must agree) and OUTSIDE it (the real question). Report whether the minimax value itself changes character or whether only the closed-form derivation's sufficient condition lapses.
4. Report an honest verdict: how many genuine scales does this construction have?

Deliver the six things. Tag your files D06ALPHA.`,
  },
  {
    tag: 'A07',
    label: 'A07 local value sharpness',
    prompt: `${RULES}

YOUR PACKAGE (supervisor priority 3): sharpen the adaptive local value bound. The current bound is too loose to claim a matching rate, and the supervisor wants the LOOSENESS of the upper bound fixed - this is not a lower-bound impossibility.

WHAT IS CURRENTLY THERE. Grep the repo for marginModulus and for the cyclic confidence sequence. Relevant modules (find the exact ones yourself): LeanD6LocalOracleRegretV1, LeanD6OracleValueStabilityV1, LeanD6LocalCurvatureLimitV1, LeanD6CyclicConfidenceSequenceV1, LeanD6CyclicValueConfidenceV1, LeanD6CyclicMeanSquareV1, LeanD6AdaptiveOracleRegretV1, LeanD6FrozenQuadraticBoundV1, LeanD6PhaseShiftLipschitzV1.
The current chain uses marginModulus(q) = 2q(2q+1) as a uniform Lipschitz modulus and Var(muhat) = (2q+1)/(L q^4), giving an error term of order sqrt(q/L * log(1/delta)). Composing these as a SUFFICIENT condition for an absolute target of order q^(-2) demands L of order q^5 (ignoring logs), and raw queries carry a further factor (2q+1). That is the looseness.

WHAT I NEED
1. Read the actual Lean statements and report precisely which constant enters where - do not trust my summary, verify it against the source, and correct me if the exponents are different.
2. Diagnose the loss. Candidates the supervisor named: (i) the value excess is QUADRATIC in the parameter error inside a phase rather than Lipschitz, (ii) there is a kink law near the phase boundary that the uniform modulus ignores, (iii) oracle-specific cancellation, (iv) a direct decision-regret bound can replace the uniform Lipschitz step entirely.
   WARNING the supervisor issued: do not confuse curvature in the ALLOCATION WEIGHTS with curvature in mu. They are different variables; state which one each of your bounds is in, with units.
3. Produce a sharper, explicitly-constant bound. Support it with a numerical probe that (a) measures the true decision regret as a function of parameter error on the actual phase value formula phaseValueFull (definitions in LeanD6ReferencePhaseValueV1.lean, closed forms a,b,c,p,r,e as in the D6 reference instance - derive them), and (b) compares the true regret against both the current bound and your proposed bound over a grid, reporting the ratio.
4. Say honestly what exponent in L your sharper bound needs, and whether that is enough to close a matching rate or only narrows the gap.

Deliver the six things. Tag your files A07.`,
  },
  {
    tag: 'STRUCT',
    label: 'Structural sharp constant',
    prompt: `${RULES}

YOUR PACKAGE (supervisor priority 4): Structural - an exact small packing/covering computation that either picks out a sharp constant or shows the gap is real.

CONTEXT. The staircase exact curve and the normalized-tolerance quantifier question are already CLOSED (LeanStructuralStaircaseToleranceCurveV1, LeanStructuralToleranceQuantifiersV1 etc.) - do NOT redo them, and do NOT chase 'unbounded at fixed epsilon', which the supervisor has ruled out. The open item is the gap between the universal upper bound and the worst-case lower bound for the prefix-cover / menu problem. Relevant modules to read: LeanStructuralPrefixCoverUniversalUpperV1, LeanStructuralPrefixCoverDimensionV1, LeanStructuralPrefixCoverChi3WitnessV1, LeanStructuralPrefixCoverWitnessesV1, LeanStructuralUnboundedPrefixCoverFamilyV1, LeanPrefixBudgetMetricCoverV1, LeanStructuralMinimumTransversalWidthV1, LeanStructuralOrderedRadiusChainV1.

WHAT I NEED
1. Read the source and state the actual upper and lower bounds currently proved, with their exact normalisation and epsilon domain. Report the numeric gap.
2. Run an EXACT small set-cover computation on the actual ranking instances the construction produces (exact integer/rational arithmetic, exhaustive or ILP with a certificate, small sizes only). Then look for an incompatibility PACKING that certifies a matching lower bound on those same instances.
3. Decide between the two branches: (a) the constant can be pinned sharp, or (b) an instance-dependent parameter computable from the radius / cancellation / budget witnesses governs it.
   ELIMINATION CRITERIA the supervisor set: if your new parameter is just the optimal menu size under another name, or if the result is a known general covering lemma, the direction is DEAD - say so and drop it.
4. Nearest prior to check: incremental/ordered optimization where one ordering serves many cardinalities (e.g. Bienkowski et al. on incremental optimization). State precisely what would be different here - additive error, normalisation, cancellation - or admit it is not different.

Deliver the six things. Tag your files STRUCT.`,
  },
  {
    tag: 'SUPPORT',
    label: 'Support epsilon-safety law',
    prompt: `${RULES}

YOUR PACKAGE (supervisor priority 5): Support - one heterogeneous epsilon-safety family with a candidate matching law.

CONTEXT. Already closed and NOT to be redone: the obstruction-order vs query-depth independence (LeanSupportObstructionQueryOrderV1, 17 clean axiom audits) and the cardinality query law (LeanSupportCardinalityQueryLawV1). Sparse/dense constructions are to be used only as regression cases. Other modules to read: LeanSupportPhysicalQueryContractV1, LeanSupportMultiTipGeometryV1, LeanSupportAdaptiveQuerySeparationV1, LeanSupportCriticalIdentificationV1, LeanSupportFibreSufficiencyV1, LeanSupportPartialTestCoverV1, LeanSupportThreeWorldWitnessV1, LeanSupportGeometryV4.

THE TASK. Keep the physical membership query, but relax zero-safety to selectedRadius <= epsilon. Use heterogeneous multi-tip supports or correlated supports so that the safe sets genuinely MOVE with epsilon. Find the phase curve of the optimal query depth as a function of epsilon, with a constructive upper bound and an adversary lower bound that match.
REQUIREMENT the supervisor set: the family must go BEYOND the already-proved cardinality law - a renaming of it does not count. Say explicitly which part of your family is not covered by the cardinality law and why.
Nearest prior to position against: overlapping decision regions / hyperedge cutting for decision-region identification (e.g. Javdani et al. on near-optimal bayesian active learning with hyperedge cutting). Novelty must be in the actual geometry and a new quantitative law, not in the framework.

Build a small exact computational probe (exhaustive optimal decision-tree depth over the family at small sizes, exact arithmetic) that traces the depth-vs-epsilon curve and tests your conjectured matching law.

Deliver the six things. Tag your files SUPPORT.`,
  },
  {
    tag: 'QUERY',
    label: 'Query reachable panel',
    prompt: `${RULES}

YOUR PACKAGE (supervisor priority 6): Query - a reachable, nonconstant panel and an exact restricted-information decoder.

THE SUPERVISOR'S EXPLICIT ORDERING (follow it; the first step is NOT adding seeds):
1. Collect trajectories with a FIXED collection policy.
2. Keep every count: generated / reachable / filtered / constant / evaluable. Inclusion accounting must be complete - a missing count is the classic way this kind of result becomes unfalsifiable.
3. Find PAIRED states that share a representation but differ in continuation target.
4. Compute the restricted-information OPTIMAL decoder exactly (not an approximation, not a trained model - exact over the restricted information).
5. Buy extra features/queries from an executable catalog.
6. Prove and measure the repair cost.

CONTEXT. The existing distance-horizon fixtures are POSITIVE CONTROLS only; they do not substitute for a natural panel - do not present them as one. Read: work/p13_conjectures/LeanQueryIdentifiabilityVerifierV1.lean, LeanQueryRepresentationNecessityV1.lean, LeanQuerySufficiencyQuantitativeV1.lean, LeanQuerySemanticCompilerV1.lean, LeanQuerySufficiencyV4.lean, plus any python under scripts/ or observatory/ matching query/identifiability/transfer (e.g. scripts/run_external_query_transfer.py, scripts/analyze_external_query_transfer.py).

HONEST VERDICT REQUIRED: the supervisor has said that if the result reduces to 'the representation loses information so you need more features', it is NOT strong enough to stand as its own paper and should become an application of the Support paper. Say which of those two it is, based on what you actually measure.

Deliver the six things. Tag your files QUERY.`,
  },
  {
    tag: 'MASTER',
    label: 'MASTER fixed-world acquisition',
    prompt: `${RULES}

YOUR PACKAGE (supervisor priority 7): MASTER - build a FIXED-WORLD acquisition model, and stop calling t a price.

THE DEFECT TO FIX. The current 'price of evidence B' artifact takes the smallest t on a grid at which the minimax value is 0 and calls that a price. That is invalid for two reasons: (i) t is not a number of queries, an amount of money, or an amount of time; (ii) the sweep re-compensates the family as t changes, so it is not one fixed world being measured. The artifact therefore certifies a piece of D6 algebra and does NOT close the acquisition gate. Find the artifact and the script that produced it (grep research/ and scripts/ for master certificate / acquisition / price of evidence, e.g. scripts/run_master_certificate_utility.py, scripts/analyze_master_certificate_utility.py) and confirm or correct this diagnosis from the source.

WHAT THE CORRECT MODEL MUST HAVE (supervisor's specification). Hold F_{A,t0} FIXED. Let a query choose a reference t1, but only if you can state: the response law, the noise, the cost, and the coordinate/query actually observed. No re-compensation of F when t1 changes. The target theorem is: there is a floor under the old reference, and the minimum COST to break that floor is X.
Read work/p13_conjectures/LeanMasterReferenceUncertaintyV1.lean, LeanD6AcquisitionBenchmarkV1.lean, LeanD6CostAwarePAECCompletionV1.lean, LeanD6PAECCostAwareAdapterV1.lean and the D6 reference modules for the response law.

DROP CRITERION the supervisor set: if changing the reference is NOT executable inside the observation model, then the acquisition direction must be DROPPED and kept only as a sensitivity theorem. Decide this honestly and say which.
Nearest prior to position against: cost-aware best-arm identification (e.g. Kanarios, Zhang, Ying 2024). A generic cost-aware result is not novel; any contribution must be a reference-contrast law specific to this construction.

Deliver the six things. Tag your files MASTER.`,
  },
]

const FINDING_SCHEMA = {
  type: 'object',
  properties: {
    dimension: { type: 'string' },
    statement: { type: 'string', description: 'The precise claim, stated no broader than what was actually checked' },
    assumptions: { type: 'array', items: { type: 'string' } },
    nearest_prior: { type: 'string' },
    proof_or_counterexample: { type: 'string', description: 'The actual argument or the actual counterexample, with numbers' },
    evidence_kind: { type: 'string', enum: ['PROVED', 'NUMERICAL EVIDENCE', 'SKETCH', 'NONE'] },
    evidence_certificate: { type: 'string', description: 'What was checked, at what precision, over what grid, with the observed residuals' },
    rerun_command: { type: 'string' },
    artifact_path: { type: 'string' },
    does_not_establish: { type: 'array', items: { type: 'string' } },
    decision: { type: 'string', enum: ['keep', 'fix', 'drop'] },
    key_numbers: { type: 'string' },
  },
  required: ['dimension', 'statement', 'assumptions', 'nearest_prior', 'proof_or_counterexample', 'evidence_kind', 'does_not_establish', 'decision'],
}

const VERDICT_SCHEMA = {
  type: 'object',
  properties: {
    refuted: { type: 'boolean', description: 'true if the claim is wrong OR stated more broadly than the evidence supports' },
    overclaim: { type: 'boolean' },
    specific_error: { type: 'string' },
    corrected_statement: { type: 'string' },
    checks_run: { type: 'string' },
  },
  required: ['refuted', 'overclaim', 'specific_error'],
}

const LENSES = [
  {
    key: 'recompute',
    ask: `Independently RECOMPUTE the central quantity from the primary source (the .lean definitions and/or your own fresh python, written from scratch - do not reuse the worker's script except to re-run their stated command as a cross-check). If the numbers do not reproduce, refuted = true.`,
  },
  {
    key: 'scope',
    ask: `Attack the SCOPE. Is the statement broader than what was actually checked - in the population sampled, the parameter range, the tie/degenerate cases, or the arithmetic precision? Did any filter in the worker's method make the claimed conclusion unfalsifiable (a check that cannot return False)? Does the 'What this does NOT establish' section actually cover the real limitations? An overclaim counts as refuted = true even when the arithmetic is right.`,
  },
]

phase('Derive')
const results = await pipeline(
  DIMENSIONS,
  d => agent(d.prompt, { label: `derive:${d.tag}`, phase: 'Derive', schema: FINDING_SCHEMA }),
  (finding, d) => {
    if (!finding) return null
    return parallel(LENSES.map(lens => () =>
      agent(`${RULES}

You are an adversarial verifier at ${REPO}. Your default is REFUTED. Only set refuted = false if you positively confirmed the claim yourself.

A worker returned this finding for package ${d.tag}:

${JSON.stringify(finding, null, 2)}

YOUR LENS: ${lens.ask}

Do the work: read the primary sources, re-run or re-derive, and report. Be specific - name the file, the line, the number, the grid point where it fails. If it survives your lens, say exactly what you checked so the survival means something. Do not write any new file except a scratch probe under ${REPO}/scripts/verify_${d.tag.toLowerCase()}_${lens.key}.py if you need one.`,
        { label: `refute:${d.tag}:${lens.key}`, phase: 'Refute', schema: VERDICT_SCHEMA })
    )).then(votes => ({ dimension: d.tag, finding, votes: votes.filter(Boolean) }))
  },
)

const out = results.filter(Boolean).map(r => {
  const refuted = r.votes.filter(v => v.refuted).length
  const overclaim = r.votes.filter(v => v.overclaim).length
  return {
    dimension: r.dimension,
    survived: refuted === 0,
    refuted_votes: refuted,
    overclaim_votes: overclaim,
    finding: r.finding,
    objections: r.votes.filter(v => v.refuted || v.overclaim).map(v => ({ error: v.specific_error, corrected: v.corrected_statement })),
    confirmations: r.votes.filter(v => !v.refuted && !v.overclaim).map(v => v.checks_run),
  }
})
log(`packages: ${out.length}; survived clean: ${out.filter(o => o.survived).length}`)
return out
