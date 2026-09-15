"""Read-only proof/evidence check, then write a machine-readable closure ledger.
This is not a clean corpus build. Imports use the existing local dependency build.
"""
import hashlib,json,re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
LEAN=ROOT/'work/p13_conjectures'
OUT=ROOT/'research/high_risk_20260910'
MODULES=['LeanSupportCardinalityQueryLawV1','LeanStructuralOrderedRadiusStepV1',
 'LeanStructuralOrderedRadiusChainV1','LeanPrefixBudgetMetricCoverV1',
 'LeanStructuralUnbalancedToleranceUpperV1','LeanStructuralRadiusReindexV1',
 'LeanStructuralStaircaseToleranceLowerV1','LeanStructuralNormalizedToleranceLawV1',
 'LeanD6DiscoveryPathLawV1','LeanD6DiscoveryVectorCertificateV1','LeanDyadicCertifiedStoppingV1',
 'LeanD6DiscoveryStoppingV1','LeanD6ActualDiscoveryBridgeV1','LeanD6DiscoveryGeometryV1',
 'LeanD6RepeatedDiscoveryV1','LeanD6RevalidationRegretBridgeV1',
 'LeanD6RecommendationMeasurabilityV1','LeanFiniteAllocationTrackerV1',
 'LeanD6AllocationTrackingStabilityV1','LeanD6ConstructiveTrackingV1',
 'LeanD6CyclicOptimalV1','LeanD6IntegerBlockAllocationV1',
 'LeanStructuralStaircaseToleranceCurveV1','LeanD6CyclicMeanSquareV1',
 'LeanD6UniformPhaseThreeRemainderV1','LeanD6RandomLabelPhaseRegretV1',
 'LeanD6DiscoveryWorldRecommendationV1','LeanD6ActualUnknownLabelPhaseRiskV1',
 'LeanD6GrowingPhaseThreeRemainderV1','LeanD6LocalCurvatureLimitV1',
 'LeanStructuralActualChi4KernelV1','LeanD6PairContractionKernelV1',
 'LeanD6GrowingUnknownLabelPhaseRiskV1','LeanD6CriticalScaleRemainderV1',
 'LeanD6EpochLossMeasurabilityV1','AxiomAuditNoveltyChainsV1',
 'LeanD6EpochMarginalLawV1','LeanD6MultiEpochCompositionV1',
 'LeanD6WeightedEpochCompositionV1','LeanD6UniformDiscoveryThresholdV1',
 'LeanD6ExpectedStoppingEpochV1','LeanD6ActualMultiEpochRiskV1',
 'LeanD6EpochBudgetArithmeticV1','LeanD6ActualDoublingEpochRiskV1',
 'LeanFiniteAllocationTrackerMeasurableV1','LeanD6SharpMarginSteeringV1',
 'LeanD6MarginSensitiveExchangeV1','LeanD6SharpMarginThresholdV1',
 'LeanD6QueryWidthInformationV1','LeanFunctionalPairFlipCostV1',
 'LeanD6SameResponseMarginLossV1','LeanD6SameResponseMarginGameV1',
 'LeanD6SameResponseMarginCertificateV1','AxiomAuditEpochReferenceV1',
 'AxiomAuditD6SameResponseMinimaxV1']

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
 rows=[]
 for name in MODULES:
  source=LEAN/(name+'.lean');log=LEAN/(name+'.compile.log');olean=LEAN/(name+'.olean')
  text=log.read_text();assert ': error' not in text and 'sorryAx' not in text,(name,text)
  assert olean.exists() and olean.stat().st_mtime_ns>=source.stat().st_mtime_ns, name
  audits=[]
  for n,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S):
   axioms=[a.strip() for a in ax.split(',') if a.strip()]
   assert set(axioms)<= {'propext','Classical.choice','Quot.sound'},(name,n,axioms)
   audits.append(dict(name=n,axioms=axioms))
  assert audits,name
  rows.append(dict(module=name,source=str(source),source_sha256=sha(source),olean=str(olean),
      olean_sha256=sha(olean),compile_log=str(log),compile_log_sha256=sha(log),audits=audits))
 exp=[]
 for file in ['structural_order_statistic_cover.json','d6_fixed_gap_discovery.json','d6_revalidation_epochs.json','allocation_tracker.json','d6_integer_block_evidence.json','d6_phase_three_plugin_risk.json']:
  p=OUT/file;x=json.loads(p.read_text());exp.append(dict(path=str(p),sha256=sha(p),cells=len(x['rows']),evidence_class=x['evidence_class']))
 result=dict(scope='Selected modules compiled with existing local dependencies; this is NOT a clean full-corpus build.',
   closed=['Structural normalized O(1/epsilon) upper without balance and matching-order staircase lower',
    'Support exact cardinality-constrained zero-error membership query cost s for s<m',
    'Standalone D6 discovery: actual legal query means, canonical Gaussian paths, a.s. termination, finite expected query cost, anytime geometric error',
    'Repeated D6 discovery: eventual correct certification a.s.; finite expected total length of wrong-label epochs',
    'Actual D6 oracle-regret contribution of wrong-label epochs bounded',
    'Measurable unique certified label recommendation including fallback',
    'Explicit legal query tracking schedule, realized-count identity, and deterministic tracking regret term',
    'Entire normalized staircase tolerance curve for all r>0: r below 1/(2r), one at and above',
    'Cyclic design attains fixed nonadaptive A-invariant linear off-query variance lower bound',
    'Optimal integer budget split within the two named cyclic/three-group block designs',
    'Actual A-free cyclic estimator mean-square control after clipping',
    'Uniform finite phase-III quadratic regret constant for fixed q',
    'One-epoch actual unknown-label phase-III recommendation regret, with both estimation and wrong-label contributions',
    'Explicit phase-III remainder <=64/q^2 for q>=8, connected to actual unknown-label one-epoch risk',
    'Full quadratic matching remainder is O(q^-3) when epsilon=O(q^-3/2), including nonvanishing local curvature',
    'Local curvature sandwich and matching coefficient bounds',
    'Chi4 and pair-contraction headline replacements with kernel-only audited dependencies',
    'Measurability and integrability of the actual one-epoch decoder/cyclic loss',
    'Finite multi-epoch actual product-law composition with shared discovery and explicit weighted recommendation risk',
    'Doubling recommendation loss bound with separate exact acquisition cost; no total-regret O(log T) claim',
    'Finite allocation tracker is measurable and causal in the target sequence',
    'Universal product-reference Top-C optimality at margin >=2 delta, with actual corner witnesses arbitrarily below two',
    'Same-nuisance uniform adjacent-swap KL average bounded by query width; not an individual-pair or optimized-nuisance bound',
    'Exact unrestricted two-score Gaussian perturbation cost; shared-F feasibility not included',
    'Actual same-Q margin family loss and primal/dual finite-world certificates; references here are corner'],
   open=['Adaptive matching TOTAL regret for unknown A','Sharp growing-q tracking/remainder constants; learning the phase interval and crossing its boundaries',
    'Termination and expected Gamma rate of the full adaptive allocation algorithm','Matching discovery lower bound and uniform growing-q transition'],
   toolchain=(LEAN/'lean-toolchain').read_text().strip(),
   lake_manifest_sha256=sha(LEAN/'lake-manifest.json'),
   supporting_sources=[dict(path=str(ROOT/'scripts'/n),sha256=sha(ROOT/'scripts'/n)) for n in
     ['verify_structural_order_statistic_cover.py','run_d6_nuisance_free_discovery.py',
      'run_d6_fixed_gap_discovery.py','run_d6_revalidation_epochs.py','verify_allocation_tracker.py',
      'run_d6_integer_block_evidence.py','run_d6_phase_three_plugin_risk.py',
      'analyze_functional_censoring_pairing.py']],
   functional_analysis=dict(path=str(OUT/'functional_paired_censoring_v2.json'),sha256=sha(OUT/'functional_paired_censoring_v2.json')),
   modules=rows,experiments=exp)
 target=OUT/'chain_closure_manifest.json';target.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(dict(modules=len(rows),audit_prints=sum(len(r['audits']) for r in rows),manifest=str(target))))
if __name__=='__main__':main()
