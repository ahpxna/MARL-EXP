#!/usr/bin/env bash
# Actual-information, deterministic local-risk and Gaussian probability foundations.
# Requires the upstream allocation bridge artifacts. Audit existing artifacts with --audit-existing.
# Anytime error correctness is proved; expected stopping sample complexity is still open.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../work/p13_conjectures"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
if [[ "${1:-}" != "--audit-existing" ]]; then
  for module in LeanD6PhaseTestingInformationV1 LeanD6PhaseBoundaryRegretV1 LeanD6AllocationPhaseThreeCoreV1 LeanD6AllocationPhaseThreeParametersV1 LeanD6FiniteRiskLowerV1 LeanD6GaussianQueryDominanceV1 LeanD6GaussianOverlapV1 LeanAdaptiveTranscriptKernelV1 LeanAdaptiveResourceMapV1 LeanD6AdaptiveTranscriptV1 LeanD6MovingNuisanceRegretV1 LeanD6AllocationRiskBridgeV1 LeanD6AllocationPhaseThreeFeasibleV1 LeanD6PhaseThreePrimalV1 LeanD6PhaseThreeDualV1 LeanD6PhaseThreeSharpV1 LeanD6LabelInformationV1 LeanD6AdaptiveLikelihoodV1 LeanD6ProfileStoppingGeometryV1 LeanD6GaussianMixtureIntegralV1 LeanD6AdaptiveMixtureRiskV1 LeanD6LocalOracleRegretV1 LeanD6PartialLabelPhaseQueryV1 LeanGaussianSampleProductV1 LeanGaussianProductOverlapV1 LeanD6CenteredTranscriptV1 LeanGaussianProductDecisionRiskV1 LeanD6AdaptiveOracleRegretV1 LeanGaussianThresholdDecisionV1 LeanD6FrozenScalarAllocationV1 LeanD6FrozenOracleGapV1 LeanD6PhaseShiftLipschitzV1 LeanD6FrozenAllocationFeasibleV1 LeanGaussianThresholdRiskV1 LeanD6FrozenQuadraticBoundV1 LeanD6LocalMatchingAlgebraV1 LeanD6LocalMatchingDesignV1 LeanD6KnownLabelMatchingRiskV1 LeanD6BoundaryNondegenerateV1 LeanD6MatchingNeighborhoodV1 LeanD6ActualSampleMatchingV1 LeanD6StoppingGeometryBridgeV1 LeanD6ActualRecordLikelihoodV1 LeanD6FrozenMixtureCertificateV1 LeanD6AnytimeFrozenCertificateV1 LeanD6BlindPhaseBlocksV1 LeanD6BlindSaddleCertificateV1 LeanAdaptivePathLawV1 LeanAdaptivePathAbsorptionV1 LeanD6AnytimePathBridgeV1 LeanD6BlindPhaseDecisionV1 LeanD6AllocationPhaseThreePrimalV1 LeanD6AllocationPhaseThreeDualV1 LeanD6AllocationPhaseThreeGameV1 LeanStructuralScalarChi5KernelV1 LeanStructuralScalarChi5GeometryKernelV1; do
    lake env lean -o "$module.olean" "$module.lean" 2>&1 | tee "$module.compile.log"
  done
fi
python3 - <<'PY'
from pathlib import Path
import re
modules={'LeanD6PhaseTestingInformationV1': 7, 'LeanD6PhaseBoundaryRegretV1': 5, 'LeanD6AllocationPhaseThreeCoreV1': 4, 'LeanD6AllocationPhaseThreeParametersV1': 5, 'LeanD6FiniteRiskLowerV1': 2, 'LeanD6GaussianQueryDominanceV1': 5, 'LeanD6GaussianOverlapV1': 4, 'LeanAdaptiveTranscriptKernelV1': 3, 'LeanAdaptiveResourceMapV1': 2, 'LeanD6AdaptiveTranscriptV1': 5, 'LeanD6MovingNuisanceRegretV1': 5, 'LeanD6AllocationRiskBridgeV1': 3, 'LeanD6AllocationPhaseThreeFeasibleV1': 8, 'LeanD6PhaseThreePrimalV1': 6, 'LeanD6PhaseThreeDualV1': 7, 'LeanD6PhaseThreeSharpV1': 4, 'LeanD6LabelInformationV1': 3, 'LeanD6AdaptiveLikelihoodV1': 6, 'LeanD6ProfileStoppingGeometryV1': 5, 'LeanD6GaussianMixtureIntegralV1': 3, 'LeanD6AdaptiveMixtureRiskV1': 3, 'LeanD6LocalOracleRegretV1': 5, 'LeanD6PartialLabelPhaseQueryV1': 4, 'LeanGaussianSampleProductV1': 3, 'LeanGaussianProductOverlapV1': 4, 'LeanD6CenteredTranscriptV1': 2, 'LeanGaussianProductDecisionRiskV1': 2, 'LeanD6AdaptiveOracleRegretV1': 3, 'LeanGaussianThresholdDecisionV1': 3, 'LeanD6FrozenScalarAllocationV1': 4, 'LeanD6FrozenOracleGapV1': 4, 'LeanD6PhaseShiftLipschitzV1': 3, 'LeanD6FrozenAllocationFeasibleV1': 3, 'LeanGaussianThresholdRiskV1': 2, 'LeanD6FrozenQuadraticBoundV1': 2, 'LeanD6LocalMatchingAlgebraV1': 4, 'LeanD6LocalMatchingDesignV1': 4, 'LeanD6KnownLabelMatchingRiskV1': 3, 'LeanD6BoundaryNondegenerateV1': 3, 'LeanD6MatchingNeighborhoodV1': 2, 'LeanD6ActualSampleMatchingV1': 3, 'LeanD6StoppingGeometryBridgeV1': 5, 'LeanD6ActualRecordLikelihoodV1': 4, 'LeanD6FrozenMixtureCertificateV1': 8, 'LeanD6AnytimeFrozenCertificateV1': 4, 'LeanD6BlindPhaseBlocksV1': 5, 'LeanD6BlindSaddleCertificateV1': 5, 'LeanAdaptivePathLawV1': 3, 'LeanAdaptivePathAbsorptionV1': 3, 'LeanD6AnytimePathBridgeV1': 4, 'LeanD6BlindPhaseDecisionV1': 5, 'LeanD6AllocationPhaseThreePrimalV1': 6, 'LeanD6AllocationPhaseThreeDualV1': 6, 'LeanD6AllocationPhaseThreeGameV1': 3, 'LeanStructuralScalarChi5KernelV1': 0, 'LeanStructuralScalarChi5GeometryKernelV1': 11}
allowed={'propext','Classical.choice','Quot.sound'}
for module,count in modules.items():
    src=Path(module+'.lean'); obj=Path(module+'.olean'); log=Path(module+'.compile.log')
    assert obj.exists() and obj.stat().st_mtime_ns>=src.stat().st_mtime_ns, ('stale/missing',obj)
    assert log.exists() and log.stat().st_mtime_ns>=src.stat().st_mtime_ns, ('stale/missing',log)
    txt=log.read_text(); assert not re.search(r'\berror(?:\(|:)',txt),log
    rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",txt)
    assert len(rows)==count,(module,len(rows),count)
    for theorem,ax in rows:
        assert {s.strip() for s in ax.split(',') if s.strip()}<=allowed,(theorem,ax)
    for dep in re.findall(r'^import «([^»]+)»',src.read_text(),re.M):
        dp=Path(dep+'.olean')
        assert dp.exists() and obj.stat().st_mtime_ns>=dp.stat().st_mtime_ns,('stale dependency',obj,dp)
print(f'PASS: {sum(modules.values())} D6 probability / allocation / path and structural geometry audits; standard axioms only.')
print('Certified: fixed-A adaptive transcript simulation; phase III actual-query saddle value; co-moving nuisance regret; adaptive likelihood normalization; conditional profile certificate -> real geometry; N-sample exact Gaussian overlap; full adaptive actual-oracle regret lower bound; known-A constructive matching leading term with explicit quadratic remainder; nonempty feasible neighborhood for every q >= 3.')
print('Also certified: raw three-query blind phase law and finite-block error; canonical adaptive path marginals and a.s. absorption; anytime label and geometry error from the actual frozen certificate; support-geometric chi >= 5 with kernel arithmetic.')
print('Remaining: actual-query symmetric moment bridge and full blind saddle; unknown-A adaptive matching regret; expected stopping sample rate Gamma; joint dependence on q and label uncertainty. No compulsory full-label-discovery lower bound is claimed.')
PY
