#!/usr/bin/env bash
set -u

REPO=/Users/phanan/cig-amf-main
BASE=/private/tmp/cig-amf-lean-v7-runtime/baseline/cig_amf_lean_v6_chain_d6_topc_final/work/p12
BUILD=/private/tmp/cig-amf-lean-v7-runtime/fresh-build-20260830
LOG=$REPO/compile_logs/v7
LEAN=/private/tmp/cig-amf-lean-v7-runtime/lean-dist/lean-4.34.0-rc2-darwin_aarch64/bin/lean
MATHLIB=/private/tmp/cig-amf-lean-v7-runtime/mathlib4

mkdir -p "$BUILD" "$LOG"

BASELINE=(
  LeanSupportGeometryV4
  LeanReferenceFidelityV4
  LeanReferenceKernelV4
  LeanPairwiseMasterV4
  LeanFunctionalBoundaryV4
  LeanStructuralRankabilityV4
  LeanProductSurrogateV4
  LeanQuerySufficiencyV4
  LeanAuxiliaryBH6StructuralV4
  LeanStructuralGeometryWitnessesV4
  LeanFunctionalAuxV4
  LeanProductMixedDifferenceV4
  LeanQueryRemovalV4
  LeanFunctionalRankingV6
)

EXTENSIONS=(
  LeanPairwiseBoxRegretV1
  LeanCertificateProbabilityV1
  LeanQuerySufficiencyQuantitativeV1
  LeanStructuralRankabilityCharacterizationV1
)

for module in "${BASELINE[@]}"; do
  cp "$BASE/$module.lean" "$BUILD/$module.lean"
done
for module in "${EXTENSIONS[@]}"; do
  cp "$REPO/work/p12/$module.lean" "$BUILD/$module.lean"
done

LEAN_PATH_VALUE="$MATHLIB/.lake/packages/Cli/.lake/build/lib/lean:$MATHLIB/.lake/packages/batteries/.lake/build/lib/lean:$MATHLIB/.lake/packages/Qq/.lake/build/lib/lean:$MATHLIB/.lake/packages/aesop/.lake/build/lib/lean:$MATHLIB/.lake/packages/proofwidgets/.lake/build/lib/lean:$MATHLIB/.lake/packages/importGraph/.lake/build/lib/lean:$MATHLIB/.lake/packages/LeanSearchClient/.lake/build/lib/lean:$MATHLIB/.lake/packages/plausible/.lake/build/lib/lean:$MATHLIB/.lake/build/lib/lean:/private/tmp/cig-amf-lean-v7-runtime/lean-dist/lean-4.34.0-rc2-darwin_aarch64/lib/lean:$BUILD"

RESULTS="$REPO/ACTIVE_COMPILE_RESULTS_V7.tsv"
printf 'module\tclass\texit_code\tduration_seconds\tsource_sha256\tolean_sha256\n' > "$RESULTS"

overall=0
compile_one() {
  module=$1
  class=$2
  started=$(date +%s)
  (cd "$BUILD" && LEAN_PATH="$LEAN_PATH_VALUE" "$LEAN" -o "$module.olean" "$module.lean") \
    > "$LOG/$module.log" 2>&1
  code=$?
  ended=$(date +%s)
  source_sha=$(shasum -a 256 "$BUILD/$module.lean" | awk '{print $1}')
  if [ -f "$BUILD/$module.olean" ]; then
    olean_sha=$(shasum -a 256 "$BUILD/$module.olean" | awk '{print $1}')
  else
    olean_sha=MISSING
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$module" "$class" "$code" "$((ended-started))" "$source_sha" "$olean_sha" \
    >> "$RESULTS"
  printf '%s %s exit=%s seconds=%s\n' "$class" "$module" "$code" "$((ended-started))"
  if [ "$code" -ne 0 ]; then
    overall=1
  fi
}

for module in "${BASELINE[@]}"; do
  compile_one "$module" baseline
done
for module in "${EXTENSIONS[@]}"; do
  compile_one "$module" extension
done

exit "$overall"
