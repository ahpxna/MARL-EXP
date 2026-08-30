#!/usr/bin/env bash
set -u

REPO=/Users/phanan/cig-amf-main
PARENT=/private/tmp/cig-amf-lean-v7-runtime/fresh-build-20260830
BUILD=/private/tmp/cig-amf-lean-v7-runtime/high-value-build-20260830
LOG=$REPO/compile_logs/high_value
LEAN=/private/tmp/cig-amf-lean-v7-runtime/lean-dist/lean-4.34.0-rc2-darwin_aarch64/bin/lean
MATHLIB=/private/tmp/cig-amf-lean-v7-runtime/mathlib4

mkdir -p "$BUILD" "$LOG"
cp "$PARENT"/*.lean "$PARENT"/*.olean "$BUILD"/

MODULES=(
  LeanMasterReferenceUncertaintyV1
  LeanD6SharpnessV1
  LeanD6WeightedInteractionV1
  LeanQueryRepresentationNecessityV1
  LeanReferenceIdentifiabilityV1
  LeanFunctionalCovarianceDesignV1
  LeanStructuralNegativeTaxonomyV1
)

for module in "${MODULES[@]}"; do
  cp "$REPO/work/p12/$module.lean" "$BUILD/$module.lean"
done

LEAN_PATH_VALUE="$MATHLIB/.lake/packages/Cli/.lake/build/lib/lean:$MATHLIB/.lake/packages/batteries/.lake/build/lib/lean:$MATHLIB/.lake/packages/Qq/.lake/build/lib/lean:$MATHLIB/.lake/packages/aesop/.lake/build/lib/lean:$MATHLIB/.lake/packages/proofwidgets/.lake/build/lib/lean:$MATHLIB/.lake/packages/importGraph/.lake/build/lib/lean:$MATHLIB/.lake/packages/LeanSearchClient/.lake/build/lib/lean:$MATHLIB/.lake/packages/plausible/.lake/build/lib/lean:$MATHLIB/.lake/build/lib/lean:/private/tmp/cig-amf-lean-v7-runtime/lean-dist/lean-4.34.0-rc2-darwin_aarch64/lib/lean:$BUILD"

RESULTS="$REPO/HIGH_VALUE_COMPILE_RESULTS.tsv"
printf 'module\texit_code\tduration_seconds\tsource_sha256\tolean_sha256\n' > "$RESULTS"
overall=0
for module in "${MODULES[@]}"; do
  started=$(date +%s)
  (cd "$BUILD" && LEAN_PATH="$LEAN_PATH_VALUE" "$LEAN" -o "$module.olean" "$module.lean") \
    > "$LOG/$module.log" 2>&1
  code=$?
  ended=$(date +%s)
  source_sha=$(shasum -a 256 "$BUILD/$module.lean" | awk '{print $1}')
  if [ -f "$BUILD/$module.olean" ]; then
    olean_sha=$(shasum -a 256 "$BUILD/$module.olean" | awk '{print $1}')
    cp "$BUILD/$module.olean" "$REPO/work/p12/$module.olean"
  else
    olean_sha=MISSING
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$module" "$code" "$((ended-started))" \
    "$source_sha" "$olean_sha" >> "$RESULTS"
  printf '%s exit=%s seconds=%s\n' "$module" "$code" "$((ended-started))"
  if [ "$code" -ne 0 ]; then overall=1; fi
done
exit "$overall"
