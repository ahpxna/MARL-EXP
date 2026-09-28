#!/bin/bash
# Full verification for the Paper A/B/C corpus.
# Acceptance: every module exit=0, err=0, sorryAx=0, no `sorry`, no `native_decide`,
# and the axioms of every audited theorem within {propext, Classical.choice, Quot.sound}.
# `sorryAx` is checked separately from the error count: an error ANYWHERE in a module
# makes Lean insert `sorryAx` into the downstream theorems of that module, so a clean
# error count alone does not establish that the theorems are proved.
#
# How it runs (rewritten 2026-09-23):
#
# * FROZEN.  Invoked from the working directory, this script copies itself, the lake
#   configuration and every module it will build into ../gate_runs/<RUN>/, hashes them, and
#   re-executes the COPY there.  Nothing the frozen run reads can change under it, and this
#   working copy may be edited as soon as the copy has started.
# * FROM SCRATCH.  The frozen directory has its own EMPTY .lake/build; only the Mathlib
#   packages are shared, read-only, through a symlink.  A module can therefore import only
#   an olean built in THIS run from THESE bytes.  The previous runner compiled seven modules
#   before one of their own imports (e.g. CEndpoint before CFamily) and so silently used an
#   olean left by an earlier run; it also listed CFamily twice.
# * EVERY LOCAL DEPENDENCY.  The build set is MODS closed under ALL local imports -- any
#   `import X` with an X.lean in this directory, not only `LeanPaper*` ones.  The corpus
#   imports 15 older modules (`LeanSupportGeometryV4`, `LeanProductMixedDifferenceV4`, ...);
#   the first frozen run omitted them, and the old runner never rebuilt them at all but used
#   whatever olean an earlier session had left.  They are rebuilt here from their bytes and
#   reported with role `dependency`.
# * ORDER FROM THE IMPORTS.  The order is not hand-maintained.  A Makefile is generated
#   from the import lines, and `make -k` builds a module only after all of its imports
#   succeeded.  An import that is neither `Mathlib*` nor in the build set is a failure.
# * `sorry` / `native_decide` are counted OUTSIDE comments, so a docstring that says "no
#   native_decide" is not a finding, while a real use still is.
# * The axiom closure is CHECKED against the whitelist, not only printed.
# * At the end the frozen bytes are compared with the working directory (report/DRIFT.txt),
#   so a PASS says which bytes it is about.
#
# Usage:   bash verify_all.sh                      full gate, J=3 parallel jobs
#          J=2 bash verify_all.sh
#          GATE_ONLY="LeanPaperCEvenTotalV1" bash verify_all.sh
#              smoke run of the named modules plus everything they import; it reports
#              SMOKE PASS/FAIL and never VERIFY PASS.
set -u

MODS="LeanPaperClosuresV1 \
LeanPaperAClosureV1 LeanPaperAAlternativesV1 LeanPaperAAlternativeUnionV1 LeanPaperAModelBridgeV1 \
LeanPaperAOracleCertificateV1 LeanPaperARepairV1 LeanPaperASeparationV1 LeanPaperARPairV1 \
LeanPaperARGamesV1 LeanPaperAHomogV1 LeanPaperAFrozenV1 LeanPaperACentredV1 \
LeanPaperACentredModelV1 LeanPaperARegionV1 LeanPaperAOracleRegionV1 LeanPaperAStrictV1 \
LeanPaperAFrontierV1 LeanPaperA7OracleSelectV1 LeanPaperA7TrackingV1 LeanPaperA7ConfidenceV1 \
LeanPaperA7StreamV1 LeanPaperAFreezeV1 LeanPaperAMartingaleV1 LeanPaperAAdaptMartV1 \
LeanPaperAStopJoinV1 LeanPaperAStoppingV1 LeanPaperA7TailV1 LeanPaperA7EtaV1 \
LeanPaperA7ChainV1 LeanPaperA2ChainV1 LeanPaperASurrogateV1 LeanPaperAConfStepV1 \
LeanPaperAIdentifyV1 LeanPaperA7ThresholdV1 LeanPaperAChangeV1 LeanPaperAActualDecisionBridgeV1 \
LeanPaperAEndgameV1 LeanPaperACertificatePerturbationV1 LeanPaperAGaussianKLV1 \
LeanPaperA7AccumulationV1 LeanPaperA7WarmTrackV1 LeanPaperAENatExpectV1 LeanPaperA7DirectLowerV1 \
LeanPaperA7ProcessV1 LeanPaperA7UpperChainV1 LeanPaperALowerKLV1 LeanPaperABridgeV1 \
LeanPaperA7SqrtLipV1 LeanPaperALowerGameV1 LeanPaperA7CorrectV1 LeanPaperA7FreeAccumV1 \
LeanPaperA7DirectFreeV1 LeanPaperABridgeDummyV1 LeanPaperAFamilyLowerV1 LeanPaperA7GLRMeasV1 \
LeanPaperA7NetOracleV1 LeanPaperA7IdealLearnerV1 LeanPaperA7IdealStopV1 \
LeanPaperA7IdealRunV1 LeanPaperA7AsymV1 LeanPaperA7IdealSelectV1 LeanPaperA7IdealBoundsV1 \
LeanPaperA7IdealDirectV1 LeanPaperA7IdealDirect2V1 LeanPaperA7IdealUpperV1 \
LeanPaperA7IdealStoppedV1 LeanPaperA7IdealFamilyV1 \
LeanPaperA6FixedDesignV1 LeanPaperA7StoppedGenV1 LeanPaperA6SurrogateCostV1 \
LeanPaperBStoppedParityV1 \
LeanPaperA6OracleLearnerV1 LeanPaperA6SurrogateAtV1 LeanPaperA6BadRoundsV1 LeanPaperA6EstCostV1 \
LeanPaperCExPostV1 \
LeanPaperCRelaxedJoinV1 LeanPaperCRatioJoinV1 \
LeanPaperCOddKinkV1 LeanPaperCOddKinkLawV1 LeanPaperCOddKinkBandV1 LeanPaperCOddFrontierV1 \
LeanPaperCCollapseScaleV1 LeanPaperCExPostBandV1 \
LeanPaperASacrificeV1 LeanPaperASacrificeIdealV1 LeanPaperBObstructionLawV1 LeanPaperBObstructionParityV1 \
LeanPaperA6TwoSurrogatesV1 LeanPaperBFamilyChannelV1 LeanPaperBFamilyLawV1 LeanPaperBFamilyDecoderV1 \
LeanPaperBStoppedLawV1 LeanUnifiedObstructionOrderV1 LeanUnifiedStructuralRelaxedV1 \
LeanPaperBHellingerTestV1 LeanPaperASacrificeDiluteV1 LeanPaperCCollapseWindowV1 \
LeanPaperBHellingerFamilyV1 LeanPaperBHellingerParityV1 LeanPaperASacrificeStoppedV1 \
LeanPaperBFamilySafeV1 \
LeanPaperASacrificeDualityV1 LeanPaperBPrivateQueryV1 LeanPaperBChiStarV1 \
LeanPaperBShareTournamentV1 LeanPaperCRobustBallV1 \
LeanPaperBCertificateChannelV1 LeanPaperARepairLawV1 LeanPaperBDecisionOrderV1 LeanPaperCTypedFlowV1 \
LeanPaperAPolicyClassesV1 LeanPaperABudgetUpperV1 LeanPaperBCriticalGameV1 LeanPaperBQueryDesignV1 LeanPaperCFreeBandV1 \
LeanPaperATwoArmRateV1 LeanPaperARepairRateV1 LeanPaperCTwoMagFourV1 \
LeanPaperARepairBridgeV1 LeanPaperBVisibleV1 LeanPaperCFlowCertV1 LeanPaperCPathMixV1 \
LeanPaperCBudgetAwareV1 LeanPaperCBudgetFamiliesV1 LeanPaperCBudgetGmV1 \
LeanPaperARepairStopV1 LeanPaperARepairGaussV1 LeanPaperAForcingStopV1 LeanPaperARepairSlopeV1 LeanPaperARepairNoPosV1 \
LeanPaperCTwoMag2211V1 LeanPaperCBudgetSymV1 LeanPaperCBudgetSharpV1 LeanPaperCCountReductionV1 LeanPaperCCountRecourseV1 \
LeanPaperBAttainmentV1 LeanPaperBHellingerV1 LeanPaperBTranscriptKLV1 LeanPaperBChangeV1 \
LeanPaperBRatesV1 LeanPaperBHeadlineV1 LeanPaperBExactConstV1 LeanPaperBDecideV1 \
LeanPaperBGeometryV1 LeanPaperBIndistV1 LeanPaperBDensityV1 LeanPaperBSafeOrderV1 \
LeanPaperBCubeV1 LeanPaperBAttainV1 LeanPaperBParityV1 LeanPaperBDecoderV1 \
LeanPaperBTranscriptV1 LeanPaperBHoeffdingV1 LeanPaperBAdaptiveV1 LeanPaperBTipV1 \
LeanPaperBKLV1 LeanPaperBRateKLV1 LeanPaperBWorldsV1 LeanPaperBQueryClassV1 \
LeanPaperBScopeV1 LeanPaperBChannelPairV1 LeanPaperBSepDerivedV1 LeanPaperBPairRateV1 \
LeanPaperBDataProcV1 LeanPaperBGaussStepV1 LeanPaperBDensRatioV1 LeanPaperBTestV1 \
LeanPaperBCrossoverV1 LeanPaperBKernelV1 LeanPaperBEndgameV1 LeanPaperBRateClosureV1 \
LeanPaperBParityNormV1 LeanPaperBParityLawV1 \
LeanPaperBChiSqV1 LeanPaperBParityChiSqV1 LeanPaperBProtocolV1 LeanPaperBObstructionV1 \
LeanPaperBConcentrationV1 LeanPaperBScheduleV1 LeanPaperBSchedTestV1 LeanPaperBParityChannelV1 \
LeanPaperBParityGapV1 LeanPaperBParityTestV1 LeanPaperBParityExperimentV1 LeanPaperBParityDecoderV1 \
LeanPaperBParityFinishV1 LeanPaperBDecoderMatchV1 \
LeanPaperCFrontierV1 LeanPaperCRankingV1 LeanPaperCBreakpointV1 LeanPaperCBandV1 \
LeanPaperCEndpointV1 LeanPaperCInstantiationV1 LeanPaperCFamilyV1 LeanPaperCRearrangeV1 \
LeanPaperCAttainV1 LeanPaperCFlowV1 LeanPaperCNamingV1 LeanPaperCTransport2V1 \
LeanPaperCTransportV1 LeanPaperCEvenV1 LeanPaperCMixV1 LeanPaperCUniformV1 \
LeanPaperCEvenResolveV1 LeanPaperCValueSetV1 LeanPaperCLowerZeroV1 LeanPaperCCollapseV1 \
LeanPaperCPermV1 LeanPaperCPathV1 LeanPaperCCyclicV1 LeanPaperCOmitV1 \
LeanPaperCOddV1 LeanPaperCWindowV1 LeanPaperCValueV1 LeanPaperCFinalV1 \
LeanPaperCVacuityV1 LeanPaperCHorizonV1 LeanPaperCHorizonSecV1 LeanPaperCRankFlowV1 \
LeanPaperCFlowLawV1 LeanPaperCRelabelV1 LeanPaperCLawPushV1 LeanPaperCLawRelabelV1 \
LeanPaperCFam13V1 LeanPaperCBreak3V1 LeanPaperCBandValueBridgeV1 LeanPaperCEvenWitnessJoinV1 \
LeanPaperCOddWitnessJoinV1 LeanPaperCFlowBandJoinV1 LeanPaperCEndgameV1 LeanPaperCOddBreakpointEndgameV1 \
LeanPaperCStabilityEndgameV1 LeanPaperCEvenTotalV1 LeanPaperCParityBaselineV1 LeanPaperCBaselineAttainV1 \
LeanPaperCEvenRankSumV1 LeanPaperCRelabelBandJoinV1 LeanPaperCEndpointLawV1 LeanPaperCFlowObjectiveV1 LeanPaperCStabilityFamilyV1"

WHITELIST='propext|Classical.choice|Quot.sound'

# Every module a source file imports, one per line (with or without «»).
imports_all() {
  # («)? not «? : the guillemet is two bytes, and «? would make only its last byte optional
  grep -E '^import ' "$1" | sed -E 's/^import +(«)?([A-Za-z0-9_.]+)(»)?.*$/\2/'
}

# The LOCAL modules a source file imports: those with a .lean file in directory $2.
local_imports() {  # local_imports FILE DIR
  for x in $(imports_all "$1"); do [ -f "$2/$x.lean" ] && echo "$x"; done
}

# Occurrences of the word $2 in $1 outside Lean comments (`--` and nested `/- -/`).
count_code() {  # count_code FILE WORD
  python3 - "$1" "$2" <<'PY'
import re, sys
s = open(sys.argv[1]).read(); w = sys.argv[2]
out = []; i = 0; depth = 0; n = len(s)
while i < n:
    if s.startswith('/-', i): depth += 1; i += 2; continue
    if depth and s.startswith('-/', i): depth -= 1; i += 2; continue
    if depth: i += 1; continue
    if s.startswith('--', i):
        j = s.find('\n', i); i = n if j < 0 else j; continue
    out.append(s[i]); i += 1
code = ''.join(out)
print(len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(w) + r'(?![A-Za-z0-9_])', code)))
PY
}

in_list() {  # in_list NAME "LIST"
  case " $2 " in *" $1 "*) return 0 ;; *) return 1 ;; esac
}

# --------------------------------------------------------------------------- freeze
if [ "${GATE_PHASE:-freeze}" = "freeze" ]; then
  SRC=$(cd "$(dirname "$0")" && pwd)
  RUN=${RUN:-$(date +%Y%m%d_%H%M%S)}
  DST="$(cd "$SRC/.." && pwd)/gate_runs/$RUN"
  if [ -e "$DST" ]; then echo "refusing to reuse existing $DST"; exit 2; fi
  for m in $MODS; do
    [ -f "$SRC/$m.lean" ] || { echo "listed module missing: $m.lean"; exit 2; }
  done
  # Selection: MODS (full) or the named modules (smoke), closed under ALL local imports.
  if [ -n "${GATE_ONLY:-}" ]; then ROOTS="$GATE_ONLY"; MODE=smoke; else ROOTS="$MODS"; MODE=full; fi
  SEL=""; todo="$ROOTS"
  while [ -n "$todo" ]; do
    next=""
    for m in $todo; do
      in_list "$m" "$SEL" && continue
      [ -f "$SRC/$m.lean" ] || { echo "missing $m.lean"; exit 2; }
      SEL="$SEL $m"
      next="$next $(local_imports "$SRC/$m.lean" "$SRC" | tr '\n' ' ')"
    done
    todo="$next"
  done
  mkdir -p "$DST/.lake" "$DST/logs" "$DST/report"
  ln -s "$SRC/.lake/packages" "$DST/.lake/packages"
  cp "$SRC/lakefile.toml" "$SRC/lake-manifest.json" "$SRC/lean-toolchain" "$DST/"
  for m in $SEL; do cp "$SRC/$m.lean" "$DST/"; done
  cp "$0" "$DST/verify_all.frozen.sh"
  echo $SEL | tr ' ' '\n' | sed '/^$/d' > "$DST/report/MODULES.list"
  echo $ROOTS | tr ' ' '\n' | sed '/^$/d' > "$DST/report/ROOTS.list"
  echo "$MODE" > "$DST/report/MODE"
  echo "$SRC" > "$DST/report/SOURCE_DIR"
  echo "frozen run: $DST ($MODE, $(wc -l < "$DST/report/MODULES.list" | tr -d ' ') modules)"
  cd "$DST" && GATE_PHASE=run RUN="$RUN" exec bash "$DST/verify_all.frozen.sh"
fi

# --------------------------------------------------------------------------- run
# From here on only the frozen directory is read.
J=${J:-3}   # each Lean process holds ~2.7 GB; 3 jobs fit in 16 GB with room to spare
SEL=$(tr '\n' ' ' < report/MODULES.list)   # space-separated: in_list matches on spaces
MODE=$(cat report/MODE)
SRC=$(cat report/SOURCE_DIR)
OL=.lake/build/lib/lean
mkdir -p "$OL"

ROOTS=$(tr '\n' ' ' < report/ROOTS.list)

# Every import must be Mathlib or one of the modules being built.
closed=1
for m in $SEL; do
  for d in $(imports_all "$m.lean"); do
    case "$d" in Mathlib|Mathlib.*) continue ;; esac
    if ! in_list "$d" "$SEL"; then echo "IMPORT OUTSIDE GATE: $m imports $d"; closed=0; fi
  done
done

shasum -a 256 $(for m in $SEL; do printf '%s.lean ' "$m"; done) > report/SOURCES.sha256
shasum -a 256 verify_all.frozen.sh lakefile.toml lake-manifest.json lean-toolchain > report/RUNNER.sha256
{
  echo "run=$RUN mode=$MODE jobs=$J"
  echo "started=$(date '+%Y-%m-%d %H:%M:%S %z')"
  echo "lean=$(lake env lean --version 2>&1)"
  echo "toolchain=$(cat lean-toolchain)"
  echo "mathlib_rev=$(grep -A1 '"rev"' lake-manifest.json | head -1 | tr -d ' ",' | sed 's/rev://')"
  echo "git_head=$(git -C "$SRC" rev-parse HEAD 2>/dev/null)"
} > report/ENV.txt

# The dependency graph, as a Makefile.  A module is compiled to a temporary name and moved
# into place only on success, so a failed module leaves no olean for its dependents.
{
  printf 'all:'
  for m in $SEL; do printf ' %s/%s.olean' "$OL" "$m"; done
  printf '\n\n'
  for m in $SEL; do
    printf '%s/%s.olean: %s.lean' "$OL" "$m" "$m"
    for d in $(local_imports "$m.lean" .); do printf ' %s/%s.olean' "$OL" "$d"; done
    printf '\n'
    printf '\t@lake env lean -o %s/%s.olean.tmp %s.lean > logs/%s.log 2>&1; rc=$$?; ' "$OL" "$m" "$m" "$m"
    printf 'echo $$rc > logs/%s.exit; ' "$m"
    printf 'if [ $$rc -eq 0 ]; then mv %s/%s.olean.tmp %s/%s.olean; fi; ' "$OL" "$m" "$OL" "$m"
    printf 'echo "%s exit=$$rc"; exit $$rc\n\n' "$m"
  done
} > report/Makefile

lake env true > /dev/null 2>&1   # let lake settle its workspace once, before parallel use
make -k -j"$J" -f report/Makefile all > report/make.log 2>&1

tot=0; bad=0; sry=0; nat=0; thm=0; nb=0
printf 'module\trole\texit\terr\tprints\tsorryAx\tsorry_src\tnative_src\tsrc_sha256\tolean_sha256\n' > report/MODULES.tsv
for m in $SEL; do
  log=logs/$m.log; [ -f "$log" ] || log=/dev/null
  if [ -f "logs/$m.exit" ]; then rc=$(cat "logs/$m.exit"); else rc=notbuilt; nb=$((nb+1)); fi
  e=$(grep -cE "^$m\.lean:[0-9]+:[0-9]+: error" "$log")
  p=$(grep -cE "depends on axioms|does not depend on any axioms" "$log")
  sx=$(grep -c "sorryAx" "$log")
  s=$(count_code "$m.lean" sorry); n=$(count_code "$m.lean" native_decide)
  if in_list "$m" "$ROOTS"; then role=listed; else role=dependency; fi
  hs=$(shasum -a 256 "$m.lean" | cut -c1-64)
  if [ -f "$OL/$m.olean" ]; then ho=$(shasum -a 256 "$OL/$m.olean" | cut -c1-64); else ho=-; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$m" "$role" "$rc" "$e" "$p" "$sx" "$s" "$n" "$hs" "$ho" >> report/MODULES.tsv
  printf "%-42s %-10s exit=%s err=%s prints=%s sorryAx=%s\n" "$m" "$role" "$rc" "$e" "$p" "$sx"
  if [ "$rc" != "0" ] || [ "$e" != "0" ] || [ "$sx" != "0" ]; then bad=$((bad+1)); fi
  tot=$((tot+1)); sry=$((sry+s)); nat=$((nat+n)); thm=$((thm+p))
done

cat logs/*.log 2>/dev/null | tr '\n' ' ' | grep -o "depends on axioms: \[[^]]*\]" \
  | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' | sed '/^$/d' | sort -u > report/AXIOMS.txt
badax=$(grep -vxE "$WHITELIST" report/AXIOMS.txt | tr '\n' ' ')

( cd "$SRC" && shasum -a 256 -c "$OLDPWD/report/SOURCES.sha256" 2>&1 | grep -v ': OK$' ) > report/DRIFT.txt

{
  echo "--- totals ---"
  echo "modules=$tot (listed=$(echo $ROOTS | wc -w | tr -d ' '), dependencies=$((tot - $(echo $ROOTS | wc -w)))) failed=$bad not_built=$nb audited_theorems=$thm sorry=$sry native_decide=$nat"
  echo "imports_closed=$closed"
  echo "--- axiom closure over every audited theorem ---"
  echo "[$(tr '\n' ' ' < report/AXIOMS.txt)]"
  [ -n "$badax" ] && echo "AXIOMS OUTSIDE WHITELIST: $badax"
  if [ -s report/DRIFT.txt ]; then
    echo "--- working directory differs from the frozen bytes (the verdict is about the frozen bytes) ---"
    cat report/DRIFT.txt
  fi
  echo "finished=$(date '+%Y-%m-%d %H:%M:%S %z')"
  ok=0
  [ "$bad" = "0" ] && [ "$sry" = "0" ] && [ "$nat" = "0" ] && [ -z "$badax" ] && [ "$closed" = "1" ] && ok=1
  if [ "$MODE" = "full" ]; then
    [ "$ok" = "1" ] && echo "VERIFY PASS" || echo "VERIFY FAIL"
  else
    [ "$ok" = "1" ] && echo "SMOKE PASS" || echo "SMOKE FAIL"
  fi
} | tee report/SUMMARY.txt
