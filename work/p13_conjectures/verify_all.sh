#!/bin/bash
# Full verification for the Paper A/B/C corpus.
# Acceptance: exit=0, err=0, sorryAx=0, no `sorry`, no `native_decide`,
# axioms subset of {propext, Classical.choice, Quot.sound}.
# `sorryAx` is checked separately from the error count: an error ANYWHERE in a module
# makes Lean insert `sorryAx` into the downstream theorems of that module, so a clean
# error count alone does not establish that the theorems are proved.
# Dependencies come before dependents: BGeometry < BTest, CBreakpoint < CFinal,
# ARPair < ARGames, A7Tail < A7Eta.
MODS="LeanPaperClosuresV1 \
LeanPaperAAlternativesV1 LeanPaperAAlternativeUnionV1 LeanPaperAModelBridgeV1 \
LeanPaperAOracleCertificateV1 LeanPaperARepairV1 LeanPaperASeparationV1 \
LeanPaperARPairV1 LeanPaperARGamesV1 LeanPaperAHomogV1 LeanPaperAFrozenV1 \
LeanPaperA7OracleSelectV1 LeanPaperA7TrackingV1 LeanPaperA7ConfidenceV1 \
LeanPaperA7StreamV1 LeanPaperA7TailV1 LeanPaperA7EtaV1 LeanPaperA2ChainV1 \
LeanPaperBAttainmentV1 LeanPaperBHellingerV1 LeanPaperBTranscriptKLV1 \
LeanPaperBRatesV1 LeanPaperBGeometryV1 LeanPaperBTestV1 LeanPaperBCrossoverV1 \
LeanPaperCFrontierV1 LeanPaperCRankingV1 LeanPaperCBreakpointV1 LeanPaperCFinalV1"
tot=0; bad=0; sry=0; nat=0; thm=0
for m in $MODS; do
  lake env lean -o .lake/build/lib/lean/$m.olean $m.lean > /tmp/v_$m.log 2>&1
  rc=$?
  e=$(grep -cE "^$m\.lean:[0-9]+:[0-9]+: error" /tmp/v_$m.log)
  p=$(grep -c "depends on axioms" /tmp/v_$m.log)
  sx=$(grep -c "sorryAx" /tmp/v_$m.log)
  s=$(grep -c "sorry" $m.lean); n=$(grep -c "native_decide" $m.lean)
  printf "%-32s exit=%d err=%s prints=%s sorryAx=%s\n" $m $rc $e $p $sx
  [ "$sx" != "0" ] && bad=$((bad+1))
  [ "$rc" != "0" ] && bad=$((bad+1))
  tot=$((tot+1)); sry=$((sry+s)); nat=$((nat+n)); thm=$((thm+p))
done
echo "--- totals ---"
echo "modules=$tot failed=$bad audited_theorems=$thm sorry=$sry native_decide=$nat"
echo "--- axiom closure over every audited theorem ---"
cat /tmp/v_Lean*.log | tr '\n' ' ' | grep -o "depends on axioms: \[[^]]*\]" | tr -s ' ' | sort -u
[ "$bad" = "0" ] && [ "$sry" = "0" ] && [ "$nat" = "0" ] && echo "VERIFY PASS" || echo "VERIFY FAIL"
