#!/usr/bin/env bash
# Compile the actual-world allocation bridge, then reject nonstandard axioms.
# Prerequisite construction/analytic .oleans are built by check_d6_threshold_bridge.sh.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../work/p13_conjectures"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
if [[ "${1:-}" != "--audit-existing" ]]; then
  for module in LeanD6AllocationFiniteBridgeV1 LeanD6AllocationPrimalBridgeV1 LeanD6AllocationDualBridgeV1 LeanD6AllocationSharpV1 LeanD6AllocationDistributionV1 LeanD6AllocationMarginV1 LeanD6AllocationMarginRegionV1 LeanD6AllocationMarginSharpV1 LeanD6UniqueOptimumV1 LeanD6AllocationMarginTheoremV1; do
    lake env lean -o "$module.olean" "$module.lean" 2>&1 | tee "$module.compile.log"
  done
fi
python3 - <<'PY'
from pathlib import Path
import re
allowed={'propext','Classical.choice','Quot.sound'}
modules={'LeanD6AllocationFiniteBridgeV1':5,'LeanD6AllocationPrimalBridgeV1':5,
         'LeanD6AllocationDualBridgeV1':6,'LeanD6AllocationSharpV1':7,
         'LeanD6AllocationDistributionV1':6,'LeanD6AllocationMarginV1':6,
         'LeanD6AllocationMarginRegionV1':5,'LeanD6AllocationMarginSharpV1':8,
         'LeanD6UniqueOptimumV1':4,'LeanD6AllocationMarginTheoremV1':3}
for module,expected in modules.items():
    source=Path(module+'.lean'); obj=Path(module+'.olean'); log=Path(module+'.compile.log')
    assert obj.exists() and obj.stat().st_mtime_ns>=source.stat().st_mtime_ns, ('stale/missing',obj)
    assert log.exists() and log.stat().st_mtime_ns>=source.stat().st_mtime_ns, ('stale/missing',log)
    for dependency in re.findall(r'^import «([^»]+)»',source.read_text(),re.M):
        if dependency in modules:
            dep=Path(dependency+'.olean')
            assert dep.exists() and obj.stat().st_mtime_ns>=dep.stat().st_mtime_ns, ('stale dependency',obj,dep)
    text=log.read_text()
    assert not re.search(r'\berror(?:\(|:)',text),log
    rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
    assert len(rows)==expected,(module,len(rows),expected)
    for theorem,listed in rows:
        axioms={a.strip() for a in listed.split(',') if a.strip()}
        assert axioms<=allowed,(theorem,axioms-allowed)
print(f'PASS: {sum(modules.values())} actual-allocation / margin / geometry theorem audits; only standard axioms.')
PY
