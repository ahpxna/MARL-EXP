#!/usr/bin/env bash
# Recompile the construction and literal geometry; fail on unexpected axioms.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../work/p13_conjectures"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
if [[ "${1:-}" != "--audit-existing" ]]; then
for module in LeanD6ThresholdConstructionV1 LeanD6GeometricRealizationV1 LeanD6UnknownMarginAllocationV1 LeanD6AllocationOrbitLawV1 LeanD6ExpandedMeasurementsV1 LeanD6ExpandedAllocationV1; do
  lake env lean -o "$module.olean" "$module.lean" 2>&1 | tee "$module.compile.log"
done
lake env lean AxiomAuditD6ThresholdConstructionV1.lean 2>&1 | tee AxiomAuditD6ThresholdConstructionV1.log
fi
python3 - <<'PY'
from pathlib import Path
import re
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
logs = {'AxiomAuditD6ThresholdConstructionV1.log': 15,
        'LeanD6GeometricRealizationV1.compile.log': 3,
        'LeanD6UnknownMarginAllocationV1.compile.log': 7,
        'LeanD6AllocationOrbitLawV1.compile.log': 9,
        'LeanD6ExpandedMeasurementsV1.compile.log': 3,
        'LeanD6ExpandedAllocationV1.compile.log': 13}
for filename, expected in logs.items():
    if filename.endswith('.compile.log'):
        source = Path(filename.replace('.compile.log', '.lean'))
        olean = source.with_suffix('.olean')
        assert olean.exists() and olean.stat().st_mtime_ns >= source.stat().st_mtime_ns, source
        assert Path(filename).stat().st_mtime_ns >= source.stat().st_mtime_ns, filename
    text = Path(filename).read_text()
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    assert len(rows) == expected, (filename, len(rows), expected)
    for theorem, listed in rows:
        axioms = {ax.strip() for ax in listed.split(',') if ax.strip()}
        assert axioms <= allowed, (theorem, axioms-allowed)
    assert not re.search(r'\berror(?:\(|:)', text), filename
print('PASS: 50 theorem audits; only the three standard axioms.')
PY
