#!/usr/bin/env python3
"""G12 -- names defined in more than one Lean module of the headline closure.

Namespaces keep them distinct in Lean; a MANUSCRIPT cannot.  This lists the collisions
that have to be renamed before the notation table is written, restricted to the
headline closure so the count is about what the papers actually cite.
"""
import json, re
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
WORK = REPO / "work/p13_conjectures"
OUT = REPO / "research/worker_G14_status_20260915"

DECL = re.compile(r'^\s*(?:noncomputable\s+)?(?:private\s+)?'
                  r'(theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_][\w\'!?]*)',
                  re.M)
IMP = re.compile(r'^\s*import\s+«([^»]+)»', re.M)

HEADLINES = [
    "LeanStructuralFamilyLowerV1", "LeanStructuralFamilyUpperV1",
    "LeanStructuralSaturationV1", "LeanStructuralAvgPathGapV1",
    "LeanSupportSamplingLawV1", "LeanSupportDecideRecoverV1",
    "LeanSupportTupleCountV1", "LeanSupportDecideExponentV1",
    "LeanFunctionalAllocationJoinV1", "LeanFunctionalHeterogeneousInstanceV1",
    "LeanFunctionalGeometryDischargeV1",
    "LeanQueryGaussianLevelV1", "LeanQueryHellingerIntervalV1",
    "LeanQueryHellingerEnvelopeV1", "LeanQuerySampleComplexityV1",
    "LeanQueryRegretBridgeV1", "LeanQueryAffinityTestingV1",
    "LeanQueryRateAssemblyV1", "LeanQueryRegretChainV1",
    "LeanMasterCalibrationLawV1", "LeanMasterAnchorCertificateV1",
    "LeanMasterAnchorThresholdV1", "LeanMasterActiveSetV1",
    "LeanMasterGroupCalibrationV1",
    "LeanD6ScalarInformationV1", "LeanD6ThreeClassPhaseV1",
]


def closure(roots):
    seen, order = set(), []

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        src = WORK / f"{m}.lean"
        if not src.exists():
            return
        for dep in IMP.findall(src.read_text()):
            visit(dep)
        order.append(m)

    for r in roots:
        visit(r)
    return order


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    mods = closure(HEADLINES)
    where = defaultdict(list)
    for m in mods:
        for _kind, name in DECL.findall((WORK / f"{m}.lean").read_text()):
            where[name].append(m)
    coll = {n: sorted(set(ms)) for n, ms in where.items() if len(set(ms)) > 1}
    ranked = sorted(coll.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    print(f"headline closure: {len(mods)} modules, {len(where)} distinct names, "
          f"{len(coll)} collisions")
    for n, ms in ranked[:25]:
        print(f"  {n:34s} {len(ms)} modules: {', '.join(x[4:] for x in ms)}")
    out = {
        "gate": "G12",
        "scope": "the headline import closure only",
        "modules": mods,
        "distinct_names": len(where),
        "collisions": len(coll),
        "collision_table": {n: ms for n, ms in ranked},
        "rule": "namespaces keep these distinct in Lean; a manuscript cannot.  Each "
                "name below must be renamed or disambiguated in the notation table.",
    }
    path = OUT / "G12_notation_collisions.json"
    path.write_text(json.dumps(out, indent=1) + "\n")
    print(f"\nartifact: {path}")


if __name__ == "__main__":
    main()
