#!/usr/bin/env python3
"""G05 -- a CLEAN build of the headline dependency closure, not a receipt inventory.

Audit item G2: the previous G05 read existing receipts.  That certifies nothing about
reproducibility.  This script

  1. computes the import closure of the headline modules (local imports only);
  2. DELETES every .olean and .compile.log in that closure;
  3. rebuilds the closure in dependency order with `compile_receipt_v2.py`, which runs
     `lake env lean` and reads the compiler's own exit code;
  4. records the toolchain, the pinned mathlib rev, every dependency rev, and the
     sha256 of every source in the closure, together with the sha256 the fresh receipt
     recorded;
  5. fails loudly if any module is not ACCEPTED or any hash disagrees.

Mathlib itself is pinned by rev + lake-manifest and is NOT rebuilt: rebuilding it would
certify the same commit twice.  What is rebuilt from nothing is every local module the
headlines depend on.
"""
import hashlib, json, os, re, shutil, subprocess, sys, time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
WORK = REPO / "work/p13_conjectures"
OUT = REPO / "research/worker_G05_cleanbuild_20260915"

HEADLINES = [
    # Structural
    "LeanStructuralFamilyLowerV1", "LeanStructuralFamilyUpperV1",
    "LeanStructuralSaturationV1", "LeanStructuralAvgPathGapV1",
    # Support
    "LeanSupportSamplingLawV1", "LeanSupportDecideRecoverV1",
    "LeanSupportTupleCountV1", "LeanSupportDecideExponentV1",
    # Functional
    "LeanFunctionalAllocationJoinV1", "LeanFunctionalHeterogeneousInstanceV1",
    "LeanFunctionalGeometryDischargeV1",
    # Query
    "LeanQueryGaussianLevelV1", "LeanQueryHellingerIntervalV1",
    "LeanQueryHellingerEnvelopeV1", "LeanQuerySampleComplexityV1",
    "LeanQueryRegretBridgeV1", "LeanQueryAffinityTestingV1",
    "LeanQueryRateAssemblyV1", "LeanQueryRegretChainV1",
    # MASTER
    "LeanMasterCalibrationLawV1", "LeanMasterAnchorCertificateV1",
    "LeanMasterAnchorThresholdV1", "LeanMasterActiveSetV1",
    "LeanMasterGroupCalibrationV1",
    # D6
    "LeanD6ScalarInformationV1", "LeanD6ThreeClassPhaseV1",
]

IMP = re.compile(r'^\s*import\s+«([^»]+)»', re.M)


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()


def closure(roots):
    seen, order = set(), []

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        src = WORK / f"{m}.lean"
        if not src.exists():
            raise SystemExit(f"missing source for {m}")
        for dep in IMP.findall(src.read_text()):
            visit(dep)
        order.append(m)

    for r in roots:
        visit(r)
    return order


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    order = closure(HEADLINES)
    print(f"import closure: {len(order)} local modules, dependency order")

    # ARCHIVE, never delete: a clean build only needs the products OUT OF THE WAY.
    stamp = time.strftime("%Y%m%d_%H%M%S")
    attic = REPO / "legacy" / f"build_products_{stamp}"
    attic.mkdir(parents=True, exist_ok=True)
    moved = []
    for m in order:
        for ext in (".olean", ".compile.log", ".compile.receipt.json"):
            p = WORK / f"{m}{ext}"
            if p.exists():
                shutil.move(str(p), str(attic / p.name))
                moved.append(p.name)
    (attic / "MANIFEST.txt").write_text(
        f"archived {len(moved)} build products of the {len(order)}-module headline\n"
        f"closure before the clean build of {stamp}.  Nothing was deleted.\n\n"
        + "\n".join(sorted(moved)) + "\n")
    print(f"archived {len(moved)} build products to {attic}; rebuilding from nothing\n")

    r = subprocess.run([str(REPO / ".venv/bin/python"),
                        str(REPO / "scripts/compile_receipt_v2.py")] + order,
                       cwd=str(REPO), capture_output=True, text=True)
    print(r.stdout[-4000:])
    if r.stderr.strip():
        print(r.stderr[-2000:], file=sys.stderr)

    rows, bad = [], []
    for m in order:
        rec = WORK / f"{m}.compile.receipt.json"
        if not rec.exists():
            bad.append(f"{m}: no receipt after clean build")
            rows.append({"module": m, "accepted": False, "reason": "no receipt"})
            continue
        d = json.loads(rec.read_text())
        cur = sha(WORK / f"{m}.lean")
        ok = bool(d.get("accepted")) and d.get("source_sha256_before") == cur
        if not ok:
            bad.append(f"{m}: accepted={d.get('accepted')} hash_match="
                       f"{d.get('source_sha256_before') == cur}")
        rows.append({
            "module": m, "accepted": bool(d.get("accepted")),
            "lean_exit": d.get("lean_exit"),
            "audits": len(d.get("axioms", {})),
            "source_sha256": cur,
            "receipt_sha256": d.get("source_sha256_before"),
            "hash_matches": d.get("source_sha256_before") == cur,
            "wall_seconds": d.get("wall_seconds"),
        })

    tool = (WORK / "lean-toolchain").read_text().strip() if (WORK / "lean-toolchain").exists() else None
    manifest = json.loads((WORK / "lake-manifest.json").read_text())
    deps = {p.get("name"): p.get("rev") for p in manifest.get("packages", [])}

    out = {
        "gate": "G05",
        "clean_build": True,
        "what_was_archived": "every .olean, .compile.log and .compile.receipt.json in the closure was MOVED to legacy/build_products_<stamp>/, not deleted",
        "archive_dir": str(attic.relative_to(REPO)),
        "mathlib_not_rebuilt": "pinned by rev + lake-manifest; rebuilding it certifies the same commit twice",
        "toolchain": tool,
        "dependency_revs": deps,
        "closure_size": len(order),
        "build_order": order,
        "modules": rows,
        "all_accepted": len(bad) == 0,
        "failures": bad,
    }
    path = OUT / "G05_clean_build.json"
    path.write_text(json.dumps(out, indent=1) + "\n")
    ok = len(bad) == 0
    print(f"\nclean build: {sum(1 for r in rows if r['accepted'])}/{len(rows)} accepted, "
          f"hashes match: {all(r.get('hash_matches') for r in rows)}")
    if bad:
        print("FAILURES:")
        for b in bad:
            print("  " + b)
    print(f"artifact: {path}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
