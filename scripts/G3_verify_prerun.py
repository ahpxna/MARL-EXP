#!/usr/bin/env python3
"""G3 -- the PRE-EXECUTION verifier.  Run this immediately before launching, never after.

Four checks, all of which must pass:

  1. SNAPSHOT IDENTITY  -- every file in the sealed closure still has its recorded hash,
                           and the recomputed digest equals the sealed one.
  2. REGISTRATION       -- an independent timestamped record exists next to the
                           preregistration and carries the same two hashes.
  3. CHRONOLOGY         -- the registration timestamp precedes the launch time.
  4. CONFIG MATCH       -- the argv about to be used agrees with the protocol's
                           comparators, seeds, instances and horizon.

Check 2 is the one a local file cannot fake.  If `external_registration.json` is absent
the verifier FAILS: hashes establish content identity, an independent record establishes
chronology, and neither substitutes for the other.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
DIR = REPO / "research/G3_prereg_20260915"


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default=str(DIR))
    ap.add_argument("--argv", nargs=argparse.REMAINDER, default=[],
                    help="the runner argv you are about to use")
    args = ap.parse_args()
    d = Path(args.dir)
    prereg = json.loads((d / "preregistration.json").read_text())
    snap = json.loads((d / "snapshot.json").read_text())
    checks, ok = [], True

    # 1 -- snapshot identity
    bad = []
    for e in snap["files"]:
        p = REPO / e["path"]
        if not p.exists():
            bad.append(f"{e['path']}: MISSING")
        elif sha(p) != e["sha256"]:
            bad.append(f"{e['path']}: HASH CHANGED")
    payload = "\n".join(f"{e['path']}:{e['sha256']}" for e in snap["files"]) \
        + f"\nLOCK:{snap['environment']['dependency_lock_sha256']}" \
          f"\nPY:{snap['environment']['python']}\n"
    redigest = hashlib.sha256(payload.encode()).hexdigest()
    c1 = (not bad) and redigest == snap["snapshot_digest"]
    checks.append({"check": "snapshot_identity", "pass": c1,
                   "recomputed_digest": redigest,
                   "sealed_digest": snap["snapshot_digest"],
                   "changed_files": bad})
    ok &= c1

    # 2 -- independent registration
    reg_path = d / "external_registration.json"
    if reg_path.exists():
        reg = json.loads(reg_path.read_text())
        c2 = (reg.get("snapshot_digest") == snap["snapshot_digest"]
              and reg.get("preregistration_sha256") == sha(d / "preregistration.json"))
        detail = {"registry": reg.get("registry"), "receipt": reg.get("receipt_id")}
    else:
        c2, reg, detail = False, None, {
            "reason": "external_registration.json is ABSENT.  A local preregistration "
                      "file proves content identity only; without an independent "
                      "timestamped record there is no evidence the protocol preceded "
                      "the outcome."}
    checks.append({"check": "independent_registration", "pass": c2, "detail": detail})
    ok &= c2

    # 3 -- chronology
    if reg and reg.get("registered_utc"):
        c3 = reg["registered_utc"] < time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        detail3 = {"registered_utc": reg["registered_utc"],
                   "now_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    else:
        c3, detail3 = False, {"reason": "no registration timestamp to compare against"}
    checks.append({"check": "chronology_registration_before_launch", "pass": c3,
                   "detail": detail3})
    ok &= c3

    # 4 -- config match
    P = prereg["protocol"]
    a = " ".join(args.argv)
    wants = {
        "instances": str(P["instances"]), "max-n": str(P["horizon_H"]),
        "relations": "5", "actions": "6", "topk": "2",
        "alpha": str(P["alpha_runner"]), "batch": str(P["batch"]),
        "rng-protocol": P["rng_protocol"],
    }
    missing = [f"--{k} {v}" for k, v in wants.items() if f"--{k} {v}" not in a]
    seeds_ok = all(str(s) in args.argv for s in P["seeds"]) if args.argv else False
    c4 = bool(args.argv) and not missing and seeds_ok
    checks.append({"check": "config_matches_protocol", "pass": c4,
                   "detail": {"argv_given": bool(args.argv),
                              "missing_flags": missing,
                              "all_protocol_seeds_present": seeds_ok}})
    ok &= c4

    for c in checks:
        print(f"  [{'PASS' if c['pass'] else 'FAIL'}] {c['check']}")
        if not c["pass"]:
            print(f"         {json.dumps(c.get('detail') or c.get('changed_files'))[:300]}")
    print(f"\n{'READY TO LAUNCH' if ok else 'DO NOT LAUNCH'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
