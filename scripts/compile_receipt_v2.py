#!/usr/bin/env python3
"""Compile Lean modules one by one and emit a per-module receipt + a manifest.

For each module, records: source sha256 BEFORE and AFTER compilation, the Lean
exit code (read from the compiler process, never from a wrapper or from `tee`),
the .olean mtime versus the source mtime, and the full axiom audit parsed out of
the compile log. A module counts as ACCEPTED only if
  exit == 0, source hash unchanged, .olean strictly newer than the source,
  at least one `#print axioms` line, and every audited name uses only
  {propext, Classical.choice, Quot.sound}  (any sorryAx => REJECTED).
Stops at the first module that fails to compile.
"""
import hashlib, json, os, re, subprocess, sys, time

WORK = "/Users/phanan/cig-amf-main/work/p13_conjectures"
OUT  = "/Users/phanan/cig-amf-main/research/high_risk_20260910"
STD  = {"propext", "Classical.choice", "Quot.sound"}

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()

def parse_axioms(text):
    out = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S):
        name = m.group(1)
        ax = [a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()]
        out[name] = ax
    return out

def main(modules):
    os.makedirs(OUT, exist_ok=True)
    env = dict(os.environ)
    env["LEAN_PATH"] = WORK + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    results = []
    for mod in modules:
        src = os.path.join(WORK, mod + ".lean")
        ole = os.path.join(WORK, mod + ".olean")
        log = os.path.join(WORK, mod + ".compile.log")
        rec = os.path.join(WORK, mod + ".compile.receipt.json")
        if not os.path.exists(src):
            print(f"{mod}: SOURCE MISSING", flush=True); break
        h0, m0 = sha(src), os.path.getmtime(src)
        t0 = time.time()
        p = subprocess.run(["lake", "env", "lean", "-o", ole, src],
                           cwd=WORK, env=env, capture_output=True, text=True)
        wall = time.time() - t0
        text = p.stdout + p.stderr
        with open(log, "w") as f:
            f.write(text)
        h1 = sha(src)
        axioms = parse_axioms(text)
        bad = {n: a for n, a in axioms.items() if set(a) - STD}
        olean_ok = os.path.exists(ole) and os.path.getmtime(ole) > m0
        accepted = (p.returncode == 0 and h0 == h1 and olean_ok
                    and len(axioms) > 0 and not bad)
        r = {"module": mod, "lean_exit": p.returncode, "wall_seconds": round(wall, 1),
             "source_sha256_before": h0, "source_sha256_after": h1,
             "source_unchanged": h0 == h1, "olean_newer_than_source": olean_ok,
             "audited_names": len(axioms), "axiom_audit": axioms,
             "nonstandard_axioms": bad, "errors": text.count("error:"),
             "accepted": accepted, "log": os.path.basename(log)}
        with open(rec, "w") as f:
            json.dump(r, f, indent=2, sort_keys=True)
        results.append(r)
        print(f"{mod}: LEAN_EXIT={p.returncode} errors={r['errors']} "
              f"audits={len(axioms)} nonstandard={len(bad)} accepted={accepted} "
              f"({wall:.1f}s)", flush=True)
        if p.returncode != 0:
            print(f"  -> stopping; read {log}", flush=True)
            break
    man = os.path.join(OUT, "d05_phase_closure_manifest_20260912.json")
    with open(man, "w") as f:
        json.dump({"generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                   "work_dir": WORK, "standard_axioms": sorted(STD),
                   "modules_requested": modules,
                   "modules_attempted": [r["module"] for r in results],
                   "all_accepted": bool(results) and all(r["accepted"] for r in results)
                                   and len(results) == len(modules),
                   "total_audited_names": sum(r["audited_names"] for r in results),
                   "receipts": results}, f, indent=2, sort_keys=True)
    print("manifest:", man, flush=True)
    return 0 if (results and all(r["accepted"] for r in results)
                 and len(results) == len(modules)) else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
