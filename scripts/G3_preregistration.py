#!/usr/bin/env python3
"""G3 -- seal a PROSPECTIVE protocol and a source/environment snapshot.

The closure guide is explicit: no file written now can prove that an old experiment was
preregistered.  This script therefore does two separate things, and neither of them
touches a historical run:

  1. it computes an immutable SNAPSHOT of everything the planned run will execute --
     the runner's repo-local import closure, the analysis code, the dependency lock,
     the interpreter and the platform -- and reduces it to one digest;
  2. it writes an immutable PREREGISTRATION containing the full protocol and that
     digest, refusing to overwrite, and prints the digest for the user to register
     wherever they choose.

It publishes nothing and contacts no service.  Registration -- where, whether, and
under what embargo -- is the user's decision; a local file establishes CONTENT
identity, and only an independent timestamped record establishes CHRONOLOGY.  Both are
needed, and this script supplies only the first.

`preregistration.json` is never updated with outcomes.  Results and any deviations go
in a separate `run_receipt.json` written after execution.
"""
from __future__ import annotations
import ast, hashlib, json, os, platform, subprocess, sys, time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
OUT = REPO / "research/G3_prereg_20260915"

RUNNER = "scripts/run_functional_variance_stopping_lab_v4.py"
HARNESS = "scripts/run_freeze_and_launch_v1.py"
ANALYSIS = ["scripts/analyze_functional_censoring_pairing.py"]

PROTOCOL = {
    "title": "Functional: certificate cost of C_lucb versus Uniform on the group-range "
             "panel (prospective holdout)",
    "status": "SEALED_NOT_EXECUTED",
    "gating": "Execution is gated on F5.5 items 1, 2 and 4.  Items 1 and 2 are done "
              "(P28: 28/28 oracle agreement at R=2 and R=3, clean primal/dual "
              "certificates).  Item 4 is partially done (P26 v2).  This protocol is "
              "sealed now so that registration precedes any outcome.",

    "target": "For each relation r, C_r(mu) = max_a mu_ra - min_a mu_ra (full range, no "
              "factor 1/2).  The answer is Top_k of C(mu).  R = 5 relations, K = 6 "
              "actions, k = 2.",
    "observation_law": "Independent Gaussian scalar reads of cell (r,a) with unknown "
                       "variance estimated from the samples themselves.  One sample = "
                       "one unit of budget.",
    "instrument_costs": "Unit price per sample; NO setup cost in this run.  Setup-cost "
                        "phases and primitive contrasts are a separate study and are "
                        "not part of this protocol.",

    "primary_hypothesis": "C_lucb reaches a certificate at a strictly lower restricted "
                          "mean sample cost than Uniform, paired by instance, at the "
                          "stated horizon.",
    "primary_endpoint": "Restricted mean number of samples to certificate, truncated at "
                        "the horizon H, paired by instance.",
    "estimand": "Paired difference (C_lucb - Uniform) of the restricted mean at H.",
    "inference": {"method": "percentile bootstrap over instances", "resamples": 4000,
                  "alpha": 0.05, "sided": "two-sided"},
    "multiplicity": "ONE primary endpoint.  Certificate fraction and false-safe rate "
                    "are SECONDARY, reported with the same interval and explicitly "
                    "labelled secondary; no alpha is spent on them and no secondary "
                    "result may be promoted after the fact.",

    "comparators_deployable": ["C_lucb", "C_anytime", "Uniform"],
    "diagnostics_not_comparators": ["C_extrema_oracle"],
    "diagnostic_rule": "C_extrema_oracle sees the truth.  It is reported separately and "
                       "is NOT a performance ceiling and NOT a baseline.",

    "generator": "scripts/run_functional_variance_stopping_lab_v4.py, version fixed by "
                 "the snapshot digest below",
    "instances": 1000,
    "horizon_H": 131072,
    "alpha_runner": 0.05,
    "batch": 16,
    "pilot_fraction": 0.15,
    "rng_protocol": "instance_cell_v1",
    "seed_policy": "Seeds are fixed in this file BEFORE any outcome is observed and are "
                   "not reused from tuning or method selection.  Choosing seeds by "
                   "observed performance is prohibited; 'new seeds' means outcomes not "
                   "used in tuning, not merely different numbers.",
    "seeds": [811, 821, 823, 827, 829, 839, 853, 857, 859, 863],

    "censoring": "Instances that do not certify by H are censored at H and enter the "
                 "restricted mean at H.  The censored fraction is reported per "
                 "comparator.",
    "failures_and_exclusions": "No exclusions are planned.  Any run that raises is "
                               "reported with its traceback and its instance id; it is "
                               "never dropped silently.",
    "stopping_rule": "Fixed.  H samples per instance, no interim analyses, no adaptive "
                     "stopping of the experiment, no peeking at the primary endpoint "
                     "before all instances finish.",
    "compute_cost_reporting": "Wall seconds, peak RSS and total samples drawn, per "
                              "comparator, recorded in run_receipt.json.",
    "deviations_policy": "Any deviation is recorded in run_receipt.json with its reason "
                         "and its timestamp.  THIS FILE IS NEVER EDITED.",
    "publication_of_this_file": "None.  This script contacts no service and registers "
                                "nothing; the user chooses whether and where to lodge "
                                "the digest.",
}


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()


def local_import_closure(entry: Path) -> list[Path]:
    """Every repo-local python file the entry point can reach by import."""
    seen, order, stack = set(), [], [entry]
    while stack:
        p = stack.pop()
        rp = p.resolve()
        if rp in seen or not p.exists():
            continue
        seen.add(rp)
        order.append(p)
        try:
            tree = ast.parse(p.read_text())
        except SyntaxError:
            continue
        names = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                names.update(a.name.split(".")[0] for a in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                names.add(node.module.split(".")[0])
        for n in names:
            for cand in (REPO / "scripts" / f"{n}.py", REPO / f"{n}.py",
                         REPO / n / "__init__.py"):
                if cand.exists():
                    stack.append(cand)
    return sorted(order, key=lambda q: str(q))


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prereg_path = OUT / "preregistration.json"
    snap_path = OUT / "snapshot.json"
    if prereg_path.exists() or snap_path.exists():
        raise SystemExit(f"Refusing to overwrite an existing preregistration in {OUT}. "
                         f"A preregistration is immutable; write a NEW dated directory.")

    files: list[Path] = []
    for e in [RUNNER, HARNESS, *ANALYSIS]:
        p = REPO / e
        if not p.exists():
            raise SystemExit(f"missing {e}")
        files.extend(local_import_closure(p))
    files = sorted({f.resolve() for f in files}, key=lambda q: str(q))

    entries = []
    for f in files:
        entries.append({"path": str(f.relative_to(REPO)), "sha256": sha(f),
                        "bytes": f.stat().st_size})

    try:
        lock = subprocess.run([str(REPO / ".venv/bin/python"), "-m", "pip", "freeze"],
                              capture_output=True, text=True, timeout=120).stdout
    except Exception as exc:                                    # noqa: BLE001
        lock = f"UNAVAILABLE: {exc}"
    lock_sha = hashlib.sha256(lock.encode()).hexdigest()

    env = {
        "python": subprocess.run([str(REPO / ".venv/bin/python"), "-V"],
                                 capture_output=True, text=True).stdout.strip(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "dependency_lock_sha256": lock_sha,
        "dependency_lock_lines": len(lock.splitlines()),
    }

    payload = "\n".join(f"{e['path']}:{e['sha256']}" for e in entries) \
        + f"\nLOCK:{lock_sha}\nPY:{env['python']}\n"
    snapshot_digest = hashlib.sha256(payload.encode()).hexdigest()

    snapshot = {
        "gate": "G3", "kind": "sealed_source_environment_snapshot",
        "sealed_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "entry_points": [RUNNER, HARNESS, *ANALYSIS],
        "closure_size": len(entries),
        "files": entries,
        "environment": env,
        "dependency_lock": lock,
        "snapshot_digest": snapshot_digest,
        "digest_rule": "sha256 over the sorted 'relative_path:sha256' lines, then the "
                       "dependency-lock digest and the interpreter string",
    }
    with snap_path.open("x") as f:
        json.dump(snapshot, f, indent=1)
        f.write("\n")

    prereg = {
        "gate": "G3", "kind": "preregistration", "immutable": True,
        "sealed_utc": snapshot["sealed_utc"],
        "protocol": PROTOCOL,
        "snapshot_digest": snapshot_digest,
        "snapshot_file": str(snap_path.relative_to(REPO)),
        "registration": {
            "registered_externally": False,
            "how_to_register": "Lodge `snapshot_digest` and this file's own sha256 with "
                               "an independent timestamping service or registry (embargo "
                               "if appropriate), then record the receipt in "
                               "external_registration.json NEXT TO this file.  Do not "
                               "edit this file.",
            "why_this_file_alone_is_not_enough": "A local file and a local mtime prove "
                                                 "content identity, not chronology.  "
                                                 "Only an independent record predating "
                                                 "outcome access establishes that the "
                                                 "protocol came first.",
        },
        "not_established": [
            "This preregistration applies ONLY to the future run it describes.",
            "It says nothing about, and cannot retroactively cover, any existing run.",
            "The run has NOT been executed; status is SEALED_NOT_EXECUTED.",
        ],
    }
    with prereg_path.open("x") as f:
        json.dump(prereg, f, indent=1)
        f.write("\n")
    prereg_sha = sha(prereg_path)

    print("G3 preregistration sealed.  Nothing was executed and nothing was published.")
    print(f"  files in snapshot closure : {len(entries)}")
    print(f"  dependency lock lines     : {env['dependency_lock_lines']}")
    print(f"  interpreter               : {env['python']}")
    print(f"  SNAPSHOT DIGEST           : {snapshot_digest}")
    print(f"  preregistration sha256    : {prereg_sha}")
    print(f"\n  -> {prereg_path.relative_to(REPO)}")
    print(f"  -> {snap_path.relative_to(REPO)}")
    print("\nRegister the two hashes above with an independent timestamped record "
          "BEFORE launching.  Then run scripts/G3_verify_prerun.py.")


if __name__ == "__main__":
    main()
