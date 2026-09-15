#!/usr/bin/env python3
"""G3 -- classify the EXISTING C_lucb runs as exploratory, permanently.

No file written today can make a past run preregistered.  This script records, for each
historical freeze sidecar, exactly what provenance it does and does not carry, and
fixes its evidence class.  It changes no artifact and re-runs nothing.
"""
from __future__ import annotations
import hashlib, json, time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
OUT = REPO / "research/G3_prereg_20260915"
SIDECARS = [
    "research/confirm_ieee_20260912/functional_v4_lucb_ieee10seed_cellv1.freeze.json",
    "research/confirm_ieee_20260912/functional_v4_lucb_dev_cellv1.freeze.json",
]


def sha(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / "exploratory_disclosure.json"
    if path.exists():
        raise SystemExit(f"Refusing to overwrite {path}")
    rows = []
    for rel in SIDECARS:
        p = REPO / rel
        d = json.loads(p.read_text())
        present = {
            "exit_code_zero": d.get("exit_code") == 0,
            "runner_hash_before_and_after": "source_sha_at_launch" in d
                                            and "source_sha_at_finish" in d,
            "runner_unchanged_during_run": d.get("source_changed_during_run") is False,
            "actual_argv_recorded": "argv" in d,
            "artifact_hash_recorded": "artifact_sha" in d,
            "start_and_finish_utc": "started_utc" in d and "finished_utc" in d,
        }
        absent = {
            "immutable_dependency_snapshot": "the sidecar predates code_fingerprint; no "
                                             "lock file, interpreter or import-closure "
                                             "hashes are recorded",
            "independent_timestamped_registration": "no external record predating "
                                                    "outcome access exists",
            "protocol_document": "no hypotheses, estimand, multiplicity or stopping "
                                 "rule were fixed in advance in a separate file",
            "proof_of_no_transient_edit": "equal before/after hashes do not exclude an "
                                          "edit that was made and reverted during the run",
        }
        rows.append({
            "sidecar": rel, "sidecar_sha256": sha(p),
            "label": d.get("label"), "started_utc": d.get("started_utc"),
            "finished_utc": d.get("finished_utc"),
            "provenance_present": present, "provenance_absent": absent,
            "evidence_class": "EXPLORATORY_DEVELOPMENT",
            "may_be_called_preregistered": False,
        })
    out = {
        "gate": "G3", "kind": "exploratory_disclosure",
        "written_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "rule": "A frozen seed set is not preregistration.  A local mtime or a fresh "
                "commit is not historical evidence.  These runs keep their numbers and "
                "their provenance; what changes is only the label attached to them.",
        "classification": "Both runs are EXPLORATORY / DEVELOPMENT evidence and must be "
                          "reported as such.  They cannot become preregistered, now or "
                          "later.",
        "what_this_does_not_mean": [
            "It does not invalidate the numbers: the runs completed, the runner hash "
            "was unchanged across them, and the artifacts are hashed.",
            "It does not invalidate any mathematical result; G3 is about experimental "
            "provenance only.",
            "It does not assert that any particular venue forbids exploratory evidence; "
            "no such requirement has been established here.",
        ],
        "if_a_prior_record_exists": "If an independent timestamped record predating "
                                    "outcome access is found, verify its CONTENT -- "
                                    "hypotheses, endpoints, comparator set, seeds, "
                                    "budget, stopping and analysis -- against these "
                                    "runs before upgrading anything.  Do not upgrade on "
                                    "the existence of a record alone.",
        "runs": rows,
    }
    with path.open("x") as f:
        json.dump(out, f, indent=1)
        f.write("\n")
    for r in rows:
        print(f"  {r['label'][:52]:54s} -> {r['evidence_class']}")
    print(f"\nartifact: {path.relative_to(REPO)}")


if __name__ == "__main__":
    main()
