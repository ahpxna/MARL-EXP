#!/usr/bin/env python3
"""Paper A: the error self-check with the right denominator, recomputed from stored JSON.

delta-correctness bounds P(stop AND answer wrong) <= alpha for each launched run.  It does
NOT bound P(wrong | stopped), and under censoring the two differ.  The producers
`EXP_paperA_deployable.py` and `EXP_paperA7_panel.py` tested the conditional quantity (wrong
among STOPPED runs).  This script recomputes the correct test from their stored runs,
without resampling anything:

    for each rule / arm:  n = launched runs,  k = runs that stopped with a wrong answer,
    tail = P(Binomial(n, alpha) >= k).

Independence: in the pilot every (r, world, rule, run) has its own seed
`[20260924, r, world, rule, run]`; in the A7 panel every (cell, arm, run) has its own seed
`[20260925, cell, arm, run]`.  So runs are independent within and across rules, and the
pooled test is also valid for these two artifacts.  (The locked paired panel shares seeds
across rules and tests each rule separately in its own producer.)  Censoring is reported
separately.

Output (new file; refuses to overwrite): research/unified_20260919/paperA_alpha_launched.json
"""

import hashlib
import json
import pathlib
import sys

from scipy.stats import binom

SRC = pathlib.Path("research/unified_20260919")
OUT = SRC / "paperA_alpha_launched.json"
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def tail(k, n, p):
    return float(binom.sf(k - 1, n, p)) if k > 0 else 1.0


def main():
    if OUT.exists():
        print(f"refusing to overwrite existing {OUT}", file=sys.stderr)
        return 2
    out = {"producer": "scripts/ANALYSE_paperA_alpha_launched.py",
           "producer_sha256": sha(__file__), "inputs": {}, "tests": {}}

    # pilot deployable panel
    f = SRC / "paperA_deployable.json"
    d = json.load(open(f))
    out["inputs"][f.name] = sha(f)
    a = d["alpha"]
    per, ok_counts = {}, True
    for row in d["rows"]:
        n = len(row["tau_per_run"])
        k = sum(1 for ans, c in zip(row["answer_per_run"], row["censored_per_run"])
                if not c and ans != row["correct_answer"])
        ok_counts &= (k == row["stopped_wrong"]) and (sum(row["censored_per_run"]) == row["censored"])
        e = per.setdefault(row["rule"], {"launched": 0, "stopped_and_wrong": 0, "censored": 0})
        e["launched"] += n; e["stopped_and_wrong"] += k; e["censored"] += row["censored"]
    for e in per.values():
        e["tail_P(X>=k)"] = tail(e["stopped_and_wrong"], e["launched"], a)
    tot_n = sum(e["launched"] for e in per.values())
    tot_k = sum(e["stopped_and_wrong"] for e in per.values())
    out["tests"]["paperA_deployable"] = {"alpha": a, "per_rule": per,
                                         "pooled": {"launched": tot_n, "stopped_and_wrong": tot_k,
                                                    "tail_P(X>=k)": tail(tot_k, tot_n, a)}}
    check("pilot: recounted wrong-and-stopped and censored equal the stored counts", ok_counts)
    check("pilot: P(stop and wrong) <= alpha is not rejected, per rule and pooled",
          all(e["tail_P(X>=k)"] >= 1e-3 for e in per.values()) and tail(tot_k, tot_n, a) >= 1e-3,
          f"{tot_k} of {tot_n} launched")

    # A7 panel
    f = SRC / "paperA7_panel.json"
    d = json.load(open(f))
    out["inputs"][f.name] = sha(f)
    a = d["config"]["alpha"]
    per, ok_counts = {}, True
    for cell in d["cells"]:
        for arm, v in cell["arms"].items():
            n = len(v["runs"])
            k = sum(1 for x in v["runs"] if not x["censored"] and x["answer"] != cell["truth"])
            ok_counts &= k == v["stopped_wrong"]
            e = per.setdefault(arm, {"launched": 0, "stopped_and_wrong": 0, "censored": 0})
            e["launched"] += n; e["stopped_and_wrong"] += k; e["censored"] += v["censored"]
    for e in per.values():
        e["tail_P(X>=k)"] = tail(e["stopped_and_wrong"], e["launched"], a)
    tot_n = sum(e["launched"] for e in per.values())
    tot_k = sum(e["stopped_and_wrong"] for e in per.values())
    out["tests"]["paperA7_panel"] = {"alpha": a, "per_arm": per,
                                     "pooled": {"launched": tot_n, "stopped_and_wrong": tot_k,
                                                "tail_P(X>=k)": tail(tot_k, tot_n, a)}}
    check("A7 panel: recounted wrong-and-stopped equal the stored counts", ok_counts)
    check("A7 panel: P(stop and wrong) <= alpha is not rejected, per arm and pooled",
          all(e["tail_P(X>=k)"] >= 1e-3 for e in per.values()) and tail(tot_k, tot_n, a) >= 1e-3,
          f"{tot_k} of {tot_n} launched")

    out["checks"] = CHECKS
    out["all_passed"] = all(c["ok"] for c in CHECKS)
    if not out["all_passed"]:
        print("REFUSING to write: a check failed.", file=sys.stderr)
        return 1
    OUT.write_text(json.dumps(out, indent=2))
    print(f"wrote {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
