"""Release-gated D6 half-factor falsification campaign.

The campaign encodes the agreed search -> proof gate.  It does not start Lean
proof engineering and does not treat survival as proof.  Deep mode covers the
specified m/alphabet/k/reference regimes; local mode can seed every compatible
search from the strongest current witness.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0, str(ROOT))

from research_chains.provenance import atomic_json, write_artifact_with_provenance
from scripts.run_d6_counterexample_optimizer import run as directed_run
from scripts.run_d6_exact_small_search import run as exact_run

PROTOCOL_VERSION = "d6_h3_transfer_campaign_v2"


def _directed_grid(profile):
    base = []
    for m, alphabet in ((3, 2), (3, 3), (4, 2), (4, 3), (5, 2)):
        for k in range(1, m):
            for q_mode in ("uniform", "random", "skewed", "boundary"):
                base.append((m, alphabet, k, q_mode, q_mode != "uniform"))
    return base if profile == "deep" else [x for x in base if x[0] == 3 and x[1] == 2]


def run(out_root, profile="quick", seeds=(701,), witness=None, resume=False,
        restarts=None, steps=None):
    out_root = Path(out_root); out_root.mkdir(parents=True, exist_ok=True)
    exact_specs = [
        (3, 2, (1, 2), 1, "full", None),
        (3, 2, (1, 2), 2, "full", None if profile == "deep" else 2000),
        (3, 3, (1, 2), 2, "selected_interactions", None),
        (4, 2, (1, 2, 3), 2, "selected_interactions", None),
    ]
    records = []; killed = False; best = None
    for m, alphabet, ks, radius, family, max_worlds in exact_specs:
        name = f"exact_m{m}_a{alphabet}_r{radius}_{family}.json"; path = out_root / name
        if resume and path.exists(): payload = json.loads(path.read_text())
        else:
            payload = exact_run(m=m, alphabet=alphabet, k_values=ks, value_radius=radius,
                world_family=family, q_grid=("1/4", "1/2", "3/4"),
                q_denominator=4, max_worlds=max_worlds)
            atomic_json(path, payload)
        records.append({"kind": "exact", "path": str(path), "candidate_killed": payload["candidate_killed"],
                        "evidence_class": payload["evidence_class"]})
        candidate = payload.get("best_ratio_witness")
        candidate_ratio = float(Fraction(candidate["h3_ratio"])) if candidate else 0.0
        if candidate and (best is None or candidate_ratio > best[0]):
            best = (candidate_ratio, str(path))
        killed = killed or payload["candidate_killed"]
        if killed: break

    if not killed:
        rr = int(restarts or (5000 if profile == "deep" else 100))
        ss = int(steps or (500 if profile == "deep" else 30))
        for seed in seeds:
            for m, alphabet, k, q_mode, optimize_q in _directed_grid(profile):
                name = f"directed_m{m}_a{alphabet}_k{k}_{q_mode}_s{seed}.json"; path = out_root / name
                if resume and path.exists(): payload = json.loads(path.read_text())
                else:
                    payload = directed_run(rr, ss, m, alphabet, k, seed, q_mode=q_mode,
                        optimize_q=optimize_q, seed_witness=witness, local_restart_fraction=.6)
                    atomic_json(path, payload)
                candidate = payload.get("best_witness")
                ratio = float(candidate.get("h3_ratio", 0)) if candidate else 0.0
                records.append({"kind": "directed", "path": str(path), "candidate_killed": payload["candidate_killed"],
                                "ratio": ratio, "mechanism": candidate.get("mechanism_class") if candidate else None})
                if best is None or ratio > best[0]: best = (ratio, str(path))
                killed = killed or payload["candidate_killed"]
                if killed: break
            if killed: break

    gates = {
        "exact_binary_coordinate_specific_q_complete": any(r["kind"] == "exact" and r["evidence_class"] == "EXHAUSTIVE_FINITE_EXACT_RATIONAL" for r in records),
        "m3_deep_all_q_modes": profile == "deep" and all(any(f"directed_m3_a2_k{k}_{q}" in r["path"] for r in records)
            for k in (1, 2) for q in ("uniform", "random", "skewed", "boundary")),
        "m4_deep": profile == "deep" and any("directed_m4_" in r["path"] for r in records),
        "m5_directed": profile == "deep" and any("directed_m5_a2" in r["path"] for r in records),
        "witness_local_campaign": bool(witness) and any(r["kind"] == "directed" for r in records),
    }
    proof_gate_open = bool(not killed and all(gates.values()))
    summary = {"protocol_version": PROTOCOL_VERSION, "profile": profile,
        "evidence_class": "FALSIFICATION_CAMPAIGN_NOT_PROOF", "candidate_killed": killed,
        "best_ratio": None if best is None else best[0], "best_artifact": None if best is None else best[1],
        "records": records, "proof_attack_gates": gates, "serious_lean_proof_gate_open": proof_gate_open,
        "optimized_objective": "J_H3=(T(S_C)-min_equal_cardinality_T T(T))/((m-1)delta_square)",
        "proof_routes_if_open": ["prove H3-old signed transfer comparison",
            "combine H3-old with surrogate Top-C optimality",
            "or prove the final selected-vs-competitor inequality directly"]}
    write_artifact_with_provenance(out_root / "CAMPAIGN_SUMMARY.json", summary, protocol={
        "protocol_version": PROTOCOL_VERSION, "profile": profile, "seeds": list(seeds),
        "witness": witness, "restarts": restarts, "steps": steps,
    }, evidence_class=summary["evidence_class"], chain="D6")
    return summary


def main(argv=None):
    p = argparse.ArgumentParser(); p.add_argument("--out-root", default="research/high_value_extensions/d6/half_factor_campaign")
    p.add_argument("--profile", choices=("quick", "deep"), default="quick")
    p.add_argument("--seeds", nargs="+", type=int, default=[701]); p.add_argument("--seed-witness")
    p.add_argument("--resume", action="store_true"); p.add_argument("--restarts", type=int); p.add_argument("--steps", type=int)
    a = p.parse_args(argv); payload = run(a.out_root, a.profile, a.seeds, a.seed_witness, a.resume, a.restarts, a.steps)
    print(json.dumps(payload, indent=2)); return 2 if payload["candidate_killed"] else 0


if __name__ == "__main__": raise SystemExit(main())
