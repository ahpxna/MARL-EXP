"""One-command source/test/experiment validation for the current six reports.

This wrapper deliberately separates hard validation failures from scientific
falsification findings.  It runs:
  1. source-only Python compilation;
  2. the repository pytest suite (unless explicitly skipped);
  3. the current six-report experiment suite.

External/confirmatory obligations are not silently replaced by local tests.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from research_chains.provenance import atomic_json, source_fingerprint
from scripts.compile_source_tree import run as compile_source_tree
from scripts.run_current_six_report_suite import PROFILES, run as run_six_suite

PROTOCOL_VERSION = "current_six_report_validation_v1"


def _run_pytest() -> dict:
    t0 = time.perf_counter()
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-q"],
        cwd=str(ROOT),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    text = proc.stdout or ""
    # Keep the manifest compact while retaining enough tail context to diagnose
    # a failure.  Full pytest output is written separately by run().
    tail = "\n".join(text.splitlines()[-30:])
    return {
        "returncode": int(proc.returncode),
        "pass": proc.returncode == 0,
        "seconds": float(time.perf_counter() - t0),
        "tail": tail,
        "full_output": text,
    }


def run(profile: str = "quick", seed: int = 7000,
        out_root: str = "research/current_six_reports_validation",
        skip_pytest: bool = False) -> dict:
    out = Path(out_root)
    out.mkdir(parents=True, exist_ok=True)

    compile_payload = compile_source_tree(ROOT)
    atomic_json(out / "SOURCE_COMPILE.json", compile_payload)

    if skip_pytest:
        pytest_payload = {"pass": True, "skipped": True, "returncode": None,
                          "seconds": 0.0, "tail": "SKIPPED_BY_CALLER"}
    else:
        raw = _run_pytest()
        (out / "PYTEST.log").write_text(raw.pop("full_output"), encoding="utf-8")
        pytest_payload = raw
    atomic_json(out / "PYTEST.json", pytest_payload)

    six_root = out / "six_reports"
    six_payload = run_six_suite(profile=profile, seed=seed, out_root=str(six_root))

    hard_pass = bool(
        compile_payload.get("pass")
        and pytest_payload.get("pass")
        and six_payload.get("hard_gate_pass")
    )
    payload = {
        "protocol_version": PROTOCOL_VERSION,
        "profile": str(profile),
        "seed": int(seed),
        "source_fingerprint": source_fingerprint(ROOT),
        "source_compile": compile_payload,
        "pytest": pytest_payload,
        "six_report_manifest": str(six_root / "SUITE_MANIFEST.json"),
        "six_report_hard_gate_pass": bool(six_payload.get("hard_gate_pass")),
        "scientific_findings": six_payload.get("scientific_findings", {}),
        "hard_validation_pass": hard_pass,
        "scope": (
            "complete local development validation for the six current reports; "
            "external and confirmatory obligations remain fail-closed"
        ),
    }
    atomic_json(out / "VALIDATION_MANIFEST.json", payload)
    return payload


def main(argv=None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--profile", choices=PROFILES, default="quick")
    p.add_argument("--seed", type=int, default=7000)
    p.add_argument("--out-root", default="research/current_six_reports_validation")
    p.add_argument("--skip-pytest", action="store_true")
    a = p.parse_args(argv)
    payload = run(a.profile, a.seed, a.out_root, a.skip_pytest)
    print(json.dumps(payload, indent=2))
    return 0 if payload["hard_validation_pass"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
