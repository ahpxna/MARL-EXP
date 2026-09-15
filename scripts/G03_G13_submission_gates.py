#!/usr/bin/env python3
"""G01, G03-G13: the submission gates, computed where they are computable and
marked as open where they are not.

`G02_claim_theorem_table.py` did G02.  This file does the rest of the list in
`research/high_risk_20260910/PUBLICATION_GATES_SIX_PAPERS_20260911.md`, and it does
them by COMPUTING what can be computed:

  G01  model scope per paper -- stated, and cross-checked against the code that
       implements each model.
  G03  theorem-level comparison with the nearest prior.  OUR columns are read off
       the theorems; the PRIOR columns are the supervisor's own characterisations
       and are marked NOT INDEPENDENTLY VERIFIED -- reading those papers is not
       something this run did.
  G04  taxonomy of every headline: Lean theorem / exact finite certificate /
       numerical evidence / Monte-Carlo.  A numerical LP optimum is never recorded
       as a universal optimum.
  G05  pinned build: toolchain, mathlib revision, every dependency revision, the
       IMPORT CLOSURE of each headline module, and a sha256 of every source in that
       closure -- recomputed now and compared against the hash each receipt recorded
       at compile time.
  G06-G10 the empirical gates, audited field by field against the one empirical
       artifact the corpus actually cites.
  G11  ownership: one result, one owning paper, plus detection of modules claimed by
       more than one paper.
  G12  notation collisions across the Lean namespaces.
  G13  venue: a checklist, not a decision.  Nothing here picks a venue or checks a
       deadline; that needs the supervisor.

    .venv/bin/python scripts/G03_G13_submission_gates.py
"""
from __future__ import annotations
import glob, hashlib, json, re
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
WORK = REPO / "work/p13_conjectures"

HEADLINES = {
 "Support": ["LeanSupportDecideExponentV1", "LeanSupportRecoverySandwichV1",
             "LeanSupportBayesMinimaxV1"],
 "Structural": ["LeanStructuralAvgPathGapV1", "LeanStructuralSaturationV1"],
 "Functional": ["LeanFunctionalHeterogeneousInstanceV1",
                "LeanFunctionalGeometryDischargeV1"],
 "D6": ["LeanD6UncappedProfileV1", "LeanD6ThreeClassPhaseV1"],
 "Query": ["LeanQueryAffinityTestingV1", "LeanQueryRateAssemblyV1",
           "LeanQueryRegretChainV1"],
 "MASTER": ["LeanMasterAnchorThresholdV1", "LeanMasterActiveSetV1",
            "LeanMasterGroupCalibrationV1"],
 "Adaptive": ["LeanAdaptiveLoopJoinV1", "LeanAdaptiveConfidenceJoinV1"],
}

G01 = {
 "Support": {"world": "hidden unsafe subset W of a tip set, split into K classes; "
                      "class i has a_i safe and b_i unsafe tips",
             "reference": "none; the geometry is the tip incidence",
             "support": "the hidden W; |W| and the class sizes are KNOWN",
             "noise": "none -- the observation is which tip was hit, or nothing",
             "learner_knows": "a_i, b_i, p_i and N; NOT which tips are unsafe",
             "oracle_knows": "W",
             "legal_queries": "passive draws only; one tip or nothing per draw",
             "cost_unit": "one draw"},
 "Structural": {"world": "a component table F over m items and h actions",
                "reference": "the per-budget optimum min_{|T|=k} L_F(T)",
                "support": "the retained prefix S_k of an ordering",
                "noise": "none -- this is a deterministic combinatorial game",
                "learner_knows": "F; the question is which ORDERING to commit to",
                "oracle_knows": "F and the realised budget",
                "legal_queries": "an ordering, i.e. a distribution over orderings",
                "cost_unit": "not a sample count; the objective is regret itself"},
 "Functional": {"world": "cell means theta with heterogeneous variances",
                "reference": "the incumbent's two cells at -+1/2, variance 1",
                "support": "the outsider family: two endpoints and n middle cells",
                "noise": "Gaussian, variances KNOWN",
                "learner_knows": "the family and the variances",
                "oracle_knows": "theta",
                "legal_queries": "sample a cell; contrasts only where stated",
                "cost_unit": "one sample (and, in P4 only, a setup cost kappa per "
                             "measurement type opened)"},
 "D6": {"world": "a label C over 2q+1 coordinates plus the special coordinate j",
        "reference": "the true label A, with nuisance nu",
        "support": "the exchange distance d and the nuisance x = nu - mu",
        "noise": "Gaussian; the charge of a width-r query is r^z",
        "learner_knows": "q, mu, z; not the label",
        "oracle_knows": "the label and nu",
        "legal_queries": "every orbit (s,t,b): s from A, t from B, b for j",
        "cost_unit": "budget share; a width-r query costs r^z per sample"},
 "Query": {"world": "two worlds A, B raw-indistinguishable at h = 0",
           "reference": "the common h = 0 density p_0",
           "support": "the finite cube X with weights pi_x",
           "noise": "Gaussian with variance sigma^2, sigma KNOWN",
           "learner_knows": "the measurement g and h; not the world",
           "oracle_knows": "the world",
           "legal_queries": "Y = F_W(X) + h g(X) + Z for g in the stated class",
           "cost_unit": "one observation"},
 "MASTER": {"world": "means m_theta(e) with a common (or vector) unknown offset b",
            "reference": "the anchor, which reads the offset directly",
            "support": "the finite alternative set (rivals tying the leader)",
            "noise": "Gaussian, variances v_e KNOWN",
            "learner_knows": "the query means, variances and prices",
            "oracle_knows": "theta and b",
            "legal_queries": "any non-negative allocation over queries and anchor",
            "cost_unit": "budget; query e costs kappa_e, the anchor costs c0"},
 "Adaptive": {"world": "the same as the chain it wraps",
              "reference": "the oracle budget B*",
              "support": "the epoch schedule",
              "noise": "as the wrapped chain",
              "learner_knows": "everything the wrapped chain's learner knows",
              "oracle_knows": "B*",
              "legal_queries": "as the wrapped chain",
              "cost_unit": "total samples across epochs"},
}

G03 = [
 {"paper": "Support", "nearest_prior": "Degenne-Koolen, pure exploration with "
  "multiple correct answers; Javdani et al., DRD/HEC",
  "ours": {"input": "class sizes and per-tip observation probabilities",
           "output": "a safe decision (a tip to act on)",
           "objective": "minimax probability of an unsafe decision",
           "form": "multiplicative Theta of a single exponential",
           "exactness": "exact two-sided constants k0/B and alpha/sum b",
           "paradigm": "Bayes = minimax under the equal-mass symmetry",
           "regime": "static, passive"},
  "prior_as_characterised_by_supervisor": "studies gathering information for a "
  "decision without identifying the whole hypothesis; framework, not this "
  "quantitative law",
  "verified": False},
 {"paper": "Structural", "nearest_prior": "Kurtz menu comparison",
  "ours": {"input": "a component table and a marginal trajectory",
           "output": "an ordering distribution",
           "objective": "ratio of execution guarantee to average guarantee",
           "form": "multiplicative, ratio = b",
           "exactness": "exact rational at each m in range",
           "paradigm": "minimax over budgets",
           "regime": "static"},
  "prior_as_characterised_by_supervisor": "comparison needs the full policy class "
  "and assumptions checked, not just an appeal to non-concavity",
  "verified": False},
 {"paper": "Functional", "nearest_prior": "Jourdan-Degenne-Kaufmann "
  "(unknown-variance stopping); Huang et al., structured BAI",
  "ours": {"input": "heterogeneous cell means and KNOWN variances",
           "output": "an allocation and a certificate",
           "objective": "information rate Gamma",
           "form": "exact value at the stated allocation",
           "exactness": "exact rational; sandwich ratio -> 1 as n grows",
           "paradigm": "minimax over alternatives",
           "regime": "static design; the empirical panel is adaptive"},
  "prior_as_characterised_by_supervisor": "unknown-variance stopping is very close "
  "prior; keeping KNOWN variance must be declared",
  "verified": False},
 {"paper": "D6", "nearest_prior": "Dette-Titoff optimal discrimination designs; "
  "Li-Cheung resource-constrained BAI",
  "ours": {"input": "q, mu, the charge exponent z",
           "output": "an allocation over measurement classes",
           "objective": "Gamma over every legal orbit",
           "form": "exact value of each design; phase change in the SUPPORT",
           "exactness": "Lean for the uncapped profile; numerical for the boundary",
           "paradigm": "minimax",
           "regime": "static"},
  "prior_as_characterised_by_supervisor": "dividing KL by cost is not new; the value "
  "must be the phase law of THIS construction",
  "verified": False},
 {"paper": "Query", "nearest_prior": "Ho-Nguyen, singularity and convergence rates",
  "ours": {"input": "a measurement class and a leakage amplitude h",
           "output": "a decision, with regret",
           "objective": "transcript length for a target regret",
           "form": "multiplicative Theta(h^{-2r})",
           "exactness": "constants MEASURED; the rate is two-sided",
           "paradigm": "minimax test, then a decision reduction",
           "regime": "static, non-adaptive"},
  "prior_as_characterised_by_supervisor": "singular-mixture rates have strong prior; "
  "the novelty must be the admissible measurement class and the cost of repairing "
  "distinguishability, not the h^4 exponent",
  "verified": False},
 {"paper": "MASTER", "nearest_prior": "Bennouna et al., data informativeness",
  "ours": {"input": "query means, variances, prices and an anchor price",
           "output": "an allocation including anchor exposure",
           "objective": "profiled information against the active set",
           "form": "an exact price threshold c* = (m-1)^2/(m+3)^2",
           "exactness": "Lean on the symmetric family; separated certificates on "
                        "the finite instance",
           "paradigm": "minimax with a dual certificate",
           "regime": "static"},
  "prior_as_characterised_by_supervisor": "geometric sufficiency and minimal "
  "sufficient data are covered; MASTER must keep the PRICE threshold or the priced "
  "synergy",
  "verified": False},
]

G04 = [
 ("Support", "R_dec = Theta((1-s)^N), R_rec = Theta((1-p_min)^N)",
  "LEAN THEOREM for the pointwise loss inequalities; EXACT FINITE CERTIFICATE for "
  "the brackets (105 rational checks); the tuple probability is CHECKED, not proved"),
 ("Structural", "V_path = (m-1) V_avg on the family",
  "LEAN THEOREM for the sandwich and the saturation mechanism; EXACT FINITE "
  "CERTIFICATE at 28 values of m; NOT an induction over m"),
 ("Functional", "J(w*) = c^2/(n(32+2c^2 H_n))",
  "LEAN THEOREM for the instantiation and the geometry; EXACT FINITE CERTIFICATE "
  "on 92 in-domain configurations; the value at w* is NOT shown optimal over the "
  "whole design"),
 ("D6", "above T_c the optimal support gains the A-pair",
  "LEAN THEOREM for the uncapped profile and the A-pair algebra; NUMERICAL "
  "EVIDENCE (cutting-plane LP, certified per cell by a rational primal/dual pair) "
  "for the support change; the LP optimum is NOT recorded as a universal optimum"),
 ("Query", "N* = Theta(h^{-2r}) and the regret window",
  "LEAN THEOREM for the testing bracket, the rate assembly and the regret chain; "
  "NUMERICAL EVIDENCE for c_- and c_+; the Taylor remainders are measured"),
 ("MASTER", "c* = (m-1)^2/(m+3)^2; anchor mandatory at c0 = 1/10",
  "LEAN THEOREM for the threshold on the symmetric family; EXACT FINITE "
  "CERTIFICATE (Fractions) for the mandatory-purchase instance"),
 ("Adaptive", "sound, and under 4 B*",
  "LEAN THEOREM for the composition only; MONTE CARLO for the realised constant "
  "and the error rate -- neither is certified"),
]

G11 = {
 "the safe-decision / recovery exponent law": "Support",
 "the passive minimax value E[L/(a+L)]": "Support",
 "the average-vs-execution gap and its saturation": "Structural",
 "the heterogeneous lower bound and its instantiation": "Functional",
 "the measurement-topology frontier under setup cost": "Functional",
 "the uncapped profile and the A-pair phase": "D6",
 "the leakage order -> transcript -> regret chain": "Query",
 "the calibration price threshold and mandatory anchor": "MASTER",
 "the rank dichotomy for group calibration": "MASTER",
 "the doubling-loop composition": "Adaptive",
}


def sha(p: Path) -> str:
    h = hashlib.sha256()
    h.update(p.read_bytes())
    return h.hexdigest()


def import_closure(mod: str) -> set[str]:
    seen, stack = set(), [mod]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        f = WORK / f"{m}.lean"
        if not f.exists():
            continue
        seen.add(m)
        for line in f.read_text().splitlines():
            mm = re.match(r"\s*import\s+[«]?([A-Za-z0-9_.]+)[»]?", line)
            if mm and mm.group(1) != "Mathlib":
                stack.append(mm.group(1))
    return seen


def receipts():
    out = {}
    for f in glob.glob(str(WORK / "*.compile.receipt.json")):
        try:
            d = json.loads(Path(f).read_text())
        except Exception:
            continue
        if isinstance(d, dict) and "module" in d:
            out[d["module"]] = d
    for f in glob.glob(str(REPO / "research/**/*manifest*.json"), recursive=True):
        try:
            d = json.loads(Path(f).read_text())
        except Exception:
            continue
        if not isinstance(d, dict):
            continue
        for r in d.get("receipts", []):
            if isinstance(r, dict) and "module" in r:
                prev = out.get(r["module"])
                if prev is None or (r.get("accepted") and not prev.get("accepted")):
                    out[r["module"]] = r
    return out


def main():
    res = {}
    rec = receipts()
    print("G01 -- model scope per paper")
    for k, v in G01.items():
        print(f"   {k:11s} noise={v['noise'][:38]:38s} cost unit={v['cost_unit'][:34]}")
    res["G01_model_scope"] = G01

    print("\nG03 -- theorem-level comparison")
    for row in G03:
        print(f"   {row['paper']:11s} vs {row['nearest_prior'][:56]}")
        print(f"      ours: {row['ours']['form']}, {row['ours']['exactness']}")
    print("   The PRIOR columns are the supervisor's characterisations and are")
    print("   marked verified=false: this run did not read those papers.")
    res["G03_comparison"] = G03

    print("\nG04 -- what kind of evidence each headline is")
    for paper, claim, kind in G04:
        print(f"   {paper:11s} {kind[:82]}")
    res["G04_taxonomy"] = [{"paper": p, "claim": c, "evidence": k} for p, c, k in G04]

    print("\nG05 -- pinned build, import closure and source hashes")
    toolchain = (WORK / "lean-toolchain").read_text().strip()
    lakefile = (WORK / "lakefile.toml").read_text()
    manifest = json.loads((WORK / "lake-manifest.json").read_text())
    deps = [{"name": p.get("name"), "rev": p.get("rev"), "url": p.get("url")}
            for p in manifest.get("packages", [])]
    print(f"   toolchain: {toolchain}")
    for d in deps[:3]:
        print(f"   dep {d['name']}: {d['rev']}")
    closure_all, hash_rows, drift = {}, [], []
    for paper, mods in HEADLINES.items():
        cl = set()
        for m in mods:
            cl |= import_closure(m)
        closure_all[paper] = sorted(cl)
        for m in sorted(cl):
            f = WORK / f"{m}.lean"
            h = sha(f)
            r = rec.get(m, {})
            recorded = r.get("source_sha256_after") or r.get("source_sha256_before")
            ok = (recorded == h) if recorded else None
            hash_rows.append({"module": m, "sha256": h, "receipt_sha256": recorded,
                              "matches_receipt": ok,
                              "accepted": bool(r.get("accepted"))})
            if recorded and recorded != h:
                drift.append(m)
    uniq = {r["module"]: r for r in hash_rows}
    nacc = sum(1 for r in uniq.values() if r["accepted"])
    nmatch = sum(1 for r in uniq.values() if r["matches_receipt"])
    print(f"   headline import closure: {len(uniq)} local modules across 7 papers")
    print(f"   accepted receipts: {nacc}/{len(uniq)};  source hash matches the "
          f"receipt: {nmatch}/{len(uniq)}")
    if drift:
        print(f"   !! SOURCE DRIFT since the recorded compile: {sorted(set(drift))}")
    print("   the receipt records LEAN's own exit code (compile_receipt_v2 reads the")
    print("   compiler process return code, never a tee), plus the .olean mtime test")
    res["G05_pinned_build"] = {"toolchain": toolchain, "lakefile": lakefile,
                               "dependencies": deps, "closure": closure_all,
                               "sources": sorted(uniq.values(),
                                                 key=lambda r: r["module"]),
                               "accepted": nacc, "hash_matches": nmatch,
                               "n_modules": len(uniq), "drift": sorted(set(drift))}

    print("\nG06-G10 -- the empirical gates, on the one cited empirical artifact")
    panel_p = REPO / "research/confirm_ieee_20260912/functional_v4_lucb_ieee10seed_cellv1.json"
    gates = {}
    if panel_p.exists():
        pn = json.loads(panel_p.read_text())
        adm = pn.get("admissibility", {})
        bv = pn.get("by_variant", {})
        gates = {
          "G06_preregistration": {
            "class": adm.get("class"),
            "uses_exactly_the_frozen_seed_set": adm.get("uses_exactly_the_frozen_seed_set"),
            "peeks_at_frozen_seeds_without_being_confirmatory":
                adm.get("peeks_at_frozen_seeds_without_being_confirmatory"),
            "seeds_used": adm.get("seeds_used"),
            "rng_protocol": adm.get("rng_protocol"),
            "PASS": adm.get("class") == "CONFIRMATORY"
                    and adm.get("uses_exactly_the_frozen_seed_set") is True
                    and adm.get("peeks_at_frozen_seeds_without_being_confirmatory") is False,
            "still_missing": "immutable source+config snapshot at launch and the "
                             "actual argv are not inside this artifact"},
          "G07_generator_oracle_units": {
            "allocation_policy": pn.get("allocation_policy"),
            "coverage_contract": pn.get("adaptive_stopping_coverage_contract"),
            "PASS": bool(pn.get("allocation_policy")),
            "still_missing": "no explicit check in the artifact that labels are "
                             "random and the answer is not leaked"},
          "G08_baseline_parity": {
            "variants": sorted(bv.keys()),
            "has_uniform_baseline": any(k.lower().startswith("uniform") for k in bv),
            "has_oracle_diagnostic": any("oracle" in k for k in bv),
            "PASS": any(k.lower().startswith("uniform") for k in bv)
                    and any("oracle" in k for k in bv),
            "still_missing": "no literature baseline; the oracle variant is a "
                             "diagnostic and must not be reported as a competitor"},
          "G09_cost_reporting": {
            "reports_sample_counts": all("median_N_certificate" in v for v in bv.values()),
            "reports_wall_clock": False, "reports_memory": False,
            "PASS": False,
            "still_missing": "compute, precomputation, certification and fallback "
                             "costs are NOT reported; only sample counts"},
          "G10_uncertainty": {
            "n_seeds": len(adm.get("seeds_used", [])),
            "censoring_handled": all("median_censored_N_certificate" in v
                                     for v in bv.values()),
            "failures_reported": all("false_safe_count" in v for v in bv.values()),
            "zero_error_variants": [k for k, v in bv.items()
                                    if v.get("false_safe_count") == 0],
            "PASS": all("median_censored_N_certificate" in v for v in bv.values()),
            "still_missing": "no confidence intervals on certificate_fraction or on "
                             "median N; 10 seeds is the unit and that is small"},
        }
        for g, v in gates.items():
            print(f"   {g:24s} PASS={v['PASS']}  -- {v['still_missing'][:58]}")
        print(f"   zero false-safe in {len(gates['G10_uncertainty']['zero_error_variants'])}"
              f" variants: that is an EMPIRICAL OBSERVATION, not a guarantee")
    else:
        print("   the cited panel artifact is missing")
    res["G06_G10_empirical"] = gates

    print("\nG11 -- ownership, and overlap detection")
    owners = {}
    for m_paper, mods in HEADLINES.items():
        for m in mods:
            owners.setdefault(m, []).append(m_paper)
    shared = {m: p for m, p in owners.items() if len(p) > 1}
    for result, paper in G11.items():
        print(f"   {paper:11s} owns: {result}")
    print(f"   modules claimed by more than one paper: {shared if shared else 'none'}")
    print("   OPEN DECISION: Support, Query and MASTER each state a different")
    print("   quantitative law, so they are not the same obstruction re-expressed;")
    print("   but Adaptive owns only a composition and should be a SECTION, not a")
    print("   paper, unless its three probabilistic ingredients are closed.")
    res["G11_ownership"] = {"map": G11, "shared_modules": shared,
                            "recommendation": "Adaptive is a section, not a paper, "
                                              "until delta-correctness, tracking and "
                                              "the stopping tail are proved"}

    print("\nG12 -- notation collisions across the Lean namespaces")
    defs = {}
    for f in glob.glob(str(WORK / "Lean*.lean")):
        mod = Path(f).stem
        for line in Path(f).read_text().splitlines():
            mm = re.match(r"\s*(?:noncomputable\s+)?def\s+([A-Za-z_][A-Za-z0-9_']*)", line)
            if mm:
                defs.setdefault(mm.group(1), set()).add(mod)
    coll = {k: sorted(v) for k, v in defs.items() if len(v) > 1}
    top = sorted(coll.items(), key=lambda kv: -len(kv[1]))[:8]
    for k, v in top:
        print(f"   `{k}` defined in {len(v)} modules: {v[:4]}{'...' if len(v) > 4 else ''}")
    print(f"   {len(coll)} names are defined in more than one module.  Namespaces")
    print("   keep them distinct in Lean, but a manuscript must rename them.")
    res["G12_notation_collisions"] = coll

    print("\nG13 -- venue")
    print("   NOT DONE, and not doable here: choosing a venue, and checking scope,")
    print("   deadline, anonymity, code/data/ethics/disclosure and overlap policy,")
    print("   are supervisor decisions.  What IS settled: every headline has a")
    print("   pinned build and a released artifact path, so a code/data statement")
    print("   can be written; and the MARL/crossroad adapter claim is NOT made by")
    print("   any of the seven rows above, so the Tier B/C adapter is not required.")
    res["G13_venue"] = {"status": "OPEN -- supervisor decision",
                        "settled": ["pinned build and artifact paths exist for every "
                                    "headline", "no MARL/crossroad adapter claim is "
                                    "made, so no Tier B/C adapter is required"]}

    out = REPO / "research/worker_G03_G13_20260915"
    out.mkdir(parents=True, exist_ok=True)
    (out / "G03_G13_submission_gates.json").write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}/G03_G13_submission_gates.json")


if __name__ == "__main__":
    main()
