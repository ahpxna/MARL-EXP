#!/usr/bin/env python3
"""ONE graphify knowledge graph over CIG-AMF source: Python (tree-sitter AST)
   + Lean 4 (lean_extract.py). Zero LLM calls.

   dedup=False on purpose: graphify's fuzzy dedup merges nodes with similar
   labels, which across 2482 Lean theorems would silently fuse DISTINCT
   declarations (e.g. D6AllocationPhaseThreeDual.actual_joint_bound vs
   D6PhaseThreeDual.actual_joint_bound). What it would have merged is written
   to dedup_would_merge.json instead, for review - never applied.
"""
import json, sys, time, traceback
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
OUT  = Path(sys.argv[2]).resolve()
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(Path(__file__).parent))

from graphify.extract import extract, collect_files
from graphify.build import build
from graphify.cluster import cluster, score_all, label_communities_by_hub
from graphify import analyze, report, export
from lean_extract import extract_lean

def log(m): print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)

PY_DIRS = ["scripts", "utils", "models", "envs", "research_chains",
           "observatory", "tests", "work/p13_conjectures"]
EXCLUDE = {".lake", ".venv", "venv", "site-packages", "__pycache__", ".git",
           "external_envs", "node_modules",
           "_audit"}   # never index graphify's own output / the audit workspace

py_paths = sorted({f for d in PY_DIRS if (ROOT / d).exists()
                   for f in collect_files(ROOT / d, root=ROOT)
                   if not any(p in EXCLUDE for p in f.parts)})
log(f"python/other files: {len(py_paths)}")
py_ext = extract(py_paths, root=ROOT)
log(f"python extraction: {len(py_ext['nodes'])} nodes, {len(py_ext['edges'])} edges")

lean_paths = sorted(p for p in (ROOT / "work").rglob("*.lean")
                    if not any(part in EXCLUDE for part in p.parts))
log(f"lean files: {len(lean_paths)}")
lean_ext = extract_lean(lean_paths, ROOT)
log(f"lean extraction: {len(lean_ext['nodes'])} nodes, {len(lean_ext['edges'])} edges")
(OUT / "extraction_python.json").write_text(json.dumps(py_ext), encoding="utf-8")
(OUT / "extraction_lean.json").write_text(json.dumps(lean_ext), encoding="utf-8")

log("building (dedup OFF) ...")
G = build([py_ext, lean_ext], dedup=False, root=ROOT)
log(f"graph: {G.number_of_nodes()} nodes, {G.number_of_edges()} edges")

log("recording what fuzzy dedup WOULD have merged (not applied) ...")
try:
    Gm = build([py_ext, lean_ext], dedup=True, root=ROOT)
    merged = sorted(set(G.nodes()) - set(Gm.nodes()))
    (OUT / "dedup_would_merge.json").write_text(
        json.dumps({"count": len(merged), "nodes": merged}, indent=1), encoding="utf-8")
    log(f"  dedup would have merged {len(merged)} nodes - NOT applied")
except Exception as e:
    log(f"  dedup probe failed: {e}")

log("clustering ...")
communities = cluster(G)
cohesion = score_all(G, communities)
labels = label_communities_by_hub(G, communities)
log(f"communities: {len(communities)}")

log("analysing ...")
gods     = analyze.god_nodes(G, top_n=40)
surprise = analyze.surprising_connections(G, communities, top_n=25)
try:    questions = analyze.suggest_questions(G, communities, labels, top_n=12)
except Exception: questions = []

# import cycles need a DIRECTED graph
log("directed build for import cycles ...")
Gdir = build([py_ext, lean_ext], directed=True, dedup=False, root=ROOT)
cycles = analyze.find_import_cycles(Gdir, top_n=60)
log(f"import cycles: {len(cycles)}")
(OUT / "import_cycles.json").write_text(json.dumps(cycles, indent=1), encoding="utf-8")

detection = {"total_files": len(py_paths) + len(lean_paths),
             "files": {"code": [str(p) for p in py_paths],
                       "lean": [str(p) for p in lean_paths]},
             "total_words": 0, "scan_root": str(ROOT)}
try:
    md = report.generate(G, communities, cohesion, labels, gods, surprise,
                         detection, {"corpus_tokens": 0, "graph_tokens": 0},
                         str(ROOT), suggested_questions=questions)
    (OUT / "GRAPH_REPORT.md").write_text(md, encoding="utf-8")
    log("GRAPH_REPORT.md written")
except Exception:
    log("report.generate failed:\n" + traceback.format_exc())

export.to_json(G, communities, str(OUT / "graph.json"), force=True, community_labels=labels)
log("graph.json written")
try:
    export.to_html(G, communities, str(OUT / "graph.html"), community_labels=labels)
    log("graph.html written (full)")
except Exception as e:
    log(f"full graph.html skipped: {e}")

# Lean-only subgraph: small enough to render, and the half that matters
log("lean-only subgraph ...")
GL = build([lean_ext], dedup=False, root=ROOT)
cl = cluster(GL); ll = label_communities_by_hub(GL, cl)
export.to_json(GL, cl, str(OUT / "graph_lean.json"), force=True, community_labels=ll)
try:
    export.to_html(GL, cl, str(OUT / "graph_lean.html"), community_labels=ll)
    log("graph_lean.html written")
except Exception as e:
    log(f"lean html failed: {e}")
log("DONE")
