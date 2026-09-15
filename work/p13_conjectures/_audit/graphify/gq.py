#!/usr/bin/env python3
"""Zero-dependency query tool over the graphify export of this repo.

  gq.py find <substr> [--type lean_theorem] [--file-substr X] [--limit N]
  gq.py node <id|label|fq_name>
  gq.py deps <id|label> [--depth N] [--rel uses,declares]      # what it depends on
  gq.py rdeps <id|label> [--depth N] [--rel uses]              # what depends on it
  gq.py module <ModuleName>                                    # declarations + imports
  gq.py file <path-substr>                                     # declarations in a file
  gq.py path <a> <b>                                           # shortest path
  gq.py stats

Graph: graph.json (nodes: lean_theorem/lean_def/lean_module/python), links carry
`relation` in {uses, declares, calls, contains, imports, imports_from, method,
references, rationale_for, indirect_call, inherits, defines, re_exports} and a
`confidence` of EXTRACTED (explicit in source) or INFERRED (resolved).
"""
import json
import os
import pickle
import sys
from collections import defaultdict, deque

HERE = os.path.dirname(os.path.abspath(__file__))
GRAPH = os.path.join(HERE, "graph.json")
# Lean side re-extracted deterministically (lean_extract.py); graph.json's Lean
# half is frozen at the build date and misses modules written since.
FRESH_LEAN = os.path.join(HERE, "extraction_lean_fresh_20260912.json")
CACHE = os.path.join(HERE, ".gq_cache.pkl")


def load():
    srcs = [p for p in (GRAPH, FRESH_LEAN) if os.path.exists(p)]
    if os.path.exists(CACHE) and all(os.path.getmtime(CACHE) > os.path.getmtime(p) for p in srcs):
        with open(CACHE, "rb") as f:
            return pickle.load(f)
    with open(GRAPH) as f:
        g = json.load(f)
    nodes = {n["id"]: n for n in g["nodes"] if not str(n.get("type", "")).startswith("lean")}
    links = list(g["links"])
    if os.path.exists(FRESH_LEAN):
        with open(FRESH_LEAN) as f:
            lean = json.load(f)
        for n in lean["nodes"]:
            nodes[n["id"]] = n
        links = [e for e in links
                 if e["source"] in nodes and e["target"] in nodes] + lean["edges"]
    out, inn = defaultdict(list), defaultdict(list)
    for e in links:
        out[e["source"]].append(e)
        inn[e["target"]].append(e)
    data = (nodes, dict(out), dict(inn))
    with open(CACHE, "wb") as f:
        pickle.dump(data, f)
    return data


def resolve(nodes, key):
    if key in nodes:
        return [key]
    k = key.lower()
    exact = [i for i, n in nodes.items()
             if n.get("label", "").lower() == k or n.get("fq_name", "").lower() == k]
    if exact:
        return exact
    return [i for i, n in nodes.items()
            if k in i.lower() or k in n.get("label", "").lower() or k in n.get("fq_name", "").lower()]


def desc(n):
    loc = f"{n.get('source_file','?')}:{n.get('source_location','')}"
    return f"[{n.get('type','py')}] {n.get('fq_name') or n.get('label')}  ({loc})"


def cmd_find(nodes, args):
    sub = args[0].lower()
    typ = flag(args, "--type")
    fsub = flag(args, "--file-substr")
    limit = int(flag(args, "--limit") or 60)
    hits = []
    for n in nodes.values():
        hay = f"{n.get('label','')} {n.get('fq_name','')} {n['id']}".lower()
        if sub not in hay:
            continue
        if typ and n.get("type") != typ:
            continue
        if fsub and fsub not in n.get("source_file", ""):
            continue
        hits.append(n)
    hits.sort(key=lambda n: (len(n.get("label", "")), n.get("source_file", "")))
    print(f"{len(hits)} hit(s)" + (f", showing {limit}" if len(hits) > limit else ""))
    for n in hits[:limit]:
        print("  " + desc(n))


def cmd_node(nodes, out, inn, args):
    for nid in resolve(nodes, args[0])[:5]:
        n = nodes[nid]
        print("=" * 90)
        print(desc(n))
        for k, v in sorted(n.items()):
            if k not in ("id", "label", "type", "source_file", "source_location", "fq_name"):
                print(f"    {k}: {str(v)[:110]}")
        for tag, edges, other in (("OUT", out.get(nid, []), "target"), ("IN", inn.get(nid, []), "source")):
            by = defaultdict(list)
            for e in edges:
                by[e["relation"]].append(e)
            for rel, es in sorted(by.items()):
                names = []
                for e in es[:40]:
                    o = nodes.get(e[other], {})
                    names.append(o.get("fq_name") or o.get("label") or e[other])
                more = f" (+{len(es)-40})" if len(es) > 40 else ""
                print(f"  {tag} {rel} ({len(es)}): " + ", ".join(names) + more)


def closure(nodes, adj, start, depth, rels, other):
    seen, order = {start: 0}, []
    q = deque([(start, 0)])
    while q:
        cur, d = q.popleft()
        if d >= depth:
            continue
        for e in adj.get(cur, []):
            if rels and e["relation"] not in rels:
                continue
            nxt = e[other]
            if nxt not in seen:
                seen[nxt] = d + 1
                order.append((nxt, d + 1, e["relation"], cur))
                q.append((nxt, d + 1))
    return order


def cmd_closure(nodes, adj, args, other, title):
    ids = resolve(nodes, args[0])
    if not ids:
        print("no match")
        return
    nid = ids[0]
    if len(ids) > 1:
        print(f"note: {len(ids)} matches, using {nid}")
    depth = int(flag(args, "--depth") or 1)
    rels = set((flag(args, "--rel") or "").split(",")) - {""} or None
    print(f"{title} of {desc(nodes[nid])}  depth={depth} rel={rels or 'any'}")
    for tid, d, rel, src in closure(nodes, adj, nid, depth, rels, other):
        t = nodes.get(tid, {"label": tid})
        print(f"  {'  '*(d-1)}{d}. [{rel}] {desc(t) if 'type' in t else tid}")


def cmd_module(nodes, out, inn, args):
    name = args[0]
    mid = f"lean_module_{name}" if not name.startswith("lean_module_") else name
    if mid not in nodes:
        cands = [i for i in nodes if i.startswith("lean_module_") and name.lower() in i.lower()]
        if not cands:
            print("no module")
            return
        mid = cands[0]
    print(desc(nodes[mid]))
    decls = [e["target"] for e in out.get(mid, []) if e["relation"] == "declares"]
    imps = [e["target"] for e in out.get(mid, []) if e["relation"] in ("imports", "imports_from")]
    rimps = [e["source"] for e in inn.get(mid, []) if e["relation"] in ("imports", "imports_from")]
    print(f"\nIMPORTS ({len(imps)}): " + ", ".join(nodes.get(i, {}).get("label", i) for i in imps))
    print(f"IMPORTED BY ({len(rimps)}): " + ", ".join(nodes.get(i, {}).get("label", i) for i in rimps))
    print(f"\nDECLARES ({len(decls)}):")
    for d in sorted(decls, key=lambda x: nodes.get(x, {}).get("source_location", "")):
        n = nodes.get(d, {})
        print(f"  {n.get('source_location',''):>7}  [{n.get('type','')}] {n.get('label', d)}")


def cmd_file(nodes, args):
    sub = args[0]
    hits = [n for n in nodes.values() if sub in n.get("source_file", "")]
    hits.sort(key=lambda n: int((n.get("source_location") or "L0")[1:].split("-")[0] or 0))
    print(f"{len(hits)} declaration(s) in files matching {sub!r}")
    for n in hits:
        print(f"  {n.get('source_location',''):>7}  [{n.get('type','')}] {n.get('label')}   <{n.get('source_file')}>")


def cmd_path(nodes, out, inn, args):
    a, b = resolve(nodes, args[0]), resolve(nodes, args[1])
    if not a or not b:
        print("no match")
        return
    src, dst = a[0], b[0]
    prev, q = {src: None}, deque([src])
    while q:
        cur = q.popleft()
        if cur == dst:
            break
        for e in out.get(cur, []) + inn.get(cur, []):
            nxt = e["target"] if e["source"] == cur else e["source"]
            if nxt not in prev:
                prev[nxt] = (cur, e["relation"])
                q.append(nxt)
    if dst not in prev:
        print("no path")
        return
    chain, cur = [], dst
    while cur:
        step = prev[cur]
        chain.append((cur, step[1] if step else None))
        cur = step[0] if step else None
    for nid, rel in reversed(chain):
        print(f"  {'--['+rel+']-->' if rel else '   '} {desc(nodes[nid])}")


def flag(args, name):
    if name in args:
        i = args.index(name)
        if i + 1 < len(args):
            return args[i + 1]
    for a in args:
        if a.startswith(name + "="):
            return a.split("=", 1)[1]
    return None


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    nodes, out, inn = load()
    cmd, args = sys.argv[1], sys.argv[2:]
    if cmd == "find":
        cmd_find(nodes, args)
    elif cmd == "node":
        cmd_node(nodes, out, inn, args)
    elif cmd == "deps":
        cmd_closure(nodes, out, args, "target", "DEPENDENCIES")
    elif cmd == "rdeps":
        cmd_closure(nodes, inn, args, "source", "REVERSE DEPENDENCIES")
    elif cmd == "module":
        cmd_module(nodes, out, inn, args)
    elif cmd == "file":
        cmd_file(nodes, args)
    elif cmd == "path":
        cmd_path(nodes, out, inn, args)
    elif cmd == "stats":
        from collections import Counter
        print("nodes:", len(nodes), Counter(n.get("type", "python") for n in nodes.values()).most_common())
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
