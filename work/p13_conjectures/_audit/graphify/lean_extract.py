#!/usr/bin/env python3
"""
Deterministic Lean 4 extractor emitting graphify's extraction schema.

    {"nodes": [{id,label,source_file,source_location,type,...}],
     "edges": [{source,target,relation,confidence}]}

No LLM. No heuristic "probably". Every edge is either:
  EXTRACTED  - written literally in the source (import, declaration, fully
               qualified reference, a `sorry` token that is actually there)
  INFERRED   - a short name resolved through the enclosing namespace or an
               `open` in scope, where exactly ONE declaration matches
  AMBIGUOUS  - a short name that matches more than one declaration; emitted
               so it is visible, never silently resolved to a guess
"""
from __future__ import annotations
import json, re, sys
from pathlib import Path

# ---------------------------------------------------------------- masking

def mask(text: str) -> str:
    """Blank out comments and string literals, preserving length and newlines.

    Nested block comments are handled (Lean 4 allows them). Everything blanked
    becomes a space, so line/column offsets of the surviving code are exact.
    """
    out = list(text)
    n = len(text)
    i = 0
    depth = 0            # /- -/ nesting depth
    in_line = False      # inside --
    in_str = False       # inside "..."
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if c == "\n":
                in_line = False
            else:
                out[i] = " "
            i += 1
            continue
        if depth:
            if c == "/" and nxt == "-":
                depth += 1; out[i] = out[i + 1] = " "; i += 2; continue
            if c == "-" and nxt == "/":
                depth -= 1; out[i] = out[i + 1] = " "; i += 2; continue
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        if in_str:
            if c == "\\":
                out[i] = " "
                if i + 1 < n and text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2; continue
            out[i] = " "
            if c == '"':
                in_str = False
            i += 1
            continue
        # not in any special state
        if c == "/" and nxt == "-":
            depth = 1; out[i] = out[i + 1] = " "; i += 2; continue
        if c == "-" and nxt == "-":
            in_line = True; out[i] = out[i + 1] = " "; i += 2; continue
        if c == '"':
            in_str = True; out[i] = " "; i += 1; continue
        i += 1
    return "".join(out)

# ---------------------------------------------------------------- patterns

MODIFIERS = r"(?:@\[[^\]]*\]\s*|private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+|nonrec\s+|mutual\s+)*"
KINDS = ("theorem", "lemma", "def", "abbrev", "instance", "structure", "class",
         "inductive", "axiom", "opaque", "example", "macro", "elab", "notation")
DECL_RE = re.compile(
    r"^" + MODIFIERS + r"(" + "|".join(KINDS) + r")\b[ \t]*([^\s:({\[⦃⟨|]+)?",
    re.MULTILINE)
IMPORT_RE = re.compile(r"^import[ \t]+(.+?)[ \t]*$", re.MULTILINE)
NAMESPACE_RE = re.compile(r"^namespace[ \t]+([^\s]+)", re.MULTILINE)
END_RE = re.compile(r"^end\b[ \t]*([^\s]*)", re.MULTILINE)
OPEN_RE = re.compile(r"^open[ \t]+(?:scoped[ \t]+)?(.+?)[ \t]*$", re.MULTILINE)
# Lean identifiers: letters (incl. unicode), digits, _ ' ! ? and subscripts, dotted
IDENT_RE = re.compile(r"[A-Za-z_À-ɏͰ-Ͽ℀-⅏]"
                      r"[A-Za-z0-9_'!?À-ɏͰ-Ͽ₀-ₜ℀-⅏]*"
                      r"(?:\.[A-Za-z_À-ɏͰ-Ͽ℀-⅏]"
                      r"[A-Za-z0-9_'!?À-ɏͰ-Ͽ₀-ₜ℀-⅏]*)*")

# Trust-relevant tokens the audit cares about, matched on MASKED text only
# (so a mention inside a comment or docstring never counts).
FLAG_TOKENS = {
    "sorry":          re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])"),
    "sorryAx":        re.compile(r"(?<![A-Za-z0-9_'])sorryAx(?![A-Za-z0-9_'])"),
    "native_decide":  re.compile(r"(?<![A-Za-z0-9_'])native_decide(?![A-Za-z0-9_'])"),
    "decide":         re.compile(r"(?<![A-Za-z0-9_'])decide(?![A-Za-z0-9_'])"),
    "print_axioms":   re.compile(r"#print[ \t]+axioms"),
    "axiom_decl":     re.compile(r"^axiom\b", re.MULTILINE),
    "ofReduceBool":   re.compile(r"(?<![A-Za-z0-9_'])Lean\.ofReduceBool(?![A-Za-z0-9_'])"),
    "maxHeartbeats":  re.compile(r"set_option[ \t]+maxHeartbeats"),
    "maxRecDepth":    re.compile(r"set_option[ \t]+maxRecDepth"),
}

# Identifiers introduced as BINDERS inside a declaration are local variables,
# not references to other declarations. Without this, every `(j : I n)` binder
# resolves to whatever top-level `j`/`I`/`S` happens to exist and the graph fills
# with false `uses` edges - single letters became the top "god nodes".
_BINDER_GROUP_RE = re.compile(r"[(\{\[⦃]\s*([^:()\{\}\[\]⦃⦄]+?)\s*:")
_FORALL_RE = re.compile(r"[∀∃Σ]\s*([^,:]{1,80}?)\s*[,:]")
_FUN_RE    = re.compile(r"\bfun\s+([^,]{1,80}?)\s*(?:=>|↦)")
_TAC_RE    = re.compile(r"\b(?:intro|intros|rintro|obtain|rcases|set|let|use)\s+([^\n]{0,120})")
_ANGLE_RE  = re.compile(r"[⟨]([^⟩]{0,120})[⟩]")
_WORD_RE   = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?₀-ₜ]*")

def binder_names(body: str) -> set:
    """Local names bound inside *body*: header binders, quantifiers, lambdas,
    and the common intro/obtain/rcases tactic forms."""
    out = set()
    for rx in (_BINDER_GROUP_RE, _FORALL_RE, _FUN_RE, _TAC_RE, _ANGLE_RE):
        for m in rx.finditer(body):
            for w in _WORD_RE.findall(m.group(1)):
                out.add(w)
    return out


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1

# ---------------------------------------------------------------- per file

def parse_file(path: Path, root: Path):
    raw = path.read_text(encoding="utf-8", errors="replace")
    src = mask(raw)
    rel = str(path.relative_to(root))
    module = path.stem

    imports = []
    for m in IMPORT_RE.finditer(src):
        tgt = m.group(1).strip().strip("«»").strip()
        if tgt:
            imports.append((tgt, line_of(src, m.start())))

    opens = []
    for m in OPEN_RE.finditer(src):
        for tok in m.group(1).split():
            tok = tok.strip()
            if tok and tok not in ("in",) and not tok.startswith("("):
                opens.append(tok)

    # namespace stack -> prefix at each byte offset
    events = []
    for m in NAMESPACE_RE.finditer(src):
        events.append((m.start(), "ns", m.group(1)))
    for m in END_RE.finditer(src):
        events.append((m.start(), "end", m.group(1)))
    events.sort()

    decls = []
    dmatches = list(DECL_RE.finditer(src))
    for idx, m in enumerate(dmatches):
        kind, name = m.group(1), m.group(2)
        start = m.start()
        end = dmatches[idx + 1].start() if idx + 1 < len(dmatches) else len(src)
        # namespace prefix in effect at `start`
        stack = []
        for pos, typ, val in events:
            if pos >= start:
                break
            if typ == "ns":
                stack.append(val)
            elif typ == "end":
                if stack and (val == stack[-1] or val == ""):
                    stack.pop()
                elif val and stack and stack[-1].endswith(val):
                    stack.pop()
        prefix = ".".join(stack)
        if not name or name in KINDS:
            name = f"_anonymous_{kind}_L{line_of(src, start)}"
        fq = f"{prefix}.{name}" if prefix else name
        body = src[start:end]
        flags = [f for f, rx in FLAG_TOKENS.items() if rx.search(body)]
        decls.append({
            "kind": kind, "name": name, "fq": fq, "prefix": prefix,
            "line": line_of(src, start), "body": body, "flags": flags,
            "opens": list(opens), "binders": binder_names(body),
        })
    file_flags = [f for f, rx in FLAG_TOKENS.items() if rx.search(src)]
    return {"module": module, "rel": rel, "imports": imports,
            "decls": decls, "file_flags": file_flags}

# ---------------------------------------------------------------- driver

def extract_lean(paths, root: Path):
    files = [parse_file(p, root) for p in paths]

    # global symbol tables
    fq_table = {}          # fully qualified name -> node id
    short_table = {}       # short name -> [node id, ...]
    for f in files:
        for d in f["decls"]:
            nid = "lean_decl_" + d["fq"]
            fq_table.setdefault(d["fq"], nid)
            short_table.setdefault(d["name"], []).append(nid)

    nodes, edges = {}, []
    seen_edges = set()

    def add_node(nid, label, sf, loc, ntype, **extra):
        if nid not in nodes:
            nodes[nid] = {"id": nid, "label": label, "source_file": sf,
                          "source_location": loc, "type": ntype, **extra}

    def add_edge(s, t, rel, conf, sf=""):
        if s == t:
            return
        key = (s, t, rel)
        if key in seen_edges:
            return
        seen_edges.add(key)
        edges.append({"source": s, "target": t, "relation": rel,
                      "confidence": conf, "source_file": sf})

    # flag nodes
    for flag in FLAG_TOKENS:
        add_node(f"lean_flag_{flag}", f"⚑ {flag}", "", "", "lean_flag")

    module_ids = {}
    for f in files:
        mid = "lean_module_" + f["module"]
        module_ids[f["module"]] = mid
        add_node(mid, f["module"], f["rel"], "L1", "lean_module")

    for f in files:
        mid = module_ids[f["module"]]
        for tgt, ln in f["imports"]:
            if tgt in module_ids:
                add_edge(mid, module_ids[tgt], "imports", "EXTRACTED", f["rel"])
            else:
                ext = "lean_external_" + tgt.split(".")[0]
                add_node(ext, tgt.split(".")[0], "", "", "lean_external")
                add_edge(mid, ext, "imports", "EXTRACTED", f["rel"])
        for flag in f["file_flags"]:
            add_edge(mid, f"lean_flag_{flag}", "contains", "EXTRACTED", f["rel"])

        for d in f["decls"]:
            nid = "lean_decl_" + d["fq"]
            add_node(nid, d["name"], f["rel"], f"L{d['line']}", f"lean_{d['kind']}",
                     namespace=d["prefix"], fq_name=d["fq"], flags=d["flags"])
            add_edge(mid, nid, "declares", "EXTRACTED", f["rel"])
            for flag in d["flags"]:
                add_edge(nid, f"lean_flag_{flag}", "contains", "EXTRACTED", f["rel"])

            # reference edges
            local = d["binders"]
            for tok in set(IDENT_RE.findall(d["body"])):
                if tok == d["name"] or tok == d["fq"]:
                    continue
                # a bare name that is bound locally is a variable, not a reference
                if "." not in tok and tok in local:
                    continue
                if tok in fq_table:                       # written out in full
                    add_edge(nid, fq_table[tok], "uses", "EXTRACTED", f["rel"])
                    continue
                cands = []
                if "." not in tok:
                    # resolve via enclosing namespace, then via each open
                    scopes = []
                    parts = d["prefix"].split(".") if d["prefix"] else []
                    for k in range(len(parts), 0, -1):
                        scopes.append(".".join(parts[:k]))
                    scopes.extend(d["opens"])
                    for sc in scopes:
                        cand = f"{sc}.{tok}"
                        if cand in fq_table:
                            cands.append(fq_table[cand])
                    if not cands and tok in short_table:
                        cands = list(dict.fromkeys(short_table[tok]))
                        if len(cands) == 1:
                            add_edge(nid, cands[0], "uses", "INFERRED", f["rel"])
                        elif len(cands) > 1:
                            for c in cands[:8]:
                                add_edge(nid, c, "uses", "AMBIGUOUS", f["rel"])
                        continue
                    if len(set(cands)) == 1:
                        add_edge(nid, cands[0], "uses", "INFERRED", f["rel"])
                    elif len(set(cands)) > 1:
                        for c in list(dict.fromkeys(cands))[:8]:
                            add_edge(nid, c, "uses", "AMBIGUOUS", f["rel"])
    return {"nodes": list(nodes.values()), "edges": edges}


if __name__ == "__main__":
    root = Path(sys.argv[1]).resolve()
    out = Path(sys.argv[2])
    excl = sys.argv[3:] or [".lake", ".git"]
    paths = sorted(p for p in root.rglob("*.lean")
                   if not any(e in p.parts for e in excl))
    data = extract_lean(paths, root)
    out.write_text(json.dumps(data, indent=1), encoding="utf-8")
    print(f"files={len(paths)} nodes={len(data['nodes'])} edges={len(data['edges'])}")
