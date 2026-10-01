#!/usr/bin/env python3
"""Check every artifact's recorded producer hash against the script on disk.

An artifact carries `source_sha256`, the hash of the script that wrote it.  If the script
has changed since, the artifact describes a different computation than the one the repo
now contains, and any number read out of it is unverifiable.  This walks the artifacts,
resolves each to its producer, and reports STALE / CURRENT / NO-HASH.
"""
import ast, hashlib, json, pathlib, re, sys

ART = pathlib.Path("research/unified_20260919")
SCR = pathlib.Path("scripts")

# `EXP_` runs an experiment, `ANALYSE_` reads an existing artifact and derives a second
# one.  Both write artifacts, so both are candidate producers.
CANDIDATES = sorted(SCR.glob("EXP_*.py")) + sorted(SCR.glob("ANALYSE_*.py"))


def written_names(script):
    """The file names a script actually WRITES, as path tails.

    Resolving a producer by searching for the literal path `research/unified_20260919/<stem>`
    misses any script that builds its destination piecewise -- `ROOT / "research" /
    "unified_20260919" / "x.json"` never contains that substring -- and such a script was
    reported as having no producer at all, which silently EXEMPTED its artifact from the
    hash comparison instead of flagging it.  So walk the syntax tree instead: find the
    expressions handed to `open(..., "w")` / `.write_text` / `.write_bytes`, follow them
    back through assignments, and keep the tail of every string constant underneath.  Only
    destinations of writes count, so a script that merely READS an artifact -- as
    `ANALYSE_paperA7_alpha_slope.py` reads `paperA7_learner.json` and `EXP_paperC_general_m.py`
    reads `paperC_exact_dual.json` -- is not attributed that artifact.

    Returns None if the file cannot be parsed, so the caller can fall back.
    """
    try:
        tree = ast.parse(script.read_text())
    except (SyntaxError, ValueError, UnicodeDecodeError):
        return None

    assigns = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for t in node.targets:
                if isinstance(t, ast.Name):
                    assigns.setdefault(t.id, []).append(node.value)

    def write_mode(call):
        """True if this open()-style call opens for writing."""
        mode = None
        if len(call.args) >= 2:
            mode = call.args[1]
        for kw in call.keywords:
            if kw.arg == "mode":
                mode = kw.value
        return (isinstance(mode, ast.Constant) and isinstance(mode.value, str)
                and mode.value[:1] in ("w", "a", "x"))

    targets = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        f = node.func
        if isinstance(f, ast.Name) and f.id == "open" and node.args and write_mode(node):
            targets.append(node.args[0])
        elif isinstance(f, ast.Attribute):
            if f.attr in ("write_text", "write_bytes"):
                targets.append(f.value)
            elif f.attr == "open" and write_mode(node):
                targets.append(f.value)

    tails, seen = set(), set()

    def collect(node, depth=0):
        if depth > 6:
            return
        for sub in ast.walk(node):
            if isinstance(sub, ast.Constant) and isinstance(sub.value, str):
                tails.add(sub.value.split("/")[-1])
            elif isinstance(sub, ast.Name) and sub.id in assigns and sub.id not in seen:
                seen.add(sub.id)
                for v in assigns[sub.id]:
                    collect(v, depth + 1)

    for t in targets:
        collect(t)
    return tails


WRITES = {s: written_names(s) for s in CANDIDATES}

# The producer question is answered from EXP_/ANALYSE_ alone, by convention.  The ORPHAN
# question is not: a stale read from an analysis script is the same bug as one from a
# figure generator, so both maps below cover every script in the directory.
ALL_SCRIPTS = sorted(SCR.glob("*.py"))


def read_names(script):
    """Every artifact-ish file name a script NAMES but does not write, as path tails.

    The same tree walk as the writer side, run over every string constant rather than only
    the ones reachable from a write.  Constants that are docstrings are skipped: this
    file's own prose names artifacts, and prose is not a dependency.  Subtracting the
    script's write destinations leaves what it consumes -- by `load("x.json")`, by
    `json.load(open(...))`, by `pathlib.Path("...").read_text()`, or by naming the file in
    a manifest.  Reads match the WHOLE basename only, never the bare stem, so nothing
    matches a fragment of prose.

    Returns None if the file cannot be parsed, so coverage can be reported honestly.
    """
    try:
        tree = ast.parse(script.read_text())
    except (SyntaxError, ValueError, UnicodeDecodeError):
        return None
    docstrings = {id(n.value) for n in ast.walk(tree)
                  if isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant)
                  and isinstance(n.value.value, str)}
    named = {n.value.split("/")[-1] for n in ast.walk(tree)
             if isinstance(n, ast.Constant) and isinstance(n.value, str)
             and id(n) not in docstrings}
    written = written_names(script) or set()
    return named - written


WRITES_ALL = {s: written_names(s) for s in ALL_SCRIPTS}
READS_ALL = {s: read_names(s) for s in ALL_SCRIPTS}
UNPARSEABLE = [s.name for s in ALL_SCRIPTS if WRITES_ALL[s] is None or READS_ALL[s] is None]


def writers_of(art_name):
    """Every script that writes this artifact, by the whole-last-component rule."""
    stem = art_name[:-len(".json")]
    return [s.name for s in ALL_SCRIPTS
            if WRITES_ALL[s] and (art_name in WRITES_ALL[s] or stem in WRITES_ALL[s])]


def readers_of(art_name):
    """Every script that names this artifact without writing it."""
    return [s.name for s in ALL_SCRIPTS if READS_ALL[s] and art_name in READS_ALL[s]]



def producer_for(art_name):
    """Map an artifact to the script that writes it.

    A script produces `x.json` when it writes a path whose last component is exactly
    `x.json`, or exactly `x` -- the second form covers the destinations assembled as
    `"research/unified_20260919/x" + ("_smoke" if smoke else "") + ".json"`.  The match is
    on the WHOLE last component, never a prefix of it, so `oracle_gap` does not claim
    `oracle_gap_corrected_v2.json` and `paperA_mechanism` does not claim
    `paperA_mechanism_smoke.json`.
    """
    stem = art_name[:-len(".json")]
    hits = [s for s in CANDIDATES
            if WRITES[s] and (art_name in WRITES[s] or stem in WRITES[s])]
    if len(hits) == 1:
        return hits[0]
    if len(hits) > 1:
        # Two scripts claiming one artifact is a repo problem, not something to resolve
        # silently: prefer the one that also names the full literal path, and if that
        # still does not separate them, take the first and let the ambiguity show.
        exact = [s for s in hits
                 if f"research/unified_20260919/{stem}" in s.read_text()]
        return (exact or hits)[0]
    # Fallback for a script the tree walk could not read: the original literal-path rule.
    for s in CANDIDATES:
        if WRITES[s] is None and f"research/unified_20260919/{stem}" in s.read_text():
            return s
    return None


rows, stale, nohash, unknown = [], 0, 0, 0
for a in sorted(ART.glob("*.json")):
    if a.name.endswith("_smoke.json") or a.name.startswith("_"):
        continue
    try:
        d = json.loads(a.read_text())
    except Exception:
        continue
    rec = d.get("source_sha256")
    prod = producer_for(a.name)
    # An artifact whose `_corrected_v2` successor exists and is current is a legacy
    # file, kept per the archive rule but no longer describing a live computation.
    succ = ART / (a.name[:-len(".json")] + "_corrected_v2.json")
    if rec is None:
        # Counted here whatever else it is.  Classifying an unhashed artifact as
        # SUPERSEDED and moving on reported it as neither stale nor missing a hash, so
        # the summary read `0 without a hash` while four artifacts carried none.
        nohash += 1
    if rec is None and succ.exists():
        rows.append({"artifact": a.name, "producer": prod.name if prod else None,
                     "recorded": None, "current": None, "status": "SUPERSEDED"})
        print(f"  {'SUPERSEDED':17s} {a.name:40s} -> {succ.name}")
        continue
    if rec is None:
        status, cur = "NO-HASH", None
    elif prod is None:
        status, cur = "UNKNOWN-PRODUCER", None
        unknown += 1
    else:
        cur = hashlib.sha256(prod.read_bytes()).hexdigest()
        status = "CURRENT" if cur == rec else "STALE"
        if status == "STALE":
            stale += 1
    rows.append({"artifact": a.name, "producer": prod.name if prod else None,
                 "recorded": rec, "current": cur, "status": status})
    print(f"  {status:17s} {a.name:40s} {prod.name if prod else '-'}")

# An artifact that NO script writes but some script reads is an orphan read: the number a
# figure or an analysis puts on the page cannot be regenerated from this repo at all.  That
# is worse than a stale hash -- a stale artifact can at least be rebuilt by running its
# script -- and it is invisible to the producer walk above, because a reader is not a
# producer.  The test is on the writer and reader maps themselves, not on any naming
# convention: a superseded file nobody thought to suffix `_corrected_v2` is caught the same.
orphans = []
for r in rows:
    if writers_of(r["artifact"]):
        continue
    who = readers_of(r["artifact"])
    if who:
        succ = ART / (r["artifact"][:-len(".json")] + "_corrected_v2.json")
        orphans.append({"artifact": r["artifact"], "readers": who,
                        "successor": succ.name if succ.exists() else None})
        r["status"] = r["status"] + "+ORPHAN-READ"
        print(f"  {'ORPHAN-READ':17s} {r['artifact']:40s} read by {', '.join(who)}"
              + (f"  (successor: {succ.name})" if succ.exists() else "  (no successor)"))

sup = sum(1 for r in rows if r["status"].startswith("SUPERSEDED"))
nohash_sup = sum(1 for r in rows if r["status"].startswith("SUPERSEDED")
                 and r["recorded"] is None)
nohash_live = nohash - nohash_sup
print(f"\n  {len(rows)} artifacts: {sum(1 for r in rows if r['status']=='CURRENT')} current,"
      f" {stale} stale, {nohash} without a hash, {sup} superseded,"
      f" {unknown} with no resolvable producer,"
      f" {len(orphans)} read but written by nothing")
print(f"  of the {nohash} without a hash, {nohash_sup} are superseded and {nohash_live}"
      f" are live -- the two counts overlap and neither implies the other")
if UNPARSEABLE:
    print(f"  {len(UNPARSEABLE)} script(s) could not be parsed, so their reads and writes"
          f" are unknown: {', '.join(UNPARSEABLE)}")
out = {"rows": rows, "stale": stale, "no_hash": nohash,
       "no_hash_superseded": nohash_sup, "no_hash_live": nohash_live,
       "unknown": unknown, "superseded": sup,
       "orphan_reads": orphans, "orphan_read_count": len(orphans),
       "unparseable_scripts": UNPARSEABLE,
       # An orphan read flips this.  The flag is read as "is the evidence base sound", and
       # letting it stay true while a published panel reads an unregenerable file is the
       # same failure as the `0 without a hash` line it already had to be fixed for.
       "all_live_current": (stale == 0 and nohash_live == 0 and unknown == 0
                            and not orphans)}
pathlib.Path("research/unified_20260919/_provenance.json").write_text(json.dumps(out, indent=2))
print("  artifact: research/unified_20260919/_provenance.json")
sys.exit(0)
