#!/usr/bin/env python3
r"""Every `\lean{...}` in a manuscript must name a declaration that exists.

A manuscript cites Lean declarations as its evidence.  A citation that no longer resolves is
worse than no citation: it reads as a proof that exists.  Renaming a theorem, or dropping
one, silently breaks these, and LaTeX cannot notice.  This is the check that does.

It also reports declarations that no manuscript cites.  That is NOT an error --- most
modules contain supporting lemmas --- but a headline theorem missing from the list is worth
a look.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TEX = ROOT / "research/papers/_tex"
LEAN = ROOT / "work/p13_conjectures"
PAPERS = ("paper_a", "paper_b", "paper_c")

DECL = re.compile(
    r"^(?:noncomputable )?(?:theorem|def|abbrev|instance|lemma) ([^\s(\[{:]+)", re.M)
CITE = re.compile(r"\\lean\{([^}]*)\}")


def main():
    decls, modules = set(), set()
    for f in sorted(LEAN.glob("*.lean")):
        modules.add(f.stem)
        decls |= set(DECL.findall(f.read_text()))
    print(f"{len(decls)} declarations across {len(modules)} modules")

    bad = 0
    cited_all = set()
    for name in PAPERS:
        src = (TEX / f"{name}.tex").read_text()
        cited = {m.replace("\\_", "_") for m in CITE.findall(src)}
        cited_all |= cited
        missing = sorted(c for c in cited
                         if c not in decls and c not in modules)
        status = "ok" if not missing else f"{len(missing)} DANGLING"
        print(f"  {name:8s} {len(cited):4d} citations   {status}")
        for c in missing:
            print(f"      DANGLING: {c}")
        bad += len(missing)

    if bad:
        print(f"\nFAIL: {bad} citation(s) name nothing in the corpus.")
        return 1
    print("\nPASS: every citation resolves.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
