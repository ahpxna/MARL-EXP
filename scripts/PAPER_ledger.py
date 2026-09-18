"""Generate every audit count in the papers from the ledger, instead of typing them.

Four of the seven papers disagreed with their own appendix about how many
statements the strand has, by six to sixteen, with the two numbers a few pages
apart.  For a programme whose selling point is audit discipline that is the
first thing a reader checks, so no number of this kind should be written by
hand again.

Every count here is derived from `sigs.json` -- the signature dump the appendix
is also generated from -- and from `promote_<paper>.json`, which records which
modules the body actually cites.  One definition is used throughout: an audited
STATEMENT is a theorem or a lemma.  The dump also carries two `def`s across the
whole corpus; counting those in one place and not the other is what made the
adaptive paper say 27 where its appendix said 26.

Run with --check to compare, --write to rewrite the papers.
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path('/Users/phanan/cig-amf-main')
TEX = ROOT / 'research/papers/_tex'
SC = pathlib.Path('/private/tmp/claude-502/-Users-phanan-cig-amf-main/'
                  '53cb7f6c-fbe2-4b96-92c8-1e901e01194d')

STRANDS = {'master': 'Master', 'query': 'Query', 'structural': 'Structural',
           'functional': 'Functional', 'd6': 'D6', 'support': 'Support',
           'adaptive': 'Adaptive'}
STATEMENT_KINDS = ('theorem', 'lemma')


def ledger():
    sigs = json.loads((SC / 'sigs.json').read_text())
    out = {}
    tot_mod = tot_stmt = 0
    for paper, tag in STRANDS.items():
        mods = {m: v for m, v in sigs.items() if m.startswith('Lean' + tag)}
        stmts = {m: sum(1 for d in v if d['kind'] in STATEMENT_KINDS)
                 for m, v in mods.items()}
        cited = set(json.loads((SC / f'promote_{paper}.json').read_text()))
        uncited = [m for m in mods if m not in cited]
        out[paper] = dict(
            modules=len(mods),
            statements=sum(stmts.values()),
            cited_modules=len(cited),
            uncited_modules=len(uncited),
            uncited_statements=sum(stmts[m] for m in uncited),
        )
        tot_mod += len(mods)
        tot_stmt += sum(stmts.values())
    out['_programme'] = dict(modules=tot_mod, statements=tot_stmt)
    return out


# Each rule is (regex with one capture group holding the number, key).
# The regexes match the sentence, not just the digits, so a number that happens
# to appear elsewhere is never touched.
RULES = [
    (r'(?s)of which \$(\d+)\$ modules carry an acceptance receipt', 'modules'),
    (r'(?s)acceptance receipt covering \$(\d+)\$ audited\s*\n?\s*declarations', 'statements'),
    (r'(?s)strand contains a further \$(\d+)\$\s*\n?\s*accepted modules', 'uncited_modules'),
    (r'(?s)accepted modules carrying \$(\d+)\$ audited declarations that no', 'uncited_statements'),
    (r'(?s)complete chain: all \$(\d+)\$ audited statements of the strand', 'statements'),
    (r'(?s)audited statements of the strand across its \$(\d+)\$ accepted modules', 'modules'),
    (r'(?s)\$(\d+)\$ modules carry an acceptance\n?\s*receipt', 'modules'),
]
# The programme line must be anchored to its own sentence: an unanchored
# "N audited declarations" also matches every per-strand sentence, which is how
# a first pass rewrote each strand's own count to the programme total.
PROGRAMME = [
    (r'Across the programme: \$[\d,{}]+\$ files, \$[\d,{}]+\$ statements,\s*\n?\s*\$(\d+)\$ accepted modules', 'modules'),
    (r'\$[\d,{}]+\$ accepted modules,\s*\n?\s*\$(\d+)\$ audited\s*\n?\s*declarations\.', 'statements'),
]


def fmt(n):
    return f'{n:,}'.replace(',', '{,}') if n >= 10000 else str(n)


def apply_to(text, want, prog):
    """Rewrite every ledger number; return (text, list of (old, new, key))."""
    changes = []

    def run(rules, src):
        nonlocal text
        for pat, key in rules:
            for m in list(re.finditer(pat, text)):
                old = m.group(1)
                new = fmt(src[key])
                if old != new:
                    changes.append((old, new, key))
                    s, e = m.span(1)
                    text = text[:s] + new + text[e:]
    run(RULES, want)
    run(PROGRAMME, prog)
    return text, changes


def main():
    L = ledger()
    prog = L.pop('_programme')
    write = '--write' in sys.argv
    print(f"{'paper':12}{'mods':>6}{'stmts':>7}{'cited':>7}{'uncited mods':>14}{'uncited stmts':>15}")
    for p, v in L.items():
        print(f"{p:12}{v['modules']:>6}{v['statements']:>7}{v['cited_modules']:>7}"
              f"{v['uncited_modules']:>14}{v['uncited_statements']:>15}")
    print(f"{'PROGRAMME':12}{prog['modules']:>6}{prog['statements']:>7}")
    print()
    total = 0
    for p, v in L.items():
        f = TEX / f'{p}.tex'
        text = f.read_text()
        new, changes = apply_to(text, v, prog)
        total += len(changes)
        if changes:
            print(f'{p}: {len(changes)} number(s) corrected')
            for old, nw, key in changes:
                print(f'    {key:20s} {old} -> {nw}')
        if write and changes:
            f.write_text(new)
    print(f'\n{total} number(s) {"corrected" if write else "would be corrected"}')
    if not write and total:
        print('re-run with --write to apply')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
