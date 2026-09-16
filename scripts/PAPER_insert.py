"""Insert promoted statements into the Methodology subsection that cites their module,
drop the trailing appendix, and replace it with a counted note."""
import json, re, pathlib, sys
sys.path.insert(0, 'scripts')
from PAPER_promote import (SIGS, OUT, classify, render, MECHANICAL, STRANDS)

LEAD = {
 'construction': 'produce the objects the step needs',
 'bound': 'supply the inequalities the step chains',
 'identity': 'supply the rewrites the step performs',
}

for paper, tag in STRANDS.items():
    path = OUT / f'{paper}.tex'
    src = path.read_text()

    cited = []
    for m in re.finditer(r'\\lean\{(Lean[A-Za-z0-9\\_]+)\}', src):
        nm = m.group(1).replace('\\_', '_')
        if nm not in cited:
            cited.append(nm)

    counter = 0
    inserts = []          # (position, text)
    used = set()
    for mod in cited:
        if mod not in SIGS:
            continue
        items = [d for d in SIGS[mod] if d['kind'] in ('theorem', 'lemma')]
        subst = [d for d in items if classify(d['sig']) not in MECHANICAL]
        mech = len(items) - len(subst)
        if not subst:
            continue
        used.add(mod)
        esc = mod.replace('_', r'\\_')
        hits = [m for m in re.finditer(r'\\leanbox\{(?:[^{}]|\{[^{}]*\})*\}', src)
                if esc in m.group(0) or mod in m.group(0)]
        if not hits:
            continue
        pos = hits[-1].end()
        kinds = sorted({classify(d['sig']) for d in subst})
        what = '; '.join(LEAD[k] for k in kinds if k in LEAD)
        body = [
            '', '',
            r'\noindent\emph{Supporting results in \lean{%s}.}~The statements below %s, '
            r'reproduced as the prover has them: Unicode maps to the corresponding \LaTeX{} '
            r'symbol and identifiers are set upright, but no structure is rewritten and no '
            r'hypothesis is dropped. A further $%d$ audited declarations in this module are '
            r'positivity checks and measurability side conditions, which carry no '
            r'mathematical content of their own and are not displayed.'
            % (esc, what or 'support the step', mech),
            '',
        ]
        for d in subst:
            counter += 1
            body += render(d, counter)
        inserts.append((pos, '\n'.join(body)))

    for pos, text in sorted(inserts, reverse=True):
        src = src[:pos] + text + src[pos:]

    # drop the trailing appendix
    src = src.replace(f'\\input{{{paper}_appendix}}\n\n', '')
    src = src.replace(f'\\input{{{paper}_appendix}}\n', '')

    # counted note for the rest of the strand
    strand_mods = [m for m in SIGS if m.startswith('Lean' + tag)]
    rest = [m for m in strand_mods if m not in used]
    rest_items = [d for m in rest for d in SIGS[m] if d['kind'] in ('theorem', 'lemma')]
    note = (
        r'Every audited statement of every module this paper cites is displayed in '
        r'Section~\ref{sec:setting}, attached to the step that uses it; only positivity '
        r'checks and measurability side conditions are omitted, and their count is given '
        r'at each block. The strand contains a further $%d$ accepted modules carrying $%d$ '
        r'audited declarations that no step of this paper uses; they belong to other '
        r'results of the programme and are not reproduced here.'
        % (len(rest), len(rest_items)))
    src = src.replace(r'Appendix~\ref{app:inventory} reproduces every audited statement of the strand.', note)
    src = src.replace(r'Appendix~\ref{app:inventory} reproduces every audited statement.', note)
    src = src.replace(r'Appendix~\ref{app:inventory} reproduces every audited' + '\nstatement.', note)
    src = re.sub(r'Appendix~\\ref\{app:inventory\} reproduces every\s+audited\s+statement\.', note, src)
    src = re.sub(r'Appendix~\\ref\{app:inventory\} reproduces every audited statement of the\s+strand\.', note, src)

    path.write_text(src)
    print(f'{paper:11s} promoted into Methodology: {counter:3d}   '
          f'appendix removed   uncited: {len(rest)} modules / {len(rest_items)} decls')
