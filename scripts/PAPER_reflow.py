"""Re-flow the Lean statement displays already sitting in the paper bodies.

The appendices are regenerated wholesale from the signature dump, but the body
displays in Section~\\ref{sec:setting} were produced once and pasted in, and the
papers have been edited by hand since.  Regenerating a body would throw that
away, so this rewrites only the displays, in place, leaving every surrounding
line untouched.

Each display is re-emitted from `sigs.json` -- the prover's own signatures --
rather than from the text on the page, so the new layout inherits the corrected
transliteration instead of copying the old one forward.  That is only safe if
the display on the page really is the statement the label names, so it is
checked rather than assumed: the old block is unwrapped back to its token stream
and compared with the transliterated signature.  Nothing is written unless every
block matches.  The one admitted difference is `\\_{}` against `\\_`: the old
transliteration appended an empty group to the literal underscore of an
identifier, which this run corrects.

A statement occupied TWO displays in the old layout, binders then conclusion,
which paid the display skip twice and split a sequent that reads as one thing.
Here the pair becomes one display, and a statement short enough to fit on a
single line gets no `aligned` environment at all.
"""
import re
import sys
import pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from PAPER_leanfmt import sequent, CAPS  # noqa: E402

TEX = pathlib.Path('research/papers/_tex')
PAPERS = ['master', 'query', 'structural', 'functional', 'd6', 'support', 'adaptive']

OPEN = r'{\footnotesize\[ \begin{aligned}[t]'
CLOSE = r'\end{aligned} \]}'


def _prelude():
    """translit/split_sig/SIGS from the promoter, without running its generation."""
    src = pathlib.Path(__file__).resolve().parent / 'PAPER_promote.py'
    text = src.read_text()
    ns = {'__file__': str(src)}
    exec(compile(text[:text.index('MECHANICAL = (')], str(src), 'exec'), ns)
    return ns['translit'], ns['split_sig'], ns['SIGS']


TRANSLIT, SPLIT_SIG, SIGS = _prelude()
BYNAME = {d['name']: d for m in SIGS for d in SIGS[m]}


def unwrap(body_lines):
    """Recover the token stream a display was wrapped from.

    Wrapping only ever inserted a line break, a leading `&` or `&\\quad`, and a
    trailing `\\\\` into a stream joined with single spaces, so stripping those
    and rejoining with single spaces is its exact inverse.
    """
    out = []
    for ln in body_lines:
        s = ln[:-2] if ln.endswith('\\\\') else ln
        s = re.sub(r'^\s*\\vdash\\;&', '', s)
        s = re.sub(r'^\s*&\\quad\s*', '', s)
        s = re.sub(r'^\s*&', '', s)
        out.append(s.strip())
    return ' '.join(x for x in out if x)


SINGLE = re.compile(r'^\{\\footnotesize\\\[ (.*) \\\]\}$')


def blocks(text):
    """Yield (start, end, kind, body_lines) for every statement display.

    Both forms are recognised: the multi-row `aligned` one and the single-line
    one this generator emits when a statement fits.  Missing the second form
    would freeze those statements -- they could never be re-wrapped once written.
    """
    lines = text.split('\n')
    i = 0
    while i < len(lines):
        m1 = SINGLE.match(lines[i].strip())
        if m1 and r'\begin{aligned}' not in lines[i]:
            yield i, i, 'single', [m1.group(1)]
            i += 1
            continue
        if lines[i].strip() == OPEN:
            j, body = i + 1, []
            while j < len(lines) and lines[j].strip() != CLOSE:
                body.append(lines[j])
                j += 1
            if j < len(lines):
                # where the turnstile row sits decides what the display holds:
                # nowhere means binders only (old layout, first of a pair), the
                # first row means a conclusion only (old layout, second of a
                # pair), and anywhere later means a merged sequent (new layout).
                v = next((q for q, b in enumerate(body)
                          if b.lstrip().startswith(r'\vdash\;&')), None)
                kind = 'binders' if v is None else 'concl' if v == 0 else 'merged'
                yield i, j, kind, body
                i = j + 1
                continue
        i += 1


def _label(lines, start):
    """The \\lean{...} declaration name introducing the display at `start`."""
    for back in range(start - 1, max(start - 4, -1), -1):
        m = re.search(r'\\lean\{([^}]*)\}', lines[back])
        if m:
            return m.group(1).replace(r'\_', '_')
    return None


def _norm(s):
    """Compare statements, not spelling.

    Two admitted differences.  The old transliteration wrote an empty group
    after the literal underscore of an identifier, which this run corrects.  And
    space is not significant in math mode -- the layout inserts and removes it
    freely between atoms -- so it cannot be part of the comparison; what keeps
    `\\leq x` from collapsing to the undefined `\\leqx` is PAPER_leanfmt._join,
    not this check.
    """
    return re.sub(r'\s+', '', s.replace(r'\_{}', r'\_'))


def plan(path):
    """(edits, problems) for one paper; edits are (start, end, new_lines)."""
    text = path.read_text()
    lines = text.split('\n')
    found = list(blocks(text))
    edits, problems = [], []
    k = 0
    while k < len(found):
        s1, e1, k1, b1 = found[k]
        nxt = found[k + 1] if k + 1 < len(found) else None
        paired = k1 == 'binders' and nxt and nxt[2] == 'concl' and nxt[0] == e1 + 1
        if paired:
            s2, e2, _, b2 = nxt
            old_b, old_c, last = unwrap(b1), unwrap(b2), e2
            k += 2
        elif k1 == 'merged':
            last = e1
            v = next(q for q, b in enumerate(b1)
                     if b.lstrip().startswith(r'\vdash\;&'))
            old_b, old_c = unwrap(b1[:v]), unwrap(b1[v:])
            k += 1
        elif k1 == 'single':
            last = e1
            raw = b1[0]
            if r'\;\vdash\;' in raw:
                lhs, rhs = raw.split(r'\;\vdash\;', 1)
                old_b, old_c = lhs.strip(), rhs.strip()
            else:
                old_b, old_c = '', re.sub(r'^\\vdash\\;\s*', '', raw).strip()
            k += 1
        else:
            last = e1
            old_b, old_c = (('', unwrap(b1)) if k1 == 'concl' else (unwrap(b1), None))
            k += 1

        name = _label(lines, s1)
        if name is None or name not in BYNAME:
            problems.append((path.name, s1 + 1, f'no signature for label {name!r}'))
            continue
        _, binders, concl = SPLIT_SIG(BYNAME[name]['sig'])
        new_b = r',\; '.join(TRANSLIT(x) for x in binders) if binders else ''
        new_c = TRANSLIT(concl)

        if _norm(old_b or '') != _norm(new_b):
            problems.append((path.name, s1 + 1, f'{name}: binders differ from the signature'))
        if old_c is not None and _norm(old_c) != _norm(new_c):
            problems.append((path.name, s1 + 1, f'{name}: conclusion differs from the signature'))
        if old_c is None:
            # a lone binders display with no conclusion: leave it alone
            continue
        edits.append((s1, last, sequent(new_b, new_c, CAPS.get(name))))
    return edits, problems


def apply(path, edits):
    lines = path.read_text().split('\n')
    out, prev = [], 0
    for s, e, repl in edits:
        out += lines[prev:s] + repl
        prev = e + 1
    out += lines[prev:]
    before = len(lines)
    path.write_text('\n'.join(out))
    return before - len(out)


if __name__ == '__main__':
    write = '--write' in sys.argv
    allplans, allprob, tot_s, tot_e = {}, [], 0, 0
    for p in PAPERS:
        f = TEX / f'{p}.tex'
        edits, probs = plan(f)
        allplans[f] = edits
        allprob += probs
        tot_e += len(edits)
        print(f'{p:12s} statements={len(edits):4d}'
              + (f'  PROBLEMS={len(probs)}' if probs else '  verified'))
    if allprob:
        print(f'\n{len(allprob)} block(s) do not match the prover signature; nothing written.')
        for a in allprob[:20]:
            print('  ', a)
        raise SystemExit(1)
    if not write:
        print('\nall blocks verified against sigs.json; re-run with --write to apply')
        raise SystemExit(0)
    for f, edits in allplans.items():
        tot_s += apply(f, edits)
    print(f'\nrewrote {tot_e} statements; {tot_s} source lines saved')
