"""Re-wrap over-long lines inside promoted/appendix statement displays.

Some statement blocks were emitted before the line breaker gained its
depth-independent hard break, so they carry lines that overflow the column.
This pass finds them in the .tex sources and re-wraps them with the current
rule, leaving every other line untouched.

Prefixes are matched with startswith rather than a regular expression: the
markers are themselves full of backslashes, and an escaping slip in the pattern
fails silently by matching nothing.
"""
import sys
import pathlib

src = pathlib.Path('scripts/PAPER_promote.py').read_text()
ns = {}
exec(src[:src.index('MECHANICAL =')], ns)
wrap = ns['wrap']

HEADS = ['\\vdash\\;&', '&\\quad ', '&']
CONT = '\\\\'          # the two characters a continued aligned line ends with
LIMIT = 56
OPS = '*/+'


def loosen(body, atom=LIMIT):
    """Insert break opportunities inside over-long atoms.

    A densely parenthesised arithmetic expression can contain no spaces at all,
    so the line breaker has nowhere to break and emits it whole. Put a space
    before each top-level arithmetic operator of any atom that is too long,
    counting brace depth so that a macro argument is never split.
    """
    out = []
    for tok in body.split(' '):
        if len(tok) <= atom:
            out.append(tok)
            continue
        buf, depth = [], 0
        for ch in tok:
            if ch == '{':
                depth += 1
            elif ch == '}':
                depth -= 1
            if ch in OPS and depth == 0 and buf:
                buf.append(' ')
            buf.append(ch)
        out.append(''.join(buf))
    return ' '.join(out)


def split_head(line):
    for h in HEADS:
        if line.startswith(h):
            return h, line[len(h):]
    return None, None


def rewrap_file(p, limit=LIMIT):
    lines = p.read_text().split('\n')
    out, changed, inblock = [], 0, False
    for ln in lines:
        if '\\begin{aligned}' in ln:
            inblock = True
            out.append(ln)
            continue
        if '\\end{aligned}' in ln:
            inblock = False
            out.append(ln)
            continue
        head, body = split_head(ln) if inblock else (None, None)
        if head is None:
            out.append(ln)
            continue
        cont = body.endswith(CONT)
        if cont:
            body = body[:-len(CONT)]
        if len(body) <= limit:
            out.append(ln)
            continue
        pieces = wrap(loosen(body))
        if len(pieces) < 2:
            out.append(ln)
            continue
        changed += 1
        for i, pc in enumerate(pieces):
            h = head if i == 0 else '&\\quad '
            tail = CONT if (i < len(pieces) - 1 or cont) else ''
            out.append(h + pc + tail)
    if changed:
        p.write_text('\n'.join(out))
    return changed


if __name__ == '__main__':
    tot = 0
    base = pathlib.Path('research/papers/_tex')
    names = sys.argv[1:] or ['master', 'query', 'structural', 'functional',
                             'd6', 'support', 'adaptive']
    for name in names:
        for p in (base / f'{name}.tex', base / f'{name}_appendix.tex'):
            if p.exists():
                c = rewrap_file(p)
                tot += c
                if c:
                    print(f'{p.name}: rewrapped {c} lines')
    print('total', tot)
