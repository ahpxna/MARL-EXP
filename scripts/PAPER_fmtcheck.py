"""Check that laying a statement out never changes what it says.

The layout is only a line-breaking decision, so reading a rendered display back
has to return the statement it was built from.  This asserts exactly that, over
every audited declaration in the corpus rather than over a sample: build the
display, parse it back, and compare with the transliterated signature modulo
whitespace, which carries no meaning in math mode.

It also re-checks the two structural faults that a display must not have -- a
row ending in a backslash, which would run into the `\\\\` row terminator, and
unbalanced braces -- because both have shipped before and neither is visible in
a page of output until it is a page of wrong output.

Run it as a check; it writes nothing.
"""
import re
import sys
import pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from PAPER_leanfmt import sequent, CAPS  # noqa: E402
import PAPER_reflow as R  # noqa: E402

OPEN_LEN = len(r'{\footnotesize\[ ')
CLOSE_LEN = len(r' \]}')
VDASH_ONLY = re.compile(r'^\s*' + re.escape('\\vdash\\;'))


def recover(rows):
    """Read a rendered display back into (binders, conclusion)."""
    if len(rows) == 1:
        body = rows[0][OPEN_LEN:-CLOSE_LEN]
        if r'\;\vdash\;' in body:
            a, b = body.split(r'\;\vdash\;', 1)
            return a, b
        return '', VDASH_ONLY.sub('', body)
    inner = rows[1:-1]
    v = next(q for q, x in enumerate(inner) if x.lstrip().startswith(r'\vdash\;&'))
    return R.unwrap(inner[:v]), R.unwrap(inner[v:])


def faults(rows):
    """Structural faults, over the CONTENT rows only.

    The opening `{\\footnotesize\\[ \\begin{aligned}[t]` and the closing
    `\\end{aligned} \\]}` carry the display's own outer brace, one each, so
    counting them per row reports every well-formed display as unbalanced.
    """
    out = []
    body = rows[1:-1] if len(rows) > 1 else [rows[0][OPEN_LEN:-CLOSE_LEN]]
    for r_ in body:
        c = r_.rstrip()
        if c.endswith('\\\\'):
            c = c[:-2].rstrip()
        if c.endswith('\\') and not c.endswith('\\\\'):
            out.append('row ends in a backslash')
        if c.count('{') - c.count(r'\{') != c.count('}') - c.count(r'\}'):
            out.append('unbalanced braces')
    return out


def main():
    n = lost = broken = 0
    for m in R.SIGS:
        for d in R.SIGS[m]:
            if d['kind'] not in ('theorem', 'lemma'):
                continue
            _, bs, cc = R.SPLIT_SIG(d['sig'])
            b = r',\; '.join(R.TRANSLIT(x) for x in bs) if bs else ''
            c = R.TRANSLIT(cc)
            rows = sequent(b, c, CAPS.get(d['name']))
            n += 1
            f = faults(rows)
            if f:
                broken += 1
                if broken <= 3:
                    print(f'MALFORMED {d["name"]}: {f}')
            gb, gc = recover(rows)
            if R._norm(gb) != R._norm(b) or R._norm(gc) != R._norm(c):
                lost += 1
                if lost <= 3:
                    print(f'CONTENT CHANGED {d["name"]}')
                    print('   got', (R._norm(gb) + ' |- ' + R._norm(gc))[:100])
                    print('   exp', (R._norm(b) + ' |- ' + R._norm(c))[:100])
    print(f'\n{n} audited declarations laid out')
    print(f'  content preserved : {n - lost}/{n}')
    print(f'  well formed       : {n - broken}/{n}')
    return 1 if (lost or broken) else 0


if __name__ == '__main__':
    raise SystemExit(main())
