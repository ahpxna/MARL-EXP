"""Lay out a transliterated Lean statement so one statement is one display.

The appendices were breaking every statement into a stack of six to twelve
display lines carrying three or four symbols each.  The cause was that the
wrapper measured `len()` of the LaTeX SOURCE: an identifier reaches it as
`\\mathit{sm}` (eleven characters) and renders as two, and `\\mathbb{R}` is ten
characters that render as one.  A source budget of 34 characters is therefore a
rendered budget of about four, so nearly every token started its own line.

Measuring rendered CHARACTERS instead is better but still wrong, because math
spacing is not uniform: a relation carries \\thickmuskip on both sides and a
binary operator \\medmuskip, so `a=b` occupies far more than three characters
while `abc` occupies three.  Across sixty real appendix lines the true cost
ranged from 2.4 to 5.2pt per rendered character -- a factor of two, which is the
difference between a tight column and one 30pt past the margin.

So the width model here is fitted rather than assumed.  Sixty lines drawn from
the generated appendices were set in an \\hbox at footnotesize and measured with
\\the\\wd; a least-squares fit over symbol classes gives the per-unit costs
below, reproducing those measurements to an rms of 7pt and a worst case of 20pt
on a 252pt column.  CAP carries that worst case as its safety margin.

The second change is structural.  A statement used to emit TWO displays, one for
the binders and one for the conclusion, which paid the display skip twice and
separated a sequent that reads as one thing.  Here the binders and the turnstile
share a single display, and a statement that fits on one line gets no `aligned`
environment at all.
"""
import re

# Fitted against \the\wd on 60 real appendix lines at footnotesize; pt per unit.
# Relations and binary operators carry their math spacing, which is why they cost
# three times an identifier character.
W = dict(id=3.89, bb=8.59, script=2.22, rel=12.87, binop=10.73,
         mac=2.32, delim=3.42, punct=6.32, dig=3.03, thin=3.85)

COLUMN = 252.0      # \columnwidth, IEEEtran conference
MARGIN = 20.0       # the fit's worst observed residual
INDENT = 8.0        # the \quad opening a continuation row
CAP = COLUMN - MARGIN - INDENT          # 224pt for a wrapped row
CAP1 = COLUMN - MARGIN                  # 232pt for an unwrapped single line
SOFT = CAP * 0.72                       # prefer a syntactic break past here

REL_M = {'leq', 'geq', 'neq', 'to', 'leftrightarrow', 'wedge', 'vee', 'Rightarrow',
         'mapsto', 'in', 'notin', 'subseteq', 'subset', 'equiv', 'approx',
         'vdash', 'mid'}
BIN_M = {'cdot', 'pm', 'setminus', 'cap', 'cup', 'circ', 'times'}

# TeX is the oracle for the residual cases: PAPER_capfit.py compiles, reads the
# overfull reports, and records a tighter cap here for the statements that still
# do not fit.  The fitted model gets within 8pt rms, which is close enough that
# only a handful of statements ever need an entry.
import json as _json
import pathlib as _pathlib
_CAPFILE = _pathlib.Path('research/papers/_tex/.capfit.json')
try:
    CAPS = {k: float(v) for k, v in _json.loads(_CAPFILE.read_text()).items()}
except Exception:
    CAPS = {}

BREAK = [r'\wedge', r'\vee', r'\leftrightarrow', r'\to', r'\leq', r'\geq',
         r'\neq', '=', '<', '>', ',']


def pwidth(s: str) -> float:
    """Typeset width of a math fragment in points, by the fitted class model."""
    f = dict.fromkeys(W, 0)
    t = s

    def eat(pat, key, count):
        nonlocal t
        def r(m):
            f[key] += count(m)
            return ' '
        t = re.sub(pat, r, t)

    eat(r'\\(?:mathit|mathbf|mathrm|textsf|texttt)\{((?:[^{}]|\\.)*)\}', 'id',
        lambda m: len(m.group(1).replace(r'\_', '_')))
    eat(r'\\mathbb\{([^{}]*)\}', 'bb', lambda m: 1)
    eat(r'[\^_]\{([^{}]*)\}', 'script',
        lambda m: max(1, len(re.sub(r'\\[A-Za-z]+', 'X', m.group(1)))))
    eat(r'\\[,;!]', 'thin', lambda m: 1)
    eat(r'\\textstyle', 'thin', lambda m: 0)

    def mac(m):
        n = m.group(1)
        f['rel' if n in REL_M else 'binop' if n in BIN_M else 'mac'] += 1
        return ' '
    t = re.sub(r'\\([A-Za-z]+)', mac, t)

    for c in t:
        if c in '*+-/':
            f['binop'] += 1
        elif c in '=<>':
            f['rel'] += 1
        elif c in '()[]|':
            f['delim'] += 1
        elif c in ',.:;':
            f['punct'] += 1
        elif c.isdigit():
            f['dig'] += 1
        elif c.isalpha():
            f['id'] += 1
        elif c in '{}\\ ':
            pass
        else:
            f['mac'] += 1
    return sum(W[k] * f[k] for k in W)


# An atom is the smallest unit a line break may not fall inside: a control
# sequence with its braced argument, a script (which binds to the atom before
# it), a run of digits, or a single character.  Splitting on spaces, as the old
# wrapper did, could not break `(1-\mathit{c}*\mathit{z})*(\mathit{m}^{2}+2*
# \mathit{m}+5)*\mathit{K}` anywhere at all, because it carries no space.
_ATOM = re.compile(r"""
      \\[A-Za-z]+\s*\{(?:[^{}]|\\[{}])*\}
    | \\[A-Za-z]+
    | [\^_]\{(?:[^{}]|\\[{}])*\}
    | [\^_]
    | \\[^A-Za-z]
    | \d+
    | .
""", re.X)


def atoms(expr: str):
    """Units a line break may fall between, each carrying its own trailing space.

    The space matters: a control word must be terminated, so `\\leq` followed by
    a bare letter has to stay `\\leq x` and not become the undefined `\\leqx`.
    """
    out = []
    for m in _ATOM.finditer(expr):
        t = m.group(0)
        if t.isspace():
            if out and not out[-1].endswith(' '):
                out[-1] += ' '
            continue
        if out and t[0] in '^_' and not out[-1].endswith(' '):
            out[-1] += t
        elif out and _SPACER.fullmatch(out[-1]):
            # a spacing control sequence must not end a row: the row terminator
            # `\\` would then read as `\ \\` run together into `\\\`, which is a
            # line break followed by a stray backslash.  Bind it to what follows.
            out[-1] += t
        else:
            out.append(t)
    return out


_BARE_CW = re.compile(r'\\[A-Za-z]+\s*$')
_SPACER = re.compile(r'\\[^A-Za-z]\s*')


def _join(parts):
    """Concatenate atoms, keeping the one space that TeX actually needs.

    A bare control word must be terminated: `\\leq` followed by a letter would
    be read as the undefined name `\\leqx`.  A regex over the joined string
    cannot do this -- it backtracks into `\\mathit` and splits it at `\\mathi t`
    -- so the boundary is decided between atoms, where it is unambiguous.
    """
    out = []
    for t in parts:
        if out and _BARE_CW.search(out[-1]) and t[:1].isalpha():
            out.append(' ')
        out.append(t)
    return ''.join(out).strip()


def wrap(expr: str, cap: float = CAP, soft: float = SOFT):
    """Break an expression into rows the column can hold.

    Greedy with lookback: a row is filled to `cap` at most, but if a preferred
    break -- after a top-level operator, past `soft` -- was passed on the way,
    the row is cut back to it.  That puts the breaks on the syntax where the
    syntax allows one and on the column margin where it does not.
    """
    A = atoms(expr)
    lines, cur, depth, good = [], [], 0, None
    for t in A:
        if cur and pwidth(_join(cur + [t])) > cap:
            k = good if (good is not None and 0 < good < len(cur)) else len(cur)
            lines.append(_join(cur[:k]))
            cur = cur[k:]
            depth = sum(x.count('(') + x.count('[') - x.count(')') - x.count(']')
                        for x in cur)
            good = None
        cur.append(t)
        u = t.replace(r'\{', '').replace(r'\}', '')
        depth += u.count('(') + u.count('[') - u.count(')') - u.count(']')
        if depth <= 0 and t.strip() in BREAK and pwidth(_join(cur)) >= soft:
            good = len(cur)
    if cur:
        lines.append(_join(cur))
    return [l for l in lines if l]


def sequent(binders_tex: str, concl_tex: str, cap: float = None):
    """One display for one statement: binders, turnstile, conclusion.

    A statement that fits on one line is emitted without an `aligned`
    environment, which is both the compact form and the one that does not
    introduce an alignment point nothing uses.
    """
    cap = CAP if cap is None else cap
    joined = (binders_tex + r' \;\vdash\; ' + concl_tex) if binders_tex else \
             (r'\vdash\; ' + concl_tex)
    if pwidth(joined) <= cap + INDENT:
        return [r'{\footnotesize\[ ' + joined + r' \]}']

    rows = []
    if binders_tex:
        for k, ln in enumerate(wrap(binders_tex, cap, cap * 0.72)):
            rows.append((r'&' if k == 0 else r'&\quad ') + ln)
    for k, ln in enumerate(wrap(concl_tex, cap, cap * 0.72)):
        rows.append((r'\vdash\;&' if k == 0 else r'&\quad ') + ln)

    out = [r'{\footnotesize\[ \begin{aligned}[t]']
    for k, r_ in enumerate(rows):
        if r_.rstrip().endswith('\\') or r_.endswith('\\ '):
            r_ = r_ + '{}'      # keep the terminator from joining a trailing \
        out.append(r_ + (r'\\' if k < len(rows) - 1 else ''))
    out.append(r'\end{aligned} \]}')
    return out
