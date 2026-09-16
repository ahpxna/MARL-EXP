"""Promote every substantive audited statement into the Methodology subsection that uses it.

Each Methodology subsection cites modules through \leanbox.  This maps every audited
theorem/lemma of those modules to that subsection, renders the substantive ones as
numbered displays with a lead-in, and leaves only mechanical scaffolding (positivity
checks, measurability side conditions) to a counted note.  No trailing appendix.
"""
import json, re, collections, pathlib

SC = ('/private/tmp/claude-502/-Users-phanan-cig-amf-main/'
      '53cb7f6c-fbe2-4b96-92c8-1e901e01194d')
SIGS = json.load(open(f'{SC}/sigs.json'))
OUT = pathlib.Path('research/papers/_tex')

SYM = {
    'ℝ≥0∞': r'\mathbb{R}_{\geq0}^{\infty}', 'ℝ≥0': r'\mathbb{R}_{\geq0}',
    'ℝ': r'\mathbb{R}', 'ℚ': r'\mathbb{Q}', 'ℕ': r'\mathbb{N}', 'ℤ': r'\mathbb{Z}',
    '∫⁻': r'\int^{-}', '∑': r'\textstyle\sum', '∏': r'\textstyle\prod', '∫': r'\int',
    '≤': r'\leq', '≥': r'\geq', '≠': r'\neq', '≈': r'\approx', '≡': r'\equiv',
    '↔': r'\leftrightarrow', '→': r'\to', '⇒': r'\Rightarrow', '↦': r'\mapsto',
    '∀': r'\forall', '∃': r'\exists', '∧': r'\wedge', '∨': r'\vee', '¬': r'\neg',
    '∈': r'\in', '∉': r'\notin', '⊆': r'\subseteq', '⊂': r'\subset',
    '∅': r'\emptyset', '∩': r'\cap', '∪': r'\cup', '∘': r'\circ', '∖': r'\setminus',
    '√': r'\surd', '·': r'\cdot', '±': r'\pm', '∞': r'\infty', '⬝': r'\cdot',
    'α': r'\alpha', 'β': r'\beta', 'γ': r'\gamma', 'δ': r'\delta',
    'ε': r'\varepsilon', 'ζ': r'\zeta', 'η': r'\eta', 'θ': r'\theta',
    'ι': r'\iota', 'κ': r'\kappa', 'λ': r'\lambda', 'μ': r'\mu',
    'ν': r'\nu', 'ξ': r'\xi', 'π': r'\pi', 'ρ': r'\rho',
    'σ': r'\sigma', 'τ': r'\tau', 'φ': r'\varphi', 'χ': r'\chi',
    'ψ': r'\psi', 'ω': r'\omega', 'Γ': r'\Gamma', 'Δ': r'\Delta',
    'Θ': r'\Theta', 'Λ': r'\Lambda', 'Σ': r'\Sigma', 'Φ': r'\Phi',
    'Ω': r'\Omega', 'Π': r'\Pi',
    '⟨': r'\langle', '⟩': r'\rangle', '⌊': r'\lfloor', '⌋': r'\rfloor',
    '⌈': r'\lceil', '⌉': r'\rceil', '‖': r'\Vert', '∣': r'\mid',
    '⁻¹': r'^{-1}', 'ᵀ': r'^{\top}', '{': r'\{', '}': r'\}',
    '₀': r'_{0}', '₁': r'_{1}', '₂': r'_{2}', '₃': r'_{3}', '₄': r'_{4}', '₅': r'_{5}',
    '⁰': r'^{0}', '¹': r'^{1}', '²': r'^{2}', '³': r'^{3}', '…': r'\ldots',
}
KEYWORDS = {'by', 'fun', 'let', 'in', 'if', 'then', 'else', 'match', 'with', 'do'}


def translit(s):
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if c.isascii() and (c.isalpha() or c == '_'):
            j = i
            while j < n and (s[j].isalnum() or s[j] in "_'"):
                j += 1
            w = s[i:j]
            out.append((r'\mathbf{' + w + '}') if w in KEYWORDS
                       else (r'\mathit{' + w.replace('_', r'\_') + '}'))
            i = j
        else:
            for k in ('ℝ≥0∞', 'ℝ≥0', '∫⁻', '⁻¹'):
                if s.startswith(k, i):
                    out.append(SYM[k] + ' '); i += len(k); break
            else:
                out.append(SYM.get(c, c) + (' ' if c in SYM else '')); i += 1
    t = ''.join(out)
    t = t.replace('%', r'\%').replace('#', r'\#').replace('&', r'\&')
    t = re.sub(r'([\^_])\s*(\\mathit\{(?:[^{}]|\\_)*\}|\\mathbf\{[^{}]*\}|\d+|\\[A-Za-z]+)',
               r'\1{\2}', t)
    t = re.sub(r'([\^_])(?!\{)', r'\1{}', t)
    return re.sub(r'\s+', ' ', t).strip()


def split_sig(sig):
    m = re.match(r'^(theorem|lemma|def|abbrev)\s+(\S+)\s*(.*)$', sig.strip(), re.S)
    if not m:
        return None, [], sig
    rest, binders, i, depth, buf, concl = m.group(3), [], 0, 0, '', ''
    while i < len(rest):
        c = rest[i]
        if c in '([{':
            depth += 1; buf += c
        elif c in ')]}':
            depth -= 1; buf += c
            if depth == 0:
                binders.append(buf.strip()); buf = ''
        elif c == ':' and depth == 0:
            concl = rest[i + 1:]; break
        else:
            if depth > 0:
                buf += c
        i += 1
    return m.group(2), binders, concl.strip()


BREAK = [r'\wedge', r'\vee', r'\leftrightarrow', r'\to', r'\leq', r'\geq',
         r'\neq', '=', '<', '>', ',']


def wrap(expr, width=40):
    toks, lines, cur, depth = expr.split(' '), [], '', 0
    for t in toks:
        u = t.replace(r'\{', '').replace(r'\}', '')
        depth += u.count('(') + u.count('[')
        depth -= u.count(')') + u.count(']')
        cand = (cur + ' ' + t).strip()
        if cur.endswith(('^', '_')) or re.search(r'\\[A-Za-z]+$', cur):
            cur = cand; continue
        if len(cand) > width and depth <= 0 and cur and t in BREAK:
            lines.append(cur); cur = t
        elif len(cand) > width * 1.15 and depth <= 0 and cur:
            lines.append(cur); cur = t
        elif len(cand) > width * 1.6 and cur:
            # hard break: a deeply nested expression never returns to depth 0,
            # and an unbroken line overflows the column whatever its nesting
            lines.append(cur); cur = t
        else:
            cur = cand
    if cur:
        lines.append(cur)
    return lines


MECHANICAL = ('measurability', 'positivity')


def classify(sig):
    if re.search(r'\bMeasurable|MeasurableSet|Integrable|AEMeasurable|StronglyMeasurable', sig):
        return 'measurability'
    if re.search(r'(0 <|0 ≤|< 0|≤ 0)', sig) and '∃' not in sig and len(sig) < 240:
        return 'positivity'
    if '∃' in sig:
        return 'construction'
    if re.search(r'≤|<|≥|>', sig):
        return 'bound'
    return 'identity'


def render(d, n):
    _, binders, concl = split_sig(d['sig'])
    nm = d['name'].replace('_', r'\_')
    L = [r'\noindent\textbf{S\,%d}\quad\lean{%s}' % (n, nm)]
    if binders:
        bl = r',\; '.join(translit(b) for b in binders)
        ls = wrap(bl)
        L.append(r'{\footnotesize\[ \begin{aligned}[t]')
        for k, ln in enumerate(ls):
            L.append((r'&' if k == 0 else r'&\quad ') + ln + (r'\\' if k < len(ls) - 1 else ''))
        L.append(r'\end{aligned} \]}')
    cl = wrap(translit(concl))
    L.append(r'{\footnotesize\[ \begin{aligned}[t]')
    for k, ln in enumerate(cl):
        L.append((r'\vdash\;&' if k == 0 else r'&\quad ') + ln + (r'\\' if k < len(cl) - 1 else ''))
    L.append(r'\end{aligned} \]}')
    L.append('')
    return L


STRANDS = {'master': 'Master', 'query': 'Query', 'structural': 'Structural',
           'functional': 'Functional', 'd6': 'D6', 'support': 'Support',
           'adaptive': 'Adaptive'}

for paper, tag in STRANDS.items():
    src = (OUT / f'{paper}.tex').read_text()
    # modules already named in the body, in order of first appearance
    cited = []
    for m in re.finditer(r'\\lean\{(Lean[A-Za-z0-9\\_]+)\}', src):
        nm = m.group(1).replace('\\_', '_')
        if nm not in cited:
            cited.append(nm)
    strand_mods = [m for m in SIGS if m.startswith('Lean' + tag)]
    counter = 0
    blocks = {}
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
        L = []
        for d in subst:
            counter += 1
            L += render(d, counter)
        blocks[mod] = (L, len(subst), mech)
    # modules of the strand never cited in the body
    rest = [m for m in strand_mods if m not in used]
    rest_items = [d for m in rest for d in SIGS[m] if d['kind'] in ('theorem', 'lemma')]
    rest_subst = [d for d in rest_items if classify(d['sig']) not in MECHANICAL]
    rest_mech = len(rest_items) - len(rest_subst)
    out = {'blocks': blocks, 'rest': rest, 'rest_subst': rest_subst,
           'rest_mech': rest_mech, 'counter': counter}
    print(f'{paper:11s} cited modules with content={len(blocks):3d} '
          f'promoted={counter:4d} uncited modules={len(rest):3d} '
          f'their substantive={len(rest_subst):4d} mechanical={rest_mech:4d}')
    json.dump({m: v[1:] for m, v in blocks.items()},
              open(f'{SC}/promote_{paper}.json', 'w'), indent=1)
    (OUT / f'{paper}_promoted.tex').write_text(
        '\n'.join(l for m in blocks for l in blocks[m][0]))
