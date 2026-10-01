"""Render every axiom-audited Lean statement of a strand as a LaTeX display.

Symbol-level transliteration only: Unicode maps to the corresponding LaTeX symbol
and identifiers are set upright.  No structure is rewritten, so what the appendix
shows is the statement the prover has, not a paraphrase.
"""
import json, re, pathlib, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from PAPER_leanfmt import wrap, sequent, CAPS

SIGS = json.load(open('/private/tmp/claude-502/-Users-phanan-cig-amf-main/'
                      '53cb7f6c-fbe2-4b96-92c8-1e901e01194d/sigs.json'))

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
    '⁻¹': r'^{-1}', 'ᵀ': r'^{\top}', "'": r"'",
    '{': r'\{', '}': r'\}',
    '₀': r'_{0}', '₁': r'_{1}', '₂': r'_{2}', '₃': r'_{3}', '₄': r'_{4}', '₅': r'_{5}',
    '⁰': r'^{0}', '¹': r'^{1}', '²': r'^{2}', '³': r'^{3}', '…': r'\ldots',
}
KEYWORDS = {'by', 'fun', 'let', 'in', 'if', 'then', 'else', 'match', 'with', 'do'}

def translit(s: str) -> str:
    """Identifiers first (raw text has no backslashes), then Unicode symbols."""
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if c.isascii() and (c.isalpha() or c == '_'):
            j = i
            while j < n and (s[j].isalnum() or s[j] in "_'"):
                j += 1
            w = s[i:j]
            if w in KEYWORDS:
                out.append(r'\mathbf{' + w + '}')
            else:
                out.append(r'\mathit{' + w.replace('_', r'\_') + '}')
            i = j
        else:
            for k in ('ℝ≥0∞', 'ℝ≥0', '∫⁻', '⁻¹'):
                if s.startswith(k, i):
                    out.append(SYM[k] + ' '); i += len(k); break
            else:
                out.append(SYM.get(c, c) + (' ' if c in SYM else ''))
                i += 1
    t = ''.join(out)
    t = t.replace('%', r'\%').replace('#', r'\#').replace('&', r'\&')
    # every ^ and _ must carry a braced argument, else a line break after it breaks TeX
    t = re.sub(r'([\^_])\s*(\\mathit\{(?:[^{}]|\\_)*\}|\\mathbf\{[^{}]*\}|\d+|\\[A-Za-z]+)',
               r'\1{\2}', t)
    # an escaped \_ is a literal underscore in an identifier, not a script marker
    t = re.sub(r'(?<!\\)([\^_])(?!\{)', r'\1{}', t)
    t = re.sub(r'\s+', ' ', t).strip()
    return t

def split_sig(sig: str):
    """Split a Lean signature into (name, [binders], conclusion)."""
    sig = sig.strip()
    m = re.match(r'^(theorem|lemma|def|abbrev)\s+(\S+)\s*(.*)$', sig, re.S)
    if not m:
        return None, [], sig
    rest = m.group(3)
    binders, i, depth, buf = [], 0, 0, ''
    concl = ''
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

STRANDS = {
    'master': ('Master', 'MASTER'), 'query': ('Query', 'Query'),
    'structural': ('Structural', 'Structural'), 'functional': ('Functional', 'Functional'),
    'd6': ('D6', 'D6'), 'support': ('Support', 'Support'),
    'adaptive': ('Adaptive', 'Adaptive'),
    'unified': ('Unified', 'unified-batch'),
}
OUT = pathlib.Path('research/papers/_tex')

for paper, (tag, title) in STRANDS.items():
    mods = {m: v for m, v in SIGS.items() if m.startswith('Lean' + tag)}
    items = [(m, d) for m in sorted(mods) for d in mods[m] if d['kind'] in ('theorem', 'lemma')]
    L = [r'\appendices', r'\section{Complete statement inventory}', r'\label{app:inventory}', '']
    _where = ('displayed beside the step that consumes them'
              if paper == 'unified'
              else r'displayed in Section~\ref{sec:setting}, beside the step that '
                   r'consumes them')
    L.append(
        r'The %s development contributes $%d$ axiom-audited theorems and lemmas across '
        r'its accepted modules. Those that any step of this paper uses are %s. This '
        r'appendix reproduces the \emph{complete} chain---every audited statement, '
        r'grouped by module, including the ones already shown---so that the development '
        r'can be read end to end without reassembling it from the body.'
        % (title, len(items), _where))
    L += ['', r'Each entry is a symbol-level transliteration of the Lean statement: Unicode '
              r'maps to the corresponding \LaTeX{} symbol and identifiers are set upright, '
              r'but no structure is rewritten and no hypothesis is dropped. Binders are '
              r'listed as the prover has them and the turnstile $\vdash$ separates them '
              r'from the conclusion. Every entry carries an acceptance receipt and an axiom '
              r'audit confining it to '
              r'$\{\textsf{propext},\textsf{Classical.choice},\textsf{Quot.sound}\}$; '
              r'none contains \texttt{sorry}.', '']
    cur, n = None, 0
    for m, d in items:
        if m != cur:
            cur = m
            L += [r'\vspace{4pt}\noindent\rule{\columnwidth}{0.4pt}\par\vspace{2pt}',
                  r'\noindent\textbf{Module \lean{%s}}\par\vspace{3pt}'
                  % m.replace('_', r'\_'), '']
        n += 1
        _, binders, concl = split_sig(d['sig'])
        nm = d['name'].replace('_', r'\_')
        L.append(r'\noindent\textbf{A\,%d}\quad\lean{%s}' % (n, nm))
        bl = r',\; '.join(translit(b) for b in binders) if binders else ''
        L += sequent(bl, translit(concl), CAPS.get(d['name']))
        L.append('')
    (OUT / f'{paper}_appendix.tex').write_text('\n'.join(L))
    print(f'{paper:12s} modules={len(mods):3d} statements={len(items):4d}')
