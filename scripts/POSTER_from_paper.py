"""Pull poster sections out of the papers, rather than paraphrasing them.

The posters were carrying a fraction of what the papers say and leaving a third
of the sheet blank. Every section taken here exists in the paper already: the
opening the literature leaves, the limitations, and the measured results. Taking
the text mechanically keeps the poster and the paper saying the same thing, and
means a later edit to the paper can be pulled through rather than retyped.

The LaTeX is reduced with two tables rather than one pile of regular
expressions: SYMBOL maps a command name to the character it prints, and WRAPPER
names the commands whose braces should be unwrapped. Writing them as command
names avoids the double-escaping that a hand-written pattern list invites -- an
earlier version of this file turned "\\;" into ";" and silently deleted every
semicolon in the extracted text.
"""
import re
import pathlib

TEX = pathlib.Path('research/papers/_tex')

SYMBOL = {
    'times': '\u00d7', 'le': '\u2264', 'leq': '\u2264', 'ge': '\u2265', 'geq': '\u2265',
    'to': '\u2192', 'mapsto': '\u21a6', 'approx': '\u2248', 'sim': '~', 'neq': '\u2260',
    'Delta': '\u0394', 'delta': '\u03b4', 'mu': '\u03bc', 'nu': '\u03bd', 'rho': '\u03c1',
    'sigma': '\u03c3', 'Sigma': '\u03a3', 'varepsilon': '\u03b5', 'epsilon': '\u03b5',
    'eta': '\u03b7', 'kappa': '\u03ba', 'Gamma': '\u0393', 'gamma': '\u03b3',
    'lambda': '\u03bb', 'Lambda': '\u039b', 'Phi': '\u03a6', 'phi': '\u03c6',
    'alpha': '\u03b1', 'beta': '\u03b2', 'theta': '\u03b8', 'Theta': '\u0398',
    'chi': '\u03c7', 'pi': '\u03c0', 'tau': '\u03c4', 'omega': '\u03c9',
    'infty': '\u221e', 'cdot': '\u00b7', 'pm': '\u00b1', 'ldots': '\u2026',
    'dots': '\u2026', 'in': '\u2208', 'notin': '\u2209', 'forall': '\u2200',
    'exists': '\u2203', 'subseteq': '\u2286', 'cup': '\u222a', 'cap': '\u2229',
    'wedge': '\u2227', 'vee': '\u2228', 'complement': 'c', 'setminus': '\\',
    'quad': ' ', 'qquad': '  ', 'ell': '\u2113', 'star': '*', 'circ': '\u00b0',
    'mathbb': '', 'displaystyle': '', 'textstyle': '',
}
WRAPPER = ('emph', 'textbf', 'textit', 'lean', 'mathrm', 'text', 'mathit',
           'mathbf', 'mathbb', 'textsc', 'underline')
DROP_ARG = ('ref', 'cite', 'label', 'leanbox')


def plain(t):
    t = re.sub(r'%.*', '', t)
    for c in WRAPPER:
        for _ in range(3):
            t = re.sub(r'\\' + c + r'\{([^{}]*)\}', r'\1', t)
    for c in DROP_ARG:
        t = re.sub(r'~?\\' + c + r'\{[^}]*\}', '', t)
    t = re.sub(r'\\eqref\{[^}]*\}', 'the equation above', t)
    t = re.sub(r'\\NUM\{\}|\\PROVED\{\}|\\CERT\{\}', '', t)
    t = re.sub(r'\\sqrt\{([^{}]*)\}', '\u221a' + r'\1', t)
    t = re.sub(r'\\t?frac\{([^{}]*)\}\{([^{}]*)\}', r'\1/\2', t)
    for name, ch in sorted(SYMBOL.items(), key=lambda kv: -len(kv[0])):
        # a function replacement, not a template: several of these characters
        # are backslashes and would be read as escapes by re.sub
        t = re.sub(r'\\' + name + r'\b', lambda _m, c=ch: c, t)
    t = t.replace('\\%', '%').replace('\\&', '&').replace('\\_', '_')
    t = re.sub(r'\\[,;!]|\\ ', ' ', t)
    t = re.sub(r'\\begin\{[^}]*\}|\\end\{[^}]*\}', ' ', t)
    t = re.sub(r'\\[a-zA-Z]+', '', t)
    t = re.sub(r'[{}$]', '', t)
    t = t.replace('---', ' \u2014 ').replace('--', '\u2013')
    t = t.replace('``', '\u201c').replace("''", '\u201d')
    return re.sub(r'\s+', ' ', t).strip()


def section(name, start, end=r'\\(?:sub)?section\{'):
    t = (TEX / f'{name}.tex').read_text()
    m = re.search(start, t)
    if not m:
        return None
    rest = t[m.end():]
    e = re.search(end, rest)
    return plain(rest[:e.start()] if e else rest)


def gap(name):
    return section(name, r'\\subsection\{The Gap\}')


def limitations(name):
    return section(name, r'\\subsection\{Shortcomings and Limitations\}')


def questions(name):
    return section(name, r'\\subsection\{Research Questions\}')


def results(name):
    """Every Results subsection of the paper, concatenated."""
    t = (TEX / f'{name}.tex').read_text()
    m = re.search(r'\\section\{Results\}', t)
    if not m:
        return None
    rest = t[m.end():]
    e = re.search(r'\\section\{Discussion\}', rest)
    body = rest[:e.start()] if e else rest
    body = re.sub(r'\\begin\{figure\}.*?\\end\{figure\}', '', body, flags=re.S)
    body = re.sub(r'\\begin\{table\}.*?\\end\{table\}', '', body, flags=re.S)
    return plain(body)
