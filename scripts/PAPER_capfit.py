"""Close the loop on display widths by measuring every row with TeX.

The fitted width model in PAPER_leanfmt gets within about 8pt rms, which is
close enough for almost every statement and not close enough for all of them:
math spacing depends on context in ways a per-symbol sum cannot see, so a
handful of rows come out past the column margin.

Widening the global safety margin until the worst case is covered would cost
every statement a fifth of the column for the sake of a few dozen.  So the
residue is measured instead of predicted.  This sets every generated row in an
\\hbox, reads back \\the\\wd, and for any statement with a row past the margin
records a tighter cap for that statement alone.  Regenerate, re-measure, repeat.

Measuring beats reading the overfull reports out of the log: TeX names the line
of the display's `\\end{aligned}`, not the row that overflowed, and the appendix
is `\\input` so the line number alone does not say which file it belongs to.
The measured widths carry no such ambiguity.

The limits are calibrated rather than assumed.  A row opening with `&` starts at
the alignment point, so it has the full 252pt column; a continuation opening
`&\\quad` starts one em in, at footnotesize 8pt, so it has 244pt.  Both are
carried a few points below that, because a row that exactly reaches the margin
is one rounding away from crossing it.
"""
import json
import re
import subprocess
import sys
import pathlib

ROOT = pathlib.Path('/Users/phanan/cig-amf-main')
TEX = ROOT / 'research/papers/_tex'
CAPFILE = TEX / '.capfit.json'
PAPERS = ['master', 'query', 'structural', 'functional', 'd6', 'support', 'adaptive']
PY = str(ROOT / '.venv/bin/python')

# `aligned` puts `\vdash\;` in the first column, and that column's width is
# added to EVERY row, not only the one carrying the turnstile.  Measured at
# 7.56pt; `\quad` at footnotesize is 8pt.  So a row opening `&` has
# 252 - 7.6 = 244pt and a continuation `&\quad` has 236pt, carried a few points
# below that.  Leaving the turnstile column out is what left a residue of
# overfull boxes exactly 7.1pt wide after the first fit converged.
VDASH = 7.6
LIMIT = {'first': 244.0 - 4, 'cont': 236.0 - 4, 'single': 248.0}
SLACK = 4.0      # pt below the scaled cap, so a retry actually moves
FLOOR = 80.0     # past this the layout is worse than the overflow


def regenerate():
    for script, extra in (('PAPER_appendix.py', []), ('PAPER_reflow.py', ['--write'])):
        r = subprocess.run([PY, str(ROOT / 'scripts' / script)] + extra,
                           cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            print(r.stdout[-3000:], r.stderr[-3000:])
            raise SystemExit(f'{script} failed')


def harvest():
    """Every generated display row: (file, line, statement, kind, content)."""
    rows = []
    for f in sorted(TEX.glob('*.tex')):
        if f.name == 'preamble.tex':
            continue
        name = None
        for i, ln in enumerate(f.read_text().split('\n')):
            m = re.search(r'\\lean\{([^}]*)\}', ln)
            if m:
                name = m.group(1).replace(r'\_', '_')
            s = ln.strip()
            if s.startswith(r'\vdash\;&'):
                kind, c = 'first', s[len(r'\vdash\;&'):]
            elif s.startswith(r'&\quad'):
                kind, c = 'cont', s[len(r'&\quad'):]
            elif s.startswith('&'):
                kind, c = 'first', s[1:]
            elif s.startswith(r'{\footnotesize\[') and r'\begin{aligned}' not in s:
                kind = 'single'
                c = s[len(r'{\footnotesize\['):]
                c = c[:c.rindex(r'\]}')]
            else:
                continue
            c = c.rstrip()
            if c.endswith('\\\\'):
                c = c[:-2]
            c = c.strip()
            # a bare & would be an alignment tab inside the probe's \hbox
            if c and not re.search(r'(?<!\\)&', c):
                rows.append((f.name, i + 1, name, kind, c))
    return rows


def validate(rows):
    """Structural faults a row must not have, checked before TeX sees them.

    A probe that dies takes the whole measurement with it, and a malformed row
    that happens to compile is worse -- it ships.  Both failures seen so far are
    here: a row ending in a backslash runs into the `\\\\` terminator, and
    unbalanced braces swallow whatever follows.
    """
    bad = []
    for f, line, name, kind, c in rows:
        if re.search(r'(?<!\\)\\$', c) or c.endswith('\\ '):
            bad.append((f, line, name, 'row ends in a backslash'))
        if c.count('{') - c.count(r'\{') != c.count('}') - c.count(r'\}'):
            bad.append((f, line, name, 'unbalanced braces'))
    return bad


def measure(rows):
    """True typeset width of each row, in points, from TeX."""
    out = [r'\input{preamble}', r'\begin{document}']
    for i, (_, _, _, _, c) in enumerate(rows):
        out.append(r'\setbox0=\hbox{\footnotesize$' + c + r'$}')
        out.append(r'\typeout{ROW %d w=\the\wd0}' % i)
    out += ['x', r'\end{document}']
    probe = TEX / '_capprobe.tex'
    probe.write_text('\n'.join(out))
    try:
        subprocess.run(['tectonic', '-X', 'compile', probe.name,
                        '--outdir', '/tmp/capprobe', '--keep-logs'],
                       cwd=TEX, capture_output=True, text=True)
        log = pathlib.Path('/tmp/capprobe/_capprobe.log').read_text(errors='replace')
    finally:
        probe.unlink(missing_ok=True)
    return {int(m.group(1)): float(m.group(2))
            for m in re.finditer(r'ROW (\d+) w=([\d.]+)pt', log)}


def main():
    pathlib.Path('/tmp/capprobe').mkdir(exist_ok=True)
    sys.path.insert(0, str(ROOT / 'scripts'))
    caps = json.loads(CAPFILE.read_text()) if CAPFILE.exists() else {}
    for rnd in range(1, 9):
        CAPFILE.write_text(json.dumps(caps, indent=1, sort_keys=True))
        regenerate()
        rows = harvest()
        bad = validate(rows)
        if bad:
            print(f'{len(bad)} malformed row(s); not measuring:')
            for b in bad[:10]:
                print('  ', b)
            raise SystemExit(1)
        w = measure(rows)
        if len(w) != len(rows):
            raise SystemExit(f'measured {len(w)} of {len(rows)} rows; probe failed')

        import importlib
        import PAPER_leanfmt as F
        importlib.reload(F)
        worst = {}
        for i, (_, _, name, kind, _) in enumerate(rows):
            over = w[i] - LIMIT[kind]
            if over > 0 and name:
                prev = worst.get(name, (0.0, 0.0))
                if over > prev[0]:
                    worst[name] = (over, w[i] / LIMIT[kind])
        print(f'round {rnd}: rows={len(rows)}  over the margin={sum(1 for i,(_,_,_,k,_) in enumerate(rows) if w[i] > LIMIT[k])}'
              f'  statements={len(worst)}  worst={max((v[0] for v in worst.values()), default=0):.1f}pt')
        if not worst:
            print(f'\nconverged: {len(caps)} statement(s) carry a tightened cap')
            break
        moved = False
        for name, (over, ratio) in worst.items():
            cur = caps.get(name, F.CAP)
            new = max(FLOOR, min(cur - SLACK, cur / ratio - SLACK))
            if new < cur - 0.5:
                caps[name] = round(new, 1)
                moved = True
        if not moved:
            print('no statement can be narrowed further; stopping')
            break
    CAPFILE.write_text(json.dumps(caps, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
