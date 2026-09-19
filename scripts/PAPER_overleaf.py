"""Bundle each paper into a folder Overleaf can open with no editing.

Overleaf takes a zip and compiles what it finds; it does not have this
repository's layout.  So each bundle is flat and self-contained: the paper as
`main.tex`, every file it `\\input`s, the shared preamble, and only the figures
that paper actually includes.  `\\graphicspath` in the preamble lists both the
repository path and `figures/`, so the same preamble works in both places and
nothing has to be edited on either side.

Which figures a paper needs is read from its `\\includegraphics` calls rather
than guessed, so a bundle never carries the other six papers' images and never
misses one of its own.

Each bundle is compiled here before it is zipped.  A bundle that does not build
is not written: the point of the exercise is that it opens on Overleaf.
"""
import pathlib
import re
import shutil
import subprocess
import sys
import zipfile

ROOT = pathlib.Path('/Users/phanan/cig-amf-main')
TEX = ROOT / 'research/papers/_tex'
FIGS = ROOT / 'research/papers/_figures'
OUT = ROOT / 'research/papers/_overleaf'

PAPERS = {
    'master': 'MASTER_calibration_price',
    'query': 'QUERY_leakage_order',
    'structural': 'STRUCTURAL_menu_law',
    'functional': 'FUNCTIONAL_range_oracle',
    'd6': 'D6_query_width',
    'support': 'SUPPORT_decide_without_identifying',
    'adaptive': 'ADAPTIVE_stopping_tracking',
    # merged drafts, named for the two strands they join
    'd6_functional': 'D6_Functional',
    'support_query': 'Support_Query',
}

INPUT = re.compile(r'\\input\{([^}]+)\}')
GRAPHIC = re.compile(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}')


def inputs_of(name, seen=None):
    """Every .tex the paper pulls in, transitively."""
    seen = seen if seen is not None else set()
    f = TEX / f'{name}.tex'
    if not f.exists() or name in seen:
        return seen
    seen.add(name)
    for dep in INPUT.findall(f.read_text()):
        inputs_of(dep, seen)
    return seen


def figures_of(names):
    out = set()
    for n in names:
        f = TEX / f'{n}.tex'
        if f.exists():
            out |= set(GRAPHIC.findall(f.read_text()))
    return out


def build(paper, folder):
    dest = OUT / folder
    if dest.exists():
        shutil.rmtree(dest)
    (dest / 'figures').mkdir(parents=True)

    deps = inputs_of(paper)
    preamble = (TEX / 'preamble.tex').read_text()
    for n in sorted(deps):
        if n == 'preamble':
            continue          # inlined below, not shipped as a file
        src = TEX / f'{n}.tex'
        if n == paper:
            # Overleaf picks the main document by looking for \documentclass.
            # With the preamble in its own file there are two candidates and it
            # picks the wrong one -- preamble.tex, which has no \end{document},
            # so the build dies with "no legal \end found". Inlining leaves
            # exactly one file carrying \documentclass and removes the choice.
            body = src.read_text().replace('\\input{preamble}', preamble.rstrip(), 1)
            (dest / 'main.tex').write_text(body)
        else:
            shutil.copy2(src, dest / f'{n}.tex')

    missing = []
    for g in sorted(figures_of(deps)):
        src = FIGS / g
        if src.exists():
            shutil.copy2(src, dest / 'figures' / g)
        else:
            missing.append(g)

    (dest / 'README.txt').write_text(
        'Overleaf bundle: ' + folder + '\n\n'
        'Upload this folder as a zip. The main document is main.tex; no paths\n'
        'need editing. Compile with pdfLaTeX.\n\n'
        'Draft notes are the coloured passages: blue is information carried\n'
        'forward, red is a decision or gap that still needs an author. To hide\n'
        'every one of them at once, change \\shownotestrue to \\shownotesfalse\n'
        'near the top of main.tex -- nothing else has to be edited.\n')
    return missing


def one_documentclass(folder):
    """Overleaf's main-document heuristic must have exactly one answer."""
    d = OUT / folder
    carriers = [f.name for f in sorted(d.rglob('*.tex'))
                if '\\documentclass' in f.read_text()]
    return carriers == ['main.tex'], carriers


def compile_ok(folder):
    d = OUT / folder
    r = subprocess.run(['tectonic', '-X', 'compile', 'main.tex', '--keep-logs'],
                       cwd=d, capture_output=True, text=True)
    log = (d / 'main.log')
    warn = 0
    if log.exists():
        t = log.read_text(errors='replace')
        warn = (len(re.findall(r'LaTeX Warning: Reference', t))
                + len(re.findall(r'Citation.*undefined', t)))
    pages = 0
    if (d / 'main.pdf').exists():
        info = subprocess.run(['pdfinfo', str(d / 'main.pdf')],
                              capture_output=True, text=True).stdout
        m = re.search(r'Pages:\s+(\d+)', info)
        pages = int(m.group(1)) if m else 0
    return r.returncode == 0, pages, warn


def main():
    OUT.mkdir(exist_ok=True)
    rows, failed = [], []
    for paper, folder in PAPERS.items():
        missing = build(paper, folder)
        single, carriers = one_documentclass(folder)
        if not single:
            print(f'  {folder}: \\documentclass appears in {carriers}; '
                  'Overleaf would have to guess the main document')
            failed.append(folder)
            rows.append((folder, 0, 0, len(missing), False))
            continue
        ok, pages, warn = compile_ok(folder)
        rows.append((folder, pages, warn, len(missing), ok))
        if missing:
            print(f'  {paper}: {len(missing)} figure(s) not found: {missing[:3]}')
        if not ok:
            failed.append(folder)
            continue
        # strip build products, then zip
        for junk in ('main.log', 'main.aux', 'main.out', 'main.pdf'):
            (OUT / folder / junk).unlink(missing_ok=True)
        z = OUT / f'{folder}.zip'
        with zipfile.ZipFile(z, 'w', zipfile.ZIP_DEFLATED) as zf:
            for f in sorted((OUT / folder).rglob('*')):
                if f.is_file() and f.name != '.DS_Store':
                    zf.write(f, f.relative_to(OUT / folder))

    print(f"\n{'bundle':38}{'pages':>6}{'warn':>6}{'figs missing':>14}")
    for folder, pages, warn, miss, ok in rows:
        print(f"{folder:38}{pages:>6}{warn:>6}{miss:>14}" + ('' if ok else '   BUILD FAILED'))
    if failed:
        print('\nnot zipped, did not build:', failed)
        return 1
    print(f'\nzips in {OUT}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
