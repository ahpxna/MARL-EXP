"""Compose two strand papers into one, under a single question.

The two merges this supports were chosen for content, not convenience: D6 and
Functional answer the same question from the two ends -- when a ranking learned
from noisy data certifies optimal compression, and how the evidence has to be
collected -- and Support and Query both ask what it costs to reach a safe
DECISION rather than to identify a world.

A merge is not a concatenation.  Three things have to be handled or the result
is a document that compiles and lies:

Labels collide.  Both papers define `sec:setting`, both number theorems from
one, and `\\ref{thm:reduction}` in merged text would resolve to whichever came
last.  Every label and every reference to it is therefore namespaced by strand,
and the rewrite is applied to the SAME token set on both sides so a reference
can never be left pointing at the other paper's theorem.

Bibliographies overlap.  Entries are merged by key; where both papers define
the same key the first is kept and the second is checked to be identical, and a
differing duplicate is reported rather than silently dropped.

Appendices cannot both open with `\\appendices`.  The second one's opener is
stripped and its inventory becomes a second appendix section.

What this script does not do is write the joining argument.  That is the point
of the merge and it is supplied per pair in `BRIDGE`, as ordinary LaTeX.
"""
import pathlib
import re
import sys

TEX = pathlib.Path('/Users/phanan/cig-amf-main/research/papers/_tex')

# ---------------------------------------------------------------------------
# the sections a paper is cut into, in order
ORDER = ['Introduction', 'Background', 'Research Aims, Questions, and Hypotheses',
         'Methodology', 'Experimental Design', 'Formal Verification', 'Results',
         'Discussion', 'Conclusion']

LABELLED = re.compile(r'\\(label|ref|eqref|autoref|Cref|cref)\{([^}]*)\}')


def namespace(text, tag):
    """Prefix every label and every reference to one, leaving citations alone."""
    def sub(m):
        cmd, key = m.group(1), m.group(2)
        if ':' in key:
            kind, rest = key.split(':', 1)
            return f'\\{cmd}{{{kind}:{tag}-{rest}}}'
        return f'\\{cmd}{{{tag}-{key}}}'
    return LABELLED.sub(sub, text)


def split_sections(body):
    """{section title -> its text}, in document order."""
    out, cur, buf = {}, None, []
    for line in body.split('\n'):
        m = re.match(r'\\section\*?\{(.+?)\}\s*$', line)
        if m:
            if cur is not None:
                out[cur] = '\n'.join(buf)
            cur, buf = m.group(1), []
        else:
            buf.append(line)
    if cur is not None:
        out[cur] = '\n'.join(buf)
    return out


def load(paper, tag):
    raw = (TEX / f'{paper}.tex').read_text()
    # inline the paper's own \input files so the merge is one flat body
    def inline(m):
        f = TEX / f'{m.group(1)}.tex'
        return f.read_text() if f.exists() and m.group(1) != 'preamble' else m.group(0)
    raw = re.sub(r'\\input\{([^}]+)\}', inline, raw)

    abstract = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', raw, re.S).group(1)
    bib = re.search(r'\\begin\{thebibliography\}\{[^}]*\}(.*?)\\end\{thebibliography\}',
                    raw, re.S).group(1)
    body = raw[raw.index(r'\section{Introduction}'):]
    body = body[:body.index(r'\section*{Acknowledgment}')]
    app = raw[raw.index(r'\appendices'):] if r'\appendices' in raw else ''
    if app:
        app = app[:app.index(r'\end{document}')] if r'\end{document}' in app else app
    return dict(abstract=namespace(abstract, tag),
                sections={k: namespace(v, tag) for k, v in split_sections(body).items()},
                bib=bib, appendix=namespace(app, tag), tag=tag)


def merge_bib(a, b):
    """Merge by key; report a key defined differently on the two sides."""
    ent = re.compile(r'\\bibitem\{([^}]+)\}(.*?)(?=\\bibitem\{|\Z)', re.S)
    out, clash = {}, []
    for src in (a, b):
        for m in ent.finditer(src):
            k, v = m.group(1), m.group(2).strip()
            if k in out and re.sub(r'\s+', ' ', out[k]) != re.sub(r'\s+', ' ', v):
                clash.append(k)
            out.setdefault(k, v)
    return out, clash


def compose(spec):
    A, B = load(*spec['left']), load(*spec['right'])
    bib, clash = merge_bib(A['bib'], B['bib'])
    if clash:
        print(f"  !! {spec['out']}: {len(clash)} key(s) differ between the two "
              f"bibliographies: {clash[:5]}")

    L = [r'\input{preamble}', '', r'\begin{document}', '',
         spec['title'], '',
         r'\author{\IEEEauthorblockN{Vu Phan An Nguyen}',
         r'\IEEEauthorblockA{\textit{Rider University} \\',
         r'Lawrenceville, NJ, USA}}', '', r'\maketitle', '',
         r'\begin{abstract}', spec['abstract'], r'\end{abstract}', '',
         r'\begin{IEEEkeywords}', spec['keywords'], r'\end{IEEEkeywords}', '',
         spec['intro'], '']

    # Both original introductions are kept. Dropping them lost content the
    # merge is supposed to preserve, and it also lost the equation labels they
    # define -- eq:order, eq:mixture and eq:capacity are all introduced there
    # and referenced from later sections, so the first merge compiled with
    # dangling references to equations that had silently vanished.
    L += [r'\subsection{Part~I as originally introduced}',
          r'\NOTEPAR{The strand papers'' own introductions are kept in full so nothing '
          r'is lost and so the equations they define remain in scope. The final version '
          r'should fold them into the joint introduction above.}', '',
          A['sections'].get('Introduction', ''), '',
          r'\subsection{Part~II as originally introduced}', '',
          B['sections'].get('Introduction', ''), '']

    # Background and aims from both, each under its own subsection banner
    for name, head in (('Background', r'\section{Background}'),
                       ('Research Aims, Questions, and Hypotheses',
                        r'\section{Research Aims, Questions, and Hypotheses}')):
        L += [head,
              r'\NOTEPAR{The two strands are merged here as written; neither '
              r'section has been rewritten to remove overlap, so the final version '
              r'should fold the shared material together.}', '']
        for P, lab in ((A, spec['left_name']), (B, spec['right_name'])):
            L += [r'\subsection{%s}' % lab, P['sections'].get(name, ''), '']

    # the joining argument, written for this pair
    L += [spec['bridge'], '']

    # the two developments, then everything else pairwise
    L += [r'\section{Part I: %s}' % spec['left_name'], '',
          A['sections'].get('Methodology', ''), '',
          r'\section{Part II: %s}' % spec['right_name'], '',
          B['sections'].get('Methodology', ''), '']

    for name in ('Experimental Design', 'Formal Verification', 'Results',
                 'Discussion', 'Conclusion'):
        L += [r'\section{%s}' % name, '']
        for P, lab in ((A, spec['left_name']), (B, spec['right_name'])):
            s = P['sections'].get(name, '')
            if s.strip():
                L += [r'\subsection{%s}' % lab, s, '']

    L += [r'\section*{Acknowledgment}', '', r'\begin{thebibliography}{00}', '']
    for k, v in bib.items():
        L += [r'\bibitem{%s} %s' % (k, v), '']
    L += [r'\end{thebibliography}', '']

    # one \appendices, two inventories
    L += [r'\appendices']
    for P, lab in ((A, spec['left_name']), (B, spec['right_name'])):
        app = P['appendix'].replace(r'\appendices', '', 1).strip()
        L += [app, '']
    L += [r'\end{document}', '']
    return '\n'.join(L)


# ===========================================================================
# The two merges. Each carries its own joining argument; everything else is
# assembled from the strand papers as written.
# ===========================================================================

D6_FUNCTIONAL = dict(
    out='d6_functional',
    left=('d6', 'd6'), right=('functional', 'fn'),
    left_name='Certified Compression Under a Known Margin',
    right_name='The Geometry of the Alternative, and What a Scalar Proxy Loses',
    title=r"""\title{From Noisy Observations to a Certified Compression:\\
A Sharp Margin Threshold, an Extrema-Aware Alternative,\\
and the Certificate That Joins Them}""",
    keywords=r"""compression, Top-$C$ selection, approximate modularity, margin threshold,
best-arm identification, confidence intervals, alternative geometry, formal verification""",
    abstract=r"""A ranking estimated from noisy data is used to compress: keep the top $C$ items and
discard the rest. Two questions have to be answered together and are usually answered apart.
How large a margin must the true ranking have before Top-$C$ is the optimal compression at
all, and how much data must be collected before that margin can be \emph{certified} from
observations? This paper puts the two halves on one page and states the rule that joins them.
The first half is deterministic. Under a product reference, an exchange bound gives
$2[L_{F}(T)-L_{F}(S)]\le|T\setminus S|\,(2\delta_{I}-\rho)$, where $\rho$ is the margin and
$\delta_{I}$ bounds the mixed difference, so the compression regret of Top-$C$ is at most
$\tfrac12\min(k,m-k)\,[2\delta_{I}-\rho]_{+}$; the threshold $2\delta_{I}$ is shown sharp by
construction, within the reference class and parameter range the theorem names. The second
half is statistical, and its content is negative: when the extrema of the alternative move,
the two-scalar proxy for the sampling problem is wrong in \emph{both} directions, by more
than a factor of two on $12.3\%$ of six thousand random instances and by up to a factor of
$41.7$, and every instance on which it overstates has a moving extremum. The joining rule is
short. Given simultaneous confidence intervals $[L_{i}(t),U_{i}(t)]$ for the capacities and a
valid bound $\overline{\delta}_{I}$, write
$\underline{\rho}_{t}=\min_{i\in T}L_{i}(t)-\max_{j\notin T}U_{j}(t)$; then
$\underline{\rho}_{t}\ge2\overline{\delta}_{I}$ certifies that Top-$C$ is optimal, on the
confidence event. Every displayed theorem of the two halves is machine-checked in Lean~4 with
no \texttt{sorry}. What is \emph{not} claimed is a stopping-time result: no experiment here
runs the whole chain from noise through certificate to realised compression loss, and the
sample complexity of the certificate is not the sample complexity of correct compression.""",
    intro=r"""\section{Introduction}

Compression by ranking is the same operation in a dozen settings: estimate a score for each
item, sort, keep the top $C$. Whether that is the \emph{right} compression is a question
about the true scores, and whether one is entitled to believe it is a question about the data.
The two are routinely answered in different papers, with the consequence that a practitioner
has a threshold with no way to check it, or a stopping rule with no statement of what it
certifies.

This paper is organised around one question that needs both.

\begin{quote}
\emph{When does a ranking learned from noisy observations suffice to certify an optimal
compression, and how must the evidence be collected?}
\end{quote}

The chain has four links, and this paper supplies the first, the second, and the rule that
closes the gap between them:
\[
\begin{aligned}
\text{noisy observation}
&\;\longrightarrow\;\text{capacity confidence intervals}\\
&\;\longrightarrow\;\text{certified margin}\\
&\;\longrightarrow\;\text{compression regret}.
\end{aligned}
\]

\emph{The deterministic end.} Part~I fixes the compression side. Under a product reference the
loss difference between Top-$C$ and any competing set of the same size obeys an exchange
bound in the margin $\rho$ and the mixed-difference modulus $\delta_{I}$, and the regret
vanishes exactly when $\rho\ge2\delta_{I}$. The threshold is not an artifact of the bound:
a construction attains it.

\emph{The statistical end.} Part~II fixes the sampling side, and its main content is a
negative result that changes how the problem must be posed. The natural reduction---summarise
the alternative by two scalars, the current extrema---is not a bound in either direction. It
fails optimistically on $9.0\%$ of instances and conservatively on $3.3\%$, and the cause is
exact rather than statistical: on every instance where it overstates, the cheapest
capacity-inverting alternative moves an extremum.

\emph{The joining rule.} Part~III is short and is the reason the two belong together. The
margin is not observed; what is observed is an interval per capacity. Replacing $\rho$ by the
worst case consistent with the intervals turns the deterministic threshold into something
checkable from data, and the resulting rule certifies optimality on the confidence event.

The scope is bounded, and two of the bounds are worth stating in the introduction because
they are easy to overstate. The boundary at which the \emph{certificate} fails is not the
boundary at which the compression is actually wrong, so the sample complexity of certifying
must not be reported as the sample complexity of compressing correctly. And Part~II's
response tables range over a class that may be wider than the tables a genuine $F$ can
generate, so a lower bound proved over that class needs a realizability argument before it
transfers; this paper does not supply one.

\NOTEPAR{This document merges the D6 and Functional strands under one question, as a draft.
Nothing from either paper has been deleted. Sections that both papers carried appear twice,
one under each strand's name, and the final version should fold them together. Labels are
namespaced \textsf{d6-} and \textsf{fn-} so cross-references cannot silently resolve to the
other strand's theorem of the same name.}""",
    bridge=r"""\section{Part III: The Certificate That Joins the Two Halves}
\label{sec:bridge}

Part~I is a statement about the true capacities and Part~II is a statement about what
sampling can learn. Neither is usable alone: the threshold $\rho\ge2\delta_{I}$ refers to a
margin nobody observes, and a sampling rule with no compression statement attached certifies
nothing about the object of interest. This section writes the rule that connects them. It is
elementary, which is the point---the work is in the two halves, and the join should be the
part a reader can check in a paragraph.

\subsection{The Observable Margin}

Fix the Top-$C$ set $T$ under the estimated ranking at time $t$. Suppose the sampling
procedure supplies \emph{simultaneous} confidence intervals for the capacities,
\begin{equation}
\mathbb{P}\Bigl(\forall i:\;c_{i}\in[L_{i}(t),U_{i}(t)]\Bigr)\;\ge\;1-\alpha ,
\label{eq:bridge-ci}
\end{equation}
and write $E_{t}$ for that event. On $E_{t}$ the true margin is bounded below by its worst
case consistent with the intervals,
\begin{equation}
\underline{\rho}_{t}\;=\;\min_{i\in T}L_{i}(t)\;-\;\max_{j\notin T}U_{j}(t)
\;\le\;\rho .
\label{eq:bridge-rho}
\end{equation}
The inequality is immediate: on $E_{t}$ every $i\in T$ has $c_{i}\ge L_{i}(t)$ and every
$j\notin T$ has $c_{j}\le U_{j}(t)$, so the smallest in-set capacity exceeds the largest
out-of-set capacity by at least the difference of the two bounds.

\subsection{The Certificate}

\begin{proposition}[Certified compression]
\label{prop:certificate}
Let $\overline{\delta}_{I}$ satisfy $\delta_{I}\le\overline{\delta}_{I}$. On the event
$E_{t}$ of \eqref{eq:bridge-ci}, if
\begin{equation}
\underline{\rho}_{t}\;\ge\;2\,\overline{\delta}_{I}
\label{eq:bridge-rule}
\end{equation}
then $T$ is an optimal compression: $L_{F}(T)\le L_{F}(S)$ for every $S$ with $|S|=|T|$.
\end{proposition}

\begin{proof}
On $E_{t}$, \eqref{eq:bridge-rho} gives $\rho\ge\underline{\rho}_{t}$, and the hypothesis on
$\overline{\delta}_{I}$ gives $2\delta_{I}\le2\overline{\delta}_{I}$. Chaining with
\eqref{eq:bridge-rule} yields $2\delta_{I}-\rho\le0$, so $[2\delta_{I}-\rho]_{+}=0$ and the
regret bound of Part~I is zero.
\end{proof}

Three remarks, each of which is a limitation rather than a flourish.

\emph{The certificate is one-sided.} Proposition~\ref{prop:certificate} says when Top-$C$ is
\emph{certainly} optimal. Its failure says nothing: $\underline{\rho}_{t}<2\overline
{\delta}_{I}$ is compatible with $T$ being optimal and the intervals merely being wide. The
boundary at which the certificate fires is therefore \emph{not} the boundary at which the
compression becomes wrong, and the sample complexity of reaching \eqref{eq:bridge-rule} is an
upper bound on the complexity of certifying, not a characterisation of the complexity of
compressing correctly. Reporting it as the latter is the error this remark exists to prevent.

\emph{The modulus is an input.} $\overline{\delta}_{I}$ is supplied, not estimated here.
Where it comes from---a structural assumption on $F$, or an estimate with its own confidence
statement---changes what \eqref{eq:bridge-ci} has to cover, and a $\overline{\delta}_{I}$
estimated from the same data must enter the simultaneous event.

\emph{The chain is not run end to end.} No experiment in this paper starts from noisy
observations, applies a sampling rule, fires \eqref{eq:bridge-rule}, and measures the realised
compression loss. Part~II's experiments concern the geometry of the alternative and the
failure of the scalar proxy; Part~I's concern the threshold. The rule above is the statement
that would let such an experiment be designed, and designing it is the natural next step.

\TODOPAR{What would make Part~III a result rather than a bridge: an expected-stopping theorem
for a sampling rule that drives $\underline{\rho}_{t}$ above $2\overline{\delta}_{I}$, with a
rate. That is the theorem this merge is aimed at and it is not proved here. Note also that
Part~II's allocator comparison is between $\mathrm{C\_lucb}$ and uniform---neither of them
built on the oracle of Part~II---so it is a comparator study and must not be read as evidence
for a new allocator.}""",
)

SUPPORT_QUERY = dict(
    out='support_query',
    left=('support', 'sp'), right=('query', 'qy'),
    left_name='Deciding Without Identifying: An Exact Minimax Law',
    right_name='The Admissible Query Sets the Leakage Order',
    title=r"""\title{The Cost of a Safe Decision Is Not the Cost of\\
Knowing the World: An Exact Minimax Law and\\
a Query-Dependent Leakage Order}""",
    keywords=r"""decision theory, minimax risk, one-sided revelation, finite mixtures, leakage order,
Hellinger distance, sample complexity, formal verification""",
    abstract=r"""Two costs are routinely conflated: what it takes to \emph{identify} which world one is in,
and what it takes to \emph{decide} safely without ever knowing. This paper treats them as
separate quantities and computes each exactly in its own model. On the decision side, a
one-sided revelation model in which only unsafe items are ever revealed admits a closed form:
the minimax decision risk is $R_{\mathrm{dec}}=\tfrac12(1-P)^{N}$, independent of the number
of items $K$, attained by the decoder that names any unexplored item, while the cost of
\emph{recovering} the full configuration grows with $K$. On the query side, the exponent that
governs how fast two fixed worlds separate is a property not of the worlds but of the
\emph{measurement one is allowed to take}: the first non-vanishing coefficient order $r$ of
the perturbed mixture changes when the admissible query changes, and a two-sided Hellinger
sandwich with explicit constants pins the exponent at $2r$ rather than bounding it above.
Together these say the two costs are different objects, and the separation is the point:
deciding can be $K$-free where identifying is not. Every displayed theorem is machine-checked
in Lean~4 with no \texttt{sorry}. What is not established is a common model carrying both
laws at once, and therefore not an exponent separation proved inside one world-and-query
model; that is named here as the next result rather than claimed as this one.""",
    intro=r"""\section{Introduction}

A decision procedure that must name a safe item does not, in general, have to learn which
world it is in. That observation is old and is not what this paper contributes. What this
paper contributes is two exact laws, one on each side of the distinction, and the beginning
of a statement about how far apart they can be.

The first law is about deciding. In a one-sided revelation model---probing an item reveals it
only when it is unsafe---the minimax risk over all decision rules has a closed form, and the
form does not involve the number of items. The natural decoder, which names any item it has
not yet ruled out, attains it. Recovering the configuration, by contrast, costs more as the
configuration grows.

The second law is about querying. Fix two worlds and ask how fast they separate as a
perturbation is turned on. The answer is governed by the first order at which the mixture
coefficients fail to cancel, and that order moves when the admissible measurement moves. The
same pair of worlds, probed differently, gives a different exponent---so the exponent is a
property of the query, and a two-sided sandwich fixes it rather than bounding it.

Read together, the two say that the cost of a safe decision and the cost of knowing the world
are different quantities with different structure. The natural target, which this paper does
not reach, is a single model carrying both, in which the two costs are shown to differ in
their exponent rather than in their constants.

Prior art is close on the framing and not on the laws, and the distinction matters. The idea
of acquiring data to decide rather than to identify is Javdani et al.'s; the idea that the
alternative set determines the sampling problem is standard in pure exploration, and Degenne
and Koolen treat multiple correct answers directly. What is offered here is not the framing
but the two exact laws and the fact that their structure differs.

\NOTEPAR{This document merges the Support and Query strands under one question, as a draft.
Nothing from either paper has been deleted; sections that both carried appear twice, one under
each strand's name. Labels are namespaced \textsf{sp-} and \textsf{qy-}.}""",
    bridge=r"""\section{Part III: What Would Make This One Theorem}
\label{sec:sq-bridge}

The two laws live in two models. Part~I's is a finite one-sided revelation model with a
symmetric prior; Part~II's is a Gaussian location mixture probed through an admissible query.
Nothing below is proved across both, and the honest statement of the merge is that the two
results are adjacent rather than joined.

What adjacency buys is a well-posed target. Write $\mathcal{C}_{\mathrm{dec}}(\varepsilon)$
for the number of queries needed to name a safe item with error $\varepsilon$, and
$\mathcal{C}_{\mathrm{id}}(\varepsilon)$ for the number needed to identify the world. Part~I
exhibits a model in which the first is free of $K$ and the second is not, which is a
separation in the \emph{parameter}. Part~II exhibits a mechanism by which a complexity
exponent can change without the worlds changing at all---only the admissible query changes.
The result these two suggest, and which neither proves, is a separation in the
\emph{exponent}:

\begin{quote}
\emph{a single world-and-query model in which
$\mathcal{C}_{\mathrm{dec}}(\varepsilon)=\Theta(\varepsilon^{-a})$ and
$\mathcal{C}_{\mathrm{id}}(\varepsilon)=\Theta(\varepsilon^{-b})$ with $a<b$.}
\end{quote}

Part~II supplies the natural mechanism for such a gap. If the leakage order relevant to a
\emph{decision} is smaller than the order relevant to \emph{identification}---because
deciding needs only to separate a coarser partition of the worlds, and coarser partitions can
leak at lower order---then the sandwich of Part~II converts that difference of orders into a
difference of exponents directly. Establishing it requires defining both costs in one model
and computing the two orders there.

\TODOPAR{This is the next result, not this one. Two things are needed and neither is here: a
common model in which both costs are defined, and a proof that the decision-relevant leakage
order is strictly smaller than the identification-relevant one on some family. Until then the
merge should be read as two exact laws placed side by side, with a conjecture stated between
them. Do not let the abstract or the title imply the separation is proved.}""",
)


def main():
    import subprocess
    specs = [D6_FUNCTIONAL, SUPPORT_QUERY]
    if len(sys.argv) > 1:
        specs = [s for s in specs if s['out'] in sys.argv[1:]]
    for spec in specs:
        text = compose(spec)
        f = TEX / f"{spec['out']}.tex"
        f.write_text(text)
        print(f"{spec['out']:18s} {len(text.splitlines()):5d} lines written")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
