from pathlib import Path
import hashlib,json
R=Path('/Users/phanan/cig-amf-main'); T=R/'research/papers/_tex'
names=['paper_b.tex','paper_b_supplement.tex','paper_c.tex']
orig={n:(T/n).read_bytes() for n in names}; d={n:s.decode() for n,s in orig.items()}
def rep(n,a,b,count=1):
    assert d[n].count(a)==count,(n,a[:90],d[n].count(a),count)
    d[n]=d[n].replace(a,b)
def before(n,mark,new): rep(n,mark,new+mark)
def sect(n,start,end,new):
    s=d[n]; assert s.count(start)==s.count(end)==1
    i=s.index(start);j=s.index(end,i);d[n]=s[:i]+new+s[j:]
B='paper_b.tex'; S='paper_b_supplement.tex'
sect(B,r'\begin{abstract}',r'\end{abstract}',r'''\begin{abstract}
A noisy compression decision may require less information than identification of the world.
We quantify this gap by combining acceptable-answer geometry with the information supplied
by admissible queries. An obstruction is a set of worlds with no common safe answer.
For finite worlds and queries with positive real observation densities, the smallest
best-pair information over obstructions gives an adaptive lower bound on the number of paid
queries. Its Hellinger counterpart gives a constructive upper bound: likelihood-ratio tests
that share a sample block whenever they use the same query need at most
$|Q|\lceil\log(|W|/\delta)/t_H^*\rceil$ rounds.
The bounds identify the signal exponent when the two informations are comparable and the
world and query sets are fixed. We also show why the query factor cannot in general be
removed, and strengthen the lower bound under a likelihood-ratio second-moment condition.
On a graded channel, the sufficient observation order is the largest, over obstructions, of
their smallest pairwise separation order. This yields matching safe-decision and identification
rates on the same continuous noisy experiment: $\Theta(h^{-2}\log(1/\delta))$ and
$\Theta(h^{-2(m-1)}\log(1/\delta))$ on a parity-mask family with $m$ worlds.
A second latent family gives orders $1$ and $r$: lower bounds hold uniformly over every
finite menu of admissible linear probes, and explicit decision and tail probes attain them.
The lower bounds include randomised adaptive policies with almost-surely finite stopping.
The contribution is the link from a query-induced information hierarchy to the order needed
for a common valid action. Lean~4 proofs accompany the core results; finite-budget decoder
experiments are reported separately from minimax rate claims.
''')
rep(B,r'''finite world set, safe-answer correspondence and channel, the minimax cost is governed by
$t^{*}$, the minimum over obstructions of the largest per-query information among their pairs.''',r'''finite world set, nonempty safe-answer correspondence and channel in the density model
specified below, the obstruction value $t^{*}$ gives a lower bound on minimax cost.
It is the minimum over obstructions of the largest per-query information among their pairs.''')
rep(B,r'''tournament attains $O(|W|^{2}\log(|W|/\delta)/t^{*}_{H})$ on every channel, with $t^{*}_{H}$ the
obstruction value of the Hellinger information (Theorem~\ref{thm:hellupper}). The two match,
up to factors in $|W|$, when the informations are comparable.''',r'''tournament attains $O(\min\{|Q|,|W|^{2}\}\log(|W|/\delta)/t^{*}_{H})$, with $t^{*}_{H}$ the
obstruction value of the Hellinger information (Theorems~\ref{thm:hellupper},
\ref{thm:sharedtests}). The two match in signal and error exponents for fixed $W,Q$ when the
informations are comparable; a private-query construction shows why cardinality factors
cannot simply be suppressed (Proposition~\ref{prop:privatequery}).''')
rep(B,r'''with $s^{*}$ the least safe order. For overlapping safe sets, $s^{*}$ is the minimum
separation order. For identification it is the maximum.''',r'''with $s^{*}$ the least safe order. For the particular overlapping correspondence
$\mathrm{safe}(w)=W\setminus\{w\}$ it is the minimum separation order; arbitrary overlapping
correspondences require the full obstruction formula. For identification it is the maximum.''')
rep(B,'architecture and every supporting declaration. All modules compile with no \\texttt{sorry} and no\n\\texttt{native\\_decide}, and their axioms lie within \\{\\texttt{propext}, \\texttt{Classical.choice},\n\\texttt{Quot.sound}\\}. A policy\'s \\emph{cost} is its expected number of informative, that is\nnon-dummy, queries. A dummy query has the same law in every world. The cost equals\n$\\mathbb{E}\\tau$ for a policy that issues no dummy before it stops, which every decoder here\nsatisfies.',r'''architecture and every supporting declaration. Audited modules use no \texttt{sorry} or
\texttt{native\_decide}, and their printed axioms lie within \{\texttt{propext},
\texttt{Classical.choice}, \texttt{Quot.sound}\}. A policy's \emph{cost} is its expected
number of paid, non-dummy queries. The dummy has the same law in every world; a non-dummy
query need not distinguish every pair. Cost equals $\mathbb{E}\tau$ if no dummy is issued
before stopping. Fixed schedules that also include a dummy block have no greater paid cost
than their displayed horizon.''')
rep(B,r'''Let $W$ be a finite set of worlds, $A$ a finite set of answers and
$\mathrm{safe}:W\to 2^{A}$ the safe answers.''',r'''Let $W$ be a finite nonempty set of worlds, $A$ a finite set of answers and
$\mathrm{safe}:W\to 2^{A}$ the nonempty safe answers at each world.''')
rep(B,'When $\\mathrm{sep}$ is read off a separation predicate on queries, the law is a statement about','The maximum formula assumes that an obstruction exists; otherwise order zero suffices.\nWhen $\\mathrm{sep}$ is read off a separation predicate on queries, the law is a statement about')
rep(B,'$\\mathrm{safe}(w)=A\\setminus\\{w\\}$ with $A=W$, every two safe sets meet, the whole world set is','$\\mathrm{safe}(w)=A\\setminus\\{w\\}$ with $A=W$ and $|W|\\ge3$, every two safe sets meet, the whole world set is')
rep(B,r'''Fix a channel: for each world and query a density, and one dummy query with the same law in
every world. Let $\kappa(w,w')\ge0$ bound the per-query divergence between two worlds.''',r'''Fix finite nonempty sets of worlds and queries. A channel assigns to each $(w,q)$ a
strictly positive measurable density $p_{w,q}$ on $\mathbb R$, with integral one relative
to Lebesgue measure, and a dummy query whose density is independent of $w$.
A randomised adaptive policy chooses its next query by a Markov kernel from the observed
history; outputs and stopping events are measurable. These are the objects implemented by
\lean{Channel} and \lean{Policy} in \lean{LeanPaperBProtocolV1}.
Throughout, ``every channel'' means this density model, not arbitrary singular experiments.
Unless stated otherwise $0<\delta<1/2$. Let $\kappa(w,w')\ge0$ bound the per-query divergence
between two distinct worlds.''')
# Explain the stronger lower law without silently replacing a KL assumption.
before(B,r'\begin{theorem}[The tournament]',r'''\subsection{A sharper lower bound under a second-moment condition}
The factor $1/(|H|-1)$ in the event-pigeonhole proof is not inevitable. It can be removed
from the leading logarithm when a stronger per-query quantity is controlled. This is an
additional assumption, not a consequence of a finite KL bound.

\begin{proposition}[Likelihood-ratio budget on an obstruction]
\label{prop:chistar}
Let $H$ be an obstruction, $w\in H$, $|H|\ge2$, and $t>0$. Suppose every $u\in H\setminus\{w\}$
and non-dummy query satisfy
\begin{equation}
\int\frac{p_{w,q}(y)^2}{p_{u,q}(y)}\,dy
=1+\chi^2(p_{w,q},p_{u,q})\le e^t.
\label{eq:m2budget}
\end{equation}
For any finite-horizon randomised adaptive policy that is $\delta$-correct at every world,
and its random paid count $N$,
\begin{equation}
\Pr_w(Nt\le y)\le\delta+2(|H|-1)\sqrt{\delta e^y}.
\label{eq:chitail}
\end{equation}
In particular, for $0<\gamma<(1-\delta)/2$ and
$y_\gamma=\log(\gamma^2/((|H|-1)^2\delta))\ge0$,
\begin{equation}
t\mathbb E_w N\ge(1-\delta-2\gamma)y_\gamma.
\label{eq:chiexpect}
\end{equation}
\end{proposition}
\begin{proof}
Write $L_u=dP_w/dP_u$ for the transcript likelihood ratio. The common policy kernels
cancel, and~\eqref{eq:m2budget} gives
$\mathbb E_w[L_u e^{-tN}]\le1$ by induction on the history. For an event $S$ unsafe at $u$,
$P_u(S)\le\delta$. Splitting at $L_u=c>0$ gives
\[
P_w(S\cap\{Nt\le y\})\le c\delta+e^y/c.
\]
On $\{Nt\le y\}$, the answer is either unsafe at $w$ or unsafe at another member of $H$.
Union bound over $H\setminus\{w\}$ and set $c=\sqrt{e^y/\delta}$ to
obtain~\eqref{eq:chitail}. Finally $Nt\ge y_\gamma\mathbf1_{\{Nt>y_\gamma\}}$ and
\eqref{eq:chitail} give~\eqref{eq:chiexpect}.
\end{proof}
\leanbox{\lean{hist\_density}, \lean{m2\_eq\_one\_add\_chi}, \lean{lintegral\_Z\_exp\_le},
\lean{one\_alt\_bound}, \lean{chi\_star\_tail}, \lean{chi\_star\_expect},
\lean{chi\_star\_satisfiable} in \lean{LeanPaperBChiStarV1}}
For fixed $H$ the cardinality now enters inside a logarithm. This proposition is stated for
finite horizons, as formalized; the earlier stopped KL law retains its own hypotheses and
constants. A uniform $\chi^2\le a h^{2s}$ implies~\eqref{eq:m2budget} with $t=a h^{2s}$,
since $1+x\le e^x$.

\subsection{Constructive upper bounds and the cost of sharing queries}
''')
before(B,r'\begin{theorem}[The order law]',r'''\begin{theorem}[Sharing observations between pair tests]
\label{thm:sharedtests}
In the setting of Theorem~\ref{thm:hellupper}, let $t>0$ resolve every obstruction under
$\kappa_H$, and let $n=\lceil\log(|W|/\delta)/t\rceil$.
There is a measurable $\delta$-correct tournament with horizon $|Q|n$ and paid cost at most
$|Q|n$: take one block of $n$ observations for each query and let every tested pair use the
block of its best query. Consequently at $t=t_H^*>0$ one can achieve
\[
\min\{|Q|,|W|^2\}\left\lceil\frac{\log(|W|/\delta)}{t_H^*}\right\rceil
\]
by choosing between this schedule and the pair-block schedule.
\end{theorem}
\begin{proof}
Choose the best query once for each unordered pair, so opposite orientations read the same
block. Break likelihood ties by one fixed ordering of worlds. The tests are antisymmetric,
and each has error at most $e^{-n\kappa_H(w,v)}$ on its block, by the proof of
Theorem~\ref{thm:hellupper}. Tests sharing a block are dependent, but no independence between
tests is needed: a union bound over the truth's tests still gives error at most $\delta$.
The survivor argument is unchanged. There are $|Q|$ blocks rather than $|W|^2$.
\end{proof}
\leanbox{\lean{qS\_symm}, \lean{beatS\_anti}, \lean{beatS\_error},
\lean{share\_tournament}, \lean{share\_tournament\_satisfiable} in
\lean{LeanPaperBShareTournamentV1}. The minimum of the two budgets is a direct corollary.}
\NOTEPAR{Release check: this newly added module was not in the completed frozen gates used
by the present audit. Include its source and dependencies in the next frozen verification
before marking this theorem formally released. The mathematical proof is given above.}

\begin{proposition}[The obstruction scalar does not encode the number of queries]
\label{prop:privatequery}
Take worlds $\{0,1,\ldots,k\}$ and queries $\{0,1,\ldots,k\}$, where query zero is dummy.
Query $j\ne0$ has law $\mathcal N(h,1)$ in world $j$ and $\mathcal N(0,1)$ in every other
world. Every distinct pair has best-query KL $h^2/2$ and best-query Hellinger information
$1-e^{-h^2/8}$. Nevertheless every finite-horizon $\delta$-correct identification policy obeys
\[
\mathbb E_0N\,\frac{h^2}{2}\ge
k\bigl((1-\delta)\log(1/\delta)-\log2\bigr).
\]
\end{proposition}
\begin{proof}
Against alternative world $j$, only query $j$ distinguishes the transcript from world zero.
The event ``output zero'' therefore forces
$\mathbb E_0N_j h^2/2\ge(1-\delta)\log(1/\delta)-\log2$. Sum over $j=1,\ldots,k$.
The Gaussian KL and affinity formulas give the stated pairwise informations.
\end{proof}
\leanbox{\lean{klq\_pq}, \lean{private\_query\_lower}, \lean{bc\_pq}, \lean{pq\_resolves},
\lean{private\_query\_satisfiable} in \lean{LeanPaperBPrivateQueryV1}}
The obstruction value identifies the small-signal exponent, but loses the allocation burden
across private queries. Thus the order law is uniform in signal and confidence for fixed
finite sets; it is not a dimension-free characterization of sample complexity. This example
requires a linear cardinality factor, not the quadratic factor of the original pair schedule.

''')
rep(B,r'''over it, and every measurable output.
\begin{enumerate}''',r'''over it, and every measurable output. The lower bounds below apply to every such menu.
The upper bounds apply to menus containing the decision probe $z_1$ for safe decoding,
and both $z_1$ and the averaged tail probe for identification.
\begin{enumerate}''')
rep(B,'So on the finite-horizon class the safe decision costs','For menus containing those probes, on the finite-horizon class the safe decision costs')
rep(B,r'''\item[4)] \textbf{Constants depend on $|W|$, $m$, $r$ and $\sigma$.} The lower constant carries
$\frac{1}{|W|-1}$ and the tournament $|W|^{2}\log|W|$. Nothing is uniform as these grow.
\item[5)] \textbf{Finitely many worlds and queries}, throughout.''',r'''\item[4)] \textbf{Dependence on problem size.} The KL-only lower law carries
$1/(|W|-1)$. Proposition~\ref{prop:chistar} replaces that loss by logarithmic dependence
under a stronger second-moment condition. The shared tournament uses $|Q|\log|W|$;
Proposition~\ref{prop:privatequery} prevents a size-free conclusion. The constants in the
continuous examples also depend on $m$, $r$ and $\sigma$.
\item[5)] \textbf{Channel scope.} Worlds and queries are finite and observations have strictly
positive densities on $\mathbb R$. General singular observation kernels and continuum query
selection are not covered by the protocol theorem used here.''')
sect(B,r'\section{Conclusion}',r'\section*{Companion material}',r'''\section{Conclusion}

Acceptable-answer geometry determines which ambiguities must be removed; the query channel
determines the order at which they can be removed. The obstruction information joins these
two requirements. A transcript lower bound and a constructive Hellinger tournament establish
matching signal exponents when the information quantities are comparable, for fixed finite
world and query sets. Sharing observations avoids paying once per world pair, while private
queries show why the remaining allocation burden is real.
On the parity channel, safe compression and world identification have orders $1$ and $m-1$
in the same experiment. On the latent family they have orders $1$ and $r$ for menus containing
the attaining probes, with lower bounds uniform over all admissible finite linear menus.
The substantive separation is therefore not simply that deciding can be easier than
identifying. It is that the observation hierarchy and the common-answer obstruction jointly
predict different, provably attainable statistical exponents.

''')
# Make newer supplemental proofs readable without changing historical proof records.
before(S,r'\paragraph{The latent family\'s rates', '') if False else None
mark=r'''\paragraph{The latent family's rates (Theorem ``Both rates on the latent family'')}'''
before(S,mark,r'''\paragraph{Shared-query tournament and its limit}
The current upper construction is \lean{share\_tournament} in
\lean{LeanPaperBShareTournamentV1}. Queries are indexed once, with one block of length $n$
per query. Both orientations of a pair choose the same best query (\lean{qS\_symm}),
so the likelihood tests remain antisymmetric even when many pairs reuse observations.
Each individual error bound is still $\mathrm{BC}^n$ (\lean{beatS\_error}); dependence
between tests is harmless for the union bound. The horizon is $|Q|n$, including any dummy
block, hence paid cost is at most that horizon.
This new module needs inclusion in the release's frozen gate. The Gaussian private-query
example in \lean{LeanPaperBPrivateQueryV1} is already a concrete instance: its
\lean{private\_query\_lower} forces a cost proportional to the number of private queries,
while \lean{bc\_pq} and \lean{pq\_resolves} instantiate the tournament's information threshold.
It does not prove the old quadratic factor in the number of worlds necessary.

\paragraph{Second-moment obstruction law}
\lean{LeanPaperBChiStarV1} proves the actual history density ratio (\lean{hist\_density}),
the identity $\int p_w^2/p_u=1+\chi^2(p_w,p_u)$ (\lean{m2\_eq\_one\_add\_chi}), and the
history-recursion bound $\mathbb E_w[L_u e^{-tN}]\le1$ (\lean{lintegral\_Z\_exp\_le}).
The unsafe-output events cover the event of insufficient information. Splitting each event
at likelihood ratio $c$ gives $c\delta+e^y/c$ (\lean{one\_alt\_bound}), and optimising $c$
gives \lean{chi\_star\_tail}. The nonnegative-count inequality on its complement yields
\lean{chi\_star\_expect}. Thus the result is about probabilities and expected counts under
the adaptive observation law, not an arithmetic lemma supplied with a transcript bound.
It assumes the stronger finite second moment uniformly over queries; finite KL alone does
not imply that condition. The released proposition is finite-horizon. The stopped KL
proposition elsewhere retains its separately proved scope.

''')
rep(S,'for every channel given by densities by \\lean{transcript\\_kl\\_le} and','for every channel with strictly positive measurable real densities in protocol form by\n\\lean{transcript\\_kl\\_le} and')
# Correct the new C proof map to the actual declaring module, without changing existing proof files.
rep('paper_c.tex',r'\lean{collapse\_all} in \lean{LeanPaperCOddWitnessJoinV1},',r'\lean{collapse\_all} in \lean{LeanPaperCEndgameV1},')
for n in names: assert (T/n).read_bytes()==orig[n],('Concurrent change',n)
for n in names: (T/n).write_text(d[n])
(R/'research/audit_current_20260925/MANUSCRIPT_EDITS_PHASE2.json').write_text(json.dumps({n:hashlib.sha256(d[n].encode()).hexdigest() for n in names},indent=2)+'\n')
print('Updated B main/supplement and C declaration reference.')
