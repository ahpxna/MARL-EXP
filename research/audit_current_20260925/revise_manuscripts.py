from pathlib import Path
import hashlib, json, shutil
R=Path('/Users/phanan/cig-amf-main')
T=R/'research/papers/_tex'
B=R/'research/papers/legacy/manuscripts_before_review_20260925'
B.mkdir(parents=True,exist_ok=True)
names=[f'paper_{p}{s}.tex' for p in 'abc' for s in ('','_supplement')]
original={n:(T/n).read_bytes() for n in names}
manifest={n:hashlib.sha256(v).hexdigest() for n,v in original.items()}
for n,v in original.items():
    dest=B/n
    if dest.exists():
        assert dest.read_bytes()==v, ('Backup already exists with other content',n)
    else: dest.write_bytes(v)
(B/'SHA256.json').write_text(json.dumps(manifest,indent=2)+'\n')
d={n:v.decode() for n,v in original.items()}
def rep(n,old,new,count=1):
    assert d[n].count(old)==count,(n,old[:100],d[n].count(old),count)
    d[n]=d[n].replace(old,new)
def section(n,start,end,new):
    s=d[n]; assert s.count(start)==s.count(end)==1,(n,start,end)
    i=s.index(start); j=s.index(end,i)
    d[n]=s[:i]+new+s[j:]
def before(n,mark,new):
    rep(n,mark,new+mark)
A='paper_a.tex'; C='paper_c.tex'
section(A,r'\begin{abstract}',r'\end{abstract}',r'''\begin{abstract}
Which observations are worth buying depends on the alternatives to the decision, not only on
the observation model. We study a compression decision whose loss contains moving extrema,
and a surrogate that freezes the extremum cells while dropping their ordering constraints.
Both objectives optimise over the same designs and the same centred parameter class.
For a family with $r$ middle-cell pairs of variance $M$, the surrogate value is $9/512$,
whereas the true value lies between $9/[128(4+2rM)]$ and $1/(8rM)$.
Every surrogate-optimal design assigns zero mass to those pairs and has zero true information;
every $\varepsilon$-optimal design has true information at most $64\varepsilon/(9rM)$.
Thus the failure persists at unit variance as the number of neglected directions grows.
We quantify its repair. Sacrificing a fraction $\beta$ of surrogate value permits true
information between $9\beta/[128(4+2rM)]$ and $\beta/(8rM)$.
A certificate based on the surrogate's dual margins extends this design tradeoff to a budget
law for adaptive policies, including unbounded stopping: at expected cost $N$, the average
design must pay $N\,\mathrm{sac}(\bar w)\ge8rM\log(1/\delta)(1-o(1))$.
An ideal learner attains the true characteristic time, while a specified learner that
re-solves the frozen surrogate at its estimate needs $\Omega(\log^2(1/\delta))$ samples under
square-root forcing. The distinction is an optimised failure of alternative geometry, followed
by a quantitative cost of correcting it. Lean~4 proofs support the stated model and policy
results. Exact rational certificates and paired simulations illustrate the mechanism;
they also show why neither a finite-precision learner nor a favourable finite panel can be
identified with the asymptotically optimal ideal algorithm.
''')
rep(A,'Computing that infimum requires the alternative set. The natural shortcut freezes the cells','Computing that infimum requires the alternative set. The shortcut studied here freezes the cells')
rep(A,r'$\Theta(rM)$ below the frozen one, and the factor is already present at unit variance.',r'$\Theta(rM)$ below the frozen one when $rM\ge1$, with absolute comparison constants; the factor is already present at unit variance.')
rep(A,r'$\beta$ of surrogate value recovers $\Theta(\beta/rM)$ of true information.',r'$\beta$ of surrogate value recovers $\Theta(\beta/rM)$ of true information when $rM\ge1$. The displayed finite-parameter bounds remain valid for every $M>0$.')
rep(A,r'$\Theta(\beta/rM)$ and the sacrifice budget',r'$\Theta(\beta/rM)$ for $rM\ge1$ and the sacrifice budget')
rep(A,'The summand is the per-query Gaussian divergence, so $1/\\Gamma$ is the rate of a\n$\\delta$-correct learner.','The summand is the per-query Gaussian divergence. Thus $1/\\Gamma$ is the candidate\ncharacteristic time; its lower-bound interpretation and attainability require the policy\nresults proved below. This definition alone does not establish an algorithmic rate.')
rep(A,'Each theorem carries one line naming its Lean declaration.', 'Each formal theorem carries a line naming its Lean declaration. Elementary consequences\nassembled here carry an explicit proof and are distinguished from separately formalized wrappers.')
rep(A,'preparation. All modules compile with no \\texttt{sorry} and no \\texttt{native\\_decide}, and\ntheir axioms lie within \\{\\texttt{propext}, \\texttt{Classical.choice}, \\texttt{Quot.sound}\\}.','preparation. The checked proof modules use no \\texttt{sorry} or \\texttt{native\\_decide};\ntheir audited axioms lie within \\{\\texttt{propext}, \\texttt{Classical.choice}, \\texttt{Quot.sound}\\}.')
rep(A,'The lower bound is attained by\n$w_{\\beta}=(1-\\beta)w_{\\rm unif}+\\beta w_{\\rm cert}$.','The design\n$w_{\\beta}=(1-\\beta)w_{\\rm unif}+\\beta w_{\\rm cert}$ achieves at least the displayed lower bound;\nwe do not assert equality with that bound or an exact formula for the repair frontier.')
rep(A,'So the budget is $\\Theta(rM\\log(1/\\delta))$, and the two constants differ by','For $rM\\ge1$, the budget is $\\Theta(rM\\log(1/\\delta))$ with absolute comparison constants.\nFor arbitrary $r,M$ the exact bounds above are the statement; their ratio is')
rep(A,'then query the four $A$ cells round-robin for $4k$ more','then query the four frozen cells (the two $A$ cells and the two $B$ anchors) round-robin for $4k$ more')
rep(A,r'=O(rM\log(1/\delta))$. So for every run length',r'=O((4+2rM)\log(1/\delta))$. So for every run length')
before(A,r'\subsection{For a policy}',r'''\subsection{A certificate that extends beyond this family}
\label{sec:repaircertificate}
The pair construction makes the constants explicit. The inference from a flawed design
criterion to a repair budget uses less structure. Let $J_f,J_t$ be nonnegative concave design
values on a finite simplex, let $\Gamma_f=\max_wJ_f(w)>0$, and write
$s(w)=1-J_f(w)/\Gamma_f$. Suppose a frozen certificate $c$ and true-alternative load vectors
$\ell_j$ satisfy, for every design $w$,
\[
J_f(w)\le\sum_e w_ec_e,\qquad
J_t(w)\le\sum_e w_e\ell_j(e)\quad\text{for every }j.
\]
A distribution over frozen alternatives supplies $c$; each true alternative supplies one
load. These are verifiable information inequalities, not estimates of the two optima.

\begin{proposition}[Certificate for repair cost]
\label{prop:repaircertificate}
Suppose $\nu_j\ge0$, $\Lambda=\sum_j\nu_j>0$, and
\begin{equation}
\sum_j\nu_j\ell_j(e)\le1-\frac{c_e}{\Gamma_f}\quad\text{for every cell }e.
\label{eq:repaircover}
\end{equation}
Then $\Lambda J_t(w)\le s(w)$ for every design. Consequently
$R(b):=\sup_{s(w)\le b}J_t(w)\le b/\Lambda$.
If expected counts $N_e\ge0$ have $N=\sum_eN_e>0$ and meet
$\sum_eN_e\ell_j(e)\ge D$ for every $j$, then
\begin{equation}
N s(N_{\cdot}/N)\ge\Lambda D.
\label{eq:generalrepairbudget}
\end{equation}
Conversely, if $w_*$ attains $\Gamma_f$, and $v$ has $s(v)>0$, then for every $b\ge0$,
\begin{equation}
R(b)\ge\min\{1,b/s(v)\}\,J_t(v).
\label{eq:clippedrepair}
\end{equation}
\end{proposition}
\begin{proof}
Multiply each true-load inequality by $\nu_j$, sum, and use~\eqref{eq:repaircover}:
\[
\Lambda J_t(w)\le\sum_e w_e\sum_j\nu_j\ell_j(e)
\le1-\frac{\sum_e w_ec_e}{\Gamma_f}\le s(w).
\]
The same calculation with $N_e$ in place of $w_e$ proves~\eqref{eq:generalrepairbudget}.
For the converse take $\lambda=\min\{1,b/s(v)\}$ and
$w=(1-\lambda)w_*+\lambda v$. Concavity gives $s(w)\le\lambda s(v)\le b$ and
$J_t(w)\ge\lambda J_t(v)$. Clipping $\lambda$ at one is necessary: extrapolation is not a design.
\end{proof}
\leanbox{\lean{exchange}, \lean{frontier\_upper}, \lean{budget}, \lean{weak\_duality},
\lean{repair\_mix} in \lean{LeanPaperASacrificeDualityV1}. Equation~\eqref{eq:clippedrepair}
is the displayed substitution into \lean{repair\_mix}, not a separately checked wrapper.}

For our family, $c_e=\Gamma_f$ on the four frozen cells and zero on the middles. A strict
alternative moves one middle pair by $1/2+d$, and has load $(1/2+d)^2/(2M)$ on each of its
two cells. Set $\nu_j=8M/(1+2d)^2$. The cover is exact on every middle cell and zero on the
others; hence $\Lambda=8rM/(1+2d)^2$. Taking $d\downarrow0$ recovers both the frontier upper
bound and the policy budget $8rMD$ without replacing strict alternatives by unattained ties.
This is a sufficient certificate and a weak-duality bound, not a claim that every game's
repair frontier has this form or that these bounds are always tight.
\leanbox{\lean{cStar\_cert}, \lean{pairLoad\_cert}, \lean{nuStar\_cover},
\lean{construction\_frontier}, \lean{construction\_budget},
\lean{certificate\_pair\_satisfiable} in \lean{LeanPaperASacrificeDualityV1}}

''')
rep(A,'Every number below is produced by a script that checks itself against a statement proved in\nLean, and refuses to write output if a check fails. Oracle arms read the true world. They are\nlabelled as oracle-allocation diagnostics and are never competitors. Error rates are tested on\nthe right quantity: $\\delta$-correctness bounds $\\Pr(\\text{stop and wrong})$ over launched runs,\nnot the error rate among stopped runs, and censoring is reported separately.',r'''The evidence has three different purposes: exact certificates check finite optimisation
instances, mechanism panels reveal where a rule spends observations, and learner panels measure
finite-budget behaviour. Runtime assertions are useful consistency checks, not independent
proofs of statistical coverage or global optimality. Oracle arms read the true world and are
labelled as oracle-allocation diagnostics. For error accounting the relevant quantity is
$\Pr(\text{stop and wrong})$ over all launched runs; censoring is reported separately.
Zero observed errors on these panels is not a certification of $\delta$-correctness.''')
rep(A,r'certificate is a valid lower bound on the likelihood ratio, not the exact',r'certificate is a lower bound on the likelihood ratio, not the exact')
rep(A,r'and $\alpha=0.05$ lies far above the $\delta_{0}$ of Theorem~\ref{thm:surlearner}. The',r'and no certified value of the asymptotic threshold $\delta_{0}$ is provided. The')
rep(A,r'certificate is a lower bound and $\alpha$ lies far above $\delta_{0}$, so this measures these',r'certificate is a lower bound and the theorem supplies no numerical $\delta_{0}$ for this panel, so this measures these')
# Make the finite-budget conclusions visible outside the figure captions.
before(A,r'\section{Limitations}',r'''\paragraph{What the panels establish}
The locked panel isolates a directional failure, not universal superiority of a new allocator.
On the base world at $(r,M)=(4,4)$, the surrogate rule reaches the $60000$ cap in all 200 runs,
whereas geometry and uniform have restricted means $13682.25$ and $15622$.
At $(1,1)$, geometry and uniform are nearly tied ($1737.5$ and $1732.25$).
On the swapped world the surrogate rule is fastest in all six parameter cells. These reversals
are informative: the cost is tied to which directions the frozen geometry excludes.
The implemented geometry rule uses a numerical ascent of a lower certificate; it is not a
globally certified maximiser of the true game. Likewise, the shipped learner's failure to
resolve its answer-selection tie on the swapped world is an implementation limitation that
the ideal learner theorem does not excuse.

''')
section(A,r'\section{Conclusion}',r'\section*{Companion material}',r'''\section{Conclusion}

The relevant failure is not merely that two design objectives assign different numbers.
On a realizable compression family, every exact and near-optimal frozen design loses the
information needed by the actual decision. A dual-margin certificate turns that geometric
failure into a design tradeoff and then into a policy-level budget. The family makes its
scale explicit: for $rM\ge1$, repair costs $\Theta(rM\log(1/\delta))$ query-units of surrogate
value. With square-root corrective exploration, the specified surrogate learner pays
$\Omega(\log^2(1/\delta))$, while the ideal true-geometry learner attains its characteristic
time. The finite panels support the mechanism and expose implementation weaknesses; they
do not establish the asymptotic rates or universal superiority over uniform allocation.

''')
# C: exact frontiers remain; repair the quantifiers of robustness.
section(C,r'\begin{abstract}',r'\end{abstract}',r'''\begin{abstract}
One random removal order may have to serve every compression budget, while each item must
have nearly uniform probability of removal at every prefix. We determine the price of this
constraint for a signed-weight family, using regret against the best subset at each budget.
For every size and every marginal-band width, we obtain the exact minimax expected regret.
With even size $m$, it is
$\max\{2/[(m+4)(m-1)],\,4(1-\eta)/[m(m+4)]\}$.
With odd size it has two affine pieces before reaching the unconstrained value at $\eta=1$.
Exact uniformity costs less than a factor two in even size but a factor proportional to $m$
in odd size. Explicit distributions attain the bounds simultaneously at all budgets; a
composition-flow formulation preserves both the objective and every item marginal.
The timing of the budget changes the answer: choosing it after the order is drawn increases
the free value by $m-1$, but the marginal constraint then costs at most $1+1/m$.
For arbitrary weight perturbations we prove a Lipschitz bound with recomputed baselines and
normalisation. In odd size, the infimum price ratio over an $\ell_1$ ball of radius
$0<\varepsilon\le1/6$ is $\Theta(\min\{m,1/\varepsilon\})$, with absolute constants.
This is a sharp scale for the erosion of a uniform guarantee, not a claim that every
perturbation destroys the parity effect. The core frontier, attainability, flow and stability
results have Lean~4 proofs; the robust-ball statement is derived explicitly from their bounds.
Stored optimisation certificates and perturbation results provide finite-instance checks.
''')
rep(C,'It vanishes exactly at $\\eta_{*}=\\frac{m-2}{2(m-1)}$','The premium over one vanishes exactly at $\\eta_{*}=\\frac{m-2}{2(m-1)}$')
rep(C,r'''\ref{thm:collapse}). A Lipschitz envelope for arbitrary weights, and the collapse scale of
the price. The price is linear exactly while the perturbation is $O(1/m)$, and it decays as
$\Theta(1/\varepsilon)$ beyond, with the lower bound $\frac1{16}\min(m-1,\frac1\varepsilon)$
holding at every size of perturbation up to $\frac16$.''',r'''\ref{thm:collapse}, Corollary~\ref{cor:robustball}). A Lipschitz envelope for arbitrary
weights, and a two-sided law for the smallest price ratio in an $\ell_1$ ball:
$\Theta(\min\{m-1,1/\varepsilon\})$ for $0<\varepsilon\le1/6$.
Radius $1/m$ marks when a linear-in-$m$ price ceases to be guaranteed uniformly;
some much larger perturbations preserve it exactly.''')
rep(C,'The next theorem locates the collapse from both\nsides.','The next theorem combines a lower bound valid for every perturbation with an upper bound\nachieved by one explicit perturbation. The distinction between those quantifiers matters.')
section(C,'Together with the last clause of Theorem~\\ref{thm:robust}', 'The upper side is a parity argument.',r'''Define the price that is guaranteed throughout a ball by
\begin{equation}
\mathcal R_m(\varepsilon)=
\inf_{\substack{\|g'-g_m\|_1\le\varepsilon\\V(g';m)>0}}
\frac{V(g';0)}{V(g';m)}.
\label{eq:robustball}
\end{equation}
The positivity condition avoids division by a zero free optimum. The set is nonempty since
it contains $g_m$.

\begin{corollary}[Sharp order of the uniform robustness guarantee]
\label{cor:robustball}
For odd $m\ge3$ and $0<\varepsilon\le1/6$,
\begin{align}
\frac1{16}\min\{m-1,\varepsilon^{-1}\}
&\le \mathcal R_m(\varepsilon)\nonumber\\
&\le\min\left\{\frac{(m+3)(m-1)}{2m},\frac{10}{\varepsilon}\right\}\nonumber\\
&\le10\min\{m-1,\varepsilon^{-1}\}.
\label{eq:robustballrate}
\end{align}
\end{corollary}
\begin{proof}
At a distance $d\in(0,\varepsilon]$, Theorem~\ref{thm:collapse}(b) bounds the ratio below by
$\min\{m-1,1/d\}/16\ge\min\{m-1,1/\varepsilon\}/16$.
At distance zero the exact ratio is $(m+3)(m-1)/(2m)$, which also satisfies that bound.
This lower bound is uniform, so it passes to the infimum.
For the upper bound use, separately, $g_m$ itself and the one-item perturbation in
Theorem~\ref{thm:collapse}(a) with $\delta=\varepsilon$. Both are feasible in the ball and
have positive free value. Finally $(m+3)/(2m)\le1$ for $m\ge3$.
\end{proof}
\leanbox{Inputs: \lean{odd\_uniform\_price\_ratio}, \lean{collapse\_upper} and
\lean{collapse\_all} in \lean{LeanPaperCOddWitnessJoinV1},
\lean{LeanPaperCCollapseScaleV1}, and \lean{LeanPaperCCollapseWindowV1}, respectively.
The infimum-over-balls wrapper is proved above; it is not yet a separate Lean declaration.}
% FORMAL FOLLOW-UP: define the ball price and discharge csInf lower/upper using the
% nonempty witness g_m, collapse_all for d>0, and collapse_upper at delta=epsilon.

\paragraph{Why this is not a law for every perturbation}
For any $\varepsilon>0$, take $g'=(1+\varepsilon/(m+4))g_m$.
Then $\|g'-g_m\|_1=\varepsilon$, but every prefix magnitude, every budget baseline and the
normaliser scale by the same positive number. The feasible laws do not change, so
$V(g';\eta)=V_m(\eta)$ at every $\eta$. Its price stays proportional to $m$ even at a fixed
nonzero radius. Thus~\eqref{eq:robustballrate} identifies when the guarantee can deteriorate,
not when every instance must deteriorate. For $\varepsilon\le1/(2m)$ the stronger uniform
lower bound $(m-1)/4$ follows directly from Theorem~\ref{thm:robust}.

''')
rep(C,'A search returns\nattained ratios, which are upper bounds on the worst case.','A minimising search returns\nattained ratios, hence upper bounds on the infimum over its perturbation domain, not lower\ncertificates for that infimum.')
rep(C,r'''with $d=\min(\|g_{m}\|_{1},\|g'\|_{1})$. A point in the shaded region would refute
Theorem~\ref{thm:robust}; none enters it, and the worst ratio is $0.32$. The producer skips
solver failures without recording them, so row counts were compared with its fixed grid, and
none was dropped.''',r'''with $d=\min(\|g_{m}\|_{1},\|g'\|_{1})$. A point in the shaded region would flag a
mismatch requiring investigation of the model, solver and theorem; none enters it, and the
largest drift/envelope ratio is $0.32$. The producer version associated with these saved
results could skip solver failures, so the 220 recorded rows were checked against the full
prescribed grid; none was missing.''')
rep(C,'which are upper bounds on the worst case,\nagainst the fixed-normaliser floor','which are upper bounds on the searched infimum,\nagainst the fixed-normaliser floor')
rep(C,'\textbf{Constants of the collapse.}', '\textbf{Constants of the collapse.}',count=0) if False else None
rep(C,r'''\item[2)] \textbf{Constants of the collapse.} Theorem~\ref{thm:collapse} pins the collapse
scale in order. Its two sides differ by a constant factor, and its lower side needs a
positive unconstrained value, which the unperturbed family has.''',r'''\item[2)] \textbf{Robustness is a guarantee over a ball.} Corollary~\ref{cor:robustball}
determines the smallest attainable ratio only up to absolute constants and excludes zero
free values. It does not characterise every perturbation, nor give an exact robustness curve.
The exact frontiers at $g_m$ and this perturbation law are different results.''')
section(C,r'\section{Conclusion}',r'\section*{Companion material}',r'''\section{Conclusion}

For one distribution over orders serving all removal budgets, uniform item marginals have
an exact price that depends sharply on parity. The complete frontier and explicit attaining
laws show where this price disappears; the composition flow preserves the optimisation over
all orders rather than restricting it to a constructed menu. Two changes of quantifier have
different effects. Choosing the budget after the draw raises the free cost but makes the
marginal band almost free. Requiring a guarantee over perturbed weights preserves a linear
odd-size price only to radius of order $1/m$; the guaranteed price thereafter scales as
$1/\varepsilon$, although individual perturbations can preserve the original ratio.
These results separate marginal fairness, budget timing and robustness within one precisely
specified compression objective.

''')
# Supplements: keep proof details and explicitly synchronize the new mathematical conclusions.
rep('paper_a_supplement.tex','round-robin over the four $A$\ncells','round-robin over the four frozen cells (two $A$ cells and two $B$ anchors)')
before('paper_a_supplement.tex',r'\section{S8.',r'''\section*{Additional proof map: the general repair certificate}
The main paper's certificate proposition uses \lean{exchange}, \lean{frontier\_upper},
\lean{budget} and \lean{weak\_duality} in \lean{LeanPaperASacrificeDualityV1}.
Its assumptions are inequalities for every allocation: a frozen upper certificate, true
alternative loads, and a nonnegative cover of those loads by the frozen margins.
They are not assumed for our example: \lean{cStar\_cert}, \lean{pairLoad\_cert},
\lean{nuStar\_cover} and \lean{certificate\_pair\_satisfiable} construct them, and
\lean{construction\_budget} takes the strict-alternative limit.
The converse uses \lean{repair\_mix} with mixing coefficient
$\lambda=\min\{1,b/s(v)\}$. Therefore its valid budget form is
$R(b)\ge\min\{1,b/s(v)\}J_t(v)$, for $s(v)>0$ and $b\ge0$.
The unclipped expression $bJ_t(v)/s(v)$ requires $b\le s(v)$.
The module's introductory prose omits that restriction, but its actual theorem explicitly
requires the mixing coefficient in $[0,1]$ and is the result used here.
Exact bounds hold for every $r\ge1,M>0$. Statements with absolute constants using
$\Theta(rM)$ or $\Theta(\beta/(rM))$ are restricted to $rM\ge1$; they are not joint limits
as $rM\downarrow0$.

''')
before('paper_c_supplement.tex',r'\paragraph{The collapse, upper side}',r'''\paragraph{Quantifiers in the robustness conclusion}
The universal lower bound and the one-item upper construction combine into a statement about
an infimum over a perturbation ball, not about every point in that ball. For odd $m$ define
$\mathcal R_m(\varepsilon)=\inf_{\|g'-g_m\|_1\le\varepsilon,\ V(g';m)>0}
V(g';0)/V(g';m)$. The main paper proves explicitly that, for $0<\varepsilon\le1/6$,
\[
\frac1{16}\min\{m-1,1/\varepsilon\}\le\mathcal R_m(\varepsilon)
\le\min\{(m+3)(m-1)/(2m),10/\varepsilon\}.
\]
To formalize this wrapper, first prove the feasible set nonempty using $g_m$ and its positive
free value. For every member at positive distance use \lean{collapse\_all}; at zero distance
substitute the exact odd ratio. This gives a uniform lower bound and boundedness below.
Apply the infimum upper bound separately to $g_m$ and the explicit one-item construction at
$\delta=\varepsilon$. No minimiser of the ball problem is required.
This wrapper has a mathematical proof in the main text but no separate Lean declaration yet.
Positive scaling, $g'=(1+\varepsilon/(m+4))g_m$, preserves all normalised regrets and gives a
counterexample to the stronger, incorrect statement that every perturbation beyond $1/m$
forces the ratio to decay.

''')
# Commit files only after all transformations and concurrent-change checks pass.
for n in names:
    assert (T/n).read_bytes()==original[n],('Concurrent edit; nothing written',n)
changed=[]
for n in names:
    if d[n].encode()!=original[n]:
        (T/n).write_text(d[n]); changed.append(n)
(R/'research/audit_current_20260925/MANUSCRIPT_EDITS_PHASE1.json').write_text(json.dumps({'backup':str(B),'before':manifest,'changed':changed},indent=2)+'\n')
print(json.dumps({'changed':changed,'backup':str(B)}))
