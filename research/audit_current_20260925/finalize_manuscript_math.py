from pathlib import Path
R=Path('/Users/phanan/cig-amf-main');T=R/'research/papers/_tex'
names=[f'paper_{p}{s}.tex' for p in 'abc' for s in ('','_supplement')]
o={n:(T/n).read_bytes() for n in names};d={n:v.decode() for n,v in o.items()}
def rep(n,a,b,count=1):
 assert d[n].count(a)==count,(n,a[:100],d[n].count(a),count)
 d[n]=d[n].replace(a,b)
def before(n,mark,new):rep(n,mark,new+mark)
A='paper_a.tex';C='paper_c.tex'
before(A,r'\begin{theorem}[The ideal learner]',r'''\subsection{The rule that the theorem actually analyses}
Let $\mathcal A_T$ be the strict centred alternatives to answer $T$, and let $N_e(t)$ and
$\widehat\theta_e(t)$ be the count and raw sample mean after $t$ observations. The variance
$\nu_e>0$ is known. For $a>0$ the stopping statistic and threshold are
\begin{align}
Z_t^a(T)&=\inf_{\lambda\in\mathcal A_T}
 \frac12\sum_e\frac{N_e(t)^2}{(a+N_e(t))\nu_e}
 (\widehat\theta_e(t)-\lambda_e)^2,\label{eq:ridgestop}\\
b_t(\delta)&=\log(1/\delta)+\frac12\sum_e\log(1+N_e(t)/a).
\label{eq:idealboundary}
\end{align}
This is the exact infimum of a ridge-weighted statistic. It is not the ordinary Gaussian
log-GLR, whose coefficient would be $N_e(t)/\nu_e$. The finite-count shrinkage is part of
the confidence argument, even though $N_e/(a+N_e)\to1$ under forcing.
The stopping time is
$\tau_\delta=\inf\{t\ge K:\max_T Z_t^a(T)>b_t(\delta)\}$, with value $+\infty$ when this set
is empty; the output is the first maximiser of $Z_t^a$ at the stop.
\leanbox{\lean{qAbs}, \lean{qAbs\_eq}, \lean{glr}, \lean{measurable\_glr} in
\lean{LeanPaperA7GLRMeasV1}; \lean{Zh}, \lean{stopAt}, \lean{answerAt}, \lean{tauI} in
\lean{LeanPaperA7IdealStopV1}; \lean{bthr} in \lean{LeanPaperA7ConfidenceV1}}

The query rule also reads only the history. First query each of the $K=4+2r$ cells once.
Thereafter let
\[
\Delta_{s+1}=\{w\in\Delta:(s+1)w_e\in\mathbb N\text{ for all }e\},
\qquad
(T_s,w_s)\in\arg\max_{T,\,w\in\Delta_{s+1}}J_T(w;\widehat\theta(s)),
\]
with a fixed tie order, where $J_T$ uses the entire alternative set, without a box.
Put $u_e=1/K$, $\rho_s=1/\sqrt{s+1}$, and $v_s=(1-\rho_s)w_s+\rho_su$.
After $t\ge K$ observations choose
\[
q_{t+1}\in\arg\max_e\left\{\sum_{s=K}^{t}v_{s,e}-N_e(t)\right\},
\]
again with fixed ties. The quota starts at zero after the warm start; the counts still
include the warm samples. This convention is the one in the formal tracking lemma.
\leanbox{\lean{netSet} in \lean{LeanPaperA7NetOracleV1}; \lean{oracle}, \lean{target},
\lean{quota}, \lean{pick}, \lean{measurable\_pick} in \lean{LeanPaperA7IdealLearnerV1};
\lean{famSpec} in \lean{LeanPaperA7IdealFamilyV1}}

Why does the threshold certify an answer? At a candidate true world $\theta$, define
\[
M_t(\theta)=\prod_e\sqrt{\frac{a}{a+N_e(t)}}
\exp\left\{\frac{N_e(t)^2(\widehat\theta_e(t)-\theta_e)^2}
{2(a+N_e(t))\nu_e}\right\}.
\]
It is a nonnegative martingale under the adaptive Gaussian observation law, starting at one.
If an incorrect answer $T$ crosses~\eqref{eq:idealboundary}, then
$\theta\in\mathcal A_T$ and $M_t(\theta)>1/\delta$.
Ville's inequality supplies correctness. Tracking, vanishing grid error and the direct
information-accumulation bound supply termination and the expected rate; correctness alone
would supply neither.

''')
rep(A,r'''$\frac{1}{\sqrt{s+1}}$ and tracks the result. It stops when some answer's generalised
likelihood ratio exceeds $\log(1/\delta)+\frac12\sum_{e}\log(1+N_{e}/a)$. On the construction,''',r'''$\frac{1}{\sqrt{s+1}}$ and tracks the result. It stops at the ridge-statistic crossing
\eqref{eq:ridgestop}--\eqref{eq:idealboundary}. On the construction,''')
rep('paper_a_supplement.tex',r'''its stop uses the exact generalised likelihood ratio, so the stopping-certificate gap is zero
by construction.''',r'''its stop uses the exact infimum of the ridge statistic
$\frac12\sum_e N_e^2(\widehat\theta_e-\lambda_e)^2/((a+N_e)\nu_e)$,
so its stopping-certificate gap is zero by construction. This is \lean{glr} in
\lean{LeanPaperA7GLRMeasV1}; despite that identifier, it is not the ordinary Gaussian
log-GLR with coefficient $N_e/\nu_e$. The main text gives the full query and stopping rule.''')
rep(C,'Each theorem carries one line naming its Lean declaration. The proof architecture and every\nsupporting declaration are in the supplement. All modules compile with no \\texttt{sorry} and\nno \\texttt{native\\_decide}, and their axioms lie within \\{\\texttt{propext},','Each formal theorem carries a line naming its Lean declaration. The robust-ball corollary\nis a mathematical consequence proved in this text, with its formal inputs identified, and is\nnot represented as a separately checked wrapper. The proof architecture and supporting\ndeclarations are in the supplement. Audited modules use no \\texttt{sorry} or\n\\texttt{native\\_decide}, and their axioms lie within \\{\\texttt{propext},')
rep(C,'\\caption{The three closed forms, drawn from the theorems. Left: the whole frontier','\\caption{Exact frontiers and robustness bounds, drawn from the theorems. Left: the whole frontier')
rep(C,'the collapse scale at $m=101$, theorem curves only. Black: the envelope floor of','the erosion of a uniform guarantee at $m=101$, theorem curves only. The lower curves hold\nfor every admissible perturbation; the dashed upper curve is attained as a bound by one\nconstruction, not imposed on every perturbation (Corollary~\\ref{cor:robustball}). Black: the envelope floor of')
rep('paper_c_supplement.tex','returns attained ratios, upper bounds on the worst case, so it can exhibit a collapse but','returns attained ratios, upper bounds on the searched infimum, so it can exhibit a collapse but')
for p in 'abc':
 n=f'paper_{p}.tex'
 rep(n,'\\caption{Nearest sources, and a theorem of this paper that does not follow from each.}', '\\caption{Closest research threads and the specific quantitative results compared here.}')
 rep(n,'Nearest source & Theorem here that does not follow', 'Nearest source & Specific result compared here')
for n in names:assert (T/n).read_bytes()==o[n],('Concurrent change',n)
for n in names:
 if d[n].encode()!=o[n]:(T/n).write_text(d[n])
p=R/'research/audit_current_20260925/check_manuscripts_static.py'
s=p.read_text().replace("re.split(r'(?<!\\\\)%',line,1)","re.split(r'(?<!\\\\)%',line,maxsplit=1)")
s=s.replace("if s.count('\\\\[')!=s.count('\\\\]'):errors.append('display delimiter mismatch')", "if len(re.findall(r'(?<!\\\\)\\\\\\[',s))!=len(re.findall(r'(?<!\\\\)\\\\\\]',s)):errors.append('display delimiter mismatch')")
p.write_text(s)
print('Updated the exact A stopping statistic and final consistency fixes.')
