# D6: a reference-dependent minimax phase law

This note derives a new candidate headline from the actual gate construction. The general cube-to-orbit reduction below is a mathematical proof, not yet a Lean theorem. The reduced bilinear certificate has been Lean-compiled separately. Numerical LP agreement is not used as the proof of the formula.

## Construction and quantifiers

There are 2k coordinates, k>=3. Fix a distinguished coordinate z and a visible k-set T excluding z. Hidden A ranges over all k-subsets excluding z, and B is its (k-1)-element complement among the other coordinates. Write

    g_A(x) = (1-x_z) 1{some coordinate of A is on, or at least two of B are on}.

The reference is the product Bernoulli(t) law, 0<=t<=1/2. For each reference construct

    F_{A,t} = g_A - E_t[g_A] + sum_i (rho 1_T(i)-s_i(t))(x_i-t),

where s_i(t) is the conditional response slope of g_A. Thus Q_i(u)=rho 1_T(i)(u-t), independent of A, and delta_square remains exactly 1. This is a family of worlds constructed for each reference, not a claim that a single fixed world has identical responses at different references.

For 1<=rho<=2, define

    c=(1-t)^(2k-2), a=c(1+(k-2)t), b=c(k-2)t.

Direct Bernoulli probabilities give s_A=a, s_B=b, s_z=a-1. In particular a-b=c>0, 0<=b<=a<=1. Also b<=1/4: putting n=k-2, the Bernoulli inequality gives (1-t)^n<=1/(1+nt), hence b<=nt/(1+nt)^2<=1/4.

## Exact oscillation reduction

A decision keeps k coordinates. Only D=T\\S matters, since the other prescribed response slopes vanish. Let d=|D| and u=|A intersect D|. Constants do not affect oscillation. The actual residual is

    g_A + sum_i (rho 1_D(i)-s_i(t)) x_i.

For 1<=rho<=2 its positive linear coefficients occur in D and its negative coefficients outside D. Let

    Lmax=rho*d-a*u-b*(d-u),
    Lmin=-a*(k-u)-b*(k-1-d+u),
    correction(d,u) = min(a,2b) if d=0;
                      b if d=1 and u=0;
                      0 otherwise.

The maximum is 1+Lmax-correction. At z=1 the minimum is Lmin+1-a. At z=0 with the gate off, the minimum is -b if a B coordinate remains outside D, and 0 otherwise. At z=0 with the gate on, the unconstrained linear minimum is feasible: either an A coordinate is negative, or all k-1>=2 B coordinates are negative. This last candidate is Lmin+1 and is no smaller than the z=1 candidate. Therefore

    loss(d,u) = [1+Lmax-correction
                 - min(Lmin+1-a, -b if k-1-d+u>0 else 0)]/2.

The accompanying script checks this formula with Fraction on the full cubes at k=3,4, five references and four margins (460 feasible count configurations), including the response slopes computed by independent product summation.

## Exact game when (k-2)b>=1

This sufficient condition ensures Lmin+1-a<=-b for every decision. Put

    p=rho-2b>0, r=2a-rho, e=min(a,2b), c=a-b.

If h=|A intersect T|, then 1<=h<=k. Up to a world-dependent constant, twice the loss is

    p*d-2c*u-correction(d,u).

An optimum is either D=empty or D=A intersect T: coefficients on A favor taking all available A when r>0, coefficients on B are positive, and the only exceptional discount favors D=empty. The singleton B exception cannot improve on empty because e>=b. Hence twice the optimal variable part is -max(e,r*h), and actual regret is

    R(h,d,u)=[p*d-2c*u-correction(d,u)+max(e,r*h)]/2.

Symmetrize any decision distribution by permutations of T and its complement fixing z. The family is invariant and worst-case risk cannot increase. Conditional on d, D is uniform among its d-subsets, so E[u]=h*d/k.

Every d is dominated by the mixture of d=0 and d=k with weights 1-d/k and d/k. For d>=2 its correction is zero while that mixture receives (1-d/k)e. For d=1 the expected correction is b(k-h)/k, which is at most (k-1)e/k. Thus the reduction to two actions is proved, not an LP ansatz.

For a mixture of these two actions the risk is convex in h, so its maximum on {1,...,k} is attained at h=1 or h=k. If kr<=e then d=0 is optimal in every world and the minimax value is zero. Otherwise the exact two-by-two matrix (rows h=1,k; columns d=0,k) is

    [ (r-e)_+/2,  (p(k-1)+(e-r)_+)/2 ]
    [ (kr-e)/2,   0                  ].

Its matching value is

    V_k(t,rho) = (kr-e)_+ [p(k-1)+(e-r)_+] / [4c(k-1)].

For the active case write U=(kr-e)/2, u0=(r-e)_+/2, v=(p(k-1)+(e-r)_+)/2. The primal puts probability v/(U-u0+v) on d=0; the dual puts probability (v-u0)/(U-u0+v) on h=k. These are in [0,1]: U>=u0 and v>=u0, using p>=1/2, r<=1 and k>=3. The singleton-intersection row means the uniform prior on actual h=1 worlds. The rational-certificate script checks every h and d and recomputes the true optimum by enumeration of all feasible (d,u).

This yields the finite-reference threshold rho_crit=2a-e/k within the stated sufficient regime. Outside that regime the general oscillation formula remains valid, but this particular minimax formula is not asserted.

## Growing dimension

For fixed tau>0 and t=tau/k, eventually (k-2)b>=1. With

    a_inf=(1+tau) exp(-2tau), b_inf=tau exp(-2tau), c_inf=exp(-2tau),

the formula implies

    V_k(tau/k,rho)/k ->
      [(rho-2 b_inf)(2 a_inf-rho)]_+ / (4 c_inf).

At tau=0 the already compiled corner theorem supplies rho(2-rho)/4. The limiting positive-floor boundary is

    2(1+tau_crit) exp(-2tau_crit)=rho.

Examples: tau_crit is approximately 0.57309661 at rho=1, 0.25899986 at rho=1.5, and 0.06265407 at rho=1.875. This is a phase boundary for decision insufficiency under a reference, not the adaptive allocation boundary mu_U.

## Evidence and remaining Lean work

- `LeanD6ReferenceReducedGameV1`: five clean axiom audits, including primal/dual equalizers for the leading bilinear game and the cost of replacing the unavailable h=0 world by h=1. It does not formalize the new general-reference construction.
- `d6_reference_phase_reduction_v1.json`: 460 exact small-cube checks and 90 numerical orbit LPs through k=64. All 36 cells meeting the sufficient condition agree with the finite formula within 5.4e-15.
- `d6_reference_phase_certificates_v1.json`: separate exact rational certificates; only count completed cells in that artifact, not this planned filename.
- Next Lean target: product sums -> three slopes -> exact oscillation -> two-action dominance -> endpoint-world reduction -> the finite formula. Reuse the existing corner same-Q chain only for the tau=0 endpoint.

An additional reference can itself be an information-bearing intervention. For a fixed world compensated at t0, its response slopes at t1 differ between A and B by c(t1)-c(t0), after subtracting the visible target. This suggests pricing reference changes jointly with queries; it is a next research target, not a proved adaptive sample-complexity claim here.
