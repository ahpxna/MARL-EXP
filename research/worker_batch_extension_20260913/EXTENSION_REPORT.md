# Worker extension — 13 September 2026

This extension continues the eight-package assignment after the separately installed 13-module checkpoint. Only modules listed as accepted in `extension_manifest.json` and `EXTENSION_RECEIPT.md` are accepted. It does not close the whole research programme.

## Structural: approximate anchors and finite minimum

For m coordinates with sorted nonnegative bounds c_i≥osc(f_i)/2, write B=sum_i c_i>0. An anchor oracle at budget a may return any set S of size a with selectedRadius(S)≤OPT_a+eta B; it need not return an exact optimum. For 0≤eta<eps, the normalized theorem proves a menu with at most floor(2/(eps−eta))+1 rankings and an eps B-optimal prefix at every budget.

The proof carries the anchor error through the actual support-radius cheap-extension theorem. At each step `nextIndex` is the minimum unused index, a finite computation which does not compare real-valued radii or use `Classical.choose`. Monotonicity of c makes it cheap enough for the previously proved one-step radius inequality. Induction gives error eta B plus accumulated charges. With potential Phi(k)=sum_{z<k}(c_z+c_{m−1−z}), each nonempty bucket of width (eps−eta)B needs only its smallest-budget anchor. Two budgets in a bucket differ in potential by less than that width. Phi(m)=2B gives the menu bound.

The Lean menu theorem is an existence theorem for rankings and assumes the anchor oracle's accuracy. The finite `nextIndex` transition is executable. The separate rational implementation `structural/approximate_menu.py` constructs complete rankings, calls its supplied oracle exactly once per nonempty bucket, caches the result, records each call budget, and records which ranking covers every budget. It validates returned cardinality and indices. Accuracy of the oracle itself must still be certified; no polynomial-time claim is made for an arbitrary anchor solver.

`check_approximate_menu.py` evaluates this actual implementation against exhaustive finite-support objectives in 144 cases. The test oracle deliberately returns the worst anchor within the allowed error. There are 269 strictly suboptimal returned anchors; every claimed prefix bound holds. Equal/reversed tolerances and unsorted bounds are rejected. These finite checks support the implementation, not a uniform runtime theorem or a lower bound on necessary oracle calls.

## D6: uniformity on compact intervals

`LeanD6UniformScaledBoundsV1` extends the accepted explicit finite-value error. All constants D, Db and Cv are monotone in nonnegative tau: polynomial factors increase and C=exp(−2tau) decreases, so reciprocal factors increase. For all tau∈[0,U], rho∈[1,2], the same bound

    |V_k(tau,rho)/k − G(tau,rho)| ≤ Cv(U)/k

holds when k≥2, k≥2U, and 2D(U)/k≤exp(−2U). This is a uniform finite inequality, with no asymptotic error premise.

On [L,U] with L>0, b_k is uniformly close to tau exp(−2tau) and the latter is at least L exp(−2U)>0. For sufficiently large k this yields (k−2)b_k≥1 simultaneously for every tau in the interval. The physical strong condition is retained and discharged uniformly. The first-order boundary-window expansion remains open.

## MASTER: fixed world, changed reference, specified instrument

`LeanMasterFixedWorldResponseV1` holds compensation and centering fixed at t0 in the actual function F_{A,t0}. Changing only the query reference to t changes its response slope to

    target_i + gateSlope(t,A,i) − gateSlope(t0,A,i).

For two equal-cardinality hidden worlds that swap membership of coordinate i, the response-slope contrast is

    (1−t)^(|A|+|others(A,j)|−1) − (1−t0)^(|A|+|others(A,j)|−1).

In the intended 2k-coordinate construction the exponent is 2k−2. The local derivative is also proved. These are identities of the fixed physical functions; no re-compensation at the new reference is performed.

The module explicitly defines a Gaussian instrument whose mean is that response slope and whose variance is a specified nonnegative parameter. At t0 its law is the same Gaussian with mean target_i across admissible hidden worlds. This law claim concerns that instrument. Adaptive KL/cost lower bounds, a finite-confidence testing upper bound, and a justified reference-cost model are still open.

The exact-rational script checks 30 reference contrasts in 6- and 8-coordinate worlds. Its negative control shows that identical first-order responses do not imply identical raw sample laws. At m=6, t0=1/8, rho=3/2, A=T={0,1,2}, B={1,2,3}, j=5, the two raw means are both zero, but the third moments are respectively

    690842536687107 / 1125899906842624
    902280581592579 / 1125899906842624.

Adding independent centered Gaussian noise preserves these third moments because both raw means are zero. The raw laws are therefore different. The script also computes the positive full-observed-X squared-difference information expression; this arithmetic check is not a Lean proof of an adaptive KL chain.

## Functional: allocator certificates from the actual full-cost oracle

`LeanFunctionalWeightCertificatesV1` defines information over the same two-row, three-action, tie-allowing full-extrema alternatives and proves equality with the previously accepted `fullCost`. Its value is concave in nonnegative precision weights, because each alternative's energy is linear in those weights.

A feasible alternative with energy at most J(p)+eps gives an eps-supergradient: g_ra=(lambda_ra−theta_ra)^2/2, and J(q)≤J(p)+eps+(q−p)·g for any nonnegative q. If q lies in the unit simplex and M bounds all six coordinates of g, then J(q)≤J(p)+eps+M−energy(p,lambda). This is a checkable global allocation-gap certificate supplied by an approximate oracle, with all full-extrema alternatives retained. These weights are precisions; conversion to query probabilities with unequal variances requires the corresponding variance factors. No empirical or theorem-level advantage over C_lucb is claimed.

## Query: physical horizon restriction on the stored panel

`query/check_physical_horizon_repair.py` reuses the existing natural reachable panel, with hashes of the panel and helper source recorded. It includes all 1,600 successful snapshot-candidate units, including 1,541 constant horizon-6 profiles. The world includes physical state and RNG state. Decoder inputs contain no seed, physical hash, RNG key, or unique identifier.

The base representation is the centered horizon-1 intervention response. The only permitted extra feature is the actual stored horizon-2 response, at the declared incremental cost of five two-step rollouts (10 environment steps). Exhausting both feature subsets gives minimax scalar ATE error 3/5 in both cases. The extra response refines two fibres to six, but does not lower the worst fibre diameter. A stored endpoint pair in the all-zero c1/c2 fibre, with distinct physical states and targets −3/5 and 3/5, certifies the lower bound; the fibre midpoint attains it. This strongest full-population floor is a degenerate-summary obstruction. Separately, the 20 units with nonzero c1 have minimax radius 1/10 both before and after the horizon-2 purchase, with a distinct-physical-state witness. The full-population 3/5 floor must not be presented as that nondegenerate witness. Thus no repair in this restricted catalog achieves eps<3/5; eps≥3/5 needs zero incremental acquisition on this empirical population.

A 15-seed/5-seed holdout split scores all 400 test units without unseen-fibre abstentions, with worst midpoint error 3/5 for both representations. This is a finite empirical result, not a population guarantee. A fabricated unique identifier produces 1,600 singleton fibres and is rejected as a physical feature. The negative result limits claims for the horizon≤2 catalog; it does not prove impossibility for every physical intervention library.

## Remaining assignment

The principal open obligations remain the adaptive common transcript and sample laws, whole-algorithm stopping tails and expected Gamma rate, matching lower bounds under the same experiment, and growing-q costs. Other open targets include the D6 boundary layer, the cyclic Support query lower/upper strategy, Functional general dimensions/coupling and comparison to C_lucb, and MASTER acquisition cost bounds. The above results should be cited with their stated scopes. No publication-readiness or literature-priority claim is made.
