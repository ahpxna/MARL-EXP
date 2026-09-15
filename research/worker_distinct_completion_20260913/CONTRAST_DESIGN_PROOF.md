# R1 complete graph design and resistance bridge

Model: a primitive edge observation has mean theta_a-theta_b, variance sigma_ab^2, and its own stated cost. The conductance is exposure/variance. It is not the difference of two scalar observations at unit cost and unit variance.

## Fixed connected graph

For symmetric nonnegative conductances with zero diagonal set L_aa=sum_b c_ab, L_ab=-c_ab, and E(z)=z' L z/2. The positive-edge graph is connected. Restrict L to vectors with coordinate sum zero. Its quadratic form is sum_{a<b} c_ab(z_a-z_b)^2, which vanishes only on constant vectors; on the restricted space that constant must be zero. Thus the restriction is positive definite and invertible.

For a != b, solve L p=e_a-e_b with sum p=0. Put R_ab=p_a-p_b=p' L p>0. If z_a-z_b=x, set h=z-(x/R_ab)p. Then h_a-h_b=0 and p' L h=(e_a-e_b)'h=0. Consequently

    E(z)=x^2/(2R_ab)+E(h).

Over z_a-z_b>=Delta>0, the minimum is Delta^2/(2R_ab), attained at z=Delta p/R_ab. Range>=Delta is the finite union over ordered pairs of these constraints. The overall infimum is therefore Delta^2/(2 max_{a!=b} R_ab). The maximizing resistance pair and its potential provide an attaining alternative and an energy certificate.

If the positive-edge graph is disconnected with at least two components, assign values Delta and zero to two component groups. Every positive-edge difference is zero, while the range is Delta. Nonnegative energy gives infimum zero. With a single vertex there is no range-changing alternative; that degenerate case is excluded from the stated formula.

## Uniform complete topology and optimal design

Let K>=2, unit variance, and sum of unordered edge exposures equal one. Uniform complete conductance is 2/[K(K-1)]. The identity

    sum_{a,b}(z_a-z_b)^2=2K sum_a(z_a-mean(z))^2

and two-endpoint inequality sum_a(z_a-mean(z))^2 >= range(z)^2/2 yield E(z)>=Delta^2/[2(K-1)]. The vector with two values +/-Delta/2 and all other values zero attains this. These identities, the lower bound, its witness, and the exact infimum are in the newly compiled Lean modules (subject to each recorded build receipt).

Optimality over all normalized complete-edge designs also follows without assuming a permutation WLOG. Choose an unordered endpoint pair uniformly and assign +/-Delta/2 to its endpoints with either orientation. For each fixed edge {i,j}, squared difference is Delta^2 if the chosen pair is {i,j}, Delta^2/4 if exactly one endpoint is in {i,j}, and zero otherwise. There is one pair of the first type and 2(K-2) of the second. Hence the average squared difference is

    [Delta^2+2(K-2)Delta^2/4]/binom(K,2)=Delta^2/(K-1).

For any design c with sum c=1, averaging E over these feasible witnesses is Delta^2/[2(K-1)]. At least one witness has energy no larger than this average. Thus no design improves on the uniform complete value. Equivalently, infima of linear energies are concave and permutation symmetrization yields the same conclusion. The finite averaging optimality proof is written here, but not yet counted as a compiled Lean theorem.

## Uniform star and path

Each of K-1 edges has conductance 1/(K-1), so resistance per edge is K-1. In a tree, the unit-current solution sends one unit along the unique a-b path and zero elsewhere; voltage drop is the path length times K-1. The star diameter is two for K>=3, and path diameter is K-1. Substitution yields

    J_star=Delta^2/[4(K-1)],
    J_path=Delta^2/[2(K-1)^2].

For K=2 the star is a single edge, not a diameter-two tree, so the star formula with the factor four is inapplicable. The complete/path complexity ratio is K-1 under these exact exposure and variance conventions.

## Evidence and remaining question

The existing exact Fraction probe covers K=3,4,6,8,12 and all three topologies, solves grounded Laplacians, and exports pair potentials, primal energy, equation residuals and dual values. It is a finite certificate, not the Lean proof of invertibility for every connected graph. The connected effective-resistance theorem and the unknown-extrema Laplacian-QP topology design remain to be formalized/implemented; the flat complete theorem does not settle those questions.
