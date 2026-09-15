# R2: a scalar-only optimum despite opposing oracle width preferences

Status: mathematical derivation below; numerical verification completed on 48 cells. This new full-game equality is not yet claimed as a compiled Lean theorem. Existing compiled actual-mean identities provide its physical model.

## Model and statement

There are q+1 ordinary A coordinates, q ordinary B coordinates, and the special coordinate j. The true nuisance is mu in [1/2,1]. Scalar response means are 1 on A, 1-mu on B, and mu-1 at j. A legal joint query (G,h) has mean 1-2h+|G intersect B|(1-mu)+h mu. Width is r=|G|+h, scalar width is 1. Thus a legal h=true query can have width q+1; the B-only envelope in the handoff has h=false and width at most q.

Let scalar cost and variance both be one, and let each joint query's product of cost and variance be at least its width. The allocation is allowed every legal scalar and joint query. Wrong labels have the same cardinality as A, exclude j, and have arbitrary nuisance nu in [0,1]. Then the fixed-instance characteristic game is exactly

    Gamma = mu^2/(2q).

An attaining design allocates cost mass 1/q to each scalar coordinate in B. In particular the equality applies to cost*variance=r^z for z>=1. The design depends on the true label, as permitted by a characteristic-game supremum; this is not an adaptive implementation or a stopping theorem.

## Lower bound, uniform B scalars

Every wrong label C contains at least one b in B: otherwise C is a subset of A of the same cardinality and hence equals A. For every such b, its response mean under (C,nu) is 1, regardless of nu. The true mean is 1-mu, so that cell alone contributes mu^2/(2q). All other cells contribute nonnegative information. This proves the lower bound simultaneously for every wrong C and every nu, with no profiling assumption.

## Upper bound, adjacent-swap mixture

Choose a uniformly from A and b uniformly from B and use C=A-a+b with nu=mu. Infimum over all wrong alternatives is at most this mixture's expected information.

For scalar queries, expected KL is mu^2/[2(q+1)] on A, mu^2/(2q) on B, and zero at j. Thus every scalar's information per cost is at most the proposed value.

For a joint query write s=|G intersect A| and t=|G intersect B|. The same-nuisance mean difference is (1-mu) times the signed indicator that exactly one swapped coordinate is in G. Its average squared difference gives

    average KL = (1-mu)^2/2 * [s/(q+1)+t/q-2st/(q(q+1))]
               <= (1-mu)^2 (s+t)/(2q).

Here s+t=|G|<=r. Dividing by cost*variance>=r bounds the per-cost information by (1-mu)^2/(2q)<=mu^2/(2q). Averaging under any feasible cost allocation cannot exceed that value. This proves the matching upper bound, including arbitrary mixtures of widths and all nuisance alternatives in the original infimum.

## Consequence for the question in the handoff

The opposing B-only label-average and known-label margin envelopes for 1<z<2 do not force the full game to mix widths. For every q>=2 and mu>=1/2 the above legal scalar design is optimal. This does not characterize the region mu<1/2: the numerical grid includes width-two optima there and some mixed-width optima near z=1, but those observations are not universal theorems.

## Numerical evidence

`width_cost_game.py` uses the earlier semi-infinite LP solver and an independent full enumeration of all legal queries and all alternative labels. It expands dual label orbits before evaluating individual query bounds. All 48 cells (q=3,4; mu=.25,.5,.75; z=0,.5,1,1.25,1.5,1.75,2,2.5) passed with primal-dual gap below 2e-8. Output includes cost mass by width, active alternatives and nuisance values. No claim that every greedy acquisition fails, no empirical-to-adaptive-Gamma inference, and no priority claim is made.
