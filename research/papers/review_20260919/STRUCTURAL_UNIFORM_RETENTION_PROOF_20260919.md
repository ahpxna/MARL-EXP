# Structural: exact price of uniform retained marginals

19 September 2026. Mathematical proof prepared during the six-paper review. This is **not a Lean-verified theorem**. No new Lean compile is claimed. The finite certificates accompanying this note are independent diagnostics, not the proof for arbitrary size.

## Setting and the distinction that matters

Take the family in `research/papers/_tex/structural.tex`, for m ≥ 5:

\[
g_m=(-3,(-1)^p,(+1)^q,3),\quad
p=\lceil(m-2)/2\rceil,\quad q=\lfloor(m-2)/2\rfloor,
\quad D=m+4.
\]

The items are labelled, including items with equal weights. For a permutation π and a budget 1 ≤ k ≤ m−1, define

\[
S_k(\pi)=\sum_{j=1}^k g_{\pi(j)},\qquad
d_k(\pi)=|S_k(\pi)|-(k\bmod2),\qquad
r_k(\pi)=d_k(\pi)/D.
\]

Let P be a distribution on permutations. The additional constraint is

\[
\mathbb P_P(i\text{ is in the first }k\text{ positions})=k/m
\quad\text{for every labelled item }i\text{ and every }k.
\]

Equivalently, every labelled item has probability 1/m of occupying each position: subtract consecutive prefix probabilities. This is much stronger than the identity that the sum of the retention probabilities is k. The latter holds for every permutation distribution and does not enforce the former.

Write

\[
V_{\rm avg}^{\rm unif}(m)
=\inf_{P:\,\text{uniform retention}}\max_{1\le k<m}\mathbb E_P r_k.
\]

## Theorem

\[
\boxed{
V_{\rm avg}^{\rm unif}(m)=
\begin{cases}
\dfrac{4}{m(m+4)},&m\text{ even},\\[4pt]
\dfrac{m+3}{m(m+4)},&m\text{ odd}.
\end{cases}}
\]

The free value already proved in the corpus is 2/((m+4)(m−1)). Thus the multiplicative price of uniform retention is

\[
\frac{V_{\rm avg}^{\rm unif}}{V_{\rm avg}^{\rm free}}
=\begin{cases}
2(m-1)/m,&m\text{ even},\\
(m+3)(m-1)/(2m),&m\text{ odd}.
\end{cases}
\]

The odd-size ratio grows linearly. Both normalized values still tend to zero; this is a relative price, not a positive limiting absolute regret.

## Even m: lower bound

At budget 1, each item is first with probability 1/m. The two items of magnitude 3 have defect 2, and all other items have defect 0. Therefore

\[
\mathbb E d_1=4/m,
\qquad V_{\rm avg}^{\rm unif}\ge4/(mD).
\]

## Even m: an attaining distribution

Set B=m/2. Form B zero-sum two-item blocks: one special block (−3,3), and B−1 ordinary blocks (−1,1).

1. Choose the position of the special block uniformly among the B block positions.
2. Independently choose a fair orientation. In one orientation every block is written negative then positive; in the other every block is written positive then negative.
3. Assign the distinct labels of the negative unit-weight items uniformly to the negative unit slots, and do the same independently for the positive unit-weight items.

Each special item occupies each position with probability (1/B)(1/2)=1/m. Each position is a negative unit slot with probability (B−1)/(2B); dividing by the B−1 labels gives 1/m for every negative unit item. The positive unit items have the same property. Thus this distribution satisfies the entire retained-marginal constraint.

Every even prefix ends at a block boundary and has sum zero. An odd prefix contains the first item of one block. That block is special with probability 1/B=2/m. Hence

\[
\mathbb E d_k=
\begin{cases}0,&k\text{ even},\\4/m,&k\text{ odd}.
\end{cases}
\]

This attains the lower bound.

## Odd m: lower bound

The full sum is −1. At budget m−1, the retained sum is −1 minus the last item's weight. Since m−1 is even, there is no parity subtraction. Uniform last-position marginals force

\[
\mathbb E d_{m-1}
=\frac{|-1-(-3)|+|-1-3|+p|-1-(-1)|+q|-1-1|}{m}
=\frac{2+4+2q}{m}
=\frac{m+3}{m}.
\]

Therefore V_avg^unif ≥ (m+3)/(mD).

## Odd m: an attaining distribution

Put n=m−1, which is even. Generate the preceding even-size construction on n labelled items. Independently insert one additional labelled item of weight −1 at a uniformly chosen one of the m possible positions. The resulting multiset is exactly g_m.

Uniform position marginals are preserved. An old item appears in new position j either from old position j, when insertion is after j, or from old position j−1, when insertion is before j. The two contributions sum to

\[
\frac1n\frac{m-j}{m}+\frac1n\frac{j-1}{m}=\frac1m.
\]

At boundary positions the impossible contribution is zero, so the same formula holds. The new item is uniform by construction.

Let Y_j be the old prefix sum. At even j, Y_j=0. At odd j, sign symmetry holds, and |Y_j| is 3 with probability 2/n and 1 otherwise. Consequently

\[
\mathbb E|Y_j|=1+4/n,
\qquad \mathbb E|Y_j-1|=1+4/n
\quad(j\text{ odd}).
\]

For a new prefix of length k, the inserted item is included with probability k/m. Conditional on its inclusion the sum is Y_(k−1)−1; otherwise it is Y_k. Independence of insertion and the old permutation now gives

\[
\mathbb E d_k=
\begin{cases}
\dfrac{4(m-k)}{m(m-1)},&k\text{ odd},\\[5pt]
\dfrac{k(m+3)}{m(m-1)},&k\text{ even}.
\end{cases}
\]

Among the even budgets the maximum is attained at k=m−1, where it equals (m+3)/m. The odd-budget maximum is 4/m, which is smaller. This proves the matching upper bound and the theorem.

## What this corrects, and what it does not claim

The manuscript's statement that uniform retention excludes no menu is false. The corresponding Lean `retained_col_sum` identity is valid; the inference from it is the problem. `retained_constrained_eq_free` also remains valid with its hypothesis of an attaining witness meeting the prescribed trajectory. That hypothesis must be proved, and fails here for a free-optimal witness with uniform retention.

Do not confuse three protocols:

- A distribution chosen before the budget, evaluated by max_k E[r_k].
- A ranking drawn once and assessed across all budgets, evaluated by E[max_k r_k].
- A menu from which a ranking may be selected **after** the budget is known.

For the last protocol, the existing one-defect schedules give a two-element zero-regret menu: take schedules whose only bad budgets differ. At every budget one of the two is optimal. One schedule cannot suffice by the existing every-order-pays theorem. Thus the adaptive menu size on this family is exactly 2. It is not m−1. This does not contradict the separate actual-geometry χ≥5 witness, which is a different construction.

The proof above concerns constrained V_avg. It does not prove a general formula for constrained V_path. The diagnostic certificates establish V_path only for the tested m=5,...,10. Nor does this note establish literature novelty; randomized rankings with prescribed marginals are already studied, for example by Singh and Joachims (2018). The prospective contribution is this exact signed-prefix law and its parity-dependent cost.

## Lean route without search or enumeration

1. Define a finite probability space of block positions, orientation, and two label permutations. Define the resulting ranking and prove it is a bijection.
2. Prove each item's position is uniform, then sum over positions to obtain retained i k = k/m.
3. Prove the prefix-sum formulas at even and odd budgets by splitting a prefix into complete blocks plus at most one item. The expectation is a finite weighted sum.
4. For odd m, add a uniform insertion slot. Prove `insert_position_uniform` once for any distribution with uniform item-position marginals. Then prove the two conditional prefix identities.
5. The lower bounds use only budgets 1 and m−1; combine them with the constructions in the definition of the constrained optimum. No solver certificate is needed for the arbitrary-m theorem.
6. Audit the final theorem on the actual prefix-regret definition. Do not replace the construction by a table of expected regrets supplied as hypotheses.

Suggested theorem names: `even_uniform_position`, `even_expected_defect`, `insert_uniform_position`, `odd_expected_defect`, `uniform_retention_value_even`, `uniform_retention_value_odd`, `uniform_retention_price`.

## Evidence files accompanying the review

`cig_scientific_checks_20260919.json` contains rational primal and dual certificates for the finite multiset-pattern LP at m=5,...,10. Pattern distributions lift to labelled permutations by uniform relabelling within equal-weight types. The values of constrained V_avg are respectively 8/45, 1/15, 10/77, 1/24, 4/39, 1/35, agreeing with the theorem above. This is supporting finite evidence, not the universal proof.

Primary related-work reference: [Singh and Joachims, Fairness of Exposure in Rankings](https://www.cs.cornell.edu/~tj/publications/singh_joachims_18a.pdf).
