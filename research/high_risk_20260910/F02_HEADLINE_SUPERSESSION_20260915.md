# F02: the Functional headline, superseded

Date: 2026-09-15. **Append-only.** This supersedes the INTERPRETATION in
`NOVELTY_AND_EVIDENCE_REVIEW_20260911.md`, which stays in place as the historical record
and is not edited.

## What is withdrawn

That review is built around C_anytime: the `2.66977` ratio of medians, the `163/163`
conditional paired wins against uniform, the conditional median paired ratio `2.183147`
with interval `[2.067163, 2.324163]`, and the observation that C_anytime nearly matches
the known-sigma diagnostic. Those numbers stand as computed, but the **framing** does not:
C_anytime is not the allocator to defend, and uniform is not the comparator to defend
against.

The reason is in the review itself. Jourdan, Degenne and Kaufmann analyse empirical-variance
and transportation-cost approaches, time-uniform stopping, and the price of unknown
variance; C_anytime's near-equality with the known-sigma diagnostic is consistent with that
existing theory, so it cannot carry the novelty claim.

## What the main panel actually says

Source: `research/confirm_ieee_20260912/functional_v4_lucb_ieee10seed_cellv1.json`,
1000 paired instances. Every number below was recomputed from that artifact, not copied.

| Policy | Certify / 1000 worlds | Median queries to certificate |
|---|---|---|
| C_lucb | 797 | 20 996 |
| C_anytime | 749 | 29 884 |
| uniform | 605 | 74 252 |

Paired, head to head, recomputed from `runs_by_variant`:

| | count |
|---|---|
| both certify | 749 |
| — C_lucb strictly faster | **748** |
| — tie | 1 |
| — C_anytime strictly faster | **0** |
| only C_lucb certifies | 48 |
| only C_anytime certifies | 0 |

The artifact's own `deployable_winner_by_median_N_certificate` is `C_lucb`, with status
`IDENTIFIED_BY_MEDIAN`.

## What this is, and what it is not

This is a result **on this panel**, under this generator, at this horizon. It is **not** a
domination theorem: nothing here proves C_lucb is better than C_anytime on any other
instance distribution, and 0 losses out of 749 is an observation, not a proof.

It does, however, settle the direction of the work. Defending "C_anytime is the best
allocator" is no longer supportable, and uniform is too weak a comparator to defend a
claim against the unknown-variance literature. **C_lucb is the same-information,
same-guarantee baseline that any new allocator must beat.**

## The consequence for the research direction

The open question is not which of the existing allocators wins. It is whether solving the
alternative correctly **when the extrema move** buys anything over C_lucb. That is the F5
programme: the alternative set is a union of convex pair regions
(`LeanFunctionalRangeAlternativeUnionV1`), the energy oracle on it is a finite check with
an exact inner value (`LeanFunctionalRangeEnergyOracleV1`), the shrink and expand formulas
are the projection and the single-pair opening (`LeanFunctionalShrinkExpandV1`), and the
inner QP carries a certificate that needs no matrix inverse
(`LeanFunctionalRangeDesignCertificateV1`).

Until an oracle-based allocator is built and compared against C_lucb **on the same
information and the same cost**, no allocator claim should appear in the Functional
manuscript at all.
