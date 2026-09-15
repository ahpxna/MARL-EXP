# Provenance and evidence-class ledger — 5 September 2026, addendum B

Append-only. This does not edit `PROVENANCE_AND_EVIDENCE_CLASS_20260905.md`; it
records the transitions that occurred after it was written. Where a line in the
earlier file is now stale, the stale line is quoted and struck rather than deleted.

## D6

### Centered RankOne/two-profile strict counterexample — PROMOTED

Earlier ledger line, now stale:

> ~~Critical non-promotion: `LeanD6StrictTwoProfileRankOneM6CounterexampleV2.lean`
> is present but the current audited extraction contains no matching `.olean`.
> Therefore the addendum does not label the centered rescue `PROVED FALSE` in Lean.~~

**Reason for the transition.** The module now compiles. `.olean` 28,733,696 bytes,
newer than its `.lean`; 0 `sorry`/`admit`; `AxiomAuditD6FalsificationV1.lean`
audits 16 theorems and every one reports `[propext, Classical.choice, Quot.sound]`.

**Class:** `EXACT_RATIONAL_COUNTEREXAMPLE_INDEPENDENTLY_RECOMPUTED`
→ **`PROVED_FALSE_LEAN4_AXIOM_AUDITED`**.

**Refuted:** `RankOneDecisionInteractionConstantAtMost witnessCell 5`, i.e.
`AllCoordinatesInteractionContrastRankOne`$(q,F)$ does not imply
$2D\le(m-1)\delta_\square$, at $m=6$, $K=3$, corner reference.

**Non-vacuity.** Nine of the sixteen audited theorems are D6's own hypotheses,
proved for the witness: nonnegative normalised product reference,
`UnitInteractionBound`, all-coordinates centred rank one, at most two profiles,
**strict** Top-C, balanced complement, `Valid` cell, and membership in the class
the law quantifies over.

**Non-claims.** $m=6$, $K=3$, corner reference only. Says nothing about D6-prime.
Does not touch `D6.world_approximation`, `D6.symmetric_difference`, or the
quarantined half-factor `sorry`.

**Artifact:** `research/d6_contrast_rank_falsification/D6_CENTRED_RANKONE_PROVED_FALSE_20260905.json`.

### Raw local contrast route — unchanged class, corrected framing

The earlier ledger's class (PROVED for the statements the modules carry) and its
scope boundary (all-coordinate-active hypothesis; reverse fibre inclusion open)
are **both correct and unchanged**.

One framing correction, recorded as an erratum against
`RAW_RANKONE_NORMAL_FORM_PROVED_20260905.json`:

> ~~The normal form serves as an exhaustiveness certificate for the fibre search.~~

**Reason.** What is proved is that for each $\phi$ the raw-rank-one worlds form
exactly a linear subspace of dimension $2^m$, plus one-way coverage of the active
stratum. The search enumerates a finite rational grid of $\phi$, so coverage in
$\phi$ is a sampling argument. **Replacement:** the normal form makes the fibre
*parameterisation* exact; it does not make the *search* exhaustive.

### D6-prime — OPEN, with first matched-budget countersearch

**Class:** OPEN. **Evidence class of the campaign:**
`NUMERICAL_AB_COMPARISON_WITH_POSITIVE_CONTROL`.

Identical script, seed, corner, fibre count, optimizer, snapping and StrictTopC
gate; the only difference is `--fiber-kind`. The centred control **must** kill and
does, reproducing `B3small_m6_d16_s13` to the digit ($1.161111322576584$). Across
six paired cells (seeds 1, 2 × denominators 4, 8, 16): raw 0/6 killed, max
$0.8903$; centred 4/6 killed, max $1.0913$; raw below centred in **6 of 6**.

**Non-claims.** Lower-bound search, path dependent. The raw ceiling **has not
saturated** — it rises monotonically with the $\lambda$-grid denominator, so
$0.8903$ is not a limit. The search's exact recheck verifies *centred* rank one,
not raw. One corner, two seeds.

### New exact structural measurement

$\dim V^{\rm raw}_\phi = 2^m$ against $\dim V_\lambda = 1+m(K-1)+(2^m-1-m)$;
codimension $m(K-2)$. Verified by exact rank over $\mathbb{Q}$ at
$(m,K) = (4,3), (6,2), (6,3)$: $16/20$, $64/64$, $64/70$. The $K=2$ row is
`binary ⇒ raw` from the dimension side. **Class:** EXACT_RATIONAL_VERIFICATION.

### Corpus-wide misalignment annotation

72 witness records, witness-free per-coordinate raw rank, decision layer
recomputed **per witness** in exact rationals. Findings: centred rank one holds at
every coordinate of every recorded witness (0 violations, an independent
confirmation of the corpus); **14 of 14 violating witnesses have at least one
misaligned coordinate**; the sole non-misaligned witness is the binary one.
**Class:** EXACT_RATIONAL_DERIVED_ANNOTATION.

### Demoted this session

| claim | disposition | reason |
|---|---|---|
| ~~$2D \le (m-1)\delta + c\,n_{\rm mis}\,\delta$~~ | DEMOTED | fitted envelope; monotone at the envelope but $n{=}6$ spans $-2.197$ to $+0.762$; biased sample; no tight cell |
| ~~raw fibre makes Top-C ties generic~~ | KILLED | measured tie rate flat, $0.2608 \to 0.2650$ across the raw→centred interpolation, optimizer-free design |
| ~~$\mu = 0 \iff$ raw rank one~~ | DEMOTED to $\Leftarrow$ | equivalence needs $h_i$ non-constant; the $\Leftarrow$ direction is unconditional and proved |
| ~~raw best ratio $= 0.9585$~~ | DEMOTED | `--snap both` projection can leave $V^{\rm raw}_\phi$; clean runs $\le 0.8903$. Confounded by seed; clean seed-13 test open |

## Structural

No change. `LeanStructuralStaircaseExactPrefixCoverV1` remains PROVED with
$\chi_{\rm prefix}(F_r,0) = r$; the `(hr : 0 < r)` hypothesis is load-bearing
because `card_eq_two_mul_sub_one_radius` is false at $r=0$ in $\mathbb{N}$.

## Dependency hygiene

`RankOneDecisionInteractionConstantAtMost` is used as a hypothesis in **zero**
theorems corpus-wide; it appears only in its own definition module and in the
counterexample refuting it. The falsification produces **no downstream rot**.

## Literature boundary — additions

- Owen (1972), *Multilinear Extensions of Games* — already listed; now the direct
  boundary for the corner reconstruction formula used in the raw normal form.
- Rota (1964) / Harsanyi (1963) — already listed; the boundary for the monomial
  (Möbius/dividend) form. The span-membership route was chosen for Lean cost, not
  to claim novelty over these.
- Attributions in this and the previous ledger are **recalled, not verified against
  the literature**. They must be checked before any citation is published.
