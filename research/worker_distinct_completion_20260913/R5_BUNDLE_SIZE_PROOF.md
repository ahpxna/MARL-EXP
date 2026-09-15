# R5 — bundle size for evidence acquisition

Module `LeanSupportParityBundleSizeV1`, receipt
`work/p13_conjectures/LeanSupportParityBundleSizeV1.compile.receipt.json`:
`lean_exit=0 errors=0 audited_names=14 nonstandard_axioms={} accepted=true`
(source sha256 `bc23be7aedc1c012bdadb1f1b7125b782a54e48a2ba64278f751ffea4c230710`).
Probe `scripts/R5_bundle_size_separation.py` -> `R5_bundle_size_separation.json`,
15793 exact checks, mutation-tested.

## Headline (this is the research claim, not XOR)

Bundle size — the number of evidence items that must be acquired TOGETHER before
any of them moves the decision — is a property of how the danger region sits
relative to the query class, not of the query primitive. The primitive is the
same physical membership test in both halves.

| geometry | danger region of a decision | bundle size |
|---|---|---|
| multi-tip | one tip | 1 (PROVED) |
| interval membership | an interval | 1 (NUMERICAL, n<=7) |
| laminar / dyadic | a dyadic block | 1 (NUMERICAL, n in {4,8}) |
| parity on d aux tips | a parity class | exactly d (PROVED) |

## PROVED (Lean, standard axioms only)

1. `radius_indicator` / `loss_indicator` — the radius bridge, derived from
   `radius_formula`, NOT assumed:
   `(2/((d:R)+1)) * selectedRadius (components (Wof S)) {decIdx b} = if b != par S then 1 else 0`.
2. `par_flipAt`, `flipAt_involutive`, `mem_flipAt_of_ne` — the bit-flip involution.
3. `adaptive_balanced` — FULLY ADAPTIVE posterior pairing. Hypotheses retained:
   `0 < d`; `Transcript Q g` (the queried set and the answer depend on the world
   only through answers already received); `(Q S)^c` nonempty for every `S`
   (i.e. not all d bits are queried, and no direct query is in the transcript,
   since `Q S : Finset (Fin d)` ranges over auxiliary bits only). Conclusion:
   `2 * #{S | g S != par S} = 2^d`.
4. `adaptive_risk_half` — the same in the actual normalised radius:
   `2 * sum_S loss S (g S) = (2:R)^d`.
5. `bundle_risk_half` (fixed bundle, `Q.card < d`), `single_bit_gain_zero`
   (one-step greedy gain of any single bit is 0, `1 < d`).
6. `parity_bundle_insufficient` (`Q.card < d` never determines the parity),
   `parity_determined_by_all` (all d bits do), `parity_decision_zero_loss`.
7. `greedy_ratio_unbounded` — `M/d` is unbounded over `M >= d`.
8. `multitip_single_query_determines`, `multitip_single_query_certifies` —
   bundle size 1 against the same `selectedRadius`.

## NUMERICAL EVIDENCE (exact fractions, not proved)

- Raw max-min recomputation of the bridge from the actual support points, d<=8.
- Every bundle of every size, d<=8: fibers split evenly below d, risk 1/2.
- Bundle sizes of the interval and laminar geometries (search capped at k<=2,
  which suffices because k=1 already succeeds).
- Hard-budget cliff `R*(B) = 1/2` for `B < min(d,M)`, `0` otherwise: full-state
  Bellman DP, d<=5 here, d<=6 in `parity_bundle_probe.json`, symmetry-reduced
  to d<=10 there.
- Greedy: risk-per-cost pays M, decision-entropy-per-cost pays M, WORLD-entropy
  -per-cost pays d = optimum. d<=6, M in {d+1, 2d, d^2+1}, M>1.

## What this does NOT establish

- No probability space, measure, or expectation is formalised. "Uniform prior"
  is counting; "risk 1/2" is `2 * #errors = 2^d`.
- COST is not in Lean. The budget B, the unit auxiliary cost and the direct cost
  M appear only as the hypotheses `Q S : Finset (Fin d)` and `(Q S)^c` nonempty.
  The value function `R*(B)` itself is numerical only.
- `Transcript` is a hypothesis, not a construction: no decision tree is built,
  and strategies that peek at the world are not covered.
- "Greedy fails" is FALSE as a general statement and is not claimed. Only
  risk-per-cost and decision-entropy-per-cost overspend by M/d; world-entropy
  acquisition is optimal on this instance.
- The multi-tip half proves one query DETERMINES safety of one decision; it does
  not quantify risk reduction under any prior. The dense-family gain 1/m is
  numerical.
- Interval and laminar bundle size 1 is numerical only — not formalised.
- Novelty: the XOR/parity instance is a benchmark (cf. Krause-Guestrin 2005 for
  information gain, Feige et al. 1994 for noisy parity). The new content is the
  separation table above and the adaptive pairing under an explicit
  transcript-measurability hypothesis.
