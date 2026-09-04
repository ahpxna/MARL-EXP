# D6 normalized balanced target: exact non-strict counterexample

Status: **FALSIFIED for the current non-strict statement**.

`LeanD6NormalizedBalancedTernaryCounterexampleV1.lean` is a quarantined P13
counterexample module.  It does not modify P12 or any legacy theorem source.

## Exact compiled witness

- Coordinates: `Fin 4`; actions: `Fin 3`.
- Reference: normalized point mass at the all-zero joint action.
- Selected set: `{0, 2}`; competitor: `{1, 3}`.
- Every first-order response span is exactly `1`, so the selected set is a
  valid **non-strict** Top-2 set under the current `IsTopKByScore` semantics.
- The world satisfies `UnitInteractionBound`.
- Exact losses are `5 / 2` for the selected set and `1 / 2` for the
  competitor.  Therefore the doubled decision gap is `4`, while `m - 1 = 3`.

The module proves:

```lean
ternaryBalancedCell4_not_atMost_three
exists_normalized_balanced_cell_violating_m_minus_one
normalizedBalancedDecisionInteractionBound_type0_false
```

Consequently, the existing proposition
`NormalizedBalancedDecisionInteractionBound` cannot be proved under its
current non-strict active-cell/Top-C assumptions.  The universal balanced
cone/tree/certificate-completion route is stopped for that proposition.

## Scope discipline

This witness has tied response spans.  It does **not** prove or disprove a
future strict-margin version, because that would be a materially stronger
assumption and must be stated, searched, and formalized separately.  No such
replacement has been promoted here.

## Verification

Pinned Lean 4.34.0-rc2 compile exited `0` on 2026-09-03.  The source contains
no `sorry`, `admit`, or user `axiom`.  The compile log is
`compile_logs/LeanD6NormalizedBalancedTernaryCounterexampleV1.log`.
