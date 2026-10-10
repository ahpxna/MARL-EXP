# PROTOCOL SHIFT: the frozen TSI-2 design under a demand shift (registered 05/10 ~01:52, before any run; descriptive robustness check)

**Question:** does the two-sided interface, frozen as tuned in TSI-2 (per-light (A, B) from `tsi2_20261005/tune/choice.json`, per-light N2 one-shot, c2 tables), keep its effect when demand rises 25 %?

- **Panel:** lights t4–t8 × fleets s213–s513 × NEW traffic 740–749 generated at period 1.6 s (instead of 2.0), after a non-existence check.
- **Arms:** R, TSI2, HYB.
- Crossed bootstrap.
- **Report:** every M3 endpoint vs R at the one-sided 95 % upper. Descriptive: it is not a second confirmation of TSI-2 and does not change TSI-2's verdict.
- Runs after TSI-2 (queue 038).
