# PROTOCOL GEN: how far does the two-sided interface generalize? (registered 05/10 ~02:00, before any run; descriptive tests that bound the claims)

**Design frozen from TSI-2:** per-light (A, B) (`tsi2_20261005/tune/choice.json`), per-light N2 one-shot, hybrid q0.5, c2 tables.

**Traffic:** fresh 750–759 (10 seeds, period 2.0; non-existence check). **Lights:** t4–t8. Crossed bootstrap. Every arm vs R on the same lights / fleet class / traffic.

| Test | Arms | Question → registered reading |
|---|---|---|
| (a) receiver class | rule R8 (`RULE0_fleet.pt`), search R9 (`theta_s2`, `theta_s3`) × {R, TSI2, HYB} | "The interface helps every frozen receiver class we have" iff TSI2 vs R has agent fuel upper < 0 for each class; the M3 limits are reported per class |
| (b) state model needed? | R10 s213–s513 × {R, TSI2, C2Q = c2 q0.5 + the same adapter} | "The state forecaster is necessary" iff TSI2 − C2Q has agent fuel upper < 0 |
| (c) penetration | R10 s213 / s313 × {R, TSI2} at fleet share ρ 0.25 and 0.75 (wrapper `CITY_rho_run.py`; the forecaster was fitted at ρ 0.5) | "Robust to penetration" iff TSI2 vs R has agent fuel upper < 0 at both ρ; TL reported |
| (d) H-PATH upgrade order | old light FT + program SPaT × {R10 s213–s513, F1-B fleets} | "Fleet-first is safe under the old light" iff F1B − R10 (FT) agent fuel upper < +0.5 % and agent TL upper < +0.5; else fleet-first is harmful |

Descriptive; none of these is a second confirmation of TSI-2.
