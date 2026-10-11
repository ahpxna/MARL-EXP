# PROTOCOL TSI variants (registered 05/10 ~01:45, before any run; exploratory, separate from the frozen TSI confirmation)

**Sources:** C-113 (c2 is exact only in the "direct" yellow cell) and the user's question on left turns (grid4 lefts are permissive 'g': green, but must yield).

## Variants (adapter q:2:0 kept)

| Variant | Fleet-side service | Hypothesis |
|---|---|---|
| HYBD | c2 only for direct yellow queries; N2 elsewhere | Removes the 5–15 s yellow cells where c2 is worse than N2 |
| HYBNL | TSI, plus links whose serving green is 'g' answer `unavailable` (the fleet drives σ\* there) | A permissive-left car told "green" may still have to stop and yield; that green is not a usable timing |
| HYBDNL | both changes | — |

Implementation: `scripts/CITY_spat_forecast_n5.py` / `CITY_eval_n5.py`, copies. The frozen TSI files are not edited.

## Test

- SELECT 650–655, RL-H k0 / k1 × fleet s13.
- Compared with the existing TSI SELECT rows (`tsi_20261005/sel/T_a2_b0_k*`) and R (`n4_20261005/sel/R_k*`).

**Decision (registered):** a variant IMPROVES ON TSI iff, on SELECT, both of:
- agent TL point ≤ TSI's − 0.15;
- agent fuel point ≤ TSI's + 0.30, with city / human TL points ≤ +0.20 vs R.

An improving variant can only be confirmed in a NEW registered confirmation on reserved traffic 720–739 (lights t4–t8, fleets s213–s513, declared as re-used checkpoints). The TSI result on 700–719 is not revised.
