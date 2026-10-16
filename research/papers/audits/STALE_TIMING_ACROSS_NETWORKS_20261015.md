# Does the old timing hurt more when the upgrade changes the signal more? Four networks (15/10/2026, 15:37 EDT)

User: "Phân tích lại dữ liệu sẵn có, không chạy mô phỏng: so mức đèn học khác kế hoạch cũ … với mức timing cũ gây hại, trên 4 mạng."

**Type:** post-hoc and descriptive. There are only four networks, and their settings differ in several ways (see Caveats). Nothing was simulated.

**Inputs:** saved rows only. Paths outside the sparse checkout were read with `git show HEAD:` (read-only, no checkout).

**Script:** `scripts/AUDIT_stale_timing_across_networks.py`. Output: `stale_timing_across_networks_20261015.json`.

## Sources

| Network | Upgrade rows (all human) | Stale-timing pairs (old timing − no SPaT, same cells) |
|---|---|---|
| grid4 | `spat_pilot_20261004/m2/eval` OFF_FT vs OFF_RLH0–3 (fresh 470–489) | F0a / F0b × RLH0–3, naive vs labelled (labelled = σ*, 0 valid calls); 8 pairs × 20 seeds |
| spider, one lane | `m4_20261004/spider/s3/eval` OFF_FT vs OFF_RLK11 / RLK111 (fresh 1000–1019) | F0 (rule fleet), naive vs labelled; 2 pairs × 20 |
| rand3 | `w8_20261005/net3/dev` FTA vs LA_t21–25 (DEV) | NAIVE vs R, t21–25 × s213–s513; 20 pairs × 6 DEV seeds |
| Salt Lake 400S & 200W | `f1_saltlake/gateW` FT vs RLW seeds 11, 12 (DEV days) | `f1_saltlake/tsi/conf` HARM vs R, RLW t11 × s13 / s113; 2 pairs × 20 CONF days |

Notes:
- At Salt Lake, HARM serves the old FT timing through a table fitted on FT traces (q 0.5).
- On the other three networks, "naive" serves the SPaT read from the static program.

## Result

| Network | Upgrade gain (city time loss vs FT) | Mean green, FT → learned | Learned green p90 / share > 50 s | Stale timing − no SPaT: agent fuel | Agent time loss | Human time loss |
|---|---|---|---|---|---|---|
| grid4 | −33.7 s/veh (−60 %) | 42.0 → 14.9 s (**−65 %**) | 33 s / 3.5 % | **+6.95 %** [+6.12, +7.75] | +1.66 [+1.23, +2.03] | −0.24 |
| spider, one lane | −58.9 (−62 %) | 37.0 → 19.0 s (**−49 %**) | 44 s / 8.5 % | **+7.16 %** [+6.83, +7.48] | +2.71 [+2.36, +3.12] | +0.57 |
| rand3 | −54.7 (−67 %) | 42.0 → 36.1 s (−14 %) | 87 s / 23 % | +2.33 % [+2.09, +2.55] | +0.92 [+0.70, +1.14] | −0.15 |
| Salt Lake | −6.3 (−20 %) | 34.1 → 28.5 s (−16 %) | 53 s / 11 % | **−4.73 %** [−5.33, −3.89] | **+1.29** [+0.79, +2.03] | −0.31 |

Intervals are 95 % crossed bootstrap over pairs × seeds (B = 2000). A positive value means the old timing is worse than giving no SPaT.

## Reading

1. **Fuel.** The fuel harm of the old timing follows how much the learned signal changes its greens. It does not follow how much the upgrade improves traffic.
   - On the two networks where greens are shortened by half or more (grid4, spider), the old timing costs about 7 % fuel.
   - On the two where mean greens change by about 15 %, it costs +2.3 % (rand3) or still saves 4.7 % (Salt Lake).
   - rand3 is the counterexample to "upgrade size". It improves traffic as much as grid4 (−67 %), but changes mean greens little, and its harm is small.
   - With four points this is a pattern, not a law. The Spearman rank correlation between |green change| and fuel harm is 0.6.
2. **Time.** The old timing costs the fleet's vehicles time on **all four** networks, Salt Lake included: +1.29 s/veh [+0.79, +2.03], above the +0.5 limit, and comparable to grid4's +1.66.
   - So the paper's sentence that on recorded Salt Lake demand "the upgrade did not remove the benefit" is true for fuel only.
   - Against no SPaT, the stale timing there fails the joint objective on the agents' time, as on the synthetic networks.
   - TSI did not remove this time cost (TG − R +1.11 s/veh, C-216).
3. **What this means for the paper.** Salt Lake is weaker as a counterexample than the text says.
   - The fuel loss did not arise, because the learned signal there kept its greens close to the old plan (−16 %; its gain over FT is only −6.3 s/veh).
   - A time cost of the old timing did arise.
   - Two qualifiers make this a predictor, not a contradiction:
     - the fuel loss needs an upgrade that changes the green durations substantially;
     - the time cost of stale timing appeared on every network tested.

## Caveats

- **Four networks.** They differ at once in:
  - light families: two-green RL-H; keep-or-advance RLK on spider; four-green RLW at Salt Lake;
  - fleets: the PPO family on grid4 / rand3 / Salt Lake; the GLOSA rule on spider;
  - panels: fresh traffic, except rand3 DEV with 6 seeds;
  - the stale-timing implementation (see Sources).
- **Coarse measure of timing change.** Mean green ignores phase order, offsets and variability. rand3's long, variable greens (p90 87 s) also make its timing hard to forecast (W10-2b).
- **Salt Lake scale.** One site; upgrade size and greens come from two light seeds, the harm from one.
- **Different reference drivers.** The no-SPaT reference is σ\* on grid4, spider and rand3, and the R fallback at Salt Lake. Both are the fleet without SPaT.

## Suggested paper text (replaces the Salt Lake sentence in F1 and in the limitations)

> On recorded Salt Lake City demand the learned signal stayed close to the old plan (mean green −16 %, against −65 % on grid4), and the
> old timing kept the fleet's fuel benefit (−4.7 % against no SPaT) but, as on every synthetic network, cost its vehicles time
> (+1.3 s/veh [+0.8, +2.0]); TSI did not remove that cost. Across the four networks the fuel harm of the old timing grows with the
> change in green durations (+7 % where greens halve, +2 % or none where they change by about 15 %), not with the upgrade's traffic
> gain (descriptive, four networks, post hoc).
