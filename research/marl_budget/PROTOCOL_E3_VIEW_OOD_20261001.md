# EXPLORATORY: communication-view OOD beyond age (user 12:1x: fresh / relay counts, coverage, age quantiles, never-heard)

Written 01/10/2026 12:21:24 EDT (`date`), while scripts/MARL_e3_viewstats_probe.py runs and before its output is read.
Same frozen relay6Cage_st_s<s> (trained under the iid capacity process), development panel seed901–904 × 8/16, seeds 0–9,
deployment regimes iid (= the training process), const K = 1, 2, 3.  The iid deployment views are the reference for the
training distribution (approximate: training used other traffic seeds and DAgger's mixed behaviour).
Per receiver-step: fresh count, relay count, coverage (entries / audible senders), never-heard count, stale count (> 2
steps), max / mean age, fresh entries by grid distance 1–4; per cell the age histograms of fresh and relayed entries.

## Expectations stated now
- V1: the total-variation distance from iid of each marginal (fresh, relay, coverage, stale, max age) is largest at K = 1
  and decreases with K.
- V2 joint support: share of receiver-steps whose (fresh, stale, max age) cell has iid frequency < 0.1 %: > 0.5 at K = 1,
  < 0.1 at K = 3.
- V3 (reported): flip_Z (Z acceptable, relay not) by stale count and max-age bucket at K = 1; at K = 2 and 3, flip_Z inside
  vs outside the iid support.
- Reading fixed now: if fresh count and coverage are also far from iid at K = 1, "age OOD" is too narrow and the regime is
  a composition shift (sparse + stale + relay-heavy); the age-clip counterfactual (age only) bounds what age alone explains.
