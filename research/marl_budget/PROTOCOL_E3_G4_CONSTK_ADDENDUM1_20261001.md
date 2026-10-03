# Addendum 1 to PROTOCOL_E3_G4_CONSTK_20261001: a cross-system staleness-burden threshold (G5) and per-step burdens

Written 01/10/2026 14:54:52 EDT (`date`).  No 4×4 const-K run exists (the launcher has not started; the 4×4 chain is still
training).  Trigger: user 14:0x — "is the critical variable the tail staleness exposure rather than literal K?"  3×3 values used to
fix the threshold (already read): B_stale = E[Σ_j (a_j − τ)+] with τ = 3 (the iid 99th percentile of the maximum copy age)
8.48 / 1.64 / 0 / 0 at K = 1 / 2 / 3 / iid, gains −1.6 / +1.0 / +1.7 / +2.1 %; decision-level age-clip gain +0.030 / 0 / 0 / 0.

## Change of instrument (before any run)
scripts/RUN_marl_g4_constk.sh uses scripts/MARL_e3_viewstats_probe_v2.py instead of v1: identical closed loop, flags and
parity checks (smoke: every v1 field byte-identical on s0 / K = 1; b3 mean 8.48 = the histogram-based B_stale) plus per-step
b2, b3.  B_stale on 4×4 uses τ_s = the iid 99th percentile of seed s's maximum copy age (as the protocol), computed from
the per-step burdens.

## Added rule (secondary)
- G5 threshold: with b* = 3.7 (the geometric mean of 3×3's 1.64 and 8.48, fixed now), for every K ∈ {1, 2, 3, iid} on 4×4,
  mean target gain(K) < 0 exactly when the development mean B_stale(K) > b*.  Reported with the K-only reading
  ("K = 1 loses, K ≥ 2 wins"): if they disagree on some K, G5 decides which variable organises the 4×4 cells.
- Reported (no rule): the exposure–response curve P(flip_Z | b3) on 3×3 and 4×4.
