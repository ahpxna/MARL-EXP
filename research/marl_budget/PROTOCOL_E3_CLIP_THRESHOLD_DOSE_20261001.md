# EXPLORATORY: decision-level age-clip dose over the clip threshold A (3×3, const K = 1, development panel)

Written 01/10/2026 19:00:15 EDT, before the runs.  scripts/MARL_e3_age_cf_probe.py --A a for a ∈ {3, 5, 7} (A = 2 exists:
acc 0.848 → clip 0.878).  Under iid training the maximum copy age never exceeds 3 (p99 3).
Prediction of the relative (training-support) reading: recovery(A = 3) ≈ recovery(A = 2) (+0.03); recovery(A = 5) clearly
smaller (< +0.015); recovery(A = 7) ≈ 0 (< +0.005).  If recovery stays large at A = 5–7, the failure is not "beyond the
training range" but a smooth age sensitivity.
