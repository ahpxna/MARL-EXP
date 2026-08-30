# Empirical claims outside Lean scope

Status for every item below: PENDING_DEPENDENCY (empirical evidence, not a deterministic Lean theorem).

- Learned Q scaling from 20 to 80 to 320 episodes.
- C null false-positive rate, bias, MAE, RMSE, and coverage.
- D sign accuracy, null false-positive rate, AIPW coverage, or AIPW superiority.
- The observed association (or lack of association) between the fraction of
  low-`lambdaC` relations and global C Spearman across V6 seeds.
- Whether aggregate Q RMSE/Spearman predicts extrema fidelity or global Top-C
  fidelity in learned runs.
- Correctness of natural-history versus frozen/transported AIPW in executed data pipelines.
- Episode-level cross-fitting availability and trajectory leakage diagnostics.
- OmniArena prevalence of rectangular or coupled support.
- Real-environment non-vacuity of support/certificate bounds.
- MARL return/fidelity and matched-budget Paper-B effects.
- F3 learned shadow-learner drift and moving-estimand behavior.
- Systems latency, memory, throughput, and absence of hidden quadratic candidate construction.
- Scientific novelty or paper-level prevalence claims.

Python randomized tests, exhaustive finite searches, and experiments can falsify or measure these claims but are not substituted for Lean proof.
