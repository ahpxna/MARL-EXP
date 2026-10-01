# Research audit instructions

User preference recorded 2026-09-20: every research/progress audit must inspect the existing experimental results relevant to the current research direction for algorithmic errors, as in the A7 audit. Checking Lean compilation, theorem counts, JSON summaries, or self-check success alone is insufficient.

## Required result-to-algorithm audit

- Trace each material claim from manuscript/theorem to the model, implemented algorithm, raw result, and reported statistic. Compare the actual implementation with the algorithm promised in the research plan.
- Establish which producer version generated each artifact using available hashes, freeze records, command/configuration, and seeds. If provenance is missing or mismatched, say so; do not assume current source generated an older result.
- Check information access: true parameters, hidden labels, optimal designs, extrema, and oracle answers may generate observations or serve explicitly labeled diagnostics, but must not silently enter a deployable learner.
- Inspect sampling, updates, tracking, stopping, censoring, and budget accounting. Verify adaptive queries and observations implement the stated model, and that stopping is certified in the correct direction.
- Inspect solver failure handling, skipped constraints/regions, primal versus dual bounds, numerical tolerances, clipping, regularization, degeneracies, and strict versus closed alternatives. A feasible primal objective is not a lower certificate for a minimization problem.
- Check statistical endpoints, pairing, uncertainty, censoring, selection/filtering, and comparators. Check that self-checks can actually fail and do not assume the conclusion being tested.
- Compare experiments with the theorem's actual hypotheses and quantifiers, including positive weights, fixed versus growing dimensions, known versus learned parameters, and fixed-design versus optimized-game claims.
- Distinguish a demonstrated bug from a missing guarantee, a provenance gap, an out-of-scope test, and a negative result. Give source locations and affected artifact/claim names. Do not declare an entire corpus correct after checking only a subset.
- Preserve useful existing results with accurate labels (for example, oracle-allocation diagnostic). Do not silently overwrite historical evidence or promote numerical checks into proofs.

Use existing JSON/raw results and logs first. Do not rerun experiments or recompile merely to perform an audit. If new computation is necessary, explain the specific unresolved question and the smallest useful run; follow the user's current authorization.

Report what was inspected, what supports the current research claim, what does not, concrete algorithmic findings, and the required corrections. A clean Lean axiom audit establishes the checked statements under their hypotheses, not that the implementation runs that algorithm or that all model hypotheses have been discharged.
