# Lean counterexamples and strictness witnesses — clean active state

No active flagship theorem was falsified.

## Structural response-geometry witnesses

- `W1_geometry_strictness_typed`: actual support states corresponding to `{000,011,100}` and primitive slopes `(-2,1,-3)`. Lean derives component spans `(2,1,3)`, proves `(2,0,1)` is the actual score Top-C ordering, proves scalar-prefix radius optimality for `(0,2,1)`, and proves Top-C is not exact.
- W2 `antiF`: actual response geometry where Top-C is exact at all budgets but global coextremizability fails.
- `W3_geometry_not_scalar_prefix_rankable`: actual one-hot support with slopes `(-3,-3,1)`; unique budget-one optimum `{2}` and budget-two optimum `{0,1}` are nonnested.

The old arbitrary-set-function W1/W3 lemmas are historical abstract logic only and are not used as scientific witnesses.

## Chain-A V6 witnesses

- `A11_local_stability_not_global_rank_stability`: two relations both preserve their true max/min actions and satisfy local `delta_Q^circ < g/2`, yet their estimated capacities reverse global order.
- `A13_lambdaC_half_worst_case_sharp`: for every `g>0` and `epsilon>g/2`, constructs a two-action response with true gap `g` and a perturbation of gauge error below `epsilon` that changes the maximum.
- `A14_within_relation_tie_no_positive_radius`: a tied true maximum can be broken by arbitrarily small positive gauge error.
- `A14_between_relation_tie_no_top1_radius`: tied relation scores admit arbitrarily small score perturbations changing strict Top-1 membership.

Before Chain D formalization, exhaustive binary checks over values `{-1,0,1}` for `m=2,3` found no counterexample. The compiled general theorem supersedes that finite evidence as proof.
