# Auxiliary programmes status — clean final state

| Programme | Target theorem | Status | Source / theorem | Exit | Scientific scope |
|---|---|---|---|---:|---|
| BH6 | global E domination; cardinality E/2 | LEAN_VERIFIED | `LeanAuxiliaryBH6StructuralV4`: `BH6_*` | 0 | actual support radius |
| Structural | modularity → Top-C | LEAN_VERIFIED | `S2_*` | 0 | actual cardinality Top-C |
| Structural | coextremizable ↔ modular | LEAN_VERIFIED | `S3_global_coextremizable_iff_all_subsets_modular` | 0 | finite nonempty support |
| Structural W1 | scalar-prefix ⇏ Top-C | LEAN_VERIFIED | `W1_geometry_strictness_typed` | 0 | actual primitive/support world and actual score TopK |
| Structural W2 | Top-C ⇏ coextremizable | LEAN_VERIFIED | actual `antiF` witness | 0 | actual primitive/support world |
| Structural W3 | nonnested optima ⇒ no scalar prefix | LEAN_VERIFIED | `W3_geometry_not_scalar_prefix_rankable` | 0 | actual primitive/support world |
| Chain D | product surrogate `(m-1) delta_square` | LEAN_VERIFIED | `D3_product_surrogate_mixed_difference_bound` | 0 | normalized product weights |
| Chain D bridge | world sup-error → compression-objective error | LEAN_VERIFIED | `compressionLoss_uniform_world_transfer`, `D4_product_compression_objective_perturbation` | 0 | actual oscillation/minimax scalar compression objective |
| Chain D decision | `L_F(S_C) ≤ min L_F + 2(m-1)delta_square` | LEAN_VERIFIED | `D5_product_compression_decision_regret` | 0 | actual product responses, actual compression loss, finite cardinality optimum |
| Chain D Top-C | Top-C minimizes `A_q` compression | LEAN_VERIFIED | `productA_compression_loss_formula`, `productA_topC_surrogate_optimal` | 0 | full Cartesian support gives exact modular omitted-span formula |
| Chain D literal route | Top-C true regret `≤ 2(m-1)delta_square` | LEAN_VERIFIED | `D6_product_topC_compression_decision_regret` | 0 | no external `hSurrogateOptimal` |
| Chain A split | selected-contrast expectation | LEAN_VERIFIED | `A5_split_estimator_targets_selected_contrast` | 0 | finite deterministic analogue |
| Chain A Neyman | continuous allocation | LEAN_VERIFIED | `A6_continuous_neyman_optimal` | 0 | positive interior; zero boundary recorded |
| Query E | removal witness | LEAN_VERIFIED | `E5`, `E6` | 0 | exact finite witness |
| A8 | gauge Q-error → C-error | LEAN_VERIFIED | `A8_gauge_capacity_bound` | 0 | exact deterministic oscillation |
| A9 | between-relation order / Top-K | LEAN_VERIFIED | `A9_pair_order_preserved`, `A9_per_relation_topK_membership` | 0 | score margin |
| A10 | Q-error → global Top-C | LEAN_VERIFIED | `A10_Q_error_topK_membership` | 0 | gauge error plus capacity margin |
| A11 | local stable ⇏ global rank stable | LEAN_VERIFIED | `A11_*` | 0 | exact two-relation response witness |
| A12 | zero-sum gauge D bound | LEAN_VERIFIED | `A12_zero_sum_gauge_direction_bound` | 0 | `sum w = 0` gives exact gauge invariance |
| A12 | lambda-D sign margin | LEAN_VERIFIED | `A12_lambdaD_lt_one_sign_stable` | 0 | `D ≠ 0`; direction, not magnitude rank |
| A13 | lambda-C half sharpness | LEAN_VERIFIED | `A13_lambdaC_half_worst_case_sharp` | 0 | constructive Fin-2 worst case |
| A14 | within/between tie impossibility | LEAN_VERIFIED | both `A14_*` theorems | 0 | arbitrarily small perturbations |

No auxiliary result invalidated an assumption of the frozen Operational MASTER.
