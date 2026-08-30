# Lean execution ledger — clean active state

Environment: Lean `4.34.0-rc2` (`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Mathlib commit `1f495c611d05d2215058cd77c7897d625bc3b445`, arm64 macOS. Compilation used the recorded Mathlib `LEAN_PATH` and explicit `lean -o <module>.olean <module>.lean` commands.

## Fresh active-source build

| Source | Exit | Status | SHA256 |
|---|---:|---|---|
| `LeanSupportGeometryV4.lean` | 0 | LEAN_VERIFIED | `d08301e3e7fe1df43d2cc000614b11f2a6b21d5e1d0370c6598ed5af005041d9` |
| `LeanReferenceKernelV4.lean` | 0 | LEAN_VERIFIED | `d09440c830a25d0721d3805ce41ff189b208c7d0cd6cfb9c2e6843d8848b8a13` |
| `LeanReferenceFidelityV4.lean` | 0 | LEAN_VERIFIED | `14ef3b93bbdf3eaa1759e7004a32ba98e1e5cd91279d39043a0208f49e18d901` |
| `LeanPairwiseMasterV4.lean` | 0 | LEAN_VERIFIED | `52c07444cd17e0f0707eee060a8b6f268d854697e514895c13af3f0301344b0e` |
| `LeanFunctionalBoundaryV4.lean` | 0 | LEAN_VERIFIED | `9c53dceb131625f82e6dd78441d35236db00fb3edbe62e07fb328944a274b50d` |
| `LeanStructuralRankabilityV4.lean` | 0 | LEAN_VERIFIED | `ea3f8323856c67ba0820c7f8864a9a98f7fff72f078d93a2ae5817c203bee3a0` |
| `LeanProductSurrogateV4.lean` | 0 | LEAN_VERIFIED | `94887a7f8f9112973a6a0de7d2a559c34ad2d4bd3f129401136430138ec58cd9` |
| `LeanQuerySufficiencyV4.lean` | 0 | LEAN_VERIFIED | `4cd2473bc33b2f784cf18a69823611ac15493ca0be38f7275191a2b71b335836` |
| `LeanAuxiliaryBH6StructuralV4.lean` | 0 | LEAN_VERIFIED | `a0e2510c5e39fa9b3d16489b0c132c904c768d8142eacc02689f04fb49888a04` |
| `LeanStructuralGeometryWitnessesV4.lean` | 0 | LEAN_VERIFIED | `9aa682d6386aba6ce62d7c43802fba1273dcd6a01d36a289cdcc9f5961c4c124` |
| `LeanFunctionalAuxV4.lean` | 0 | LEAN_VERIFIED | `2449f04ce37ae199a0e2794e56e5ce0caf5b1f6c5aaf1304c4863942bf7976fd` |
| `LeanProductMixedDifferenceV4.lean` | 0 | LEAN_VERIFIED | `8d362429b4757c70a796ae53de88e531eff850d07941cef81d9dca8671a87037` |
| `LeanQueryRemovalV4.lean` | 0 | LEAN_VERIFIED | `0fac1e36c3feb47c5e3ef3995da21161d8e91ce7f4f037d66edc8a70d0779c29` |
| `LeanFunctionalRankingV6.lean` | 0 | LEAN_VERIFIED | `3e9ad55922e8eb7cb4b0d71e0c3b79725124bf50fcf1b4521ff3e79d1e2aea65` |

Active V4/V6 sources contain 199 named theorems. Static scan: `sorry=0`, `admit=0`, user `axiom=0`.

## Programme results

| Programme | Status | Principal compiled theorem(s) |
|---|---|---|
| Frozen Operational MASTER | LEAN_VERIFIED | `FULLY_INSTANTIATED_OPERATIONAL_MASTER` |
| BH1–BH6, finite zeta/Delta, CERT, support brackets | LEAN_VERIFIED | `BH6_deficit_le_globalE`, `BH6_cardinality_topC_global_E_half` and dependencies |
| R_iso finite kernel, TV, RF1 | LEAN_VERIFIED | Reference kernel/fidelity V4 modules |
| Structural equivalence and actual strictness | LEAN_VERIFIED | `S3_global_coextremizable_iff_all_subsets_modular`, `W1_geometry_strictness_typed`, W2, `W3_geometry_not_scalar_prefix_rankable` |
| Product-surrogate Top-C compression decision route | LEAN_VERIFIED | D3, actual compression bridge, `productA_topC_surrogate_optimal`, `D6_product_topC_compression_decision_regret` |
| Split selected contrast / continuous Neyman | LEAN_VERIFIED | `A5_split_estimator_targets_selected_contrast`, `A6_continuous_neyman_optimal` |
| Query E including removal | LEAN_VERIFIED | Query V4 modules |
| Chain-A V6 two-margin and zero-sum direction package | LEAN_VERIFIED | A8–A14, `A12_zero_sum_gauge_direction_bound`, `A12_lambdaD_lt_one_sign_stable` |

`LeanUnifiedChainsV2.lean` is a historical superseded scratch file, not an active V4/V6 dependency. Its fresh compile exits `1`; it is explicitly excluded from verified active sources rather than hidden or composed into the active chain.
