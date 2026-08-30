# Immutable Baseline Integrity

Baseline archive:

`cig_amf_lean_v6_chain_d6_topc_final.zip`

Archive SHA256:

`6872c8975be8a55de6f11c7cb6cf9aaa5fa85fe6c39958f5f5ae6d57bb44036a`

Pinned environment:

- Lean `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`;
- Mathlib `1f495c611d05d2215058cd77c7897d625bc3b445`;
- 14 active baseline modules;
- 199 baseline theorem declarations;
- baseline `sorry=0`, `admit=0`, user `axiom=0`.

All 14 repository baseline sources were compared byte-for-byte with the supplied archive before extension work. No differences were found. The fresh source-to-olean build in `ACTIVE_COMPILE_RESULTS_V7.tsv` records exit code 0 for all 14 modules and for the four previously requested V7 extensions.

The high-value work is contained only in new extension modules. `LeanUnifiedChainsV2.lean` is historical and excluded from every active build.
