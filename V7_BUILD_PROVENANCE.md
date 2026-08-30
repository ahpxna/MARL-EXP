# V7 Build Provenance

Canonical reconstruction performed before the V7 patch was written.

| Stage | Artifact | SHA-256 |
|---|---|---|
| V4 base | `cig-amf-main-chain-harness-v4-runchecked (1).zip` | `da60cf9f1e76da42806d6c044ac83d4b02bbb91a5a4dc502256f20b25b357c1a` |
| V5 patch | `CIG_AMF_OMNI_SUPPORT_V5.patch` | `0f430750e752d4499f5c70ec4402024851890a8609a1682e9c75897393e81a17` |
| V6 patch | `CIG_AMF_FUNCTIONAL_BOUNDARY_V6.patch` | `e4f712cbf86da115a484dfda30af84b0aceea9970f3e88cc9829d57fbebc900d` |
| V6 development results re-read for V7 design | `930ff2de-7e04-4ce7-8522-3878e0ef7355.zip` | `f44a5ea170df113c3e7a360ca8d9a154bdef4f9eec0fc14fd5b21cf80381351e` |

Both V5 and V6 patches were applied first with `patch --dry-run -p1` and then
with `patch -p1`; both passed on the fresh V4 tree.

The V7 patch is generated against that reconstructed V6 tree, not against an
assumed or remembered V6 snapshot.

## V6 result facts used to design V7

- 5 seeds x 3 budgets x 1,800 pair rows per budget = 5,400 pair rows.
- `lambda_C < 0.5` certified rows: 40 (ep20), 223 (ep80), 428 (ep320), 691 total.
- Certified extrema-stability violations: 0 / 691.
- Median finite `lambda_C`: approximately 1.035 -> 0.639 -> 0.447.
- The evaluation populations were not longitudinally identical.  Exact
  `oracle_range` equality for matching `(seed,state_idx,ego,neighbor)` keys was
  only about 13.8% (20 vs 80), 16.8% (80 vs 320), and 14.1% (20 vs 320).
- Therefore V7 does not interpret cross-budget phase movement unless the panel
  hash and oracle outputs are identical.
