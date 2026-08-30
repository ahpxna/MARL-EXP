# Adapter capability matrix for redesigned CIG-AMF experiments

This matrix is intentionally fail-closed. `requestable support` and
`resolved/honored support` are different scientific objects.

| Adapter | Clone | Explicit mask | Execution receipt | Coupled support candidate | D6 full-product candidate | Reference/Query | Dynamic |
|---|---|---|---|---|---|---|---|
| Omni | yes | yes | verified | **no** in canonical Omni | yes, but current decision tasks are easy | limited | D0 only |
| RWARE | yes | all 5 requests | **new resolved-action receipt** | **promising for honored support** because conflicts may cancel requests | only at states/panels where every required tuple is honored | good coordination/removal primitive | restricted |
| Flatland | yes | topology-dependent | not yet stable in adapter | promising, but must expose motion-resolution receipt first | blocked until execution receipt is trusted | coordination/removal | restricted |
| CybORG | yes | heterogeneous discrete | submitted-action receipt only | no current coupled-feasibility contract | claim-specific audit required | **promising for reference/query** | promising after learned-policy hook |
| CityFlow | yes | phase masks | applied phase receipt | no current coupled command constraint | **promising**: independent phase tuple + dynamically coupled traffic response | promising | promising after learned-policy hook |

## Recommended roles

- **MASTER coupled support:** synthetic exact supports + RWARE honored-support probe if runtime enumeration finds non-Cartesian resolved support. Flatland is second choice after movement-resolution telemetry is instrumented.
- **D6 external:** CityFlow first; canonical Omni remains an applicability/authority sanity environment. RWARE is usable only on panels with a verified full product of honored commands.
- **QUERY external:** CybORG + RWARE/Flatland coordination states; CityFlow for control/interaction queries. MPE2 `Simple Spread` / `Simple Reference` is a good *next* package for communication/coordination, but is not added to the pinned runtime in this patch to avoid silently expanding the dependency lock.
- **DYNAMIC/F3:** defer until an adapter exposes a claim-specific learned-policy update hook.

## Canonical Omni versus modified Omni

Do **not** change canonical Omni and then call it external coupled-support evidence.
If an explicit pre-execution shared-resource constraint is added later, name it
`Omni-Coupled` and report it as a controlled synthetic stress environment.  It
can test the theorem chain but cannot substitute for a naturally constrained
external benchmark.
