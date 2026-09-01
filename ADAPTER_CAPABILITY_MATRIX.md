# Adapter capability matrix for redesigned CIG-AMF experiments

This matrix is intentionally fail-closed. `requestable support` and
`resolved/honored support` are different scientific objects.

| Adapter | Clone | Explicit mask | Execution receipt | Pre-execution joint feasibility | Honored-support diagnostic | D6 full-product candidate | Reference/Query | Dynamic |
|---|---|---|---|---|---|---|---|
| Omni | yes | yes | verified | **not exposed** | Cartesian control only | yes, but current decision tasks are easy | limited | D0 only |
| RWARE | yes | all 5 requests | runtime verification required | **not exposed** | post-collision cancellation can be measured but is not feasible-command support | only at states/panels where every required tuple is honored | coordination/removal primitive | restricted |
| Flatland | yes | topology-dependent | not yet stable | **not exposed** | blocked until motion-resolution receipt exists | blocked until execution receipt is trusted | coordination/removal | restricted |
| CybORG | yes | heterogeneous discrete | submitted-action only | **not exposed** | no coupled-feasibility contract | claim-specific audit required | promising after receipt/query contracts | promising after learned-policy hook |
| CityFlow | yes | phase masks | applied phase receipt | **not exposed** | independent current command space | **promising**: Cartesian phases + coupled traffic response | possible | promising after learned-policy hook |

## Recommended roles

- **MASTER coupled support:** none of the current external adapters exposes a genuine pre-execution joint-feasibility oracle. Keep exact synthetic supports as theorem tests. RWARE/Flatland post-resolution probes are diagnostics only until an explicit command-admissibility contract exists.
- **D6 external:** CityFlow first; canonical Omni remains an applicability/authority sanity environment. RWARE is usable only on panels with a verified full product of honored commands.
- **QUERY external:** CybORG + RWARE/Flatland coordination states; CityFlow for control/interaction queries. MPE2 `Simple Spread` / `Simple Reference` is a good *next* package for communication/coordination, but is not added to the pinned runtime in this patch to avoid silently expanding the dependency lock.
- **DYNAMIC/F3:** defer until an adapter exposes a claim-specific learned-policy update hook.

## Canonical Omni versus modified Omni

Do **not** change canonical Omni and then call it external coupled-support evidence.
If an explicit pre-execution shared-resource constraint is added later, name it
`Omni-Coupled` and report it as a controlled synthetic stress environment.  It
can test the theorem chain but cannot substitute for a naturally constrained
external benchmark.
