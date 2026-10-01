# E3 DIRECTION (b) PROTOCOL — DRAFT, NOT FROZEN (29/09/2026, 18:11 EDT, clock-checked)

Scope: decision-aware truncation of the prefix stream, i.e. send FEWER bytes than the prefix while keeping waiting.
- This draft freezes nothing.
- Seeds 1301–1316 stay closed (as in `PROTOCOL_E3_FINAL_DRAFT_20260928.md`).
- The endpoint type is the authors' decision.  This draft proposes endpoint type (b) of that draft:
  non-inferiority within a PRE-SET margin at fewer bytes.
- It becomes a protocol only when the authors accept it and a dated FROZEN copy with its sha256 is written.
- Selection rules below were written BEFORE the v3 development results (`e3_truncation_cl_v3_20260929`) were seen.

## 1. Actors
- The 11 learned actors of the development runs: scratch rs s0/s1/s2/s4 and scratch s3; BC s0–s4; mix s3.
- Each is its `ckpt_best.pt`, sha256 recorded at freeze.
- All are reported.  Families (scratch / BC / mix) are reported separately; no family is dropped after the test.

## 2. Methods (same frozen actor; runtime `scripts/MARL_e3_truncation_closed_loop_v2.py` with its self-checks)
| rule | role |
|---|---|
| prefix | reference |
| `proxyage_<s*>`: receiver proxy with staleness bound s* (1-byte report per receiver, 10 B/step charged) | proposed |
| `proxy` (no staleness bound) | ablation (the future-cache effect) |
| `cap_<c>` for c = 5, 6, 7 (blind stream caps) | same-byte comparator curve |
| `tmc_4` (sender-side "send only if changed", Zhang et al. 2020 style) | literature comparator |
| budget-matched actor: `cap6` training (`MARL_e3_actor_train_delivery_v2.py`), run under cap 6 | strongest same-byte comparator (if its training finishes and passes its own select check) |
| `exact_local` and the H = end zero-loss oracle (`MARL_e3_zero_loss_truncation.py`) | diagnostics, not deployable |

## 3. Choice of s* (declared before v3 was seen; development data only)
- Grid s ∈ {40, 50, 60, 80, 100, 150} seconds.
- On the v3 development panel (seeds 901–964 × 8/16, 128 episodes per actor), per family, s* is the value with the
  LARGEST pooled bytes saved such that the pooled development upper 95 % bootstrap bound of the waiting change is
  below +1.0 %.
- If no s qualifies, the family's method is the prefix itself: it saves nothing and is reported as such.

## 4. Endpoints
- Primary (non-inferiority): per family, the paired episode waiting change of `proxyage_<s*>` against the same actor's
  prefix.  Two-level bootstrap: actors, then traffic seeds, with both loads of a seed kept together.
  The upper 95 % bound must be below +1.0 %.  Bytes saved are reported with it.
- Secondary (superiority at the same bytes): the waiting change of `proxyage_<s*>` minus the blind cap curve
  interpolated at its saving, and minus `tmc_4`, paired, with the same bootstrap.
- A CI containing 0 is never read as equivalence; only the pre-set +1.0 % margin is.
- Guardrails:
  - finished trips and unfinished trips;
  - the first-divergence step (the legal rules have NO identity guarantee;
    `LeanMarlDecisionCertificateV1` covers only the exact oracle's certificate).

## 5. Panel
- Traffic seeds 1301–1316 × headways 8 and 16 (32 episodes), iid capacities.
- If the authors want the development power (128 episodes), a new closed seed block must be declared here before
  freezing.  32 episodes gave ±2 % CIs in development, which is too wide for a ±1 % margin.

## 6. Known limits (to be stated in any write-up)
- The legal rules check the CURRENT decision with a proxy (cached content marked fresh), plus a staleness bound.
  They do not certify the future.  Exact decision-preserving savings are known only from the oracle.
- The staleness bounds 40/60 in v2 were set after a one-episode smoke at 20/30 saved nothing.
- Development evidence so far: L-94 … L-99 of `research/papers/audits/MARL_SELF_AUDIT_LEDGER_20260928.md`.
