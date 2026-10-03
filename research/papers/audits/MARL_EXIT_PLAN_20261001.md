# MARL / E3 — the way out (01/10/2026 16:0x EDT; synthesis of L-200 … L-213, updated as results land)

## Candidate claim (one sentence)
A learned receiver that could always fall back to compiled silence (its input contains the silent student's) still loses to
silence when a structural channel regime puts its communication view outside the training range; the loss is a
compatibility failure, not missing information — it is visible at the decision level against the silent comparator,
organised by a stale-tail dose variable, reduced by a representation-only intervention and (pending) removed by matched
training or by a silence-fallback gate keyed on the receiver's own view.

## Evidence map
| Link | Evidence | Status |
|---|---|---|
| Silence is in the relay's policy class | architecture check + relay net with Z weights and φ ≡ 0 reproduces Z 8/8 (K = 1, iid) | ✅ verified |
| Optimal value is information-monotone | bayes_refine (single decision, Lean); team nesting (ignore messages) | ✅ (decision-level Lean) |
| Imitation optimum is NOT information-monotone | LeanMarlImitationGapV1.imitation_gap (3-world instance; agreement 7/10 → 4/5, unacceptable 0 → 1/5) | ✅ compiled, standard axioms (gate pending) |
| Sign reversal at const K = 1 | −1.65 / −1.45 / −1.70 % on panels 2801 / 3001 / 3101 (CIs exclude 0) | ✅ replicated 3× |
| Decision-level signature vs Z | net_Z −0.026 at K = 1 (10/10 seeds), + at K = 2, 3, iid; Z parity full | ✅ exploratory |
| Dose variable | stale-tail burden B_stale 8.48 / 1.64 / 0 (K = 1 / 2 / 3); CORRECTED (artifact agent, verified): at constant K b3 is a deterministic function of (K, t), so the exposure–response curve is a BETWEEN-regime contrast plus the early K = 1 ramp; within K = 1 late steps the slope is flat (0.0013 per unit [−0.004, +0.0065]); clip-threshold dose graded, not a step: decision recovery +0.030 / +0.017 / +0.006 / +0.001 at A = 2 / 3 / 5 / 7 | ⚠️ between-regime only |
| Age-interface repair (closed loop) | clip +0.79 % [+0.05, +1.55] at K = 1, neutral at iid; roughly half of the gap | ✅ prospective (A1, A3) |
| Second component | early-episode sparse coverage (flip 0.062 vs 0.011, never-heard 5.5); per-seed σ_early ↔ residual after clip ρ +0.49, σ_tail ↔ clip effect ρ +0.77 | ✅ exploratory |
| Matched-training repair | TM1–TM4 (seeds 0–4, panel 3201–3264); TM4 dev net_Z +0.029 / +0.057 | ⏳ (seed 3 retrying after deadlocks) |
| Silence-fallback gate (CAVEAT: at constant K, b3 > 6 ≡ 'K = 1 and t ≥ 8', so the prospective cells test a K = 1 schedule, not a view-keyed gate; random-capacity cells needed) | dev: tail gate (Z when b3 > 6) −0.16 / +1.32 / +1.39 / +2.73 % vs Z at K = 1 / 2 / 3 / iid (plain −1.33 / +1.32 / +1.39 / +2.73); prospective GT1–GT3 on 3401–3464 | ❌ GT1 (K = 1 gate vs Z −0.59 % [−1.17, +0.02]); ✅ GT3 (+0.78 % [+0.12, +1.53] vs plain); prospective 3401–3464 |
| Second network | 4×4 const-K G1–G5 (b* = 3.7), R5 | ⏳ after the 4×4 chain (≈ 02–04 h) |

| Shared per-seed fragility (artifact agent H1, verified) | ρ(K = 1 gain averaged over 2801 / 3001 / 3101, reserved congestion-order penalty at cap4 / low) = −0.818 (perm p 0.003); unrelated to N_s (0.24 / 0.04); dev net_Z(K = 1) ↔ congestion cap4/low gain +0.721 | ✅ exploratory |

## Positioning (verified prior art)
Staleness harm: Don't Fire Together (Sensors 2026), CoDe (AAAI 2025), VIL2C, CAIC.  More information hurting imitation:
causal confusion (de Haan et al. 2019), copycat (Wen et al. 2020), imitation gap (Weihs et al. 2021).  Receivers failing to
ignore messages: Gong et al. (arXiv 2609.36855, LLM agents).  Fallback controllers: Simplex / runtime assurance.
Distinct here: a capacity-structural trigger with a measured dose variable, decision-level diagnosis against compiled
silence, two independent repairs (deployment-side and training-side) with prospective tests, a gate that keeps the
system no worse than silence, and a second network.

## Kill / scope rules
- If TM1 and the gate both fail: the mechanism is "half explained" (age interface) and the paper is v2 + a boundary section.
- If the 4×4 G1 fails: the K = 1 reversal is 3×3-specific; keep it as a v2 limitation, not a headline.
- If TM passes and the gate passes prospectively and G1 / G3 / G4 hold on 4×4: write the compatibility paper (or v2's main
  new section) around the evidence map above.

## Update 21:5x (01/10) — reframed as channel–receiver compatibility (MARL_DIRECTION_BRAINSTORM_20261001.md)
Candidate claim (replaces the one above if the pending tests support it): **we separate communication failures that the
network can repair from those that no scheduler can repair for the deployed receiver.**  F(κ) = exposures a channel can
produce (outer bound: the receiver floor, now PROVED for the real prefix rule with unequal budgets); R_θ = exposures the
learned receiver tolerates against compiled silence; scheduler repair is possible iff they intersect.
| Link | Evidence | Status |
|---|---|---|
| Outer bound of F(κ) for every scheduler | LeanMarlReceiverFloorV1/V2 + LeanMarlPrefixInstanceV1 (prefix rule ⇒ two inclusions ⇒ Σ_s K*(s)) | ✅ compiled clean; smoke gate smokeMARLFLOOR_20261001 running |
| Schedule-only traversal of F at fixed K, bytes, fresh count | hold-r prospective (L-228): +0.92 → −0.80 %, HD1 / HD3 / HD4 ✅, HD2 sign only | ✅ (do not claim first: Don't Fire Together) |
| R_θ moves with training (same channel) | train-match TM1–TM4; dev SELECT indicator −2.7 / −2.7 / −4.3 % vs Z at K = 1 (optimistic) | ⏳ target pending (~01:30–02:00) |
| R_θ is a band, not a half-space (H-B) | P-UP1 / P-UP2 registered on TM3 | ⏳ |
| The learned error-vs-age function follows the TRAINING age distribution (H-C) | age-response shift (L-237): peak 1–2 → 3–4 in 4/4 seeds, HC1 / HC2 3/4; K = 1-trained student worse at the young label a = 1 | ✅ exploratory (n = 4); decision-level support for the band |
| R_θ across architectures | arch control AC1–AC3; attention learns iid policies on par | ⏳ (~04:00) |
| Third "semantic" class (meaning shift under state-dependent order) | staleness-meaning probe (L-231): SM1 ✅ null, SM2 ❌, SM3 ❌ | ❌ dropped: two classes only |
| Low-dimensional coordinate of R_θ | net = fresh − (stale > τ_train + never), CHANNEL-ONLY: ρ +0.983 over 9 order × capacity cells (L-239, = teacher-witness N); out of sample on hold cells ρ +0.850 and 6/6 prospective signs (L-240); count beats burden; bounded by the net floor (LeanMarlNetFloorV1, compiling) and attained by age-first | ✅ 3×3 (exploratory + out-of-sample); prospective 4×4 (Addendum 4) ⏳ |
| Provisioning rule K_min = (1 + θ)(m − 1)/(τ_train + 2) (A) | 3×3 signs 3/3 + K = 1-trained; 4×4 relative vs absolute pending | ✅ known cells; ⏳ 4×4 |
| Count-targeting scheduler (B) | zero room at K ≤ 2 (the floor), ≤ 0.5 copies elsewhere ⇒ predicted ≈ 0.07 % | ✅ closed as "age-first is near-optimal for the coordinate" |
| Second network | 4×4 replication + const-K | ⏳ ≈ 30 h |
Dropped since 16:0x: SafeEdit gate (L-229); "stale information is intrinsically harmful"; decision-level acceptability as a
return surrogate (H6); rich7 as support (missed its prediction).
