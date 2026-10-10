# Why nothing wins yet, where winning is possible, and where I disagree with the audit — 03/10/2026 19:0x EDT

Inputs: METHOD_ADVANTAGE_PLAN_20261003 and RECEIVER_ADAPTATION_IMPLEMENTATION_SPEC_20261003 (external audit), the ledger
(L-01 … L-305), E3_INTERIM_RESULTS (selector diagnostics, N1/N2, 18:57 correction), MARL_LESSONS_AND_STORY_20261002, the
4×4 / 3×3 checkpoint manifests and training logs, the P1/P2 protocols and smoke files. No new simulation for this note.

## 1. Did we lose, or did we not compare?

Both. The comparisons that were run were mostly **inside our own family**. The comparisons that would decide "beats other
methods" were mostly **never run**.

| Comparison | Run? | Outcome |
|---|---|---|
| Learned selector / critic / DFL vs prefix and direct rules (Sept) | yes, many | no stable closed-loop advantage |
| Age-first relay protocol vs prefix and the learned selector (Sept–Oct) | yes | **relay won**; it is our own hand-designed protocol, not a learned method |
| Support fallback vs freshness gate, vs Mahalanobis | yes (4901); paired panel running (P1) | trade-off; no dominance |
| Input adapters (remap, onefresh, clip, EMU, THR) vs plain | yes | lost |
| Train-match, mixture vs frozen and Z | yes | won against frozen and Z; these are retraining references, not new methods |
| Fine-tune from the old checkpoint, FT-mix, PCT, BCWI, paired-channel candidate | **no** | — |
| Any method vs published comm-MARL baselines on an external benchmark | **no** (MPE2 download not approved) | — |

So "we searched everything and nothing can win" is false. The adaptation branch was never built.

## 2. Two facts from re-reading that change the plan

### 2.1 The ceiling is already reached on matched channels

Select-set queue sums from the checkpoint manifests (the training-time selection set) give each method's gain vs Z, the same
seed's compiled-silent student:

| Grid | Teacher with the FULL current view (set_full) | CK1 on K1 | Cage on iid | MIX | Seeds |
|---|---|---|---|---|---|
| 4×4 | **+5.81 %** | +5.31 % | +5.95 % | +5.38 % | 10 |
| 3×3 | **+2.08 %** | +2.32 % | +3.14 % | +2.69 % | 5 |

**Caveats.** These numbers are selected on that very set, so they carry selection bias in both directions. The panel numbers
(4201: CK1@K1 +5.80, Cage@iid +6.02) agree.

**Reading.**

* Distilled from a full-information teacher, the relay students on their own channel are **at the teacher's level**. The
  value of information in this framework is about 6 % (4×4) or about 2–3 % (3×3), and the age-first relay protocol already
  extracts essentially all of it.
* Any method compared on final return on a matched channel, or against MIX, has headroom of about the MIX premium
  (≈ 0.5–1 point) or less. That premium is about the size of select noise (§2.2).
* The only large quantity left is the **hazard itself**: about 9 points between a frozen receiver and a matched one
  (4201: −9.35 upgrade, −8.60 downgrade).

**Consequence.** A method can win in E3 only on **how cheaply and how safely it closes the hazard** (new-channel data,
old-channel retention, retraining avoided). It cannot win on final return over retraining, which already sits at the
ceiling. To beat other methods on return, the setting must have more headroom: a better teacher, an RL fine-tune on return,
or a task where communication is worth much more (external benchmark).

### 2.2 Retraining from scratch is fast, and select noise is large

**The ckpt_best iterations** (of 500) on 4×4 seed 0:

| Receiver | ckpt_best iteration |
|---|---|
| Cage | 20 |
| CK1 | 40 |
| MIX | 100 |
| Z | 180 |

**Select curves.** Cage was at 1170 at it 20, then 1188–1206. CK1 was at 1265 at it 20, then 1183 at it 40, then 1183–1215.
MIX was at 1283 at it 20, then 1195 at it 40, then 1189–1213.

* **The plateau** is reached by about **iteration 40**: 8 % of the recipe, 320 training episodes, about 11 CPU-minutes.
* Later points fluctuate by about ±10 queue units, roughly ±0.8 %. That is as large as the MIX premium; part of the "MIX vs
  specialist" gap may be selection noise.
* Retraining on the simulator is therefore cheap. The cost that matters in deployment is **new-channel interaction**
  (episodes on the upgraded network) and **old-channel regression**, not CPU.

## 3. Branch by branch: why it lost, what differs, can it improve

| Branch | Why it lost (evidence) | What I add or dispute | Can it improve? |
|---|---|---|---|
| **Selector / critic (Sept)** | The critic cannot rank candidates within a state: Spearman −0.02 … +0.04. Out-of-sample tie-half pair accuracy is 0.495 / 0.526, with CIs that contain 0.5. Regret ≈ ranking loss (+15.24 / +14.17); the threshold effect is n.s. Oracle per-state gain was +15.4, so the problem was ESTIMATION, not missing room. | **(a) Headroom moved.** The later age-first relay captured the information value (students ≈ teacher). A selector now has ≈ 0 room on 4×4; on 3×3 the teacher itself is only +2 %. **(b) Co-adaptation hypothesis.** Changing which messages are sent changes the receiver's input distribution. The student was trained under prefix, so a selector's "better" message sets can push it out of support — the same mechanism as the hazard. Untested. | Not worth reopening in E3. A learned selector needs a setting where the protocol leaves room, and it must be trained jointly with the receiver. |
| **Support fallback (FB_S)** | It asks "is the view familiar?", not "does using it help?" (audit, agreed). | **Structural cap.** Fallback picks, per decision, between the frozen receiver and Z, so its gain is bounded by roughly the better of the two. It can never beat a matched or MIX receiver. It is a safety device; its competitors are other runtime gates (SIL-C style), not methods that learn. | Better gates (utility-aware, matched features) — P1 measures the trade-off. To keep the information when falling back, the fallback target must use messages (e.g. MIX), which costs a second trained receiver. |
| **Mahalanobis** | Trade-off vs FB_S. The float-tie bug is fixed in P1. | Audit's new finding: CK1's covariance has rank 7, because feature 0 is constant = 1 under K1, and the pseudo-inverse ignores that direction. That is a real weakness of the baseline. A residual guard, ‖(I − CC⁺)(x − μ)‖, should be a SEPARATE versioned arm, to make the baseline stronger, not weaker. Agreed. | Yes, as a stronger baseline. It still cannot turn distance into decision value. |
| **EMU / THR (input adapters)** | P2: on the deployed upgrade (U1), 50.8 % of direct K1 packets are absent from the receiver's prefix; with relay, 79 % of K1 view entries are recoverable on 4×4. | **The audit's two corrections are accepted.** (1) "Not nested on packet traces; the emulator cannot rebuild every K1 entry on U1" is the safe claim; it does not rule out a sufficient statistic. (2) N4 not significant would be inconclusive, not "harm is all reorder". | Even with 100 % availability (U2), exact emulation only RETURNS to K1 (rollback). To exceed K1 the receiver must learn to use the new information, which is adaptation. |
| **MIX** | It is near the specialists everywhere (worst cell +5.27 vs +5.8 / +6.0, 4×4) but not equal. | The premium (0.5–1) is within select noise; with the same 500 iterations, each regime gets about a quarter of the data. Not yet separated: per-regime data, gradient conflict, capacity. | Learning-curve comparison at equal per-regime data before any architecture change (audit, agreed). |

## 4. Where a win is actually possible

| # | What | Win condition | Strongest competitor |
|---|---|---|---|
| A | **Data-efficient receiver adaptation** from the old checkpoint (audit W-plan) | At a SMALL fixed budget of new-channel episodes (well below the 320-episode plateau), a higher new-channel gain with old-channel non-inferiority. Primary endpoint = return at fixed small budget, from the learning curve. | FT-mix (warm start, old + new replay), PCT / focal distillation, BCWI |
| B | **Mixed-version fleet with backward-compatible (nested) scheduling** | Old receivers stay exact (EXACT on U2 = K1, zero retraining) while new or MIX receivers use the extra capacity. Smoke hint: MIX was better on U2 than on U1 (+11.0 vs +9.0, 1 seed — NOT evidence). | U1 + frozen, U1 + fallback, retrain-all |
| C | **Higher-headroom setting** | Communication is worth much more than 6 % (external benchmark), so method differences exceed noise. | Published comm-MARL baselines |

**Novelty check (03/10 18:5x, 3 searches, not exhaustive).**

* **A.** PCT / Focal Distillation already up-weights samples the old model got right, including in fine-tuning. The only
  distinct element is the **paired channel views on the same physical state** that define the regression indicator. Mandatory
  ablation vs PCT. No MARL channel-change receiver fine-tuning paper was found.
* **B.** Legacy-compatible operation is classical in wireless (backward compatibility). Max-age-first is the known optimal
  greedy for symmetric broadcast AoI (Kadota et al.). The angle "re-ordering on a capacity upgrade breaks nesting for LEARNED
  receivers; nested scheduling restores exact compatibility" was not found.

## 5. Where I disagree with the audit spec

1. **Pilot budgets "10 % and 20 % of 500 iterations" are too large.** From-scratch training plateaus at about 8 % (iteration
   40). At 10–20 % even training from scratch is done, so the arms cannot separate.
   * Use a learning curve at 1, 2, 5, 10, 20 and 40 iterations (8–320 episodes).
   * The primary budget should be counted in **simulated environment episodes, all channels included**: a paired episode
     costs 2.
2. **The primary endpoint should be return at a fixed small budget (data efficiency), declared now.** The final-return
   headroom over FT-mix or MIX is ≤ select noise (§2.1, §2.2). This choice comes from training logs, not from any test
   result. The audit's "1-point improvement at the end of training" is unreachable when the ceiling is about 0.5 point
   above MIX.
3. **Old-channel ε = 0.5 point needs paired panels.** Unpaired select-set noise is about ±0.8. Paired 128-episode panels
   give paired-difference CIs of about ±0.5–1.0 (4201), so ε needs ≥ 10 seeds or a larger panel.
4. **The paired-view collector can be exact and simple:** two CityFlow instances stepped with the SAME actions, one per
   channel. CityFlow is deterministic and the channel never changes physics, so both stay physically identical. The
   physical identity is asserted at every step, and the old views are genuine K1 histories, causal by construction. This
   replaces the audit's "two simulator channel states" with a stronger check.
5. **Teacher-margin labels as h.** The flip probe found about 12 % of acceptable decisions turning unacceptable (CK1, 4×4,
   const1 → iid). Weighting by h therefore up-weights roughly that fraction. At the 1–40-iteration budgets, a data-efficiency
   gain is plausible; a final-return gain is not.

## 6. What happens now

* P1 (repair table) and P2 (nesting) are running; their predictions are frozen. They are not used to tune the adaptation
  arms.
* **W1–W3 code starts now.** W1: a v12 trainer that imports v11 and adds `--init-from` with a fresh optimizer and lineage.
  W2: the two-env lockstep paired collector. W3: the arms FT-new, FT-mix, PCT-focal and PAIRED (+ γ = 0 and λ = 0 ablations).
  BCWI comes after the fine-tuned descendants exist.
* The W4 protocol (budgets, endpoints, ε, seeds, panels) is written before any adaptation run. The pilot runs after P1
  frees the CPU.

## Corrections (20:0x, external audit ADAPT_V12_P2_AUDIT_20261003)

**§2.1 and §4 overclaimed the ceiling.**

* The full-view teacher is a LEARNED policy, not the optimum over full-view policies. The table itself has students above
  the teacher.
* Correct wording: the current recipes reach about the reference teacher; the true ceiling is unknown.
* Withdrawn:
  * "cannot win by more than ≈ 0.5 point";
  * "the relay has captured the whole information value";
  * "only data efficiency can win".
* What stays: on THIS teacher and recipe, matched / MIX receivers sit near the reference. That is why the pilot's endpoint is
  data efficiency at small budgets. It is a choice for this pilot, not a theorem about headroom.

**§3, selector row.** The later relay protocol does not retrospectively explain the September selector failure. That failure
had oracle headroom on another actor (+15.4 per state). The "headroom moved" point applies only to reopening a selector NOW,
on top of the relay.

**§4 B (mixed-version fleets).** Untested: P2 had homogeneous teams. See PROTOCOL_E3_MIXED_FLEET_20261003.
