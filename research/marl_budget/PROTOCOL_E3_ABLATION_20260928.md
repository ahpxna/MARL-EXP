# PROTOCOL E3-ABLATION — bid × response head for a learned actor (28/09/2026, 09:20)

- Written before any ablation result on real labels. The only runs so far used the tiny smoke labels
  of `e3_chain_smoke_20260928_003728`.
- No ledger is edited.
- Companion to PROTOCOL_E3_PILOT and PROTOCOL_E3_SCRATCH. Those files are unchanged.

**Variants.**
- Produced by `scripts/MARL_e3_selector_train_v2.py` on the SAME continuation labels, with the same
  critic, tuning allowance and init seeds 0–2.
- `sel_nobid`: no bid, no head.
- `sel_bid`: the 1-byte bid (the actor's top-2 phases and logit-gap bin), no head.
- `sel_resp`: a response head from legal data only, no bid.
- `sel_bid_resp`: bid + head. This is the method: B2's design ported to the learned actor.
- The head is trained on train-split labels; its inputs are legal.

**Evaluation.**
- `scripts/MARL_e3_closed_loop_v3.py`: direct policy, +84 B total cap with the bid charged at every
  step, pilot panel 901–916, MP2 reference.
- Report: `MARL_hetero_closed_loop_report.py --control sel_nobid`.
- Runner: `scripts/RUN_marl_e3_ablation.sh`.

**Reading rules, fixed now.**
- Only for actors that pass G1 and G2 of their own protocol.
- BC pilot seed 0 failed G1, so the BC chain's ablation is recorded and not read. Where the
  protocol gates per seed (the scratch chain), each passing seed is read.
- Contrasts, each paired by episode with a bootstrap over episodes, with every init seed shown:
  - the method: sel_bid_resp − sel_nobid;
  - the bid without the head: sel_bid − sel_nobid;
  - the head without the bid: sel_resp − sel_nobid;
  - selection at all: sel_* − prefix.
- The development gains of the selectors (held-out labels) are reported with the head's
  change-prediction precision and recall against its base rate.
- Nothing here is confirmatory. The confirmatory test uses seeds 1301–1316 after a freeze.

**Known gap.** A queue bid with the same bytes cannot be built from the stored labels, which do not
contain the receiver's fresh own queue. It is deferred to the labelling round of the confirmatory test.

## Amendment 1 (28/09, 10:20; written after the first ablation result, before any dense-label result)

**Why.** The first ablation (scratch s3) shows no selector gain, even offline. Its training set is
768 states and its select split 48 states. This amendment adds DATA, not features, in the spirit of
the B1 learning curve.

**Dense labels for the same actor.**
- Snapshots at every step t ∈ {4, …, 22} (19 per episode) on train, select and development.
  That gives about 2,432 train states and about 304 select and 304 development states.
- Same producer (`MARL_e3_continuation_labels.py`), same candidate family, same continuation.
- New directories `labels_dense_*`; the original labels are kept.

**Selectors.** The same four variants with the same code (`MARL_e3_selector_train_v2.py`); the same
reading rules and contrasts; closed loop on the same pilot panel 901–916.

**Additional reading rule.** Compare the realised development gain against the original labels on
the same variants. If the dense labels still give ≤ 0 offline, the E3 selector question is recorded
as open for this actor, and the method claim stays with the fixed-MP2 held-phase result (B2).
