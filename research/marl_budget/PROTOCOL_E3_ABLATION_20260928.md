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
