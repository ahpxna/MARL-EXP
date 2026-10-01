# A BYTE-budget protocol variant with compressed payloads (DEVELOPMENT-CONFIRM protocol, 29/09/2026, written 22:5x EDT)

This is written BEFORE any run on the panel below.  The ledger entries are L-128 … L-130.  Direction 2 is described in
`research/papers/audits/MARL_NEW_DIRECTIONS_20260929.md`.

## Where this comes from (development panel 901–964, eval-only, already seen)
- Sender-side quantised payloads keep the whole full-information value of `set_full_s0`: 2 / 3 / 4 / 5 B per packet give
  −6.2 / −6.6 / −6.4 / −6.0 % vs set_none_s0.  Raw full delivery is −5.8 %.
- Under the byte-budget variant below, the 3 B codebook gives −3.5 % [−4.6, −2.5] against the 0-byte distilled student
  distill_none_s0.  That student is the strongest no-deployment-communication baseline (L-129).
- Selection: 4 codebook sizes were compared on that panel; L = 4 (3 B) was the best.  It is FIXED here.

## The variant (NOT PROTOCOL_HETERO_v0; a declared new protocol)
- Capacity: receiver i can decode 25·K_i BYTES per step, with K_i ~ U{1..7} i.i.d. per step (HETERO_v0's process in
  packets of 25 B).  It decodes floor(25·K_i / 3) compressed packets, at most 8.
- Payload: each sender quantises its own summary with the codebook
  `research/marl_budget/e3_payload_codebook_20260929.json`, level L = 4 (21 bits, 3 B).  The codebook was fitted on
  TRAIN traffic 301–304 only.  The phase is exact; elapsed has 2 levels; vehicles 4 levels per slot; waiting 2 levels
  per slot.
- Stream: the protocol's prefix order.  Receivers decode the prefix of the stream within their byte capacity.  With 3 B
  packets every receiver decodes all 8, so the stream carries all 9 senders.
- Bytes: 3 B × transmitted packets + the shared description cost (models.marl_hetero_selector.profile_cost with 3 B
  payloads).  The evaluator records the 25 B accounting; the report converts it (× 3/25; repl = 0 when every receiver
  decodes all).
- Receiver: fresh-only pooling (FO, `--adapter-override freshonly`).
- Actor: set_full_s s, trained on RAW full delivery.  The compression is applied at evaluation only.  A trained
  compressed-payload actor is a later step.
- Evaluator: `scripts/MARL_e3_delivery_eval_v7.py --quant 4 --byte-capacity 3 --adapter-override freshonly --deliveries
  prefix`.

## Panel
- **Traffic seeds 2101–2164 × headways 8 / 16** (128 episodes).
- Checked unused for any E3 episode at 22:5x.  It is used once, for this comparison.
- Panel 2001–2064 is not reused: it served the FO protocol.

## Pre-stated criterion
- **PRIMARY**, per training seed s ∈ {0, 1}:
  - statistic: the ratio of summed waiting, variant (set_full_s s) / the 0-byte student distill_none_s s (distilled from
    set_full_s s), minus 1;
  - bootstrap over traffic seeds, both headways, 4000 resamples;
  - the upper 95 % bound must be < 0.
- The variant is supported only if BOTH seeds pass.
- Seed 1 needs set_full_s1 (training) and distill_none_s1 (to distil after it).
- **Secondary**, reported as measured:
  - vs set_none_s s;
  - vs raw full delivery (225 B/step);
  - by headway;
  - the byte cost per step.

## Not claimed
- This is not the reserved test (1301–1316 stays closed).
- It is not a trained compressed protocol.
- It does not show that the bytes-limited capacity model describes any real channel.  It is a stated alternative to the
  packet model of HETERO_v0.
