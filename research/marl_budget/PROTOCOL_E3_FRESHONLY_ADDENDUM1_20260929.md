# Addendum 1 to PROTOCOL_E3_FRESHONLY_20260929.md (sha256 853caa9a…), written 22:5x EDT, BEFORE the comparator below is run on panel 2001–2064

## Why
- On the development panel (901–964), the 0-byte student `distill_none_s0` equals FO under the prefix: FO − student
  +0.1 % [−0.9, +1.0].
  - The student is DAgger-distilled from the same full-information teacher set_full_s0 (ledger L-122).
  - Both beat set_none_s0 by −3.2 / −3.3 %.
- So the primary criterion of the protocol (FO vs the co-trained none actor) cannot separate two things:
  - the value of messages AT DEPLOYMENT;
  - the value of communication IN TRAINING (a full-information teacher).
- The 0-byte distilled student is the stronger no-deployment-communication baseline.

## Added comparator (secondary; the protocol's primary criterion is unchanged)
- `distill_none_s0` with no messages, on panel 2001–2064.  Later, a seed-1 student distilled from set_full_s1.
- Statistic: FO(set_full_s s) under the prefix vs distill_none_s s, the same bootstrap as the primary.
- Reading, fixed now:
  - upper bound < 0: deployment messages add value beyond training-time communication;
  - interval containing 0: the value is training-time only, at this capacity;
  - lower bound > 0: the student is better.
- FULL delivery vs the student is reported too.  It is the ceiling of deployment messages without capacity limits.
