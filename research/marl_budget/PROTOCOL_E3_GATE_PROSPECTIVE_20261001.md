# Pre-specified PROSPECTIVE test: a stale-tail silence-fallback gate is never worse than compiled silence and keeps the gain

Written 01/10/2026 16:09:35 EDT (`date`), BEFORE any run on the panel below.  Design fixed on the development panel
(e3_gate_dev_report_20261001.txt, EXPLORATORY; seed901–904 × 8/16, seeds 0–9): of four arms (age clip; tail gate; coverage
gate + clip; both), the TAIL gate was best — K = 1 −0.16 % vs Z (plain relay −1.33 %), identical to the plain relay at K = 2,
3 and iid (no fallback there); clip lowered K = 2 (−0.62 %) and the coverage gate lowered K = 1 and K = 2.

## The gate (deployable: uses only the receiver's own merged view; Z costs 0 bytes)
Every receiver carries its relay student relay6Cage_st_s<s> and its zero-byte student distill_none_s<s>.  At each step it
computes b3 = Σ_j (a_j − 3)+ over the ages (decision steps) of the entries of its merged view; if b3 > 6 it acts with Z on its
local observation, else with the relay student on the unmodified view.  scripts/MARL_e3_gate_eval.py --A -1 --bmax 6
--nmax 1e9 (self-checks: an always-fallback gate reproduces Z's rows and a never gate the plain relay's rows, 8/8 each).

## Panel and arms
Traffic seeds 3401–3464 × 8/16 (checked unused 16:0x; maximum used 3264; 3301–3364 is reserved by
PROTOCOL_E3_G4_CONSTK_20261001), used once.  Seeds 0–9.  Z (scripts/MARL_e3_delivery_eval_v6.py), plain relay
(scripts/MARL_e3_ageclip_eval.py --A -1) and gate, at const K = 1, 2, 3 and iid.  Endpoint and two-level bootstrap as
PROTOCOL_E3_AGECLIP_PROSPECTIVE_20261001.

## Rules
- GT1 never worse than silence: gate vs Z bootstrap lower bound > −0.5 % at every K ∈ {1, 2, 3, iid}.
- GT2 communication kept where the view is in range: fallback share ≤ 2 % of decisions at K = 2, 3 and iid.
- GT3 repair at K = 1: gate vs plain relay mean > 0 with lower bound > 0.
Interpretation: GT1–GT3 → a receiver that falls back to silence only on far-tail stale views is no worse than compiled
silence in every tested capacity regime and keeps the relay's gain elsewhere (the practical exit of the compatibility
reading).  GT1 failing only at K = 1 → the far-tail gate is not enough; the residual is the early sparse-coverage component.
Launcher `scripts/RUN_marl_e3_gate_prospective.sh`, report `scripts/MARL_e3_gate_prospective_report.py`, both written before
the runs.
