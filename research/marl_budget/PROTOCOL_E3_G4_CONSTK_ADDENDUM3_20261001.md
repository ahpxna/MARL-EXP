# Addendum 3 to PROTOCOL_E3_G4_CONSTK_20261001: the forced-tail predicate, own-trajectory decision diagnostic, headroom-vs-fragility split

Written 01/10/2026 19:13:58 EDT, before any 4×4 const-K TARGET run (e3_g4_constk_20261001 absent).  DISCLOSURE: one seed (s0)
has been looked at on development episodes (PROTOCOL_E3_G4_S0_DEVLOOK_20261001, L-219; gain K = 1 −2.41 % over 32 episodes,
K = 2 +1.38 %, K = 3 +4.27 % on 8); the target panel 3301–3364 and seeds 1–9 are unseen.  Rules G1–G5 and Addenda 1–2 unchanged.

## Added predictions (secondary)
- G6 forced-tail predicate (Lean/papers subagent, numerically checked, NOT proved): at constant K every scheduler leaves a
  receiver-age tail beyond τ when K(τ + 1) < m − 1 (never-heard senders counted as old).  With τ = the iid-training p99 of the
  maximum copy age (4×4: 9) the predicate forces K = 1 only ⇒ predicted target signs: gain(1) < 0, gain(2) > 0, gain(3) > 0.  With
  τ = 3 (absolute) it forces K = 1, 2, 3 ⇒ gain(2) < 0 and gain(3) < 0.  G6 SUPPORTED if the three mean target gains have the
  relative signs (each bootstrap interval excluding 0 in that direction for K = 1 and K = 2).
- G7 own-trajectory decision sign: acc(relay on its own states) − acc(Z on Z's own states) (scripts/MARL_e3_negflip_probe_v3.py)
  has the sign of the mean target gain at K = 1, 2, 3, iid.  (Same-state net_Z failed on seed 0 at K = 1: +0.010 vs own −0.042.)
- G8 headroom vs fragility (artifact subagent H1): Spearman(N_s, gain(K = 1)) | < 0.3 | while Spearman(N_s, gain(iid)) ≥ 0.5.
