# Paper-1 draft figures (03/10/2026 08:0x EDT; drafted by subagent B in wake 3, reviewed by me — F1 and F2 viewed)
Every plotted number is in the matching *_data.json with its source; scripts regenerate the figures from the repo's raw rows.
F1 train × deploy heatmaps · F2 information vs excess (RI exact Bayes, C0 exact table in regret units, E3 matched-receiver
proxy per panel) · F3 cross-channel flips on identical states (L-292) · F4 gain-vs-channel shapes · F5 repairs at the upgraded
channel (PLAIN / LAB / EMU / FB_S / matched / MIX).
Open caption decisions (from B's report): (1) the 4×4 pooled cells include test D 4601 (CK1 K1 +5.86 vs README +5.80 etc.) —
state the pooling rule; fallback / emulation panels are NOT pooled (would shift K1 / iid cells by ≤ 0.18); (2) F3's iid → K1
row mirrors K1 → iid exactly (NF(A→B) = PF(B→A)) — drop it or say so; (3) F2 mixes three bases and units — name them; C0
regret units differ from the exact cost-unit split (FT −3.27 vs −3.62); (4) Z-driven states (F3) vs own closed loop
(age-response probes) give different accuracies — do not mix; (5) single-panel rows: 3×3 CK2 (3901), MIX2 (4501), 4×4 MIX (4601).
Provenance: 425 manifests of the newly used panels COMPLETE + PASS; 415 checkpoint sha = current files (10 test-D Z manifests
lack a sha).
