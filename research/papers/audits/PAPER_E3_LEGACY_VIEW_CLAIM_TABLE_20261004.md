# Claim table: "Upgrading Communication Without Retraining Every Agent: Legacy-View Emulation for Mixed-Version MARL"

Written 04/10/2026 05:55 EDT (wake 4). It supersedes `PAPER1_CLAIM_MAP_20261003.md` for the legacy-view framing; that file is kept as history.

Every claim below points to a registered endpoint, a report line, its producer and the allowed wording. CIs come from the paper's single rule (`PAPER1_CLAIM_MAP` §3): a two-level crossed bootstrap, actor seeds × traffic-seed blocks, ONE traffic resample per draw shared by all drawn seeds, 2000 draws, rng 0. E7 is already computed this way (`MARL_e3_wave2_report.py`, `bootf`).

## Main claims

| # | Claim (allowed wording) | Evidence (registered endpoint → report line) | Producer (sha) |
|---|---|---|---|
| C1 | A NEW protocol that keeps the legacy relay structure in base packets lets every node rebuild the frozen receivers' K1 view exactly, from local information only, on the same physical trajectory. | E9b-1, E9b-2 (2560/2560), E9c-1, E9c-3 SUPPORTED; E9c-2 wire4: 0 mismatches over 2800 episodes → `e3_wave_20261003/e9_report.txt` l.1–5. Lean `LeanMarlLegacyViewDecoderV1` (`dec_eq_ref`, `dec_wire_eq_ref`; smoke gate smokeMARLLEGACY2, 21 audited theorems) | `MARL_e3_legacy_decoder_nodes_eval.py` 2d268743…; `MARL_e3_e9_report.py` 13aadb17… |
| C2 | The naive design, the same 25 B packet carrying the NEW (U2) table, does not: it changes the legacy view at nearly every OLD step. | E9c control `u2table`: 3200 view mismatches per seed, 1048–1940 action mismatches → `e9_report.txt` l.8 | same |
| C3 | A zero-byte emulator, using only what OLD receivers already hear, is exact exactly when coverage holds; coverage failed on 3.8e-5 of OLD agent-steps on the panel. | E12-b: 532 460 covered & equal, 20 uncovered & different, 0 exceptions; E12-c(1), (2) SUPPORTED → `e12/report.txt` (ledger L-330). Lean `LeanMarlPacketEmulatorV1` (`emu_eq_ref_iff`, `emu_older_iff`; smoke gate smokeMARLEMU12A, 10 theorems, L-332) | `MARL_e3_emu_coverage_eval.py` b4964c67…; `MARL_e3_e12_report.py` f73b7825… |
| C4 | In a mixed fleet (8 OLD / 8 NEW, layout D), emulation recovers system performance relative to fallback (P-a) and relative to running OLD on U2 without emulation (P-b), and keeps NEW agents non-inferior (P-c). | P-a +3.15 [2.24, 4.07]; P-b +4.00 [2.67, 5.33]; P-c SUPPORTED (layout C: P-a +3.28 [2.06, 4.58]) → `w2/report_e7.txt` | `MARL_e3_mixed_fleet_eval_v2.py` b656a1f6…; `MARL_e3_wave2_report.py` bb36f5af… |
| C5 | Against update-permitted references (retraining the OLD receivers with FT-mix or PCT), the emulator showed **no detected difference**. Not equivalence. | EMU − FT +0.32 and EMU − PCT +0.56, CIs contain 0 → `report_e7.txt` (secondary). E14: OP − FTMIX +0.36 [−0.17, +0.93], NOT SUPPORTED, so FT-mix / PCT stay the references (L-331) | `MARL_e3_e14_report.py` bcd16643… |
| C6 | Cost: E9 adds about 1 300 B unique and 10 400 B decoded per episode; EMU adds 0 B. The upgraded channel delivers 78 058 B / episode vs 10 400 for rollback. | `e9_report.txt` l.12–13; `report_e7.txt` byte columns | — |

## Limits that must appear (wording rules)

| Do NOT write | Write |
|---|---|
| "OLD agents are protected" / "per-agent non-inferiority" | "No OLD agent was significantly worse than all-OLD by more than 0.5 point (E13-1). Per-agent non-inferiority was not established: Bonferroni lower bounds reach −9.4 % (D) and −12.9 % (C), and all 8 point estimates are negative." |
| "emulation preserves the old returns" | "Exact legacy VIEW on the same physical trajectory (C1, C3). NEW agents change the trajectory, so OLD returns are not implied (E13)." |
| "EMU matches FT / PCT" | "No detected difference vs FT / PCT (C5); not an equivalence test." |
| "exact" for EMU without condition | "exact iff coverage" (C3) |
| "cheaper than every alternative" | Give the byte vector, including rollback (C6). |
| "iff" for the older E3 sufficiency results | As in `PAPER1_CLAIM_MAP` §4 |

## Open for this paper (not blocking the claim table)

1. An external check: another simulator or a published comm-MARL baseline. P3 needs download permission.
2. Figures from these exact report rows (the old P5 list is superseded: F1–F5 become C1–C6 plus E13 as a supplement panel).
3. If individual protection is wanted: a registered per-agent NI on a fresh panel.

Producer provenance: every row comes from manifests with status COMPLETE and self_check PASS, and source hashes recorded in the manifests.

## Figures (06:29)

`scripts/MARL_e3_paper_figs_20261004.py` (sha 2cff46ba4d8431a3) READS the cited reports; it computes nothing new. Output in `research/papers/_tex/figs_e3_legacy/`:

| File | Content | Claim |
|---|---|---|
| `fig_e7_arms.pdf` | E7, 11 arms × system / OLD / NEW, layouts D and C, delivered bytes per arm in the labels | C4–C6 |
| `fig_e13_forest.pdf` | Per-OLD-agent gain vs all-OLD with Bonferroni CIs; the −0.5 line marked | Shows why per-agent NI fails (wording rule) |
| `fig_e12_coverage.pdf` | The 2×2 contingency on a log scale (0 exceptions) | C3 |

Visually checked 06:29.

## Draft skeleton (08:50)
`research/papers/_tex/paper_legacy_view.tex` (compiles with tectonic): abstract, contract, both theorems stated exactly as in Lean (decoder: full precision every step; wire c: exact for t ≤ c+1, beyond that empirical E9c-2), E9 / E12 / E7 / E13 with the three figures, limitations and provenance. Wording follows the rules above.

## Draft v2 (08:56)
`paper_legacy_view.tex` v2 (compiles) adds:
- introduction with the contract `D_i(T^U_i(h_t)) = v^K_i(h_t)` and three contributions;
- a setting section (4×4 CityFlow, 26 steps, ZTEAM bar, K1 / U1 / U2, layouts D and C);
- the E7 layout-D table copied row by row from `w2/report_e7.txt`;
- related work (refinement, backward-compatible updates, delay-robust MARL, consistent updates).

The draft now states one result that was missing from the claim table: **EMU − ALLNEW = −0.59 [−1.35, −0.02]** (layout D; C −0.49 [−1.21, +0.11]). The mixed fleet with emulation is slightly below a fully retrained fleet. Rule: always report it next to C4 / C5.

The rollback ratio is 78 058 / 10 400 = 7.5×.

## Figures v2 (09:46)
`scripts/MARL_e3_paper_figs_v2_20261004.py` (sha 085da4c1f1e670b3) differs from v1 only in the docstring and the E12 y-limit, so the count labels no longer overlap the title. The numbers are re-read from the same reports. The v1 PDFs are archived in `legacy/figs_e3_legacy_v1_20261004/`.
