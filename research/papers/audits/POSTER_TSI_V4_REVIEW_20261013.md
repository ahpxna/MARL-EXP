# Review of the TSI poster v4 (posted on LinkedIn), 13/10/2026

**Files:** `research/papers/TSI_two_population/TSI_poster_v4.pdf` and `.pptx`, built 09/10 17:37 (ledger C-231).

**Method:**
- Every claim on the poster was traced to the ledger (`research/city_sim/CITY_LEDGER_20261002.md`), the paper (`research/papers/_tex/paper_two_population.tex`) and the Fig. 3 data (`fig3_repr.json`).
- The PDF was rendered at 400 dpi and read region by region.
- The PPTX was inspected shape by shape with python-pptx.
- The seven 2025–2026 references were checked online.
- Nothing was rerun.

**Status (13/10 15:36): fixed in v5** (`TSI_poster_v5.pdf`, script `POSTER_SCRIPT_20261013_v5.md`, ledger C-240).

**Verdict:** the layout and most numbers are correct. But six statements are false or contradict the poster's own decision rule, and three omissions make the fuel claims read stronger than the evidence. The script's sentence "Mọi con số trên poster đều đúng với dữ liệu đã đăng ký" (POSTER_SCRIPT_20261009.md, line 12) is therefore not true. These errors were introduced in the v4 text written on 09/10.

---

## A. False statements or self-contradictions (fix)

### A1. "TSI-G repairs the community defaults" (col. 3), Fig. 3 caption "TSI and TSI-G remove the penalty", and Bottom line "repairs it"
- **Problem:** on RESCO's MPLight state, TSI-G fails the poster's own decision rule: the fleet's extra delay is +0.51 [0.30, 0.71], with a registered one-sided upper bound of +0.74 against a limit of +0.5. The result is NOT SHOWN.
- **Source:** C-230.
- **Replace:** "TSI-G repairs sumo-rl's default and RESCO's IDQN / IPPO state without retraining; on RESCO's MPLight state it removes 97% of the extra delay (16.0 → 0.5 s/veh), just short of our limit."

### A2. "A car gliding on SPaT never counts" (Why, col. 1) and the Fig. 3A group label "counts only stopped cars"
- **Problem:** sumo-rl's default state includes lane **density**, which counts every vehicle, and RESCO's drq (IDQN / IPPO) includes **approaching** counts and a **speed sum**. Only the queue, waiting-time and pressure features are stop-thresholded.
- **Source:** `scripts/CITY_w20_bench.py` docstring; C-227.
- **Replace:**
  - Why: "A car gliding on SPaT never enters their queue, waiting-time or pressure counts, so the light serves it later."
  - Fig. 3 label: "stop-based inputs".

### A3. "For cities and carmakers: … speed or position inputs work with the forecast alone", and "We pinpoint the cause: … signals that see speed groups, queue positions or every vehicle need no repair"
- **Problem:** RESCO IDQN has speed and approach inputs, and sumo-rl has density, yet both needed a repair (+2.6 and +5.4 s/veh). What separates the two groups is the absence of any stop-thresholded input, not the presence of speed or position.
- **Source:** C-230; fig3_repr.json.
- **Replace:** "Inputs with no stop threshold (speed groups, queue positions, all-vehicle counts) work with the forecast alone; a stop-thresholded input (queue, waiting time, queued pressure) needs TSI or TSI-G, even next to density or speed features."

### A4. "Its default setting, fixed in advance, … transfers to two more networks, and tolerates 80% detection and 20% message loss" (col. 3)
- **(a) Transfer.** The transfers used other calibrations, not the default fixed in advance:
  - **spider:** four registered failures on the one-lane build; then a two-lane rebuild passed with (A, B) = (1, 0.5), −1.49% (ledger lines 1430–1450).
  - **rand3:** a second attempt with an extended per-signal adapter grid passed, against the registered expectation, −2.17%; the chain bound over the two attempts is 0.075 (C-153).
- **(b) Robustness.** For the quantile revision (q 0.1), 80% detection **misses** the fleet-time limit (upper +0.56) (C-184). The "80% detection" tolerance belongs to the older design (C-142). The quantile revision does tolerate a 1-s delay (−3.29%), 20% loss (−3.66%), 50% loss (−1.88%) and 1 m/s speed noise (−4.60%).
  - *Correction, 13/10 recheck:* these W14-2 rows are the quantile revision TRB, whose adapters were chosen per signal; they are not the fixed default (1, 0.25), which had no separate robustness test. The v5 wording was fixed accordingly.
- **Replace:** "Its default setting, fixed in advance, saves 5.6% (HBEFA4) and 3.3% (PHEMlight5) on new signals and fleets and tolerates a 1-s SPaT delay, 20–50% message loss and speed noise; recalibrated, TSI also passed on a second network and on a two-lane build of a third."

### A5. "with TSI-G, −0.2, −0.2 and 0.5, and 5–10% fuel saved" (col. 3)
- **Problem:** 5–10% is HBEFA4 only. Fig. 3B's own PHEMlight5 bars show 2.8–5.6%.
- **Source:** fig3_repr.json.
- **Replace:** "… and 5–10% fuel saved (HBEFA4; 3–6% under PHEMlight5)."

### A6. Fig. 3A y-axis "Fleet's extra wait (s/veh)"
- **Problem:** the plotted quantity is time loss (delay), not SUMO waiting time; the text says "lose 5.4 s/veh".
- **Replace:** "Fleet's extra delay (s/veh)" (regenerate with `scripts/POSTER_tsi_fig3_bars.py`).

---

## B. Misleading by omission (strongly recommended, since the poster is public)

### B1. Limitations: "Calibrated simulation"
- **Problem:** every headline number uses SUMO's default Krauss drivers. The project's own field check found that Krauss brakes too late and hard at a stop (F4, NGSIM Peachtree, C-199).
  - With drivers matched to field data, the fleet saves about 1% (HBEFA4) and nothing detectable (PHEMlight5) (W17, C-218).
  - No fleet design reached 3% under both models (W18, C-223).
  - The paper's abstract states "Field data bound the benefit" (C-219); the poster says the opposite by omission.
- **Replace:** "Simulation with SUMO's default drivers; with drivers matched to field trajectories the fleet's fuel saving shrinks to about 1%, so the robust finding is the time effect. A road pilot is next."

### B2. "Checked against field data"
- **Problem:** it lists only the favourable checks. It omits:
  - the driver check (B1), the field result that most limits the headline;
  - that on Salt Lake City demand TSI was worse than the old timing and its decision failed (C-217). The ~10% there is the fleet against human drivers under fixed time (M1).
- **Fix:** add the driver result, or retitle "Field checks of the components".

### B3. "Registered confirmation: TSI cut fleet fuel by 3.85% (95% CI 3.26–4.43)"
- **Problem:** this figure is HBEFA4 only. The same design costs +1.76% under PHEMlight5 (C-142), which is the model the poster itself says measured fuel favours. With fresh (non-reused) checkpoints the saving was −2.61% (ledger line 1230).
- **Fix:** mark it "(HBEFA4)" and lead with the default setting (5.6% / 3.3%).

---

## C. Minor and presentation
1. **"On RL-H, TSI-G beats TSI (−0.3 s/veh)":** this holds for the fleet's time only; human cars are +0.57 s/veh against TSI (C-230). → "cuts the fleet's delay by a further 0.3 s/veh".
2. **"ported DC-Ada and FoRL":** → "our ports of DC-Ada and FoRL". They are not the authors' code.
3. **"MaxPressure counts vehicles at every speed":** this is Varaiya's MaxPressure (W9-6). RESCO's MaxPressure baseline uses the queued-based mplight pressure (C-227). → "Varaiya's MaxPressure".
4. **"The finding holds when the reward or any scale constant is changed":** only ×½, ×2 and reward ÷1 / ÷100 were tried. → "the scale constants we varied".
5. **Fig. 1:** R9, R10, rule, spider and grid4 are not explained.
6. **Fig. 4B:** "TSI, global adapter" is the first TSI design (C-114). Four of its five points lie above the 0.5 line, which a careful reader will read as TSI failing. Say in the caption that it is the first design, shown for the mechanism.
7. **Undefined symbols:** Q_j, θ, λ and α. The queue formula is dark red while the other formulas are black.
8. **Dangling asterisk:** "*This material …" has no matching asterisk on the author line.
9. **References:** straight quotes in [10] and [11], curly quotes elsewhere; the whole block is bold.
10. **Metadata:** the PPTX has no document properties (its title shows as "PowerPoint Presentation"), and the PDF has no Title or Author.

---

## Verified correct
| Claim | Source |
|---|---|
| Fleet saves 6.5% under fixed time | R10 vs σ* −6.54% (C-57) |
| TSI −3.85% [3.26, 4.43], every time limit met | ledger line 933 |
| Default 5.6% / 3.3% | fig3 RL-H TSI −5.57 / −3.25 |
| Forecast alone, extra delay: RL-H +1.7; sumo-rl +5.4; IDQN +2.6; MPLight +16.0 | fig3_repr.json, C-230 |
| TSI-G: −0.18 / −0.23 / +0.51 | C-230 |
| Controls: −0.39, −0.40, −1.05 | fig3_repr.json |
| MaxPressure −2.68%, met | ledger line 1331 |
| Hamburg: q0.1 coverage 0.117 [0.098, 0.139] and 0.102 | C-206 |
| Salt Lake: 9.4% / 10.2% (fleet vs humans, fixed time) | paper, sec. f1 |
| One-car theorem; hypotheses satisfiable (s = 2, w = 3) | paper, Thm. twosided |

**References verified online:**
- [3] Otto et al., VEHITS 2025, pp. 148–156.
- [5] Li, Wang, Hu, TR-C 177:105198.
- [6] Gerner et al., FoRL (IJCAI 2026 XAI workshop; repo urbanAIthi/26_FORL_IJCAIXAI).
- [7] Alqithami, DC-Ada (arXiv 2604.03905; DOI 10.1109/ACCESS.2026.3687163).
- [4] Xue et al.: title and authors confirmed; the TR-C volume was not independently confirmed.

**Layout:**
- No overlapping, hidden or off-slide shapes; no notes.
- Every image is ≥ 172 dpi at 48 in.
- Fonts are embedded (Liberation Serif, metric-compatible with Times New Roman).
- At 48 in: body 24 pt, captions 19 pt, references 18 pt.

## Outdated in POSTER_SCRIPT_20261009.md
- Part 1: "chịu được 80% phát hiện" (wrong for the default design).
- Part 6 #6: "trễ 1 s còn 0.74%" (applies to the older design; the default keeps −3.29%).
- Part 6 #4 is right about MPLight, but the poster's headline still says "repairs".

## Not checked
- The LinkedIn post's own text, which was not available.
- Image content of Fig. 1 and Fig. 4 against their raw runs: only the plotted labels and values were read; Fig. 3 was checked against its data.
