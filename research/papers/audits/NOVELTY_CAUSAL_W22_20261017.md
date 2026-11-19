# Collision search for the causal follow-up (17/10/2026, before W22)

**Scope.** About 25 standard web searches on 16–17/10/2026, plus one fetched abstract (arXiv 2110.00118). This is a first-pass screen, not a systematic review: Scholar citation chasing and full-text reading are still to do.

## D1: owner-side identification of a signal's response to the fleet, by randomisation

**Nearest work:**
- **Passive inference of signal timing from probe data.** Patents US 10181263 and US 10074272 fit cycle times, or match observed movements to SPaT. Trajectory-based retiming (Michigan field deployment, about 7 % probe share). Iowa DOT trajectory-assisted actuated control.
- **The reverse direction:** connected-vehicle adaptive control, where the signal estimates the vehicles (Arizona work; FHWA 11044).
- **Our own method:** the CIG-AMF Paper A ε-forcing with a known propensity, and the capacity C.

**Not found:** any vehicle-side active or randomised identification of whether, or how strongly, a signal responds to the vehicles' behaviour. Searches covered "vehicles deliberately perturb", "probing adaptive controller", "randomized experiment connected vehicles … responds to fleet", and "detect signal responsiveness".

**Verdict:** open as of this screen.

## D2: interference bias of per-vehicle A/B tests through a responsive controller

**The interference class is well studied:**
- **Two-sided marketplaces:** Johari, Li, Liskovich, Weintraub (arXiv 2002.05670, 2104.12222). Customer- vs listing-side randomisation is biased depending on market balance; they propose two-sided randomisation.
- **Graph cluster randomisation:** Eckles, Karrer, Ugander (arXiv 1404.7530).
- **Switchback design and inference:** Bojinov et al. (arXiv 2009.00148); Blanchet et al., AISTATS 2026, "Conservative Inference in Switchback Experiments" (PMLR v300).
- **Data-training loops / symbiosis bias:** Si (arXiv 2310.17496); Brennan et al. (arXiv 2309.07107); BAFF (arXiv 2609.08725); Li, Wang, Wang (arXiv 2507.11891).
- **Closest structural analogue:** Spang et al., "Unbiased Experiments in Congested Networks" (arXiv 2110.00118, computer networks). A/B tests of congestion control over a shared bottleneck at Netflix misjudged the direction of some metrics and overstated others. A new algorithm looked much better at low share and much worse at high share, although the two perform identically at full deployment.

**Traffic-specific findings:**
- **GLOSA field evaluations** use within-subject baselines (driving with vs without advice). Examples: Virginia Tech B-GLOSA, with a split-split-plot design under light traffic only; the Ottawa fleet pilot with 7 vehicles on actuated signals; an Alberta thesis with 1 vehicle at 1 intersection. No randomised fleet trial was found.
- **CAV/CV penetration** studies note SUTVA concerns in general terms only.

**Not found:** interference through a *responsive signal controller* whose sensing is biased by the treated vehicles. Nor any quantification of A/B bias for SPaT/GLOSA features.

**Verdict:** the mechanism class is known, so we must cite Johari et al., Spang et al. and the switchback literature. The traffic-signal instance and its sensing channel are new as of this screen. The contribution would be the instance, its measurement against a known global effect, and design guidance, not the interference concept.

## Directions noted, not pursued yet

- **Mediation** (direct effect vs effect through the signal). Transport mediation work exists (TR-A 2025, London Cycle Superhighways; an interrupted-time-series emissions paper, arXiv 2608.18326), but none was found on SPaT and signal response.
- **Interventional / performative forecasts:**
  - performative prediction and RL theory exists: Perdomo 2020; Mandal, Triantafyllou, Radanovic, ICML 2023 and AISTATS 2025; multi-agent PP, NeurIPS 2022; survey arXiv 2602.10176;
  - congestion forecasting as an intervention, JSAI 2026, abstract only.
