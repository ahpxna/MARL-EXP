# Math closure and novelty audit — 2026-09-25

Scope: papers A, B, C and their supplements as of 2026-09-25 (uncommitted, after 174490c).
Companion files: `OPEN_MATH_20260924.md` (ledger), `CLAIM_MAP_9COL_20260924.md` (claim map),
`/Users/phanan/Documents/ChatGPT/CIG-AMF/research/novelty_comparison_20260925/COMPARISON.md`
(external comparison, file time 08:05, reviewed in §4).

## 1. What was inspected

**Mechanical integrity (all six manuscripts).**
- The script `sweep_math.py` (session scratchpad) parsed every `\lean{}` citation: 1,342
  citations, 1,212 unique per paper. Each one was resolved to its declaring
  module and checked against the import closure of `verify_all.sh` MODS, which is 223 modules.
  Result: every citation resolves inside the gated closure.
- No gated module declares an `axiom`, contains `sorry` or uses `native_decide`. The directory
  has one `sorry`, in `LeanD6DecisionHalfFactorConjecture`, which is neither gated nor cited.
  The directory has three `native_decide` files, also not gated.
- Some cited lemmas have no `#print axioms` line: 5 in A, 5 in B, 1 in C, plus more in the
  supplements (mostly defs). Their axiom closure follows from the scan above, not from a
  printed check.
- Short names shared by two modules (`stoppedPol`, `famChan`, `hist_congr`, `trunc_correct`,
  `qStar`, `value`, …) are always cited next to their module, so they are unambiguous.
- `AUDIT_lean_citations.py` passes after this round's edits.
- All six PDFs rebuild with rc = 0, and no citation or reference is undefined.
- A rendering defect is fixed. Lean names containing `₀` printed without the glyph. The
  preamble now maps `₀` to a subscript 0 via `newunicodechar`.

**Gates.**
- `full7_20260925` covers 219 modules. At 10:40 it had 180 built with 0 failures, and it is
  still running.
- `smokeR2_20260925` covers 96 modules, the closure of the four round-2 modules. At 10:40 it
  had 82 built with 0 failures, and it is still running.
- The build records in the supplements are final only once both logs report.

**Statement-level re-checks this round (Lean vs manuscript).**
- `sacrifice_cost_law`, `dilution`, `dilution_small`, and `sacrifice_law_stopped` with
  `CorrectA` and `expCntSt`. These match Theorems `thm:sacrifice`, `thm:dilute` and
  `thm:sacstop` of paper A. The counts are over real cells only (`Sum.inl e`); the dummy query
  is not counted.
- `odd_frontier`, `expost_even`, `expost_odd`, `collapse_upper`, `collapse_lower` and
  `collapse_all`. These match C's Theorems `thm:odd`, `thm:expostband` and `thm:collapse`. The
  collapse results are for odd `m = 2s+3` only, and the paper says so.
- `famChi_v_le` and `famChi_u_le`, with the model `famDens`/`famChan`:
  - The bound holds uniformly over probes with `Σ|a_i| ≤ 1`.
  - The constant `Cv r σ h₀` does not depend on the probe.
  - The observation is `3u z₁ − 2z₂ − 2z₃ + v·∏z_tail + h⟨a,z⟩ + ξ`.
  - The channel is a finite menu `Fin (k+1)` with a pure-noise dummy.
- Older theorems were not re-read line by line this round. Their fidelity rests on the claim-map
  audits of 2026-09-24/25.

**Experiments.**
- No experiment was re-run or re-audited in this round.
- The last result-to-algorithm audit covered `paperA_deployable_paired.json`
  (sha256 `5d4a41db…`, with its provenance note) and `paperA_frozen_proxy_exact.json` (7/7
  exact), both earlier on 2026-09-25.
- Nothing in this round depends on a numerical result.

**Primary sources read or re-read this round.** Each finding below was checked against the
source itself.
- Huang, arXiv:2608.02267.
  - Cost-weighted certification constant `C_i = min Σ g_i(a) n_a` subject to
    `Σ n_a KL ≥ 1` against every alternative.
  - Lower bound `C_i·kl(δ,1−δ)`; CTS matches as `δ→0`.
  - Fixed kernel, finite class, losses not observed.
  - "Switching and repair remain outside the fixed-kernel guarantees."
- Yang–Tan–Jin, arXiv:2409.18909: regret before stopping in δ-PAC best-arm identification.
- Overstall, arXiv:2003.07315. If the reduced objective lacks enough global maxima, the
  designs maximising expected FIG lead to non-identifiability. This is conditional, and it
  covers every maximiser.
- Bennouna et al., arXiv:2505.21692.
  - Definition 1: recover the optimal set for every `c ∈ C`.
  - Theorem 1: sufficiency holds if and only if `Δ(X,C) ⊂ span D`.
  - Noiseless, offline; Proposition 3 covers small noise.
  - This paper was not cited in A before this round; A cited the different 2026 paper
    arXiv:2602.15365.
- Javdani et al. 2014, §3.2. The splitting hyperedges are multisets of `k` subregions that
  no single decision region contains, and cutting all of them is necessary and sufficient.
  Tests are noise-free, and the greedy policy is competitive with the optimal one.
- Singh–Kempe–Joachims 2021, Definition 2.1. φ-fairness is imposed for every agent and every
  position `k`, on top-`k` probabilities.
- Disser–Klimm–Schewior–Weckbecker, ICALP 2023: competitive ratios.
- Bienkowski et al., arXiv:2606.28558: 1.373-competitive, and no algorithm can beat 1.25.
- Koike–Lin–Wang, arXiv:2204.11438: joint mixes.
- Shukla–Basu, arXiv:2412.02988: a convex relaxation of the lower bound.
- Qin–You, arXiv:2310.19319: dual-directed design. The abstract does not describe a
  finite-union-of-convex decomposition, so no such claim is attributed to it.
- Bibliographic data verified: Kaufmann–Cappé–Garivier (JMLR 17, 1–42), Donoho–Liu II (AoS
  19(2), 633–667), Naghshvar–Javidi (AoS 41(6), 2703–2738), Le Cam 1973 (AoS 1, 38–53), Birgé
  1983 (ZW 65, 181–237), Rotnitzky–Cox–Bottai–Robins (Bernoulli 6(2), 243–284), Heinrich–Kahn
  (AoS 46(6A), 2844–2870), Ho–Nguyen (arXiv:1501.02497), and Jourdan et al. (ALT 2021, PMLR
  132, 805–849).

## 2. Is the mathematics closed?

**Closed.** Every theorem the six manuscripts state as proved has a compiled Lean theorem at
the paper's objects, under the stated hypotheses.

The ledger's closed items are:
- C: C1, C2 (with the window, via `collapse_all`) and C3.
- A: A1, A3, A4, A5, A6-lower, A6-spreading, A-S and A-STOP.
- B: B1, B2, B5, B-KLH and B-SAFE.

**Open**, and stated as open in the papers:

| Item | What is missing |
|---|---|
| A2 | Rate and correctness of the *shipped* learner under finite precision. Theorem I is conditional on `hgood`, `hinit`, `hEsum` and `hsup`. |
| A6 constant | Lower `8rMD` against the ideal learner's `N₀ ≤ 128(4+2rM)/9·log(1/δ)`: a factor `32/9 + 64/(9rM)`. Also open: whether interleaving during the run lowers the budget below `N₀`. |
| P-7 (optional) | The upper side of `sup KL ≍ h⁶ + η²h⁴` on `Q_η`. |

**Scope, not gaps.** The papers must keep saying these; after this round they do:
- A: one construction carries the rates and learners. The second class has both mispricing
  directions but no learners.
- B:
  - The lower constant is `1/(|W|−1)` and the upper one is `|W|² log|W|`.
  - The world set is finite and the menus are finite.
  - The upper sides need the decoder's probes in the menu.
  - Constants depend on `r` and `σ`.
  - A continuum of probes is not covered.
  - `t*` is coarser than the characteristic time.
- C: the collapse theorems hold for odd `m` only. The constants `1/16` and `10` are not tight
  (Θ only). The family is specific.

## 3. Novelty assessment

**Overall.** This is not a breakthrough, and it is not patchwork. Each paper asks one sharp
question and proves an exact or two-sided answer, machine-checked. All three reuse classical
machinery:
- change of measure;
- Track-and-Stop and characteristic times;
- Le Cam–Birgé tournaments;
- flow decompositions.

In each paper the new content is a specific quantitative relation that the machinery does not
produce by itself. The Lean formalisation raises trust; it is not a statistical contribution.

**Paper A.**
- *Inherited:*
  - the KL game, GLR stopping and tracking;
  - "a proxy can select a non-identifying design", even at every optimum (Overstall,
    conditional);
  - decision-focused acquisition (Wan et al.);
  - exact data sufficiency (Bennouna 2025);
  - pricing identification in a second currency (Yang–Tan–Jin; Huang 2026, a cost-weighted
    characteristic time).
- *New:*
  - a correct model with a valid test and an unchanged decision, where only the frozen
    alternative geometry is wrong;
  - that geometry misprices by an unbounded factor in both directions, after optimisation
    (`Θ(1/rM)` on one class, `≥ M/96` on another);
  - the near-optimal leak `64ε/(9rM)`;
  - the repair frontier `Θ(β/rM)`;
  - the policy budget `N·sac(w̄) ≥ 8rMD`, which is two-sided up to `32/9`, also holds for
    a.s. stopping, and can be spread by padding;
  - the forcing law.
- *Comparison with cost-weighted certification.*
  - `sac` is convex in the design, so `N·sac(w̄) ≤ Σ_e N_e·sac(1_e)`. The budget therefore
    implies a Huang-type cumulative-cost bound with cost `g(e) = sac(1_e)`, but not
    conversely.
  - The currency is the surrogate's own concave value, and the object is the repair Huang
    leaves open.
- *Weak points:*
  - Everything rate-level is on one construction; no general characterisation says when a
    frozen surrogate misprices.
  - The `Ω(log²)` learner separation is the forcing law at `a = 1/2`. Its content is proving
    that the two learners satisfy the pathwise hypothesis, not the exponent.
- *Verdict:* a coherent, defensible chain (A1→A5), narrow in scope. The strongest pieces are
  the frontier and the budget.

**Paper B.**
- *Inherited:*
  - obstructions, which are exactly Javdani's splitting hyperedges;
  - the change-of-measure inequality (Kaufmann–Cappé–Garivier);
  - controlled sensing (Chernoff; Naghshvar–Javidi);
  - multiple-answer characteristic time (Degenne–Koolen);
  - Hellinger tournaments (Le Cam, Birgé);
  - rates governed by Hellinger moduli (Donoho–Liu);
  - an order of degeneracy fixing a rate (Rotnitzky et al.; Heinrich–Kahn; Ho–Nguyen);
  - high-order masking (Grosso–Standaert–Prouff, Rioul et al., Duc et al.).
- *Derivation recorded here.* For `w` in an obstruction attaining `t*` and any answer `a` safe
  at `w`, some `v` in the obstruction makes `a` unsafe. Hence
  `Σ_q w_q KL_q(w,v) ≤ κ(w,v) ≤ t*`, so the Degenne–Koolen time satisfies `T*(w) ≥ 1/t*`.
  Their `δ→0` bound therefore already implies B's lower law in that limit, without the
  `1/(|W|−1)`.
- *New:*
  - the lower law at every `δ` and `h` jointly, which the `h→0` order law needs;
  - the matching Hellinger upper side on every channel;
  - the order law `s* = max_{obstruction} min sep`: the same separation matrix gives the min
    for overlapping answers and the max for identification;
  - two channels where both rates are two-sided against every a.s.-stopping policy, with an
    arbitrary exponent gap on the parity channel;
  - on the latent family, a uniform bound over the whole unit-`ℓ₁` probe class, so the gap is
    not an artefact of one bad query;
  - safe sets derived from losses.
- *Verdict:* the most substantial of the three as a law. It is a new combination with tight
  examples, not new tools.

**Paper C.**
- *Inherited:*
  - randomised rankings with all-prefix marginal constraints (Singh–Kempe–Joachims);
  - prefix representation (Celis et al.);
  - ex-ante versus ex-post (Freeman et al.);
  - flow decomposition (Schrijver);
  - one order for all budgets (incremental maximization);
  - dependence optimisation for unknown subsets (Koike–Lin–Wang);
  - `max E ≤ E max`.
- *New:*
  - the objective depends on the joint law of each prefix, not on marginals; the
    `(+1,+1,−1,−1)` example gives `0` versus `1`;
  - exact frontiers at every size (C1 even, C2 odd, the kink at `η_t = 1 − 2/m(m−1)`);
  - the exact banded ex-post value;
  - the non-multiplication of band and timing (band ≤ `1+1/m` ex post, against `Θ(m)` ex
    ante for odd `m`);
  - the collapse scale `Θ(min(m, 1/ε))`.
- *Verdict:* the cleanest exact package. Its limitation is the specific family.

## 4. Review of the external comparison (COMPARISON.md, 08:05)

Accurate, and adopted:
- A: the formulas A1–A5 and their Lean anchors; that Overstall's "every optimizer" quantifier
  exists; that Bennouna 2025 has `Δ ⊂ span D`; that Wan et al. Theorem 3.2 covers
  decision-blind failure; that Jourdan and Degenne–Koolen supply attainability.
- B: that obstructions are Javdani's; that order-to-rate is known (Ho–Nguyen, Rioul, Duc);
  that `t*` is coarser than Degenne–Koolen; the Donoho–Liu positioning; the finite-menu,
  decoder-probe, `r` and `σ` scope.
- C: the formulas C1, C2 and C3 (re-derived and matched to Lean); the joint-law example; the
  incremental-maximization and Koike–Lin–Wang positioning; the reading of the robustness
  quantifier.

Superseded by results proved after 08:05:
- "The tournament remains conditional on pairwise testability."
  - `hellinger_tournament` is unconditional in `t*_H` (`LeanPaperBHellingerTestV1`).
  - Comparability is proved on both channels (`LeanPaperBHellingerFamilyV1`,
    `LeanPaperBHellingerParityV1`).
- "The family safe correspondence is used … the physical-loss identification must remain
  distinguishable." `famSafe_derived` (`LeanPaperBFamilySafeV1`) derives `famSafe` from the
  losses, for `r ≥ 2` and `0 ≤ ε < 1`.
- "The operational law at every small β does not follow from the static frontier."
  - `dilution` and `dilution_small` show that for every `N ≥ N₀`, in steps of four, a δ-correct
    policy has `sac ≤ N₀/N`, so `N·sac = Θ(rM log(1/δ))` at every sacrifice level.
  - What is still open is the constant, and whether the sacrifice can be spent *usefully*.
    The padded queries carry no decision information.
- The C robustness pieces are joined by `collapse_all`: `≥ min(m−1, 1/ε)/16` on
  `0 < ε ≤ 1/6`, with no window.

Needing qualification:
- The C robustness statements hold for odd `m` only.
- B's "m arbitrary" exponent gap is for each fixed `m`. The constants depend on `m`, so `m`
  cannot grow with `1/h`.
- The comparison does not list Huang 2026 or Yang–Tan–Jin, which are the nearest prior work for
  A's budget. It also does not list Kaufmann–Cappé–Garivier, Le Cam–Birgé, Rotnitzky or
  Heinrich–Kahn for B.

## 5. Edits applied this round

Pre-edit copies are in `legacy/manuscripts_pre_rewrite_20260924/*_pre_novelty_20260925.tex`
and `legacy/OPEN_MATH_20260924_pre_novelty_20260925.md`.

- **paper_a.tex.**
  - Prior work now credits Garivier–Kaufmann, Kaufmann–Cappé–Garivier, Jourdan et al. and
    Shukla–Basu.
  - Overstall's every-optimum result is stated as conditional and known.
  - Bennouna 2025 is added with `Δ ⊂ span D`.
  - A paragraph on second-currency pricing is added (Yang–Tan–Jin, Huang).
  - Table rows are fixed: the Overstall row now claims only the leak and the bracket, and
    Bennouna and cost-weighted rows are added.
  - Limitation 2 now says the padded queries carry no decision information.
  - Six bibitems are added.
- **paper_b.tex.**
  - Prior work adds Javdani's hyperedges as obstructions, Chernoff, Naghshvar–Javidi,
    Kaufmann–Cappé–Garivier, Le Cam–Birgé, Donoho–Liu, Rotnitzky et al., Heinrich–Kahn and
    Ho–Nguyen.
  - A new paragraph notes that `T*(w) ≥ 1/t*`, so the `δ→0` limit follows from Degenne–Koolen,
    and states what does not follow.
  - Table rows are fixed and added.
  - The abstract and results say "up to factors in `|W|`".
  - Limitation 3 gains the finite-menu, decoder-probe, `r`/`σ` and no-continuum sentences.
    Limitation 4 adds `σ`.
  - Nine bibitems are added.
- **paper_c.tex.**
  - Prior work adds Singh–Kempe–Joachims' all-`k` top-`k` constraint, incremental
    maximization (Disser et al., Bienkowski et al.), Koike–Lin–Wang, and the joint-law
    example.
  - Two table rows and three bibitems are added.
- **Supplements.** Ambiguous slash fractions became `\frac` in paper_c_supplement (`2/D(m-1)`,
  `4/mD`, `1-2/m(m-1)`, `(m+3)/m(m+4)`, …) and paper_b_supplement (`T`).
- **preamble.tex.** The `₀` glyph is mapped.
- **OPEN_MATH_20260924.md.** The stale "Open: comparability" note is closed, and the sweep is
  recorded.

## 6. What would move the programme from "defensible" to "strong"

1. **A.** A general theorem, not a construction: a condition on the frozen and true alternative
   sets under which `Γ_true/Γ_fr` and the repair frontier are determined. For example, the
   starvation mass needed per strict alternative, in terms of the cells the freeze drops. Then
   the construction becomes the tightness example.
2. **A.** Close the `32/9` constant, or show that a policy can spend the sacrifice on
   informative queries.
3. **B.** Remove or match the `|W|` factors: the lower `1/(|W|−1)` and the upper
   `|W|² log|W|`. A result that `t*` is instance-optimal up to absolute constants on graded
   channels would make the law sharp.
4. **B.** A continuous query kernel bridge, so the latent family covers adaptive real-valued
   probe choice.
5. **C.** Even-`m` collapse, and tight constants in `Θ(min(m, 1/ε))`.
6. A single consolidated claim map (statement → theorem → scope → figure/JSON), still pending.
