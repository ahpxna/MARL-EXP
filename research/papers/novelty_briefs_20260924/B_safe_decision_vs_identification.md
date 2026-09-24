# Brief B — "How far you must observe to decide, not to identify"

Read `00_PROTOCOL.md` first. Manuscript: `research/papers/_tex/paper_b.tex`. Claim map:
`research/papers/THEOREM_MAP.md`.

**Place in the programme.** The price of solving the wrong intermediate problem: here,
distinguishing more worlds than the decision needs. Generic "decide without identifying" and
pairwise testing are established. The contribution must be carried by the *same-model*
separation of observation order and cost, and by the boundary where richer measurements
change the exponent.

## 1. The objects, self-contained

- **Worlds and safe answers.** A finite set of worlds `w`, each with a set of safe answers
  `A_w`. The safe sets are computed from a compression loss (`selectedRadius`), not posited.
- **Unsafe sets.** A set of worlds `H` is *unsafe* (an obstruction) when no answer is safe in
  all of them: `∩_{w∈H} A_w = ∅`.
- **Queries and resolving order.** An admissible query class. The resolving order
  `r(θ, λ)` is the first order in the perturbation scale `h` at which some admissible query
  separates the observation laws of `θ` and `λ`.
- **The two orders.** The combinatorial law is

      s_safe = max over unsafe H of ( min over distinct θ, λ ∈ H of r(θ, λ) ),
      s_id   = max over distinct θ, λ of r(θ, λ).

  A pair that is hard to separate costs nothing if the two worlds share a safe answer; the
  difficulty sits in groups of worlds with no common answer.
- **Zero-query floor.** If `δ ≥ 1/m` for the tip family `A_w = [m] ∖ {w}`, a random answer is
  already safe with probability `1 − 1/m`, so no positive rate can hold there.

**Two observation models, kept separate.**

1. **The raw-F four-world family** `F_{u,v}(z) = 3u z₁ − 2z₂ − 2z₃ + v ∏_{ℓ≥4} z_ℓ` on
   `{−1,1}^{r+3}`. The observation is `Y = F(Z) + h·g(Z) + ξ`, with `Z` latent, `g` a bounded
   linear probe and `ξ ~ N(0, σ²)`.
2. **The m-world parity-membership channel.** Query `j` returns

       Y_j = v(j,w) ∏_{ℓ≤j} Z_ℓ + (h/j) Σ_{ℓ≤j} Z_ℓ + ξ,     v(j,w) = −1 iff j = w,

   with `Z` uniform signs and latent. Safe answers `A_w = [m] ∖ {w}`.

## 2. Headline claims

| id | claim | quantifiers / scope |
|---|---|---|
| **B-H1** | **Combinatorial order law**: at order `s` there is a safe decision iff no unsafe set is "together" (no pair in it resolved) at order `s`. This gives the `s_safe` formula; minimal obstructions suffice. Against an obstruction, every *randomised* rule leaves unsafe mass at least `1/|H|`. | Finite worlds. Distinct-pair semantics; the diagonal was a bug, now fixed. |
| **B-H2** | **Moment/order law on bounded linear probes** (raw-F family): for every admissible query of degree `d`, the mixed moments against the hidden character vanish below order `⌈n/d⌉`. The averaged tail query attains that order with leading coefficient exactly `r!/r^r`. | Uniform over the admissible class, with a query-independent constant. |
| **B-H3** | **Same-channel separation** (parity channel): the minimax expected number of queries is `Θ(log(1/δ)/h²)` for the safe decision and `Θ(log(1/δ)/h^{2(m−1)})` for identification. Both hold against every randomised adaptive policy with a finite horizon, uniformly on a rectangle `h ≤ h₀`, `δ ≤ δ₀`. The upper sides are concrete decoders using bounded statistics `cos(Y)`/`sin(Y)` and Hoeffding. | Fixed `m ≥ 3` and `σ > 0`, with constants depending on them. The safe hard pair is derived from the algorithm's own output distribution: some `v ≠ w₀` has `P_{w₀}(answer = v) ≥ (1−δ)/(m−1)`. Continuous Gaussian observations. |
| **B-H4** (optional upgrade, not done) | **Query-class boundary**: widening the class to `Q_η` (linear plus `η`·quadratic) gives `sup KL ≍ h⁶ + η²h⁴`, a phase change at `η ≍ h`. | Not yet a theorem. The artifacts contain one probe only. |

## 3. Already conceded — check that our description of each is fair

- Javdani et al., "Near optimal Bayesian active learning for decision making", AISTATS 2014:
  overlapping decision regions, deciding before identifying.
- Masking and high-order leakage:
  - Grosso, Standaert, Prouff, "Low entropy masking schemes", 2014;
  - Duc, Faust, Standaert, "Making masking security proofs concrete", EUROCRYPT 2015 / IACR
    ePrint 2015/119;
  - Rioul, Cheng, Guilley, "Cumulant expansion of mutual information", 2021.
- Degenne & Koolen 2019 (multiple correct answers) and Wang & You 2026: the information-game
  framework.
- O'Donnell, *Analysis of Boolean Functions*.
- Tsybakov, *Introduction to Nonparametric Estimation* (Le Cam, Fano).

## 4. Candidate collision zones

**Z1. Masking order ⇒ sample cost. Highest risk for the identification side.**
Candidates:

- Chari, Jutla, Rao, Rohatgi, "Towards sound approaches to counteract power-analysis
  attacks", CRYPTO 1999: the number of traces grows exponentially in the masking order;
- Prouff & Rivain, "Masking against side-channel attacks: a formal security proof",
  EUROCRYPT 2013;
- Duc–Faust–Standaert 2014/2015;
- Standaert, Malkin, Yung, "A unified framework for the analysis of side-channel key recovery
  attacks", 2009.

Questions:

- (a) Does `Θ(log(1/δ)/h^{2(m−1)})` for identification on the parity channel follow, after
  relabelling, from a known "d-th order masked secret needs `Ω(σ^{2d})` traces" theorem?
- (b) Does the side-channel literature contain the SAFE-decision side: overlapping acceptable
  answers, a lower order than identification, on the same leakage? If not, B-H3's novelty is
  the pairing of the two tasks on one channel with matched upper and lower bounds.

**Z2. Moment matching ⇒ small divergence (mixtures and SQ).**
Candidates:

- Chen, "Optimal rate of convergence for finite mixture models", Ann. Statist. 1995;
- Heinrich & Kahn, "Strong identifiability and optimal minimax rates for finite mixture
  estimation", Ann. Statist. 2018;
- Wu & Yang, "Optimal estimation of Gaussian mixtures via denoised method of moments", Ann.
  Statist. 2020;
- Moitra & Valiant 2010; Hardt & Price, "Tight bounds for learning a mixture of two
  Gaussians", STOC 2015;
- Diakonikolas, Kane, Stewart, SQ lower bounds via moment matching, FOCS 2017.

Question: is "if the first `s−1` coefficients agree then `χ² ≤ C h^{2s}`, and a test attains
it" a known lemma? It likely is. Then B-H2's claim must rest on uniformity over the
admissible query class, the exact constant `r!/r^r`, and the vanishing threshold `⌈n/d⌉` for
degree-`d` probes. Check whether that threshold is known (it resembles Fourier-degree
arguments; see O'Donnell).

**Z3. Decision easier than identification: exponent separations.**
Candidates:

- Degenne–Koolen 2019 (examples where the any-correct-answer cost differs from identification);
- "good arm identification" (Kano et al., 2019);
- thresholding bandits (Locatelli, Gutzeit, Carpentier, 2016);
- active hypothesis testing with composite or overlapping hypotheses (Naghshvar & Javidi,
  Ann. Statist. 2013);
- controlled sensing (Nitinawarat, Atia, Veeravalli, 2013);
- testing versus learning gaps in property testing.

Question: is there a theorem showing an *exponent* gap (`h^{-2}` versus `h^{-2k}`) between
deciding and identifying on the same observation channel?

**Z4. Parity and SQ learning.** Learning parities with noise; SQ dimension; the fact that a
k-sparse parity needs correlation of order k. Question: does a known SQ or low-degree result
give B-H3's identification lower bound directly, and does the literature separate "decide a
coarse property of the parity" from "identify it"?

**Z5. The obstruction-based safe lower bound.** The step "choose `v` with
`P_{w₀}(answer = v) ≥ (1−δ)/(m−1)`, then data processing and binary KL" resembles standard
Fano/Le Cam arguments for multiple hypotheses and the Degenne–Koolen lower bound. Question: is
this exact argument for overlapping safe sets already written somewhere? If so, cite it and
keep only the channel-specific rate.

## 5. Hostile questions

1. Remove the compression loss and posit the safe sets directly. Is B-H1 then a known result
   on decision regions (Javdani; Golovin, Krause, Ray, "Near-optimal Bayesian active learning
   with noisy observations", NeurIPS 2010; Chen et al., "Submodular surrogates for value of
   information", AAAI 2015)?
2. Is the parity channel equivalent to a known first-order-secure masking scheme with public
   noise? If so, is the safe/identify pair new there?
3. The policy class is finite-horizon. Does the nearest prior lower bound cover all stopping
   times? If it does, and ours does not, we are strictly weaker there and must say so.

## 6. Search strings

- "decision region determination" active learning overlapping
- "multiple correct answers" identification "exponent" OR "order" separation
- masking order "number of traces" lower bound noise "exponential"
- "moment matching" chi-square mixture lower bound "order"
- "statistical query" parity "decision" versus "identification"
- "active hypothesis testing" composite overlapping hypotheses sample complexity
- "controlled sensing" "multihypothesis" decision

Screen the `B_order` and `B_testing` groups of `research/literature_audit_20260921` first.
