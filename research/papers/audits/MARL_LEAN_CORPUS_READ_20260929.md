# Lean corpus and paper read for the E3 problem (29/09/2026, written 01:14 EDT, clock-checked)

Scope: every module header (title, WHAT IS PROVED, WHAT THIS DOES NOT ESTABLISH) and theorem-name list of the 776 modules in work/p13_conjectures (work/p12 is the frozen baseline: same modules), THEOREM_MAP.md, the abstracts of the ten papers, and the MARL manuscript's theory/method/E3 sections. Proof bodies were NOT read line by line (they are machine-checked by the gates; statements and hypotheses are what applicability depends on). A literal line-by-line reading of ~250k Lean lines would need subagents (the user's 'fetch' rule).

E3 problem (as of L-81): scheduler headroom = best-of-N over (plausible) action perturbations of an imperfect actor;
legal critics at chance; 3-step label vs full-episode mismatch; actor fragility sets the sign; F1/DFL/normaliser/cache all ruled out.

## MARL (19 modules)
- SafeEdit: edit only if est. gain > 2eps => never harms; 2eps sharp; "with 2eps above every gain it never edits".
  -> E3 code uses tau tuned on SELECT (max gain), NOT 2eps; eps never estimated. With eps >> gains the safe rule = prefix.
- EstimatedRevision.deployed_regret: f T - f S^ <= 2(delta+u)(|P\T|-R)+ + 2eps + nu + zeta.
- SubsetFrontier / RevisionFrontier / BlockFrontier: a good repair EXISTS within (d-R)+ * 2delta (value tables; not expected return).
- RepairCalibration (needle class): per_repair_lower, calibration_lower |Amb|*D <= E0[rollouts]*beta^2/2,
  zero_allocation_impossible (never rolling out an ambiguous repair => not acceptable), calibration_upper (targeted block LR tests).
  CalibrationGap: log|Amb| factor for fixed schedules; PairCalibration: shared interaction; Starvation: symmetric design cost (C(m,k)-1)D/(beta^2/2).
  -> E3 = NEEDLE regime at deployment: the value of a candidate is idiosyncratic (L-81), zero rollouts at deployment =>
     zero_allocation_impossible is the theorem-level reason a legal selector cannot beat the prefix in the worst case.
- ProxyBlindness: first-order info cannot choose the right 2-set; one pair query suffices (power suffices, info does not).
- Tabulation: per-budget table dominates revision (value side).  GenericRecourse/MenuRevision/XorGame: commitment prices, B<=V^R<=U.
- E1bRealization/Uniform: actor realisation for the E1b decoder only (not traffic).

## Paper A (91 modules): "optimising a surrogate can cost the decision"
- Separation Gamma_true/Gamma_fr in [4/(4+2rM), 64/(9rM)]; sacrifice law N*sac(w) >= 8rM*D; forcing law.
- A6: a learner that follows / RE-SOLVES the surrogate's optimum starves the middle cells: E tau >= (KM/8)^2 log^2(1/delta)
  vs O(log(1/delta)) for the ideal learner.  Mechanism: forcing 1/sqrt(s+1) is the ONLY source of queries on starved cells.
- A7: ideal learner (Track-and-Stop with GLR stop, forcing, oracle of the estimate), delta-correct for every learner (Ville),
  upper rate log(1/delta)/(Gamma-eta)+A; answer stabilisation via Lipschitz VALUE (Degenne-Koolen), no optimiser continuity.
  -> E3 analogue: training/acquisition on the prefix trajectory = surrogate design; decision-relevant states/candidates starved;
     only forced exploration (off-prefix edits in the actor/label data = the MIX actor) samples them.  Qualitative only:
     A's theorems are about Gaussian cells with a fixed design, not E3.
- A frontier/repair: R(b) = sup{J_t(w): sacrifice(w) <= b}, concave; the mixture (1-beta)*surrogate-optimal + beta*uniform
  on starved cells buys back Theta(beta/(rM)) true information; RepairV1: a CHECKABLE condition under which the surrogate
  is exactly right; SacrificeDuality: dual margins of the surrogate price the repair.
  -> E3 reading: the MIX actor (p_mix = 0.5) is literally the beta-mixture on the ACTOR side; it bought edit-robustness
     (random edits ~0) at the price of prefix message value (G1: +4..7% -> -0.9%).  No theorem transfers; analogy only.

## Paper B (79 modules): safe decision vs identification, obstruction law
- ObstructionLaw: obstruction = set of worlds with no common safe answer; every policy that is safe w.p. 1-delta pays
  E N * t* >= ((1-delta)/(|W|-1)) log(1/delta) - log 2 (ChiStar removes 1/(|W|-1)); Hellinger tournament attains
  |W|^2 log(|W|/delta)/t*_H (ShareTournament: |Q| blocks instead of |W|^2).  Graded channels: t* = C h^{2 s*}.
- SafeOrder / DecisionOrder / Visible: deciding safely needs only the order at which obstructions separate; identifying
  needs the (higher) identification order: Theta(log(1/delta)/h^2) safe vs Theta(log(1/delta)/h^{2r}) identify.
- PrivateQuery: worlds 0..k, only query j separates world j from world 0 => any law in t* must pay the NUMBER of queries.
- QueryDesign: choosing a sub-menu of queries to reach a decision order = hitting set (NP-hard; greedy H_n).
  -> E3 reading: (i) the scheduler does not need to IDENTIFY the best edit; it needs a SAFE decision (never worse than
     the prefix by more than eps).  "Prefix" is a common safe answer only if no needle exceeds eps; E3 has needles
     (oracle +12..16), so {prefix-is-best world, needle-at-c worlds} is an OBSTRUCTION; resolving it needs information
     that separates those worlds at deployment.  Legal features separate them at chance (L-80, F1) => order effectively
     infinite => the only safe policy is the prefix (matches SafeEdit and the closed-loop results).
     (ii) PrivateQuery is the E3 regime: a candidate's value is revealed only by querying THAT candidate (L-81).

## Paper C (98 modules): commitment before the budget, band (exposure) constraint, recourse
- Exact frontiers V_m(eta) (even/odd), ex-post V^post = 2/(m+4) = (m-1) x ex-ante V_free (choose budget after draw),
  budget-aware B, universal U, recourse V^(R): one exchange reaches B on g_m (recourse_one_even/odd);
  stability |V(g)-V(g')| <= 3||g-g'||_1/d, but the PRICE RATIO collapses Theta(min(m,1/eps)) under perturbation eps.
  -> E3 reading: E3 is a C-type protocol (commit prefix before K, revise R edits after).  C says one exchange SUFFICES
     structurally (matches the E3 oracle: one swap has +12..16 headroom) and that the value is stable in the weights but
     its RATIO to the free value is fragile.  C assumes the cost table is KNOWN; it says nothing about learning which
     exchange, which is exactly where E3 fails.  Ex-post factor (m-1) is C's E-max vs max-E; E3's hindsight gap was small
     (arrivals only), so C-H5' is not the E3 bottleneck.

## Support (39): decide vs recover; passive certification
- RecoverySandwich/DecideRecover: safe decision R* = Theta((1 - sum_i p_i)^N) vs full recovery Theta((1 - min_i p_i)^N).
- PassiveDecisionMass: with an anchor of mass 1-eta and a dangerous tip of mass eta, NO passive uniformly-correct
  procedure can stop at the anchor-only world (eta can be pushed below any transcript threshold); certification needs a
  hypothesis on the MASS of the dangerous region.  PassiveSamplingMass: region of mass >= gamma missed by N iid draws w.p.
  (1-gamma)^N.  ParityBundleSize: how many queries must be acquired TOGETHER before any moves the decision (XOR).
  ObstructionQueryOrder/UnboundedObstruction: obstruction order does not determine query cost.
  -> E3 reading: the selector is a PASSIVE learner on logged prefix-trajectory states; the decision-relevant states
     (where one specific edit is a big win / a big loss) have small mass in that log; PassiveDecisionMass says a passive
     procedure cannot certify "prefix is safe" or "edit c is good" without a mass hypothesis on that region.  The dense
     labels (F1: 3.2x states, t = 4..22) raise the mass of early states but not of the idiosyncratic needle => no gain,
     consistent.
## Query (21): Hellinger order H^2 ~ h^{2r} => N* = Theta(h^{-2r}); InterventionFloor: deterministic minimax is NOT a floor
   for randomised procedures (factor 1.456 on the witness); RegretBridge gamma*e <= R <= L_max*e (test error -> regret).
## Master (11): calibration/anchor price: an anchor query (profiles out a common offset) is MANDATORY above a price
   threshold; a group of calibration queries beats every single one only if the nuisance has rank >= 2.
  -> E3: the paired label (candidate minus prefix at the same state) is exactly an anchor that removes the state offset;
     the trainers already anchor (p - p[0]).  No new lever.

## Structural (50): prefix-cover dimension / menu law, V_avg vs V_path
- AvgPathGap/Saturation: avgVal = max_k E_P r_k (guarantee on average per budget) <= pathVal = E_P max_k r_k (on
  execution) <= b * avgVal, attained (b = number of budgets).  Prefix-cover dimension unbounded (staircase family),
  O(1/eps) normalized tolerance law; one ranking within 1/2 at every budget on the staircase (approximation robust).
  -> E3: the pre-registered 3-step label is an "average over budgets/steps" object; the closed loop is an execution object;
     AvgPathGap is the structural statement that the two can differ by up to the number of steps (26), with equality
     attained - the sign of what L-73 measured (g3 captures -32..68% of the full-episode best).  Analogy, not a proof.
## Adaptive (13): tracking, online quota fails (no online rule keeps deficit < 1), layer-cake stopping; join of scheduler,
   revalidation and stopping.  Methodological, no E3 lever.
## Functional (37): range/extrema oracle, contrast design (effective resistance), scalar proxy wrong both ways by no
   constant (F05), CertificateLifetime under deterministic POLICY DRIFT, Residual/SelectiveMaintenance (safety conditional
   on coverage + stated future-error bound).

## D6 (267): product-reference compression, mixed differences (interaction), discovery/allocation/revalidation
- SharpMarginThreshold: a cut margin >= 2 delta (delta = mixed-difference bound) is universally sufficient for the
  Top-C/first-order choice to be optimal; matching witnesses at every margin in [1,2).  (Same shape as MARL subset_zero_price.)
- FirstOrderInsufficiencyWitness V1/V2: two worlds with IDENTICAL first-order product responses have DIFFERENT optimal
  retained sets (any singleton controller fails) => escalation to interaction queries is necessary.
- (m-1) decision-interaction law refuted (binary/ternary counterexamples); rank-one interaction profiles characterised.
- Discovery -> allocation -> revalidation epochs; forced scalar exploration supplies information (ScalarExplorationSeparation).
  -> E3 reading: E3's value is NOT first-order in the senders (L-81: the joint action induced, i.e. an interaction of the
     delivered message with the receiver's private state and the actor), and the cut margins are tiny (share within 1 of
     best 1.4-5%); D6/SubsetFrontier's sufficient condition (margin >= 2 delta) fails, and FirstOrderInsufficiency is the
     formal reason first-order (legal feature) learners cannot pick the optimum in the worst case.

## Other / unified (51): typed certificate completion (TCC) and typed obstructions
- TCCResponseScoreSeparation: two response worlds keep ALL non-response evidence fixed and swap the unique optimum =>
  a controller that cannot observe response/score evidence cannot be universally zero-regret.
- TCCQuerySeparation: identical complete pairwise-response summaries, interaction-query targets separated by 4.
- TypedObstructionIndispensabilityCalculus: independent obstruction scopes assemble into a product instance; deleting any
  one unresolved evidence type leaves an obstruction.  UnifiedObstructionOrder: decide without identifying (law).
  -> E3 reading (the closest formal match): the E3 privileged arm is exactly RESPONSE evidence (the counterfactual joint
     action each candidate induces); the legal scheduler lacks it; TCC-response says no controller without that evidence
     type is universally zero-regret.  The E3 data (legal ~ chance, privileged +1.6..2.2 offline) is the empirical face of
     this obstruction.  Caveat: TCC is a deterministic worst-case witness, not an E3 theorem.

## Paper abstracts (7 older): the one closest to E3 is MASTER's NECESSITY DICHOTOMY: configurations where every ordinary
   query has identical means in two worlds with different answers => attainable value exactly 0, no amount of ordinary
   sampling helps; admitting a priced calibration query gives an exact price law Gamma* = Delta^2/(2K(sqrt(vm)+sqrt(nu kappa))^2)
   and a crossover nu*kappa = v*m.  E3 analogue: legal features = ordinary queries (value ~0, L-80/F1); a response bid =
   the priced calibration query (M1 on MP2: +1.85, 18% of oracle, preregistered).  Support: deciding is cheaper than
   identifying (coupon collector vs L/(a+L)).  Structural: V_path/V_avg = m-1 exactly.

## CORRECTION (29/09, 10:50, after the user's review) — read this before any "E3 reading" line above
Every "-> E3 reading" line above that says E3 IS in a theorem's regime (needle class, PrivateQuery, TCC-response
obstruction, MASTER's necessity dichotomy, first-order insufficiency) or that a theorem is "the formal reason" legal
selectors fail OVERREACHES.  Those theorems are statements about their own model classes (finite worlds, Gaussian
channels, offset models).  No module states or proves anything about CityFlow/E3, and E3 has not been shown to satisfy
their hypotheses.  What is legitimate: the E3 observations have the same shape (value concentrated in a few candidates;
first-order/legal features rank at chance; response-type privileged evidence helps offline).  "Legal information cannot
suffice for E3" is NOT established.  The one directly usable statement remains SafeEdit's rule, conditional on an eps
that has not been certified for any E3 critic.  See ledger L-86.
