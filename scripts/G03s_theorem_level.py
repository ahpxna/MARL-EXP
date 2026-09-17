#!/usr/bin/env python3
"""G03s upgrade: prior comparison verified at THEOREM level, not abstract level.

Each row below records theorem numbers and statements read from the paper itself, the
boundary they leave open, and -- explicitly -- what the reading does NOT settle.  Rows
still at abstract level are carried over unchanged and remain flagged.
"""
import argparse, json
from pathlib import Path

SRC = Path('research/worker_G03_prior_20260915/G03_prior_comparison.json')
OUT = 'research/worker_G03s_theorem_20260915/G03s_prior_theorem_level_v2.json'

VERIFIED = {
 'Structural': {
  'source_read': 'arXiv:2305.01310, ar5iv full text (Disser, Klimm, Schewior, Weckbecker).',
  'theorems_read': [
   {'id': 'Definition (objective class)',
    'statement': 'The objective is a monotone function f : 2^U -> R_{>=0}.  The codomain is '
                 'the NON-NEGATIVE reals.'},
   {'id': 'Definition (accountable)',
    'statement': 'f is accountable if for every X subset of U there exists e in X with '
                 'f(X \\ {e}) >= f(X) - f(X)/|X|.'},
   {'id': 'Theorem 1',
    'statement': 'For every instance of IncMaxCont there is a starting value c1 such that '
                 'GreedyScaling(c1, rho*) achieves the best-possible competitive ratio '
                 'rho* >= 1.'},
   {'id': 'Theorem 2',
    'statement': 'GreedyScaling(c1, phi+1) is (phi+1)-competitive if and only if '
                 'd(c1) >= 1/(phi+1).'},
   {'id': 'Theorem 4', 'statement': 'IncMax has competitive ratio at least 2.246.'},
   {'id': 'Theorem 5', 'statement': 'IncMax admits a 1.772-competitive randomised algorithm.'}],
  'what_is_therefore_prior': [
   'The whole incremental-maximisation programme for monotone accountable objectives: the '
   'upper bound phi+1 ~ 2.618, the lower bound 2.246, and the randomised 1.772.',
   'The idea of one schedule serving every budget.  Structural must credit this.'],
  'what_is_NOT_in_the_prior': [
   'DECISIVE: the objective class is f : 2^U -> R_{>=0}.  The structural family '
   'g_m = (-3, (-1)^p, (+1)^q, 3) has prefix values that go NEGATIVE, so it fails the '
   'codomain restriction before accountability is even tested.  Our objective is not in '
   'the prior class at all -- this is a class separation, not a constant improvement.',
   'The prior guarantee is MULTIPLICATIVE (a competitive ratio).  Ours is ADDITIVE and '
   'normalised by D = sum |g_i| = m+4.  The two are not comparable numbers.',
   'The prior asks for ONE ordering serving all cardinalities.  Ours asks for the MINIMUM '
   'MENU of orderings, and proves the menu size is exactly m-1.'],
  'boundary_Structural_may_claim':
   'The signed-cancellation regime, which the prior class excludes by its codomain; the '
   'ADDITIVE normalised two-sided law V_path/V_avg = m-1 for every m >= 5; and the MENU '
   'formulation.  The incremental-maximisation idea and every multiplicative constant are '
   'cited to the prior.',
  'verified_level': 'theorem', 'theorem_level_verified': True},

 'MASTER (design/duality)': {
  'source_read': 'arXiv:0908.1912v1 (Ann. Statist. 37 (2009) 2056-2082), full PDF, Sections 1-2.',
  'theorems_read': [
   {'id': 'Theorem 2.1',
    'statement': 'sup_xi Delta(xi) = sup_xi inf_{theta2} Delta(theta2, xi) '
                 '= inf_{theta2} ||eta - eta_2(.,theta2)||_infty^2.  Moreover the minimising '
                 'theta2* is a best UNIFORM approximation of eta by the family eta_2(.,theta2), '
                 'Delta(xi*) = ||eta - eta_2(.,theta2*)||_infty^2, and supp(xi*) is contained in '
                 'the set A where |eta - eta_2(.,theta2*)| attains its sup-norm.'},
   {'id': 'Theorem 2.2',
    'statement': 'Assuming the best uniform approximation theta_bar_2 is unique and interior: '
                 '(a) if xi* is T-optimal then the linear system int_A (eta - eta_2(x,theta_bar_2)) '
                 'd/dtheta2 eta_2(x,theta2)|_{theta_bar_2} dxi*(x) = 0 holds; (b) conversely that '
                 'system plus supp(xi*) subset A plus a unique interior minimiser implies '
                 'T-optimality.  This characterises ALL T-optimal designs.'},
   {'id': 'equation (2.4) and the delta^2 calculation',
    'statement': 'The T-criterion Delta(xi) = inf_{theta2} int (eta - eta_2(x,theta2))^2 dxi is '
                 'itself a PROFILED quantity, and the local-alternative noncentrality is '
                 'delta^2 = theta_0^T M_{11.2}(xi) theta_0 with M_{11.2} the SCHUR COMPLEMENT of '
                 'M_{m2} in M_{m1}, with delta^2 = Delta(xi) + o(1).'}],
  'what_is_therefore_prior': [
   'Profiling the nuisance out of a discrimination criterion (2.4)/(2.6).',
   'The Schur-complement form of the noncentrality parameter -- the same shape as '
   'I_u = D_u - M_u^2/(2K).  MASTER must NOT present that shape as new.',
   'A closed-form VALUE for the optimal criterion: Theorem 2.1 gives it as the squared '
   'Chebyshev approximation error.  "We give a closed form" is therefore not by itself a '
   'contribution.',
   'A complete characterisation of the optimal designs and their non-uniqueness.'],
  'what_is_NOT_in_the_prior': [
   'No price or cost attached to an observation TYPE: the design space X is fixed and every '
   'support point costs the same.  There is no parameter playing the role of kappa.',
   'No necessity dichotomy: nothing states when a design problem has value ZERO without a '
   'particular kind of query and positive value with it.',
   'No rate expressed in the structural parameters (number of groups K, group size m, control '
   'price kappa).  The Chebyshev constant is not such a rate.'],
  'boundary_MASTER_may_claim':
   'The PRICE LAW only: (i) the dichotomy Gamma = 0 without a calibration query, exhibited by '
   'the hidden-shift witness; (ii) the exact value Gamma* = Delta^2/(2K(sqrt m + sqrt kappa)^2) '
   'once one is bought, proved as a lower bound, an upper bound and an attaining design. '
   'Every other ingredient must be cited to Dette-Titoff.',
  'verified_level': 'theorem', 'theorem_level_verified': True},

 'MASTER (sufficiency)': {
  'source_read': 'arXiv:2505.21692v1, HTML full text.',
  'theorems_read': [
   {'id': 'Theorem 1',
    'statement': 'D is a sufficient decision dataset for uncertainty set C and decision set X '
                 'if and only if Delta(X,C) is contained in span D.'},
   {'id': 'Theorem 2',
    'statement': 'For any convex C in R^d, span Delta(X,C) = dir(X*(C)).'},
   {'id': 'Theorem 3',
    'statement': 'The construction algorithm terminates with probability 1 after '
                 'dim dir(X*(C)) <= d steps.'}],
  'what_is_therefore_prior': [
   'The exact geometric characterisation of when a data set suffices to recover an optimal '
   'decision.  The IDENTIFIABILITY half of any MASTER witness is prior.',
   'Constructing a minimal or least-costly sufficient data set for a fixed task.'],
  'what_is_NOT_in_the_prior': [
   'Every theorem is existential: whether a FIXED data set suffices.  No theorem gives a rate '
   'or a cost as a function of a budget or a price parameter.',
   'No nuisance parameter is profiled out anywhere.',
   'The query set Q is PREDEFINED.  The theorems say which queries from Q are required; they '
   'do not address when Q itself must be enlarged -- which is exactly the calibration-query '
   'question.'],
  'boundary_MASTER_may_claim':
   'MASTER claims the PRICE and the RATE, never the identifiability fact.  The sufficiency '
   'half of the anchor witness is cited to this prior; what is new is that the required query '
   'lies OUTSIDE the ordinary query set and what it costs to add it.',
  'verified_level': 'theorem', 'theorem_level_verified': True},

 'Query': {
  'source_read': 'arXiv:1609.02655, ar5iv full text.',
  'theorems_read': [
   {'id': 'Theorem 3.1',
    'statement': 'If G0 has singularity level r relative to the ambient space G, then '
                 'inf_{G in G} ||p_G - p_{G0}||_infty / W_s^s(G,G0) > 0 for any s >= r+1, with '
                 'the analogous bound in total variation.'},
   {'id': 'Theorem 3.3(a)',
    'statement': 'Minimax lower bound inf_{Ghat_n} sup_{G0 in G_r} E W_s(Ghat_n, G0) '
                 '>~ n^{-1/(2s)} for s in [1, r+1), giving rate n^{-1/(2(r+1))} at singularity '
                 'level r, over a COMPACT parameter space.'}],
  'what_is_therefore_prior': [
   'The phenomenon that singularity degrades the estimation rate, WITH minimax lower bounds '
   'already proved.  Query must credit this and must not present the phenomenon as new.',
   'The dependence of the rate on the singularity level r through r+1.'],
  'what_is_NOT_in_the_prior': [
   'The observation model is FIXED throughout: i.i.d. samples from the mixture density.  No '
   'theorem varies which measurements are legal.  This is the axis Query varies.',
   'No separation parameter h appears anywhere; rates are powers of the sample size n.  The '
   'earlier note that "claiming only the rate is h^{-4} puts us inside the prior" is too '
   'strong as stated -- the prior contains no h at all.  What it does contain is the '
   'singularity-degrades-the-rate phenomenon, and THAT is what must be credited.',
   'No cost of restoring distinguishability under a restricted measurement class.',
   'The paper is about parameter estimation, not hypothesis testing between two fixed worlds.'],
  'boundary_Query_may_claim':
   'That the SAME two worlds acquire different leakage orders under different admissible '
   'queries, and the sample/regret cost of restoring distinguishability at a given order.  The '
   'degradation phenomenon itself is cited to Ho-Nguyen.',
  'verified_level': 'theorem', 'theorem_level_verified': True},
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=OUT)
    a = ap.parse_args()
    out = Path(a.out)
    if out.exists():
        raise SystemExit(f'Refusing to overwrite {out}')
    src = json.loads(SRC.read_text())
    rows = src['rows'] if 'rows' in src else src
    rows = rows if isinstance(rows, list) else list(rows.values())
    merged, upgraded = [], 0
    for r in rows:
        r = dict(r)
        v = VERIFIED.get(r['paper'])
        if v:
            r.update(v)
            upgraded += 1
        merged.append(r)
    result = {
        'gate': 'G03s', 'kind': 'prior_comparison_theorem_level',
        'supersedes': str(SRC),
        'rows': merged,
        'upgraded_to_theorem_level': upgraded,
        'still_abstract_only': [r['paper'] for r in merged if not r.get('theorem_level_verified')],
        'reading_rule': 'A row is theorem_level_verified only if the paper itself was opened and '
                        'its theorem statements transcribed.  An abstract, a summary or a '
                        'secondary description never upgrades a row.',
        'not_established': [
            'Reading the priors settles what they DO prove.  It does not prove that no OTHER '
            'paper anticipates the boundary; a literature search is a different gate.',
            'The three rows still at abstract level (Structural, Support, Functional) cannot '
            'support a novelty claim yet and are listed above.'],
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open('x') as f:
        json.dump(result, f, indent=1)
    print(f'{upgraded}/{len(merged)} rows upgraded to theorem level')
    for r in merged:
        mark = 'THEOREM ' if r.get('theorem_level_verified') else 'abstract'
        print(f'  [{mark}] {r["paper"]}')
    print(f'artifact: {out}')


if __name__ == '__main__':
    main()
