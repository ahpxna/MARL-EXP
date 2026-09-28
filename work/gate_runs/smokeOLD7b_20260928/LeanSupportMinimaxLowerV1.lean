import «LeanSupportEquivariantDecoderV1»

/-! # Support S-eq: the minimax LOWER bound, over ALL decision rules.

`LeanSupportEquivariantDecoderV1` constructs a decoder whose risk is the same number in
every compatible world, and `bayes_is_minimax` shows that for THAT decoder the Bayes risk
equals its worst case.  Its own "what this does not establish" names the gap precisely:
there is no infimum over decision rules, so nothing yet says the decoder is optimal --
only that it is flat.

This file supplies the missing half.  The argument is the classical one, and each step is
a theorem rather than a definition:

  1.  Bayes risk factors through the posterior loss:  B(d) = Σ_x g(x, d x).
  2.  Hence the pointwise argmin rule is optimal over ALL rules (`bayes_optimal_lower`),
      and it EXISTS (`bayes_optimal_attained`) -- the infimum is attained, so it is a
      minimum and no limit argument is needed.
  3.  Worst case dominates Bayes for every prior (`bayes_le_minimax`, already proved).
  4.  Chaining 2 and 3, the Bayes-optimal value lower-bounds the worst-case risk of EVERY
      rule (`minimax_ge_bayes_optimal`).
  5.  A rule with constant risk equal to that value is therefore minimax, and this is
      stated as `IsLeast` over the set of achievable worst-case risks -- an infimum over
      all rules, attained (`equivariant_is_minimax`).

## WHAT IS PROVED

* `bayesRisk_eq_sum_postLoss` — the factorisation, by exchanging two finite sums.
* `bayes_optimal_lower` — every rule's Bayes risk is at least Σ_x min_a g(x,a).
* `bayes_optimal_attained` — a rule achieving it exists, constructed from the pointwise
  argmin.
* `minimax_ge_bayes_optimal` — the Bayes-optimal value lower-bounds the worst-case risk
  of every rule, for every prior.
* `equivariant_is_minimax` — **the minimax statement**: a constant-risk rule whose value
  is the Bayes-optimal value is a least element of the achievable worst-case risks.
* `constant_risk_of_symmetry` — a risk invariant under a transitive symmetry group is
  constant, which is how the equivariant decoder's flatness is OBTAINED from relabelling
  worlds rather than assumed.

## WHAT THIS DOES NOT ESTABLISH

- The prior is arbitrary but FIXED.  This is minimaxity via one Bayes prior; it is not a
  general minimax theorem and no saddle point is claimed in the abstract.
- Finitely many worlds, transcripts and actions throughout.  Nothing here extends to
  infinite action sets, where the pointwise minimum may fail to be attained.
- `constant_risk_of_symmetry` takes the transitive symmetry as a hypothesis.  That the
  Support problem's relabelling group is transitive on compatible worlds is a fact about
  that problem, supplied where it is used, not proved here in the abstract.
-/

namespace CIGAMF.P13.SupportMinimaxLower

open Finset
open CIGAMF.P13.SupportSamplingLaw

noncomputable section

variable {World Obs Act : Type*}
  [Fintype World] [DecidableEq World]
  [Fintype Obs] [DecidableEq Obs]
  [Fintype Act] [Nonempty Act] [DecidableEq Act]

/-- The unnormalised posterior loss of action `a` after observing `x`. -/
def postLoss (pri : World → ℝ) (P : World → Obs → ℝ) (L : World → Act → ℝ)
    (x : Obs) (a : Act) : ℝ :=
  ∑ w, pri w * P w x * L w a

/-- The risk of a rule in world `w`. -/
def risk (P : World → Obs → ℝ) (L : World → Act → ℝ) (d : Obs → Act) (w : World) : ℝ :=
  ∑ x, P w x * L w (d x)

/-- Bayes risk of a rule. -/
def bayesRisk (pri : World → ℝ) (P : World → Obs → ℝ) (L : World → Act → ℝ)
    (d : Obs → Act) : ℝ :=
  ∑ w, pri w * risk P L d w

/-- The Bayes-optimal value: the posterior loss minimised pointwise, then summed. -/
def bayesOptValue (pri : World → ℝ) (P : World → Obs → ℝ) (L : World → Act → ℝ) : ℝ :=
  ∑ x, (univ : Finset Act).inf' univ_nonempty (postLoss pri P L x)

/-- **The factorisation.**  Bayes risk is the posterior loss summed along the rule. -/
theorem bayesRisk_eq_sum_postLoss (pri : World → ℝ) (P : World → Obs → ℝ)
    (L : World → Act → ℝ) (d : Obs → Act) :
    bayesRisk pri P L d = ∑ x, postLoss pri P L x (d x) := by
  classical
  unfold bayesRisk risk postLoss
  have h1 : ∀ w : World,
      pri w * (∑ x, P w x * L w (d x)) = ∑ x, pri w * P w x * L w (d x) := by
    intro w
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Finset.sum_congr rfl (fun w _ => h1 w)]
  exact Finset.sum_comm

/-- **Optimality over ALL rules.**  No rule beats the pointwise posterior minimum. -/
theorem bayes_optimal_lower (pri : World → ℝ) (P : World → Obs → ℝ)
    (L : World → Act → ℝ) (d : Obs → Act) :
    bayesOptValue pri P L ≤ bayesRisk pri P L d := by
  rw [bayesRisk_eq_sum_postLoss]
  unfold bayesOptValue
  exact Finset.sum_le_sum fun x _ => Finset.inf'_le _ (mem_univ (d x))

/-- **And it is attained**, so the infimum over rules is a minimum. -/
theorem bayes_optimal_attained (pri : World → ℝ) (P : World → Obs → ℝ)
    (L : World → Act → ℝ) :
    ∃ d : Obs → Act, bayesRisk pri P L d = bayesOptValue pri P L := by
  classical
  have hchoice : ∀ x : Obs, ∃ a : Act,
      postLoss pri P L x a = (univ : Finset Act).inf' univ_nonempty (postLoss pri P L x) := by
    intro x
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (univ_nonempty) (postLoss pri P L x)
    exact ⟨a, ha.symm⟩
  choose d hd using hchoice
  refine ⟨d, ?_⟩
  rw [bayesRisk_eq_sum_postLoss]
  unfold bayesOptValue
  exact Finset.sum_congr rfl fun x _ => hd x

/-- **The lower bound on the worst case.**  For every prior and every rule, the
Bayes-optimal value lower-bounds the rule's worst-case risk. -/
theorem minimax_ge_bayes_optimal [Nonempty World] (pri : World → ℝ) (P : World → Obs → ℝ)
    (L : World → Act → ℝ) (hpi : ∀ w, 0 ≤ pri w) (hsum : ∑ w, pri w = 1)
    (d : Obs → Act) :
    bayesOptValue pri P L
      ≤ (univ : Finset World).sup' univ_nonempty (risk P L d) := by
  refine le_trans (bayes_optimal_lower pri P L d) ?_
  exact bayes_le_minimax pri (risk P L d) hpi hsum

/-- **The minimax statement.**  A rule whose risk is constant and equal to the
Bayes-optimal value is a LEAST element of the achievable worst-case risks -- an infimum
over all rules, attained. -/
theorem equivariant_is_minimax [Nonempty World] (pri : World → ℝ) (P : World → Obs → ℝ)
    (L : World → Act → ℝ) (hpi : ∀ w, 0 ≤ pri w) (hsum : ∑ w, pri w = 1)
    (d₀ : Obs → Act) (r : ℝ)
    (hconst : ∀ w, risk P L d₀ w = r)
    (hopt : bayesOptValue pri P L = r) :
    IsLeast {v : ℝ | ∃ d : Obs → Act,
      (univ : Finset World).sup' univ_nonempty (risk P L d) = v} r := by
  constructor
  · exact ⟨d₀, minimax_eq_of_constant (risk P L d₀) r hconst⟩
  · rintro v ⟨d, rfl⟩
    rw [← hopt]
    exact minimax_ge_bayes_optimal pri P L hpi hsum d

/-- **Flatness from relabelling, not by assumption.**  If a symmetry group acts on worlds
leaving the risk invariant, and acts transitively, then the risk is constant.  This is how
the equivariant decoder's flatness is OBTAINED rather than assumed. -/
theorem constant_risk_of_symmetry {G : Type*} (act : G → World → World) (R : World → ℝ)
    (hinv : ∀ g w, R (act g w) = R w)
    (htrans : ∀ w w' : World, ∃ g, act g w = w') :
    ∀ w w' : World, R w = R w' := by
  intro w w'
  obtain ⟨g, hg⟩ := htrans w w'
  rw [← hg, hinv]

#print axioms bayesRisk_eq_sum_postLoss
#print axioms bayes_optimal_lower
#print axioms bayes_optimal_attained
#print axioms minimax_ge_bayes_optimal
#print axioms equivariant_is_minimax
#print axioms constant_risk_of_symmetry

end

end CIGAMF.P13.SupportMinimaxLower
