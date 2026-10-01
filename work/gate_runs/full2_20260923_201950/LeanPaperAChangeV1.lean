import «LeanPaperBDataProcV1»
import «LeanPaperASurrogateV1»

/-!
# Paper A: `hchange` discharged

`surrogate_cost_quadratic` takes

    hchange : 2 r / d^2 * kl <= C + C' * ma,

the stopped change of measure at a hidden pair, summed over the `r` pairs.  It is the one
hypothesis that carries part of A-H5's conclusion, and `THEOREM_MAP.md` said so.

It is a consequence of three things the corpus now has.

1. **The divergence of an adaptive transcript is the expected count of the queries that
   separate the pair, times the per-query divergence.**  `klChain` and `visitCount` are the
   same recursion with the per-step cost replaced, so
   `klChain = (d^2/2) * visitCount` whenever the per-step divergence is `d^2/2` on the
   pair's own queries and `0` elsewhere -- `klChain_eq_scaled_visit`.
2. **Data processing.**  `kl2_le_klChain` (`LeanPaperBDataProcV1`) bounds the binary
   divergence of ANY bounded statistic read off the transcript by the transcript divergence.
   At the decision event this is `kl <= klChain`.
3. **Forced exploration's budget.**  The learner's own middle-cell count is at most
   `C + C' E sqrt(tau)`, which is what `sqrt_exploration_rate` produces.

`pair_bound_from_transcript` turns (1) and (2) into `2/d^2 * kl <= visitCount` for ONE
hidden pair; `hchange_from_pairs` sums the `r` disjoint pairs; and
`surrogate_omega_log_squared_closed` is `surrogate_omega_log_squared` with `hchange` gone.

WHAT REMAINS.  The finite alphabet of `LeanPaperBTranscriptV1`, and the support condition
`hqf`/`hqf'` that the decision event carries mass under both worlds.  Neither is
conclusion-shaped; both are properties of the rule and the channel.
-/

namespace CIGAMF.P13.PaperAChange

open Finset
open CIGAMF.P13.PaperBTranscript
open CIGAMF.P13.PaperBDataProc
open CIGAMF.P13.PaperASurrogate
open CIGAMF.P13.PaperBRates

variable {K Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## The expected count of a marked query -/

/-- The expected number of times, along `t` further steps, that the policy issues a query
carrying the mark `A`.  The recursion is `klChain`'s with the per-step divergence replaced
by the mark. -/
noncomputable def visitCount (π : List Y → K) (p : K → Y → ℝ) (A : K → ℝ) :
    ℕ → List Y → ℝ
  | 0, _ => 0
  | (t + 1), h => A (π h) + ∑ y, p (π h) y * visitCount π p A t (y :: h)

theorem visitCount_zero (π : List Y → K) (p : K → Y → ℝ) (A : K → ℝ) (h : List Y) :
    visitCount π p A 0 h = 0 := rfl

theorem visitCount_succ (π : List Y → K) (p : K → Y → ℝ) (A : K → ℝ) (t : ℕ)
    (h : List Y) :
    visitCount π p A (t + 1) h
      = A (π h) + ∑ y, p (π h) y * visitCount π p A t (y :: h) := rfl

/-- **The transcript divergence IS the count, scaled.**  If each query's divergence is `c`
times its mark, the whole transcript's is `c` times the expected total mark. -/
theorem klChain_eq_scaled_visit (π : List Y → K) (p q : K → Y → ℝ) (c : ℝ) (ind : K → ℝ)
    (hstep : ∀ k, klStep p q k = c * ind k) :
    ∀ (t : ℕ) (h : List Y),
      klChain π p q t h = c * visitCount π p ind t h := by
  intro t
  induction t with
  | zero => intro h; rw [klChain_zero, visitCount_zero, mul_zero]
  | succ t ih =>
      intro h
      rw [klChain_succ, visitCount_succ, hstep (π h), mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [ih (y :: h)]
      ring

/-! ## One hidden pair -/

/-- **The change of measure at one hidden pair.**  The divergence the decision needs is at
most `d^2/2` times the expected number of samples the policy spends on that pair's queries.
Nothing here is assumed about the policy: `hdp` is data processing and `hstep` is the
channel's per-query divergence. -/
theorem pair_bound_from_transcript (π : List Y → K) (p q : K → Y → ℝ) (d kl : ℝ)
    (hd : 0 < d) (ind : K → ℝ) (t : ℕ)
    (hstep : ∀ k, klStep p q k = d ^ 2 / 2 * ind k)
    (hdp : kl ≤ klChain π p q t []) :
    2 / d ^ 2 * kl ≤ visitCount π p ind t [] := by
  have hd2 : (0 : ℝ) < d ^ 2 := by positivity
  have heq := klChain_eq_scaled_visit π p q (d ^ 2 / 2) ind hstep t []
  rw [heq] at hdp
  rw [div_mul_eq_mul_div, div_le_iff₀ hd2]
  nlinarith [hdp, hd2]

/-! ## Summing the pairs -/

/-- **`hchange`, assembled.**  Each of the `r` disjoint hidden pairs contributes
`2/d^2 * kl` to the learner's own sample count, and forced exploration bounds the total. -/
theorem hchange_from_pairs (r : ℕ) (d kl C C' ma : ℝ) (hd : 0 < d)
    (pairCount : Fin r → ℝ)
    (hpair : ∀ i, 2 / d ^ 2 * kl ≤ pairCount i)
    (htotal : ∑ i, pairCount i ≤ C + C' * ma) :
    2 * (r : ℝ) / d ^ 2 * kl ≤ C + C' * ma := by
  have hsum : ∑ _i : Fin r, (2 / d ^ 2 * kl) ≤ ∑ i, pairCount i :=
    Finset.sum_le_sum (fun i _ => hpair i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hrw : (r : ℝ) * (2 / d ^ 2 * kl) = 2 * (r : ℝ) / d ^ 2 * kl := by ring
  rw [hrw] at hsum
  linarith [hsum, htotal]

/-! ## A-H5 with `hchange` gone -/

/-- **The surrogate learner's quadratic cost, with the change of measure supplied.**  The
same conclusion as `surrogate_omega_log_squared`, with `hchange` replaced by the transcript
facts that produce it. -/
theorem surrogate_omega_log_squared_closed (r : ℕ) (d C C' Eτ ma α : ℝ)
    (hC' : 0 < C') (hEτ : 0 ≤ Eτ) (hd : 0 < d) (hα : 0 < α) (hα1 : α < 1)
    (hAC : C ≤ 2 * (r : ℝ) / d ^ 2 * kl2 (1 - α) α)
    (hma : ma ≤ Eτ ^ (1 / 2 : ℝ))
    (pairCount : Fin r → ℝ)
    (hpair : ∀ i, 2 / d ^ 2 * kl2 (1 - α) α ≤ pairCount i)
    (htotal : ∑ i, pairCount i ≤ C + C' * ma) :
    ((2 * (r : ℝ) / d ^ 2 * kl2 (1 - α) α - C) / C') ^ (1 / (1 / 2 : ℝ)) ≤ Eτ :=
  surrogate_omega_log_squared (r : ℝ) d C C' Eτ ma α hC' hEτ hd hα hα1 hAC hma
    (hchange_from_pairs r d (kl2 (1 - α) α) C C' ma hd pairCount hpair htotal)

/-! ## Audit -/

#print axioms klChain_eq_scaled_visit
#print axioms pair_bound_from_transcript
#print axioms hchange_from_pairs
#print axioms surrogate_omega_log_squared_closed

end CIGAMF.P13.PaperAChange
