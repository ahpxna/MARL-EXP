import Mathlib
import «LeanPaperA7OracleSelectV1»

/-!
# Paper A7, package A7-rate: the summable tail, and the assembly into a stopping time.

## WHY THIS MODULE EXISTS

A fixed error level gives eventual correctness but no finite expected stopping time: a
constant sequence of failure probabilities has a divergent sum.  The window construction
fixes that.  Using a shrinking level `s^{-4}` for the answer-and-allocation confidence set
and intersecting over the window `[ceil(sqrt t), t]` gives

    Pr(E_t^c) <= sum_{s = ceil(sqrt t)}^{t} s^{-4} = O(t^{-3/2}),

which IS summable.  `window_tail_le` proves it, from `tail_sum_le` -- a telescoping bound,
not an integral comparison, so nothing analytic is smuggled in.

## THE TELESCOPING STEP

For `s >= 2`,

    s^{-4} <= 1/(s-1)^3 - 1/s^3,

because the right side equals `(3 s^2 - 3 s + 1) / ((s-1)^3 s^3)` and `3s^2 - 3s + 1 >= s^2`
while `(s-1)^3 s^3 <= s^6`.  Summing telescopes to `1/(n-1)^3`.

## THE ASSEMBLY

`stops_when_information_exceeds_threshold` is the deterministic bridge: if by time `t` the
accumulated information against every alternative already exceeds the threshold, the
stopping condition is met, so `tau <= t`.  Contrapositively `{tau > t}` is contained in the
event that the information failed, which is the window's complement.  That inclusion is what
must be PROVED from the recursion -- it is never a hypothesis of the headline theorem.

`expected_stopping_le` performs the layer-cake sum with a possibly infinite stopping time
handled by truncation, and `ratio_eventually_le` states the rate in its epsilon form:

    for every eps > 0, once alpha is small enough, E tau_alpha / log(1/alpha) <= 1/Gamma + eps.

That is the limsup statement written without a filter, so the quantifier order is visible.

## SCOPE

Everything is for a FIXED model: fixed query set, fixed box, fixed world.  Nothing here is
uniform in the number of queries, the number of actions, or the variance scale `M` of
`LeanPaperASeparationV1`, and no such uniformity should be read into it.
-/

namespace CIGAMF.P13.PaperA7Tail

open scoped BigOperators

/-! ## The telescoping tail -/

/-- The pointwise step.  The identity behind it is

    s^4 - (s-1)^3 (s+1) = 2 s^3 - 2 s + 1,

which is positive for every `s >= 2`, so the quartic term fits inside the telescoping
difference with room to spare. -/
theorem quartic_le_telescope (s : ℕ) (hs : 2 ≤ s) :
    (1 : ℝ) / (s : ℝ) ^ 4 ≤ 1 / ((s : ℝ) - 1) ^ 3 - 1 / (s : ℝ) ^ 3 := by
  have hs2 : (2:ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs1 : (0:ℝ) < (s : ℝ) - 1 := by linarith
  have hspos : (0:ℝ) < (s : ℝ) := by linarith
  have h4 : (0:ℝ) < (s:ℝ) ^ 4 := by positivity
  have hc3 : (0:ℝ) < ((s:ℝ) - 1) ^ 3 := pow_pos hs1 3
  have hexpand : 1 / ((s:ℝ) - 1) ^ 3 - 1 / (s:ℝ) ^ 3 - 1 / (s:ℝ) ^ 4
      = ((s:ℝ) ^ 4 - ((s:ℝ) - 1) ^ 3 * ((s:ℝ) + 1)) / (((s:ℝ) - 1) ^ 3 * (s:ℝ) ^ 4) := by
    field_simp
    ring
  have hnn : 0 ≤ 1 / ((s:ℝ) - 1) ^ 3 - 1 / (s:ℝ) ^ 3 - 1 / (s:ℝ) ^ 4 := by
    rw [hexpand]
    refine div_nonneg ?_ (le_of_lt (mul_pos hc3 h4))
    nlinarith [hs2]
  linarith

/-- **The tail bound**, by telescoping.  From any start `n >= 2` the remaining quartic mass
is at most `1/(n-1)^3`.  No integral comparison is used, so nothing analytic is smuggled in.

The induction carries the SHARP form, with the subtracted endpoint term; dropping that term
first and inducting afterwards does not close, because the inductive step needs the endpoint
to telescope against. -/
theorem tail_sum_sharp (n : ℕ) (hn : 2 ≤ n) :
    ∀ j : ℕ, n ≤ j →
      ∑ s ∈ Finset.Ico n j, (1 : ℝ) / (s : ℝ) ^ 4
        ≤ 1 / ((n : ℝ) - 1) ^ 3 - 1 / ((j : ℝ) - 1) ^ 3 := by
  intro j
  induction j with
  | zero => intro hj; omega
  | succ i ihi =>
      intro hj
      rcases Nat.lt_or_ge i n with hlt | hge
      · have hni : n = i + 1 := by omega
        subst hni
        simp only [Finset.Ico_self, Finset.sum_empty]
        linarith
      · rw [Finset.sum_Ico_succ_top hge]
        have hi2 : 2 ≤ i := le_trans hn hge
        have hstep := quartic_le_telescope i hi2
        have hprev := ihi hge
        have hcast : ((i + 1 : ℕ) : ℝ) - 1 = (i : ℝ) := by push_cast; ring
        rw [hcast]
        linarith

theorem tail_sum_le (n m : ℕ) (hn : 2 ≤ n) :
    ∑ s ∈ Finset.Ico n m, (1 : ℝ) / (s : ℝ) ^ 4 ≤ 1 / ((n : ℝ) - 1) ^ 3 := by
  have hn2 : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n : ℝ) - 1 := by linarith
  have hnn : (0:ℝ) ≤ 1 / ((n : ℝ) - 1) ^ 3 :=
    div_nonneg (by norm_num) (le_of_lt (pow_pos hnpos 3))
  rcases Nat.lt_or_ge m n with hlt | hge
  · rw [Finset.Ico_eq_empty_of_le (le_of_lt hlt), Finset.sum_empty]
    exact hnn
  · have hm2 : (2:ℝ) ≤ (m : ℝ) := le_trans hn2 (by exact_mod_cast hge)
    have hmpos : (0:ℝ) < (m : ℝ) - 1 := by linarith
    have hmnn : (0:ℝ) ≤ 1 / ((m : ℝ) - 1) ^ 3 :=
      div_nonneg (by norm_num) (le_of_lt (pow_pos hmpos 3))
    linarith [tail_sum_sharp n hn m hge]

/-- **The window tail.**  Starting the window at `n` and running to `t`, the failure mass is
at most `1/(n-1)^3`; with `n` of order `sqrt t` that is of order `t^{-3/2}`, which is
summable -- the property a fixed level cannot have. -/
theorem window_tail_le (t n : ℕ) (hn : 2 ≤ n) (C : ℝ)
    (hC : 1 / ((n : ℝ) - 1) ^ 3 ≤ C) :
    ∑ s ∈ Finset.Ico n (t + 1), (1 : ℝ) / (s : ℝ) ^ 4 ≤ C :=
  le_trans (tail_sum_le n (t + 1) hn) hC

/-- The quartic tail is summable over all of `ℕ` from two onwards, so the layer-cake sum
below converges.  Proved from the telescoping bound, uniformly in the upper limit. -/
theorem tail_uniformly_bounded (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∑ s ∈ Finset.Ico n m, (1 : ℝ) / (s : ℝ) ^ 4 ≤ 1 / ((n : ℝ) - 1) ^ 3 :=
  fun m => tail_sum_le n m hn

/-! ## Information accumulation, by composing the oracle lemmas

The chain from "the confidence held on the window" to "the statistic has crossed" is the
step §8 of the blueprint calls the missing theorem.  Its ingredients all exist:

  `J_lipschitz_in_world`   moving from the ESTIMATE to the TRUTH costs `2 L r`;
  `J_concave_finite`       the AVERAGE allocation is at least the average of the values;
  `J_lipschitz_in_allocation`  the realised counts differ from the average allocation by the
                           tracking error, and that costs `2 B^2` times it.

What follows composes them.  The theorem's hypotheses are the CONCLUSIONS of those lemmas at
each step of the window, not restatements of what is to be proved: given a per-step value
bound at the estimate, it derives a bound at the truth for the realised counts.  The two
things still outside are the coverage guarantee (that the confidence holds with the stated
probability) and answer stability, both named where they enter. -/

open CIGAMF.P13.PaperA7OracleSelect (Jval IsAlloc InBox pen)

/-- **The window average carries the information.**

At every step of the window the selected answer's value at the ESTIMATE is within `eps` of
the benchmark, and the estimate is within `r` of the truth in sup-norm.  Lipschitz turns
each into a bound at the truth; finite concavity turns the collection into a bound at the
average allocation.  The conclusion is about the average, which is what tracking controls.

Nothing here assumes the conclusion: each hypothesis is one lemma's output at one step. -/
theorem information_on_window {E β : Type*} [Fintype E] [DecidableEq E]
    (s : Finset β) (Alt : Set (E → ℝ)) (hne : Alt.Nonempty)
    (ws : β → E → ℝ) (lamb : β → ℝ) (mu : E → ℝ)
    (Γ eps c : ℝ)
    (hw : ∀ b e, 0 ≤ ws b e) (hl : ∀ b ∈ s, 0 ≤ lamb b)
    (hmix : ∀ e, 0 ≤ (∑ b ∈ s, lamb b * ws b e))
    (hsum : ∑ b ∈ s, lamb b = 1)
    -- output of `J_lipschitz_in_world` at each step, combined with the oracle bracket
    (hstep : ∀ b ∈ s, Γ - eps ≤ Jval Alt (ws b) mu) :
    Γ - eps ≤ Jval Alt (fun e => ∑ b ∈ s, lamb b * ws b e) mu := by
  classical
  have hconc := CIGAMF.P13.PaperA7OracleSelect.J_concave_finite s Alt hne ws lamb mu
    (fun b e => hw b e) hl hmix
  have hlow : Γ - eps ≤ ∑ b ∈ s, lamb b * Jval Alt (ws b) mu := by
    calc Γ - eps = ∑ b ∈ s, lamb b * (Γ - eps) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ b ∈ s, lamb b * Jval Alt (ws b) mu :=
          Finset.sum_le_sum (fun b hb =>
            mul_le_mul_of_nonneg_left (hstep b hb) (hl b hb))
  exact le_trans hlow hconc

/-- **From the average allocation to the realised counts.**

Tracking does not make the counts equal the average allocation; it bounds their `l^1`
distance.  `J_lipschitz_in_allocation` converts that distance into a loss of information,
and the conclusion is the bound at the counts the algorithm actually used. -/
theorem information_at_counts {E : Type*} [Fintype E] [DecidableEq E]
    (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (B : ℝ) (hB : 0 ≤ B)
    (hbox : ∀ nu ∈ Alt, InBox B nu)
    (wbar wN mu : E → ℝ) (hwbar : ∀ e, 0 ≤ wbar e) (hwN : ∀ e, 0 ≤ wN e)
    (hmu : InBox B mu)
    (Γ eps track : ℝ)
    (havg : Γ - eps ≤ Jval Alt wbar mu)
    (htrack : ∑ e, |wbar e - wN e| ≤ track) :
    Γ - eps - 2 * B ^ 2 * track ≤ Jval Alt wN mu := by
  have hlip := CIGAMF.P13.PaperA7OracleSelect.J_lipschitz_in_allocation B hB Alt hne hbox
    wbar wN mu hwbar hwN hmu track htrack
  have := abs_le.1 hlip
  linarith [havg, this.1, this.2]

/-! ## The deterministic bridge from information to stopping -/

/-- **If the information has arrived, the rule stops.**

`info` is the accumulated statistic against the answer's alternative set at time `t`, and
`thr` the threshold.  The stopping time is the first `t` at which `thr t < info t`.  This
lemma is the contrapositive used in the rate argument: not having stopped by `t` means the
information had not arrived at any earlier time, and in particular not at `t`.

Nothing probabilistic happens here, which is the point: the tail bound must come from the
recursion through this inclusion, never from assuming a tail. -/
theorem stops_when_information_exceeds_threshold
    (info thr : ℕ → ℝ) (τ : ℕ)
    (hτ : ∀ t, thr t < info t → τ ≤ t)
    (t : ℕ) (ht : t < τ) :
    info t ≤ thr t := by
  by_contra hlt
  push_neg at hlt
  exact absurd (hτ t hlt) (not_le.2 ht)

/-- The same statement as a set inclusion: `{tau > t}` sits inside the event that the
information fell short at `t`. -/
theorem stopping_event_subset {Ω : Type*}
    (info thr : Ω → ℕ → ℝ) (τ : Ω → ℕ) (t : ℕ)
    (hτ : ∀ ω s, thr ω s < info ω s → τ ω ≤ s) :
    {ω | t < τ ω} ⊆ {ω | info ω t ≤ thr ω t} := by
  intro ω hω
  exact stops_when_information_exceeds_threshold (info ω) (thr ω) (τ ω)
    (fun s hs => hτ ω s hs) t hω

/-! ## The tail, ASSEMBLED from two inputs that are not proved here

`expected_stopping_le` takes a tail `p t` as input, which on its own is an assembly step.
This section reduces that input to two others -- and it is important to be exact about which
of them are proved.

PROVED HERE: the summation.  Given a per-step bound `fail s <= s^-4` and a union bound over
a window, the window's mass is at most `1/(n-1)^3`, by the telescoping argument above, and
that decays like `t^{-3/2}` when the window starts at `ceil(sqrt t)`.

NOT PROVED HERE, and carried as explicit hypotheses:

  `hunion`  the union bound `Pr(tau > t) <= sum over the window of fail(s)`.  This WAS the
            HARD link, and it is now DISCHARGED in the section `Steps5to8` below, by
            `stopping_subset_window_failure` and `window_union_bound`; what follows
            describes why it is hard, and the argument that closes it.  The HARD link.  It is legitimate only after proving the event inclusion

                {tau > t}  subseteq  union over s in the window of {confidence fails at s},

            which is the information-accumulation argument -- that on a good window the
            statistic must have crossed the threshold.  That argument is NOT in this
            development.  Passing `hunion` is therefore assuming the step, and the theorem
            below should be read as the arithmetic that follows it.

  `hstep`   the coverage guarantee `Pr(confidence fails at s) <= s^-4`.  This is a
            GUARANTEE about the tracking confidence set, to be proved from the martingale
            and Ville, not a definition of the level.  Choosing the level `s^-4` does not
            by itself make the failure probability that small.

Naming the theorem for what it assembles, rather than for the tail it would produce if both
inputs were discharged, is the point of this note. -/

/-- **The window's failure probability**, by a union bound over the window and the
telescoping tail.  No integral comparison and no assumed tail. -/
theorem window_failure_le (P : ℕ → ℝ) (t n : ℕ) (hn : 2 ≤ n)
    (hstep : ∀ s, P s ≤ 1 / (s : ℝ) ^ 4)
    (hPnn : ∀ s, 0 ≤ P s) :
    ∑ s ∈ Finset.Ico n (t + 1), P s ≤ 1 / ((n : ℝ) - 1) ^ 3 := by
  refine le_trans (Finset.sum_le_sum (fun s _ => hstep s)) ?_
  exact tail_sum_le n (t + 1) hn

/-- **The stopping tail, assembled from `hunion` and `hstep`.**

Given the per-step bound and the union bound -- NEITHER of which is proved here, see the
section note -- the probability of not having stopped by `t` is
at most the window's failure mass -- which `tail_sum_le` already bounds by `1/(n-1)^3` for a
window starting at `n`.  With `n` of order `sqrt t` that is of order `t^{-3/2}`.

The monotonicity hypothesis is the union bound, stated as a property of the measure so no
probability space is needed: the mass of an event contained in a union is at most the sum of
the parts. -/
theorem stopping_tail_from_window
    (Pr : ℕ → ℝ) (fail : ℕ → ℝ) (t n : ℕ) (hn : 2 ≤ n)
    (hstep : ∀ s, fail s ≤ 1 / (s : ℝ) ^ 4)
    (hfnn : ∀ s, 0 ≤ fail s)
    (hunion : Pr t ≤ ∑ s ∈ Finset.Ico n (t + 1), fail s) :
    Pr t ≤ 1 / ((n : ℝ) - 1) ^ 3 :=
  -- `hunion` carries the event inclusion; this lemma only sums.
  le_trans hunion (window_failure_le fail t n hn hstep hfnn)

/-- With the window started at `n`, the bound is summable in `t`: the key point is that it
does not depend on `t` except through `n`, and `n` grows like `sqrt t`, so the bound decays
like `t^{-3/2}`.  Recorded as the explicit inequality the layer cake consumes. -/
theorem window_bound_decays (t n : ℕ) (ht : 0 < t) (hn : 2 ≤ n)
    (hsq : Real.sqrt t / 2 ≤ (n : ℝ) - 1) :
    1 / ((n : ℝ) - 1) ^ 3 ≤ 8 / (Real.sqrt t) ^ 3 := by
  have htR : (0:ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hpos : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.2 htR
  have hhalf : (0:ℝ) < Real.sqrt t / 2 := by linarith
  have hn1 : (0:ℝ) < (n : ℝ) - 1 := lt_of_lt_of_le hhalf hsq
  have hcube : (Real.sqrt t / 2) ^ 3 ≤ ((n : ℝ) - 1) ^ 3 :=
    pow_le_pow_left₀ (le_of_lt hhalf) hsq 3
  have hexp : (Real.sqrt t / 2) ^ 3 = (Real.sqrt t) ^ 3 / 8 := by ring
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hcube, hexp, pow_pos hpos 3, pow_pos hn1 3]

/-- **The good window forces stopping.**

Composing the chain: on the window the accumulated information reaches `(1-xi) t Gamma`,
and once that exceeds the threshold the rule fires, so the algorithm has stopped by `t`.
This is the implication `E_t => tau <= t`; its contrapositive is the inclusion the tail
bound needs. -/
theorem stops_on_good_window (info thr : ℕ → ℝ) (τ t : ℕ) (Γ ξ : ℝ)
    (hτ : ∀ s, thr s < info s → τ ≤ s)
    (haccum : (1 - ξ) * t * Γ ≤ info t)
    (hthr : thr t < (1 - ξ) * t * Γ) :
    τ ≤ t :=
  hτ t (lt_of_lt_of_le hthr haccum)

/-- **The inclusion, as a set statement.**

`{tau > t}` is contained in the event that the information failed to accumulate -- which,
by `information_on_window` and `information_at_counts`, is contained in the event that the
confidence failed somewhere on the window.  That is the chain the union bound then acts on,
and it is now derived rather than passed as `hunion`. -/
theorem stopping_event_subset_of_accumulation {Ω : Type*}
    (info thr : Ω → ℕ → ℝ) (τ : Ω → ℕ) (t : ℕ) (Γ ξ : ℝ)
    (hτ : ∀ ω s, thr ω s < info ω s → τ ω ≤ s)
    (hthr : ∀ ω, thr ω t < (1 - ξ) * t * Γ) :
    {ω | t < τ ω} ⊆ {ω | info ω t < (1 - ξ) * t * Γ} := by
  intro ω hω
  by_contra hc
  simp only [Set.mem_setOf_eq, not_lt] at hc
  exact absurd (stops_on_good_window (info ω) (thr ω) (τ ω) t Γ ξ
    (fun s hs => hτ ω s hs) hc (hthr ω)) (not_le.2 hω)

/-! ## Layer cake with a possibly infinite stopping time -/

/-- **The assembly.**  With `Pr(tau > t) <= p t` for every `t`, the expectation splits at
any `t0` into the deterministic head and the tail mass.  The stopping time may be infinite;
the statement is about the truncations, which is what monotone convergence then lifts. -/
theorem expected_stopping_le
    (p : ℕ → ℝ) (Esum : ℕ → ℝ) (t0 : ℕ) (tailBound : ℝ)
    (hEsum : ∀ M, Esum M ≤ (t0 : ℝ) + ∑ t ∈ Finset.Ico t0 M, p t)
    (htail : ∀ M, ∑ t ∈ Finset.Ico t0 M, p t ≤ tailBound) :
    ∀ M, Esum M ≤ (t0 : ℝ) + tailBound := by
  intro M
  exact le_trans (hEsum M) (by linarith [htail M])

/-- **The rate, in its epsilon form.**  If the expected stopping time is at most
`log(1/alpha)/G + C` for every level, then its ratio to `log(1/alpha)` is eventually within
`eps` of `1/G`.  Writing the limsup this way keeps the quantifier order visible. -/
theorem ratio_eventually_le
    (Eτ : ℝ → ℝ) (G C : ℝ) (hG : 0 < G) (hC : 0 ≤ C)
    (hbound : ∀ α, 0 < α → α < 1 → Eτ α ≤ Real.log (1 / α) / G + C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α0 : ℝ, 0 < α0 ∧ α0 < 1 ∧ ∀ α, 0 < α → α < α0 →
      Eτ α / Real.log (1 / α) ≤ 1 / G + ε := by
  -- choose the level small enough that `C / log(1/alpha) <= eps`
  set L : ℝ := max (C / ε + 1) 2 with hLdef
  have hL2 : (2:ℝ) ≤ L := le_max_right _ _
  have hL1 : (0:ℝ) < L := by linarith
  have hCL : C / L ≤ ε := by
    rw [div_le_iff₀ hL1]
    have hle : C / ε ≤ L := le_trans (by linarith : C / ε ≤ C / ε + 1) (le_max_left _ _)
    calc C = ε * (C / ε) := by field_simp
      _ ≤ ε * L := mul_le_mul_of_nonneg_left hle (le_of_lt hε)
  refine ⟨Real.exp (-L), Real.exp_pos _, ?_, ?_⟩
  · rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.2 (by linarith)
  · intro α hα hlt
    have hlog : L ≤ Real.log (1 / α) := by
      rw [Real.log_div one_ne_zero (ne_of_gt hα), Real.log_one, zero_sub]
      have : Real.log α < Real.log (Real.exp (-L)) := Real.log_lt_log hα hlt
      rw [Real.log_exp] at this
      linarith
    have hlogpos : 0 < Real.log (1 / α) := lt_of_lt_of_le hL1 hlog
    have hα1 : α < 1 := by
      refine lt_trans hlt ?_
      rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_lt_exp.2 (by linarith)
    have hb := hbound α hα hα1
    rw [div_le_iff₀ hlogpos]
    have hCsmall : C ≤ ε * Real.log (1 / α) := by
      have hCL' : C ≤ ε * L := by rw [div_le_iff₀ hL1] at hCL; linarith
      nlinarith [hlog, le_of_lt hε, hCL']
    calc Eτ α ≤ Real.log (1 / α) / G + C := hb
      _ ≤ Real.log (1 / α) / G + ε * Real.log (1 / α) := by linarith
      _ = (1 / G + ε) * Real.log (1 / α) := by field_simp

/-! ## Audit -/

#print axioms quartic_le_telescope
#print axioms tail_sum_sharp
#print axioms tail_sum_le
#print axioms window_tail_le
#print axioms tail_uniformly_bounded
#print axioms information_on_window
#print axioms information_at_counts
#print axioms stops_when_information_exceeds_threshold
#print axioms stops_on_good_window
#print axioms stopping_event_subset_of_accumulation
#print axioms stopping_event_subset
#print axioms window_failure_le
#print axioms stopping_tail_from_window
#print axioms window_bound_decays
#print axioms expected_stopping_le
#print axioms ratio_eventually_le

/-! ## Steps 5-8: accumulation, the window, almost-sure finiteness, and the rate

This section closes the gap the note above flags.  `hunion` is no longer a hypothesis:
`stopping_subset_window_failure` DERIVES the event inclusion from the accumulation
inequality, and `window_union_bound` turns that inclusion into the real-valued union
bound.  What is left as an input is only the per-step confidence guarantee
`mu (good s)^c <= s^-4`, which is the martingale side and belongs to the confidence
modules, not here.

  Step 5  `good_window_accumulation`      Z_t/t >= G - 2 Gamma n/t - C/t on a good window,
          `good_window_rate`              with G = Gamma - 3 L rbar - ebar - Gamma rhobar.
          `stopping_subset_window_failure`  {tau > t} subseteq union of window failures.
  Step 6  `sqrt_window_admissible`        n = ceil(sqrt t) is a legal window for t >= 16,
          `sqrt_window_tail`              and gives Pr(tau > t) <= 8 t^{-3/2}.
  Step 7  `tail_forces_finite_stopping`   a t^{-3/2} tail forces Pr(tau = infinity) = 0.
  Step 8  `sqrt_tail_sum_le`              the t^{-3/2} tail sums, by its own telescoping,
          `expected_stopping_bound_at_level`  E tau <= log(1/alpha)/Gamma + 19,
          `a7_rate_limsup`                so limsup E tau / log(1/alpha) <= 1/Gamma.

The `t^{-3/2}` tail needs its own telescoping lemma: `tail_sum_le` handles `s^-4`, and
`sqrt_cube_le_telescope` is the analogue, resting on the identity
`1/sqrt(t-1) - 1/sqrt t = 1/(sqrt(t-1) sqrt t (sqrt(t-1) + sqrt t))` and `a(a+b) <= 2b^2`.
Every constant in the chain is explicit; none is asymptotic. -/

section Steps5to8

open MeasureTheory

/-- **Step 5.  The good-window accumulation.** -/
theorem good_window_accumulation
    (z : ℕ → ℝ) (Zt : ℝ) (t n : ℕ) (hnt : n ≤ t) (ht : 0 < t)
    (Γ G C : ℝ) (hΓ : 0 ≤ Γ) (hGΓ : G ≤ Γ) (hC : 0 ≤ C)
    (hhead : ∀ s, s < n → -Γ ≤ z s)
    (hwin : ∀ s, n ≤ s → s < t → G ≤ z s)
    (hinit : (∑ s ∈ Finset.range t, z s) - C ≤ Zt) :
    G - 2 * Γ * (n : ℝ) / t - C / t ≤ Zt / t := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hsplit : ∑ s ∈ Finset.range t, z s
      = ∑ s ∈ Finset.range n, z s + ∑ s ∈ Finset.Ico n t, z s := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le n) hnt]
  have hheadsum : -(Γ * (n : ℝ)) ≤ ∑ s ∈ Finset.range n, z s := by
    have h : ∑ s ∈ Finset.range n, (-Γ) ≤ ∑ s ∈ Finset.range n, z s :=
      Finset.sum_le_sum (fun s hs => hhead s (Finset.mem_range.mp hs))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      show ((n : ℝ)) * (-Γ) = -(Γ * (n : ℝ)) from by ring] at h
    exact h
  have hwinsum : ((t : ℝ) - n) * G ≤ ∑ s ∈ Finset.Ico n t, z s := by
    have hle : ∑ s ∈ Finset.Ico n t, G ≤ ∑ s ∈ Finset.Ico n t, z s :=
      Finset.sum_le_sum (fun s hs => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hs; exact hwin s h1 h2)
    have hcard : ((Finset.Ico n t).card : ℝ) = (t : ℝ) - n := by
      rw [Nat.card_Ico]; push_cast [Nat.cast_sub hnt]; ring
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at hle
    exact hle
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkey : G * (t : ℝ) - 2 * Γ * n - C ≤ Zt := by
    have h1 : G * (t : ℝ) - (G + Γ) * n ≤ ∑ s ∈ Finset.range t, z s := by
      rw [hsplit]; nlinarith [hheadsum, hwinsum]
    have h2 : (G + Γ) * (n : ℝ) ≤ 2 * Γ * n := by nlinarith [hGΓ, hnR]
    linarith [hinit, h1, h2]
  rw [le_div_iff₀ htR,
    show (G - 2 * Γ * (n : ℝ) / t - C / t) * t = G * t - 2 * Γ * n - C from by
      field_simp]
  exact hkey

/-- **Step 5, in the roadmap's variables.** -/
theorem good_window_rate
    (z : ℕ → ℝ) (Zt : ℝ) (t n : ℕ) (hnt : n ≤ t) (ht : 0 < t)
    (Γ L rbar ebar rhobar C : ℝ) (hΓ : 0 ≤ Γ) (hC : 0 ≤ C)
    (hslack : 0 ≤ 3 * L * rbar + ebar + Γ * rhobar)
    (hhead : ∀ s, s < n → -Γ ≤ z s)
    (hwin : ∀ s, n ≤ s → s < t → Γ - 3 * L * rbar - ebar - Γ * rhobar ≤ z s)
    (hinit : (∑ s ∈ Finset.range t, z s) - C ≤ Zt) :
    Γ - 3 * L * rbar - ebar - Γ * rhobar - 2 * Γ * (n : ℝ) / t - C / t ≤ Zt / t :=
  good_window_accumulation z Zt t n hnt ht Γ
    (Γ - 3 * L * rbar - ebar - Γ * rhobar) C hΓ (by linarith) hC hhead hwin hinit

/-- **The hard link, now proved.**  Not having stopped by `t` forces one of the window's
confidence events to have failed. -/
theorem stopping_subset_window_failure {Ω : Type*}
    (good : ℕ → Set Ω) (z : Ω → ℕ → ℝ) (Z thr : Ω → ℕ → ℝ) (τ : Ω → ℕ)
    (t n : ℕ) (hnt : n ≤ t) (ht : 0 < t) (Γ G C : ℝ)
    (hΓ : 0 ≤ Γ) (hGΓ : G ≤ Γ) (hC : 0 ≤ C)
    (hτ : ∀ ω s, thr ω s < Z ω s → τ ω ≤ s)
    (hhead : ∀ ω s, s < n → -Γ ≤ z ω s)
    (hgood : ∀ ω s, n ≤ s → s < t → ω ∈ good s → G ≤ z ω s)
    (hinit : ∀ ω, (∑ s ∈ Finset.range t, z ω s) - C ≤ Z ω t)
    (hthr : ∀ ω, thr ω t < G * t - 2 * Γ * n - C) :
    {ω | t < τ ω} ⊆ ⋃ s ∈ Finset.Ico n t, (good s)ᶜ := by
  intro ω hω
  by_contra hc
  simp only [Set.mem_iUnion, not_exists, Set.mem_compl_iff, not_not] at hc
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hwin : ∀ s, n ≤ s → s < t → G ≤ z ω s := by
    intro s h1 h2
    exact hgood ω s h1 h2 (hc s (Finset.mem_Ico.mpr ⟨h1, h2⟩))
  have hacc := good_window_accumulation (z ω) (Z ω t) t n hnt ht Γ G C hΓ hGΓ hC
    (fun s hs => hhead ω s hs) hwin (hinit ω)
  have hZ : G * t - 2 * Γ * n - C ≤ Z ω t := by
    have h1 : (G - 2 * Γ * (n : ℝ) / t - C / t) * t ≤ (Z ω t / t) * t :=
      mul_le_mul_of_nonneg_right hacc htR.le
    rw [div_mul_cancel₀ _ (ne_of_gt htR),
      show (G - 2 * Γ * (n : ℝ) / t - C / t) * t = G * t - 2 * Γ * n - C from by
        field_simp] at h1
    exact h1
  exact absurd (hτ ω t (lt_of_lt_of_le (hthr ω) hZ)) (not_le.2 hω)

/-- **The union bound over the window**, in real-valued probabilities. -/
theorem window_union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (good : ℕ → Set Ω) (τ : Ω → ℕ) (t n : ℕ) (hn : 2 ≤ n)
    (hsub : {ω | t < τ ω} ⊆ ⋃ s ∈ Finset.Ico n t, (good s)ᶜ)
    (hstep : ∀ s, (μ (good s)ᶜ).toReal ≤ 1 / (s : ℝ) ^ 4) :
    (μ {ω | t < τ ω}).toReal ≤ 1 / ((n : ℝ) - 1) ^ 3 := by
  have hfin : ∀ s : ℕ, μ (good s)ᶜ ≠ ⊤ := fun s => measure_ne_top μ _
  have hle : μ {ω | t < τ ω} ≤ ∑ s ∈ Finset.Ico n t, μ (good s)ᶜ :=
    le_trans (measure_mono hsub) (measure_biUnion_finset_le _ _)
  have h1 : (μ {ω | t < τ ω}).toReal ≤ (∑ s ∈ Finset.Ico n t, μ (good s)ᶜ).toReal :=
    ENNReal.toReal_mono (by
      refine (ENNReal.sum_lt_top.mpr ?_).ne
      exact fun s _ => lt_top_iff_ne_top.mpr (hfin s)) hle
  rw [ENNReal.toReal_sum (fun s _ => hfin s)] at h1
  exact le_trans (le_trans h1 (Finset.sum_le_sum (fun s _ => hstep s))) (tail_sum_le n t hn)

/-- **Step 6.  The window at `ceil(sqrt t)` is admissible.** -/
theorem sqrt_window_admissible (t : ℕ) (ht : 16 ≤ t) :
    2 ≤ ⌈Real.sqrt t⌉₊ ∧ ⌈Real.sqrt t⌉₊ ≤ t ∧
      Real.sqrt t / 2 ≤ (⌈Real.sqrt t⌉₊ : ℝ) - 1 := by
  have htR : (16 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by linarith
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs4 : (4 : ℝ) ≤ Real.sqrt t := by
    have := Real.sqrt_le_sqrt htR
    rwa [h16] at this
  have hceil : Real.sqrt t ≤ (⌈Real.sqrt t⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨?_, ?_, by linarith⟩
  · have : (4 : ℝ) ≤ (⌈Real.sqrt t⌉₊ : ℝ) := le_trans hs4 hceil
    have h4 : (4 : ℕ) ≤ ⌈Real.sqrt t⌉₊ := by exact_mod_cast this
    omega
  · refine Nat.ceil_le.mpr ?_
    have hsq : Real.sqrt t ≤ Real.sqrt ((t : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq ht0] at hsq

/-- **Step 6, assembled.**  At the `sqrt t` window the tail is `8 t^{-3/2}`. -/
theorem sqrt_window_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (good : ℕ → Set Ω) (τ : Ω → ℕ) (t : ℕ) (ht : 16 ≤ t)
    (hsub : {ω | t < τ ω} ⊆ ⋃ s ∈ Finset.Ico ⌈Real.sqrt t⌉₊ t, (good s)ᶜ)
    (hstep : ∀ s, (μ (good s)ᶜ).toReal ≤ 1 / (s : ℝ) ^ 4) :
    (μ {ω | t < τ ω}).toReal ≤ 8 / (Real.sqrt t) ^ 3 := by
  obtain ⟨hn2, _, hsq⟩ := sqrt_window_admissible t ht
  exact le_trans (window_union_bound μ good τ t ⌈Real.sqrt t⌉₊ hn2 hsub hstep)
    (window_bound_decays t ⌈Real.sqrt t⌉₊ (by omega) hn2 hsq)

/-- **Step 7.  The stopping time is almost surely finite.** -/
theorem tail_forces_finite_stopping (P : ℕ → ℝ) (Pinf : ℝ) (hnn : 0 ≤ Pinf)
    (hPinf : ∀ t, 16 ≤ t → Pinf ≤ P t)
    (htail : ∀ t, 16 ≤ t → P t ≤ 8 / (Real.sqrt t) ^ 3) : Pinf = 0 := by
  by_contra hne
  have hpos : 0 < Pinf := lt_of_le_of_ne hnn (Ne.symm hne)
  set m : ℕ := max 16 (⌈8 / Pinf⌉₊ + 1) with hm
  have hm16 : 16 ≤ m := le_max_left _ _
  have hmc : ⌈8 / Pinf⌉₊ + 1 ≤ m := le_max_right _ _
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm16
    linarith
  have hsq : Real.sqrt m ≥ 1 := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt m :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < m))
    rwa [Real.sqrt_one] at h1
  have hcube : (m : ℝ) ≤ (Real.sqrt m) ^ 3 := by
    have h2 : (Real.sqrt m) ^ 2 = (m : ℝ) := Real.sq_sqrt (le_of_lt hmR)
    nlinarith [hsq, h2]
  have hchain : Pinf ≤ 8 / (m : ℝ) := by
    have h1 := le_trans (hPinf m hm16) (htail m hm16)
    have h2 : 8 / (Real.sqrt m) ^ 3 ≤ 8 / (m : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hmR hcube
    linarith
  have hbig : 8 / Pinf < (m : ℝ) := by
    have h1 : (8 : ℝ) / Pinf ≤ (⌈8 / Pinf⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈8 / Pinf⌉₊ + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmc
    push_cast at h2
    linarith
  rw [div_lt_iff₀ hpos] at hbig
  rw [le_div_iff₀ hmR] at hchain
  linarith

/-- The pointwise telescoping step for the `t^{-3/2}` tail.  With `a = sqrt(t-1)` and
`b = sqrt t`, the difference `1/a - 1/b` equals `1/(a b (a+b))`, and `a(a+b) <= 2 b^2`. -/
theorem sqrt_cube_le_telescope (t : ℕ) (ht : 2 ≤ t) :
    8 / (Real.sqrt t) ^ 3 ≤ 16 * (1 / Real.sqrt ((t : ℝ) - 1) - 1 / Real.sqrt t) := by
  have htR : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  set a := Real.sqrt ((t : ℝ) - 1) with hadef
  set b := Real.sqrt (t : ℝ) with hbdef
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = (t : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (t : ℝ) := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := by nlinarith [ha2, hb2, ha0, hb0]
  have hid : 1 / a - 1 / b = 1 / (a * b * (a + b)) := by
    rw [div_sub_div _ _ (ne_of_gt ha0) (ne_of_gt hb0), eq_div_iff (by positivity)]
    field_simp
    nlinarith [ha2, hb2]
  rw [hid, div_le_iff₀ (by positivity), mul_comm (16 : ℝ), mul_assoc,
    one_div_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith [ha0, hb0, hab, sq_nonneg (b - a), pow_pos hb0 3]

/-- The sharp telescoped tail, in the form the induction needs. -/
theorem sqrt_tail_sum_sharp (n : ℕ) (hn : 2 ≤ n) :
    ∀ M : ℕ, n ≤ M →
      ∑ t ∈ Finset.Ico n M, 8 / (Real.sqrt t) ^ 3
        ≤ 16 / Real.sqrt ((n : ℝ) - 1) - 16 / Real.sqrt ((M : ℝ) - 1) := by
  intro M
  induction M with
  | zero => intro h; omega
  | succ i ihi =>
      intro h
      rcases Nat.lt_or_ge i n with hlt | hge
      · have hni : n = i + 1 := by omega
        subst hni
        simp only [Finset.Ico_self, Finset.sum_empty]
        linarith
      · rw [Finset.sum_Ico_succ_top hge]
        have hi2 : 2 ≤ i := le_trans hn hge
        have hstep := sqrt_cube_le_telescope i hi2
        have hprev := ihi hge
        have hcast : ((i + 1 : ℕ) : ℝ) - 1 = (i : ℝ) := by push_cast; ring
        rw [hcast]
        have hexp : 16 * (1 / Real.sqrt ((i : ℝ) - 1) - 1 / Real.sqrt i)
            = 16 / Real.sqrt ((i : ℝ) - 1) - 16 / Real.sqrt i := by ring
        rw [hexp] at hstep
        linarith

theorem sqrt_tail_sum_le (n M : ℕ) (hn : 2 ≤ n) :
    ∑ t ∈ Finset.Ico n M, 8 / (Real.sqrt t) ^ 3 ≤ 16 / Real.sqrt ((n : ℝ) - 1) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnnn : (0 : ℝ) ≤ 16 / Real.sqrt ((n : ℝ) - 1) := by positivity
  rcases Nat.lt_or_ge M n with hlt | hge
  · rw [Finset.Ico_eq_empty_of_le (le_of_lt hlt), Finset.sum_empty]; exact hnnn
  · have hmnn : (0 : ℝ) ≤ 16 / Real.sqrt ((M : ℝ) - 1) := by positivity
    linarith [sqrt_tail_sum_sharp n hn M hge]

/-- **Step 8.  The expected stopping time at level `alpha`.**

With the window at `sqrt t`, the truncated expectations are bounded by the deterministic
head `t_0 = ceil(log(1/alpha)/Gamma) + 2` plus the `t^{-3/2}` tail from `t_0`, which the
telescoping bounds by `16/sqrt(t_0 - 1) <= 16`.  The constant is explicit. -/
theorem expected_stopping_bound_at_level
    (Esum p : ℕ → ℝ) (Γ α : ℝ) (hΓ : 0 < Γ) (hα : 0 < α) (hα1 : α < 1)
    (hp : ∀ t, p t ≤ 8 / (Real.sqrt t) ^ 3)
    (hEsum : ∀ M, Esum M ≤ ((⌈Real.log (1 / α) / Γ⌉₊ + 2 : ℕ) : ℝ)
        + ∑ t ∈ Finset.Ico (⌈Real.log (1 / α) / Γ⌉₊ + 2) M, p t) :
    ∀ M, Esum M ≤ Real.log (1 / α) / Γ + 19 := by
  intro M
  set t0 : ℕ := ⌈Real.log (1 / α) / Γ⌉₊ + 2 with ht0
  have ht02 : 2 ≤ t0 := by omega
  have hlog : 0 ≤ Real.log (1 / α) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hα]; linarith
  have hdiv : 0 ≤ Real.log (1 / α) / Γ := div_nonneg hlog (le_of_lt hΓ)
  have hceil : (⌈Real.log (1 / α) / Γ⌉₊ : ℝ) ≤ Real.log (1 / α) / Γ + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hdiv)
  have ht0R : (t0 : ℝ) ≤ Real.log (1 / α) / Γ + 3 := by
    rw [ht0]; push_cast; linarith
  have hsum : ∑ t ∈ Finset.Ico t0 M, p t ≤ 16 / Real.sqrt ((t0 : ℝ) - 1) :=
    le_trans (Finset.sum_le_sum (fun t _ => hp t)) (sqrt_tail_sum_le t0 M ht02)
  have ht01 : (1 : ℝ) ≤ (t0 : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (t0 : ℝ) := by exact_mod_cast ht02
    linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((t0 : ℝ) - 1) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt ((t0 : ℝ) - 1) := Real.sqrt_le_sqrt ht01
    rwa [Real.sqrt_one] at h1
  have h16 : 16 / Real.sqrt ((t0 : ℝ) - 1) ≤ 16 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith [hEsum M, hsum, ht0R, h16]

/-- **Step 8, the conclusion.**  The ratio of the expected stopping time to `log(1/alpha)`
is eventually within `eps` of `1/Gamma`: the limsup is at most `1/Gamma`. -/
theorem a7_rate_limsup (Eτ : ℝ → ℝ) (Γ : ℝ) (hΓ : 0 < Γ)
    (hbound : ∀ α, 0 < α → α < 1 → Eτ α ≤ Real.log (1 / α) / Γ + 19)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ α0 : ℝ, 0 < α0 ∧ α0 < 1 ∧ ∀ α, 0 < α → α < α0 →
      Eτ α / Real.log (1 / α) ≤ 1 / Γ + ε :=
  ratio_eventually_le Eτ Γ 19 hΓ (by norm_num) hbound ε hε

/-! ### Audit for Steps 5-8 -/

#print axioms good_window_accumulation
#print axioms good_window_rate
#print axioms stopping_subset_window_failure
#print axioms window_union_bound
#print axioms sqrt_window_admissible
#print axioms sqrt_window_tail
#print axioms tail_forces_finite_stopping
#print axioms sqrt_cube_le_telescope
#print axioms sqrt_tail_sum_le
#print axioms expected_stopping_bound_at_level
#print axioms a7_rate_limsup

end Steps5to8

section ExplorationCost

/-! # (A2) and (A3): a cost law in the CUMULATIVE EXPLORATION

`J_true(w*_proxy) = 0` does not by itself give `E tau = Omega(log^2(1/alpha))`.  A learner
may add forced exploration, its estimated extrema may move, or an approximate oracle may
put mass on the starved cells.  What the rate really depends on is how much exploration
the sampling rule accumulates, and the statement below makes that the hypothesis rather
than the conclusion.

  (A1)  change of measure:   `(d^2/2) E N_movable(tau) >= r * kl(1-alpha, alpha)`
  (A2)  the sampling rule:   `E N_movable(tau) <= C + C' E[tau^a]`,  `0 < a < 1`
  (A3)  Jensen:              `E tau >= ((A - C)/C')^{1/a}`,  `A` the (A1) right side.

`a = 1/2` --- cumulative exploration `O(sqrt t)` --- gives `Omega(log^2(1/alpha))`;
`a = 1` gives only `Omega(log(1/alpha))`.  The hard half is (A2), and what is proved here
is the accounting that reduces it to three measurable quantities, plus the exploration sum
and the Jensen step.  (A1) is the standard transportation lemma and is an input. -/

/-- **The accounting.**  Movable-cell mass accrues only from a bad estimate, from forced
exploration, or from the oracle's own slack, so it telescopes into their sum. -/
theorem movable_count_accounting (Nmov bad rho eps : ℕ → ℝ) (h0 : Nmov 0 = 0)
    (hstep : ∀ s, Nmov (s + 1) - Nmov s ≤ bad s + rho s + eps s) :
    ∀ t, Nmov t ≤ ∑ s ∈ Finset.range t, (bad s + rho s + eps s) := by
  intro t
  induction t with
  | zero => simp [h0]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep n, ih]

/-- Forced exploration at rate `1/sqrt(s+1)` accumulates to `2 sqrt t`, so `a = 1/2`. -/
theorem sum_inv_sqrt_le : ∀ t : ℕ,
    ∑ s ∈ Finset.range t, 1 / Real.sqrt (s + 1) ≤ 2 * Real.sqrt t := by
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hs : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      have hsn : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hsq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
      have hsq0 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn
      -- 1/sqrt(n+1) <= 2 sqrt(n+1) - 2 sqrt n
      have key : 1 / Real.sqrt ((n : ℝ) + 1)
          ≤ 2 * Real.sqrt ((n : ℝ) + 1) - 2 * Real.sqrt (n : ℝ) := by
        rw [div_le_iff₀ hs]
        nlinarith [hsq, hsq0, hsn, hs, Real.sqrt_nonneg (n : ℝ)]
      have hcast : ((n : ℕ) + 1 : ℕ) = (n : ℕ) + 1 := rfl
      have hc : Real.sqrt (((n + 1 : ℕ) : ℝ)) = Real.sqrt ((n : ℝ) + 1) := by
        norm_cast
      rw [hc]
      linarith [ih, key]

/-- **(A3), the Jensen step.**  With `E[tau^a] <= (E tau)^a` for `0 < a <= 1`, the
accumulated-exploration bound inverts into a lower bound on `E tau`. -/
theorem jensen_step (A C C' Eτ ma a : ℝ) (ha : 0 < a) (hC' : 0 < C')
    (hEτ : 0 ≤ Eτ) (hAC : C ≤ A) (hma : ma ≤ Eτ ^ a) (hA : A ≤ C + C' * ma) :
    ((A - C) / C') ^ (1 / a) ≤ Eτ := by
  have hb : (0 : ℝ) ≤ (A - C) / C' := div_nonneg (by linarith) (le_of_lt hC')
  have h1 : (A - C) / C' ≤ ma := by rw [div_le_iff₀ hC']; linarith
  have h2 : (A - C) / C' ≤ Eτ ^ a := le_trans h1 hma
  have hstep := Real.rpow_le_rpow hb h2 (le_of_lt (by positivity : (0:ℝ) < 1 / a))
  rwa [← Real.rpow_mul hEτ, mul_one_div, div_self (ne_of_gt ha), Real.rpow_one] at hstep

/-- **The law, at `a = 1/2`.**  Cumulative exploration of order `sqrt t` forces a SQUARED
logarithm: the change-of-measure budget `A` enters to the power `1/a = 2`. -/
theorem sqrt_exploration_rate (A C C' Eτ ma : ℝ) (hC' : 0 < C') (hEτ : 0 ≤ Eτ)
    (hAC : C ≤ A) (hma : ma ≤ Eτ ^ ((1 : ℝ) / 2)) (hA : A ≤ C + C' * ma) :
    ((A - C) / C') ^ (2 : ℕ) ≤ Eτ := by
  have h := jensen_step A C C' Eτ ma (1 / 2) (by norm_num) hC' hEτ hAC hma hA
  rw [show (1 : ℝ) / (1 / 2) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  exact h

/-- **And at `a = 1`, only a single logarithm.**  So the exponent is a property of the
sampling rule's exploration, not of the separation: writing `log^2` without a count bound
of order `sqrt t` would be asserting something about the algorithm that has not been
shown. -/
theorem linear_exploration_rate (A C C' Eτ ma : ℝ) (hC' : 0 < C') (hEτ : 0 ≤ Eτ)
    (hAC : C ≤ A) (hma : ma ≤ Eτ) (hA : A ≤ C + C' * ma) :
    (A - C) / C' ≤ Eτ := by
  have h1 : (A - C) / C' ≤ ma := by rw [div_le_iff₀ hC']; linarith
  linarith [h1, hma]

/-- **The chain, assembled.**  (A1) supplies `A`, `movable_count_accounting` plus the
exploration sum supply `C` and `C'`, and `jensen_step` inverts.  Everything except (A1)
and the per-round tail is proved. -/
theorem exploration_cost_law (r d kl C C' Eτ ma a : ℝ)
    (ha : 0 < a) (hC' : 0 < C') (hEτ : 0 ≤ Eτ) (hd : 0 < d)
    (hAC : C ≤ 2 * r / d ^ 2 * kl)
    (hma : ma ≤ Eτ ^ a)
    (hA2 : 2 * r / d ^ 2 * kl ≤ C + C' * ma) :
    ((2 * r / d ^ 2 * kl - C) / C') ^ (1 / a) ≤ Eτ :=
  jensen_step (2 * r / d ^ 2 * kl) C C' Eτ ma a ha hC' hEτ hAC hma hA2

#print axioms movable_count_accounting
#print axioms sum_inv_sqrt_le
#print axioms jensen_step
#print axioms sqrt_exploration_rate
#print axioms linear_exploration_rate
#print axioms exploration_cost_law

end ExplorationCost

end CIGAMF.P13.PaperA7Tail
