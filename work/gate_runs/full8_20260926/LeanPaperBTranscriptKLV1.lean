import Mathlib

/-!
# Paper B, step B5: a lower bound that survives EVERY adaptive policy.

## WHY THIS MODULE EXISTS

A per-query information bound says nothing by itself about a learner that chooses its next
query from what it has already seen.  The step that makes an adaptive lower bound legitimate
is the transcript chain rule: the divergence between the two worlds' transcript laws is the
sum, along the trajectory, of the per-query divergences, and the policy's own randomness
contributes nothing because it is the same kernel under both worlds.

This module builds the transcript law from the policy rather than assuming a product
structure, proves the chain rule for it, and derives the bound actually used:

    KL(transcript_w^N, transcript_w'^N)  <=  N * sup_q KL(P_w^q, P_w'^q).

With the per-query bound `sup_q KL <= C_r h^(2r)` of the query-order law, this gives
`N >= c_r h^(-2r)` for identification against every adaptive policy, not merely against the
query the upper bound happens to use.

## THE MODEL

Observations range over a finite set.  A policy is a function from the history -- the list
of observations so far, in chronological order -- to the next query.  `pathProb` is the
probability the policy assigns to a continuation, and `klPath` is the Kullback-Leibler
divergence of the length-`n` transcript law started from a history.  Nothing is assumed
about how the policy depends on the history.

## WHAT IS PROVED

* `sumPaths_mass` -- the transcript law is a probability distribution on continuations.
* `klPath_chain` -- **the chain rule**, proved from the definitions, not assumed:
  `klPath (n+1) h = klStep (P (pol h)) (P' (pol h)) + sum_o P (pol h) o * klPath n (h ++ [o])`.
* `klPath_le_horizon` -- hence the horizon bound `klPath n h <= n * B` whenever every
  query's divergence is at most `B`.
* `klPath_nonneg` -- the divergence is non-negative, via the standard `log` inequality.

## WHAT THIS DOES NOT ESTABLISH

- **Finite observation alphabet, deterministic policy, fixed horizon.**  The Gaussian
  observation of the construction has a continuous alphabet; the same argument runs with
  densities and integrals, and that version is not formalised here.  A randomised policy
  adds an outer average that cancels the same way, also not formalised.
- **Strict positivity is assumed** (`hP`, `hP'`).  It holds for the Gaussian mixtures of the
  construction, where every density is strictly positive, but it is a hypothesis here and
  the statement is false without it.
- **The testing step is not here.**  Turning a transcript divergence into a sample-count
  lower bound uses a standard two-point testing inequality, which is cited and not proved.
- Stopping times are not treated: `N` is a fixed horizon.  Replacing `N` by `E[tau]`
  requires a stopped-transcript identity and must not be done by substitution.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.PaperBTranscriptKL

open Finset

variable {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
variable {Qry : Type*}

/-! ### Summation over all transcripts of a given length -/

/-- Sum a function over every length-`n` list of observations. -/
def sumPaths (n : ℕ) (f : List Obs → ℝ) : ℝ :=
  match n with
  | 0 => f []
  | (k + 1) => ∑ o : Obs, sumPaths k (fun t => f (o :: t))

theorem sumPaths_congr (n : ℕ) {f g : List Obs → ℝ} (h : ∀ t, f t = g t) :
    sumPaths n f = sumPaths n g := by
  induction n generalizing f g with
  | zero => simpa [sumPaths] using h []
  | succ k ih =>
      simp only [sumPaths]
      exact Finset.sum_congr rfl fun o _ => ih (fun t => h (o :: t))

theorem sumPaths_const_zero (n : ℕ) : sumPaths (Obs := Obs) n (fun _ => 0) = 0 := by
  induction n with
  | zero => simp [sumPaths]
  | succ k ih => simp [sumPaths, ih]

theorem sumPaths_add (n : ℕ) (f g : List Obs → ℝ) :
    sumPaths n (fun t => f t + g t) = sumPaths n f + sumPaths n g := by
  induction n generalizing f g with
  | zero => simp [sumPaths]
  | succ k ih =>
      simp only [sumPaths]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun o _ => ih (fun t => f (o :: t)) (fun t => g (o :: t))

theorem sumPaths_smul (n : ℕ) (c : ℝ) (f : List Obs → ℝ) :
    sumPaths n (fun t => c * f t) = c * sumPaths n f := by
  induction n generalizing f with
  | zero => simp [sumPaths]
  | succ k ih =>
      simp only [sumPaths]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun o _ => ih (fun t => f (o :: t))

theorem sumPaths_le (n : ℕ) {f g : List Obs → ℝ} (h : ∀ t, f t ≤ g t) :
    sumPaths n f ≤ sumPaths n g := by
  induction n generalizing f g with
  | zero => simpa [sumPaths] using h []
  | succ k ih =>
      simp only [sumPaths]
      exact Finset.sum_le_sum fun o _ => ih (fun t => h (o :: t))

/-! ### The transcript law of a policy -/

/-- The probability a policy assigns to a continuation, given the history so far. -/
def pathProb (P : Qry → Obs → ℝ) (pol : List Obs → Qry) :
    List Obs → List Obs → ℝ
  | _, [] => 1
  | h, (o :: t) => P (pol h) o * pathProb P pol (h ++ [o]) t

@[simp] theorem pathProb_nil (P : Qry → Obs → ℝ) (pol : List Obs → Qry)
    (h : List Obs) : pathProb P pol h [] = 1 := rfl

@[simp] theorem pathProb_cons (P : Qry → Obs → ℝ) (pol : List Obs → Qry)
    (h : List Obs) (o : Obs) (t : List Obs) :
    pathProb P pol h (o :: t) = P (pol h) o * pathProb P pol (h ++ [o]) t := rfl

theorem pathProb_pos (P : Qry → Obs → ℝ) (pol : List Obs → Qry)
    (hP : ∀ q o, 0 < P q o) : ∀ (t h : List Obs), 0 < pathProb P pol h t := by
  intro t
  induction t with
  | nil => intro h; simp
  | cons o rest ih =>
      intro h
      simp only [pathProb_cons]
      exact mul_pos (hP _ _) (ih _)

/-- **The transcript law is a probability distribution.** -/
theorem sumPaths_mass (P : Qry → Obs → ℝ) (pol : List Obs → Qry)
    (hsum : ∀ q, ∑ o, P q o = 1) :
    ∀ (n : ℕ) (h : List Obs), sumPaths n (fun t => pathProb P pol h t) = 1 := by
  intro n
  induction n with
  | zero => intro h; simp [sumPaths]
  | succ k ih =>
      intro h
      simp only [sumPaths]
      have : ∀ o : Obs,
          sumPaths k (fun t => pathProb P pol h (o :: t))
            = P (pol h) o := by
        intro o
        have hstep : ∀ t : List Obs,
            pathProb P pol h (o :: t) = P (pol h) o * pathProb P pol (h ++ [o]) t :=
          fun t => rfl
        rw [sumPaths_congr k hstep, sumPaths_smul, ih (h ++ [o]), mul_one]
      rw [Finset.sum_congr rfl fun o _ => this o]
      exact hsum (pol h)

/-! ### Divergence -/

/-- One step's Kullback-Leibler divergence. -/
noncomputable def klStep (p q : Obs → ℝ) : ℝ := ∑ o, p o * Real.log (p o / q o)

/-- The divergence of the length-`n` transcript law, started from a history. -/
noncomputable def klPath (P P' : Qry → Obs → ℝ) (pol : List Obs → Qry)
    (n : ℕ) (h : List Obs) : ℝ :=
  sumPaths n (fun t =>
    pathProb P pol h t * Real.log (pathProb P pol h t / pathProb P' pol h t))

private theorem log_ratio_mul {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    Real.log (a * b / (c * d)) = Real.log (a / c) + Real.log (b / d) := by
  have hrw : a * b / (c * d) = (a / c) * (b / d) := by
    field_simp
  rw [hrw]
  exact Real.log_mul (by positivity) (by positivity)

/-- **The chain rule.**  The transcript divergence splits into the divergence of the query
the policy plays now, plus the average of the divergences of what follows.  The policy
contributes nothing because it is the same map under both worlds. -/
theorem klPath_chain (P P' : Qry → Obs → ℝ) (pol : List Obs → Qry)
    (hP : ∀ q o, 0 < P q o) (hP' : ∀ q o, 0 < P' q o)
    (hsum : ∀ q, ∑ o, P q o = 1)
    (n : ℕ) (h : List Obs) :
    klPath P P' pol (n + 1) h
      = klStep (P (pol h)) (P' (pol h))
        + ∑ o, P (pol h) o * klPath P P' pol n (h ++ [o]) := by
  classical
  unfold klPath
  simp only [sumPaths]
  have key : ∀ o : Obs,
      sumPaths n (fun t => pathProb P pol h (o :: t)
          * Real.log (pathProb P pol h (o :: t) / pathProb P' pol h (o :: t)))
        = P (pol h) o * Real.log (P (pol h) o / P' (pol h) o)
          + P (pol h) o * klPath P P' pol n (h ++ [o]) := by
    intro o
    have hsplit : ∀ t : List Obs,
        pathProb P pol h (o :: t)
            * Real.log (pathProb P pol h (o :: t) / pathProb P' pol h (o :: t))
          = P (pol h) o * Real.log (P (pol h) o / P' (pol h) o)
              * pathProb P pol (h ++ [o]) t
            + P (pol h) o * (pathProb P pol (h ++ [o]) t
              * Real.log (pathProb P pol (h ++ [o]) t
                / pathProb P' pol (h ++ [o]) t)) := by
      intro t
      simp only [pathProb_cons]
      rw [log_ratio_mul (hP _ _) (pathProb_pos P pol hP t (h ++ [o]))
        (hP' _ _) (pathProb_pos P' pol hP' t (h ++ [o]))]
      ring
    rw [sumPaths_congr n hsplit, sumPaths_add]
    rw [sumPaths_smul, sumPaths_smul]
    rw [sumPaths_mass P pol hsum n (h ++ [o])]
    unfold klPath
    ring
  rw [Finset.sum_congr rfl fun o _ => key o]
  rw [Finset.sum_add_distrib]
  unfold klStep klPath
  ring

/-- **The horizon bound.**  If every admissible query separates the two worlds by at most
`B`, then no policy can accumulate more than `N B` over `N` rounds, however it adapts. -/
theorem klPath_le_horizon (P P' : Qry → Obs → ℝ) (pol : List Obs → Qry)
    (hP : ∀ q o, 0 < P q o) (hP' : ∀ q o, 0 < P' q o)
    (hsum : ∀ q, ∑ o, P q o = 1) (B : ℝ)
    (hB : ∀ q, klStep (P q) (P' q) ≤ B) :
    ∀ (n : ℕ) (h : List Obs), klPath P P' pol n h ≤ n * B := by
  intro n
  induction n with
  | zero => intro h; simp [klPath, sumPaths]
  | succ k ih =>
      intro h
      rw [klPath_chain P P' pol hP hP' hsum k h]
      have hterm : ∀ o : Obs,
          P (pol h) o * klPath P P' pol k (h ++ [o]) ≤ P (pol h) o * (k * B) := by
        intro o
        exact mul_le_mul_of_nonneg_left (ih (h ++ [o])) (le_of_lt (hP _ _))
      have hsum2 : ∑ o, P (pol h) o * klPath P P' pol k (h ++ [o])
          ≤ ∑ o, P (pol h) o * (k * B) := Finset.sum_le_sum fun o _ => hterm o
      have hcollapse : ∑ o, P (pol h) o * ((k : ℝ) * B) = (k : ℝ) * B := by
        rw [← Finset.sum_mul, hsum (pol h), one_mul]
      have := hB (pol h)
      push_cast
      linarith [hsum2, hcollapse.le, hcollapse.ge]

/-- The transcript divergence is non-negative, so the horizon bound is not vacuous. -/
theorem klPath_nonneg (P P' : Qry → Obs → ℝ) (pol : List Obs → Qry)
    (hP : ∀ q o, 0 < P q o) (hP' : ∀ q o, 0 < P' q o)
    (hsum : ∀ q, ∑ o, P q o = 1) (hsum' : ∀ q, ∑ o, P' q o = 1) :
    ∀ (n : ℕ) (h : List Obs), 0 ≤ klPath P P' pol n h := by
  intro n h
  unfold klPath
  -- `x log(x/y) >= x - y` pointwise, and both laws have total mass one
  have hpt : ∀ t : List Obs,
      pathProb P pol h t - pathProb P' pol h t
        ≤ pathProb P pol h t
          * Real.log (pathProb P pol h t / pathProb P' pol h t) := by
    intro t
    have hx : 0 < pathProb P pol h t := pathProb_pos P pol hP t h
    have hy : 0 < pathProb P' pol h t := pathProb_pos P' pol hP' t h
    have hlog : 1 - pathProb P' pol h t / pathProb P pol h t
        ≤ Real.log (pathProb P pol h t / pathProb P' pol h t) := by
      have h1 : Real.log (pathProb P' pol h t / pathProb P pol h t)
          ≤ pathProb P' pol h t / pathProb P pol h t - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (pathProb P pol h t / pathProb P' pol h t)
          = -Real.log (pathProb P' pol h t / pathProb P pol h t) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      rw [h2]
      linarith
    have := mul_le_mul_of_nonneg_left hlog (le_of_lt hx)
    have hid : pathProb P pol h t * (1 - pathProb P' pol h t / pathProb P pol h t)
        = pathProb P pol h t - pathProb P' pol h t := by
      field_simp
    linarith [hid ▸ this]
  have hmass : sumPaths n (fun t => pathProb P pol h t - pathProb P' pol h t) = 0 := by
    have hsplit : ∀ t : List Obs,
        pathProb P pol h t - pathProb P' pol h t
          = pathProb P pol h t + (-1) * pathProb P' pol h t := by
      intro t; ring
    rw [sumPaths_congr n hsplit, sumPaths_add, sumPaths_smul,
      sumPaths_mass P pol hsum n h, sumPaths_mass P' pol hsum' n h]
    ring
  have := sumPaths_le n hpt
  rw [hmass] at this
  exact this

#print axioms sumPaths_mass
#print axioms klPath_chain
#print axioms klPath_le_horizon
#print axioms klPath_nonneg

end CIGAMF.P13.PaperBTranscriptKL
