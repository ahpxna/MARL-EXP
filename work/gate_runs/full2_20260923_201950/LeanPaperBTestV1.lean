import «LeanPaperBGeometryV1»

/-!
# Paper B, the matching upper bound: the per-pair test bound, DERIVED

`bounds_same_order` in `LeanPaperBGeometryV1` takes `hbd : forall i, err i <= delta / K`
as a HYPOTHESIS: some test is assumed to distinguish each pair at level `delta/K`.  That
hypothesis is the whole content of the upper bound, so assuming it assumes the result.

This module discharges it.  The test is exhibited (the likelihood-ratio test), its error is
computed exactly (not bounded by a named inequality), and the bound is derived from the
observation model alone:

    err  =  (1/2) sum_t min(P t, Q t)            -- exact, the LRT's own error
         <= (1/2) (sum_o sqrt(p o q o))^N        -- min <= geometric mean, then tensorise
          = (1/2) (1 - H^2(p,q))^N
         <= (1/2) exp(-N H^2(p,q))
         <= delta / K                            -- once N >= log(K/delta) / H^2.

With `H^2 >= c0 h^(2r)` the sample size is `N = O(h^(-2r) log(K/delta))`, which is the
exponent the lower bound produces.  Nothing here is assumed about the test.
-/

namespace CIGAMF.P13.PaperBTest

open Finset

variable {Obs : Type*} [Fintype Obs] [DecidableEq Obs]

/-! ## Affinity and its tensorisation -/

/-- The Hellinger affinity (Bhattacharyya coefficient) of two laws on one observation. -/
noncomputable def affinity (p q : Obs → ℝ) : ℝ := ∑ o, Real.sqrt (p o * q o)

/-- Squared Hellinger distance in the normalisation `H^2 = 1 - affinity`. -/
noncomputable def hsq (p q : Obs → ℝ) : ℝ := 1 - affinity p q

/-- The law of `N` independent observations. -/
noncomputable def prodLaw (N : ℕ) (p : Obs → ℝ) : (Fin N → Obs) → ℝ :=
  fun t => ∏ i, p (t i)

theorem affinity_nonneg (p q : Obs → ℝ) : 0 ≤ affinity p q :=
  Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

theorem prodLaw_nonneg (N : ℕ) (p : Obs → ℝ) (hp : ∀ o, 0 ≤ p o) (t : Fin N → Obs) :
    0 ≤ prodLaw N p t :=
  Finset.prod_nonneg (fun i _ => hp (t i))

/-- The square root of a product of non-negative numbers. -/
theorem sqrt_prod' {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
          Real.sqrt_mul (hf a (Finset.mem_insert_self a s)),
          ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Summing a product over all sequences factorises. -/
theorem sum_prod_eq_pow (N : ℕ) (g : Obs → ℝ) :
    ∑ t : Fin N → Obs, ∏ i, g (t i) = (∑ o, g o) ^ N := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin N => (univ : Finset Obs)) (fun _ o => g o)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [Fintype.piFinset_univ] at h
  exact h.symm

/-- **The product law is a probability distribution.**  This also shows the hypotheses of
the theorems below are satisfiable rather than vacuous. -/
theorem prodLaw_sum (N : ℕ) (p : Obs → ℝ) (hp1 : ∑ o, p o = 1) :
    ∑ t : Fin N → Obs, prodLaw N p t = 1 := by
  unfold prodLaw
  rw [sum_prod_eq_pow N p, hp1, one_pow]

/-- **Tensorisation.**  The affinity of `N` independent copies is the `N`-th power. -/
theorem affinity_prodLaw (N : ℕ) (p q : Obs → ℝ) (hp : ∀ o, 0 ≤ p o) (hq : ∀ o, 0 ≤ q o) :
    ∑ t : Fin N → Obs, Real.sqrt (prodLaw N p t * prodLaw N q t) = (affinity p q) ^ N := by
  classical
  have hterm : ∀ t : Fin N → Obs,
      Real.sqrt (prodLaw N p t * prodLaw N q t) = ∏ i, Real.sqrt (p (t i) * q (t i)) := by
    intro t
    unfold prodLaw
    rw [← Finset.prod_mul_distrib]
    exact sqrt_prod' _ _ (fun i _ => mul_nonneg (hp (t i)) (hq (t i)))
  rw [Finset.sum_congr rfl (fun t _ => hterm t)]
  exact sum_prod_eq_pow N (fun o => Real.sqrt (p o * q o))

/-! ## The likelihood-ratio test and its exact error -/

/-- Type-I error: the test says `q` when the truth is `p`.  The test declares the first
world exactly on the sequences it makes at least as likely. -/
noncomputable def errI (N : ℕ) (p q : Obs → ℝ) : ℝ :=
  ∑ t : Fin N → Obs, if prodLaw N q t ≤ prodLaw N p t then 0 else prodLaw N p t

/-- Type-II error: the test says `p` when the truth is `q`. -/
noncomputable def errII (N : ℕ) (p q : Obs → ℝ) : ℝ :=
  ∑ t : Fin N → Obs, if prodLaw N q t ≤ prodLaw N p t then prodLaw N q t else 0

/-- **The average error of the test, computed exactly.**  No inequality is used here: the
two error sums recombine, term by term, into the sum of pointwise minima. -/
theorem err_eq_sum_min (N : ℕ) (p q : Obs → ℝ) :
    (errI N p q + errII N p q) / 2
      = (∑ t : Fin N → Obs, min (prodLaw N p t) (prodLaw N q t)) / 2 := by
  classical
  unfold errI errII
  rw [← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h : prodLaw N q t ≤ prodLaw N p t
  · rw [if_pos h, if_pos h, zero_add, min_eq_right h]
  · rw [if_neg h, if_neg h, add_zero, min_eq_left (not_le.mp h).le]

/-- **The test's error is at most half the `N`-th power of the affinity.** -/
theorem err_le_affinity_pow (N : ℕ) (p q : Obs → ℝ) (hp : ∀ o, 0 ≤ p o) (hq : ∀ o, 0 ≤ q o) :
    (errI N p q + errII N p q) / 2 ≤ (affinity p q) ^ N / 2 := by
  classical
  rw [err_eq_sum_min]
  have hstep : ∀ t : Fin N → Obs,
      min (prodLaw N p t) (prodLaw N q t) ≤ Real.sqrt (prodLaw N p t * prodLaw N q t) := by
    intro t
    have ha := prodLaw_nonneg N p hp t
    have hb := prodLaw_nonneg N q hq t
    have hmin : 0 ≤ min (prodLaw N p t) (prodLaw N q t) := le_min ha hb
    have hsq : (min (prodLaw N p t) (prodLaw N q t)) ^ 2
        ≤ prodLaw N p t * prodLaw N q t := by
      have h1 : min (prodLaw N p t) (prodLaw N q t) ≤ prodLaw N p t := min_le_left _ _
      have h2 : min (prodLaw N p t) (prodLaw N q t) ≤ prodLaw N q t := min_le_right _ _
      nlinarith [hmin, h1, h2]
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hmin] at this
  have hsum : ∑ t : Fin N → Obs, min (prodLaw N p t) (prodLaw N q t)
      ≤ ∑ t : Fin N → Obs, Real.sqrt (prodLaw N p t * prodLaw N q t) :=
    Finset.sum_le_sum (fun t _ => hstep t)
  rw [affinity_prodLaw N p q hp hq] at hsum
  linarith

theorem errI_nonneg (N : ℕ) (p q : Obs → ℝ) (hp : ∀ o, 0 ≤ p o) : 0 ≤ errI N p q := by
  refine Finset.sum_nonneg (fun t _ => ?_)
  by_cases h : prodLaw N q t ≤ prodLaw N p t
  · rw [if_pos h]
  · rw [if_neg h]; exact prodLaw_nonneg N p hp t

theorem errII_nonneg (N : ℕ) (p q : Obs → ℝ) (hq : ∀ o, 0 ≤ q o) : 0 ≤ errII N p q := by
  refine Finset.sum_nonneg (fun t _ => ?_)
  by_cases h : prodLaw N q t ≤ prodLaw N p t
  · rw [if_pos h]; exact prodLaw_nonneg N q hq t
  · rw [if_neg h]

/-! ## The sample-size bound -/

/-- **The per-pair test bound, derived from the model.**

Given a separation `c` in squared Hellinger per observation, the likelihood-ratio test on
`N >= log(K/delta)/c` observations errs with probability at most `delta / K`.  This is
exactly the statement `bounds_same_order` previously took as the hypothesis `hbd`. -/
theorem lrt_error_le (N : ℕ) (p q : Obs → ℝ) (hp : ∀ o, 0 ≤ p o) (hq : ∀ o, 0 ≤ q o)
    (c δ K : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hK : 0 < K)
    (hsep : c ≤ hsq p q) (hH1 : hsq p q ≤ 1)
    (hN : Real.log (K / δ) / c ≤ (N : ℝ)) :
    errI N p q + errII N p q ≤ δ / K := by
  have haff : affinity p q = 1 - hsq p q := by unfold hsq; ring
  have haff0 : 0 ≤ affinity p q := affinity_nonneg p q
  -- 1 - x <= exp (-x)
  have hexp1 : affinity p q ≤ Real.exp (-(hsq p q)) := by
    have := Real.add_one_le_exp (-(hsq p q))
    rw [haff]; linarith
  have hpow : (affinity p q) ^ N ≤ (Real.exp (-(hsq p q))) ^ N :=
    pow_le_pow_left₀ haff0 hexp1 N
  have hrew : (Real.exp (-(hsq p q))) ^ N = Real.exp (-((N : ℝ) * hsq p q)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hNc : Real.log (K / δ) ≤ (N : ℝ) * c := by
    rw [div_le_iff₀ hc] at hN; linarith
  have hmono : (N : ℝ) * c ≤ (N : ℝ) * hsq p q :=
    mul_le_mul_of_nonneg_left hsep (Nat.cast_nonneg N)
  have hfinal : Real.exp (-((N : ℝ) * hsq p q)) ≤ δ / K := by
    have hlog : Real.log (K / δ) ≤ (N : ℝ) * hsq p q := le_trans hNc hmono
    have h1 : Real.exp (-((N : ℝ) * hsq p q)) ≤ Real.exp (-(Real.log (K / δ))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(Real.log (K / δ))) = δ / K := by
      rw [← Real.log_inv, Real.exp_log (by positivity)]
      rw [inv_div]
    linarith
  have hchain := err_le_affinity_pow N p q hp hq
  rw [hrew] at hpow
  have hA : (affinity p q) ^ N ≤ δ / K := le_trans hpow hfinal
  -- `err_le_affinity_pow` bounds the AVERAGE by `affinity^N / 2`, so the SUM is bounded by
  -- `affinity^N` itself.  The budget already carried that factor of two, so nothing is lost
  -- by reporting the sum -- and the sum is what bounds each world's own error.
  linarith

/-- **The exponent, named.**  With per-observation separation `c0 * h^(2r)` the sample
size is `log(K/delta) / c0 * h^(-2r)`: the SAME exponent in `h` that the lower bound
produces, so the two sides of Paper B's claim match in order and differ only in the
constant. -/
theorem identify_sample_complexity (N : ℕ) (p q : Obs → ℝ)
    (hp : ∀ o, 0 ≤ p o) (hq : ∀ o, 0 ≤ q o)
    (h c0 δ K : ℝ) (r : ℕ) (hh : 0 < h) (hc0 : 0 < c0) (hδ : 0 < δ) (hK : 0 < K)
    (hsep : c0 * h ^ (2 * r) ≤ hsq p q) (hH1 : hsq p q ≤ 1)
    (hN : Real.log (K / δ) / c0 / h ^ (2 * r) ≤ (N : ℝ)) :
    errI N p q + errII N p q ≤ δ / K := by
  have hpos : (0 : ℝ) < h ^ (2 * r) := pow_pos hh _
  refine lrt_error_le N p q hp hq (c0 * h ^ (2 * r)) δ K (by positivity) hδ hK hsep hH1 ?_
  rw [div_le_iff₀ (by positivity)]
  rw [div_div, div_le_iff₀ (by positivity)] at hN
  linarith [hN]

/-! ## Non-vacuity -/

/-- The hypotheses are satisfiable, and not only at the degenerate extreme: this pair has
`0 < H^2 < 1`, so `lrt_error_le` is not vacuously true. -/
theorem separation_nonvacuous :
    ∃ p q : Bool → ℝ, (∀ o, 0 ≤ p o) ∧ (∀ o, 0 ≤ q o) ∧
      (∑ o, p o = 1) ∧ (∑ o, q o = 1) ∧ 0 < hsq p q ∧ hsq p q < 1 := by
  refine ⟨fun b => if b then 1 / 2 else 1 / 2, fun b => if b then 1 else 0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o; cases o <;> norm_num
  · intro o; cases o <;> norm_num
  · norm_num [Fintype.sum_bool]
  · norm_num [Fintype.sum_bool]
  · have haff : affinity (fun b : Bool => if b then (1 : ℝ) / 2 else 1 / 2)
        (fun b : Bool => if b then (1 : ℝ) else 0) = Real.sqrt (1 / 2) := by
      unfold affinity
      rw [Fintype.sum_bool]
      norm_num
    have hlt : Real.sqrt (1 / 2) < 1 := by
      have h1 : Real.sqrt (1 / 2) < Real.sqrt 1 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      simpa using h1
    unfold hsq; rw [haff]; linarith
  · have haff : affinity (fun b : Bool => if b then (1 : ℝ) / 2 else 1 / 2)
        (fun b : Bool => if b then (1 : ℝ) else 0) = Real.sqrt (1 / 2) := by
      unfold affinity
      rw [Fintype.sum_bool]
      norm_num
    have hpos : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
    unfold hsq; rw [haff]; linarith


/-! ## The decoder's total error, with nothing assumed

`bounds_same_order` took `hbd : forall i, err i <= delta / K`.  Here the `K` per-pair
errors are the errors of an exhibited test, each bounded by `lrt_error_le`, and the union
bound then gives the decoder's total.  No error level is assumed anywhere. -/

/-- Each world's own error, separately: the test errs under `p` with probability at most
`delta/K`, and under `q` likewise.  Summing the two and calling that "the error" would be
a statement about neither world, which is why both are stated. -/
theorem lrt_error_each (N : ℕ) (p q : Obs → ℝ) (hp : ∀ o, 0 ≤ p o) (hq : ∀ o, 0 ≤ q o)
    (c δ K : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hK : 0 < K)
    (hsep : c ≤ hsq p q) (hH1 : hsq p q ≤ 1)
    (hN : Real.log (K / δ) / c ≤ (N : ℝ)) :
    errI N p q ≤ δ / K ∧ errII N p q ≤ δ / K := by
  have hsum := lrt_error_le N p q hp hq c δ K hc hδ hK hsep hH1 hN
  exact ⟨by linarith [errII_nonneg N p q hq], by linarith [errI_nonneg N p q hp]⟩

/-- **The decoder's total error, derived.**  `K` pairs, each separated by at least `c` in
squared Hellinger per observation, each tested by its own likelihood-ratio test on
`N >= log(K/delta)/c` observations: the total error is at most `delta`. -/
theorem decoder_total_error (K N : ℕ) (hK : 0 < K)
    (pp qq : Fin K → Obs → ℝ)
    (hp : ∀ i o, 0 ≤ pp i o) (hq : ∀ i o, 0 ≤ qq i o)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hsep : ∀ i, c ≤ hsq (pp i) (qq i)) (hH1 : ∀ i, hsq (pp i) (qq i) ≤ 1)
    (hN : Real.log ((K : ℝ) / δ) / c ≤ (N : ℝ)) :
    (∑ i : Fin K, errI N (pp i) (qq i) ≤ δ)
      ∧ ∑ i : Fin K, errII N (pp i) (qq i) ≤ δ := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have heach : ∀ i : Fin K,
      errI N (pp i) (qq i) ≤ δ / (K : ℝ) ∧ errII N (pp i) (qq i) ≤ δ / (K : ℝ) :=
    fun i => lrt_error_each N (pp i) (qq i) (hp i) (hq i) c δ (K : ℝ) hc hδ hKR
      (hsep i) (hH1 i) hN
  have hconst : ∑ _i : Fin K, δ / (K : ℝ) = δ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  constructor
  · calc ∑ i : Fin K, errI N (pp i) (qq i)
        ≤ ∑ _i : Fin K, δ / (K : ℝ) := Finset.sum_le_sum (fun i _ => (heach i).1)
      _ = δ := hconst
  · calc ∑ i : Fin K, errII N (pp i) (qq i)
        ≤ ∑ _i : Fin K, δ / (K : ℝ) := Finset.sum_le_sum (fun i _ => (heach i).2)
      _ = δ := hconst

/-! ## Audit -/

#print axioms affinity_prodLaw
#print axioms prodLaw_sum
#print axioms err_eq_sum_min
#print axioms err_le_affinity_pow
#print axioms lrt_error_le
#print axioms identify_sample_complexity
#print axioms separation_nonvacuous
#print axioms errI_nonneg
#print axioms errII_nonneg
#print axioms lrt_error_each
#print axioms decoder_total_error

end CIGAMF.P13.PaperBTest
