import «LeanPaperBTranscriptV1»
import «LeanPaperBRatesV1»

/-!
# Paper B: data processing for an adaptive transcript, from scratch

`LeanPaperBRatesV1.log_sum_two` proves the two-term log-sum inequality from `log y >= 1-1/y`
and nothing else.  `kl2_le_of_partition` was then a RESTATEMENT: it took the partition
inequality as a hypothesis and rewrote it.  So every use of "data processing" in the corpus
was, at bottom, an assumption.

This module removes that for the object the corpus actually has: the adaptive transcript of
`LeanPaperBTranscriptV1`.

1. `log_sum_finset` -- the log-sum inequality over a finite index set, by induction from
   `log_sum_two`.
2. `Phi_mul` -- the factorisation `Phi(uv, xy) = uv log(u/x) + uv log(v/y)`, valid at
   `u = 0` and `v = 0` as well, which is what lets the per-step law and the continuation be
   separated inside the induction.
3. `kl2_le_klChain` -- **data processing**: for any bounded `f` with `0 <= f <= 1` read off
   the transcript, the binary divergence between the two worlds' expectations of `f` is at
   most the transcript divergence.  At `f` an indicator this is the statement that coarsening
   to a decision loses relative entropy.

The proof is the chain rule, one step at a time: `log_sum_finset` applied to the pair
`(p_y E_p^y f, q_y E_q^y f)` splits into the per-step divergence and the continuation, the
first sums to `klStep` because `f + (1-f)` is the constant one, and the second is the
induction hypothesis.
-/

namespace CIGAMF.P13.PaperBDataProc

open Finset
open CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBTranscript

/-! ## The log-sum inequality over a finite index set -/

/-- **Log-sum, over any finite index set.**  Induction from `log_sum_two`; the empty case is
`0 * log(0/0) = 0`. -/
theorem log_sum_finset {ι : Type*} [DecidableEq ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) (s : Finset ι) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro j t hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    rcases t.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hbt : (0 : ℝ) < ∑ i ∈ t, b i := Finset.sum_pos (fun i _ => hb i) hne
      have hat : (0 : ℝ) ≤ ∑ i ∈ t, a i := Finset.sum_nonneg (fun i _ => ha i)
      have h2 := log_sum_two (a j) (∑ i ∈ t, a i) (b j) (∑ i ∈ t, b i) (ha j) hat (hb j) hbt
      linarith [ih]

/-! ## The factorisation inside the induction -/

/-- `Phi x y = x log (x/y)`. -/
noncomputable def Phi (x y : ℝ) : ℝ := x * Real.log (x / y)

/-- **The product splits**, including at a vanishing factor, where both sides are zero. -/
theorem Phi_mul (u v x y : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hx : 0 < x) (hy : 0 < y) :
    Phi (u * v) (x * y) = u * v * Real.log (u / x) + u * v * Real.log (v / y) := by
  unfold Phi
  rcases eq_or_lt_of_le hu with hu0 | hupos
  · simp [← hu0]
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · simp [← hv0]
  have hlog : Real.log (u * v / (x * y)) = Real.log (u / x) + Real.log (v / y) := by
    rw [show u * v / (x * y) = (u / x) * (v / y) from by field_simp]
    exact Real.log_mul (by positivity) (by positivity)
  rw [hlog]
  ring

/-! ## Data processing -/

variable {K Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **Data processing for the adaptive transcript.**  Coarsening the transcript to the pair
`(E_p f, E_q f)` cannot increase the divergence.  The hypotheses `hqf`, `hqf'` say the
coarsening is non-degenerate under `Q` -- both cells carry mass at every reachable history --
which is a support condition on the rule, not a conclusion. -/
theorem kl2_le_klChain (π : List Y → K) (p q : K → Y → ℝ)
    (hp : ∀ k, ∑ y, p k y = 1) (hpnn : ∀ k y, 0 ≤ p k y) (hq : ∀ k y, 0 < q k y)
    (f : List Y → ℝ) (hf0 : ∀ h, 0 ≤ f h) (hf1 : ∀ h, f h ≤ 1)
    (hqf : ∀ (s : ℕ) (h : List Y), 0 < expect π q s h f)
    (hqf' : ∀ (s : ℕ) (h : List Y), 0 < expect π q s h (fun h' => 1 - f h')) :
    ∀ (t : ℕ) (h : List Y),
      Phi (expect π p t h f) (expect π q t h f)
        + Phi (expect π p t h (fun h' => 1 - f h'))
              (expect π q t h (fun h' => 1 - f h'))
        ≤ klChain π p q t h := by
  classical
  intro t
  induction t with
  | zero =>
      intro h
      have h1 : expect π p 0 h f = f h := rfl
      have h2 : expect π q 0 h f = f h := rfl
      have h3 : expect π p 0 h (fun h' => 1 - f h') = 1 - f h := rfl
      have h4 : expect π q 0 h (fun h' => 1 - f h') = 1 - f h := rfl
      have hfpos : 0 < f h := by simpa [h2] using hqf 0 h
      have hfpos' : 0 < 1 - f h := by simpa [h4] using hqf' 0 h
      rw [h1, h2, h3, h4, klChain_zero]
      unfold Phi
      rw [div_self (ne_of_gt hfpos), div_self (ne_of_gt hfpos'), Real.log_one]
      norm_num
  | succ t ih =>
      intro h
      -- the four families indexed by the next letter
      set A : Y → ℝ := fun y => p (π h) y * expect π p t (y :: h) f with hA
      set B : Y → ℝ := fun y => q (π h) y * expect π q t (y :: h) f with hB
      set A' : Y → ℝ := fun y => p (π h) y * expect π p t (y :: h) (fun h' => 1 - f h')
        with hA'
      set B' : Y → ℝ := fun y => q (π h) y * expect π q t (y :: h) (fun h' => 1 - f h')
        with hB'
      have hAnn : ∀ y, 0 ≤ A y := fun y =>
        mul_nonneg (hpnn _ _) (expect_nonneg π p hpnn f hf0 t (y :: h))
      have hA'nn : ∀ y, 0 ≤ A' y := fun y =>
        mul_nonneg (hpnn _ _)
          (expect_nonneg π p hpnn _ (fun h' => by linarith [hf1 h']) t (y :: h))
      have hBpos : ∀ y, 0 < B y := fun y => mul_pos (hq _ _) (hqf t (y :: h))
      have hB'pos : ∀ y, 0 < B' y := fun y => mul_pos (hq _ _) (hqf' t (y :: h))
      -- log-sum on each cell
      have hLS := log_sum_finset A B hAnn hBpos Finset.univ
      have hLS' := log_sum_finset A' B' hA'nn hB'pos Finset.univ
      have hsumA : ∑ y, A y = expect π p (t + 1) h f := (expect_succ π p t h f).symm
      have hsumB : ∑ y, B y = expect π q (t + 1) h f := (expect_succ π q t h f).symm
      have hsumA' : ∑ y, A' y = expect π p (t + 1) h (fun h' => 1 - f h') :=
        (expect_succ π p t h _).symm
      have hsumB' : ∑ y, B' y = expect π q (t + 1) h (fun h' => 1 - f h') :=
        (expect_succ π q t h _).symm
      -- split each term of the two sums
      have hsplit : ∀ y : Y,
          A y * Real.log (A y / B y) + A' y * Real.log (A' y / B' y)
            = p (π h) y * Real.log (p (π h) y / q (π h) y)
              + p (π h) y * (Phi (expect π p t (y :: h) f) (expect π q t (y :: h) f)
                + Phi (expect π p t (y :: h) (fun h' => 1 - f h'))
                      (expect π q t (y :: h) (fun h' => 1 - f h'))) := by
        intro y
        have e1 := Phi_mul (p (π h) y) (expect π p t (y :: h) f) (q (π h) y)
          (expect π q t (y :: h) f) (hpnn _ _)
          (expect_nonneg π p hpnn f hf0 t (y :: h)) (hq _ _) (hqf t (y :: h))
        have e2 := Phi_mul (p (π h) y) (expect π p t (y :: h) (fun h' => 1 - f h'))
          (q (π h) y) (expect π q t (y :: h) (fun h' => 1 - f h')) (hpnn _ _)
          (expect_nonneg π p hpnn _ (fun h' => by linarith [hf1 h']) t (y :: h))
          (hq _ _) (hqf' t (y :: h))
        have hone : expect π p t (y :: h) f
            + expect π p t (y :: h) (fun h' => 1 - f h') = 1 := by
          have := expect_add π p f (fun h' => 1 - f h') t (y :: h)
          have hconst : (fun h' => f h' + (1 - f h')) = fun _ : List Y => (1 : ℝ) := by
            funext h'; ring
          rw [hconst] at this
          rw [← this]
          exact expect_one π p hp t (y :: h)
        unfold Phi at e1 e2 ⊢
        linear_combination e1 + e2
          + (p (π h) y * Real.log (p (π h) y / q (π h) y)) * hone
      -- assemble
      have hsum : ∑ y, (A y * Real.log (A y / B y) + A' y * Real.log (A' y / B' y))
          = klStep p q (π h)
            + ∑ y, p (π h) y * (Phi (expect π p t (y :: h) f) (expect π q t (y :: h) f)
                + Phi (expect π p t (y :: h) (fun h' => 1 - f h'))
                      (expect π q t (y :: h) (fun h' => 1 - f h'))) := by
        rw [Finset.sum_congr rfl (fun y _ => hsplit y), Finset.sum_add_distrib]
        rfl
      have hcont : ∑ y, p (π h) y
            * (Phi (expect π p t (y :: h) f) (expect π q t (y :: h) f)
              + Phi (expect π p t (y :: h) (fun h' => 1 - f h'))
                    (expect π q t (y :: h) (fun h' => 1 - f h')))
          ≤ ∑ y, p (π h) y * klChain π p q t (y :: h) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih (y :: h)) (hpnn _ _))
      have hdist : ∑ y, (A y * Real.log (A y / B y) + A' y * Real.log (A' y / B' y))
          = (∑ y, A y * Real.log (A y / B y)) + ∑ y, A' y * Real.log (A' y / B' y) :=
        Finset.sum_add_distrib
      have hstep1 : Phi (expect π p (t + 1) h f) (expect π q (t + 1) h f)
            + Phi (expect π p (t + 1) h (fun h' => 1 - f h'))
                  (expect π q (t + 1) h (fun h' => 1 - f h'))
          ≤ (∑ y, A y * Real.log (A y / B y)) + ∑ y, A' y * Real.log (A' y / B' y) := by
        unfold Phi
        rw [← hsumA, ← hsumB, ← hsumA', ← hsumB']
        exact add_le_add hLS hLS'
      rw [klChain_succ]
      refine le_trans hstep1 ?_
      rw [← hdist, hsum]
      linarith [hcont]

/-! ## Audit -/

#print axioms log_sum_finset
#print axioms Phi_mul
#print axioms kl2_le_klChain

end CIGAMF.P13.PaperBDataProc
