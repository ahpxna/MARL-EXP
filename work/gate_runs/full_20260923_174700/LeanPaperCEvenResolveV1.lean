import «LeanPaperCUniformV1»

/-!
# Paper C: the even breakpoint and the `eta = 0` mixture do not conflict

`LeanPaperCUniformV1` proves that the mixture of the `m-1` insertion rankings WITH the flat
ranking, symmetrised by the sign flip, has every per-item marginal exactly `k/m` -- band
`eta = 0`.  When that was found, a note was added to `THEOREM_MAP.md` saying it might
contradict the even breakpoint `eta_* = (m-2)/(2(m-1))` of `breakpoint_lower_even`, which
says a law attaining the free value needs band at least that.

**That note was wrong, and this module retracts it by computing both values.**

`breakpoint_lower_even` assumes `hfree : sum_x P x (r_1 + r_{m-1}) = 4/(D(m-1))`, the value
the insertion mixture ALONE attains (`insMixtureEven_free_value` gives `2/(D(m-1))` per
budget).  The flat-augmented mixture attains `4/(mD)` per budget
(`evenMixture_value_at_D`), and

    2/(D(m-1))  <  4/(mD)        for every m > 2,

so the band-`0` mixture does NOT satisfy `hfree`.  There is no law here with band `0` and
the free value, and `breakpoint_lower_even` is untouched.

What the two results say together is the intended picture, now with both halves proved:
the insertion mixture buys the smaller objective and pays band `(m-2)/(2(m-1))`; adding the
flat ranking buys band `0` and pays the larger objective `4/(m(m+4))` -- which is exactly
the value C-H1 claims at uniform marginals.
-/

namespace CIGAMF.P13.PaperCEvenResolve

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCEven
open CIGAMF.P13.PaperCMix

/-- **The sign flip costs nothing on the objective.**  The flip-symmetrised mixture of the
`m-1` insertion rankings and the flat one has the same per-budget value as the unflipped
one, because `excess` depends on the weights only through `|S_k|`. -/
theorem evenMixtureFlipped_value_at_D (m : ℕ) (hm : 1 < m) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ m - 1) :
    (∑ a ∈ Finset.range (m - 1),
        ((1 / (2 * (m : ℝ))) * (excess (insRanking m a) k / ((m : ℝ) + 4))
          + (1 / (2 * (m : ℝ)))
            * (excess (fun i => -(insRanking m a i)) k / ((m : ℝ) + 4))))
        + ((1 / (2 * (m : ℝ))) * (excess (flatEven m) k / ((m : ℝ) + 4))
          + (1 / (2 * (m : ℝ)))
            * (excess (fun i => -(flatEven m i)) k / ((m : ℝ) + 4)))
      = 4 / ((m : ℝ) * ((m : ℝ) + 4)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hterm : ∀ a ∈ Finset.range (m - 1),
      ((1 / (2 * (m : ℝ))) * (excess (insRanking m a) k / ((m : ℝ) + 4))
        + (1 / (2 * (m : ℝ)))
          * (excess (fun i => -(insRanking m a i)) k / ((m : ℝ) + 4)))
      = (1 / (m : ℝ)) * (excess (insRanking m a) k / ((m : ℝ) + 4)) := by
    intro a _
    rw [excess_neg m (insRanking m a) k]
    field_simp
    ring
  have hflat : ((1 / (2 * (m : ℝ))) * (excess (flatEven m) k / ((m : ℝ) + 4))
      + (1 / (2 * (m : ℝ))) * (excess (fun i => -(flatEven m i)) k / ((m : ℝ) + 4)))
      = (1 / (m : ℝ)) * (excess (flatEven m) k / ((m : ℝ) + 4)) := by
    rw [excess_neg m (flatEven m) k]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, hflat]
  exact evenMixture_value_at_D m hm k hk1 hk

/-- **The two even values are different, and in the direction that resolves the note.**  The
insertion mixture's free value is strictly below the flat-augmented mixture's, at every
`m > 2`. -/
theorem free_value_lt_uniform_value (m D : ℝ) (hm : 2 < m) (hD : 0 < D) :
    2 / (D * (m - 1)) < 4 / (m * D) := by
  have hm1 : (0 : ℝ) < m - 1 := by linarith
  have hmpos : (0 : ℝ) < m := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **So the band-`0` mixture does not satisfy `hfree`.**  `breakpoint_lower_even` asks for
`r_1 + r_{m-1} = 4/(D(m-1))`; the flat-augmented mixture gives `8/(mD)`, and the two are
unequal at every `m > 2`.  The even breakpoint is therefore not contradicted by the `eta = 0`
construction, and the note claiming it might be is withdrawn. -/
theorem band_zero_does_not_attain_free_value (m D : ℝ) (hm : 2 < m) (hD : 0 < D) :
    4 / (D * (m - 1)) ≠ 2 * (4 / (m * D)) := by
  have h := free_value_lt_uniform_value m D hm hD
  have hlt : 4 / (D * (m - 1)) < 2 * (4 / (m * D)) := by
    have hdouble : 4 / (D * (m - 1)) = 2 * (2 / (D * (m - 1))) := by ring
    rw [hdouble]
    linarith
  exact ne_of_lt hlt

/-- **The picture, in one statement.**  At every even size the two constructions sit on
opposite sides of the trade-off: the insertion mixture has the smaller objective and needs
the positive band; the flat-augmented mixture has band `0` and the larger objective, which is
the value C-H1 reports at uniform marginals. -/
theorem even_tradeoff (m : ℕ) (hm : 2 < m) :
    2 / (((m : ℝ) + 4) * ((m : ℝ) - 1)) < 4 / ((m : ℝ) * ((m : ℝ) + 4)) := by
  have hmR : (2 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact free_value_lt_uniform_value (m : ℝ) ((m : ℝ) + 4) hmR (by linarith)

/-! ## Audit -/

#print axioms evenMixtureFlipped_value_at_D
#print axioms free_value_lt_uniform_value
#print axioms band_zero_does_not_attain_free_value
#print axioms even_tradeoff

end CIGAMF.P13.PaperCEvenResolve
