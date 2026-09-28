import «LeanPaperBParityV1»

/-!
# Paper B: the missing normalisation in front of the cube difference

`parity_cf_difference` (`LeanPaperBParityV1`) was labelled "the channel's
characteristic-function difference, exactly".  It is not: it is the difference of two
UNNORMALISED sums over the `2^j` cube points, and it carries a leading `2^j` that a
characteristic function does not have.  Two links were missing, and each moves the constant:

1. the latent cube is UNIFORM, so every point carries probability `2^(-j)`;
2. the observation adds independent Gaussian noise, contributing `exp (-sigma^2 t^2 / 2)`.

This module supplies the first, which is where the spurious `2^j` was.  The second needs the
observation LAW itself -- a mixture of Gaussians over the cube -- and is not in this module;
no definition here stands in for it.  After normalising, the constant is
`2` -- NOT `2^(j+1)` -- because `2^(j+1) / 2^j = 2`.  `EXP_paperB_decoder.py` already
implements the normalised form in `closed_form_gap`, so no measured number changes; what
changes is that the Lean statement and the manuscript stop claiming a characteristic
function for an unnormalised sum.

The `h`-dependence was never in doubt and is untouched: it is the `j`-th power either way,
which is all `parity_gap_order` and the decoder's order claim use.
-/

namespace CIGAMF.P13.PaperBParityNorm

open CIGAMF.P13.PaperBCube CIGAMF.P13.PaperBParity

/-- **The normalisation, and the constant it fixes.**  Averaging over the uniform cube --
dividing by `2^j` -- turns the leading `2^(j+1)` into a single `2`. -/
theorem parity_cf_difference_normalised (j : ℕ) (t hh : ℝ) :
    ((2 : ℂ) ^ j)⁻¹ *
        ((∑ z : Fin j → Bool,
            Complex.exp ((Complex.I * t) * chr z + (Complex.I * t * hh / j) * csum z))
          - ∑ z : Fin j → Bool,
            Complex.exp ((-(Complex.I * t)) * chr z + (Complex.I * t * hh / j) * csum z))
      = 2 * Complex.sinh (Complex.I * t)
          * Complex.sinh (Complex.I * t * hh / j) ^ j := by
  have h2 : ((2 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [parity_cf_difference j t hh]
  field_simp

/-- **The constant is `2`, stated as the bare arithmetic fact** that the audit turned on:
`2^(j+1) / 2^j = 2`, so an unnormalised reading overstates the difference by `2^j`. -/
theorem normalisation_factor (j : ℕ) :
    ((2 : ℂ) ^ j)⁻¹ * (2 ^ j * (2 : ℂ)) = 2 := by
  have h2 : ((2 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-! ## Audit -/

#print axioms parity_cf_difference_normalised
#print axioms normalisation_factor

end CIGAMF.P13.PaperBParityNorm
