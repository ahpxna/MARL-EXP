import «LeanPaperBWorldsV1»

/-!
# Paper B: the decoder's own density pair, and the difference it satisfies

`LeanPaperBWorldsV1.worlds_diff` proves an identity for the pair `(worldP, worldQ)`: their
difference is the iterated symmetric difference of the base `M`.  That pair was built to
repair the vacuous `hdiff`, and it does so, but it is NOT the pair the decoder reads.  The
decoder's observation is

    Y = v * prod_l Z_l + sum_l b_l Z_l + xi,        v in {-1, +1},

so the two densities it separates are, over the sign cube,

    p_v(y) = 2^{-r} sum_z  phi(y - v * parity z - shift b z),

and their difference is NOT `iterDiff phi b` -- the hidden bit `v` multiplies the PARITY, not
the base.  Writing it out, splitting the cube by parity and collecting,

    p_+ - p_-  =  2^{-r} sum_z  parity z * G(y - shift b z)  =  iterDiff G (b),
    G(u) = phi(u - 1) - phi(u + 1),

so the base on the right is a DIFFERENCE OF TWO TRANSLATES of the kernel, not the kernel.
`channel_pair_diff` is that identity.  It is the missing link between the constructed pair
and the experiment's channel, and it says exactly which envelope argument the rate bound
needs: one applied to `G`, i.e. to each of the two components separately and then added.

WHAT IS AND IS NOT HERE.  The identity is proved.  Applying `hellinger_rate_bound` to `G`
is NOT done here: `G` is a difference, so the envelope has to be taken componentwise and
the two bounds added, and the normalisation of `gkern` -- which is the UNNORMALISED Gaussian
-- to a probability density has to be carried through.  Both are named rather than assumed.
-/

namespace CIGAMF.P13.PaperBChannelPair

open Finset
open CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBWorlds

variable {r : ℕ}

/-- The channel's density at hidden bit `v`, as a mixture over the sign cube: the parity is
displaced by `v` and the coordinates by `b`. -/
noncomputable def chanDens (φ : ℝ → ℝ) (b : Fin r → ℝ) (v : ℝ) (y : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ r * ∑ z : Fin r → Bool, φ (y - v * parity z - shiftOf b z)

/-- The base the difference actually sees: a difference of two translates of the kernel. -/
noncomputable def pairBase (φ : ℝ → ℝ) (u : ℝ) : ℝ := φ (u - 1) - φ (u + 1)

/-- Each sign pattern's contribution, with the parity pulled out.  `parity z` is `+-1`, so
displacing by `+parity z` and by `-parity z` exchanges the two translates and flips the
sign of their difference. -/
theorem chan_term (φ : ℝ → ℝ) (b : Fin r → ℝ) (y : ℝ) (z : Fin r → Bool) :
    φ (y - 1 * parity z - shiftOf b z) - φ (y - (-1) * parity z - shiftOf b z)
      = parity z * pairBase φ (y - shiftOf b z) := by
  have habs : |parity z| = 1 := parity_abs z
  rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp habs with hp | hp
  · rw [hp]
    unfold pairBase
    rw [show y - 1 * (1 : ℝ) - shiftOf b z = y - shiftOf b z - 1 from by ring,
      show y - (-1) * (1 : ℝ) - shiftOf b z = y - shiftOf b z + 1 from by ring]
    ring
  · rw [hp]
    unfold pairBase
    rw [show y - 1 * (-1 : ℝ) - shiftOf b z = y - shiftOf b z + 1 from by ring,
      show y - (-1) * (-1 : ℝ) - shiftOf b z = y - shiftOf b z - 1 from by ring]
    ring

/-- **The decoder's pair, and its difference.**  The two hidden-bit densities differ by the
iterated symmetric difference of `pairBase`, NOT of the kernel.  This is the identity the
rate bound has to be applied to. -/
theorem channel_pair_diff (φ : ℝ → ℝ) (b : Fin r → ℝ) (y : ℝ) :
    chanDens φ b 1 y - chanDens φ b (-1) y
      = iterDiff (pairBase φ) (List.ofFn b) y := by
  unfold chanDens
  rw [iterDiff_eq_signSum r (pairBase φ) b y, ← mul_sub, ← Finset.sum_sub_distrib]
  refine congrArg _ (Finset.sum_congr rfl (fun z _ => ?_))
  have h := chan_term φ b y z
  unfold parity shiftOf at h ⊢
  linarith [h]

/-- **The two densities are nonnegative** when the kernel is, so the pair is a pair of
mixtures and not a formal difference. -/
theorem chanDens_nonneg (φ : ℝ → ℝ) (hφ : ∀ u, 0 ≤ φ u) (b : Fin r → ℝ) (v y : ℝ) :
    0 ≤ chanDens φ b v y := by
  unfold chanDens
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun z _ => hφ _))

/-- **The base is odd about the origin when the kernel is even**, which is why the two
components have to be bounded separately: `pairBase` is not a density and has no envelope of
its own. -/
theorem pairBase_odd (φ : ℝ → ℝ) (hev : ∀ u, φ (-u) = φ u) (u : ℝ) :
    pairBase φ (-u) = -pairBase φ u := by
  unfold pairBase
  rw [show (-u) - 1 = -(u + 1) from by ring, show (-u) + 1 = -(u - 1) from by ring,
    hev (u + 1), hev (u - 1)]
  ring

/-- **The componentwise split the envelope argument needs.**  The iterated difference of the
base is the difference of the iterated differences of the two translates, so a bound on each
translate's iterated difference gives a bound on the pair's by the triangle inequality. -/
theorem pair_iterDiff_split (φ : ℝ → ℝ) (b : Fin r → ℝ) (y : ℝ) :
    iterDiff (pairBase φ) (List.ofFn b) y
      = iterDiff (fun u => φ (u - 1)) (List.ofFn b) y
        - iterDiff (fun u => φ (u + 1)) (List.ofFn b) y := by
  rw [iterDiff_eq_signSum r (pairBase φ) b y,
    iterDiff_eq_signSum r (fun u => φ (u - 1)) b y,
    iterDiff_eq_signSum r (fun u => φ (u + 1)) b y, ← mul_sub, ← Finset.sum_sub_distrib]
  refine congrArg _ (Finset.sum_congr rfl (fun z _ => ?_))
  unfold pairBase
  ring

/-! ## Audit -/

#print axioms chan_term
#print axioms channel_pair_diff
#print axioms chanDens_nonneg
#print axioms pairBase_odd
#print axioms pair_iterDiff_split

end CIGAMF.P13.PaperBChannelPair
