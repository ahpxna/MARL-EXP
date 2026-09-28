import «LeanPaperBObstructionParityV1»

/-!
# Paper B: the latent family `F_{u,v}` as a channel, and its adaptive lower rates

The latent family of Paper B is
`F_{u,v}(z) = 3u z_1 - 2 z_2 - 2 z_3 + v z_4 ... z_{r+3}` on the sign cube, observed through a
bounded linear probe `g(z) = a . z` as `Y = F_{u,v}(Z) + h g(Z) + xi`, with `Z` uniform and LATENT
and `xi ~ N(0, sigma^2)`.  Up to now only a per-step bound for a constructed pair was proved,
and the family's own channel was never assembled.  This module assembles it and closes the
adaptive lower bound on the Gaussian model itself.

* `famDens`: the observation density of a probe `(aH, aT)` (head and tail coefficients) in world
  `(u, v)`.  It is the exact Gaussian mixture over the `8 * 2^r` latent sign patterns.
* `famChan`: the family as a `Channel` over worlds `Bool × Bool` and queries `Fin (k+1)`.  Query
  `0` is the dummy (pure noise), and queries `1..k` are ANY finite family of linear probes with
  `sum |aH| + sum |aT| <= 1`.  Density, positivity and unit mass are proved.
* `famDens_vdiff`: the two nuisance worlds `v = +-1` differ by EXACTLY
  `Zc^-1 * iterDiff (pairBase M_head) (h aT)`, the `r`-fold difference of a mixture over the eight
  head patterns.  This is the identification of the latent family with the iterated-difference
  structure, which was the missing modelling step.
* `famDens_udiff`: flipping `z_1` turns the two decision worlds `u = +-1` into a FIRST difference
  of step `h aH_1` of two non-negative mixtures.
* `famChi_v_le`, `famChi_u_le`: per-query chi-squares `<= Cv h^{2r}` and `<= Cu h^2`, with
  constants that mention no probe.
* `family_safe_lower`, `family_id_lower`: through the general obstruction law, every
  finite-horizon randomised adaptive policy on this Gaussian channel that answers safely (resp.
  identifies) with probability `1 - delta` pays `E[#queries] * Cu h^2 >= (1-delta) log(1/delta)
  - log 2`, resp. `E[#queries] * Cv h^{2r} >= ...`.  So the safe decision needs
  `Omega(log(1/delta)/h^2)` and identification `Omega(log(1/delta)/h^{2r})` queries.

The safe correspondence is the family's: at `u = -1` only answer `0` (the singleton `{1}`) is
safe, at `u = +1` every other answer is.  These safe sets are the ones computed from the losses
in `EXP_paperB_construction`; here they are the stated correspondence.
-/

namespace CIGAMF.P13.PaperBFamilyChannel

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBWorlds CIGAMF.P13.PaperBChannelPair
open CIGAMF.P13.PaperBPairRate CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBProtocol
open CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBObstructionParity

/-! ## 0. Translating differences, and reindexing mixtures -/

theorem iterDiff_translate : ∀ (bs : List ℝ) (f : ℝ → ℝ) (x c : ℝ),
    iterDiff f bs (x - c) = iterDiff (fun z => f (z - c)) bs x := by
  intro bs
  induction bs with
  | nil => intro f x c; rfl
  | cons b bs ih =>
      intro f x c
      show symDiff (iterDiff f bs) b (x - c) = symDiff (iterDiff (fun z => f (z - c)) bs) b x
      unfold symDiff
      rw [← ih f (x - b) c, ← ih f (x + b) c]
      have e1 : x - c - b = x - b - c := by ring
      have e2 : x - c + b = x + b - c := by ring
      rw [e1, e2]

theorem sum_eq_mixDens {ι : Type*} [Fintype ι] (σ : ℝ) (w cs : ι → ℝ) (y : ℝ) :
    ∑ i, w i * gkern σ (y - cs i)
      = mixDens σ (Fintype.card ι) (fun k => w ((Fintype.equivFin ι).symm k))
          (fun k => cs ((Fintype.equivFin ι).symm k)) y := by
  unfold mixDens
  exact Fintype.sum_equiv (Fintype.equivFin ι) _ _ (fun i => by simp)

theorem sum_reindex {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    ∑ k, w ((Fintype.equivFin ι).symm k) = ∑ i, w i :=
  Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun k => rfl)

theorem pair_envelope_fin {ι : Type*} [Fintype ι] {r : ℕ} (σ R h₀ : ℝ) (hσ : 0 < σ)
    (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀) (w cs : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i ≤ 1)
    (hcs : ∀ i, |cs i| ≤ R) (b : Fin r → ℝ) (hb : ∑ i, |b i| ≤ h₀) (y : ℝ) :
    |iterDiff (pairBase (fun x => ∑ i, w i * gkern σ (x - cs i))) (List.ofFn b) y|
      ≤ 2 * ((∏ i, |b i|) * envUp σ (R + 1 + h₀) r y) := by
  have hfun : (fun x => ∑ i, w i * gkern σ (x - cs i))
      = mixDens σ (Fintype.card ι) (fun k => w ((Fintype.equivFin ι).symm k))
          (fun k => cs ((Fintype.equivFin ι).symm k)) := funext (sum_eq_mixDens σ w cs)
  rw [hfun]
  exact pair_envelope σ R h₀ hσ hR hh₀ r _ _ (fun k => hw _) (by rw [sum_reindex]; exact hw1) _
    (fun k => hcs _) b hb y

theorem mixture_envelope_fin {ι : Type*} [Fintype ι] {r : ℕ} (σ R h₀ : ℝ) (hσ : 0 < σ)
    (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀) (w cs : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i ≤ 1)
    (hcs : ∀ i, |cs i| ≤ R) (b : Fin r → ℝ) (hb : ∑ i, |b i| ≤ h₀) (y : ℝ) :
    |iterDiff (fun x => ∑ i, w i * gkern σ (x - cs i)) (List.ofFn b) y|
      ≤ (∏ i, |b i|) * envUp σ (R + h₀) r y := by
  have hfun : (fun x => ∑ i, w i * gkern σ (x - cs i))
      = fun z => ∑ k, (fun k => w ((Fintype.equivFin ι).symm k)) k
          * gkern σ (z - (fun k => cs ((Fintype.equivFin ι).symm k)) k) :=
    funext (sum_eq_mixDens σ w cs)
  rw [hfun]
  exact iterDiff_mixture_envelope σ R h₀ hσ hR hh₀ r _ _ (fun k => hw _)
    (by rw [sum_reindex]; exact hw1) _ (fun k => hcs _) b hb y

/-! ## 1. The family's density -/

/-- The head part of the mean: `3u z_1 - 2 z_2 - 2 z_3 + h aH . z_head`. -/
noncomputable def headC (u h : ℝ) (aH : Fin 3 → ℝ) (zh : Fin 3 → Bool) : ℝ :=
  3 * u * sgnB (zh 0) - 2 * sgnB (zh 1) - 2 * sgnB (zh 2) + h * ∑ i, aH i * sgnB (zh i)

/-- The tail steps `h aT`. -/
noncomputable def tailB {r : ℕ} (h : ℝ) (aT : Fin r → ℝ) : Fin r → ℝ := fun i => h * aT i

/-- **The observation density of probe `(aH, aT)` in world `(u, v)`.** -/
noncomputable def famDens {r : ℕ} (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) (y : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ 3 * ∑ zh : Fin 3 → Bool, (2 : ℝ)⁻¹ ^ r * ∑ t : Fin r → Bool,
    gaussianPDFReal (headC u h aH zh + v * parity t + shiftOf (tailB h aT) t) (var2 σ) y

/-- The density in channel coordinates. -/
theorem famDens_eq {r : ℕ} (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) (y : ℝ) :
    famDens σ h u v aH aT y
      = (2 : ℝ)⁻¹ ^ 3 * ∑ zh : Fin 3 → Bool,
          (Zc σ)⁻¹ * chanDens (gkern σ) (tailB h aT) v (y - headC u h aH zh) := by
  unfold famDens chanDens
  refine congrArg _ (Finset.sum_congr rfl fun zh _ => ?_)
  have hterm : ∀ t : Fin r → Bool,
      gaussianPDFReal (headC u h aH zh + v * parity t + shiftOf (tailB h aT) t) (var2 σ) y
        = (Zc σ)⁻¹ * gkern σ (y - headC u h aH zh - v * parity t - shiftOf (tailB h aT) t) := by
    intro t
    rw [gaussianPDFReal_eq]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.mul_sum]
  ring

/-- **The nuisance pair is an iterated difference.**  The two worlds `v = +-1` differ by
exactly the `r`-fold difference, at steps `h aT`, of `pairBase` of the mixture over the eight
head patterns. -/
theorem famDens_vdiff {r : ℕ} (σ h u : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) (y : ℝ) :
    famDens σ h u 1 aH aT y - famDens σ h u (-1) aH aT y
      = (Zc σ)⁻¹ * iterDiff (pairBase (fun x => ∑ zh : Fin 3 → Bool,
          (2 : ℝ)⁻¹ ^ 3 * gkern σ (x - headC u h aH zh))) (List.ofFn (tailB h aT)) y := by
  rw [famDens_eq, famDens_eq, ← mul_sub, ← Finset.sum_sub_distrib]
  have hpb : pairBase (fun x => ∑ zh : Fin 3 → Bool, (2 : ℝ)⁻¹ ^ 3 * gkern σ (x - headC u h aH zh))
      = fun x => ∑ zh : Fin 3 → Bool,
          (2 : ℝ)⁻¹ ^ 3 * pairBase (gkern σ) (x - headC u h aH zh) := by
    funext x
    unfold pairBase
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun zh _ => ?_
    have e1 : x - 1 - headC u h aH zh = x - headC u h aH zh - 1 := by ring
    have e2 : x + 1 - headC u h aH zh = x - headC u h aH zh + 1 := by ring
    rw [e1, e2]
    ring
  rw [hpb, iterDiff_finset_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun zh _ => ?_
  rw [← mul_sub, channel_pair_diff, iterDiff_const_mul,
    iterDiff_translate (List.ofFn (tailB h aT)) (pairBase (gkern σ)) y (headC u h aH zh)]
  ring

/-! ## 2. The decision pair: flipping the first head coordinate -/

/-- Flip the first head coordinate. -/
def flip0 (zh : Fin 3 → Bool) : Fin 3 → Bool := Function.update zh 0 (!(zh 0))

theorem flip0_flip0 (zh : Fin 3 → Bool) : flip0 (flip0 zh) = zh := by
  funext i
  unfold flip0
  by_cases hi : i = 0
  · subst hi; simp
  · simp [Function.update_of_ne hi]

/-- The head mean without the first probe coefficient. -/
noncomputable def headK (h : ℝ) (aH : Fin 3 → ℝ) (zh : Fin 3 → Bool) : ℝ :=
  3 * sgnB (zh 0) - 2 * sgnB (zh 1) - 2 * sgnB (zh 2)
    + h * (aH 1 * sgnB (zh 1) + aH 2 * sgnB (zh 2))

theorem sgnB_not (b : Bool) : sgnB (!b) = - sgnB b := by cases b <;> norm_num [sgnB]

theorem headC_plus (h : ℝ) (aH : Fin 3 → ℝ) (zh : Fin 3 → Bool) :
    headC 1 h aH zh = headK h aH zh + h * aH 0 * sgnB (zh 0) := by
  unfold headC headK
  rw [Fin.sum_univ_three]
  ring

theorem headC_minus_flip (h : ℝ) (aH : Fin 3 → ℝ) (zh : Fin 3 → Bool) :
    headC (-1) h aH (flip0 zh) = headK h aH zh - h * aH 0 * sgnB (zh 0) := by
  unfold headC headK flip0
  rw [Fin.sum_univ_three]
  simp only [Function.update_self, Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide), sgnB_not]
  ring

/-- The inner (tail) mixture of one head pattern, as a sum of shifted kernels. -/
noncomputable def tailMix {r : ℕ} (σ h v : ℝ) (aT : Fin r → ℝ) (x : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ r * ∑ t : Fin r → Bool, gkern σ (x - v * parity t - shiftOf (tailB h aT) t)

theorem famDens_eq_tailMix {r : ℕ} (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) (y : ℝ) :
    famDens σ h u v aH aT y
      = (Zc σ)⁻¹ * ((2 : ℝ)⁻¹ ^ 3 * ∑ zh : Fin 3 → Bool, tailMix σ h v aT (y - headC u h aH zh)) := by
  rw [famDens_eq]
  unfold chanDens tailMix
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun zh _ => ?_
  ring

/-- The signed combination of translates that the decision pair's difference is. -/
noncomputable def uWeight {r : ℕ} (s : Bool) (zh : Fin 3 → Bool) (_t : Fin r → Bool) : ℝ :=
  if zh 0 = s then (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r else 0

noncomputable def uCentre {r : ℕ} (h v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ)
    (p : (Fin 3 → Bool) × (Fin r → Bool)) : ℝ :=
  headK h aH p.1 + v * parity p.2 + shiftOf (tailB h aT) p.2

/-- **The decision pair is a first difference.**  Flipping `z_1` in the `u = -1` world matches
the `3u z_1` terms, and what is left is a symmetric difference of step `h aH_1`, with sign
`sgn(z_1)`, of the translates.  Splitting by the sign of `z_1` gives two non-negative mixtures. -/
theorem famDens_udiff {r : ℕ} (σ h v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) (y : ℝ) :
    famDens σ h 1 v aH aT y - famDens σ h (-1) v aH aT y
      = 2 * (Zc σ)⁻¹ *
          (iterDiff (fun x => ∑ p : (Fin 3 → Bool) × (Fin r → Bool),
              uWeight true p.1 p.2 * gkern σ (x - uCentre h v aH aT p)) [h * aH 0] y
            - iterDiff (fun x => ∑ p : (Fin 3 → Bool) × (Fin r → Bool),
              uWeight false p.1 p.2 * gkern σ (x - uCentre h v aH aT p)) [h * aH 0] y) := by
  -- reindex the u = -1 world by flipping z_1
  have hinv : Function.Involutive flip0 := fun zh => flip0_flip0 zh
  have hflip : ∑ zh : Fin 3 → Bool, tailMix σ h v aT (y - headC (-1) h aH zh)
      = ∑ zh : Fin 3 → Bool, tailMix σ h v aT (y - headC (-1) h aH (flip0 zh)) :=
    (Fintype.sum_equiv (Function.Involutive.toPerm flip0 hinv) _ _
      (fun zh => by simp [Function.Involutive.coe_toPerm, flip0_flip0])).symm
  rw [famDens_eq_tailMix, famDens_eq_tailMix, hflip]
  simp only [headC_plus, headC_minus_flip]
  -- both sides as sums over (head, tail) patterns
  have hL : ∀ zh : Fin 3 → Bool,
      tailMix σ h v aT (y - (headK h aH zh + h * aH 0 * sgnB (zh 0)))
        - tailMix σ h v aT (y - (headK h aH zh - h * aH 0 * sgnB (zh 0)))
      = (2 : ℝ)⁻¹ ^ r * ∑ t : Fin r → Bool, sgnB (zh 0) *
          (gkern σ ((y - h * aH 0) - uCentre h v aH aT (zh, t))
            - gkern σ ((y + h * aH 0) - uCentre h v aH aT (zh, t))) := by
    intro zh
    unfold tailMix
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun t _ => ?_)
    unfold uCentre
    cases hz : zh 0
    · simp only [hz, sgnB]
      norm_num
      ring_nf
    · simp only [hz, sgnB]
      norm_num
      ring_nf
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun zh _ => hL zh]
  -- the right-hand side, as one sum over (head, tail) patterns
  have hR : ∀ s : Bool, iterDiff (fun x => ∑ p : (Fin 3 → Bool) × (Fin r → Bool),
      uWeight s p.1 p.2 * gkern σ (x - uCentre h v aH aT p)) [h * aH 0] y
      = (∑ p : (Fin 3 → Bool) × (Fin r → Bool), uWeight s p.1 p.2 *
          (gkern σ ((y - h * aH 0) - uCentre h v aH aT p)
            - gkern σ ((y + h * aH 0) - uCentre h v aH aT p))) / 2 := by
    intro s
    simp only [iterDiff_cons, iterDiff_nil, symDiff]
    rw [← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hR true, hR false]
  have key : ∀ (a S T : ℝ), 2 * a * (S / 2 - T / 2) = a * (S - T) := by intros; ring
  rw [key, ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun zh _ => Finset.sum_congr rfl fun t _ => ?_
  unfold uWeight
  cases hz : zh 0 <;> simp only [sgnB, Bool.false_eq_true, Bool.true_eq_false, ite_true,
    ite_false, if_true, if_false] <;> ring

/-! ## 3. Envelopes, floor, chi-squares -/

theorem abs_headC_le (u h : ℝ) (hu : u = 1 ∨ u = -1) (hh : 0 ≤ h) (aH : Fin 3 → ℝ)
    (zh : Fin 3 → Bool) : |headC u h aH zh| ≤ 7 + h * ∑ i, |aH i| := by
  unfold headC
  have h0 : |3 * u * sgnB (zh 0)| = 3 := by
    rw [abs_mul, abs_mul, sgnB_abs]; rcases hu with rfl | rfl <;> norm_num
  have h1 : |2 * sgnB (zh 1)| = 2 := by rw [abs_mul, sgnB_abs]; norm_num
  have h2 : |2 * sgnB (zh 2)| = 2 := by rw [abs_mul, sgnB_abs]; norm_num
  have h3 : |h * ∑ i, aH i * sgnB (zh i)| ≤ h * ∑ i, |aH i| := by
    rw [abs_mul, abs_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left ?_ hh
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, sgnB_abs, mul_one]
  calc |3 * u * sgnB (zh 0) - 2 * sgnB (zh 1) - 2 * sgnB (zh 2) + h * ∑ i, aH i * sgnB (zh i)|
      ≤ |3 * u * sgnB (zh 0)| + |2 * sgnB (zh 1)| + |2 * sgnB (zh 2)|
          + |h * ∑ i, aH i * sgnB (zh i)| := by
        have := abs_add_le (3 * u * sgnB (zh 0) - 2 * sgnB (zh 1) - 2 * sgnB (zh 2))
          (h * ∑ i, aH i * sgnB (zh i))
        have := abs_sub (3 * u * sgnB (zh 0) - 2 * sgnB (zh 1)) (2 * sgnB (zh 2))
        have := abs_sub (3 * u * sgnB (zh 0)) (2 * sgnB (zh 1))
        linarith
    _ ≤ 7 + h * ∑ i, |aH i| := by rw [h0, h1, h2]; linarith

theorem abs_shiftOf_tailB_le {r : ℕ} (h : ℝ) (hh : 0 ≤ h) (aT : Fin r → ℝ) (t : Fin r → Bool) :
    |shiftOf (tailB h aT) t| ≤ h * ∑ i, |aT i| := by
  refine (abs_shiftOf_le _ t).trans (le_of_eq ?_)
  unfold tailB
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul, abs_of_nonneg hh]

/-- **Every density of the family sits above one floor.** -/
theorem famDens_floor {r : ℕ} (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hhh : h ≤ h₀)
    (u v : ℝ) (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ)
    (hnorm : ∑ i, |aH i| + ∑ i, |aT i| ≤ 1) (y : ℝ) :
    (Zc σ)⁻¹ * envLo σ (8 + 2 * h₀) y ≤ famDens σ h u v aH aT y := by
  have hZ := Zc_pos σ hσ
  have hterm : ∀ zh t, (Zc σ)⁻¹ * envLo σ (8 + 2 * h₀) y
      ≤ gaussianPDFReal (headC u h aH zh + v * parity t + shiftOf (tailB h aT) t) (var2 σ) y := by
    intro zh t
    rw [gaussianPDFReal_eq]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hZ.le)
    refine gaussian_lower_envelope σ _ y _ hσ ?_
    have ha := abs_headC_le u h hu hh aH zh
    have hp : |v * parity t| = 1 := by
      rw [abs_mul, parity_abs]; rcases hv with rfl | rfl <;> norm_num
    have hs := abs_shiftOf_tailB_le h hh aT t
    have hA : h * (∑ i, |aH i| + ∑ i, |aT i|) ≤ h₀ :=
      (mul_le_of_le_one_right hh hnorm).trans hhh
    calc |headC u h aH zh + v * parity t + shiftOf (tailB h aT) t|
        ≤ |headC u h aH zh| + |v * parity t| + |shiftOf (tailB h aT) t| := by
          have := abs_add_le (headC u h aH zh + v * parity t) (shiftOf (tailB h aT) t)
          have := abs_add_le (headC u h aH zh) (v * parity t)
          linarith
      _ ≤ 8 + 2 * h₀ := by nlinarith [abs_nonneg (aH 0), hh]
  unfold famDens
  have hc3 : ((2 : ℝ)⁻¹ ^ 3) * ((Fintype.card (Fin 3 → Bool) : ℕ) : ℝ) = 1 := by
    simp [Fintype.card_fun]; norm_num
  have hcr : ((2 : ℝ)⁻¹ ^ r) * ((Fintype.card (Fin r → Bool) : ℕ) : ℝ) = 1 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
  set E := (Zc σ)⁻¹ * envLo σ (8 + 2 * h₀) y with hE
  have hinner : ∀ zh, E ≤ (2 : ℝ)⁻¹ ^ r * ∑ t : Fin r → Bool,
      gaussianPDFReal (headC u h aH zh + v * parity t + shiftOf (tailB h aT) t) (var2 σ) y := by
    intro zh
    have hs := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin r → Bool))) =>
      hterm zh t)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    calc E = (2 : ℝ)⁻¹ ^ r * ((Fintype.card (Fin r → Bool) : ℕ) : ℝ) * E := by rw [hcr, one_mul]
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hs := Finset.sum_le_sum (fun zh (_ : zh ∈ (Finset.univ : Finset (Fin 3 → Bool))) =>
    hinner zh)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  calc E = (2 : ℝ)⁻¹ ^ 3 * ((Fintype.card (Fin 3 → Bool) : ℕ) : ℝ) * E := by rw [hc3, one_mul]
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- The identification constant: no probe, no `h`. -/
noncomputable def Cv (r : ℕ) (σ h₀ : ℝ) : ℝ :=
  4 / Zc σ * ∫ y, envUp σ (8 + 2 * h₀) r y ^ 2 / envLo σ (8 + 2 * h₀) y

/-- The decision constant: no probe, no `h`. -/
noncomputable def Cu (σ h₀ : ℝ) : ℝ :=
  16 / Zc σ * ∫ y, envUp σ (8 + 2 * h₀) 1 y ^ 2 / envLo σ (8 + 2 * h₀) y

/-- A pointwise envelope and the floor give the chi-square. -/
theorem chi_of_envelope (σ R : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (s : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (p q : ℝ → ℝ) (hfl : ∀ y, (Zc σ)⁻¹ * envLo σ R y ≤ q y)
    (hd : ∀ y, |p y - q y| ≤ (Zc σ)⁻¹ * (K * envUp σ R s y)) :
    ∫⁻ y, ENNReal.ofReal ((p y - q y) ^ 2 / q y)
      ≤ ENNReal.ofReal (K ^ 2 / Zc σ * ∫ y, envUp σ R s y ^ 2 / envLo σ R y) := by
  have hZ := Zc_pos σ hσ
  have hpt : ∀ y, (p y - q y) ^ 2 / q y
      ≤ K ^ 2 / Zc σ * (envUp σ R s y ^ 2 / envLo σ R y) := by
    intro y
    have hlo := envLo_pos σ R y
    have hflpos : 0 < (Zc σ)⁻¹ * envLo σ R y := mul_pos (inv_pos.mpr hZ) hlo
    have hE : 0 ≤ K * envUp σ R s y := mul_nonneg hK (envUp_nonneg σ R s y hR)
    have hsq : (p y - q y) ^ 2 ≤ ((Zc σ)⁻¹ * (K * envUp σ R s y)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hd y) 2
    calc (p y - q y) ^ 2 / q y ≤ ((Zc σ)⁻¹ * (K * envUp σ R s y)) ^ 2
          / ((Zc σ)⁻¹ * envLo σ R y) := div_le_div₀ (sq_nonneg _) hsq hflpos (hfl y)
      _ = K ^ 2 / Zc σ * (envUp σ R s y ^ 2 / envLo σ R y) := by
          field_simp
  have hint : Integrable (fun y => K ^ 2 / Zc σ * (envUp σ R s y ^ 2 / envLo σ R y)) :=
    (envRatio_integrable σ R hσ hR s).const_mul _
  have hnn : 0 ≤ᵐ[volume] fun y => K ^ 2 / Zc σ * (envUp σ R s y ^ 2 / envLo σ R y) :=
    Filter.Eventually.of_forall fun y =>
      mul_nonneg (div_nonneg (sq_nonneg K) hZ.le) (div_nonneg (sq_nonneg _) (envLo_pos _ _ _).le)
  calc ∫⁻ y, ENNReal.ofReal ((p y - q y) ^ 2 / q y)
      ≤ ∫⁻ y, ENNReal.ofReal (K ^ 2 / Zc σ * (envUp σ R s y ^ 2 / envLo σ R y)) :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpt y)
    _ = ENNReal.ofReal (∫ y, K ^ 2 / Zc σ * (envUp σ R s y ^ 2 / envLo σ R y)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = _ := by rw [integral_const_mul]

/-- **Identification pair: chi-square `<= Cv h^{2r}`, uniformly over the probes.** -/
theorem famChi_v_le {r : ℕ} (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hhh : h ≤ h₀)
    (u : ℝ) (hu : u = 1 ∨ u = -1) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ)
    (hnorm : ∑ i, |aH i| + ∑ i, |aT i| ≤ 1) :
    ∫⁻ y, ENNReal.ofReal ((famDens σ h u 1 aH aT y - famDens σ h u (-1) aH aT y) ^ 2
        / famDens σ h u (-1) aH aT y)
      ≤ ENNReal.ofReal (Cv r σ h₀ * h ^ (2 * r)) := by
  have h₀nn : 0 ≤ h₀ := hh.trans hhh
  have hZ := Zc_pos σ hσ
  have hTsum : ∑ i, |aT i| ≤ 1 := by
    have : 0 ≤ ∑ i, |aH i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hHsum : ∑ i, |aH i| ≤ 1 := by
    have : 0 ≤ ∑ i, |aT i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hprod : ∏ i, |tailB h aT i| ≤ h ^ r := by
    unfold tailB
    have : ∀ i, |h * aT i| ≤ h := by
      intro i
      rw [abs_mul, abs_of_nonneg hh]
      have hi : |aT i| ≤ ∑ j, |aT j| :=
        Finset.single_le_sum (f := fun j => |aT j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      nlinarith
    calc ∏ i, |h * aT i| ≤ ∏ _i : Fin r, h :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => this i)
      _ = h ^ r := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hb : ∑ i, |tailB h aT i| ≤ h₀ := by
    unfold tailB
    have : ∑ i, |h * aT i| = h * ∑ i, |aT i| := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg hh]
    rw [this]
    nlinarith
  have hcs : ∀ zh, |headC u h aH zh| ≤ 7 + h₀ := by
    intro zh
    have := abs_headC_le u h hu hh aH zh
    nlinarith
  have henv := fun y => pair_envelope_fin σ (7 + h₀) h₀ hσ (by linarith) h₀nn
    (fun _ : Fin 3 → Bool => (2 : ℝ)⁻¹ ^ 3) (fun zh => headC u h aH zh) (fun _ => by positivity)
    (by simp [Fintype.card_fun]; norm_num) hcs (tailB h aT) hb y
  have hR : (7 + h₀) + 1 + h₀ = 8 + 2 * h₀ := by ring
  have hd : ∀ y, |famDens σ h u 1 aH aT y - famDens σ h u (-1) aH aT y|
      ≤ (Zc σ)⁻¹ * ((2 * h ^ r) * envUp σ (8 + 2 * h₀) r y) := by
    intro y
    rw [famDens_vdiff, abs_mul, abs_of_pos (inv_pos.mpr hZ)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hZ.le)
    have hE := envUp_nonneg σ (8 + 2 * h₀) r y (by linarith)
    have := henv y
    rw [hR] at this
    calc _ ≤ 2 * ((∏ i, |tailB h aT i|) * envUp σ (8 + 2 * h₀) r y) := this
      _ ≤ 2 * (h ^ r * envUp σ (8 + 2 * h₀) r y) := by gcongr
      _ = (2 * h ^ r) * envUp σ (8 + 2 * h₀) r y := by ring
  have hchi := chi_of_envelope σ (8 + 2 * h₀) hσ (by linarith) r (2 * h ^ r) (by positivity)
    (famDens σ h u 1 aH aT) (famDens σ h u (-1) aH aT)
    (fun y => famDens_floor σ h h₀ hσ hh hhh u (-1) hu (Or.inr rfl) aH aT hnorm y) hd
  refine hchi.trans (le_of_eq ?_)
  unfold Cv
  congr 1
  rw [mul_pow, ← pow_mul]
  ring

/-- **Decision pair: chi-square `<= Cu h^2`, uniformly over the probes.** -/
theorem famChi_u_le {r : ℕ} (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hhh : h ≤ h₀)
    (v : ℝ) (hv : v = 1 ∨ v = -1) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ)
    (hnorm : ∑ i, |aH i| + ∑ i, |aT i| ≤ 1) :
    ∫⁻ y, ENNReal.ofReal ((famDens σ h 1 v aH aT y - famDens σ h (-1) v aH aT y) ^ 2
        / famDens σ h (-1) v aH aT y)
      ≤ ENNReal.ofReal (Cu σ h₀ * h ^ 2) := by
  have h₀nn : 0 ≤ h₀ := hh.trans hhh
  have hZ := Zc_pos σ hσ
  have hA0 : |aH 0| ≤ 1 := by
    have h0 : |aH 0| ≤ ∑ i, |aH i| :=
      Finset.single_le_sum (f := fun i => |aH i|) (fun i _ => abs_nonneg _) (Finset.mem_univ 0)
    have : 0 ≤ ∑ i, |aT i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hβ : |h * aH 0| ≤ h := by
    rw [abs_mul, abs_of_nonneg hh]; nlinarith [abs_nonneg (aH 0)]
  -- centres of the decision mixtures
  have hcs : ∀ p : (Fin 3 → Bool) × (Fin r → Bool), |uCentre h v aH aT p| ≤ 8 + h₀ := by
    intro p
    unfold uCentre headK
    have hs := abs_shiftOf_tailB_le h hh aT p.2
    have hp : |v * parity p.2| = 1 := by
      rw [abs_mul, parity_abs]; rcases hv with rfl | rfl <;> norm_num
    have h1 : |3 * sgnB (p.1 0)| = 3 := by rw [abs_mul, sgnB_abs]; norm_num
    have h2 : |2 * sgnB (p.1 1)| = 2 := by rw [abs_mul, sgnB_abs]; norm_num
    have h3 : |2 * sgnB (p.1 2)| = 2 := by rw [abs_mul, sgnB_abs]; norm_num
    have h4 : |h * (aH 1 * sgnB (p.1 1) + aH 2 * sgnB (p.1 2))| ≤ h * (|aH 1| + |aH 2|) := by
      rw [abs_mul, abs_of_nonneg hh]
      refine mul_le_mul_of_nonneg_left ?_ hh
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, sgnB_abs, sgnB_abs, mul_one, mul_one]
    have hsumH : |aH 1| + |aH 2| ≤ ∑ i, |aH i| := by
      rw [Fin.sum_univ_three]; linarith [abs_nonneg (aH 0)]
    have hA : h * (∑ i, |aH i| + ∑ i, |aT i|) ≤ h₀ :=
      (mul_le_of_le_one_right hh hnorm).trans hhh
    calc |3 * sgnB (p.1 0) - 2 * sgnB (p.1 1) - 2 * sgnB (p.1 2)
          + h * (aH 1 * sgnB (p.1 1) + aH 2 * sgnB (p.1 2)) + v * parity p.2
          + shiftOf (tailB h aT) p.2|
        ≤ |3 * sgnB (p.1 0)| + |2 * sgnB (p.1 1)| + |2 * sgnB (p.1 2)|
          + |h * (aH 1 * sgnB (p.1 1) + aH 2 * sgnB (p.1 2))| + |v * parity p.2|
          + |shiftOf (tailB h aT) p.2| := by
          have := abs_add_le (3 * sgnB (p.1 0) - 2 * sgnB (p.1 1) - 2 * sgnB (p.1 2)
            + h * (aH 1 * sgnB (p.1 1) + aH 2 * sgnB (p.1 2)) + v * parity p.2)
            (shiftOf (tailB h aT) p.2)
          have := abs_add_le (3 * sgnB (p.1 0) - 2 * sgnB (p.1 1) - 2 * sgnB (p.1 2)
            + h * (aH 1 * sgnB (p.1 1) + aH 2 * sgnB (p.1 2))) (v * parity p.2)
          have := abs_add_le (3 * sgnB (p.1 0) - 2 * sgnB (p.1 1) - 2 * sgnB (p.1 2))
            (h * (aH 1 * sgnB (p.1 1) + aH 2 * sgnB (p.1 2)))
          have := abs_sub (3 * sgnB (p.1 0) - 2 * sgnB (p.1 1)) (2 * sgnB (p.1 2))
          have := abs_sub (3 * sgnB (p.1 0)) (2 * sgnB (p.1 1))
          linarith
      _ ≤ 8 + h₀ := by
          rw [h1, h2, h3, hp]
          nlinarith [hh]
  have hwsum : ∀ s : Bool, ∑ p : (Fin 3 → Bool) × (Fin r → Bool), uWeight s p.1 p.2 ≤ 1 := by
    intro s
    have hle : ∀ p : (Fin 3 → Bool) × (Fin r → Bool),
        uWeight s p.1 p.2 ≤ (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r := by
      intro p; unfold uWeight; split_ifs
      · exact le_rfl
      · positivity
    calc ∑ p : (Fin 3 → Bool) × (Fin r → Bool), uWeight s p.1 p.2
        ≤ ∑ _p : (Fin 3 → Bool) × (Fin r → Bool), (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r :=
          Finset.sum_le_sum fun p _ => hle p
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
          push_cast
          rw [show (8 : ℝ) * 2 ^ r * ((2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r)
              = (8 * (2 : ℝ)⁻¹ ^ 3) * ((2 : ℝ) ^ r * (2 : ℝ)⁻¹ ^ r) by ring, ← mul_pow]
          norm_num
  have hwnn : ∀ s : Bool, ∀ p : (Fin 3 → Bool) × (Fin r → Bool), 0 ≤ uWeight s p.1 p.2 := by
    intro s p; unfold uWeight; split_ifs <;> positivity
  have hbstep : ∑ i : Fin 1, |(fun _ : Fin 1 => h * aH 0) i| ≤ h₀ := by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    linarith
  have hofFn : List.ofFn (fun _ : Fin 1 => h * aH 0) = [h * aH 0] := by simp
  have henv : ∀ s : Bool, ∀ y, |iterDiff (fun x => ∑ p : (Fin 3 → Bool) × (Fin r → Bool),
      uWeight s p.1 p.2 * gkern σ (x - uCentre h v aH aT p)) [h * aH 0] y|
        ≤ h * envUp σ (8 + 2 * h₀) 1 y := by
    intro s y
    have := mixture_envelope_fin σ (8 + h₀) h₀ hσ (by linarith) h₀nn
      (fun p : (Fin 3 → Bool) × (Fin r → Bool) => uWeight s p.1 p.2)
      (uCentre h v aH aT) (hwnn s) (hwsum s) hcs (fun _ : Fin 1 => h * aH 0) hbstep y
    rw [hofFn] at this
    have hR : 8 + h₀ + h₀ = 8 + 2 * h₀ := by ring
    rw [hR] at this
    have hE := envUp_nonneg σ (8 + 2 * h₀) 1 y (by linarith)
    refine this.trans ?_
    simp only [Finset.univ_unique, Finset.prod_singleton]
    exact mul_le_mul_of_nonneg_right hβ hE
  have hd : ∀ y, |famDens σ h 1 v aH aT y - famDens σ h (-1) v aH aT y|
      ≤ (Zc σ)⁻¹ * (4 * h * envUp σ (8 + 2 * h₀) 1 y) := by
    intro y
    rw [famDens_udiff]
    have h1 := henv true y
    have h2 := henv false y
    have hsub := abs_sub (iterDiff (fun x => ∑ p : (Fin 3 → Bool) × (Fin r → Bool),
      uWeight true p.1 p.2 * gkern σ (x - uCentre h v aH aT p)) [h * aH 0] y)
      (iterDiff (fun x => ∑ p : (Fin 3 → Bool) × (Fin r → Bool),
      uWeight false p.1 p.2 * gkern σ (x - uCentre h v aH aT p)) [h * aH 0] y)
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (inv_pos.mpr hZ)]
    have hZ' : 0 ≤ (Zc σ)⁻¹ := inv_nonneg.mpr hZ.le
    calc 2 * (Zc σ)⁻¹ * |_| ≤ 2 * (Zc σ)⁻¹ * (h * envUp σ (8 + 2 * h₀) 1 y
          + h * envUp σ (8 + 2 * h₀) 1 y) := by
          gcongr
          linarith
      _ = (Zc σ)⁻¹ * (4 * h * envUp σ (8 + 2 * h₀) 1 y) := by ring
  have hchi := chi_of_envelope σ (8 + 2 * h₀) hσ (by linarith) 1 (4 * h) (by positivity)
    (famDens σ h 1 v aH aT) (famDens σ h (-1) v aH aT)
    (fun y => famDens_floor σ h h₀ hσ hh hhh (-1) v (Or.inr rfl) hv aH aT hnorm y)
    (fun y => by have := hd y; rwa [show 4 * h * envUp σ (8 + 2 * h₀) 1 y
      = (4 * h) * envUp σ (8 + 2 * h₀) 1 y by ring] at this)
  refine hchi.trans (le_of_eq ?_)
  unfold Cu
  congr 1
  ring

/-! ## 4. The channel -/

theorem famDens_pos {r : ℕ} (σ h u v : ℝ) (hσ : 0 < σ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ)
    (y : ℝ) : 0 < famDens σ h u v aH aT y := by
  unfold famDens
  refine mul_pos (by positivity) (Finset.sum_pos (fun zh _ => mul_pos (by positivity)
    (Finset.sum_pos (fun t _ => gaussianPDFReal_pos _ _ _ (var2_ne_zero σ hσ))
      Finset.univ_nonempty)) Finset.univ_nonempty)

theorem continuous_famDens {r : ℕ} (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) :
    Continuous (famDens σ h u v aH aT) := by
  unfold famDens gaussianPDFReal
  fun_prop

theorem lintegral_famDens {r : ℕ} (σ h u v : ℝ) (hσ : 0 < σ) (aH : Fin 3 → ℝ)
    (aT : Fin r → ℝ) : ∫⁻ y, ENNReal.ofReal (famDens σ h u v aH aT y) = 1 := by
  have hv := var2_ne_zero σ hσ
  set c : ℝ := (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ y, ENNReal.ofReal (famDens σ h u v aH aT y)
      = ∑ zh : Fin 3 → Bool, ∑ t : Fin r → Bool, ENNReal.ofReal c
          * gaussianPDF (headC u h aH zh + v * parity t + shiftOf (tailB h aT) t) (var2 σ) y := by
    intro y
    have hexp : famDens σ h u v aH aT y = ∑ zh : Fin 3 → Bool, ∑ t : Fin r → Bool, c
        * gaussianPDFReal (headC u h aH zh + v * parity t + shiftOf (tailB h aT) t) (var2 σ) y := by
      unfold famDens
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun zh _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hc]; ring
    rw [hexp, ENNReal.ofReal_sum_of_nonneg (fun zh _ => Finset.sum_nonneg fun t _ =>
      mul_nonneg hc0 (gaussianPDFReal_nonneg _ _ _))]
    refine Finset.sum_congr rfl fun zh _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg hc0 (gaussianPDFReal_nonneg _ _ _))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ENNReal.ofReal_mul hc0]
    rfl
  simp_rw [hpt]
  rw [lintegral_finset_sum _ (fun zh _ => Finset.measurable_sum _ fun t _ =>
    (measurable_gaussianPDF _ _).const_mul _)]
  have hone : ∀ zh : Fin 3 → Bool, ∫⁻ y, ∑ t : Fin r → Bool, ENNReal.ofReal c
      * gaussianPDF (headC u h aH zh + v * parity t + shiftOf (tailB h aT) t) (var2 σ) y
      = ∑ _t : Fin r → Bool, ENNReal.ofReal c := by
    intro zh
    rw [lintegral_finset_sum _ (fun t _ => (measurable_gaussianPDF _ _).const_mul _)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [lintegral_const_mul _ (measurable_gaussianPDF _ _), lintegral_gaussianPDF_eq_one _ hv,
      mul_one]
  simp_rw [hone]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, nsmul_eq_mul,
    nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  have : (((Fintype.card (Fin 3 → Bool) * Fintype.card (Fin r → Bool) : ℕ) : ℝ)) * c = 1 := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    rw [hc, show (8 : ℝ) * 2 ^ r * ((2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r)
        = (8 * (2 : ℝ)⁻¹ ^ 3) * ((2 : ℝ) ^ r * (2 : ℝ)⁻¹ ^ r) by ring, ← mul_pow]
    norm_num
  rw [this, ENNReal.ofReal_one]

/-- The world's `u` and `v` as signs. -/
noncomputable def uOf (w : Bool × Bool) : ℝ := sgnB w.1
noncomputable def vOf (w : Bool × Bool) : ℝ := sgnB w.2

theorem sgnB_pm (b : Bool) : sgnB b = 1 ∨ sgnB b = -1 := by cases b <;> simp [sgnB]

/-- The channel's density: query `0` is pure noise, query `q >= 1` is probe `q`. -/
noncomputable def famChanDens {r k : ℕ} (σ h : ℝ) (aH : Fin (k + 1) → Fin 3 → ℝ)
    (aT : Fin (k + 1) → Fin r → ℝ) (w : Bool × Bool) (q : Fin (k + 1)) (y : ℝ) : ℝ :=
  if (q : ℕ) = 0 then gaussianPDFReal 0 (var2 σ) y
  else famDens σ h (uOf w) (vOf w) (aH q) (aT q) y

/-- **The latent family as a channel**, for ANY finite family of probes. -/
noncomputable def famChan {r k : ℕ} (σ h : ℝ) (hσ : 0 < σ) (aH : Fin (k + 1) → Fin 3 → ℝ)
    (aT : Fin (k + 1) → Fin r → ℝ) : Channel (Bool × Bool) (Fin (k + 1)) where
  dens := famChanDens σ h aH aT
  dummy := 0
  meas := by
    intro w q
    unfold famChanDens
    split_ifs
    · exact measurable_gaussianPDFReal 0 (var2 σ)
    · exact (continuous_famDens _ _ _ _ _ _).measurable
  pos := by
    intro w q y
    unfold famChanDens
    split_ifs
    · exact gaussianPDFReal_pos _ _ _ (var2_ne_zero σ hσ)
    · exact famDens_pos _ _ _ _ hσ _ _ y
  mass := by
    intro w q
    unfold famChanDens
    split_ifs
    · exact lintegral_gaussianPDF_eq_one 0 (var2_ne_zero σ hσ)
    · exact lintegral_famDens _ _ _ _ hσ _ _
  dummy_same := by
    intro w w' y
    unfold famChanDens
    simp

/-! ## 5. The adaptive lower rates on the Gaussian model -/

/-- The family's safe correspondence: at `u = -1` only answer `0` is safe; at `u = +1` every
other answer is. -/
noncomputable def famSafe (r : ℕ) (w : Bool × Bool) : Finset (Fin (r + 3)) :=
  if w.1 then Finset.univ.erase 0 else {0}

/-- The decision obstruction: the two worlds differing in `u`. -/
theorem famSafe_unsafe (r : ℕ) :
    Unsafe (famSafe r) ({(true, true), (false, true)} : Finset (Bool × Bool)) := by
  intro a
  by_cases ha : a = 0
  · exact ⟨(true, true), by simp, by simp [famSafe, ha]⟩
  · exact ⟨(false, true), by simp, by simp [famSafe, ha]⟩

/-- **The safe decision's adaptive lower rate on the latent Gaussian family.**  Every
finite-horizon randomised adaptive policy that answers safely with probability `1 - delta` in
every world pays, at the world `u = v = +1`, `Cu h^2 * E[#queries] >= (1-delta) log(1/delta)
- log 2`.  The probe family is arbitrary. -/
theorem family_safe_lower {r k : ℕ} (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hhh : h ≤ h₀)
    (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ)
    (hnorm : ∀ q, ∑ i, |aH q i| + ∑ i, |aT q i| ≤ 1)
    (pol : Policy (Fin (k + 1))) (n : ℕ) (out : Hist (Fin (k + 1)) n → Fin (r + 3))
    (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ famSafe r w})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : ∀ w, 1 - δ ≤ (hist (famChan σ h hσ aH aT) pol w n).real {ω | out ω ∈ famSafe r w}) :
    ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2)
      ≤ ENNReal.ofReal (Cu σ h₀ * h ^ 2) * costN (famChan σ h hσ aH aT) pol (true, true) n := by
  have hcard : 2 ≤ ({(true, true), (false, true)} : Finset (Bool × Bool)).card := by decide
  have h := obstruction_lower_chi (famChan σ h hσ aH aT) pol n out (famSafe r) hmeas δ hδ hδ1 hcorr
    {(true, true), (false, true)} (famSafe_unsafe r) hcard (true, true) (by simp)
    (ENNReal.ofReal (Cu σ h₀ * h ^ 2)) (fun v hv hne q hq => by
      have hv' : v = (false, true) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact absurd rfl hne
        · rfl
      subst hv'
      have hq0 : (q : ℕ) ≠ 0 := fun h0 => hq (Fin.ext h0)
      unfold chi
      show ∫⁻ y, ENNReal.ofReal ((famChanDens σ h aH aT (true, true) q y
          - famChanDens σ h aH aT (false, true) q y) ^ 2
          / famChanDens σ h aH aT (false, true) q y) ≤ _
      unfold famChanDens uOf vOf
      simp only [hq0, if_false, sgnB, if_true]
      exact famChi_u_le σ h h₀ hσ hh hhh 1 (Or.inl rfl) (aH q) (aT q) (hnorm q))
  have hc : ((({(true, true), (false, true)} : Finset (Bool × Bool)).card : ℝ) - 1) = 1 := by
    rw [show ({(true, true), (false, true)} : Finset (Bool × Bool)).card = 2 by decide]
    norm_num
  rw [hc, div_one] at h
  exact h

/-- **Identification's adaptive lower rate on the latent Gaussian family.**  At the obstruction
of the two nuisance worlds, `Cv h^{2r} * E[#queries] >= (1-delta) log(1/delta) - log 2`. -/
theorem family_id_lower {r k : ℕ} (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hhh : h ≤ h₀)
    (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ)
    (hnorm : ∀ q, ∑ i, |aH q i| + ∑ i, |aT q i| ≤ 1)
    (pol : Policy (Fin (k + 1))) (n : ℕ) (out : Hist (Fin (k + 1)) n → Bool × Bool)
    (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ ({w} : Finset (Bool × Bool))})
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcorr : ∀ w, 1 - δ ≤ (hist (famChan σ h hσ aH aT) pol w n).real
      {ω | out ω ∈ ({w} : Finset (Bool × Bool))}) :
    ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2)
      ≤ ENNReal.ofReal (Cv r σ h₀ * h ^ (2 * r))
          * costN (famChan σ h hσ aH aT) pol (true, true) n := by
  have hU : Unsafe (fun w : Bool × Bool => ({w} : Finset (Bool × Bool)))
      ({(true, true), (true, false)} : Finset (Bool × Bool)) := by
    intro a
    by_cases ha : a = (true, true)
    · exact ⟨(true, false), by simp, by simp [ha]⟩
    · exact ⟨(true, true), by simp, by simp [ha]⟩
  have hcard : 2 ≤ ({(true, true), (true, false)} : Finset (Bool × Bool)).card := by decide
  have h := obstruction_lower_chi (famChan σ h hσ aH aT) pol n out
    (fun w : Bool × Bool => ({w} : Finset (Bool × Bool))) hmeas δ hδ hδ1 hcorr
    {(true, true), (true, false)} hU hcard (true, true) (by simp)
    (ENNReal.ofReal (Cv r σ h₀ * h ^ (2 * r))) (fun v hv hne q hq => by
      have hv' : v = (true, false) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact absurd rfl hne
        · rfl
      subst hv'
      have hq0 : (q : ℕ) ≠ 0 := fun h0 => hq (Fin.ext h0)
      unfold chi
      show ∫⁻ y, ENNReal.ofReal ((famChanDens σ h aH aT (true, true) q y
          - famChanDens σ h aH aT (true, false) q y) ^ 2
          / famChanDens σ h aH aT (true, false) q y) ≤ _
      unfold famChanDens uOf vOf
      simp only [hq0, if_false, sgnB, if_true]
      exact famChi_v_le σ h h₀ hσ hh hhh 1 (Or.inl rfl) (aH q) (aT q) (hnorm q))
  have hc : ((({(true, true), (true, false)} : Finset (Bool × Bool)).card : ℝ) - 1) = 1 := by
    rw [show ({(true, true), (true, false)} : Finset (Bool × Bool)).card = 2 by decide]
    norm_num
  rw [hc, div_one] at h
  exact h

#print axioms iterDiff_translate
#print axioms famDens_vdiff
#print axioms famDens_udiff
#print axioms famDens_floor
#print axioms famChi_v_le
#print axioms famChi_u_le
#print axioms lintegral_famDens
#print axioms family_safe_lower
#print axioms family_id_lower

end CIGAMF.P13.PaperBFamilyChannel
