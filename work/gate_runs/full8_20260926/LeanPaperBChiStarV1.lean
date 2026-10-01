import «LeanPaperBPrivateQueryV1»

/-!
# The χ² star law: the obstruction lower bound without the `1/(|W|-1)` factor

`obstruction_lower` pays `1/(|H|-1)` because it bounds a single binary event by the KL
divergence. The certificate channel shows that this factor is necessary for KL information.
Measured with the second moment of the likelihood ratio, `m2 = ∫ p_w²/p_u = 1 + χ²`, the factor
disappears: `|H|` enters only additively, inside the logarithm.

**The law** (`chi_star_lower`). Take any channel, any finite-horizon policy that is safe with
probability `1 - δ` at every world, an obstruction `H`, a world `w ∈ H`, and `t` with
`m2(w ‖ u; q) ≤ e^t` for every `u ∈ H`, `u ≠ w`, and every informative query `q`. Then for all
`y` and `c > 0`:
```
P_w(N · t ≤ y) ≤ δ + (|H| - 1)(c δ + e^y / c).
```
Here `N` is the number of informative queries. With `c = √(e^y/δ)` the right side is
`δ + 2(|H|-1)√(δ e^y)` (`chi_star_tail`). Hence
`E_w N · t ≥ (1 - δ - 2η)(log(1/δ) - 2 log((|H|-1)/η))` (`chi_star_expect`).

**Proof.**
1. For each `u ∈ H∖{w}`, the event `S_u = {output unsafe at u}` has `P_u(S_u) ≤ δ`. Because `H`
   is an obstruction, the sets `S_u` cover `{output safe at w}`.
2. With `R = dP_u/dP_w` and `Z = dP_w/dP_u = 1/R`, pointwise
   `1_{S_u ∩ B} ≤ c R 1_{S_u} + (Z/c) 1_B`, where `B = {N t ≤ y}`.
3. Integrate under `P_w`. The first term is `c P_u(S_u)` by the density identity
   (`hist_density`).
4. The second is at most `(e^y/c) ∫ Z e^{-tN} dP_w ≤ e^y/c` by the product inequality
   (`lintegral_prodQ_le`): each informative step contributes `m2 · e^{-t} ≤ 1`, the dummy `1`.

The change of measure is Degenne–Koolen's Proposition 18. The second moment replaces their
sub-Gaussian concentration, so the bound is non-asymptotic and needs no assumption on the
channel.
-/

namespace CIGAMF.P13.PaperBChiStar

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperALowerKL
open CIGAMF.P13.PaperBObstructionLaw CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBPrivateQuery
open CIGAMF.P13.PaperBHellingerTest

variable {W Q A : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-! ## 1. Products along a history -/

/-- The product of a per-round factor along a history. -/
noncomputable def prodQ (f : Q → ℝ → ℝ≥0∞) (n : ℕ) (ω : Hist Q n) : ℝ≥0∞ :=
  ∏ i : Fin n, f (ω i).1 (ω i).2

theorem measurable_uncurryQ (f : Q → ℝ → ℝ≥0∞) (hf : ∀ q, Measurable (f q)) :
    Measurable fun p : Q × ℝ => f p.1 p.2 :=
  measurable_from_prod_countable_right fun q => hf q

theorem measurable_prodQ (f : Q → ℝ → ℝ≥0∞) (hf : ∀ q, Measurable (f q)) (n : ℕ) :
    Measurable (prodQ f n) := by
  unfold prodQ
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_uncurryQ f hf).comp (measurable_pi_apply i)

theorem prodQ_snoc (f : Q → ℝ → ℝ≥0∞) (n : ℕ) (p : (Hist Q n × Q) × ℝ) :
    prodQ f (n + 1) (snocMap n p) = prodQ f n p.1.1 * f p.1.2 p.2 := by
  unfold prodQ snocMap
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- **The product inequality for adaptive policies.**  If every round's factor has mean at most
one under the world's observation law, so does the product along the history. -/
theorem lintegral_prodQ_le (C : Channel W Q) (π : Policy Q) (w : W) (f : Q → ℝ → ℝ≥0∞)
    (hf : ∀ q, Measurable (f q)) (h1 : ∀ q, ∫⁻ y, f q y ∂obsLawC C w q ≤ 1) :
    ∀ n, ∫⁻ ω, prodQ f n ω ∂hist C π w n ≤ 1
  | 0 => by
      haveI := hist_prob C π w 0
      simp [prodQ]
  | n + 1 => by
      haveI := hist_prob C π w n
      haveI := π.markov n
      haveI := obsKernel_markov C w n
      have hG := measurable_prodQ f hf n
      simp only [hist]
      rw [lintegral_map (measurable_prodQ f hf (n + 1)) (measurable_snocMap n)]
      simp_rw [prodQ_snoc]
      have hmstep : Measurable fun p : (Hist Q n × Q) × ℝ => prodQ f n p.1.1 * f p.1.2 p.2 :=
        (hG.comp measurable_fst.fst).mul
          ((measurable_uncurryQ f hf).comp (measurable_fst.snd.prodMk measurable_snd))
      rw [Measure.lintegral_compProd hmstep]
      have hin : ∀ x : Hist Q n × Q,
          ∫⁻ y, prodQ f n x.1 * f x.2 y ∂obsKernel C w n x
            = prodQ f n x.1 * ∫⁻ y, f x.2 y ∂obsLawC C w x.2 := by
        intro x
        rw [lintegral_const_mul _ (hf x.2), obsKernel_apply]
      simp_rw [hin]
      calc ∫⁻ x, prodQ f n x.1 * ∫⁻ y, f x.2 y ∂obsLawC C w x.2 ∂(hist C π w n ⊗ₘ π.step n)
          ≤ ∫⁻ x, prodQ f n x.1 ∂(hist C π w n ⊗ₘ π.step n) := by
            refine lintegral_mono fun x => ?_
            calc prodQ f n x.1 * ∫⁻ y, f x.2 y ∂obsLawC C w x.2 ≤ prodQ f n x.1 * 1 := by
                  gcongr; exact h1 x.2
              _ = prodQ f n x.1 := mul_one _
        _ = ∫⁻ ω, prodQ f n ω ∂hist C π w n := lintegral_compProd_fst _ _ hG
        _ ≤ 1 := lintegral_prodQ_le C π w f hf h1 n

/-! ## 2. The density of one world's history law against another's -/

/-- The per-round likelihood ratio `p_v / p_w`. -/
noncomputable def ratio (C : Channel W Q) (v w : W) (q : Q) (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (C.dens v q y / C.dens w q y)

theorem measurable_ratio (C : Channel W Q) (v w : W) (q : Q) : Measurable (ratio C v w q) :=
  ((C.meas v q).div (C.meas w q)).ennreal_ofReal

theorem ratio_mul_dens (C : Channel W Q) (v w : W) (q : Q) (y : ℝ) :
    ENNReal.ofReal (C.dens w q y) * ratio C v w q y = ENNReal.ofReal (C.dens v q y) := by
  unfold ratio
  rw [← ENNReal.ofReal_mul (C.pos w q y).le]
  congr 1
  field_simp [(C.pos w q y).ne']

theorem ratio_mul_ratio (C : Channel W Q) (v w : W) (q : Q) (y : ℝ) :
    ratio C v w q y * ratio C w v q y = 1 := by
  unfold ratio
  rw [← ENNReal.ofReal_mul (div_nonneg (C.pos v q y).le (C.pos w q y).le)]
  rw [show C.dens v q y / C.dens w q y * (C.dens w q y / C.dens v q y) = 1 by
    field_simp [(C.pos w q y).ne', (C.pos v q y).ne']]
  simp

theorem prodQ_ratio_mul (C : Channel W Q) (v w : W) (n : ℕ) (ω : Hist Q n) :
    prodQ (ratio C v w) n ω * prodQ (ratio C w v) n ω = 1 := by
  unfold prodQ
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => ratio_mul_ratio C v w _ _

/-- One round of the density identity: integrating against `v`'s observation law is
integrating against `w`'s with the ratio. -/
theorem lintegral_obs_ratio (C : Channel W Q) (v w : W) (q : Q) (g : ℝ → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ y, g y ∂obsLawC C v q = ∫⁻ y, g y * ratio C v w q y ∂obsLawC C w q := by
  have e1 : ∫⁻ y, g y ∂(volume.withDensity fun y => ENNReal.ofReal (C.dens v q y))
      = ∫⁻ y, ENNReal.ofReal (C.dens v q y) * g y :=
    lintegral_withDensity_eq_lintegral_mul _ (C.meas v q).ennreal_ofReal hg
  have e2 : ∫⁻ y, g y * ratio C v w q y ∂(volume.withDensity fun y => ENNReal.ofReal (C.dens w q y))
      = ∫⁻ y, ENNReal.ofReal (C.dens w q y) * (g y * ratio C v w q y) :=
    lintegral_withDensity_eq_lintegral_mul _ (C.meas w q).ennreal_ofReal
      (hg.mul (measurable_ratio C v w q))
  unfold obsLawC
  rw [e1, e2]
  refine lintegral_congr fun y => ?_
  rw [← ratio_mul_dens C v w q y]
  ring

/-- **The density identity.**  For every adaptive policy and every measurable `F ≥ 0`,
`∫ F dP_v = ∫ F · ∏ (p_v/p_w) dP_w` on histories. -/
theorem hist_density (C : Channel W Q) (π : Policy Q) (v w : W) :
    ∀ n (F : Hist Q n → ℝ≥0∞), Measurable F →
      ∫⁻ ω, F ω ∂hist C π v n = ∫⁻ ω, F ω * prodQ (ratio C v w) n ω ∂hist C π w n
  | 0, F, _ => by
      simp [hist, prodQ]
  | n + 1, F, hF => by
      haveI := hist_prob C π v n
      haveI := hist_prob C π w n
      haveI := π.markov n
      haveI := obsKernel_markov C v n
      haveI := obsKernel_markov C w n
      have hR := measurable_prodQ (ratio C v w) (measurable_ratio C v w) n
      have hRs := measurable_prodQ (ratio C v w) (measurable_ratio C v w) (n + 1)
      have hrat2 := measurable_uncurryQ (ratio C v w) (measurable_ratio C v w)
      have hFs : Measurable fun p : (Hist Q n × Q) × ℝ => F (snocMap n p) :=
        hF.comp (measurable_snocMap n)
      -- the inner integrand, against `w`, with the new ratio
      set g : (Hist Q n × Q) × ℝ → ℝ≥0∞ :=
        fun p => F (snocMap n p) * ratio C v w p.1.2 p.2 with hg
      have hgm : Measurable g :=
        hFs.mul (hrat2.comp (measurable_fst.snd.prodMk measurable_snd))
      set G : Hist Q n × Q → ℝ≥0∞ := fun x => ∫⁻ y, g (x, y) ∂obsKernel C w n x with hGdef
      have hGm : Measurable G := hgm.lintegral_kernel_prod_right'
      set G' : Hist Q n → ℝ≥0∞ := fun h => ∫⁻ q, G (h, q) ∂π.step n h with hG'def
      have hG'm : Measurable G' := (hGm.comp measurable_id).lintegral_kernel_prod_right'
      simp only [hist]
      rw [lintegral_map hF (measurable_snocMap n),
        lintegral_map (f := fun ω => F ω * prodQ (ratio C v w) (n + 1) ω) (hF.mul hRs)
          (measurable_snocMap n)]
      rw [Measure.lintegral_compProd hFs,
        Measure.lintegral_compProd
          (f := fun p => F (snocMap n p) * prodQ (ratio C v w) (n + 1) (snocMap n p))
          ((hF.mul hRs).comp (measurable_snocMap n))]
      -- left: rewrite each inner integral against `w`
      have hleft : ∀ x : Hist Q n × Q,
          ∫⁻ y, F (snocMap n (x, y)) ∂obsKernel C v n x = G x := by
        intro x
        rw [obsKernel_apply, hGdef]
        simp only
        rw [obsKernel_apply]
        exact lintegral_obs_ratio C v w x.2 _ (hF.comp ((measurable_snocMap n).comp
          (measurable_const.prodMk measurable_id)))
      simp_rw [hleft]
      -- right: the new product splits off the old one
      have hright : ∀ x : Hist Q n × Q,
          ∫⁻ y, (F (snocMap n (x, y)) * prodQ (ratio C v w) (n + 1) (snocMap n (x, y)))
              ∂obsKernel C w n x
            = prodQ (ratio C v w) n x.1 * G x := by
        intro x
        have hmx : Measurable fun y : ℝ => g (x, y) :=
          hgm.comp (measurable_const.prodMk measurable_id)
        rw [hGdef]
        simp only
        rw [← lintegral_const_mul _ hmx]
        refine lintegral_congr fun y => ?_
        rw [prodQ_snoc, hg]
        ring
      simp_rw [hright]
      rw [Measure.lintegral_compProd hGm,
        Measure.lintegral_compProd (f := fun a => prodQ (ratio C v w) n a.1 * G a)
          ((hR.comp measurable_fst).mul hGm)]
      have hpull : ∀ h : Hist Q n,
          ∫⁻ q, prodQ (ratio C v w) n (h, q).1 * G (h, q) ∂π.step n h
            = G' h * prodQ (ratio C v w) n h := by
        intro h
        have hmh : Measurable fun q : Q => G (h, q) := hGm.comp (measurable_const.prodMk measurable_id)
        rw [hG'def]
        simp only
        rw [lintegral_const_mul _ hmh, mul_comm]
      simp_rw [hpull]
      exact hist_density C π v w n G' hG'm

/-- **The density identity on events.** -/
theorem hist_density_set (C : Channel W Q) (π : Policy Q) (v w : W) (n : ℕ)
    (S : Set (Hist Q n)) (hS : MeasurableSet S) :
    hist C π v n S = ∫⁻ ω, S.indicator 1 ω * prodQ (ratio C v w) n ω ∂hist C π w n := by
  rw [← hist_density C π v w n (S.indicator 1) (measurable_one.indicator hS),
    lintegral_indicator_one hS]

/-! ## 3. The second moment of the likelihood ratio -/

/-- `m2(w ‖ u; q) = ∫ p_w² / p_u`, which is `1 + χ²(P_w ‖ P_u)`. -/
noncomputable def m2 (C : Channel W Q) (w u : W) (q : Q) : ℝ≥0∞ :=
  ∫⁻ y, ratio C w u q y ∂obsLawC C w q

theorem m2_eq_one_add_chi (C : Channel W Q) (w u : W) (q : Q) :
    m2 C w u q = 1 + chi C w u q := by
  have hmass_w : ∫⁻ y, ENNReal.ofReal (C.dens w q y) = 1 := C.mass w q
  have hmass_u : ∫⁻ y, ENNReal.ofReal (C.dens u q y) = 1 := C.mass u q
  have hm2 : m2 C w u q = ∫⁻ y, ENNReal.ofReal (C.dens w q y ^ 2 / C.dens u q y) := by
    unfold m2 obsLawC
    rw [lintegral_withDensity_eq_lintegral_mul _ (C.meas w q).ennreal_ofReal
      (measurable_ratio C w u q)]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    unfold ratio
    rw [← ENNReal.ofReal_mul (C.pos w q y).le]
    congr 1
    ring
  -- pointwise: p_w²/p_u + p_u = (p_w - p_u)²/p_u + 2 p_w
  have hpt : ∀ y, ENNReal.ofReal (C.dens w q y ^ 2 / C.dens u q y)
      + ENNReal.ofReal (C.dens u q y)
      = ENNReal.ofReal ((C.dens w q y - C.dens u q y) ^ 2 / C.dens u q y)
        + 2 * ENNReal.ofReal (C.dens w q y) := by
    intro y
    have hu := C.pos u q y
    have hw := C.pos w q y
    rw [← ENNReal.ofReal_add (by positivity) hu.le,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp [hu.ne']
    ring
  have hA : Measurable fun y => ENNReal.ofReal (C.dens w q y ^ 2 / C.dens u q y) :=
    ((C.meas w q).pow_const 2 |>.div (C.meas u q)).ennreal_ofReal
  have hB : Measurable fun y => ENNReal.ofReal ((C.dens w q y - C.dens u q y) ^ 2 / C.dens u q y) :=
    (((C.meas w q).sub (C.meas u q)).pow_const 2 |>.div (C.meas u q)).ennreal_ofReal
  have key : (∫⁻ y, ENNReal.ofReal (C.dens w q y ^ 2 / C.dens u q y)) + 1
      = chi C w u q + 1 + 1 := by
    calc (∫⁻ y, ENNReal.ofReal (C.dens w q y ^ 2 / C.dens u q y)) + 1
        = (∫⁻ y, ENNReal.ofReal (C.dens w q y ^ 2 / C.dens u q y))
            + ∫⁻ y, ENNReal.ofReal (C.dens u q y) := by rw [hmass_u]
      _ = ∫⁻ y, (ENNReal.ofReal (C.dens w q y ^ 2 / C.dens u q y)
            + ENNReal.ofReal (C.dens u q y)) := (lintegral_add_left hA _).symm
      _ = ∫⁻ y, (ENNReal.ofReal ((C.dens w q y - C.dens u q y) ^ 2 / C.dens u q y)
            + 2 * ENNReal.ofReal (C.dens w q y)) := lintegral_congr hpt
      _ = chi C w u q + 2 * 1 := by
          rw [lintegral_add_left hB, lintegral_const_mul _ (C.meas w q).ennreal_ofReal, hmass_w]
          rfl
      _ = chi C w u q + 1 + 1 := by rw [mul_one, add_assoc, one_add_one_eq_two]
  rw [hm2, add_comm (1 : ℝ≥0∞) (chi C w u q)]
  exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp key

/-! ## 4. The law -/

variable [Fintype Q]

/-- The factor `e^{-t}` on informative rounds and `1` on the dummy. -/
noncomputable def expFac (d : Q) (t : ℝ) (q : Q) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(t * (if q = d then 0 else 1))))

theorem prodQ_expFac (d : Q) (t : ℝ) (n : ℕ) (ω : Hist Q n) :
    prodQ (fun q _ => expFac d t q) n ω = ENNReal.ofReal (Real.exp (-(t * tauN d n ω))) := by
  unfold prodQ expFac tauN
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- **The χ² supermartingale.**  With `m2 ≤ e^t` on every informative query,
`∫ ∏ (p_w/p_u) · e^{-t N} dP_w ≤ 1`. -/
theorem lintegral_Z_exp_le (C : Channel W Q) (π : Policy Q) (w u : W) (t : ℝ)
    (hm : ∀ q, q ≠ C.dummy → m2 C w u q ≤ ENNReal.ofReal (Real.exp t)) (n : ℕ) :
    ∫⁻ ω, prodQ (ratio C w u) n ω * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω)))
      ∂hist C π w n ≤ 1 := by
  have heq : ∀ ω : Hist Q n, prodQ (ratio C w u) n ω
      * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω)))
      = prodQ (fun q y => ratio C w u q y * expFac C.dummy t q) n ω := by
    intro ω
    rw [← prodQ_expFac]
    unfold prodQ
    rw [← Finset.prod_mul_distrib]
  simp_rw [heq]
  refine lintegral_prodQ_le C π w _ (fun q => (measurable_ratio C w u q).mul_const _) (fun q => ?_) n
  rw [lintegral_mul_const _ (measurable_ratio C w u q)]
  show m2 C w u q * expFac C.dummy t q ≤ 1
  by_cases hq : q = C.dummy
  · subst hq
    have hr : ∀ y, ratio C w u C.dummy y = 1 := by
      intro y
      unfold ratio
      rw [C.dummy_same w u y, div_self (C.pos u _ y).ne', ENNReal.ofReal_one]
    have : m2 C w u C.dummy = 1 := by
      unfold m2
      simp_rw [hr]
      simp
    rw [this]
    unfold expFac
    simp
  · unfold expFac
    rw [if_neg hq, mul_one]
    calc m2 C w u q * ENNReal.ofReal (Real.exp (-t))
        ≤ ENNReal.ofReal (Real.exp t) * ENNReal.ofReal (Real.exp (-t)) := by
          gcongr; exact hm q hq
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          simp

/-- **One alternative.**  `P_w(S ∩ {N t ≤ y}) ≤ c P_u(S) + e^y / c`. -/
theorem one_alt_bound (C : Channel W Q) (π : Policy Q) (w u : W) (t y c : ℝ) (hc : 0 < c)
    (hm : ∀ q, q ≠ C.dummy → m2 C w u q ≤ ENNReal.ofReal (Real.exp t)) (n : ℕ)
    (S : Set (Hist Q n)) (hS : MeasurableSet S) :
    hist C π w n (S ∩ {ω | (tauN C.dummy n ω : ℝ) * t ≤ y})
      ≤ ENNReal.ofReal c * hist C π u n S + ENNReal.ofReal (Real.exp y / c) := by
  haveI := hist_prob C π w n
  have hNm : Measurable fun ω : Hist Q n => (tauN C.dummy n ω : ℝ) :=
    (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_tauN C.dummy n)
  have hBm : MeasurableSet {ω : Hist Q n | (tauN C.dummy n ω : ℝ) * t ≤ y} :=
    measurableSet_le (hNm.mul_const _) measurable_const
  have hRZ : ∀ ω, prodQ (ratio C u w) n ω * prodQ (ratio C w u) n ω = 1 :=
    fun ω => prodQ_ratio_mul C u w n ω
  have hRm : Measurable (prodQ (ratio C u w) n) := measurable_prodQ _ (measurable_ratio C u w) n
  have hZm : Measurable (prodQ (ratio C w u) n) := measurable_prodQ _ (measurable_ratio C w u) n
  have hEm : Measurable fun ω : Hist Q n =>
      ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω))) :=
    (Real.measurable_exp.comp ((hNm.const_mul t).neg)).ennreal_ofReal
  have hIm : Measurable (S.indicator (1 : Hist Q n → ℝ≥0∞)) := measurable_one.indicator hS
  -- pointwise: 1_{S∩B} ≤ c R 1_S + (e^y/c) Z e^{-tN}
  have hpt : ∀ ω, (S ∩ {ω | (tauN C.dummy n ω : ℝ) * t ≤ y}).indicator 1 ω
      ≤ ENNReal.ofReal c * (S.indicator 1 ω * prodQ (ratio C u w) n ω)
        + ENNReal.ofReal (Real.exp y / c)
          * (prodQ (ratio C w u) n ω * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω)))) := by
    intro ω
    by_cases hω : ω ∈ S ∩ {ω | (tauN C.dummy n ω : ℝ) * t ≤ y}
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω.1]
      simp only [Pi.one_apply, one_mul]
      have hNt : (tauN C.dummy n ω : ℝ) * t ≤ y := hω.2
      by_cases hZc : prodQ (ratio C w u) n ω ≤ ENNReal.ofReal c
      · refine le_add_right ?_
        calc (1 : ℝ≥0∞) = prodQ (ratio C u w) n ω * prodQ (ratio C w u) n ω := (hRZ ω).symm
          _ ≤ prodQ (ratio C u w) n ω * ENNReal.ofReal c := by gcongr
          _ = ENNReal.ofReal c * prodQ (ratio C u w) n ω := mul_comm _ _
      · push_neg at hZc
        refine le_add_left ?_
        have hexp : ENNReal.ofReal (1 / c) ≤ ENNReal.ofReal (Real.exp y / c)
            * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [div_mul_eq_mul_div, ← Real.exp_add]
          apply div_le_div_of_nonneg_right _ hc.le
          rw [Real.one_le_exp_iff]
          nlinarith
        calc (1 : ℝ≥0∞) = ENNReal.ofReal c * ENNReal.ofReal (1 / c) := by
              rw [← ENNReal.ofReal_mul hc.le, mul_one_div_cancel hc.ne', ENNReal.ofReal_one]
          _ ≤ prodQ (ratio C w u) n ω * ENNReal.ofReal (1 / c) := by gcongr
          _ ≤ prodQ (ratio C w u) n ω * (ENNReal.ofReal (Real.exp y / c)
                * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω)))) := by gcongr
          _ = ENNReal.ofReal (Real.exp y / c)
                * (prodQ (ratio C w u) n ω
                  * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω)))) := by ring
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have hint := lintegral_mono (μ := hist C π w n) hpt
  rw [lintegral_indicator_one (hS.inter hBm)] at hint
  have hdens : ∫⁻ ω, S.indicator 1 ω * prodQ (ratio C u w) n ω ∂hist C π w n
      = hist C π u n S := by
    rw [← hist_density C π u w n (S.indicator 1) hIm, lintegral_indicator_one hS]
  have hsplit : ∫⁻ ω, (ENNReal.ofReal c * (S.indicator 1 ω * prodQ (ratio C u w) n ω)
        + ENNReal.ofReal (Real.exp y / c)
          * (prodQ (ratio C w u) n ω * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω)))))
        ∂hist C π w n
      = ENNReal.ofReal c * ∫⁻ ω, S.indicator 1 ω * prodQ (ratio C u w) n ω ∂hist C π w n
        + ENNReal.ofReal (Real.exp y / c)
          * ∫⁻ ω, prodQ (ratio C w u) n ω * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω)))
            ∂hist C π w n := by
    rw [lintegral_add_left
      (f := fun ω => ENNReal.ofReal c * (S.indicator 1 ω * prodQ (ratio C u w) n ω))
      ((hIm.mul hRm).const_mul _)]
    rw [lintegral_const_mul (f := fun ω => S.indicator 1 ω * prodQ (ratio C u w) n ω) _
      (hIm.mul hRm)]
    rw [lintegral_const_mul
      (f := fun ω => prodQ (ratio C w u) n ω * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω))))
      _ (hZm.mul hEm)]
  have hZE := lintegral_Z_exp_le C π w u t hm n
  calc hist C π w n (S ∩ {ω | (tauN C.dummy n ω : ℝ) * t ≤ y})
      ≤ _ := hint
    _ = ENNReal.ofReal c * hist C π u n S + ENNReal.ofReal (Real.exp y / c)
          * ∫⁻ ω, prodQ (ratio C w u) n ω * ENNReal.ofReal (Real.exp (-(t * tauN C.dummy n ω)))
            ∂hist C π w n := by rw [hsplit, hdens]
    _ ≤ ENNReal.ofReal c * hist C π u n S + ENNReal.ofReal (Real.exp y / c) * 1 := by
        gcongr
    _ = _ := by rw [mul_one]

variable [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

/-- **The χ² star law.**  At every world `w` of an obstruction `H`, for all `y` and `c > 0`:
`P_w(N t ≤ y) ≤ δ + (|H| - 1)(c δ + e^y / c)`. -/
theorem chi_star_lower (C : Channel W Q) (π : Policy Q) (n : ℕ) (out : Hist Q n → A)
    (safe : W → Finset A) (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ safe w})
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcorr : ∀ w, hist C π w n {ω | out ω ∉ safe w} ≤ ENNReal.ofReal δ)
    (H : Finset W) (hH : Unsafe safe H) (w : W) (hw : w ∈ H) (t y c : ℝ) (hc : 0 < c)
    (hm : ∀ u ∈ H, u ≠ w → ∀ q, q ≠ C.dummy → m2 C w u q ≤ ENNReal.ofReal (Real.exp t)) :
    hist C π w n {ω | (tauN C.dummy n ω : ℝ) * t ≤ y}
      ≤ ENNReal.ofReal δ
        + ((H.card - 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal c * ENNReal.ofReal δ
          + ENNReal.ofReal (Real.exp y / c)) := by
  classical
  set B : Set (Hist Q n) := {ω | (tauN C.dummy n ω : ℝ) * t ≤ y} with hB
  set E := H.erase w with hE
  have hEcard : E.card = H.card - 1 := Finset.card_erase_of_mem hw
  -- cover: B ⊆ {unsafe at w} ∪ ⋃_{u ∈ E} ({unsafe at u} ∩ B)
  have hcover : B ⊆ {ω | out ω ∉ safe w} ∪ ⋃ u ∈ E, ({ω | out ω ∉ safe u} ∩ B) := by
    intro ω hωB
    by_cases hs : out ω ∈ safe w
    · right
      obtain ⟨u, hu, hna⟩ := hH (out ω)
      have hne : u ≠ w := by rintro rfl; exact hna hs
      exact Set.mem_biUnion (Finset.mem_erase.mpr ⟨hne, hu⟩) ⟨hna, hωB⟩
    · left; exact hs
  calc hist C π w n B
      ≤ hist C π w n ({ω | out ω ∉ safe w} ∪ ⋃ u ∈ E, ({ω | out ω ∉ safe u} ∩ B)) :=
        measure_mono hcover
    _ ≤ hist C π w n {ω | out ω ∉ safe w}
          + hist C π w n (⋃ u ∈ E, ({ω | out ω ∉ safe u} ∩ B)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal δ + ∑ u ∈ E, hist C π w n ({ω | out ω ∉ safe u} ∩ B) := by
        gcongr
        · exact hcorr w
        · exact measure_biUnion_finset_le E _
    _ ≤ ENNReal.ofReal δ + ∑ _u ∈ E, (ENNReal.ofReal c * ENNReal.ofReal δ
          + ENNReal.ofReal (Real.exp y / c)) := by
        gcongr with u hu
        have hne := (Finset.mem_erase.mp hu).1
        have huH := (Finset.mem_erase.mp hu).2
        refine (one_alt_bound C π w u t y c hc (hm u huH hne) n _ (hmeas u).compl).trans ?_
        gcongr
        exact hcorr u
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hEcard]

/-- **The tail, optimised.**  With `c = √(e^y/δ)`: `P_w(N t ≤ y) ≤ δ + 2(|H|-1)√(δ e^y)`. -/
theorem chi_star_tail (C : Channel W Q) (π : Policy Q) (n : ℕ) (out : Hist Q n → A)
    (safe : W → Finset A) (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ safe w})
    (δ : ℝ) (hδ : 0 < δ)
    (hcorr : ∀ w, hist C π w n {ω | out ω ∉ safe w} ≤ ENNReal.ofReal δ)
    (H : Finset W) (hH : Unsafe safe H) (w : W) (hw : w ∈ H) (t y : ℝ)
    (hm : ∀ u ∈ H, u ≠ w → ∀ q, q ≠ C.dummy → m2 C w u q ≤ ENNReal.ofReal (Real.exp t)) :
    hist C π w n {ω | (tauN C.dummy n ω : ℝ) * t ≤ y}
      ≤ ENNReal.ofReal (δ + 2 * ((H.card : ℝ) - 1) * Real.sqrt (δ * Real.exp y)) := by
  have hey : 0 < Real.exp y := Real.exp_pos y
  set c := Real.sqrt (Real.exp y / δ) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hey hδ)
  have h := chi_star_lower C π n out safe hmeas δ hδ.le hcorr H hH w hw t y c hc hm
  refine h.trans (le_of_eq ?_)
  have hcard1 : 1 ≤ H.card := Finset.card_pos.mpr ⟨w, hw⟩
  have hk : ((H.card - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((H.card : ℝ) - 1) := by
    rw [← ENNReal.ofReal_natCast, Nat.cast_sub hcard1]
    simp
  have hcδ : c * δ = Real.sqrt (δ * Real.exp y) := by
    rw [hcdef, show δ = Real.sqrt δ ^ 2 from (Real.sq_sqrt hδ.le).symm]
    rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ Real.sqrt δ ^ 2), Real.sqrt_sq (Real.sqrt_nonneg _)]
    rw [Real.sqrt_mul (by positivity) , Real.sqrt_sq (Real.sqrt_nonneg _)]
    have : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    field_simp
  have hyc : Real.exp y / c = Real.sqrt (δ * Real.exp y) := by
    have hsq : Real.sqrt (Real.exp y / δ) * Real.sqrt (δ * Real.exp y) = Real.exp y := by
      rw [← Real.sqrt_mul (div_nonneg hey.le hδ.le)]
      rw [show Real.exp y / δ * (δ * Real.exp y) = Real.exp y ^ 2 by field_simp]
      exact Real.sqrt_sq hey.le
    rw [hcdef, div_eq_iff hc.ne']
    linarith [hsq]
  rw [hk, ← ENNReal.ofReal_mul hc.le, hcδ, hyc, ← ENNReal.ofReal_add (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by
      have : (1 : ℝ) ≤ H.card := by exact_mod_cast hcard1
      linarith), ← ENNReal.ofReal_add hδ.le (by
      have : (1 : ℝ) ≤ H.card := by exact_mod_cast hcard1
      positivity)]
  congr 1
  ring

/-- **The law in expectation.**  With `η ∈ (0,1)`, `2 ≤ |H|` and `t > 0`,
`E_w[N] · t ≥ (1 - δ - 2η) · log(η² / ((|H|-1)² δ))`: the leading term is `log(1/δ)`, and `|H|`
enters only inside the logarithm. -/
theorem chi_star_expect (C : Channel W Q) (π : Policy Q) (n : ℕ) (out : Hist Q n → A)
    (safe : W → Finset A) (hmeas : ∀ w, MeasurableSet {ω | out ω ∈ safe w})
    (δ : ℝ) (hδ : 0 < δ)
    (hcorr : ∀ w, hist C π w n {ω | out ω ∉ safe w} ≤ ENNReal.ofReal δ)
    (H : Finset W) (hH : Unsafe safe H) (hcard : 2 ≤ H.card) (w : W) (hw : w ∈ H)
    (t : ℝ) (ht : 0 < t)
    (hm : ∀ u ∈ H, u ≠ w → ∀ q, q ≠ C.dummy → m2 C w u q ≤ ENNReal.ofReal (Real.exp t))
    (η : ℝ) (hη : 0 < η)
    (hy : 0 ≤ Real.log (η ^ 2 / (((H.card : ℝ) - 1) ^ 2 * δ))) :
    ENNReal.ofReal ((1 - δ - 2 * η) * Real.log (η ^ 2 / (((H.card : ℝ) - 1) ^ 2 * δ)))
      ≤ costN C π w n * ENNReal.ofReal t := by
  haveI := hist_prob C π w n
  set k : ℝ := (H.card : ℝ) - 1 with hk
  have hk1 : 1 ≤ k := by
    have : (2 : ℝ) ≤ H.card := by exact_mod_cast hcard
    linarith
  set y := Real.log (η ^ 2 / (k ^ 2 * δ)) with hydef
  have hpos : 0 < η ^ 2 / (k ^ 2 * δ) := by positivity
  have hey : Real.exp y = η ^ 2 / (k ^ 2 * δ) := Real.exp_log hpos
  have htail := chi_star_tail C π n out safe hmeas δ hδ hcorr H hH w hw t y hm
  have hsq : Real.sqrt (δ * Real.exp y) = η / k := by
    rw [hey, show δ * (η ^ 2 / (k ^ 2 * δ)) = (η / k) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [hsq, show δ + 2 * k * (η / k) = δ + 2 * η by field_simp] at htail
  -- Markov on the complement: N t > y with probability at least 1 - δ - 2η
  have hNm : Measurable fun ω : Hist Q n => (tauN C.dummy n ω : ℝ) :=
    (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_tauN C.dummy n)
  have hBm : MeasurableSet {ω : Hist Q n | (tauN C.dummy n ω : ℝ) * t ≤ y} :=
    measurableSet_le (hNm.mul_const _) measurable_const
  have hpt : ∀ ω, ENNReal.ofReal y * ({ω : Hist Q n | (tauN C.dummy n ω : ℝ) * t ≤ y}ᶜ).indicator 1 ω
      ≤ (tauN C.dummy n ω : ℝ≥0∞) * ENNReal.ofReal t := by
    intro ω
    by_cases hω : ω ∈ {ω : Hist Q n | (tauN C.dummy n ω : ℝ) * t ≤ y}ᶜ
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have : y < (tauN C.dummy n ω : ℝ) * t := lt_of_not_ge hω
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact ENNReal.ofReal_le_ofReal this.le
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact zero_le
  have hint := lintegral_mono (μ := hist C π w n) hpt
  rw [lintegral_const_mul _ (measurable_one.indicator hBm.compl), lintegral_indicator_one hBm.compl,
    lintegral_mul_const _ (measurable_tauN_ennreal C.dummy n)] at hint
  have hcompl : ENNReal.ofReal (1 - δ - 2 * η) ≤ hist C π w n {ω | (tauN C.dummy n ω : ℝ) * t ≤ y}ᶜ := by
    rw [measure_compl hBm (measure_ne_top _ _), measure_univ]
    have hle : hist C π w n {ω | (tauN C.dummy n ω : ℝ) * t ≤ y} ≤ ENNReal.ofReal (δ + 2 * η) := htail
    calc ENNReal.ofReal (1 - δ - 2 * η) = ENNReal.ofReal 1 - ENNReal.ofReal (δ + 2 * η) := by
          rw [← ENNReal.ofReal_sub _ (by positivity)]; ring_nf
      _ ≤ 1 - hist C π w n {ω | (tauN C.dummy n ω : ℝ) * t ≤ y} := by
          rw [ENNReal.ofReal_one]; exact tsub_le_tsub_left hle 1
  calc ENNReal.ofReal ((1 - δ - 2 * η) * y)
      ≤ ENNReal.ofReal y * ENNReal.ofReal (1 - δ - 2 * η) := by
        by_cases h0 : 0 ≤ 1 - δ - 2 * η
        · rw [← ENNReal.ofReal_mul hy, mul_comm]
        · have : (1 - δ - 2 * η) * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hy
          rw [ENNReal.ofReal_of_nonpos this]; exact zero_le
    _ ≤ ENNReal.ofReal y * hist C π w n {ω | (tauN C.dummy n ω : ℝ) * t ≤ y}ᶜ := by gcongr
    _ ≤ (∫⁻ ω, (tauN C.dummy n ω : ℝ≥0∞) ∂hist C π w n) * ENNReal.ofReal t := hint
    _ = costN C π w n * ENNReal.ofReal t := rfl

/-! ## 5. The hypotheses are satisfiable: the private-query channel -/

section Satisfiable

open Real

theorem gauss_sq_div (a b y : ℝ) :
    gaussianPDFReal a 1 y ^ 2 / gaussianPDFReal b 1 y
      = Real.exp ((a - b) ^ 2) * gaussianPDFReal (2 * a - b) 1 y := by
  simp only [gaussianPDFReal, NNReal.coe_one]
  have hs : (0 : ℝ) < √(2 * π * 1) := Real.sqrt_pos.mpr (by positivity)
  rw [div_eq_iff (by positivity)]
  have e : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [← Real.exp_nat_mul]; norm_num
  rw [mul_pow, e]
  have key : 2 * (-(y - a) ^ 2 / (2 * 1))
      = (a - b) ^ 2 + -(y - (2 * a - b)) ^ 2 / (2 * 1) + -(y - b) ^ 2 / (2 * 1) := by ring
  rw [key, Real.exp_add, Real.exp_add]
  field_simp

theorem m2_pq (k : ℕ) (h : ℝ) (a b q : Fin (k + 1)) :
    m2 (pqChan k h) a b q
      = ENNReal.ofReal (Real.exp ((pmean k h a q - pmean k h b q) ^ 2)) := by
  unfold m2 obsLawC
  rw [lintegral_withDensity_eq_lintegral_mul _ ((pqChan k h).meas a q).ennreal_ofReal
    (measurable_ratio (pqChan k h) a b q)]
  have hpt : ∀ y, ((fun y => ENNReal.ofReal ((pqChan k h).dens a q y)) * ratio (pqChan k h) a b q) y
      = ENNReal.ofReal (Real.exp ((pmean k h a q - pmean k h b q) ^ 2))
        * ENNReal.ofReal (gaussianPDFReal (2 * pmean k h a q - pmean k h b q) 1 y) := by
    intro y
    simp only [Pi.mul_apply]
    unfold ratio
    rw [← ENNReal.ofReal_mul ((pqChan k h).pos a q y).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    show gaussianPDFReal (pmean k h a q) 1 y
        * (gaussianPDFReal (pmean k h a q) 1 y / gaussianPDFReal (pmean k h b q) 1 y) = _
    rw [← gauss_sq_div, mul_div_assoc', sq]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (measurable_gaussianPDFReal _ 1).ennreal_ofReal,
    lintegral_gaussianPDFReal_eq_one _ one_ne_zero, mul_one]

theorem m2_pq_le (k : ℕ) (h : ℝ) (a b q : Fin (k + 1)) :
    m2 (pqChan k h) a b q ≤ ENNReal.ofReal (Real.exp (h ^ 2)) := by
  rw [m2_pq]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  unfold pmean
  split_ifs <;> nlinarith [sq_nonneg h]

/-- **The χ² star law is not vacuous.**  On the private-query channel with `k ≥ 1` informative
queries and `h ≠ 0`, identification makes the whole world set an obstruction, the Hellinger
tournament is a `δ`-correct policy with measurable output, and `m2 ≤ e^{h²}`. So
`chi_star_tail` applies at the noise world with `t = h²`. -/
theorem chi_star_satisfiable (k : ℕ) (hk : 1 ≤ k) (h : ℝ) (hh : h ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (pol : Policy (Fin (k + 1))) (n : ℕ) (out : Hist (Fin (k + 1)) n → Fin (k + 1)),
      (∀ w, MeasurableSet {ω | out ω ∈ ({w} : Finset (Fin (k + 1)))})
        ∧ (∀ w, hist (pqChan k h) pol w n {ω | out ω ∉ ({w} : Finset (Fin (k + 1)))}
            ≤ ENNReal.ofReal δ)
        ∧ Unsafe (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1)))) Finset.univ
        ∧ (∀ u, u ≠ 0 → ∀ q, q ≠ (pqChan k h).dummy →
            m2 (pqChan k h) 0 u q ≤ ENNReal.ofReal (Real.exp (h ^ 2)))
        ∧ ∀ y, hist (pqChan k h) pol 0 n {ω | (tauN (pqChan k h).dummy n ω : ℝ) * h ^ 2 ≤ y}
            ≤ ENNReal.ofReal (δ + 2 * (((Finset.univ : Finset (Fin (k + 1))).card : ℝ) - 1)
              * Real.sqrt (δ * Real.exp y)) := by
  classical
  have hpos : 0 < 1 - Real.exp (-h ^ 2 / 8) := by
    have : Real.exp (-h ^ 2 / 8) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < h ^ 2 := by positivity
      linarith)
    linarith
  set t : ℝ≥0 := ⟨1 - Real.exp (-h ^ 2 / 8), hpos.le⟩ with ht
  have htpos : 0 < t := by
    show (0 : ℝ) < 1 - Real.exp (-h ^ 2 / 8); exact hpos
  set m : ℕ := ⌈Real.log ((Fintype.card (Fin (k + 1)) : ℝ) / δ) / t⌉₊ with hm
  have hn : Real.log ((Fintype.card (Fin (k + 1)) : ℝ) / δ) / t ≤ m := Nat.le_ceil _
  obtain ⟨herr, -⟩ := CIGAMF.P13.PaperBHellingerTest.hellinger_tournament (pqChan k h)
    (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1)))) t htpos (pq_resolves k h) 0 δ hδ m hn
  have hmeasS : ∀ w, MeasurableSet {ω | CIGAMF.P13.PaperBObstructionLaw.decode
      (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1))))
      (pairSet (CIGAMF.P13.PaperBHellingerTest.kH (pqChan k h)) t)
      (CIGAMF.P13.PaperBHellingerTest.beatH (pqChan k h) t m) 0 ω ∈ ({w} : Finset (Fin (k + 1)))} :=
    fun w => measurableSet_decode_mem _ _ _ (measurableSet_beatH (pqChan k h) t m) 0 _
  have hUns : Unsafe (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1)))) Finset.univ := by
    intro a
    by_cases ha : a = 0
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      rw [Finset.mem_singleton, ha]
      intro h01
      have : ((1 : Fin (k + 1)) : ℕ) = ((0 : Fin (k + 1)) : ℕ) := by rw [h01]
      simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < k + 1)] at this
    · exact ⟨0, Finset.mem_univ _, by rw [Finset.mem_singleton]; exact fun h => ha h⟩
  have hm2 : ∀ u, u ≠ 0 → ∀ q, q ≠ (pqChan k h).dummy →
      m2 (pqChan k h) 0 u q ≤ ENNReal.ofReal (Real.exp (h ^ 2)) :=
    fun u _ q _ => m2_pq_le k h 0 u q
  refine ⟨_, _, _, hmeasS, herr, hUns, hm2, fun y => ?_⟩
  exact chi_star_tail (pqChan k h) _ _ _ (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1))))
    hmeasS δ hδ herr Finset.univ hUns 0 (Finset.mem_univ _) (h ^ 2) y
    (fun u _ hu q hq => hm2 u hu q hq)

end Satisfiable

#print axioms lintegral_prodQ_le
#print axioms hist_density
#print axioms hist_density_set
#print axioms m2_eq_one_add_chi
#print axioms lintegral_Z_exp_le
#print axioms one_alt_bound
#print axioms chi_star_lower
#print axioms chi_star_tail
#print axioms chi_star_expect
#print axioms m2_pq
#print axioms chi_star_satisfiable

end CIGAMF.P13.PaperBChiStar
