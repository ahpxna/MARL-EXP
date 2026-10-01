import «LeanPaperBRateKLV1»

/-!
# Paper B: the two worlds behind `hdiff`, and why the old form of it was empty

`LeanPaperBRateKLV1.kl_rate_of_mixture` carried the density-difference identification as a
hypothesis

    hdiff : forall y, p y - q y = iterDiff q shifts y,

with `q` the mixture appearing on BOTH sides, and asked separately for `hp : 0 <= p`.  That
pair of hypotheses is not satisfiable.  With one Gaussian component and one nonzero shift,
`q + symDiff q s` is negative far enough into the tail the shift moves mass away from,
because the tail ratio `q(y+s)/q(y)` is unbounded.  `self_difference_not_a_density` proves
it.  So the old composition was vacuous exactly where it mattered --- at `h != 0` --- and
the `h^{2r}` rate it reported said nothing.

The repair is to stop asking one density to be its own difference, and to build the two
worlds the difference actually comes from.  Write `v z` for the signed shift sum of a sign
pattern `z` and `parity z` for the product of its signs.  Set

    Q(y) = 2^{-r} sum_z        M(y - v z),
    P(y) = 2^{-r} sum_z (1 + parity z) M(y - v z).

`P` keeps the even patterns at double weight and drops the odd ones, `Q` is the flat
average.  Both are non-negative combinations of translates of the same base `M`, both have
the same total mass, and

    P - Q = 2^{-r} sum_z parity z * M(y - v z) = iterDiff M (shifts),

which is `worlds_diff` --- an identity, not an assumption.  `hdiff` is therefore discharged
rather than carried, and it is discharged for the pair that the construction produces.

Uniformity over the query class is then immediate and is the point: the bound produced by
`hellinger_rate_bound` is `h^{2r} (1/r)^{2r} * klConst`, and `klConst` depends only on
`(sigma, R, h_0, r)`.  The query enters only through `w`, `cs` and `a`, all of which have
been quantified away inside the box constraints.  `kl_uniform_over_queries` states it in
that form: one constant, every admissible query.

Two integrability side conditions on the constructed pair are carried into the KL
statement.  `chi2_uniform` needs none and is proved outright; the KL statement additionally
needs `p log (p/q)` to be integrable, which is a property of the pair, not a modelling
assumption.
-/

namespace CIGAMF.P13.PaperBWorlds

open MeasureTheory
open CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBKL

/-! ## The old `hdiff` is unsatisfiable -/

/-- **A density cannot be its own first difference plus itself.**  With one Gaussian
component and shift `s > 0`, any `p` obeying `p - q = symDiff q s` with `q = gkern` is
negative at `y = -(s^2 + 4 sigma^2)/(2 s)`.  This is `kl_rate_of_mixture` at `n = 1`,
`r = 1`, `w = 1`, `cs = 0`, `h * a 0 = s`: its hypotheses are contradictory there. -/
theorem self_difference_not_a_density (σ s : ℝ) (hσ : 0 < σ) (hs : 0 < s)
    (p : ℝ → ℝ) (hp : ∀ y, 0 ≤ p y)
    (hdiff : ∀ y, p y - gkern σ y = iterDiff (gkern σ) [s] y) : False := by
  obtain ⟨T, hTpos, hTs⟩ : ∃ T : ℝ, 0 < T ∧ 2 * T * s - s ^ 2 = 4 * σ ^ 2 := by
    refine ⟨(s ^ 2 + 4 * σ ^ 2) / (2 * s), by positivity, ?_⟩
    field_simp <;> ring
  have heven : ∀ x : ℝ, gkern σ (-x) = gkern σ x := by
    intro x; unfold gkern; ring_nf
  -- the value at `-T`
  have hval : p (-T) - gkern σ T = (gkern σ (T + s) - gkern σ (T - s)) / 2 := by
    have h := hdiff (-T)
    simp only [iterDiff_cons, iterDiff_nil, symDiff] at h
    rw [show -T - s = -(T + s) from by ring, show -T + s = -(T - s) from by ring,
      heven (T + s), heven (T - s), heven T] at h
    exact h
  -- the tail ratio at the chosen point is exactly `exp 2`
  have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity
  have hkey : -((T - s) ^ 2) / (2 * σ ^ 2) = 2 + -(T ^ 2) / (2 * σ ^ 2) := by
    have hne : (2 * σ ^ 2) ≠ 0 := ne_of_gt hσ2
    rw [div_eq_iff hne, add_mul, div_mul_cancel₀ _ hne]
    linear_combination hTs
  have hratio : gkern σ (T - s) = Real.exp 2 * gkern σ T := by
    unfold gkern
    rw [← Real.exp_add]
    exact congrArg Real.exp hkey
  have hmono : gkern σ (T + s) ≤ gkern σ T := by
    unfold gkern
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_div_iff_of_pos_right hσ2]
    nlinarith
  have hgpos : 0 < gkern σ T := gkern_pos σ T
  have hexp : (3 : ℝ) < Real.exp 2 := by
    have := Real.add_one_lt_exp (x := 2) (by norm_num)
    linarith
  have hneg : p (-T) < 0 := by
    rw [show p (-T) = gkern σ T + (gkern σ (T + s) - gkern σ (T - s)) / 2 from by
      linarith [hval]]
    rw [hratio]
    nlinarith [hmono, hgpos, hexp]
  exact absurd (hp (-T)) (not_le.2 hneg)

/-! ## The two worlds -/

variable {r : ℕ}

/-- The signed shift attached to a sign pattern. -/
noncomputable def shiftOf (b : Fin r → ℝ) (z : Fin r → Bool) : ℝ := ∑ i, b i * sgnB (z i)

/-- The parity of a sign pattern, as `+-1`. -/
noncomputable def parity (z : Fin r → Bool) : ℝ := ∏ i, sgnB (z i)

/-- The flat world: the base averaged over all sign patterns. -/
noncomputable def worldQ (M : ℝ → ℝ) (b : Fin r → ℝ) (y : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ r * ∑ z : Fin r → Bool, M (y - shiftOf b z)

/-- The tilted world: the even patterns at double weight, the odd ones dropped. -/
noncomputable def worldP (M : ℝ → ℝ) (b : Fin r → ℝ) (y : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ r * ∑ z : Fin r → Bool, (1 + parity z) * M (y - shiftOf b z)

theorem sgnB_abs (b : Bool) : |sgnB b| = 1 := by
  cases b <;> simp [sgnB]

theorem parity_abs (z : Fin r → Bool) : |parity z| = 1 := by
  unfold parity
  rw [Finset.abs_prod]
  simp [sgnB_abs]

theorem parity_nonneg_shift (z : Fin r → Bool) : 0 ≤ 1 + parity z := by
  have h := abs_le.mp (le_of_eq (parity_abs z))
  linarith [h.1]

theorem abs_shiftOf_le (b : Fin r → ℝ) (z : Fin r → Bool) :
    |shiftOf b z| ≤ ∑ i, |b i| := by
  unfold shiftOf
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [abs_mul, sgnB_abs, mul_one]

/-- **The identity `hdiff` asked for, now proved.**  The two worlds differ by exactly the
iterated symmetric difference of the base. -/
theorem worlds_diff (M : ℝ → ℝ) (b : Fin r → ℝ) (y : ℝ) :
    worldP M b y - worldQ M b y = iterDiff M (List.ofFn b) y := by
  unfold worldP worldQ parity shiftOf
  rw [iterDiff_eq_signSum r M b y, ← mul_sub, ← Finset.sum_sub_distrib]
  refine congrArg _ (Finset.sum_congr rfl (fun z _ => ?_))
  ring

theorem worldQ_nonneg (M : ℝ → ℝ) (hM : ∀ y, 0 ≤ M y) (b : Fin r → ℝ) (y : ℝ) :
    0 ≤ worldQ M b y := by
  unfold worldQ
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun z _ => hM _))

theorem worldP_nonneg (M : ℝ → ℝ) (hM : ∀ y, 0 ≤ M y) (b : Fin r → ℝ) (y : ℝ) :
    0 ≤ worldP M b y := by
  unfold worldP
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun z _ => mul_nonneg (parity_nonneg_shift z) (hM _)))

/-- **The flat world inherits any floor the base has on the shift window.** -/
theorem worldQ_floor (M L : ℝ → ℝ) (b : Fin r → ℝ) (h₀ : ℝ) (hb : ∑ i, |b i| ≤ h₀)
    (hfloor : ∀ v y, |v| ≤ h₀ → L y ≤ M (y - v)) (y : ℝ) : L y ≤ worldQ M b y := by
  classical
  have hterm : ∀ z ∈ (Finset.univ : Finset (Fin r → Bool)), L y ≤ M (y - shiftOf b z) :=
    fun z _ => hfloor _ y (le_trans (abs_shiftOf_le b z) hb)
  have hsum : ((Finset.univ : Finset (Fin r → Bool)).card : ℝ) * L y
      ≤ ∑ z : Fin r → Bool, M (y - shiftOf b z) := by
    have := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have hcard : ((Finset.univ : Finset (Fin r → Bool)).card : ℝ) = 2 ^ r := by
    simp [Finset.card_univ]
  rw [hcard] at hsum
  unfold worldQ
  have hpow : (0 : ℝ) < (2 : ℝ)⁻¹ ^ r := by positivity
  have := mul_le_mul_of_nonneg_left hsum hpow.le
  calc L y = (2 : ℝ)⁻¹ ^ r * (2 ^ r * L y) := by
        rw [← mul_assoc, ← mul_pow]; norm_num
    _ ≤ (2 : ℝ)⁻¹ ^ r * ∑ z : Fin r → Bool, M (y - shiftOf b z) := this

/-! ## Mass: the two worlds are normalised by the same constant -/

theorem integral_symDiff_zero (f : ℝ → ℝ) (hf : Integrable f volume) (b : ℝ) :
    ∫ y, symDiff f b y = 0 := by
  unfold symDiff
  have h1 : Integrable (fun y => f (y - b)) volume := hf.comp_sub_right b
  have h2 : Integrable (fun y => f (y + b)) volume := hf.comp_add_right b
  rw [integral_div, integral_sub h1 h2, integral_sub_right_eq_self f b,
    integral_add_right_eq_self f b, sub_self, zero_div]

theorem iterDiff_integrable (f : ℝ → ℝ) (hf : Integrable f volume) :
    ∀ bs : List ℝ, Integrable (iterDiff f bs) volume := by
  intro bs
  induction bs with
  | nil => exact hf
  | cons b bs ih =>
    have h : Integrable
        (fun y => (iterDiff f bs (y - b) - iterDiff f bs (y + b)) / 2) volume :=
      ((ih.comp_sub_right b).sub (ih.comp_add_right b)).div_const 2
    exact h

theorem integral_iterDiff_zero (f : ℝ → ℝ) (hf : Integrable f volume)
    (b : ℝ) (bs : List ℝ) : ∫ y, iterDiff f (b :: bs) y = 0 := by
  simp only [iterDiff_cons]
  exact integral_symDiff_zero _ (iterDiff_integrable f hf bs) b

/-! ## The Gaussian mixture instantiation -/

/-- The base mixture. -/
noncomputable def mixDens (σ : ℝ) (n : ℕ) (w cs : Fin n → ℝ) (y : ℝ) : ℝ :=
  ∑ j, w j * gkern σ (y - cs j)

theorem mixDens_nonneg (σ : ℝ) (n : ℕ) (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (y : ℝ) :
    0 ≤ mixDens σ n w cs y :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (gkern_pos σ _).le)

theorem mixDens_continuous (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (w cs : Fin n → ℝ) :
    Continuous (mixDens σ n w cs) := by
  unfold mixDens gkern
  refine continuous_finsetSum _ (fun j _ => ?_)
  exact continuous_const.mul (Real.continuous_exp.comp (by continuity))

/-- **The base's floor on the shift window.**  A translate by at most `h_0` of a mixture
with centres in `[-R, R]` is still above the envelope at `R + h_0`. -/
theorem mixDens_floor (σ R h₀ : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀)
    (n : ℕ) (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (hcs : ∀ j, |cs j| ≤ R) (v y : ℝ) (hv : |v| ≤ h₀) :
    envLo σ (R + h₀) y ≤ mixDens σ n w cs (y - v) := by
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      w j * envLo σ (R + h₀) y ≤ w j * gkern σ (y - v - cs j) := by
    intro j _
    refine mul_le_mul_of_nonneg_left ?_ (hw j)
    have hc : |v + cs j| ≤ R + h₀ := by
      have h1 : |v + cs j| ≤ |v| + |cs j| := abs_add_le v (cs j)
      linarith [hv, hcs j]
    have := gaussian_lower_envelope σ (R + h₀) y (v + cs j) hσ hc
    rw [show y - (v + cs j) = y - v - cs j from by ring] at this
    exact this
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, hw1, one_mul] at hsum
  exact hsum

/-- The query-independent constant. -/
noncomputable def klConst (σ R h₀ : ℝ) (r : ℕ) : ℝ :=
  ∫ y, envUp σ (R + h₀) r y ^ 2 / envLo σ (R + h₀) y

/-- **The chi-square bound, uniform over the query class.**  No integrability hypothesis:
`hellinger_rate_bound` carries its own. -/
theorem chi2_uniform (σ R h₀ h : ℝ) (r n : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hh₀ : 0 ≤ h₀) (hh : 0 ≤ h) (a : Fin r → ℝ) (ha : ∑ i, |a i| ≤ 1)
    (hscale : ∑ i, |h * a i| ≤ h₀)
    (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hcs : ∀ j, |cs j| ≤ R) :
    ∫ y, (worldP (mixDens σ n w cs) (fun i => h * a i) y
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / envLo σ (R + h₀) y
      ≤ h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2 * klConst σ R h₀ r := by
  have hRh : 0 ≤ R + h₀ := by linarith
  refine hellinger_rate_bound σ (R + h₀) h r hr hσ hRh hh a ha _ _ (fun y => ?_)
    (fun y => le_rfl)
  rw [worlds_diff]
  exact iterDiff_mixture_envelope σ R h₀ hσ hR hh₀ r n w hw (le_of_eq hw1) cs hcs
    (fun i => h * a i) hscale y

/-- **The divergence bound, uniform over the query class.**  The right-hand side does not
mention `w`, `cs` or `a`: one constant serves every admissible query. -/
theorem kl_uniform_over_queries (σ R h₀ h : ℝ) (r n : ℕ) (hr : 0 < r) (hσ : 0 < σ)
    (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀) (hh : 0 ≤ h) (a : Fin r → ℝ) (ha : ∑ i, |a i| ≤ 1)
    (hscale : ∑ i, |h * a i| ≤ h₀)
    (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hcs : ∀ j, |cs j| ≤ R)
    (hkl : Integrable (fun y =>
        worldP (mixDens σ n w cs) (fun i => h * a i) y
          * Real.log (worldP (mixDens σ n w cs) (fun i => h * a i) y
              / worldQ (mixDens σ n w cs) (fun i => h * a i) y)) volume)
    (henv : Integrable (fun y =>
        (worldP (mixDens σ n w cs) (fun i => h * a i) y
          - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / envLo σ (R + h₀) y) volume)
    (hint : Integrable (fun y =>
        worldP (mixDens σ n w cs) (fun i => h * a i) y
          - worldQ (mixDens σ n w cs) (fun i => h * a i) y) volume)
    (hmass : ∫ y, (worldP (mixDens σ n w cs) (fun i => h * a i) y
          - worldQ (mixDens σ n w cs) (fun i => h * a i) y) = 0) :
    ∫ y, worldP (mixDens σ n w cs) (fun i => h * a i) y
        * Real.log (worldP (mixDens σ n w cs) (fun i => h * a i) y
            / worldQ (mixDens σ n w cs) (fun i => h * a i) y)
      ≤ h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2 * klConst σ R h₀ r := by
  have hfloor : ∀ y, envLo σ (R + h₀) y
      ≤ worldQ (mixDens σ n w cs) (fun i => h * a i) y := by
    intro y
    refine worldQ_floor _ _ _ h₀ hscale (fun v y' hv => ?_) y
    exact mixDens_floor σ R h₀ hσ hR hh₀ n w cs hw hw1 hcs v y' hv
  have hQpos : ∀ y, 0 < worldQ (mixDens σ n w cs) (fun i => h * a i) y :=
    fun y => lt_of_lt_of_le (envLo_pos σ (R + h₀) y) (hfloor y)
  have hkle := kl_le_envelope volume _ _ (envLo σ (R + h₀))
    (worldP_nonneg _ (mixDens_nonneg σ n w cs hw) _) hQpos
    (fun y => envLo_pos σ (R + h₀) y) hfloor hkl henv hint hmass
  exact le_trans hkle
    (chi2_uniform σ R h₀ h r n hr hσ hR hh₀ hh a ha hscale w cs hw hw1 hcs)

/-! ## Audit -/

#print axioms self_difference_not_a_density
#print axioms worlds_diff
#print axioms worldP_nonneg
#print axioms worldQ_floor
#print axioms integral_symDiff_zero
#print axioms iterDiff_integrable
#print axioms integral_iterDiff_zero
#print axioms mixDens_floor
#print axioms chi2_uniform
#print axioms kl_uniform_over_queries

end CIGAMF.P13.PaperBWorlds
