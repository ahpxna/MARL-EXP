import «LeanUnifiedSupportExchangeV1»

/-!
# A conditional span bound for ADDITIVE residuals

The mathematical inequalities below are retained. This audit corrects their scope;
it adds no theorem and makes no new compile claim.

Let s_j = osc_X Q_j and c_j = osc_K Q_j. Under the stated full-span additivity
hypothesis, the omitted-component model satisfies
  D_K(S) - D_K(T) <= (1/2) sum_{j in T \ S} (s_j + c_j).
Thus any kappa >= (s_j+c_j)/2 on T is a valid additive-model bound.

LIMITATION: this does NOT close the useful computable-margin problem. For a genuine
Top-C margin, rho + s_j <= s_i for i in T and j outside T. Nonnegative spans and
  2 delta + 2 kappa <= rho,  (s_i+c_i)/2 <= kappa
force 2 delta + c_i + s_j <= 0. Hence delta=0, c_i=0, s_j=0. If both T and its
complement are nonempty, all support spans vanish (c_j <= s_j outside T). The resulting
additive support loss is zero. Even K=X can have positive span-bound kappa although
its exact geometry gap is identically zero. This is not a useful nontrivial threshold.

MEASUREMENT MODEL: 2m span VALUES are used; these are not 2m point, noisy, or membership
queries. Each span requires known extrema on the full domain/support, a certified range
oracle, or exhaustive evaluation. Observed sample extrema alone are lower bounds on spans.

LOCAL VS GLOBAL: evaluating k(m-k) single-swap neighbours yields only a local constant.
It does not bound all equal-cardinality competitors without an additional exchange law.
For the additive diagonal-support weights (4,-4,1,1), retaining {0,1} has loss 1;
its four single-swap neighbours have losses 3/2,3/2,5/2,5/2, while {2,3} has loss 0.

MODEL SCOPE: fullProduct_supportOsc_modular proves span additivity for coordinatewise
components on a product domain. It does NOT say the true F equals its additive surrogate.
The corpus productA_compression_loss_formula concerns productA q F. For general F the
actual residual is F - sum_retained Q, which need not equal sum_omitted Q plus a constant.
The present theorems concern the omitted-component model, not that missing actual-F join.

Section 2c remains OPEN as a useful certificate for general support-restricted compression.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.UnifiedGeometryBound

open Finset CIGAMF.V4.SupportGeometry CIGAMF.P13.UnifiedSupportExchange

/-! ### The oscillation is a seminorm on any support -/

section Seminorm

variable {A : Type*} [DecidableEq A]

theorem le_maxOn (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) {a : A} (ha : a ∈ S) :
    f a ≤ maxOn S hS f :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem minOn_le (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) {a : A} (ha : a ∈ S) :
    minOn S hS f ≤ f a :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem maxOn_le_of (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) (b : ℝ)
    (h : ∀ x ∈ S, f x ≤ b) : maxOn S hS f ≤ b := by
  apply (Finset.max'_le_iff _ _).2
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  exact h z hz

theorem le_minOn_of (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) (b : ℝ)
    (h : ∀ x ∈ S, b ≤ f x) : b ≤ minOn S hS f := by
  apply (Finset.le_min'_iff _ _).2
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
  exact h z hz

/-- The maximiser is attained on the support. -/
theorem exists_maxOn (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    ∃ a ∈ S, f a = maxOn S hS f := by
  have hm := Finset.max'_mem (S.image f) (Finset.image_nonempty.mpr hS)
  rcases Finset.mem_image.mp hm with ⟨a, ha, hfa⟩
  exact ⟨a, ha, hfa⟩

/-- ...and so is the minimiser. -/
theorem exists_minOn (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    ∃ a ∈ S, f a = minOn S hS f := by
  have hm := Finset.min'_mem (S.image f) (Finset.image_nonempty.mpr hS)
  rcases Finset.mem_image.mp hm with ⟨a, ha, hfa⟩
  exact ⟨a, ha, hfa⟩

theorem oscOn_nonneg (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) : 0 ≤ oscOn S hS f := by
  obtain ⟨a, ha⟩ := id hS
  have h1 := le_maxOn S hS f ha
  have h2 := minOn_le S hS f ha
  unfold oscOn
  linarith

theorem oscOn_const (S : Finset A) (hS : S.Nonempty) (b : ℝ) :
    oscOn S hS (fun _ => b) = 0 := by
  obtain ⟨a, ha⟩ := id hS
  have h1 : maxOn S hS (fun _ => b) = b :=
    le_antisymm (maxOn_le_of S hS (fun _ => b) b (fun _ _ => le_refl b))
      (le_maxOn S hS (fun _ => b) ha)
  have h2 : minOn S hS (fun _ => b) = b :=
    le_antisymm (minOn_le S hS (fun _ => b) ha)
      (le_minOn_of S hS (fun _ => b) b (fun _ _ => le_refl b))
  unfold oscOn
  rw [h1, h2]
  ring

/-- **Subadditivity.** -/
theorem oscOn_add_le (S : Finset A) (hS : S.Nonempty) (f g : A → ℝ) :
    oscOn S hS (fun x => f x + g x) ≤ oscOn S hS f + oscOn S hS g := by
  have hmax : maxOn S hS (fun x => f x + g x) ≤ maxOn S hS f + maxOn S hS g := by
    apply maxOn_le_of
    intro x hx
    exact add_le_add (le_maxOn S hS f hx) (le_maxOn S hS g hx)
  have hmin : minOn S hS f + minOn S hS g ≤ minOn S hS (fun x => f x + g x) := by
    apply le_minOn_of
    intro x hx
    exact add_le_add (minOn_le S hS f hx) (minOn_le S hS g hx)
  unfold oscOn
  linarith

/-- The oscillation does not see a sign change. -/
theorem oscOn_neg (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    oscOn S hS (fun x => -f x) = oscOn S hS f := by
  have hmax : maxOn S hS (fun x => -f x) = -minOn S hS f := by
    refine le_antisymm (maxOn_le_of S hS _ _ ?_) ?_
    · intro x hx
      have := minOn_le S hS f hx
      linarith
    · obtain ⟨a, ha, hfa⟩ := exists_minOn S hS f
      have := le_maxOn S hS (fun x => -f x) ha
      simp only [hfa] at this
      linarith
  have hmin : minOn S hS (fun x => -f x) = -maxOn S hS f := by
    refine le_antisymm ?_ (le_minOn_of S hS _ _ ?_)
    · obtain ⟨a, ha, hfa⟩ := exists_maxOn S hS f
      have := minOn_le S hS (fun x => -f x) ha
      simp only [hfa] at this
      linarith
    · intro x hx
      have := le_maxOn S hS f hx
      linarith
  unfold oscOn
  rw [hmax, hmin]
  ring

/-- Subadditivity for a difference. -/
theorem oscOn_sub_le (S : Finset A) (hS : S.Nonempty) (f g : A → ℝ) :
    oscOn S hS (fun x => f x - g x) ≤ oscOn S hS f + oscOn S hS g := by
  have h : (fun x => f x - g x) = fun x => f x + (-g x) := by funext x; ring
  rw [h]
  have := oscOn_add_le S hS f (fun x => -g x)
  rw [oscOn_neg S hS g] at this
  exact this

/-- Subadditivity over a finite sum of components. -/
theorem oscOn_sum_le {ι : Type*} [DecidableEq ι] (S : Finset A) (hS : S.Nonempty)
    (Q : ι → A → ℝ) (E : Finset ι) :
    oscOn S hS (fun x => ∑ j ∈ E, Q j x) ≤ ∑ j ∈ E, oscOn S hS (Q j) := by
  classical
  induction E using Finset.induction with
  | empty => simp [oscOn_const S hS 0]
  | insert a E ha ih =>
      have hfun : (fun x => ∑ j ∈ insert a E, Q j x)
          = fun x => Q a x + ∑ j ∈ E, Q j x := by
        funext x
        rw [Finset.sum_insert ha]
      rw [hfun, Finset.sum_insert ha]
      exact le_trans (oscOn_add_le S hS (Q a) (fun x => ∑ j ∈ E, Q j x))
        (by linarith [ih])

end Seminorm

/-! ### The gap, in measured quantities -/

section Bound

variable {A ι : Type*} [DecidableEq A] [Fintype ι] [DecidableEq ι]

/-- The residual of a retained set: the sum of the omitted components. -/
noncomputable def sumOver (Q : ι → A → ℝ) (E : Finset ι) (x : A) : ℝ := ∑ j ∈ E, Q j x

/-- **The gap in measured quantities**, on a domain where the components are modular:
the total full span of the omitted coordinates, less what the support lets their sum
actually reach. -/
theorem geomGap_eq_of_modular
    (K X : Finset A) (hK : K.Nonempty) (hX : X.Nonempty)
    (Q : ι → A → ℝ) (E : Finset ι)
    (hmod : oscOn X hX (sumOver Q E) = ∑ j ∈ E, oscOn X hX (Q j)) :
    geomGap K X hK hX (sumOver Q E)
      = ((∑ j ∈ E, oscOn X hX (Q j)) - oscOn K hK (sumOver Q E)) / 2 := by
  unfold geomGap lossOn
  rw [hmod]
  ring

private theorem compl_sdiff_compl (S T : Finset ι) : Sᶜ \ Tᶜ = T \ S := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_compl, not_not]
  tauto

/-- **The computable bound on the geometry rate.**  Only the coordinates `T` gives up can
pay: the competitor's own coordinates contribute a non-positive amount because a support
span never exceeds a full span. -/
theorem geomGap_diff_le_spans
    (K X : Finset A) (hK : K.Nonempty) (hX : X.Nonempty) (hsub : K ⊆ X)
    (Q : ι → A → ℝ) (T S : Finset ι)
    (hmod : ∀ E : Finset ι, oscOn X hX (sumOver Q E) = ∑ j ∈ E, oscOn X hX (Q j)) :
    geomGap K X hK hX (sumOver Q Sᶜ) - geomGap K X hK hX (sumOver Q Tᶜ)
      ≤ (∑ j ∈ T \ S, (oscOn X hX (Q j) + oscOn K hK (Q j))) / 2 := by
  classical
  set s : ι → ℝ := fun j => oscOn X hX (Q j) with hs
  set c : ι → ℝ := fun j => oscOn K hK (Q j) with hc
  -- each support span is dominated by the corresponding full span
  have hcs : ∀ j, c j ≤ s j := fun j => oscOn_mono K X hK hX hsub (Q j)
  -- the two gaps, in measured quantities
  rw [geomGap_eq_of_modular K X hK hX Q Sᶜ (hmod Sᶜ),
    geomGap_eq_of_modular K X hK hX Q Tᶜ (hmod Tᶜ)]
  -- the span difference telescopes onto the exchanged sets
  have hspan : (∑ j ∈ Sᶜ, s j) - (∑ j ∈ Tᶜ, s j) = (∑ j ∈ T \ S, s j) - (∑ j ∈ S \ T, s j) := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff, compl_sdiff_compl, compl_sdiff_compl]
  -- the residuals differ by the exchanged components
  have hdiff : (fun x => sumOver Q Tᶜ x - sumOver Q Sᶜ x)
      = fun x => sumOver Q (S \ T) x - sumOver Q (T \ S) x := by
    funext x
    unfold sumOver
    have := Finset.sum_sdiff_sub_sum_sdiff (s₁ := Tᶜ) (s₂ := Sᶜ) (f := fun j => Q j x)
    rw [compl_sdiff_compl, compl_sdiff_compl] at this
    linarith [this]
  -- so the support oscillations cannot separate by more than the exchanged spans
  have hosc : oscOn K hK (sumOver Q Tᶜ) - oscOn K hK (sumOver Q Sᶜ)
      ≤ (∑ j ∈ S \ T, c j) + (∑ j ∈ T \ S, c j) := by
    have hsplit : (fun x => sumOver Q Sᶜ x + (sumOver Q Tᶜ x - sumOver Q Sᶜ x))
        = sumOver Q Tᶜ := by funext x; ring
    have hstep : oscOn K hK (sumOver Q Tᶜ)
        ≤ oscOn K hK (sumOver Q Sᶜ)
          + oscOn K hK (fun x => sumOver Q Tᶜ x - sumOver Q Sᶜ x) := by
      have := oscOn_add_le K hK (sumOver Q Sᶜ)
        (fun x => sumOver Q Tᶜ x - sumOver Q Sᶜ x)
      rwa [hsplit] at this
    have hbound : oscOn K hK (fun x => sumOver Q Tᶜ x - sumOver Q Sᶜ x)
        ≤ (∑ j ∈ S \ T, c j) + (∑ j ∈ T \ S, c j) := by
      rw [hdiff]
      refine le_trans (oscOn_sub_le K hK (sumOver Q (S \ T)) (sumOver Q (T \ S))) ?_
      exact add_le_add (oscOn_sum_le K hK Q (S \ T)) (oscOn_sum_le K hK Q (T \ S))
    linarith
  -- the competitor's own coordinates contribute nothing
  have hneg : (∑ j ∈ S \ T, c j) - (∑ j ∈ S \ T, s j) ≤ 0 := by
    have : (∑ j ∈ S \ T, c j) ≤ (∑ j ∈ S \ T, s j) :=
      Finset.sum_le_sum fun j _ => hcs j
    linarith
  have hsum : (∑ j ∈ T \ S, (s j + c j)) = (∑ j ∈ T \ S, s j) + (∑ j ∈ T \ S, c j) := by
    rw [← Finset.sum_add_distrib]
  rw [hsum]
  linarith [hspan, hosc, hneg]

/-- **Any `kappa` dominating the measured half-sum of spans on `T` is a valid geometry
rate.**  Nothing is searched over: the condition is checked coordinate by coordinate. -/
theorem kappa_of_spans
    (K X : Finset A) (hK : K.Nonempty) (hX : X.Nonempty) (hsub : K ⊆ X)
    (Q : ι → A → ℝ) (T S : Finset ι) (kappa : ℝ)
    (hmod : ∀ E : Finset ι, oscOn X hX (sumOver Q E) = ∑ j ∈ E, oscOn X hX (Q j))
    (hkap : ∀ j ∈ T, (oscOn X hX (Q j) + oscOn K hK (Q j)) / 2 ≤ kappa) :
    geomGap K X hK hX (sumOver Q Sᶜ) - geomGap K X hK hX (sumOver Q Tᶜ)
      ≤ kappa * ((T \ S).card : ℝ) := by
  classical
  refine le_trans (geomGap_diff_le_spans K X hK hX hsub Q T S hmod) ?_
  have hterm : ∀ j ∈ T \ S, (oscOn X hX (Q j) + oscOn K hK (Q j)) ≤ 2 * kappa := by
    intro j hj
    have hjT : j ∈ T := (Finset.mem_sdiff.mp hj).1
    have := hkap j hjT
    linarith
  have hbound : (∑ j ∈ T \ S, (oscOn X hX (Q j) + oscOn K hK (Q j)))
      ≤ ∑ _j ∈ T \ S, 2 * kappa := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hbound
  linarith

/-- Conditional threshold for the additive omitted-component model. The name is
preserved for compatibility. Span computation is an oracle/input requirement; with an
actual Top-C margin the sufficient condition forces the degeneracy described above. -/
theorem computable_threshold
    (K X : Finset A) (hK : K.Nonempty) (hX : X.Nonempty) (hsub : K ⊆ X)
    (Q : ι → A → ℝ) (T S : Finset ι) (delta rho kappa : ℝ)
    (hmod : ∀ E : Finset ι, oscOn X hX (sumOver Q E) = ∑ j ∈ E, oscOn X hX (Q j))
    (hkap : ∀ j ∈ T, (oscOn X hX (Q j) + oscOn K hK (Q j)) / 2 ≤ kappa)
    (hfull : 2 * (lossOn X hX (sumOver Q Tᶜ) - lossOn X hX (sumOver Q Sᶜ))
      ≤ (((T \ S).card : ℕ) : ℝ) * (2 * delta - rho))
    (hthr : 2 * delta + 2 * kappa ≤ rho) :
    lossOn K hK (sumOver Q Tᶜ) ≤ lossOn K hK (sumOver Q Sᶜ) := by
  refine support_optimal_of_margin K X hK hX (sumOver Q Tᶜ) (sumOver Q Sᶜ)
    (T \ S).card delta rho kappa hfull ?_ hthr
  exact kappa_of_spans K X hK hX hsub Q T S kappa hmod hkap

end Bound

#print axioms oscOn_add_le
#print axioms oscOn_neg
#print axioms oscOn_sub_le
#print axioms oscOn_sum_le
#print axioms geomGap_eq_of_modular
#print axioms geomGap_diff_le_spans
#print axioms kappa_of_spans
#print axioms computable_threshold

end CIGAMF.P13.UnifiedGeometryBound
