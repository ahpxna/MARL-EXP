import «LeanD6MarginSensitiveExchangeV1»

/-!
# The exchange law on a RESTRICTED SUPPORT, with its geometry term.

## WHY THIS MODULE EXISTS

The D6 exchange theorem bounds `L(T) - L(S)` where the loss is an oscillation over the
FULL product domain.  Compression, however, is only ever required to be good on the set
of inputs that actually occur.  Restricting the oscillation to a support `K` is not a
harmless weakening of the statement: it changes which set is optimal, and it can do so
even when the interaction term `delta_I` -- the whole content of the D6 hypothesis -- is
exactly zero.

The witness at the bottom of this file is three coordinates wide:

    F(x) = 3 x1 - 2 x2 - 2 x3,   X = {0,1}^3,   K = {000, 111}.

`F` is additive, so `delta_I = 0` and every D6 hypothesis holds in its strongest form.
The component spans are `(3,2,2)`, so Top-C at `k = 1` retains coordinate `1`.  On the
full cube that is optimal.  On `K` it is the WORST of the three singletons: its loss is
`2` against `1/2`.  Top-C is wrong, and no amount of interaction control repairs it,
because the failure has nothing to do with interaction.

So the support is an independent variable, and this file supplies the law that carries
it.  Writing `D_K(T) = L_X(T) - L_K(T)` for the loss the support removes,

    L_K(T) - L_K(S) = (L_X(T) - L_X(S)) + (D_K(S) - D_K(T)),

an identity, and therefore -- feeding in ANY full-domain exchange bound --

    2 (L_K(T) - L_K(S))  <=  |T \ S| (2 delta_I - rho) + 2 (D_K(S) - D_K(T)).

The geometry term is not slack.  At the witness the inequality is an EQUALITY, so no
proof can remove the term and keep the conclusion.

## WHAT IS PROVED

* `geomGap_nonneg` -- the support can only help: `D_K >= 0`, from `oscOn_mono`.
* `support_decomposition` -- the identity above, for arbitrary residuals.
* `support_exchange_of_full` -- any full-domain bound transported to the support.
* `support_optimal_of_margin` -- **the threshold**: if the geometry term grows at most
  linearly, `D_K(S) - D_K(T) <= kappa |T \ S|`, then `rho >= 2 delta_I + 2 kappa` forces
  `T` to be optimal on `K`.  At `kappa = 0` this is exactly the D6 threshold, so the law
  degrades to the known one when the support is the whole domain.
* `osc_eq_oscOn_univ` -- the bridge making the full domain a special case of a support,
  so the two statements are about the same object and not merely analogous.
* The witness block: `witness_interaction_zero`, `witness_spans`, the four losses,
  `witness_topC_not_optimal_on_support`, and `witness_exchange_equality`.

## WHAT THIS DOES NOT ESTABLISH

- `kappa` is an INPUT.  Nothing here computes it from the support, and the witness shows
  it cannot be bounded by anything derived from `delta_I` alone: there `delta_I = 0` while
  `kappa = 2`.  Estimating or learning `kappa` from support queries is open, and is the
  point at which this law stops being a bridge and would become a result.
- The threshold is sufficient, not necessary. A failing instance below the threshold
  does not establish that the condition is nonvacuous or sharp. No matching lower
  construction is given here for general `kappa`.
- One reference and one budget.  Nothing is claimed about varying `q` or about `k > 1`.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.UnifiedSupportExchange

open Finset CIGAMF.V4.SupportGeometry

/-! ### Reading an oscillation off an explicit maximiser and minimiser -/

section Helpers

variable {A : Type*} [DecidableEq A]

theorem maxOn_eq_of (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) (a : A)
    (ha : a ∈ S) (hmax : ∀ x ∈ S, f x ≤ f a) : maxOn S hS f = f a := by
  apply le_antisymm
  · apply (Finset.max'_le_iff _ _).2
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact hmax z hz
  · exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem minOn_eq_of (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) (b : A)
    (hb : b ∈ S) (hmin : ∀ x ∈ S, f b ≤ f x) : minOn S hS f = f b := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  · apply (Finset.le_min'_iff _ _).2
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact hmin z hz

/-- The oscillation over a support, read off an explicit maximiser and minimiser. -/
theorem oscOn_eq_sub (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) (a b : A)
    (ha : a ∈ S) (hb : b ∈ S)
    (hmax : ∀ x ∈ S, f x ≤ f a) (hmin : ∀ x ∈ S, f b ≤ f x) :
    oscOn S hS f = f a - f b := by
  unfold oscOn
  rw [maxOn_eq_of S hS f a ha hmax, minOn_eq_of S hS f b hb hmin]

/-- **The full domain is the special case `K = univ`.**  Without this the support law and
the D6 law would be statements about two different objects. -/
theorem osc_eq_oscOn_univ {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : A → ℝ) : osc f = oscOn univ Finset.univ_nonempty f := rfl

end Helpers

/-! ### The law -/

section Law

variable {A : Type*} [DecidableEq A]

/-- Compression loss measured on a support: half the oscillation of the residual. -/
noncomputable def lossOn (S : Finset A) (hS : S.Nonempty) (r : A → ℝ) : ℝ :=
  oscOn S hS r / 2

/-- The loss the support removes.  Non-negative, and generally NOT a function of the
interaction. -/
noncomputable def geomGap (K X : Finset A) (hK : K.Nonempty) (hX : X.Nonempty)
    (r : A → ℝ) : ℝ := lossOn X hX r - lossOn K hK r

/-- **Restricting to a support can only lower the loss.**  This is `oscOn_mono`. -/
theorem geomGap_nonneg (K X : Finset A) (hK : K.Nonempty) (hX : X.Nonempty)
    (hsub : K ⊆ X) (r : A → ℝ) : 0 ≤ geomGap K X hK hX r := by
  have h := oscOn_mono K X hK hX hsub r
  unfold geomGap lossOn
  linarith

/-- **The decomposition identity.**  Everything the support does to a comparison is
carried by the two gap terms; the full-domain difference is untouched. -/
theorem support_decomposition (K X : Finset A) (hK : K.Nonempty) (hX : X.Nonempty)
    (rT rS : A → ℝ) :
    lossOn K hK rT - lossOn K hK rS
      = (lossOn X hX rT - lossOn X hX rS)
        + (geomGap K X hK hX rS - geomGap K X hK hX rT) := by
  unfold geomGap
  ring

/-- **Any full-domain exchange bound, transported to the support.**  The hypothesis is
whatever the unrestricted theory proves; the conclusion pays exactly the geometry term. -/
theorem support_exchange_of_full (K X : Finset A) (hK : K.Nonempty) (hX : X.Nonempty)
    (rT rS : A → ℝ) (bound : ℝ)
    (hfull : 2 * (lossOn X hX rT - lossOn X hX rS) ≤ bound) :
    2 * (lossOn K hK rT - lossOn K hK rS)
      ≤ bound + 2 * (geomGap K X hK hX rS - geomGap K X hK hX rT) := by
  rw [support_decomposition K X hK hX rT rS]
  linarith

/-- **The threshold.**  A margin beating twice the interaction AND twice the geometry rate
makes `T` optimal on the support.  At `kappa = 0` this is the D6 condition unchanged. -/
theorem support_optimal_of_margin (K X : Finset A) (hK : K.Nonempty) (hX : X.Nonempty)
    (rT rS : A → ℝ) (card : ℕ) (delta rho kappa : ℝ)
    (hfull : 2 * (lossOn X hX rT - lossOn X hX rS) ≤ (card : ℝ) * (2 * delta - rho))
    (hkappa : geomGap K X hK hX rS - geomGap K X hK hX rT ≤ kappa * (card : ℝ))
    (hthr : 2 * delta + 2 * kappa ≤ rho) :
    lossOn K hK rT ≤ lossOn K hK rS := by
  have hc : (0 : ℝ) ≤ (card : ℝ) := Nat.cast_nonneg card
  have hstep := support_exchange_of_full K X hK hX rT rS
    ((card : ℝ) * (2 * delta - rho)) hfull
  have hmul : (card : ℝ) * (2 * delta - rho) + 2 * (kappa * (card : ℝ))
      = (card : ℝ) * (2 * delta + 2 * kappa - rho) := by ring
  have hneg : (card : ℝ) * (2 * delta + 2 * kappa - rho) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc (by linarith)
  linarith

end Law

/-! ### The witness: Top-C fails on a support with zero interaction, and the
geometry-corrected bound holds with equality. -/

section Witness

/-- Points of the three-fold binary product domain. -/
abbrev Pt : Type := Fin 3 → Fin 2

/-- The real value of a binary coordinate. -/
def bit (u : Fin 2) : ℝ := if u = 1 then 1 else 0

@[simp] theorem bit_zero : bit 0 = 0 := by simp [bit]
@[simp] theorem bit_one : bit 1 = 1 := by simp [bit]

theorem bit_nonneg (u : Fin 2) : 0 ≤ bit u := by unfold bit; split <;> norm_num
theorem bit_le_one (u : Fin 2) : bit u ≤ 1 := by unfold bit; split <;> norm_num

/-- `F(x) = 3 x1 - 2 x2 - 2 x3`: additive, hence zero interaction. -/
def Fw (x : Pt) : ℝ := 3 * bit (x 0) - 2 * bit (x 1) - 2 * bit (x 2)

/-- The corner-reference product responses of `Fw`: `Q_j(u) = F(e_j u)`. -/
def Qw (j : Fin 3) (u : Fin 2) : ℝ := (if j = 0 then 3 else -2) * bit u

/-- The residual left after retaining the coordinate set `T`. -/
noncomputable def resid (T : Finset (Fin 3)) (x : Pt) : ℝ :=
  Fw x - ∑ j ∈ T, Qw j (x j)

/-- The all-zero point `000`. -/
def p0 : Pt := fun _ => 0

/-- The all-one point `111`. -/
def p1 : Pt := fun _ => 1

/-- `100`, where the residual of `{1}` is largest on the cube. -/
def pA : Pt := ![1, 0, 0]

/-- `001`, where the residual of `{1}` is smallest on the cube. -/
def pB : Pt := ![0, 0, 1]

/-- The diagonal support `K = {000, 111}`. -/
def Kw : Finset Pt := {p0, p1}

theorem Kw_nonempty : Kw.Nonempty := ⟨p0, by simp [Kw]⟩

theorem Kw_sub_univ : Kw ⊆ (univ : Finset Pt) := Finset.subset_univ Kw

/-- **The interaction vanishes identically.**  `Fw` is additive, so every hypothesis of the
D6 exchange theorem holds in its strongest form: `delta_I = 0`. -/
theorem witness_interaction_zero (i : Fin 3) (x c : Pt) :
    CIGAMF.V4.ProductSurrogate.mixedDifference Fw i x c = 0 := by
  unfold CIGAMF.V4.ProductSurrogate.mixedDifference Fw
  fin_cases i <;> simp [Function.update_apply] <;> ring

/-- The component spans are `|C| = (3, 2, 2)`, so Top-C at `k = 1` retains coordinate `0`. -/
theorem witness_spans :
    Qw 0 1 - Qw 0 0 = 3 ∧ Qw 1 1 - Qw 1 0 = -2 ∧ Qw 2 1 - Qw 2 0 = -2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Qw]

/-- The residual retained by `T = {0}` is `-2 x2 - 2 x3`. -/
theorem resid_zero (x : Pt) : resid {0} x = -2 * bit (x 1) - 2 * bit (x 2) := by
  unfold resid Fw
  rw [Finset.sum_singleton]
  simp [Qw]
  ring

/-- The residual retained by `T = {1}` is `3 x1 - 2 x3`. -/
theorem resid_one (x : Pt) : resid {1} x = 3 * bit (x 0) - 2 * bit (x 2) := by
  unfold resid Fw
  rw [Finset.sum_singleton]
  simp [Qw]
  ring

private theorem mem_Kw (x : Pt) (hx : x ∈ Kw) : x = p0 ∨ x = p1 := by
  simpa [Kw] using hx

/-! Each of the four losses below is EVALUATED from `Fw`; none is supplied as data. -/

/-- On the support, retaining coordinate `0` costs `2`. -/
theorem witness_lossK_zero : lossOn Kw Kw_nonempty (resid {0}) = 2 := by
  have h : oscOn Kw Kw_nonempty (resid {0}) = resid {0} p0 - resid {0} p1 := by
    refine oscOn_eq_sub Kw Kw_nonempty (resid {0}) p0 p1 (by simp [Kw]) (by simp [Kw])
      ?_ ?_
    · intro x hx
      rcases mem_Kw x hx with rfl | rfl <;>
        simp [resid_zero, p0, p1] <;> norm_num
    · intro x hx
      rcases mem_Kw x hx with rfl | rfl <;>
        simp [resid_zero, p0, p1] <;> norm_num
  unfold lossOn
  rw [h]
  simp [resid_zero, p0, p1]

/-- On the support, retaining coordinate `1` costs only `1/2`. -/
theorem witness_lossK_one : lossOn Kw Kw_nonempty (resid {1}) = 1 / 2 := by
  have h : oscOn Kw Kw_nonempty (resid {1}) = resid {1} p1 - resid {1} p0 := by
    refine oscOn_eq_sub Kw Kw_nonempty (resid {1}) p1 p0 (by simp [Kw]) (by simp [Kw])
      ?_ ?_
    · intro x hx
      rcases mem_Kw x hx with rfl | rfl <;>
        simp [resid_one, p0, p1] <;> norm_num
    · intro x hx
      rcases mem_Kw x hx with rfl | rfl <;>
        simp [resid_one, p0, p1] <;> norm_num
  unfold lossOn
  rw [h]
  simp [resid_one, p0, p1]
  norm_num

/-- On the FULL cube, retaining coordinate `0` also costs `2`: the support removes nothing. -/
theorem witness_lossX_zero :
    lossOn (univ : Finset Pt) Finset.univ_nonempty (resid {0}) = 2 := by
  have h : oscOn (univ : Finset Pt) Finset.univ_nonempty (resid {0})
      = resid {0} p0 - resid {0} p1 := by
    refine oscOn_eq_sub _ _ (resid {0}) p0 p1 (Finset.mem_univ _) (Finset.mem_univ _)
      ?_ ?_
    · intro x _
      simp only [resid_zero, p0]
      have h1 := bit_nonneg (x 1)
      have h2 := bit_nonneg (x 2)
      simp only [bit_zero]
      linarith
    · intro x _
      simp only [resid_zero, p1]
      have h1 := bit_le_one (x 1)
      have h2 := bit_le_one (x 2)
      simp only [bit_one]
      linarith
  unfold lossOn
  rw [h]
  simp [resid_zero, p0, p1]

/-- On the FULL cube, retaining coordinate `1` costs `5/2`: MORE than on the support.
This is the whole point -- the two domains rank the two answers in opposite orders. -/
theorem witness_lossX_one :
    lossOn (univ : Finset Pt) Finset.univ_nonempty (resid {1}) = 5 / 2 := by
  have h : oscOn (univ : Finset Pt) Finset.univ_nonempty (resid {1})
      = resid {1} pA - resid {1} pB := by
    refine oscOn_eq_sub _ _ (resid {1}) pA pB (Finset.mem_univ _) (Finset.mem_univ _)
      ?_ ?_
    · intro x _
      simp only [resid_one, pA, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      have h0 := bit_le_one (x 0)
      have h2 := bit_nonneg (x 2)
      simp only [bit_zero, bit_one]
      linarith
    · intro x _
      simp only [resid_one, pB, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      have h0 := bit_nonneg (x 0)
      have h2 := bit_le_one (x 2)
      simp only [bit_zero, bit_one]
      linarith
  unfold lossOn
  rw [h]
  simp only [resid_one, pA, pB, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, bit_zero, bit_one]
  norm_num

/-- The support removes nothing from the Top-C answer. -/
theorem witness_gap_zero :
    geomGap Kw univ Kw_nonempty Finset.univ_nonempty (resid {0}) = 0 := by
  unfold geomGap
  rw [witness_lossX_zero, witness_lossK_zero]
  norm_num

/-- ...but it removes `2` from the competitor.  That asymmetry IS the failure. -/
theorem witness_gap_one :
    geomGap Kw univ Kw_nonempty Finset.univ_nonempty (resid {1}) = 2 := by
  unfold geomGap
  rw [witness_lossX_one, witness_lossK_one]
  norm_num

/-- **Top-C is not optimal on the support**, although the interaction is identically zero
and the D6 margin hypothesis holds. -/
theorem witness_topC_not_optimal_on_support :
    lossOn Kw Kw_nonempty (resid {1}) < lossOn Kw Kw_nonempty (resid {0}) := by
  rw [witness_lossK_zero, witness_lossK_one]
  norm_num

/-- ...while on the full cube the same Top-C answer IS optimal between these two. -/
theorem witness_topC_optimal_on_cube :
    lossOn (univ : Finset Pt) Finset.univ_nonempty (resid {0})
      < lossOn (univ : Finset Pt) Finset.univ_nonempty (resid {1}) := by
  rw [witness_lossX_zero, witness_lossX_one]
  norm_num

/-- The doubled support regret of the Top-C set against the better competitor is `3`. -/
theorem witness_doubled_support_regret :
    2 * (lossOn Kw Kw_nonempty (resid {0}) - lossOn Kw Kw_nonempty (resid {1})) = 3 := by
  rw [witness_lossK_zero, witness_lossK_one]
  norm_num

/-- **The plain full-domain bound is FALSE on the support.**  With `delta_I = 0` and margin
`rho = 1` it asserts the doubled regret is at most `-1`, and the true value is `3`. -/
theorem witness_plain_bound_fails :
    ¬ (2 * (lossOn Kw Kw_nonempty (resid {0}) - lossOn Kw Kw_nonempty (resid {1}))
        ≤ (1 : ℝ) * (2 * 0 - 1)) := by
  rw [witness_doubled_support_regret]
  norm_num

/-- **The geometry-corrected bound holds with EQUALITY.**  Both sides are `3`, so the
geometry term is not slack: a proof that dropped it would be proving something false. -/
theorem witness_exchange_equality :
    2 * (lossOn Kw Kw_nonempty (resid {0}) - lossOn Kw Kw_nonempty (resid {1}))
      = (1 : ℝ) * (2 * 0 - 1)
        + 2 * (geomGap Kw univ Kw_nonempty Finset.univ_nonempty (resid {1})
             - geomGap Kw univ Kw_nonempty Finset.univ_nonempty (resid {0})) := by
  rw [witness_gap_zero, witness_gap_one, witness_doubled_support_regret]
  norm_num

/-- **The geometry rate the witness demands is `kappa = 2`, with `delta_I = 0`.**  So the
threshold of `support_optimal_of_margin` asks for `rho >= 4`, while the actual margin is
`rho = 1`. The computed losses independently establish failure; being below a sufficient
threshold does not by itself imply failure. This instance rules out a bound proportional
to interaction, or one vanishing at zero interaction; by itself it does not rule out
EVERY possible function of interaction. -/
theorem witness_kappa_is_two :
    geomGap Kw univ Kw_nonempty Finset.univ_nonempty (resid {1})
      - geomGap Kw univ Kw_nonempty Finset.univ_nonempty (resid {0}) = 2 * (1 : ℝ) := by
  rw [witness_gap_zero, witness_gap_one]
  norm_num

end Witness

#print axioms geomGap_nonneg
#print axioms support_decomposition
#print axioms support_exchange_of_full
#print axioms support_optimal_of_margin
#print axioms osc_eq_oscOn_univ
#print axioms witness_interaction_zero
#print axioms witness_lossK_zero
#print axioms witness_lossK_one
#print axioms witness_lossX_zero
#print axioms witness_lossX_one
#print axioms witness_gap_zero
#print axioms witness_gap_one
#print axioms witness_plain_bound_fails
#print axioms witness_kappa_is_two
#print axioms witness_topC_not_optimal_on_support
#print axioms witness_exchange_equality

end CIGAMF.P13.UnifiedSupportExchange
