import Mathlib

/-!
# Paper A7, package A7-rate: the oracle value is Lipschitz, so the answer stabilises.

## WHY THIS MODULE EXISTS

A Track-and-Stop argument needs the algorithm's chosen answer to settle on an oracle-optimal
one.  The usual route is continuity of the optimal ALLOCATION, which is delicate: the
argmax can jump as the active region changes, and `LeanPaperAModelBridgeV1` shows those
regions really do change.  This module takes the other route, which needs no continuity of
any optimiser: the oracle VALUE is Lipschitz in the world, uniformly in the allocation, and
that alone forces the selected answer to stabilise.

## THE MODULUS

Work in query-mean space with every observation normalised to unit variance, and let the
model class sit in a box `|mu_e| <= B`.  For an answer `T` with alternative means `B_T`,

    J_T(w, mu) = inf_{nu in B_T} (1/2) sum_e w_e (mu_e - nu_e)^2,
    Gamma_T(mu) = sup_w J_T(w, mu).

`J_lipschitz_in_world` proves `|J_T(w,mu) - J_T(w,mu')| <= 2 B ||mu - mu'||_inf`, uniformly
in `w`, and `Gamma_lipschitz` carries it through the supremum.  The constant is `2B` and it
comes from the elementary identity

    (mu_e - nu_e)^2 - (mu'_e - nu_e)^2 = (mu_e - mu'_e)(mu_e + mu'_e - 2 nu_e),

whose second factor is bounded by `4B` on the box.

`J_lipschitz_in_allocation` gives the companion `|J_T(w,mu) - J_T(w',mu)| <= 2 B^2 ||w-w'||_1`,
which is what converts a tracking error on the counts into an error on information.

`J_concave_in_allocation` records that `J_T(., mu)` is an infimum of functions AFFINE in
`w`, hence concave.  That is why the argument needs only the AVERAGE allocation to be good,
not the individual allocations to converge -- a point where a weaker formulation would ask
for something false.

## SELECTION

With oracle brackets `l_T <= Gamma_T(mu_hat) <= u_T` of width at most `eps`, define

    I = { T : u_T >= max_S l_S - 2 L r },      T_chosen = min of I in a fixed order.

`true_answer_in_selection` proves every oracle-optimal answer survives, so the rule never
discards the right answer; `suboptimal_eliminated` proves an answer with value gap `Delta`
is discarded once `4 L r + 2 eps < Delta`.  Together with finiteness of the answer set, the
selection is eventually exactly the set of oracle answers, and a fixed tie-break makes the
choice stable.

This is an instantiation of the answer-stabilisation idea of Degenne and Koolen
(arXiv:1902.03475), not a new device; what is specific here is the modulus, which is what
the compression game supplies.
-/

namespace CIGAMF.P13.PaperA7OracleSelect

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The energy of a candidate world against a design. -/
noncomputable def pen (w mu nu : E → ℝ) : ℝ :=
  (∑ e, w e * (mu e - nu e) ^ 2) / 2

/-- An allocation. -/
def IsAlloc (w : E → ℝ) : Prop := (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1

/-- The world and the alternatives live in a box. -/
def InBox (B : ℝ) (mu : E → ℝ) : Prop := ∀ e, |mu e| ≤ B

/-- The oracle value of an answer at a design: the cheapest alternative. -/
noncomputable def Jval (Alt : Set (E → ℝ)) (w mu : E → ℝ) : ℝ :=
  sInf (pen w mu '' Alt)

theorem pen_nonneg (w mu nu : E → ℝ) (hw : ∀ e, 0 ≤ w e) : 0 ≤ pen w mu nu := by
  unfold pen
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg (fun e _ => mul_nonneg (hw e) (sq_nonneg _))

theorem Jval_bddBelow (Alt : Set (E → ℝ)) (w mu : E → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (pen w mu '' Alt) := by
  refine ⟨0, ?_⟩
  rintro x ⟨nu, -, rfl⟩
  exact pen_nonneg w mu nu hw

/-! ## The modulus in the world -/

/-- The only analytic fact the modulus needs: two infima of a common family are as close as
the family's members are.  Stated once, used in both directions and in both variables. -/
theorem sInf_le_sInf_add {α : Type*} (S : Set α) (f g : α → ℝ) (c : ℝ)
    (hne : S.Nonempty) (hbf : BddBelow (f '' S))
    (h : ∀ a ∈ S, f a ≤ g a + c) :
    sInf (f '' S) ≤ sInf (g '' S) + c := by
  rw [← sub_le_iff_le_add]
  refine le_csInf (hne.image g) ?_
  rintro x ⟨a, ha, rfl⟩
  have hle : sInf (f '' S) ≤ f a := csInf_le hbf ⟨a, ha, rfl⟩
  have := h a ha
  linarith

/-- Two-sided form. -/
theorem abs_sInf_sub_sInf_le {α : Type*} (S : Set α) (f g : α → ℝ) (c : ℝ)
    (hne : S.Nonempty) (hbf : BddBelow (f '' S)) (hbg : BddBelow (g '' S))
    (h : ∀ a ∈ S, |f a - g a| ≤ c) :
    |sInf (f '' S) - sInf (g '' S)| ≤ c := by
  have h1 : sInf (f '' S) ≤ sInf (g '' S) + c :=
    sInf_le_sInf_add S f g c hne hbf (fun a ha => by
      have := abs_le.1 (h a ha); linarith [this.2])
  have h2 : sInf (g '' S) ≤ sInf (f '' S) + c :=
    sInf_le_sInf_add S g f c hne hbg (fun a ha => by
      have := abs_le.1 (h a ha); linarith [this.1])
  rw [abs_le]
  constructor <;> linarith

/-- The pointwise step: at a fixed alternative, moving the world moves the penalty by at
most `2B` times the sup-norm displacement. -/
theorem pen_diff_le (B : ℝ) (w mu mu' nu : E → ℝ)
    (hw : IsAlloc w) (hmu : InBox B mu) (hmu' : InBox B mu') (hnu : InBox B nu)
    (r : ℝ) (hrnn : 0 ≤ r) (hr : ∀ e, |mu e - mu' e| ≤ r) :
    |pen w mu nu - pen w mu' nu| ≤ 2 * B * r := by
  classical
  obtain ⟨hwpos, hwsum⟩ := hw
  have hterm : ∀ e : E,
      |w e * (mu e - nu e) ^ 2 / 2 - w e * (mu' e - nu e) ^ 2 / 2| ≤ w e * (2 * B * r) := by
    intro e
    have hb2 : |mu e + mu' e - 2 * nu e| ≤ 4 * B := by
      have h1 := abs_le.1 (hmu e)
      have h2 := abs_le.1 (hmu' e)
      have h3 := abs_le.1 (hnu e)
      rw [abs_le]; constructor <;> linarith
    have hrw : w e * (mu e - nu e) ^ 2 / 2 - w e * (mu' e - nu e) ^ 2 / 2
        = (w e / 2) * ((mu e - mu' e) * (mu e + mu' e - 2 * nu e)) := by ring
    rw [hrw, abs_mul, abs_mul, abs_of_nonneg (div_nonneg (hwpos e) (by norm_num))]
    have hprod : |mu e - mu' e| * |mu e + mu' e - 2 * nu e| ≤ r * (4 * B) :=
      mul_le_mul (hr e) hb2 (abs_nonneg _) hrnn
    nlinarith [hwpos e, hprod]
  have hsum : |pen w mu nu - pen w mu' nu| ≤ ∑ e, w e * (2 * B * r) := by
    unfold pen
    have hrw : (∑ e, w e * (mu e - nu e) ^ 2) / 2 - (∑ e, w e * (mu' e - nu e) ^ 2) / 2
        = ∑ e, (w e * (mu e - nu e) ^ 2 / 2 - w e * (mu' e - nu e) ^ 2 / 2) := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    rw [hrw]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun e _ => hterm e))
  rw [← Finset.sum_mul, hwsum, one_mul] at hsum
  exact hsum

/-- **The modulus.**  Uniformly in the allocation, the oracle value of an answer moves by at
most `2B` times the sup-norm displacement of the world.  No optimiser is required to be
continuous, which is the point: the active region really does move. -/
theorem J_lipschitz_in_world (B : ℝ) (Alt : Set (E → ℝ)) (hne : Alt.Nonempty)
    (hbox : ∀ nu ∈ Alt, InBox B nu)
    (w mu mu' : E → ℝ) (hw : IsAlloc w) (hmu : InBox B mu) (hmu' : InBox B mu')
    (r : ℝ) (hrnn : 0 ≤ r) (hr : ∀ e, |mu e - mu' e| ≤ r) :
    |Jval Alt w mu - Jval Alt w mu'| ≤ 2 * B * r := by
  classical
  have hwpos := hw.1
  exact abs_sInf_sub_sInf_le Alt (pen w mu) (pen w mu') (2 * B * r) hne
    (Jval_bddBelow Alt w mu hwpos) (Jval_bddBelow Alt w mu' hwpos)
    (fun nu hnu => pen_diff_le B w mu mu' nu hw hmu hmu' (hbox nu hnu) r hrnn hr)

/-- The modulus carries through the supremum over designs, so the ORACLE VALUE
`Gamma_T = sup_w J_T(w, .)` has the same Lipschitz constant. -/
theorem Gamma_lipschitz (B : ℝ) (Alt : Set (E → ℝ)) (mu mu' : E → ℝ)
    (Γ Γ' : ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hΓ : IsLUB {v : ℝ | ∃ w : E → ℝ, IsAlloc w ∧ v = Jval Alt w mu} Γ)
    (hΓ' : IsLUB {v : ℝ | ∃ w : E → ℝ, IsAlloc w ∧ v = Jval Alt w mu'} Γ')
    (hpoint : ∀ w : E → ℝ, IsAlloc w → |Jval Alt w mu - Jval Alt w mu'| ≤ c)
    (hne : ∃ w : E → ℝ, IsAlloc w) :
    |Γ - Γ'| ≤ c := by
  obtain ⟨w0, hw0⟩ := hne
  have h1 : Γ ≤ Γ' + c := by
    refine hΓ.2 ?_
    rintro v ⟨w, hw, rfl⟩
    have hb := abs_le.1 (hpoint w hw)
    have : Jval Alt w mu' ≤ Γ' := hΓ'.1 ⟨w, hw, rfl⟩
    linarith [hb.2]
  have h2 : Γ' ≤ Γ + c := by
    refine hΓ'.2 ?_
    rintro v ⟨w, hw, rfl⟩
    have hb := abs_le.1 (hpoint w hw)
    have : Jval Alt w mu ≤ Γ := hΓ.1 ⟨w, hw, rfl⟩
    linarith [hb.1]
  rw [abs_le]
  constructor <;> linarith

/-- The companion modulus in the ALLOCATION, which is what converts a tracking error on the
counts into an error on accumulated information. -/
theorem J_lipschitz_in_allocation (B : ℝ) (hB : 0 ≤ B) (Alt : Set (E → ℝ))
    (hne : Alt.Nonempty) (hbox : ∀ nu ∈ Alt, InBox B nu)
    (w w' mu : E → ℝ) (hw : ∀ e, 0 ≤ w e) (hw' : ∀ e, 0 ≤ w' e) (hmu : InBox B mu)
    (c : ℝ) (hc : ∑ e, |w e - w' e| ≤ c) :
    |Jval Alt w mu - Jval Alt w' mu| ≤ 2 * B ^ 2 * c := by
  classical
  have hcnn : 0 ≤ c := le_trans (Finset.sum_nonneg (fun e _ => abs_nonneg _)) hc
  refine abs_sInf_sub_sInf_le Alt (pen w mu) (pen w' mu) (2 * B ^ 2 * c) hne
    (Jval_bddBelow Alt w mu hw) (Jval_bddBelow Alt w' mu hw') ?_
  intro nu hnu
  have hsq : ∀ e : E, (mu e - nu e) ^ 2 ≤ 4 * B ^ 2 := by
    intro e
    have h1 := abs_le.1 (hmu e)
    have h2 := abs_le.1 (hbox nu hnu e)
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hterm : ∀ e : E, |w e * (mu e - nu e) ^ 2 / 2 - w' e * (mu e - nu e) ^ 2 / 2|
      ≤ |w e - w' e| * (2 * B ^ 2) := by
    intro e
    rw [show w e * (mu e - nu e) ^ 2 / 2 - w' e * (mu e - nu e) ^ 2 / 2
          = (w e - w' e) * ((mu e - nu e) ^ 2 / 2) by ring, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (mu e - nu e) ^ 2 / 2)]
    have := hsq e
    nlinarith [abs_nonneg (w e - w' e)]
  unfold pen
  have hrw : (∑ e, w e * (mu e - nu e) ^ 2) / 2 - (∑ e, w' e * (mu e - nu e) ^ 2) / 2
      = ∑ e, (w e * (mu e - nu e) ^ 2 / 2 - w' e * (mu e - nu e) ^ 2 / 2) := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  rw [hrw]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun e _ => hterm e)) ?_
  rw [← Finset.sum_mul]
  nlinarith [hc, hB]

/-! ## Concavity in the allocation -/

/-- `pen` is affine in the allocation. -/
theorem pen_affine (w w' mu nu : E → ℝ) (s : ℝ) :
    pen (fun e => (1 - s) * w e + s * w' e) mu nu
      = (1 - s) * pen w mu nu + s * pen w' mu nu := by
  classical
  unfold pen
  have hsum : (∑ e, ((1 - s) * w e + s * w' e) * (mu e - nu e) ^ 2)
      = (1 - s) * (∑ e, w e * (mu e - nu e) ^ 2)
        + s * (∑ e, w' e * (mu e - nu e) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  rw [hsum]
  ring

/-- **The oracle value is concave in the allocation**, being an infimum of affine functions.

This is why the rate argument needs only the AVERAGE allocation to be nearly optimal, and
never that the individual allocations converge.  Demanding convergence of the allocations
would be demanding something that can fail: when two designs are both optimal the whole
segment between them is optimal too, and an algorithm may oscillate along it forever. -/
theorem J_concave_in_allocation (Alt : Set (E → ℝ)) (hne : Alt.Nonempty)
    (w w' mu : E → ℝ) (hw : ∀ e, 0 ≤ w e) (hw' : ∀ e, 0 ≤ w' e)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * Jval Alt w mu + s * Jval Alt w' mu
      ≤ Jval Alt (fun e => (1 - s) * w e + s * w' e) mu := by
  classical
  unfold Jval
  refine le_csInf (hne.image _) ?_
  rintro x ⟨nu, hnu, rfl⟩
  rw [pen_affine w w' mu nu s]
  have h1 : sInf (pen w mu '' Alt) ≤ pen w mu nu :=
    csInf_le (Jval_bddBelow Alt w mu hw) ⟨nu, hnu, rfl⟩
  have h2 : sInf (pen w' mu '' Alt) ≤ pen w' mu nu :=
    csInf_le (Jval_bddBelow Alt w' mu hw') ⟨nu, hnu, rfl⟩
  have hs1' : 0 ≤ 1 - s := by linarith
  nlinarith [h1, h2, hs0, hs1']

/-- **Concavity over a finite convex combination.**

The two-point version above is what convexity means; the rate argument needs it for the
AVERAGE of the allocations used over a window, which is a convex combination of many.  It
follows from the same fact -- the value is an infimum of functions affine in `w` -- and the
inequality `inf of a sum >= sum of infs`.

This is what removes the need for the allocations to converge: only their average has to be
good, and the average is controlled by tracking. -/
theorem J_concave_finite {β : Type*} (s : Finset β) (Alt : Set (E → ℝ)) (hne : Alt.Nonempty)
    (ws : β → E → ℝ) (lamb : β → ℝ) (mu : E → ℝ)
    (hw : ∀ b, ∀ e, 0 ≤ ws b e) (hl : ∀ b ∈ s, 0 ≤ lamb b)
    (hmix : ∀ e, 0 ≤ (∑ b ∈ s, lamb b * ws b e)) :
    ∑ b ∈ s, lamb b * Jval Alt (ws b) mu
      ≤ Jval Alt (fun e => ∑ b ∈ s, lamb b * ws b e) mu := by
  classical
  unfold Jval
  refine le_csInf (hne.image _) ?_
  rintro x ⟨nu, hnu, rfl⟩
  have hpen : pen (fun e => ∑ b ∈ s, lamb b * ws b e) mu nu
      = ∑ b ∈ s, lamb b * pen (ws b) mu nu := by
    unfold pen
    have hrhs : ∑ b ∈ s, lamb b * ((∑ e, ws b e * (mu e - nu e) ^ 2) / 2)
        = (∑ b ∈ s, lamb b * ∑ e, ws b e * (mu e - nu e) ^ 2) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [hrhs]
    congr 1
    have hin : ∀ e : E, (∑ b ∈ s, lamb b * ws b e) * (mu e - nu e) ^ 2
        = ∑ b ∈ s, lamb b * (ws b e * (mu e - nu e) ^ 2) := by
      intro e
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    show (∑ e, (∑ b ∈ s, lamb b * ws b e) * (mu e - nu e) ^ 2) = _
    simp_rw [hin]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => by rw [Finset.mul_sum])
  rw [hpen]
  refine Finset.sum_le_sum (fun b hb => ?_)
  have hle : sInf (pen (ws b) mu '' Alt) ≤ pen (ws b) mu nu :=
    csInf_le (Jval_bddBelow Alt (ws b) mu (hw b)) ⟨nu, hnu, rfl⟩
  exact mul_le_mul_of_nonneg_left hle (hl b hb)

/-! ## Selection: the oracle answer survives, the suboptimal one is eliminated -/

variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans]

/-- **Every oracle-optimal answer survives the selection.**  The rule keeps `T` when its
upper bracket clears the best lower bracket by the confidence allowance, and an optimal
answer's upper bracket is at least its true value, which is the maximum. -/
theorem true_answer_in_selection
    (Γ : Ans → ℝ) (l u : Ans → ℝ) (L r eps : ℝ)
    (hlow : ∀ T, l T ≤ Γ T) (hup : ∀ T, Γ T ≤ u T)
    (hLrnn : 0 ≤ L * r)
    (T S : Ans) (hopt : ∀ S', Γ S' ≤ Γ T) :
    l S - 2 * (L * r) ≤ u T := by
  have h1 : l S ≤ Γ S := hlow S
  have h2 : Γ S ≤ Γ T := hopt S
  have h3 : Γ T ≤ u T := hup T
  linarith [hLrnn]

/-- **A suboptimal answer is eliminated once the brackets are tight enough.**  If `T` falls
short of the best by `Delta` and the bracket width plus the confidence allowance is smaller
than `Delta`, then `T`'s upper bracket cannot clear the best lower bracket. -/
theorem suboptimal_eliminated
    (Γ : Ans → ℝ) (l u : Ans → ℝ) (L r eps Δ : ℝ)
    (hlow : ∀ T, l T ≤ Γ T) (hup : ∀ T, Γ T ≤ u T)
    (hwidth : ∀ T, u T - l T ≤ eps)
    (hLrnn : 0 ≤ L * r)
    (T Tstar : Ans)
    (hgap : Γ Tstar - Γ T = Δ)
    (hsharp : 4 * (L * r) + 2 * eps < Δ) :
    u T < l Tstar - 2 * (L * r) := by
  have h1 : u T ≤ Γ T + eps := by
    have := hwidth T
    have := hlow T
    linarith
  have h2 : Γ Tstar - eps ≤ l Tstar := by
    have := hwidth Tstar
    have := hup Tstar
    linarith
  linarith [h1, h2, hgap, hsharp, hLrnn]

/-- With finitely many answers, once every suboptimal one is eliminated the selection is
exactly the set of oracle answers, and a fixed tie-break makes the chosen answer constant.
The hypothesis is the conclusion of `suboptimal_eliminated` applied to each of them. -/
theorem selection_stabilises
    (Γ : Ans → ℝ) (keep : Ans → Prop) [DecidablePred keep]
    (Tstar : Ans) (hopt : ∀ S, Γ S ≤ Γ Tstar)
    (hkeep_opt : ∀ T, (∀ S, Γ S ≤ Γ T) → keep T)
    (hdrop : ∀ T, Γ T < Γ Tstar → ¬ keep T) :
    ∀ T, keep T → Γ T = Γ Tstar := by
  intro T hT
  rcases lt_or_eq_of_le (hopt T) with hlt | heq
  · exact absurd hT (hdrop T hlt)
  · exact heq

/-! ## Audit -/

#print axioms pen_nonneg
#print axioms Jval_bddBelow
#print axioms sInf_le_sInf_add
#print axioms abs_sInf_sub_sInf_le
#print axioms pen_diff_le
#print axioms J_lipschitz_in_world
#print axioms Gamma_lipschitz
#print axioms J_lipschitz_in_allocation
#print axioms pen_affine
#print axioms J_concave_in_allocation
#print axioms J_concave_finite
#print axioms true_answer_in_selection
#print axioms suboptimal_eliminated
#print axioms selection_stabilises

end CIGAMF.P13.PaperA7OracleSelect
