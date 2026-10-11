import Mathlib
import «LeanPaperAModelBridgeV1»

/-!
# Paper A, package A-separation: the frozen proxy misprices AFTER optimising the design.

## WHY THIS MODULE EXISTS

It is easy to show a surrogate is wrong at a FIXED allocation: pick a bad allocation.  The
claim worth making is that the surrogate is wrong after the experimenter has already chosen
the best allocation for it, i.e. after the `sup_w`.  This module proves that, in both
directions, on two explicit four-action worlds.

## THE GAME

Two relations `A` and `B`, four cells each, so eight cells in all:

    index 0 1 2 3 = A1 A2 A3 A4,    index 4 5 6 7 = B1 B2 B3 B4.

Retaining one relation and discarding the other costs half the range of the discarded
table, so the compression decision compares `range(A)` with `range(B)`.  Each query observes
one cell with known variance, all queries cost one, and an allocation is a probability
vector on the eight cells.  The information a design `w` gives against an alternative
`lambda` is the energy

    E_w(lambda) = (1/2) sum_e w_e (lambda_e - theta_e)^2 / var_e,

so the value of a design is `inf` over the alternative set, and the value of the game is the
`sup` over allocations.  TRUE uses the alternatives of the actual decision, a comparison of
two ranges.  PROXY freezes the current argmax and argmin of each table and uses the
resulting linear contrast.  Both games run over the SAME allocations and the SAME class of
worlds; only the alternative set differs.

## THE TWO SEPARATIONS

`family_low_ratio_le` :  Gamma_true / Gamma_proxy <= 64 / M.
`family_high_ratio_ge`:  Gamma_true / Gamma_proxy >= M / 96.

Each is assembled from two halves proved separately:

  an upper bound on one game valid for EVERY allocation, so it survives the `sup`, exhibited
  by naming an alternative and computing its energy;

  a lower bound on the other game at ONE named allocation, so it is a valid `sup`, proved
  against EVERY member of that alternative set by Cauchy-Schwarz.

That asymmetry is what brackets the `sup_w`, and it is why neither half may be replaced by a
numerical optimum.

## HOW THE STATEMENTS ARE PHRASED

The worlds are not written as literal vectors.  Each theorem takes the world, the variances
and the allocation as arbitrary functions constrained by hypotheses on the cells it actually
uses.  That is stronger than fixing one vector -- the bounds hold for every world meeting
the stated conditions -- and it keeps the proofs about the geometry rather than about
evaluating a literal.

## REALIZABILITY

`additive_response_shift` shows that for an additive `F(a,b) = QA(a) + QB(b)` over a uniform
reference, the product response at each coordinate reproduces that coordinate's table plus a
constant, and `rng_shift_invariant` shows a constant does not move a range.  So every table
below is the response table of a genuine `F`, and centring the tables -- which is what makes
them valid zero-mean responses -- changes nothing the decision can see.  The fourth action
is what lets the alternatives below preserve each table's total.

## SCOPE, STATED HONESTLY

`M` is a known variance of the observation model, so this is a separation within a
heteroscedastic family.  It is NOT a statement about a fixed homogeneous variance, and the
ratios are for `epsilon = 0`, at an instance whose decision is unique.  Removing the
dependence on heteroscedasticity needs the `r`-pair variant, which is not proved here.
-/

namespace CIGAMF.P13.PaperASeparation

open scoped BigOperators

/-! ## The game -/

/-- An allocation: a probability vector on the eight cells. -/
def IsAlloc (w : Fin 8 → ℝ) : Prop := (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1

/-- The information a design gives against a candidate world. -/
noncomputable def energy (w var θ lam : Fin 8 → ℝ) : ℝ :=
  (∑ e, w e * (lam e - θ e) ^ 2 / var e) / 2

/-- The range of four numbers. -/
noncomputable def rng (a b c d : ℝ) : ℝ :=
  max (max a b) (max c d) - min (min a b) (min c d)

noncomputable def rangeAof (lam : Fin 8 → ℝ) : ℝ := rng (lam 0) (lam 1) (lam 2) (lam 3)
noncomputable def rangeBof (lam : Fin 8 → ℝ) : ℝ := rng (lam 4) (lam 5) (lam 6) (lam 7)

/-- The TRUE alternative set of "retain `A`": a world in which discarding `B` is no longer
at least as good, i.e. `B`'s range has caught `A`'s. -/
def TrueAlt (lam : Fin 8 → ℝ) : Prop := rangeAof lam ≤ rangeBof lam

/-- The PROXY alternative set: the frozen extrema of the current world are kept, so the
condition is a single linear contrast on four cells. -/
def ProxyAlt (lam : Fin 8 → ℝ) : Prop := (lam 1 - lam 0) - (lam 5 - lam 4) ≤ 0

/-! ## The model class: centered tables, where the energy IS the information

`rng_shift_invariant` says a constant does not move a range, so the LOSS cannot see it.  The
INFORMATION can.  For an additive world the response carries the other arm's mean,

    R_A(a) = Q_A(a) + mean(Q_B),

so moving from `theta` to `lambda` changes the response by `Delta Q_A(a) + Delta mean(Q_B)`,
and that trailing term enters the Gaussian KL.  Two arbitrary tables are therefore NOT
interchangeable as far as information is concerned, even when their ranges agree.

`CIGAMF.P13.PaperAModelBridge.centered_additive_response` removes the term on the centered
class, and `gaussian_kl_eq_sq_gap` identifies the per-cell divergence with the squared gap
there.  So the game below is taken over alternatives in that class, and the `energy` it
optimises is the information the queries carry -- not a stand-in for it.

The witnesses move two cells of one arm by equal and opposite amounts, so they preserve each
arm's total and stay in the class.  That is what the fourth action is for. -/

/-- The centered class: each arm's table sums to zero. -/
def InClass (lam : Fin 8 → ℝ) : Prop :=
  lam 0 + lam 1 + lam 2 + lam 3 = 0 ∧ lam 4 + lam 5 + lam 6 + lam 7 = 0

/-- A shift of two cells of one arm by equal and opposite amounts stays in the class. -/
theorem inClass_of_opposite_shift (θ lam : Fin 8 → ℝ) (hθ : InClass θ) (d : ℝ)
    (i j : Fin 8) (hij : i ≠ j)
    (hsame : (i.val < 4 ∧ j.val < 4) ∨ (4 ≤ i.val ∧ 4 ≤ j.val))
    (hdi : lam i - θ i = d) (hdj : lam j - θ j = -d)
    (hrest : ∀ e : Fin 8, e ≠ i → e ≠ j → lam e = θ e) :
    InClass lam := by
  obtain ⟨hA, hB⟩ := hθ
  constructor <;> [skip; skip] <;>
  · rcases hsame with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;>
    · fin_cases i <;> fin_cases j <;>
      simp_all <;>
      first
        | linarith
        | (rw [hrest 0 (by decide) (by decide), hrest 1 (by decide) (by decide),
               hrest 2 (by decide) (by decide), hrest 3 (by decide) (by decide)] <;>
           linarith)
        | (rw [hrest 4 (by decide) (by decide), hrest 5 (by decide) (by decide),
               hrest 6 (by decide) (by decide), hrest 7 (by decide) (by decide)] <;>
           linarith)

/-! ## Centring is a change of coordinates, not a change of problem

The tables in the paper are written in raw units and they are NOT centered.  The model class
is the centered one.  So a theorem may not name the raw cell values AND assert `InClass` of
the same world: those two hypotheses cannot both hold, and any theorem carrying both is
empty.  An earlier version of the A-low wrapper did exactly that -- it asked for
`InClass theta` alongside `theta 0 = 0, theta 1 = 1, theta 2 = 1/2, theta 3 = 1/2`, whose
sum is `2`, not `0`.  This section is the repair, and the theorems below name the CENTERED
cells, so the hypotheses are satisfiable; `low_world_hypotheses_consistent` says so in one
statement.

`shiftArms` subtracts a constant from each arm separately.  The lemmas that follow say the
decision problem is invariant under it: each arm's range is unchanged, so `TrueAlt` is
unchanged; the frozen contrast is unchanged, so `ProxyAlt` is unchanged; and -- because BOTH
the world and the candidate are shifted by the SAME constants -- the energy is unchanged.
Centring each arm by its own mean lands in the class.

Two warnings the statements enforce.  The shift must be applied to `theta` and `lambda`
together: `energy_shiftArms` takes both.  And it must be the SAME constant for both: centring
each alternative by its own mean is a different map and does not preserve energy. -/

/-- Subtract `cA` from arm `A` and `cB` from arm `B`. -/
noncomputable def shiftArms (cA cB : ℝ) (x : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun e => if e.val < 4 then x e - cA else x e - cB

theorem shiftArms_A (cA cB : ℝ) (x : Fin 8 → ℝ) (e : Fin 8) (he : e.val < 4) :
    shiftArms cA cB x e = x e - cA := by simp [shiftArms, he]

theorem shiftArms_B (cA cB : ℝ) (x : Fin 8 → ℝ) (e : Fin 8) (he : ¬ e.val < 4) :
    shiftArms cA cB x e = x e - cB := by simp [shiftArms, he]

/-- A common shift moves neither the maximum nor the minimum of four numbers, so it does not
move their difference. -/
theorem rng_sub_const (a b c d k : ℝ) :
    rng (a - k) (b - k) (c - k) (d - k) = rng a b c d := by
  have hmax : ∀ x y : ℝ, max (x - k) (y - k) = max x y - k := by
    intro x y
    rcases le_total x y with h | h
    · rw [max_eq_right h, max_eq_right (by linarith : x - k ≤ y - k)]
    · rw [max_eq_left h, max_eq_left (by linarith : y - k ≤ x - k)]
  have hmin : ∀ x y : ℝ, min (x - k) (y - k) = min x y - k := by
    intro x y
    rcases le_total x y with h | h
    · rw [min_eq_left h, min_eq_left (by linarith : x - k ≤ y - k)]
    · rw [min_eq_right h, min_eq_right (by linarith : y - k ≤ x - k)]
  unfold rng
  rw [hmax a b, hmax c d, hmax, hmin a b, hmin c d, hmin]
  ring

theorem rangeAof_shiftArms (cA cB : ℝ) (x : Fin 8 → ℝ) :
    rangeAof (shiftArms cA cB x) = rangeAof x := by
  unfold rangeAof
  rw [shiftArms_A cA cB x 0 (by decide), shiftArms_A cA cB x 1 (by decide),
      shiftArms_A cA cB x 2 (by decide), shiftArms_A cA cB x 3 (by decide)]
  exact rng_sub_const _ _ _ _ cA

theorem rangeBof_shiftArms (cA cB : ℝ) (x : Fin 8 → ℝ) :
    rangeBof (shiftArms cA cB x) = rangeBof x := by
  unfold rangeBof
  rw [shiftArms_B cA cB x 4 (by decide), shiftArms_B cA cB x 5 (by decide),
      shiftArms_B cA cB x 6 (by decide), shiftArms_B cA cB x 7 (by decide)]
  exact rng_sub_const _ _ _ _ cB

theorem trueAlt_shiftArms (cA cB : ℝ) (x : Fin 8 → ℝ) :
    TrueAlt (shiftArms cA cB x) ↔ TrueAlt x := by
  unfold TrueAlt
  rw [rangeAof_shiftArms, rangeBof_shiftArms]

theorem proxyAlt_shiftArms (cA cB : ℝ) (x : Fin 8 → ℝ) :
    ProxyAlt (shiftArms cA cB x) ↔ ProxyAlt x := by
  unfold ProxyAlt
  rw [shiftArms_A cA cB x 0 (by decide), shiftArms_A cA cB x 1 (by decide),
      shiftArms_B cA cB x 4 (by decide), shiftArms_B cA cB x 5 (by decide)]
  constructor <;> intro h <;> linarith

/-- **The energy is blind to a common shift of the world and the candidate.** -/
theorem energy_shiftArms (cA cB : ℝ) (w var θ lam : Fin 8 → ℝ) :
    energy w var (shiftArms cA cB θ) (shiftArms cA cB lam) = energy w var θ lam := by
  unfold energy
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  have hd : shiftArms cA cB lam e - shiftArms cA cB θ e = lam e - θ e := by
    by_cases h : e.val < 4
    · rw [shiftArms_A cA cB lam e h, shiftArms_A cA cB θ e h]; ring
    · rw [shiftArms_B cA cB lam e h, shiftArms_B cA cB θ e h]; ring
  rw [hd]

/-- **Centring each arm by its own mean lands in the class.** -/
theorem inClass_center (x : Fin 8 → ℝ) :
    InClass (shiftArms ((x 0 + x 1 + x 2 + x 3) / 4) ((x 4 + x 5 + x 6 + x 7) / 4) x) := by
  constructor
  · rw [shiftArms_A _ _ x 0 (by decide), shiftArms_A _ _ x 1 (by decide),
        shiftArms_A _ _ x 2 (by decide), shiftArms_A _ _ x 3 (by decide)]
    ring
  · rw [shiftArms_B _ _ x 4 (by decide), shiftArms_B _ _ x 5 (by decide),
        shiftArms_B _ _ x 6 (by decide), shiftArms_B _ _ x 7 (by decide)]
    ring

/-! ### The two worlds, written in centered coordinates

`thetaLowRaw` and `thetaHighRaw` are the tables as the paper prints them.  `thetaLowC` and
`thetaHighC` are the same tables with each arm's mean removed, and the two bridge theorems
below PROVE that identification instead of asserting it. -/

noncomputable def thetaLowRaw : Fin 8 → ℝ := fun e =>
  if e = 0 then 0 else if e = 1 then 1 else if e = 2 then 1/2 else if e = 3 then 1/2
  else if e = 4 then 0 else if e = 5 then 3/4 else 1/2

noncomputable def thetaLowC : Fin 8 → ℝ := fun e =>
  if e = 0 then -(1/2) else if e = 1 then 1/2 else if e = 2 then 0 else if e = 3 then 0
  else if e = 4 then -(7/16) else if e = 5 then 5/16 else 1/16

noncomputable def thetaHighRaw : Fin 8 → ℝ := fun e =>
  if e = 0 then 0 else if e = 1 then 1 else if e = 2 then 3/4 else if e = 3 then 1/2
  else if e = 4 then 0 else if e = 5 then 1/2 else 1/4

noncomputable def thetaHighC : Fin 8 → ℝ := fun e =>
  if e = 0 then -(9/16) else if e = 1 then 7/16 else if e = 2 then 3/16
  else if e = 3 then -(1/16) else if e = 4 then -(1/4) else if e = 5 then 1/4 else 0

@[simp] theorem thetaLowRaw_0 : thetaLowRaw 0 = 0 := by simp [thetaLowRaw]
@[simp] theorem thetaLowRaw_1 : thetaLowRaw 1 = 1 := by simp [thetaLowRaw]
@[simp] theorem thetaLowRaw_2 : thetaLowRaw 2 = 1/2 := by simp [thetaLowRaw]
@[simp] theorem thetaLowRaw_3 : thetaLowRaw 3 = 1/2 := by simp [thetaLowRaw]
@[simp] theorem thetaLowRaw_4 : thetaLowRaw 4 = 0 := by simp [thetaLowRaw]
@[simp] theorem thetaLowRaw_5 : thetaLowRaw 5 = 3/4 := by simp [thetaLowRaw]
@[simp] theorem thetaLowRaw_6 : thetaLowRaw 6 = 1/2 := by simp [thetaLowRaw]
@[simp] theorem thetaLowRaw_7 : thetaLowRaw 7 = 1/2 := by simp [thetaLowRaw]
@[simp] theorem thetaLowC_0 : thetaLowC 0 = -(1/2) := by simp [thetaLowC]
@[simp] theorem thetaLowC_1 : thetaLowC 1 = 1/2 := by simp [thetaLowC]
@[simp] theorem thetaLowC_2 : thetaLowC 2 = 0 := by simp [thetaLowC]
@[simp] theorem thetaLowC_3 : thetaLowC 3 = 0 := by simp [thetaLowC]
@[simp] theorem thetaLowC_4 : thetaLowC 4 = -(7/16) := by simp [thetaLowC]
@[simp] theorem thetaLowC_5 : thetaLowC 5 = 5/16 := by simp [thetaLowC]
@[simp] theorem thetaLowC_6 : thetaLowC 6 = 1/16 := by simp [thetaLowC]
@[simp] theorem thetaLowC_7 : thetaLowC 7 = 1/16 := by simp [thetaLowC]
@[simp] theorem thetaHighRaw_0 : thetaHighRaw 0 = 0 := by simp [thetaHighRaw]
@[simp] theorem thetaHighRaw_1 : thetaHighRaw 1 = 1 := by simp [thetaHighRaw]
@[simp] theorem thetaHighRaw_2 : thetaHighRaw 2 = 3/4 := by simp [thetaHighRaw]
@[simp] theorem thetaHighRaw_3 : thetaHighRaw 3 = 1/2 := by simp [thetaHighRaw]
@[simp] theorem thetaHighRaw_4 : thetaHighRaw 4 = 0 := by simp [thetaHighRaw]
@[simp] theorem thetaHighRaw_5 : thetaHighRaw 5 = 1/2 := by simp [thetaHighRaw]
@[simp] theorem thetaHighRaw_6 : thetaHighRaw 6 = 1/4 := by simp [thetaHighRaw]
@[simp] theorem thetaHighRaw_7 : thetaHighRaw 7 = 1/4 := by simp [thetaHighRaw]
@[simp] theorem thetaHighC_0 : thetaHighC 0 = -(9/16) := by simp [thetaHighC]
@[simp] theorem thetaHighC_1 : thetaHighC 1 = 7/16 := by simp [thetaHighC]
@[simp] theorem thetaHighC_2 : thetaHighC 2 = 3/16 := by simp [thetaHighC]
@[simp] theorem thetaHighC_3 : thetaHighC 3 = -(1/16) := by simp [thetaHighC]
@[simp] theorem thetaHighC_4 : thetaHighC 4 = -(1/4) := by simp [thetaHighC]
@[simp] theorem thetaHighC_5 : thetaHighC 5 = 1/4 := by simp [thetaHighC]
@[simp] theorem thetaHighC_6 : thetaHighC 6 = 0 := by simp [thetaHighC]
@[simp] theorem thetaHighC_7 : thetaHighC 7 = 0 := by simp [thetaHighC]

theorem thetaLowRaw_meanA :
    (thetaLowRaw 0 + thetaLowRaw 1 + thetaLowRaw 2 + thetaLowRaw 3) / 4 = 1/2 := by norm_num
theorem thetaLowRaw_meanB :
    (thetaLowRaw 4 + thetaLowRaw 5 + thetaLowRaw 6 + thetaLowRaw 7) / 4 = 7/16 := by norm_num
theorem thetaHighRaw_meanA :
    (thetaHighRaw 0 + thetaHighRaw 1 + thetaHighRaw 2 + thetaHighRaw 3) / 4 = 9/16 := by
  norm_num
theorem thetaHighRaw_meanB :
    (thetaHighRaw 4 + thetaHighRaw 5 + thetaHighRaw 6 + thetaHighRaw 7) / 4 = 1/4 := by
  norm_num

/-- **The A-low centered table IS the paper's A-low table, centered.** -/
theorem thetaLowC_eq_centered_raw :
    thetaLowC = shiftArms
      ((thetaLowRaw 0 + thetaLowRaw 1 + thetaLowRaw 2 + thetaLowRaw 3) / 4)
      ((thetaLowRaw 4 + thetaLowRaw 5 + thetaLowRaw 6 + thetaLowRaw 7) / 4) thetaLowRaw := by
  rw [thetaLowRaw_meanA, thetaLowRaw_meanB]
  funext e
  have h : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 := by revert e; decide
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [shiftArms_A _ _ _ 0 (by decide)]; norm_num
  · rw [shiftArms_A _ _ _ 1 (by decide)]; norm_num
  · rw [shiftArms_A _ _ _ 2 (by decide)]; norm_num
  · rw [shiftArms_A _ _ _ 3 (by decide)]; norm_num
  · rw [shiftArms_B _ _ _ 4 (by decide)]; norm_num
  · rw [shiftArms_B _ _ _ 5 (by decide)]; norm_num
  · rw [shiftArms_B _ _ _ 6 (by decide)]; norm_num
  · rw [shiftArms_B _ _ _ 7 (by decide)]; norm_num

/-- **The A-high centered table IS the paper's A-high table, centered.** -/
theorem thetaHighC_eq_centered_raw :
    thetaHighC = shiftArms
      ((thetaHighRaw 0 + thetaHighRaw 1 + thetaHighRaw 2 + thetaHighRaw 3) / 4)
      ((thetaHighRaw 4 + thetaHighRaw 5 + thetaHighRaw 6 + thetaHighRaw 7) / 4) thetaHighRaw := by
  rw [thetaHighRaw_meanA, thetaHighRaw_meanB]
  funext e
  have h : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 := by revert e; decide
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [shiftArms_A _ _ _ 0 (by decide)]; norm_num
  · rw [shiftArms_A _ _ _ 1 (by decide)]; norm_num
  · rw [shiftArms_A _ _ _ 2 (by decide)]; norm_num
  · rw [shiftArms_A _ _ _ 3 (by decide)]; norm_num
  · rw [shiftArms_B _ _ _ 4 (by decide)]; norm_num
  · rw [shiftArms_B _ _ _ 5 (by decide)]; norm_num
  · rw [shiftArms_B _ _ _ 6 (by decide)]; norm_num
  · rw [shiftArms_B _ _ _ 7 (by decide)]; norm_num

theorem thetaLowC_inClass : InClass thetaLowC := by constructor <;> norm_num

theorem thetaHighC_inClass : InClass thetaHighC := by constructor <;> norm_num

/-- **The A-low hypotheses are jointly satisfiable.**  This is the statement whose failure
made the earlier wrapper empty: the named cells and `InClass` hold at one and the same
world, and the frozen contrast really does sit at `1/4` there. -/
theorem low_world_hypotheses_consistent :
    InClass thetaLowC ∧
    thetaLowC 0 = -(1/2) ∧ thetaLowC 1 = 1/2 ∧ thetaLowC 2 = 0 ∧ thetaLowC 3 = 0 ∧
    thetaLowC 4 = -(7/16) ∧ thetaLowC 5 = 5/16 ∧ thetaLowC 6 = 1/16 ∧
    thetaLowC 7 = 1/16 ∧
    (thetaLowC 1 - thetaLowC 0) - (thetaLowC 5 - thetaLowC 4) = 1/4 :=
  ⟨thetaLowC_inClass, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The A-high hypotheses are jointly satisfiable**, including `InClass` of the world,
which the earlier wrapper did not even require.  The `A2 - A0` spread is what the lower
bound actually uses, and it is shift-invariant, unlike the two cell values it replaces. -/
theorem high_world_hypotheses_consistent :
    InClass thetaHighC ∧ thetaHighC 2 - thetaHighC 0 = 3/4 ∧ rangeBof thetaHighC = 1/2 := by
  refine ⟨thetaHighC_inClass, by norm_num, ?_⟩
  unfold rangeBof rng
  norm_num

/-! ## Two Cauchy-Schwarz inequalities, proved by hand

Mathlib's finite-sum Cauchy-Schwarz is not available under the name used elsewhere in this
corpus, and only the two- and four-term cases are needed. -/

theorem cs_two (a b : ℝ) : (|a| + |b|) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

theorem cs_four (a b c e : ℝ) :
    (|a| + |b| + |c| + |e|) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| - |c|), sq_nonneg (|a| - |e|),
             sq_nonneg (|b| - |c|), sq_nonneg (|b| - |e|), sq_nonneg (|c| - |e|),
             sq_abs a, sq_abs b, sq_abs c, sq_abs e]

/-! ## Expanding the energy over the eight cells -/

theorem energy_expand (w var θ lam : Fin 8 → ℝ) :
    energy w var θ lam
      = (w 0 * (lam 0 - θ 0) ^ 2 / var 0 + w 1 * (lam 1 - θ 1) ^ 2 / var 1
          + w 2 * (lam 2 - θ 2) ^ 2 / var 2 + w 3 * (lam 3 - θ 3) ^ 2 / var 3
          + w 4 * (lam 4 - θ 4) ^ 2 / var 4 + w 5 * (lam 5 - θ 5) ^ 2 / var 5
          + w 6 * (lam 6 - θ 6) ^ 2 / var 6 + w 7 * (lam 7 - θ 7) ^ 2 / var 7) / 2 := by
  unfold energy
  rw [Fin.sum_univ_eight]

/-- Every term of the energy is nonnegative when the allocation and the variances are. -/
theorem energy_term_nonneg (w var θ lam : Fin 8 → ℝ) (e : Fin 8)
    (hw : 0 ≤ w e) (hv : 0 < var e) : 0 ≤ w e * (lam e - θ e) ^ 2 / var e := by
  apply div_nonneg _ (le_of_lt hv)
  exact mul_nonneg hw (sq_nonneg _)

/-! ## Family A-low: the proxy prices the information too HIGH

    A = (0, 1, 1/2, 1/2),   B = (0, 3/4, 1/2, 1/2),   variance `M` on B3 and B4.

Freezing the extrema forces four unit-variance cells to close a gap of `1/4`.  The true
alternative may instead lift `B3` until `B`'s range catches `A`'s, which costs only
`O(1/M)`. -/

/-- **The exhibited alternative is a genuine TRUE alternative.**  Moving `B3` up and `B4`
down by `1/2` keeps `B`'s total fixed -- so the table is still a valid response -- and
brings `B`'s range up to `A`'s. -/
theorem altLow_is_true_alt (lam : Fin 8 → ℝ)
    (h0 : lam 0 = 0) (h1 : lam 1 = 1) (h2 : lam 2 = 1/2) (h3 : lam 3 = 1/2)
    (h4 : lam 4 = 0) (h5 : lam 5 = 3/4) (h6 : lam 6 = 1) (h7 : lam 7 = 0) :
    TrueAlt lam := by
  unfold TrueAlt rangeAof rangeBof rng
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  norm_num

/-- **Upper half of A-low, valid for EVERY allocation.**  However the experimenter
allocates, the same cheap alternative is available, so the true game is worth at most
`1/(8M)`.  Only the two `M`-variance cells move, each by `1/2`. -/
theorem low_true_le (M : ℝ) (hM : 0 < M) (w var θ lam : Fin 8 → ℝ)
    (hw : IsAlloc w) (hvpos : ∀ e, 0 < var e)
    (hv6 : var 6 = M) (hv7 : var 7 = M)
    (hd6 : lam 6 - θ 6 = 1/2) (hd7 : lam 7 - θ 7 = -(1/2))
    (hrest : ∀ e : Fin 8, e ≠ 6 → e ≠ 7 → lam e = θ e) :
    energy w var θ lam ≤ 1 / (8 * M) := by
  obtain ⟨hpos, hsum⟩ := hw
  rw [energy_expand]
  have z : ∀ e : Fin 8, e ≠ 6 → e ≠ 7 → w e * (lam e - θ e) ^ 2 / var e = 0 := by
    intro e p q
    rw [hrest e p q]
    simp
  rw [z 0 (by decide) (by decide), z 1 (by decide) (by decide),
      z 2 (by decide) (by decide), z 3 (by decide) (by decide),
      z 4 (by decide) (by decide), z 5 (by decide) (by decide),
      hd6, hd7, hv6, hv7]
  have h6 : (0:ℝ) ≤ w 6 := hpos 6
  have h7 : (0:ℝ) ≤ w 7 := hpos 7
  have hle : w 6 + w 7 ≤ 1 := by
    rw [Fin.sum_univ_eight] at hsum
    have a0 := hpos 0; have a1 := hpos 1; have a2 := hpos 2; have a3 := hpos 3
    have a4 := hpos 4; have a5 := hpos 5
    linarith
  have hM4 : (0:ℝ) < 4 * M := by linarith
  have e6 : w 6 * ((1:ℝ)/2) ^ 2 / M = w 6 / (4 * M) := by
    rw [div_eq_div_iff (ne_of_gt hM) (ne_of_gt hM4)]; ring
  have e7 : w 7 * (-((1:ℝ)/2)) ^ 2 / M = w 7 / (4 * M) := by
    rw [div_eq_div_iff (ne_of_gt hM) (ne_of_gt hM4)]; ring
  rw [e6, e7]
  have hcollapse : (0 + 0 + 0 + 0 + 0 + 0 + w 6 / (4 * M) + w 7 / (4 * M)) / 2
      = (w 6 + w 7) / (8 * M) := by
    field_simp
    ring
  rw [hcollapse]
  have : (w 6 + w 7) / (8 * M) ≤ 1 / (8 * M) :=
    div_le_div_of_nonneg_right hle (by linarith)
  linarith

/-! ### The boundary witness, and the strictly-bad alternatives behind it

`altLow_is_true_alt` exhibits a world at `d = 1/2`, where `range(A) = range(B)`.  That is a
TIE: retaining `A` is not yet WRONG there, only no longer strictly better.  With `eps = 0`
the alternative set of a decision is the set of worlds where the answer is not optimal, and
a tie does not belong to it.

The boundary witness is still the right object -- it is where the infimum sits -- but the
infimum has to be taken over the STRICT set.  The two lemmas below do that: every `d > 1/2`
gives a strictly bad world, and their energies approach the boundary value from above.  So
the bound is an infimum over strictly bad alternatives, not a value attained at a tie. -/

/-- A world in which retaining `A` is STRICTLY worse, not merely tied. -/
def StrictTrueAlt (lam : Fin 8 → ℝ) : Prop := rangeAof lam < rangeBof lam

theorem strictTrueAlt_imp (lam : Fin 8 → ℝ) (h : StrictTrueAlt lam) : TrueAlt lam :=
  le_of_lt h

/-- **Every `d > 1/2` gives a strictly bad world.**  `A` is untouched, so its range stays
`1`; `B`'s two middle cells move apart by `2d > 1`, which overshoots it. -/
theorem shifted_is_strict (d : ℝ) (hd : 1/2 < d) (lam : Fin 8 → ℝ)
    (h0 : lam 0 = 0) (h1 : lam 1 = 1) (h2 : lam 2 = 1/2) (h3 : lam 3 = 1/2)
    (h4 : lam 4 = 0) (h5 : lam 5 = 3/4) (h6 : lam 6 = 1/2 + d) (h7 : lam 7 = 1/2 - d) :
    StrictTrueAlt lam := by
  unfold StrictTrueAlt rangeAof rangeBof rng
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  have hc1 : max (0:ℝ) (3/4) = 3/4 := by norm_num
  have hc2 : min (0:ℝ) (3/4) = 0 := by norm_num
  have hmax : max (max (0:ℝ) (3/4)) (max (1/2 + d) (1/2 - d)) = 1/2 + d := by
    rw [hc1, max_eq_left (by linarith : (1:ℝ)/2 - d ≤ 1/2 + d),
        max_eq_right (by linarith : (3:ℝ)/4 ≤ 1/2 + d)]
  have hmin : min (min (0:ℝ) (3/4)) (min (1/2 + d) (1/2 - d)) = 1/2 - d := by
    rw [hc2, min_eq_right (by linarith : (1:ℝ)/2 - d ≤ 1/2 + d),
        min_eq_right (by linarith : (1:ℝ)/2 - d ≤ (0:ℝ))]
  rw [hmax, hmin]
  have hA : max (max (0:ℝ) 1) (max (1/2 : ℝ) (1/2)) - min (min (0:ℝ) 1)
      (min (1/2 : ℝ) (1/2)) = 1 := by norm_num
  rw [hA]
  linarith

/-- **The same statement at the centered world.**  Arm `A` is untouched so its range stays
`1`; arm `B`'s two `M`-variance cells move apart by `2d > 1`, which overshoots it.  The
numerals are `thetaLowC`, i.e. the paper's table with each arm's mean removed. -/
theorem shifted_is_strict_centered (d : ℝ) (hd : 1/2 < d) (lam : Fin 8 → ℝ)
    (h0 : lam 0 = -(1/2)) (h1 : lam 1 = 1/2) (h2 : lam 2 = 0) (h3 : lam 3 = 0)
    (h4 : lam 4 = -(7/16)) (h5 : lam 5 = 5/16)
    (h6 : lam 6 = 1/16 + d) (h7 : lam 7 = 1/16 - d) :
    StrictTrueAlt lam := by
  unfold StrictTrueAlt rangeAof rangeBof rng
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  have hc1 : max (-(7/16) : ℝ) (5/16) = 5/16 := by norm_num
  have hc2 : min (-(7/16) : ℝ) (5/16) = -(7/16) := by norm_num
  have hmax : max (max (-(7/16) : ℝ) (5/16)) (max (1/16 + d) (1/16 - d)) = 1/16 + d := by
    rw [hc1, max_eq_left (by linarith : (1:ℝ)/16 - d ≤ 1/16 + d),
        max_eq_right (by linarith : (5:ℝ)/16 ≤ 1/16 + d)]
  have hmin : min (min (-(7/16) : ℝ) (5/16)) (min (1/16 + d) (1/16 - d)) = 1/16 - d := by
    rw [hc2, min_eq_right (by linarith : (1:ℝ)/16 - d ≤ 1/16 + d),
        min_eq_right (by linarith : (1:ℝ)/16 - d ≤ -(7/16))]
  rw [hmax, hmin]
  have hA : max (max (-(1/2) : ℝ) (1/2)) (max (0:ℝ) 0)
      - min (min (-(1/2) : ℝ) (1/2)) (min (0:ℝ) 0) = 1 := by norm_num
  rw [hA]
  linarith

/-- The energy of the shifted world, for any design: only the two `M`-variance cells move. -/
theorem shifted_energy_le (M d : ℝ) (hM : 0 < M) (hd : 0 < d)
    (w var θ lam : Fin 8 → ℝ) (hw : IsAlloc w)
    (hv6 : var 6 = M) (hv7 : var 7 = M)
    (hd6 : lam 6 - θ 6 = d) (hd7 : lam 7 - θ 7 = -d)
    (hrest : ∀ e : Fin 8, e ≠ 6 → e ≠ 7 → lam e = θ e) :
    energy w var θ lam ≤ d ^ 2 / (2 * M) := by
  obtain ⟨hpos, hsum⟩ := hw
  rw [energy_expand]
  have z : ∀ e : Fin 8, e ≠ 6 → e ≠ 7 → w e * (lam e - θ e) ^ 2 / var e = 0 := by
    intro e p q
    rw [hrest e p q]
    simp
  rw [z 0 (by decide) (by decide), z 1 (by decide) (by decide),
      z 2 (by decide) (by decide), z 3 (by decide) (by decide),
      z 4 (by decide) (by decide), z 5 (by decide) (by decide),
      hd6, hd7, hv6, hv7]
  have hle : w 6 + w 7 ≤ 1 := by
    rw [Fin.sum_univ_eight] at hsum
    have a0 := hpos 0; have a1 := hpos 1; have a2 := hpos 2; have a3 := hpos 3
    have a4 := hpos 4; have a5 := hpos 5
    linarith
  have hM2 : (0:ℝ) < 2 * M := by linarith
  have e6 : w 6 * d ^ 2 / M = w 6 * d ^ 2 * 2 / (2 * M) := by
    rw [div_eq_div_iff (ne_of_gt hM) (ne_of_gt hM2)]; ring
  have e7 : w 7 * (-d) ^ 2 / M = w 7 * d ^ 2 * 2 / (2 * M) := by
    rw [div_eq_div_iff (ne_of_gt hM) (ne_of_gt hM2)]; ring
  rw [e6, e7]
  have hcollapse : (0 + 0 + 0 + 0 + 0 + 0 + w 6 * d ^ 2 * 2 / (2 * M)
      + w 7 * d ^ 2 * 2 / (2 * M)) / 2 = (w 6 + w 7) * d ^ 2 / (2 * M) := by
    field_simp
    ring
  rw [hcollapse]
  rw [div_le_div_iff₀ hM2 hM2]
  have hkey : (0:ℝ) ≤ (1 - (w 6 + w 7)) * (d ^ 2 * (2 * M)) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [hkey]

/-- **The infimum over STRICTLY bad worlds is still at most `1/(8M)`.**

For every design and every tolerance there is a strictly bad world within that tolerance of
the boundary value.  So the upper bound survives the move from the closed alternative set to
the open one, which is what `eps = 0` requires.  The witness at `d = 1/2` is retained as the
BOUNDARY point that pins the infimum, and is no longer claimed to be an alternative. -/
theorem low_true_strict_le (M : ℝ) (hM : 0 < M) (w var θ : Fin 8 → ℝ)
    (hw : IsAlloc w) (hv6 : var 6 = M) (hv7 : var 7 = M)
    (hθ0 : θ 0 = -(1/2)) (hθ1 : θ 1 = 1/2) (hθ2 : θ 2 = 0) (hθ3 : θ 3 = 0)
    (hθ4 : θ 4 = -(7/16)) (hθ5 : θ 5 = 5/16) (hθ6 : θ 6 = 1/16) (hθ7 : θ 7 = 1/16)
    (hθcls : InClass θ)
    (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ lam : Fin 8 → ℝ, StrictTrueAlt lam ∧ InClass lam ∧
      energy w var θ lam ≤ 1 / (8 * M) + ξ := by
  classical
  obtain ⟨η, hη0, hη1, hηsmall⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η + η ^ 2 ≤ 2 * M * ξ := by
    refine ⟨min 1 (M * ξ), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    have h1 : min 1 (M * ξ) ≤ 1 := min_le_left _ _
    have h2 : min 1 (M * ξ) ≤ M * ξ := min_le_right _ _
    have h3 : (0:ℝ) < min 1 (M * ξ) := lt_min one_pos (by positivity)
    nlinarith [h1, h2, h3]
  set d := 1/2 + η with hd
  have hdhalf : 1/2 < d := by rw [hd]; linarith
  have hdpos : 0 < d := by linarith
  refine ⟨fun e => if e = 6 then 1/16 + d else if e = 7 then 1/16 - d else θ e, ?_, ?_, ?_⟩
  · refine shifted_is_strict_centered d hdhalf _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [hθ0, hθ1, hθ2, hθ3, hθ4, hθ5]
  · -- the two moved cells belong to the same arm and move oppositely, so each arm's
    -- total is unchanged and the witness stays in the centered class
    obtain ⟨hA, hB⟩ := hθcls
    constructor
    · simpa using hA
    · simp only [show ((4:Fin 8) = 6) = False by simp,
                 show ((4:Fin 8) = 7) = False by simp,
                 show ((5:Fin 8) = 6) = False by simp,
                 show ((5:Fin 8) = 7) = False by simp,
                 show ((6:Fin 8) = 6) = True by simp,
                 show ((7:Fin 8) = 6) = False by simp,
                 show ((7:Fin 8) = 7) = True by simp]
      simp
      rw [hθ6, hθ7] at hB
      linarith
  · have hbound := shifted_energy_le M d hM hdpos w var θ
      (fun e => if e = 6 then 1/16 + d else if e = 7 then 1/16 - d else θ e) hw hv6 hv7
      (by simp [hθ6]) (by simp [hθ7])
      (by intro e p q; simp [p, q])
    have harith : d ^ 2 / (2 * M) ≤ 1 / (8 * M) + ξ := by
      have h8 : (0:ℝ) < 8 * M := by linarith
      have h2 : (0:ℝ) < 2 * M := by linarith
      rw [hd]
      rw [div_le_iff₀ h2]
      have : 1 / (8 * M) * (2 * M) = 1/4 := by field_simp; ring
      nlinarith [hηsmall, hη0, this, hM, hξ]
    linarith [hbound, harith]

/-- The design that is optimal for the PROXY in family A-low: a quarter on each of the four
frozen extrema, all of which have unit variance. -/
noncomputable def wLowStar : Fin 8 → ℝ :=
  fun e => if e.val = 0 ∨ e.val = 1 ∨ e.val = 4 ∨ e.val = 5 then 1/4 else 0

theorem wLowStar_isAlloc : IsAlloc wLowStar := by
  constructor
  · intro e
    unfold wLowStar
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_eight]
    norm_num [wLowStar]

theorem wLowStar_val0 : wLowStar 0 = 1/4 := by norm_num [wLowStar]
theorem wLowStar_val1 : wLowStar 1 = 1/4 := by norm_num [wLowStar]
theorem wLowStar_val4 : wLowStar 4 = 1/4 := by norm_num [wLowStar]
theorem wLowStar_val5 : wLowStar 5 = 1/4 := by norm_num [wLowStar]

/-- **Lower half of A-low, at a named allocation.**  Against EVERY proxy alternative the
quarter-on-each-extremum design already buys energy `1/512`.

The frozen contrast sits at `1/4` in the true world and must be driven to zero, so the four
measured deviations have `l^1` norm at least `1/4`; four-term Cauchy-Schwarz turns that into
squared norm at least `1/64`, and the design converts it into energy. -/
theorem low_proxy_ge (w var θ lam : Fin 8 → ℝ) (h : ProxyAlt lam)
    (hgap : (θ 1 - θ 0) - (θ 5 - θ 4) = 1/4)
    (hw0 : w 0 = 1/4) (hw1 : w 1 = 1/4) (hw4 : w 4 = 1/4) (hw5 : w 5 = 1/4)
    (hwpos : ∀ e, 0 ≤ w e) (hvpos : ∀ e, 0 < var e)
    (hv0 : var 0 = 1) (hv1 : var 1 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1) :
    1 / 512 ≤ energy w var θ lam := by
  unfold ProxyAlt at h
  have habs : (1:ℝ)/4
      ≤ |lam 0 - θ 0| + |lam 1 - θ 1| + |lam 4 - θ 4| + |lam 5 - θ 5| := by
    have b0 := neg_abs_le (lam 0 - θ 0); have c0 := le_abs_self (lam 0 - θ 0)
    have b1 := neg_abs_le (lam 1 - θ 1); have c1 := le_abs_self (lam 1 - θ 1)
    have b4 := neg_abs_le (lam 4 - θ 4); have c4 := le_abs_self (lam 4 - θ 4)
    have b5 := neg_abs_le (lam 5 - θ 5); have c5 := le_abs_self (lam 5 - θ 5)
    linarith
  have hsq : (1:ℝ)/64 ≤ (lam 0 - θ 0) ^ 2 + (lam 1 - θ 1) ^ 2
      + (lam 4 - θ 4) ^ 2 + (lam 5 - θ 5) ^ 2 := by
    nlinarith [cs_four (lam 0 - θ 0) (lam 1 - θ 1) (lam 4 - θ 4) (lam 5 - θ 5), habs,
               abs_nonneg (lam 0 - θ 0), abs_nonneg (lam 1 - θ 1),
               abs_nonneg (lam 4 - θ 4), abs_nonneg (lam 5 - θ 5)]
  have t2 := energy_term_nonneg w var θ lam 2 (hwpos 2) (hvpos 2)
  have t3 := energy_term_nonneg w var θ lam 3 (hwpos 3) (hvpos 3)
  have t6 := energy_term_nonneg w var θ lam 6 (hwpos 6) (hvpos 6)
  have t7 := energy_term_nonneg w var θ lam 7 (hwpos 7) (hvpos 7)
  have q0 : w 0 * (lam 0 - θ 0) ^ 2 / var 0 = (lam 0 - θ 0) ^ 2 / 4 := by
    rw [hw0, hv0]; ring
  have q1 : w 1 * (lam 1 - θ 1) ^ 2 / var 1 = (lam 1 - θ 1) ^ 2 / 4 := by
    rw [hw1, hv1]; ring
  have q4 : w 4 * (lam 4 - θ 4) ^ 2 / var 4 = (lam 4 - θ 4) ^ 2 / 4 := by
    rw [hw4, hv4]; ring
  have q5 : w 5 * (lam 5 - θ 5) ^ 2 / var 5 = (lam 5 - θ 5) ^ 2 / 4 := by
    rw [hw5, hv5]; ring
  rw [energy_expand, q0, q1, q4, q5]
  linarith [hsq, t2, t3, t6, t7]

/-! ## The game itself, so the ratio theorems are about a supremum and not a hypothesis

Up to here the module proves statements about ENERGIES at particular designs.  A separation
claim is about the VALUE of a game, `Gamma = sup_w inf_lambda E_w(lambda)`, and a theorem
that takes `Gamma_true <= U` and `Gamma_proxy >= L` as hypotheses proves only arithmetic.
This section defines the game and derives those two bounds from the energy lemmas, so the
ratio theorems below quantify over worlds rather than over assumed numbers. -/

/-- `Gamma` is an upper bound for the game when EVERY design admits a cheap alternative.
The alternative may depend on the design, which is what makes this usable against a
supremum: the adversary answers after seeing `w`. -/
theorem game_le_of_forall_design
    (Alt : (Fin 8 → ℝ) → Prop) (var θ : Fin 8 → ℝ) (U : ℝ) (Γ : ℝ)
    (hΓ : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, Alt lam ∧ u = energy w var θ lam} v} Γ)
    (hcheap : ∀ w : Fin 8 → ℝ, IsAlloc w → ∃ lam, Alt lam ∧ energy w var θ lam ≤ U) :
    Γ ≤ U := by
  refine hΓ.2 ?_
  rintro v ⟨w, hw, hv⟩
  obtain ⟨lam, hlam, hle⟩ := hcheap w hw
  exact le_trans (hv.1 ⟨lam, hlam, rfl⟩) hle

/-- `Gamma` is a lower bound for the game when ONE design beats every alternative.  The
design is fixed first, so this is a valid statement about a supremum. -/
theorem game_ge_of_exists_design
    (Alt : (Fin 8 → ℝ) → Prop) (var θ : Fin 8 → ℝ) (L : ℝ) (Γ : ℝ)
    (w₀ : Fin 8 → ℝ) (hw₀ : IsAlloc w₀)
    (hΓ : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, Alt lam ∧ u = energy w var θ lam} v} Γ)
    (hgood : ∀ lam, Alt lam → L ≤ energy w₀ var θ lam)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, Alt lam ∧ u = energy w₀ var θ lam} v₀)
    (hne : ∃ lam, Alt lam) :
    L ≤ Γ := by
  have hLv : L ≤ v₀ := by
    refine hv₀.2 ?_
    rintro u ⟨lam, hlam, rfl⟩
    exact hgood lam hlam
  exact le_trans hLv (hΓ.1 ⟨w₀, hw₀, hv₀⟩)

/-- **A-low: the true game is worth at most `1/(8M)`.**  Derived, not assumed: the cheap
alternative of `low_true_le` is available against every design. -/
theorem low_true_game_le (M : ℝ) (hM : 0 < M) (var θ : Fin 8 → ℝ)
    (hvpos : ∀ e, 0 < var e) (hv6 : var 6 = M) (hv7 : var 7 = M)
    (Γ : ℝ)
    (hΓ : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, TrueAlt lam ∧ u = energy w var θ lam} v} Γ)
    (lam₀ : Fin 8 → ℝ) (halt : TrueAlt lam₀)
    (hd6 : lam₀ 6 - θ 6 = 1/2) (hd7 : lam₀ 7 - θ 7 = -(1/2))
    (hrest : ∀ e : Fin 8, e ≠ 6 → e ≠ 7 → lam₀ e = θ e) :
    Γ ≤ 1 / (8 * M) := by
  refine game_le_of_forall_design TrueAlt var θ (1 / (8 * M)) Γ hΓ ?_
  intro w hw
  exact ⟨lam₀, halt, low_true_le M hM w var θ lam₀ hw hvpos hv6 hv7 hd6 hd7 hrest⟩

/-- **A-low: the proxy game is worth at least `1/512`.**  Derived from `low_proxy_ge` at the
design that lemma names. -/
theorem low_proxy_game_ge (var θ : Fin 8 → ℝ)
    (hgap : (θ 1 - θ 0) - (θ 5 - θ 4) = 1/4)
    (hvpos : ∀ e, 0 < var e)
    (hv0 : var 0 = 1) (hv1 : var 1 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1)
    (Γ : ℝ)
    (hΓ : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, ProxyAlt lam ∧ u = energy w var θ lam} v} Γ)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, ProxyAlt lam ∧ u = energy wLowStar var θ lam} v₀)
    (hne : ∃ lam, ProxyAlt lam) :
    1 / 512 ≤ Γ := by
  refine game_ge_of_exists_design ProxyAlt var θ (1 / 512) Γ wLowStar wLowStar_isAlloc
    hΓ ?_ v₀ hv₀ hne
  intro lam hlam
  exact low_proxy_ge wLowStar var θ lam hlam hgap wLowStar_val0 wLowStar_val1
    wLowStar_val4 wLowStar_val5 wLowStar_isAlloc.1 hvpos hv0 hv1 hv4 hv5

/-! ### The game on the class, with STRICT alternatives

Three changes from the version above, each demanded by a hypothesis of a theorem this
module relies on:

  the alternative set is intersected with `InClass`, so `centered_additive_response` applies
  and the energy is the information;

  the true alternatives are the STRICT ones, since at `eps = 0` a tie is not a world where
  the answer is wrong;

  the upper bound is stated in epsilon form, because a strict set need not attain its
  infimum -- the boundary witness at `d = 1/2` is where the infimum sits, and it is not
  itself an alternative. -/

/-- The value of a game whose alternatives are confined to the model class. -/
def GameLUB (Alt : (Fin 8 → ℝ) → Prop) (var θ : Fin 8 → ℝ) (Γ : ℝ) : Prop :=
  IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
    IsGLB {u : ℝ | ∃ lam, (Alt lam ∧ InClass lam) ∧ u = energy w var θ lam} v} Γ

/-- An upper bound on a game whose alternative set may not attain its infimum. -/
theorem game_le_of_forall_design_eps
    (Alt : (Fin 8 → ℝ) → Prop) (var θ : Fin 8 → ℝ) (U : ℝ) (Γ : ℝ)
    (hΓ : GameLUB Alt var θ Γ)
    (hcheap : ∀ w : Fin 8 → ℝ, IsAlloc w → ∀ ξ : ℝ, 0 < ξ →
      ∃ lam, Alt lam ∧ InClass lam ∧ energy w var θ lam ≤ U + ξ) :
    Γ ≤ U := by
  refine le_of_forall_pos_le_add ?_
  intro ξ hξ
  refine hΓ.2 ?_
  rintro v ⟨w, hw, hv⟩
  obtain ⟨lam, hlam, hcls, hle⟩ := hcheap w hw ξ hξ
  exact le_trans (hv.1 ⟨lam, ⟨hlam, hcls⟩, rfl⟩) hle

/-- A lower bound at one design, on the class-restricted game. -/
theorem game_ge_of_exists_design_class
    (Alt : (Fin 8 → ℝ) → Prop) (var θ : Fin 8 → ℝ) (L : ℝ) (Γ : ℝ)
    (w₀ : Fin 8 → ℝ) (hw₀ : IsAlloc w₀)
    (hΓ : GameLUB Alt var θ Γ)
    (hgood : ∀ lam, Alt lam → InClass lam → L ≤ energy w₀ var θ lam)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, (Alt lam ∧ InClass lam) ∧ u = energy w₀ var θ lam} v₀) :
    L ≤ Γ := by
  have hLv : L ≤ v₀ := by
    refine hv₀.2 ?_
    rintro u ⟨lam, ⟨hlam, hcls⟩, rfl⟩
    exact hgood lam hlam hcls
  exact le_trans hLv (hΓ.1 ⟨w₀, hw₀, hv₀⟩)

/-- **A-low on the class, with strict alternatives.**  The shifted witness is strictly bad,
lies in the centered class because it moves two cells of one arm oppositely, and its energy
approaches `1/(8M)` from above as the shift approaches the boundary. -/
theorem low_true_class_le (M : ℝ) (hM : 0 < M) (var θ : Fin 8 → ℝ)
    (hvpos : ∀ e, 0 < var e) (hv6 : var 6 = M) (hv7 : var 7 = M)
    (hθcls : InClass θ)
    (hθ0 : θ 0 = -(1/2)) (hθ1 : θ 1 = 1/2) (hθ2 : θ 2 = 0) (hθ3 : θ 3 = 0)
    (hθ4 : θ 4 = -(7/16)) (hθ5 : θ 5 = 5/16) (hθ6 : θ 6 = 1/16) (hθ7 : θ 7 = 1/16)
    (Γ : ℝ) (hΓ : GameLUB StrictTrueAlt var θ Γ) :
    Γ ≤ 1 / (8 * M) := by
  refine game_le_of_forall_design_eps StrictTrueAlt var θ (1 / (8 * M)) Γ hΓ ?_
  intro w hw ξ hξ
  obtain ⟨lam, hstrict, hcls, hen⟩ :=
    low_true_strict_le M hM w var θ hw hv6 hv7 hθ0 hθ1 hθ2 hθ3 hθ4 hθ5 hθ6 hθ7
      hθcls ξ hξ
  exact ⟨lam, hstrict, hcls, hen⟩

/-- **Family A-low, after the `sup_w`.**  The true value is at most `1/(8M)` and the proxy
value at least `1/512`, so the ratio is at most `64/M` and tends to zero. -/
theorem family_low_ratio_le (M : ℝ) (hM : 0 < M) (Γtrue Γproxy : ℝ)
    (htrue : Γtrue ≤ 1 / (8 * M)) (hproxy : 1 / 512 ≤ Γproxy) (hpos : 0 < Γproxy) :
    Γtrue / Γproxy ≤ 64 / M := by
  have h1 : Γtrue / Γproxy ≤ (1 / (8 * M)) / Γproxy :=
    div_le_div_of_nonneg_right htrue (le_of_lt hpos)
  have h2 : (1 / (8 * M)) / Γproxy ≤ (1 / (8 * M)) / (1 / 512) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hproxy
  have h3 : (1 / (8 * M)) / (1 / 512 : ℝ) = 64 / M := by
    field_simp
    norm_num
  linarith [h1, h2, h3.le, h3.ge]

/-! ## Family A-high: the proxy prices the information too LOW

    A = (0, 1, 3/4, 1/2),   B = (0, 1/2, 1/4, 1/4),   variance `M` on A2 and A4.

Lowering the cheap maximum `A2` satisfies the frozen contrast at cost `O(1/M)`, but it does
not make `A`'s range catch `B`'s: the runner-up `A3 = 3/4` survives, and a design that
simply ignores the two noisy cells still pays a constant. -/

/-- The alternative that lowers `A2` and raises `A4` by `1/2` keeps `A`'s total fixed and
satisfies the FROZEN contrast, which is the whole point. -/
theorem altHigh_is_proxy_alt (lam : Fin 8 → ℝ)
    (h0 : lam 0 = 0) (h1 : lam 1 = 1/2) (h4 : lam 4 = 0) (h5 : lam 5 = 1/2) :
    ProxyAlt lam := by
  unfold ProxyAlt
  rw [h0, h1, h4, h5]
  norm_num

/-- **Upper half of A-high, valid for EVERY allocation.**  The proxy game is worth at most
`1/(8M)` whatever the allocation, because the cheap frozen-contrast alternative is always
available. -/
theorem high_proxy_le (M : ℝ) (hM : 0 < M) (w var θ lam : Fin 8 → ℝ)
    (hw : IsAlloc w) (hvpos : ∀ e, 0 < var e)
    (hv1 : var 1 = M) (hv3 : var 3 = M)
    (hd1 : lam 1 - θ 1 = -(1/2)) (hd3 : lam 3 - θ 3 = 1/2)
    (hrest : ∀ e : Fin 8, e ≠ 1 → e ≠ 3 → lam e = θ e) :
    energy w var θ lam ≤ 1 / (8 * M) := by
  obtain ⟨hpos, hsum⟩ := hw
  rw [energy_expand]
  have z : ∀ e : Fin 8, e ≠ 1 → e ≠ 3 → w e * (lam e - θ e) ^ 2 / var e = 0 := by
    intro e p q
    rw [hrest e p q]
    simp
  rw [z 0 (by decide) (by decide), z 2 (by decide) (by decide),
      z 4 (by decide) (by decide), z 5 (by decide) (by decide),
      z 6 (by decide) (by decide), z 7 (by decide) (by decide),
      hd1, hd3, hv1, hv3]
  have h1 : (0:ℝ) ≤ w 1 := hpos 1
  have h3 : (0:ℝ) ≤ w 3 := hpos 3
  have hle : w 1 + w 3 ≤ 1 := by
    rw [Fin.sum_univ_eight] at hsum
    have a0 := hpos 0; have a2 := hpos 2; have a4 := hpos 4
    have a5 := hpos 5; have a6 := hpos 6; have a7 := hpos 7
    linarith
  have hM4 : (0:ℝ) < 4 * M := by linarith
  have e1 : w 1 * (-((1:ℝ)/2)) ^ 2 / M = w 1 / (4 * M) := by
    rw [div_eq_div_iff (ne_of_gt hM) (ne_of_gt hM4)]; ring
  have e3 : w 3 * ((1:ℝ)/2) ^ 2 / M = w 3 / (4 * M) := by
    rw [div_eq_div_iff (ne_of_gt hM) (ne_of_gt hM4)]; ring
  rw [e1, e3]
  have hcollapse : (0 + w 1 / (4 * M) + 0 + w 3 / (4 * M) + 0 + 0 + 0 + 0) / 2
      = (w 1 + w 3) / (8 * M) := by
    field_simp
    ring
  rw [hcollapse]
  have : (w 1 + w 3) / (8 * M) ≤ 1 / (8 * M) :=
    div_le_div_of_nonneg_right hle (by linarith)
  linarith

/-- The design that ignores the two noisy cells and spreads evenly over the six others. -/
noncomputable def wHighStar : Fin 8 → ℝ :=
  fun e => if e.val = 1 ∨ e.val = 3 then 0 else 1/6

theorem wHighStar_isAlloc : IsAlloc wHighStar := by
  constructor
  · intro e
    unfold wHighStar
    split_ifs <;> norm_num
  · rw [Fin.sum_univ_eight]
    norm_num [wHighStar]

/-! ### The geometric core of the A-high lower bound -/

/-- A maximum of four reals is one of them. -/
theorem max4_witness (a b c e : ℝ) :
    max (max a b) (max c e) = a ∨ max (max a b) (max c e) = b
      ∨ max (max a b) (max c e) = c ∨ max (max a b) (max c e) = e := by
  rcases le_total (max a b) (max c e) with h | h
  · rcases le_total c e with h2 | h2
    · exact Or.inr (Or.inr (Or.inr (by rw [max_eq_right h, max_eq_right h2])))
    · exact Or.inr (Or.inr (Or.inl (by rw [max_eq_right h, max_eq_left h2])))
  · rcases le_total a b with h2 | h2
    · exact Or.inr (Or.inl (by rw [max_eq_left h, max_eq_right h2]))
    · exact Or.inl (by rw [max_eq_left h, max_eq_left h2])

/-- A minimum of four reals is one of them. -/
theorem min4_witness (a b c e : ℝ) :
    min (min a b) (min c e) = a ∨ min (min a b) (min c e) = b
      ∨ min (min a b) (min c e) = c ∨ min (min a b) (min c e) = e := by
  rcases le_total (min a b) (min c e) with h | h
  · rcases le_total a b with h2 | h2
    · exact Or.inl (by rw [min_eq_left h, min_eq_left h2])
    · exact Or.inr (Or.inl (by rw [min_eq_left h, min_eq_right h2]))
  · rcases le_total c e with h2 | h2
    · exact Or.inr (Or.inr (Or.inl (by rw [min_eq_right h, min_eq_left h2])))
    · exact Or.inr (Or.inr (Or.inr (by rw [min_eq_right h, min_eq_right h2])))

/-- The new maximum is realised by some cell, so it exceeds the old maximum by at most that
cell's deviation -- and the deviation is NAMED, which is what keeps the constant sharp. -/
theorem max4_le_add (a b c e a' b' c' e' : ℝ) :
    ∃ p : ℝ, (p = a' - a ∨ p = b' - b ∨ p = c' - c ∨ p = e' - e) ∧
      max (max a' b') (max c' e') ≤ max (max a b) (max c e) + p := by
  obtain h | h | h | h := max4_witness a' b' c' e'
  · exact ⟨a' - a, Or.inl rfl, by
      rw [h]; have : a ≤ max (max a b) (max c e) :=
        le_trans (le_max_left a b) (le_max_left _ _); linarith⟩
  · exact ⟨b' - b, Or.inr (Or.inl rfl), by
      rw [h]; have : b ≤ max (max a b) (max c e) :=
        le_trans (le_max_right a b) (le_max_left _ _); linarith⟩
  · exact ⟨c' - c, Or.inr (Or.inr (Or.inl rfl)), by
      rw [h]; have : c ≤ max (max a b) (max c e) :=
        le_trans (le_max_left c e) (le_max_right _ _); linarith⟩
  · exact ⟨e' - e, Or.inr (Or.inr (Or.inr rfl)), by
      rw [h]; have : e ≤ max (max a b) (max c e) :=
        le_trans (le_max_right c e) (le_max_right _ _); linarith⟩

/-- Dually for the minimum. -/
theorem min4_ge_add (a b c e a' b' c' e' : ℝ) :
    ∃ q : ℝ, (q = a' - a ∨ q = b' - b ∨ q = c' - c ∨ q = e' - e) ∧
      min (min a b) (min c e) + q ≤ min (min a' b') (min c' e') := by
  obtain h | h | h | h := min4_witness a' b' c' e'
  · exact ⟨a' - a, Or.inl rfl, by
      rw [h]; have : min (min a b) (min c e) ≤ a :=
        le_trans (min_le_left _ _) (min_le_left a b); linarith⟩
  · exact ⟨b' - b, Or.inr (Or.inl rfl), by
      rw [h]; have : min (min a b) (min c e) ≤ b :=
        le_trans (min_le_left _ _) (min_le_right a b); linarith⟩
  · exact ⟨c' - c, Or.inr (Or.inr (Or.inl rfl)), by
      rw [h]; have : min (min a b) (min c e) ≤ c :=
        le_trans (min_le_right _ _) (min_le_left c e); linarith⟩
  · exact ⟨e' - e, Or.inr (Or.inr (Or.inr rfl)), by
      rw [h]; have : min (min a b) (min c e) ≤ e :=
        le_trans (min_le_right _ _) (min_le_right c e); linarith⟩

/-- **The range moves by at most the spread of two NAMED deviations.**  Bounding instead by
twice the largest deviation would be valid but lossy, and would cost the final constant. -/
theorem rng_move_pairwise (a b c e a' b' c' e' : ℝ) :
    ∃ p q : ℝ,
      (p = a' - a ∨ p = b' - b ∨ p = c' - c ∨ p = e' - e) ∧
      (q = a' - a ∨ q = b' - b ∨ q = c' - c ∨ q = e' - e) ∧
      rng a' b' c' e' ≤ rng a b c e + (p - q) := by
  obtain ⟨p, hp, hple⟩ := max4_le_add a b c e a' b' c' e'
  obtain ⟨q, hq, hqle⟩ := min4_ge_add a b c e a' b' c' e'
  exact ⟨p, q, hp, hq, by unfold rng; linarith⟩

/-- Two deviations drawn from four cells, with DISTINCT values so necessarily distinct
cells, have squared sum at most the total.  The four diagonal cases are discharged by the
distinctness hypothesis itself. -/
theorem two_distinct_sq_le (d4 d5 d6 d7 p q : ℝ)
    (hp : p = d4 ∨ p = d5 ∨ p = d6 ∨ p = d7)
    (hq : q = d4 ∨ q = d5 ∨ q = d6 ∨ q = d7)
    (hne : p ≠ q) :
    p ^ 2 + q ^ 2 ≤ d4 ^ 2 + d5 ^ 2 + d6 ^ 2 + d7 ^ 2 := by
  have s4 := sq_nonneg d4
  have s5 := sq_nonneg d5
  have s6 := sq_nonneg d6
  have s7 := sq_nonneg d7
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | linarith

/-- **The arithmetic core of the A-high lower bound**, isolated so the elaborator never
sees it mixed with the eight-cell energy expansion.

From the displacement inequality `1/4 <= |x0| + |x2| + (p - q)`, with `p` and `q` drawn from
the four `B` deviations, the six measured deviations have squared norm at least `1/64`.  The
single case split is on whether `p` and `q` coincide: if they do, `B`'s range has not moved
and the two `A` cells must close the whole gap, which two-term Cauchy-Schwarz turns into the
stronger `1/32`. -/
theorem six_norm_lower (x0 x2 x4 x5 x6 x7 p q : ℝ)
    (hp : p = x4 ∨ p = x5 ∨ p = x6 ∨ p = x7)
    (hq : q = x4 ∨ q = x5 ∨ q = x6 ∨ q = x7)
    (hkey : (1:ℝ)/4 ≤ |x0| + |x2| + (p - q)) :
    (1:ℝ)/64 ≤ x0 ^ 2 + x2 ^ 2 + (x4 ^ 2 + x5 ^ 2 + x6 ^ 2 + x7 ^ 2) := by
  have n4 := sq_nonneg x4
  have n5 := sq_nonneg x5
  have n6 := sq_nonneg x6
  have n7 := sq_nonneg x7
  by_cases hpq : p = q
  · rw [hpq] at hkey
    have h2 : (1:ℝ)/4 ≤ |x0| + |x2| := by linarith
    have hnn : (0:ℝ) ≤ |x0| + |x2| := by positivity
    have hsq1 : (1:ℝ)/16 ≤ (|x0| + |x2|) ^ 2 := by nlinarith [h2, hnn]
    have hsq2 := cs_two x0 x2
    linarith [hsq1, hsq2]
  · have hpd := two_distinct_sq_le x4 x5 x6 x7 p q hp hq hpq
    have habs : (1:ℝ)/4 ≤ |x0| + |x2| + |p| + |q| := by
      have bp := le_abs_self p
      have bq := neg_abs_le q
      linarith [hkey]
    have hnn : (0:ℝ) ≤ |x0| + |x2| + |p| + |q| := by positivity
    have hsq1 : (1:ℝ)/16 ≤ (|x0| + |x2| + |p| + |q|) ^ 2 := by nlinarith [habs, hnn]
    have hsq2 := cs_four x0 x2 p q
    linarith [hsq1, hsq2, hpd]

/-- `rangeAof` is at least the spread between `A1` and `A3`, the two cells the design still
measures.  This is what stops the adversary hiding behind the two noisy cells. -/
theorem rangeAof_ge_pair (lam : Fin 8 → ℝ) : lam 2 - lam 0 ≤ rangeAof lam := by
  unfold rangeAof rng
  have h2 : lam 2 ≤ max (max (lam 0) (lam 1)) (max (lam 2) (lam 3)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h0 : min (min (lam 0) (lam 1)) (min (lam 2) (lam 3)) ≤ lam 0 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  linarith

/-- **Lower half of A-high, at a named allocation.**  Against EVERY true alternative the
design that ignores the two noisy cells buys energy at least `1/768`.

A true alternative must bring `A`'s range down to `B`'s; `A`'s range is at least the
`A3 - A1` spread, which starts at `3/4`; and `B`'s range, which starts at `1/2`, moves by at
most the spread of two named `B` deviations.  So the six measured deviations must satisfy
`|dA1| + |dA3| + p - q >= 1/4`, and Cauchy-Schwarz converts that into squared norm `1/64`.
The single case split is on whether the two named deviations coincide: if they do, `B`'s
range has not moved at all and the two `A` cells must do all the work. -/
theorem high_true_ge (w var θ lam : Fin 8 → ℝ) (h : TrueAlt lam)
    (hθspread : θ 2 - θ 0 = 3/4) (hθB : rangeBof θ = 1/2)
    (hw0 : w 0 = 1/6) (hw2 : w 2 = 1/6) (hw4 : w 4 = 1/6) (hw5 : w 5 = 1/6)
    (hw6 : w 6 = 1/6) (hw7 : w 7 = 1/6)
    (hwpos : ∀ e, 0 ≤ w e) (hvpos : ∀ e, 0 < var e)
    (hv0 : var 0 = 1) (hv2 : var 2 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1)
    (hv6 : var 6 = 1) (hv7 : var 7 = 1) :
    1 / 768 ≤ energy w var θ lam := by
  classical
  obtain ⟨p, q, hp, hq, hmove⟩ :=
    rng_move_pairwise (θ 4) (θ 5) (θ 6) (θ 7) (lam 4) (lam 5) (lam 6) (lam 7)
  have hB : rangeBof lam ≤ 1/2 + (p - q) := by
    have hrw : rangeBof lam ≤ rangeBof θ + (p - q) := by
      simpa [rangeBof] using hmove
    rw [hθB] at hrw
    exact hrw
  have hA : (3:ℝ)/4 - |lam 0 - θ 0| - |lam 2 - θ 2| ≤ rangeAof lam := by
    have hpair := rangeAof_ge_pair lam
    have b0 := le_abs_self (lam 0 - θ 0); have c0 := neg_abs_le (lam 0 - θ 0)
    have b2 := le_abs_self (lam 2 - θ 2); have c2 := neg_abs_le (lam 2 - θ 2)
    have hexp : lam 2 - lam 0 = 3/4 + (lam 2 - θ 2) - (lam 0 - θ 0) := by
      linarith [hθspread]
    linarith [hpair, b0, c0, b2, c2, hexp.le, hexp.ge]
  have hkey : (1:ℝ)/4 ≤ |lam 0 - θ 0| + |lam 2 - θ 2| + (p - q) := by
    unfold TrueAlt at h
    linarith [hA, hB, h]
  have hsix := six_norm_lower (lam 0 - θ 0) (lam 2 - θ 2) (lam 4 - θ 4) (lam 5 - θ 5)
    (lam 6 - θ 6) (lam 7 - θ 7) p q hp hq hkey
  have t1 := energy_term_nonneg w var θ lam 1 (hwpos 1) (hvpos 1)
  have t3 := energy_term_nonneg w var θ lam 3 (hwpos 3) (hvpos 3)
  have q0 : w 0 * (lam 0 - θ 0) ^ 2 / var 0 = (lam 0 - θ 0) ^ 2 / 6 := by
    rw [hw0, hv0]; ring
  have q2 : w 2 * (lam 2 - θ 2) ^ 2 / var 2 = (lam 2 - θ 2) ^ 2 / 6 := by
    rw [hw2, hv2]; ring
  have q4 : w 4 * (lam 4 - θ 4) ^ 2 / var 4 = (lam 4 - θ 4) ^ 2 / 6 := by
    rw [hw4, hv4]; ring
  have q5 : w 5 * (lam 5 - θ 5) ^ 2 / var 5 = (lam 5 - θ 5) ^ 2 / 6 := by
    rw [hw5, hv5]; ring
  have q6 : w 6 * (lam 6 - θ 6) ^ 2 / var 6 = (lam 6 - θ 6) ^ 2 / 6 := by
    rw [hw6, hv6]; ring
  have q7 : w 7 * (lam 7 - θ 7) ^ 2 / var 7 = (lam 7 - θ 7) ^ 2 / 6 := by
    rw [hw7, hv7]; ring
  rw [energy_expand, q0, q2, q4, q5, q6, q7]
  linarith [hsix, t1, t3]

/-- **A-high: the proxy game is worth at most `1/(8M)`.** -/
theorem high_proxy_game_le (M : ℝ) (hM : 0 < M) (var θ : Fin 8 → ℝ)
    (hvpos : ∀ e, 0 < var e) (hv1 : var 1 = M) (hv3 : var 3 = M)
    (Γ : ℝ)
    (hΓ : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, ProxyAlt lam ∧ u = energy w var θ lam} v} Γ)
    (lam₀ : Fin 8 → ℝ) (halt : ProxyAlt lam₀)
    (hd1 : lam₀ 1 - θ 1 = -(1/2)) (hd3 : lam₀ 3 - θ 3 = 1/2)
    (hrest : ∀ e : Fin 8, e ≠ 1 → e ≠ 3 → lam₀ e = θ e) :
    Γ ≤ 1 / (8 * M) := by
  refine game_le_of_forall_design ProxyAlt var θ (1 / (8 * M)) Γ hΓ ?_
  intro w hw
  exact ⟨lam₀, halt, high_proxy_le M hM w var θ lam₀ hw hvpos hv1 hv3 hd1 hd3 hrest⟩

/-- **A-high: the true game is worth at least `1/768`.** -/
theorem high_true_game_ge (var θ : Fin 8 → ℝ)
    (hθspread : θ 2 - θ 0 = 3/4) (hθB : rangeBof θ = 1/2)
    (hvpos : ∀ e, 0 < var e)
    (hv0 : var 0 = 1) (hv2 : var 2 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1)
    (hv6 : var 6 = 1) (hv7 : var 7 = 1)
    (Γ : ℝ)
    (hΓ : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, TrueAlt lam ∧ u = energy w var θ lam} v} Γ)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, TrueAlt lam ∧ u = energy wHighStar var θ lam} v₀)
    (hne : ∃ lam, TrueAlt lam) :
    1 / 768 ≤ Γ := by
  refine game_ge_of_exists_design TrueAlt var θ (1 / 768) Γ wHighStar wHighStar_isAlloc
    hΓ ?_ v₀ hv₀ hne
  intro lam hlam
  refine high_true_ge wHighStar var θ lam hlam hθspread hθB ?_ ?_ ?_ ?_ ?_ ?_
    wHighStar_isAlloc.1 hvpos hv0 hv2 hv4 hv5 hv6 hv7 <;>
    norm_num [wHighStar]

/-- **Family A-high, after the `sup_w`.**  The proxy value is at most `1/(8M)` and the true
value at least `1/768`, so the ratio is at least `M/96` and diverges. -/
theorem family_high_ratio_ge (M : ℝ) (hM : 0 < M) (Γtrue Γproxy : ℝ)
    (htrue : 1 / 768 ≤ Γtrue) (hproxy : Γproxy ≤ 1 / (8 * M)) (hpos : 0 < Γproxy) :
    M / 96 ≤ Γtrue / Γproxy := by
  have h1 : (1 / 768 : ℝ) / Γproxy ≤ Γtrue / Γproxy :=
    div_le_div_of_nonneg_right htrue (le_of_lt hpos)
  have h2 : (1 / 768 : ℝ) / (1 / (8 * M)) ≤ (1 / 768) / Γproxy :=
    div_le_div_of_nonneg_left (by norm_num) hpos hproxy
  have h3 : (1 / 768 : ℝ) / (1 / (8 * M)) = M / 96 := by
    field_simp
    ring
  linarith [h1, h2, h3.le, h3.ge]

/-- **A-low, end to end.**  The ratio bound with NO assumed bound on either game value:
both come from the energy lemmas via `low_true_game_le` and `low_proxy_game_ge`. -/
theorem family_low_separation (M : ℝ) (hM : 0 < M) (var θ : Fin 8 → ℝ)
    (hvpos : ∀ e, 0 < var e) (hv6 : var 6 = M) (hv7 : var 7 = M)
    (hv0 : var 0 = 1) (hv1 : var 1 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1)
    (hgap : (θ 1 - θ 0) - (θ 5 - θ 4) = 1/4)
    (lam₀ : Fin 8 → ℝ) (halt : TrueAlt lam₀)
    (hd6 : lam₀ 6 - θ 6 = 1/2) (hd7 : lam₀ 7 - θ 7 = -(1/2))
    (hrest : ∀ e : Fin 8, e ≠ 6 → e ≠ 7 → lam₀ e = θ e)
    (Γtrue Γproxy : ℝ)
    (hT : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, TrueAlt lam ∧ u = energy w var θ lam} v} Γtrue)
    (hP : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, ProxyAlt lam ∧ u = energy w var θ lam} v} Γproxy)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, ProxyAlt lam ∧ u = energy wLowStar var θ lam} v₀)
    (hne : ∃ lam, ProxyAlt lam)
    (hPpos : 0 < Γproxy) :
    Γtrue / Γproxy ≤ 64 / M := by
  have hu := low_true_game_le M hM var θ hvpos hv6 hv7 Γtrue hT lam₀ halt hd6 hd7 hrest
  have hl := low_proxy_game_ge var θ hgap hvpos hv0 hv1 hv4 hv5 Γproxy hP v₀ hv₀ hne
  exact family_low_ratio_le M hM Γtrue Γproxy hu hl hPpos

/-- **A-high, end to end.**  Same, in the other direction. -/
theorem family_high_separation (M : ℝ) (hM : 0 < M) (var θ : Fin 8 → ℝ)
    (hvpos : ∀ e, 0 < var e) (hv1 : var 1 = M) (hv3 : var 3 = M)
    (hv0 : var 0 = 1) (hv2 : var 2 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1)
    (hv6 : var 6 = 1) (hv7 : var 7 = 1)
    (hθspread : θ 2 - θ 0 = 3/4) (hθB : rangeBof θ = 1/2)
    (lam₀ : Fin 8 → ℝ) (halt : ProxyAlt lam₀)
    (hd1 : lam₀ 1 - θ 1 = -(1/2)) (hd3 : lam₀ 3 - θ 3 = 1/2)
    (hrest : ∀ e : Fin 8, e ≠ 1 → e ≠ 3 → lam₀ e = θ e)
    (Γtrue Γproxy : ℝ)
    (hT : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, TrueAlt lam ∧ u = energy w var θ lam} v} Γtrue)
    (hP : IsLUB {v : ℝ | ∃ w : Fin 8 → ℝ, IsAlloc w ∧
            IsGLB {u : ℝ | ∃ lam, ProxyAlt lam ∧ u = energy w var θ lam} v} Γproxy)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, TrueAlt lam ∧ u = energy wHighStar var θ lam} v₀)
    (hne : ∃ lam, TrueAlt lam)
    (hPpos : 0 < Γproxy) :
    M / 96 ≤ Γtrue / Γproxy := by
  have hu := high_proxy_game_le M hM var θ hvpos hv1 hv3 Γproxy hP lam₀ halt hd1 hd3 hrest
  have hl := high_true_game_ge var θ hθspread hθB hvpos hv0 hv2 hv4 hv5 hv6 hv7
    Γtrue hT v₀ hv₀ hne
  exact family_high_ratio_ge M hM Γtrue Γproxy hl hu hPpos

/-- **One variance defeats every constant at once.**

For any candidate approximation factor `c` there is a SINGLE `M` at which the A-low ratio
falls below `c` and the A-high ratio rises above it.  So no `c` can bound the surrogate's
error in both families, and the quantifiers range over the game values that the theorems
above derive, not over free numbers. -/
theorem no_constant_factor_after_sup (c : ℝ) (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧
      (∀ Γt Γp : ℝ, 0 < Γp → Γt ≤ 1 / (8 * M) → 1 / 512 ≤ Γp → Γt / Γp < c) ∧
      (∀ Γt Γp : ℝ, 0 < Γp → 1 / 768 ≤ Γt → Γp ≤ 1 / (8 * M) → c < Γt / Γp) := by
  refine ⟨max (64 / c + 1) (96 * c + 1), ?_, ?_, ?_⟩
  · have : (0:ℝ) < 96 * c + 1 := by positivity
    exact lt_of_lt_of_le this (le_max_right _ _)
  · intro Γt Γp hp ht hl
    have hM : (0:ℝ) < max (64 / c + 1) (96 * c + 1) := by
      have : (0:ℝ) < 96 * c + 1 := by positivity
      exact lt_of_lt_of_le this (le_max_right _ _)
    have hrat := family_low_ratio_le _ hM Γt Γp ht hl hp
    have hbig : 64 / c < max (64 / c + 1) (96 * c + 1) :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have : 64 / max (64 / c + 1) (96 * c + 1) < c := by
      rw [div_lt_iff₀ hM]
      rw [div_lt_iff₀ hc] at hbig
      linarith
    linarith
  · intro Γt Γp hp hl hu
    have hM : (0:ℝ) < max (64 / c + 1) (96 * c + 1) := by
      have : (0:ℝ) < 96 * c + 1 := by positivity
      exact lt_of_lt_of_le this (le_max_right _ _)
    have hrat := family_high_ratio_ge _ hM Γt Γp hl hu hp
    have hbig : 96 * c < max (64 / c + 1) (96 * c + 1) :=
      lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have : c < max (64 / c + 1) (96 * c + 1) / 96 := by
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 96)]
      linarith
    linarith

/-- **Both directions on the same decision rule.**  No constant can relate the two games in
both families at once, so no constant-factor guarantee for the frozen surrogate exists,
however the allocation is chosen. -/
theorem no_constant_factor_guarantee :
    ∀ c : ℝ, 0 < c → ∃ M : ℝ, 0 < M ∧ (64 / M < c ∨ c < M / 96) := by
  intro c hc
  refine ⟨96 * c + 96, by positivity, Or.inr ?_⟩
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 96)]
  linarith

/-! ## The separation on the class-restricted game, end to end

Everything below is about `GameLUB`, so the alternatives are strictly bad AND in the
centered class.  The hypotheses name the world's cells; nothing about `Gamma` is assumed. -/

/-- The proxy game on the class is still worth at least `1/512`: restricting the adversary
can only raise an infimum, so `low_proxy_ge` transfers unchanged. -/
theorem low_proxy_class_ge (var θ : Fin 8 → ℝ)
    (hgap : (θ 1 - θ 0) - (θ 5 - θ 4) = 1/4)
    (hvpos : ∀ e, 0 < var e)
    (hv0 : var 0 = 1) (hv1 : var 1 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1)
    (Γ : ℝ) (hΓ : GameLUB ProxyAlt var θ Γ)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, (ProxyAlt lam ∧ InClass lam)
      ∧ u = energy wLowStar var θ lam} v₀) :
    1 / 512 ≤ Γ := by
  refine game_ge_of_exists_design_class ProxyAlt var θ (1 / 512) Γ wLowStar
    wLowStar_isAlloc hΓ ?_ v₀ hv₀
  intro lam hlam _
  exact low_proxy_ge wLowStar var θ lam hlam hgap wLowStar_val0 wLowStar_val1
    wLowStar_val4 wLowStar_val5 wLowStar_isAlloc.1 hvpos hv0 hv1 hv4 hv5

/-- The true game on the class is still worth at least `1/768`, for the same reason. -/
theorem high_true_class_ge (var θ : Fin 8 → ℝ)
    (hθspread : θ 2 - θ 0 = 3/4) (hθB : rangeBof θ = 1/2)
    (hvpos : ∀ e, 0 < var e)
    (hv0 : var 0 = 1) (hv2 : var 2 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1)
    (hv6 : var 6 = 1) (hv7 : var 7 = 1)
    (Γ : ℝ) (hΓ : GameLUB StrictTrueAlt var θ Γ)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, (StrictTrueAlt lam ∧ InClass lam)
      ∧ u = energy wHighStar var θ lam} v₀) :
    1 / 768 ≤ Γ := by
  refine game_ge_of_exists_design_class StrictTrueAlt var θ (1 / 768) Γ wHighStar
    wHighStar_isAlloc hΓ ?_ v₀ hv₀
  intro lam hlam _
  refine high_true_ge wHighStar var θ lam (strictTrueAlt_imp lam hlam)
    hθspread hθB ?_ ?_ ?_ ?_ ?_ ?_ wHighStar_isAlloc.1 hvpos hv0 hv2 hv4 hv5 hv6 hv7 <;>
    norm_num [wHighStar]

/-- The proxy game on the class is still worth at most `1/(8M)` in A-high, provided the
cheap witness lies in the class -- which it does, moving `A2` and `A4` oppositely. -/
theorem high_proxy_class_le (M : ℝ) (hM : 0 < M) (var θ : Fin 8 → ℝ)
    (hvpos : ∀ e, 0 < var e) (hv1 : var 1 = M) (hv3 : var 3 = M)
    (Γ : ℝ) (hΓ : GameLUB ProxyAlt var θ Γ)
    (lam₀ : Fin 8 → ℝ) (halt : ProxyAlt lam₀) (hcls : InClass lam₀)
    (hd1 : lam₀ 1 - θ 1 = -(1/2)) (hd3 : lam₀ 3 - θ 3 = 1/2)
    (hrest : ∀ e : Fin 8, e ≠ 1 → e ≠ 3 → lam₀ e = θ e) :
    Γ ≤ 1 / (8 * M) := by
  refine game_le_of_forall_design_eps ProxyAlt var θ (1 / (8 * M)) Γ hΓ ?_
  intro w hw ξ hξ
  exact ⟨lam₀, halt, hcls,
    le_trans (high_proxy_le M hM w var θ lam₀ hw hvpos hv1 hv3 hd1 hd3 hrest)
      (by linarith)⟩

/-- **A-low, end to end on the class-restricted game with strict alternatives.** -/
theorem family_low_separation_class (M : ℝ) (hM : 0 < M) (var θ : Fin 8 → ℝ)
    (hvpos : ∀ e, 0 < var e) (hv6 : var 6 = M) (hv7 : var 7 = M)
    (hv0 : var 0 = 1) (hv1 : var 1 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1)
    (hθcls : InClass θ)
    (hθ0 : θ 0 = -(1/2)) (hθ1 : θ 1 = 1/2) (hθ2 : θ 2 = 0) (hθ3 : θ 3 = 0)
    (hθ4 : θ 4 = -(7/16)) (hθ5 : θ 5 = 5/16) (hθ6 : θ 6 = 1/16) (hθ7 : θ 7 = 1/16)
    (hgap : (θ 1 - θ 0) - (θ 5 - θ 4) = 1/4)
    (Γtrue Γproxy : ℝ)
    (hT : GameLUB StrictTrueAlt var θ Γtrue)
    (hP : GameLUB ProxyAlt var θ Γproxy)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, (ProxyAlt lam ∧ InClass lam)
      ∧ u = energy wLowStar var θ lam} v₀)
    (hPpos : 0 < Γproxy) :
    Γtrue / Γproxy ≤ 64 / M := by
  have hu := low_true_class_le M hM var θ hvpos hv6 hv7 hθcls
    hθ0 hθ1 hθ2 hθ3 hθ4 hθ5 hθ6 hθ7 Γtrue hT
  have hl := low_proxy_class_ge var θ hgap hvpos hv0 hv1 hv4 hv5 Γproxy hP v₀ hv₀
  exact family_low_ratio_le M hM Γtrue Γproxy hu hl hPpos

/-- **A-high, end to end on the class-restricted game.** -/
theorem family_high_separation_class (M : ℝ) (hM : 0 < M) (var θ : Fin 8 → ℝ)
    (hvpos : ∀ e, 0 < var e) (hv1 : var 1 = M) (hv3 : var 3 = M)
    (hv0 : var 0 = 1) (hv2 : var 2 = 1) (hv4 : var 4 = 1) (hv5 : var 5 = 1)
    (hv6 : var 6 = 1) (hv7 : var 7 = 1)
    (hθspread : θ 2 - θ 0 = 3/4) (hθB : rangeBof θ = 1/2)
    (lam₀ : Fin 8 → ℝ) (halt : ProxyAlt lam₀) (hcls : InClass lam₀)
    (hd1 : lam₀ 1 - θ 1 = -(1/2)) (hd3 : lam₀ 3 - θ 3 = 1/2)
    (hrest : ∀ e : Fin 8, e ≠ 1 → e ≠ 3 → lam₀ e = θ e)
    (Γtrue Γproxy : ℝ)
    (hT : GameLUB StrictTrueAlt var θ Γtrue)
    (hP : GameLUB ProxyAlt var θ Γproxy)
    (v₀ : ℝ)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, (StrictTrueAlt lam ∧ InClass lam)
      ∧ u = energy wHighStar var θ lam} v₀)
    (hPpos : 0 < Γproxy) :
    M / 96 ≤ Γtrue / Γproxy := by
  have hu := high_proxy_class_le M hM var θ hvpos hv1 hv3 Γproxy hP lam₀ halt hcls
    hd1 hd3 hrest
  have hl := high_true_class_ge var θ hθspread hθB hvpos hv0 hv2 hv4 hv5 hv6 hv7
    Γtrue hT v₀ hv₀
  exact family_high_ratio_ge M hM Γtrue Γproxy hl hu hPpos

/-- **No constant factor, quantified over the two real families.**

For every candidate factor `c` there is a single variance `M` at which the A-low ratio falls
below `c` and the A-high ratio rises above it -- and the ratios in question are the values
of the class-restricted games with strict alternatives, delivered by the two theorems above.
So no `c` relates the surrogate to the truth in both families, after the allocation has been
optimised. -/
theorem no_constant_factor_on_families (c : ℝ) (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧
      (∀ (var θ : Fin 8 → ℝ) (Γt Γp v₀ : ℝ),
        (∀ e, 0 < var e) → var 6 = M → var 7 = M →
        var 0 = 1 → var 1 = 1 → var 4 = 1 → var 5 = 1 →
        InClass θ → θ 0 = -(1/2) → θ 1 = 1/2 → θ 2 = 0 → θ 3 = 0 →
        θ 4 = -(7/16) → θ 5 = 5/16 → θ 6 = 1/16 → θ 7 = 1/16 →
        (θ 1 - θ 0) - (θ 5 - θ 4) = 1/4 →
        GameLUB StrictTrueAlt var θ Γt → GameLUB ProxyAlt var θ Γp →
        IsGLB {u : ℝ | ∃ lam, (ProxyAlt lam ∧ InClass lam)
          ∧ u = energy wLowStar var θ lam} v₀ →
        0 < Γp → Γt / Γp < c) ∧
      (∀ (var θ lam₀ : Fin 8 → ℝ) (Γt Γp v₀ : ℝ),
        (∀ e, 0 < var e) → var 1 = M → var 3 = M →
        var 0 = 1 → var 2 = 1 → var 4 = 1 → var 5 = 1 → var 6 = 1 → var 7 = 1 →
        θ 2 - θ 0 = 3/4 → rangeBof θ = 1/2 →
        ProxyAlt lam₀ → InClass lam₀ →
        lam₀ 1 - θ 1 = -(1/2) → lam₀ 3 - θ 3 = 1/2 →
        (∀ e : Fin 8, e ≠ 1 → e ≠ 3 → lam₀ e = θ e) →
        GameLUB StrictTrueAlt var θ Γt → GameLUB ProxyAlt var θ Γp →
        IsGLB {u : ℝ | ∃ lam, (StrictTrueAlt lam ∧ InClass lam)
          ∧ u = energy wHighStar var θ lam} v₀ →
        0 < Γp → c < Γt / Γp) := by
  obtain ⟨M, hM, hlow, hhigh⟩ := no_constant_factor_after_sup c hc
  refine ⟨M, hM, ?_, ?_⟩
  · intro var θ Γt Γp v₀ hvpos hv6 hv7 hv0 hv1 hv4 hv5 hcls h0 h1 h2 h3 h4 h5 h6 h7
      hgap hT hP hv₀ hPpos
    have hu := low_true_class_le M hM var θ hvpos hv6 hv7 hcls h0 h1 h2 h3 h4 h5 h6 h7 Γt hT
    have hl := low_proxy_class_ge var θ hgap hvpos hv0 hv1 hv4 hv5 Γp hP v₀ hv₀
    exact hlow Γt Γp hPpos hu hl
  · intro var θ lam₀ Γt Γp v₀ hvpos hv1 hv3 hv0 hv2 hv4 hv5 hv6 hv7 h2 hB
      halt hcls hd1 hd3 hrest hT hP hv₀ hPpos
    have hu := high_proxy_class_le M hM var θ hvpos hv1 hv3 Γp hP lam₀ halt hcls
      hd1 hd3 hrest
    have hl := high_true_class_ge var θ h2 hB hvpos hv0 hv2 hv4 hv5 hv6 hv7 Γt hT v₀ hv₀
    exact hhigh Γt Γp hPpos hl hu

/-! ## The game values exist, and the worlds that carry them are concrete

Every separation theorem above is conditional on an `IsLUB` and an `IsGLB` existing.  They
do, and this section proves it instead of assuming it: each inner set is nonempty and
bounded below by zero, and each outer set is bounded above by the cheap alternative that the
separation already exhibits.  The section ends with the two families instantiated at the
concrete centered worlds, so the statements are known to have instances. -/

/-- Shifting both arms does not change which worlds are STRICTLY bad either. -/
theorem strictTrueAlt_shiftArms (cA cB : ℝ) (x : Fin 8 → ℝ) :
    StrictTrueAlt (shiftArms cA cB x) ↔ StrictTrueAlt x := by
  unfold StrictTrueAlt
  rw [rangeAof_shiftArms, rangeBof_shiftArms]

/-- The energy is nonnegative for any allocation with nonnegative weights. -/
theorem energy_nonneg (w var θ lam : Fin 8 → ℝ) (hw : ∀ e, 0 ≤ w e) (hv : ∀ e, 0 < var e) :
    0 ≤ energy w var θ lam := by
  unfold energy
  refine div_nonneg (Finset.sum_nonneg fun e _ => ?_) (by norm_num)
  exact energy_term_nonneg w var θ lam e (hw e) (hv e)

/-- A candidate whose every deviation is at most `c`, against variances at least `m`, costs
at most `c^2/(2m)` however the design allocates.  This is what bounds the outer set above
when the cheap alternative is a fixed world rather than a family. -/
theorem energy_le_of_dev_bound (w var θ lam : Fin 8 → ℝ) (hw : IsAlloc w)
    (c m : ℝ) (hm : 0 < m) (hv : ∀ e, m ≤ var e) (hd : ∀ e, |lam e - θ e| ≤ c) :
    energy w var θ lam ≤ c ^ 2 / (2 * m) := by
  obtain ⟨hpos, hsum⟩ := hw
  have hterm : ∀ e : Fin 8, w e * (lam e - θ e) ^ 2 / var e ≤ w e * c ^ 2 / m := by
    intro e
    have hve : 0 < var e := lt_of_lt_of_le hm (hv e)
    have hsq : (lam e - θ e) ^ 2 ≤ c ^ 2 := by
      have h0 := hd e
      have h1 := abs_nonneg (lam e - θ e)
      have h2 : (lam e - θ e) ^ 2 = |lam e - θ e| ^ 2 := (sq_abs _).symm
      nlinarith [h0, h1, h2]
    have hnum : w e * (lam e - θ e) ^ 2 ≤ w e * c ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (hpos e)
    refine le_trans (div_le_div_of_nonneg_right hnum hve.le) ?_
    exact div_le_div_of_nonneg_left (mul_nonneg (hpos e) (sq_nonneg c)) hm (hv e)
  have hbig : ∑ e, w e * (lam e - θ e) ^ 2 / var e ≤ ∑ e : Fin 8, w e * c ^ 2 / m :=
    Finset.sum_le_sum fun e _ => hterm e
  have hrhs : ∑ e : Fin 8, w e * c ^ 2 / m = c ^ 2 / m := by
    have hfac : ∑ e : Fin 8, w e * c ^ 2 / m = (∑ e : Fin 8, w e) * (c ^ 2 / m) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [hfac, hsum]; ring
  rw [hrhs] at hbig
  have hmul : (∑ e, w e * (lam e - θ e) ^ 2 / var e) * (2 * m) ≤ c ^ 2 * 2 := by
    have h := mul_le_mul_of_nonneg_right hbig (by linarith : (0:ℝ) ≤ 2 * m)
    have hc : c ^ 2 / m * (2 * m) = c ^ 2 * 2 := by field_simp
    linarith [h, hc.le, hc.ge]
  unfold energy
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by linarith : (0:ℝ) < 2 * m)]
  exact hmul

/-- The uniform allocation, used only to witness that the outer set is nonempty. -/
noncomputable def wUnif : Fin 8 → ℝ := fun _ => 1/8

theorem wUnif_isAlloc : IsAlloc wUnif := by
  refine ⟨fun e => by norm_num [wUnif], ?_⟩
  rw [Fin.sum_univ_eight]; norm_num [wUnif]

/-- **The inner infimum exists**: energies are bounded below by zero. -/
theorem exists_inner_glb (Alt : (Fin 8 → ℝ) → Prop) (w var θ : Fin 8 → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hv : ∀ e, 0 < var e)
    (hne : ∃ lam, Alt lam ∧ InClass lam) :
    ∃ v, IsGLB {u : ℝ | ∃ lam, (Alt lam ∧ InClass lam) ∧ u = energy w var θ lam} v := by
  obtain ⟨lam0, h1, h2⟩ := hne
  refine Real.exists_isGLB ⟨energy w var θ lam0, ⟨lam0, ⟨h1, h2⟩, rfl⟩⟩ ⟨0, ?_⟩
  rintro u ⟨lam, -, rfl⟩
  exact energy_nonneg w var θ lam hw hv

/-- **The game value exists**: the cheap alternative caps every design's inner value. -/
theorem exists_game_lub (Alt : (Fin 8 → ℝ) → Prop) (var θ : Fin 8 → ℝ) (U : ℝ)
    (hv : ∀ e, 0 < var e)
    (hne : ∃ lam, Alt lam ∧ InClass lam)
    (hcheap : ∀ w : Fin 8 → ℝ, IsAlloc w → ∀ ξ : ℝ, 0 < ξ →
      ∃ lam, Alt lam ∧ InClass lam ∧ energy w var θ lam ≤ U + ξ) :
    ∃ Γ, GameLUB Alt var θ Γ := by
  obtain ⟨v0, hv0⟩ := exists_inner_glb Alt wUnif var θ wUnif_isAlloc.1 hv hne
  refine Real.exists_isLUB ⟨v0, ⟨wUnif, wUnif_isAlloc, hv0⟩⟩ ⟨U, ?_⟩
  rintro v ⟨w, hw, hglb⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨lam, ha, hc, hle⟩ := hcheap w hw ((v - U) / 2) (by linarith)
  have hlow : v ≤ energy w var θ lam := hglb.1 ⟨lam, ⟨ha, hc⟩, rfl⟩
  linarith

/-! ### The A-low world, with every hypothesis discharged -/

noncomputable def varLowC (M : ℝ) : Fin 8 → ℝ := fun e => if e = 6 ∨ e = 7 then M else 1

@[simp] theorem varLowC_0 (M : ℝ) : varLowC M 0 = 1 := by simp [varLowC]
@[simp] theorem varLowC_1 (M : ℝ) : varLowC M 1 = 1 := by simp [varLowC]
@[simp] theorem varLowC_2 (M : ℝ) : varLowC M 2 = 1 := by simp [varLowC]
@[simp] theorem varLowC_3 (M : ℝ) : varLowC M 3 = 1 := by simp [varLowC]
@[simp] theorem varLowC_4 (M : ℝ) : varLowC M 4 = 1 := by simp [varLowC]
@[simp] theorem varLowC_5 (M : ℝ) : varLowC M 5 = 1 := by simp [varLowC]
@[simp] theorem varLowC_6 (M : ℝ) : varLowC M 6 = M := by simp [varLowC]
@[simp] theorem varLowC_7 (M : ℝ) : varLowC M 7 = M := by simp [varLowC]

theorem varLowC_pos (M : ℝ) (hM : 0 < M) : ∀ e, 0 < varLowC M e := by
  intro e; unfold varLowC; split_ifs with h
  · exact hM
  · norm_num

theorem varLowC_floor (M : ℝ) (hM : 0 < M) : ∀ e, min 1 M ≤ varLowC M e := by
  intro e; unfold varLowC; split_ifs with h
  · exact min_le_right _ _
  · exact min_le_left _ _

/-- The cheap PROXY alternative at the A-low world: push `A1` down and `A2` up by `1/4`, so
the frozen contrast is met exactly and arm `A`'s total is preserved. -/
noncomputable def lamLowProxy : Fin 8 → ℝ := fun e =>
  if e = 1 then 1/4 else if e = 2 then 1/4 else thetaLowC e

@[simp] theorem lamLowProxy_0 : lamLowProxy 0 = -(1/2) := by simp [lamLowProxy]
@[simp] theorem lamLowProxy_1 : lamLowProxy 1 = 1/4 := by simp [lamLowProxy]
@[simp] theorem lamLowProxy_2 : lamLowProxy 2 = 1/4 := by simp [lamLowProxy]
@[simp] theorem lamLowProxy_3 : lamLowProxy 3 = 0 := by simp [lamLowProxy]
@[simp] theorem lamLowProxy_4 : lamLowProxy 4 = -(7/16) := by simp [lamLowProxy]
@[simp] theorem lamLowProxy_5 : lamLowProxy 5 = 5/16 := by simp [lamLowProxy]
@[simp] theorem lamLowProxy_6 : lamLowProxy 6 = 1/16 := by simp [lamLowProxy]
@[simp] theorem lamLowProxy_7 : lamLowProxy 7 = 1/16 := by simp [lamLowProxy]

theorem lamLowProxy_alt : ProxyAlt lamLowProxy := by unfold ProxyAlt; norm_num

theorem lamLowProxy_inClass : InClass lamLowProxy := by constructor <;> norm_num

theorem lamLowProxy_dev (e : Fin 8) : |lamLowProxy e - thetaLowC e| ≤ 1/4 := by
  have h : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 := by revert e; decide
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [abs_le] <;> norm_num

/-- **Both A-low game values exist, at the concrete centered world.** -/
theorem exists_low_games (M : ℝ) (hM : 0 < M) :
    (∃ Γ, GameLUB StrictTrueAlt (varLowC M) thetaLowC Γ) ∧
    (∃ Γ, GameLUB ProxyAlt (varLowC M) thetaLowC Γ) := by
  have hvpos := varLowC_pos M hM
  constructor
  · refine exists_game_lub StrictTrueAlt (varLowC M) thetaLowC (1 / (8 * M)) hvpos ?_ ?_
    · obtain ⟨lam, hs, hc, -⟩ := low_true_strict_le M hM wUnif (varLowC M) thetaLowC
        wUnif_isAlloc (varLowC_6 M) (varLowC_7 M) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        thetaLowC_inClass 1 one_pos
      exact ⟨lam, hs, hc⟩
    · intro w hw ξ hξ
      exact low_true_strict_le M hM w (varLowC M) thetaLowC hw (varLowC_6 M) (varLowC_7 M)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) thetaLowC_inClass ξ hξ
  · refine exists_game_lub ProxyAlt (varLowC M) thetaLowC
      ((1/4 : ℝ) ^ 2 / (2 * min 1 M)) hvpos
      ⟨lamLowProxy, lamLowProxy_alt, lamLowProxy_inClass⟩ ?_
    intro w hw ξ hξ
    refine ⟨lamLowProxy, lamLowProxy_alt, lamLowProxy_inClass, ?_⟩
    have hb := energy_le_of_dev_bound w (varLowC M) thetaLowC lamLowProxy hw (1/4)
      (min 1 M) (lt_min one_pos hM) (varLowC_floor M hM) lamLowProxy_dev
    linarith

/-! ### The A-high world, with every hypothesis discharged -/

noncomputable def varHighC (M : ℝ) : Fin 8 → ℝ := fun e => if e = 1 ∨ e = 3 then M else 1

@[simp] theorem varHighC_0 (M : ℝ) : varHighC M 0 = 1 := by simp [varHighC]
@[simp] theorem varHighC_1 (M : ℝ) : varHighC M 1 = M := by simp [varHighC]
@[simp] theorem varHighC_2 (M : ℝ) : varHighC M 2 = 1 := by simp [varHighC]
@[simp] theorem varHighC_3 (M : ℝ) : varHighC M 3 = M := by simp [varHighC]
@[simp] theorem varHighC_4 (M : ℝ) : varHighC M 4 = 1 := by simp [varHighC]
@[simp] theorem varHighC_5 (M : ℝ) : varHighC M 5 = 1 := by simp [varHighC]
@[simp] theorem varHighC_6 (M : ℝ) : varHighC M 6 = 1 := by simp [varHighC]
@[simp] theorem varHighC_7 (M : ℝ) : varHighC M 7 = 1 := by simp [varHighC]

theorem varHighC_pos (M : ℝ) (hM : 0 < M) : ∀ e, 0 < varHighC M e := by
  intro e; unfold varHighC; split_ifs with h
  · exact hM
  · norm_num

theorem varHighC_floor (M : ℝ) (hM : 0 < M) : ∀ e, min 1 M ≤ varHighC M e := by
  intro e; unfold varHighC; split_ifs with h
  · exact min_le_right _ _
  · exact min_le_left _ _

/-- The cheap PROXY alternative at the A-high world: lower `A1` and raise `A3` by `1/2`.
It satisfies the frozen contrast exactly, keeps arm `A`'s total at zero -- and does NOT make
arm `A`'s range catch arm `B`'s, which is the whole point of the family. -/
noncomputable def lamHighProxy : Fin 8 → ℝ := fun e =>
  if e = 1 then -(1/16) else if e = 3 then 7/16 else thetaHighC e

@[simp] theorem lamHighProxy_0 : lamHighProxy 0 = -(9/16) := by simp [lamHighProxy]
@[simp] theorem lamHighProxy_1 : lamHighProxy 1 = -(1/16) := by simp [lamHighProxy]
@[simp] theorem lamHighProxy_2 : lamHighProxy 2 = 3/16 := by simp [lamHighProxy]
@[simp] theorem lamHighProxy_3 : lamHighProxy 3 = 7/16 := by simp [lamHighProxy]
@[simp] theorem lamHighProxy_4 : lamHighProxy 4 = -(1/4) := by simp [lamHighProxy]
@[simp] theorem lamHighProxy_5 : lamHighProxy 5 = 1/4 := by simp [lamHighProxy]
@[simp] theorem lamHighProxy_6 : lamHighProxy 6 = 0 := by simp [lamHighProxy]
@[simp] theorem lamHighProxy_7 : lamHighProxy 7 = 0 := by simp [lamHighProxy]

theorem lamHighProxy_alt : ProxyAlt lamHighProxy := by unfold ProxyAlt; norm_num

theorem lamHighProxy_inClass : InClass lamHighProxy := by constructor <;> norm_num

theorem lamHighProxy_d1 : lamHighProxy 1 - thetaHighC 1 = -(1/2) := by norm_num

theorem lamHighProxy_d3 : lamHighProxy 3 - thetaHighC 3 = 1/2 := by norm_num

theorem lamHighProxy_rest : ∀ e : Fin 8, e ≠ 1 → e ≠ 3 → lamHighProxy e = thetaHighC e := by
  intro e h1 h3; simp [lamHighProxy, h1, h3]

/-- A STRICTLY bad world at the A-high table: squeeze arm `A` to range `3/8`, below arm
`B`'s `1/2`, keeping arm `A`'s total at zero.  This is what makes the true game's inner set
nonempty, and it is genuinely expensive because the design measures those cells. -/
noncomputable def lamHighTrue : Fin 8 → ℝ := fun e =>
  if e = 0 then -(3/16) else if e = 1 then 3/16 else if e = 2 then 1/16
  else if e = 3 then -(1/16) else thetaHighC e

@[simp] theorem lamHighTrue_0 : lamHighTrue 0 = -(3/16) := by simp [lamHighTrue]
@[simp] theorem lamHighTrue_1 : lamHighTrue 1 = 3/16 := by simp [lamHighTrue]
@[simp] theorem lamHighTrue_2 : lamHighTrue 2 = 1/16 := by simp [lamHighTrue]
@[simp] theorem lamHighTrue_3 : lamHighTrue 3 = -(1/16) := by simp [lamHighTrue]
@[simp] theorem lamHighTrue_4 : lamHighTrue 4 = -(1/4) := by simp [lamHighTrue]
@[simp] theorem lamHighTrue_5 : lamHighTrue 5 = 1/4 := by simp [lamHighTrue]
@[simp] theorem lamHighTrue_6 : lamHighTrue 6 = 0 := by simp [lamHighTrue]
@[simp] theorem lamHighTrue_7 : lamHighTrue 7 = 0 := by simp [lamHighTrue]

theorem lamHighTrue_alt : StrictTrueAlt lamHighTrue := by
  unfold StrictTrueAlt rangeAof rangeBof rng
  norm_num

theorem lamHighTrue_inClass : InClass lamHighTrue := by constructor <;> norm_num

theorem lamHighTrue_dev (e : Fin 8) : |lamHighTrue e - thetaHighC e| ≤ 3/8 := by
  have h : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 := by revert e; decide
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [abs_le] <;> norm_num

/-- **Both A-high game values exist, at the concrete centered world.** -/
theorem exists_high_games (M : ℝ) (hM : 0 < M) :
    (∃ Γ, GameLUB StrictTrueAlt (varHighC M) thetaHighC Γ) ∧
    (∃ Γ, GameLUB ProxyAlt (varHighC M) thetaHighC Γ) := by
  have hvpos := varHighC_pos M hM
  constructor
  · refine exists_game_lub StrictTrueAlt (varHighC M) thetaHighC
      ((3/8 : ℝ) ^ 2 / (2 * min 1 M)) hvpos
      ⟨lamHighTrue, lamHighTrue_alt, lamHighTrue_inClass⟩ ?_
    intro w hw ξ hξ
    refine ⟨lamHighTrue, lamHighTrue_alt, lamHighTrue_inClass, ?_⟩
    have hb := energy_le_of_dev_bound w (varHighC M) thetaHighC lamHighTrue hw (3/8)
      (min 1 M) (lt_min one_pos hM) (varHighC_floor M hM) lamHighTrue_dev
    linarith
  · refine exists_game_lub ProxyAlt (varHighC M) thetaHighC (1 / (8 * M)) hvpos
      ⟨lamHighProxy, lamHighProxy_alt, lamHighProxy_inClass⟩ ?_
    intro w hw ξ hξ
    refine ⟨lamHighProxy, lamHighProxy_alt, lamHighProxy_inClass, ?_⟩
    have hb := high_proxy_le M hM w (varHighC M) thetaHighC lamHighProxy hw hvpos
      (varHighC_1 M) (varHighC_3 M) lamHighProxy_d1 lamHighProxy_d3 lamHighProxy_rest
    linarith

/-! ### The separation, at worlds that exist

These are the headline statements with NO hypothesis left on the world: the world is named,
the variances are named, and the only remaining inputs are the two game values and the inner
infimum, whose existence the two theorems above supply. -/

/-- **A-low at the concrete centered world.** -/
theorem low_separation_at_world (M : ℝ) (hM : 0 < M) (Γtrue Γproxy v₀ : ℝ)
    (hT : GameLUB StrictTrueAlt (varLowC M) thetaLowC Γtrue)
    (hP : GameLUB ProxyAlt (varLowC M) thetaLowC Γproxy)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, (ProxyAlt lam ∧ InClass lam)
      ∧ u = energy wLowStar (varLowC M) thetaLowC lam} v₀)
    (hPpos : 0 < Γproxy) :
    Γtrue / Γproxy ≤ 64 / M :=
  family_low_separation_class M hM (varLowC M) thetaLowC (varLowC_pos M hM)
    (varLowC_6 M) (varLowC_7 M) (varLowC_0 M) (varLowC_1 M) (varLowC_4 M) (varLowC_5 M)
    thetaLowC_inClass (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Γtrue Γproxy hT hP v₀ hv₀ hPpos

/-- **A-high at the concrete centered world.** -/
theorem high_separation_at_world (M : ℝ) (hM : 0 < M) (Γtrue Γproxy v₀ : ℝ)
    (hT : GameLUB StrictTrueAlt (varHighC M) thetaHighC Γtrue)
    (hP : GameLUB ProxyAlt (varHighC M) thetaHighC Γproxy)
    (hv₀ : IsGLB {u : ℝ | ∃ lam, (StrictTrueAlt lam ∧ InClass lam)
      ∧ u = energy wHighStar (varHighC M) thetaHighC lam} v₀)
    (hPpos : 0 < Γproxy) :
    M / 96 ≤ Γtrue / Γproxy :=
  family_high_separation_class M hM (varHighC M) thetaHighC (varHighC_pos M hM)
    (varHighC_1 M) (varHighC_3 M) (varHighC_0 M) (varHighC_2 M) (varHighC_4 M)
    (varHighC_5 M) (varHighC_6 M) (varHighC_7 M)
    (by norm_num) (by unfold rangeBof rng; norm_num)
    lamHighProxy lamHighProxy_alt lamHighProxy_inClass
    lamHighProxy_d1 lamHighProxy_d3 lamHighProxy_rest
    Γtrue Γproxy hT hP v₀ hv₀ hPpos

/-! ## Realizability: the tables are response tables of a genuine additive world -/

/-- For an additive world over a uniform reference, the product response at a coordinate is
that coordinate's table plus a constant. -/
theorem additive_response_shift (QA QB : Fin 4 → ℝ) (u : Fin 4) :
    (∑ b : Fin 4, (1/4 : ℝ) * (QA u + QB b)) = QA u + (∑ b : Fin 4, (1/4 : ℝ) * QB b) := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  ring

/-- A constant shift leaves the range unchanged, which is why centring the tables -- the
step that makes them valid zero-mean responses -- changes nothing the decision can see. -/
theorem rng_shift_invariant (a b c e k : ℝ) :
    rng (a + k) (b + k) (c + k) (e + k) = rng a b c e := by
  unfold rng
  simp only [max_add_add_right, min_add_add_right]
  ring

/-! ## Audit -/

#print axioms cs_two
#print axioms cs_four
#print axioms energy_expand
#print axioms altLow_is_true_alt
#print axioms low_true_le
#print axioms shifted_is_strict
#print axioms shifted_energy_le
#print axioms low_true_strict_le
#print axioms wLowStar_isAlloc
#print axioms low_proxy_ge
#print axioms game_le_of_forall_design
#print axioms game_ge_of_exists_design
#print axioms low_true_game_le
#print axioms low_proxy_game_ge
#print axioms high_proxy_game_le
#print axioms high_true_game_ge
#print axioms family_low_ratio_le
#print axioms altHigh_is_proxy_alt
#print axioms high_proxy_le
#print axioms wHighStar_isAlloc
#print axioms max4_witness
#print axioms min4_witness
#print axioms max4_le_add
#print axioms min4_ge_add
#print axioms rng_move_pairwise
#print axioms two_distinct_sq_le
#print axioms six_norm_lower
#print axioms rangeAof_ge_pair
#print axioms high_true_ge
#print axioms family_high_ratio_ge
#print axioms family_low_separation
#print axioms family_high_separation
#print axioms InClass
#print axioms game_le_of_forall_design_eps
#print axioms game_ge_of_exists_design_class
#print axioms low_true_class_le
#print axioms low_proxy_class_ge
#print axioms high_true_class_ge
#print axioms high_proxy_class_le
#print axioms family_low_separation_class
#print axioms family_high_separation_class
#print axioms no_constant_factor_on_families
#print axioms no_constant_factor_after_sup
#print axioms no_constant_factor_guarantee
#print axioms shiftArms_A
#print axioms shiftArms_B
#print axioms rng_sub_const
#print axioms rangeAof_shiftArms
#print axioms rangeBof_shiftArms
#print axioms trueAlt_shiftArms
#print axioms strictTrueAlt_shiftArms
#print axioms proxyAlt_shiftArms
#print axioms energy_shiftArms
#print axioms inClass_center
#print axioms thetaLowC_eq_centered_raw
#print axioms thetaHighC_eq_centered_raw
#print axioms thetaLowC_inClass
#print axioms thetaHighC_inClass
#print axioms low_world_hypotheses_consistent
#print axioms high_world_hypotheses_consistent
#print axioms shifted_is_strict_centered
#print axioms energy_nonneg
#print axioms energy_le_of_dev_bound
#print axioms wUnif_isAlloc
#print axioms exists_inner_glb
#print axioms exists_game_lub
#print axioms strictTrueAlt_shiftArms
#print axioms varLowC_pos
#print axioms varLowC_floor
#print axioms lamLowProxy_alt
#print axioms lamLowProxy_inClass
#print axioms lamLowProxy_dev
#print axioms exists_low_games
#print axioms varHighC_pos
#print axioms varHighC_floor
#print axioms lamHighProxy_alt
#print axioms lamHighProxy_inClass
#print axioms lamHighTrue_alt
#print axioms lamHighTrue_inClass
#print axioms lamHighTrue_dev
#print axioms exists_high_games
#print axioms low_separation_at_world
#print axioms high_separation_at_world
#print axioms additive_response_shift
#print axioms rng_shift_invariant

end CIGAMF.P13.PaperASeparation
