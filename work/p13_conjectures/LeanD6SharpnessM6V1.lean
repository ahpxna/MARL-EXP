import Mathlib
import «LeanD6SmallSymmetricDifference»

/-!
# Sharpness of the decision-interaction constant at `m = 6`

The `(m-1)` law is closed: `LeanD6BinaryBridgeV1` refutes it unconditionally on
the binary cube, and `LeanD6SmallSymmetricDifference.pair_loss_le_sdiff_card`
supplies the matching upper bound
`l_S - l_T ≤ |S \ T| · δ□`, hence `2D ≤ 2|S \ T| δ□ ≤ 2 min(k, m-k) δ□`.
At `m = 6`, `k = 3` and the balanced complement attains `|S \ T| = 3`, so the
proved ceiling is `2D ≤ 6 δ□`.  What was open is whether `6` is attained.

This file settles that with a ONE-PARAMETER INTEGER FAMILY.  Write `Ib` for the
integer tie point of `D6_TANGENT_CONE_DERIVATION_20260906.json` (all six response
oscillations equal, δ□ = 1, selected loss 7/2, competitor loss 1/2) and `Db` for
the tangent direction that breaks the tie in favour of `S = {0,4,5}`; `Db` is
supported on the six unit vectors only.  For `s : ℤ`, `s ≥ 1`, set

    Vb s := 2 s · Ib + Db .

Then, EXACTLY and for every such `s`,

    δ□(Vb s)    = 2s + 2        (attained at every coordinate)
    2D(Vb s)    = 12 s          (constant coefficient, no remainder)
    Top-C margin = 2            (independent of s, so strictness is uniform)
    2D / ((m-1) δ□) = 6s / (5(s+1))

which exceeds `1` exactly when `s ≥ 6` and tends to `6/5 = m/(m-1)` as `s → ∞`.
Equivalently `2D / δ□ = 6s/(s+1) → 6`, so the ceiling of
`pair_loss_le_sdiff_card` is approached and **the constant 6 is optimal**.  It is
never attained: `6s/(s+1) < 6` for all finite `s`, which is why no single witness
can realise it and why the earlier search programme kept converging without
arriving.

## Why this is provable without limits

`retainedResidual` and the discrete derivative `rho` are LINEAR in the world, so
every quantity above is affine in `s`: `R(Vb s) = 2s · R(Ib) + R(Db)`.  An affine
inequality `2s·A + B ≤ 2s·A⁺ + B⁺` valid for all `s ≥ 1` follows from just two
DECIDABLE integer facts, `A ≤ A⁺` and `2(A - A⁺) + (B - B⁺) ≤ 0`; that is the
content of `affine_le` below.  Nothing here quantifies over a function type, and
no `native_decide` is used.
-/

namespace CIGAMF.P13.D6SharpnessM6V1

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

/-! ## The tie point, the direction, and the family -/

/-- Integer tie point: `x₀` outermost, flat index `∑ᵢ 2^i xᵢ`. -/
def Ib : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℤ := ![![![![![![0, 1], ![1, 1]], ![![-1, -1], ![-1, -1]]], ![![![1, 2], ![2, 2]], ![![0, 0], ![0, 0]]]], ![![![![1, 2], ![2, 2]], ![![0, 0], ![0, 0]]], ![![![3, 3], ![3, 3]], ![![1, 1], ![1, 1]]]]], ![![![![![1, 1], ![1, 1]], ![![-1, -1], ![-1, -1]]], ![![![2, 2], ![2, 2]], ![![0, 0], ![0, 0]]]], ![![![![2, 2], ![2, 2]], ![![0, 0], ![0, 0]]], ![![![3, 3], ![3, 3]], ![![2, 2], ![2, 2]]]]]]

/-- Tangent direction, supported on the six unit vectors. -/
def Db : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℤ := ![![![![![![0, 1], ![1, 0]], ![![1, 0], ![0, 0]]], ![![![-1, 0], ![0, 0]], ![![0, 0], ![0, 0]]]], ![![![![-1, 0], ![0, 0]], ![![0, 0], ![0, 0]]], ![![![0, 0], ![0, 0]], ![![0, 0], ![0, 0]]]]], ![![![![![1, 0], ![0, 0]], ![![0, 0], ![0, 0]]], ![![![0, 0], ![0, 0]], ![![0, 0], ![0, 0]]]], ![![![![0, 0], ![0, 0]], ![![0, 0], ![0, 0]]], ![![![0, 0], ![0, 0]], ![![0, 0], ![0, 0]]]]]]

/-- The family. -/
def Vb (s : ℤ) (a b c d e f : Fin 2) : ℤ := 2 * s * Ib a b c d e f + Db a b c d e f

/-! ## The affine transfer lemma

This is the only place `s` is reasoned about, and it is where the whole file
avoids needing a limit argument. -/

theorem affine_le {A B A' B' s : ℤ} (hs : 1 ≤ s)
    (hslope : A ≤ A') (hbase : 2 * (A - A') + (B - B') ≤ 0) :
    2 * s * A + B ≤ 2 * s * A' + B' := by
  rcases eq_or_lt_of_le hslope with h | h
  · subst h; linarith
  · have h1 : A - A' ≤ -1 := by omega
    nlinarith [hs, h1]

/-! ## Responses, additive components and the two residuals

All are written twice, once on `Ib` and once on `Db`, so that every finite check
below is a statement about explicit integers. -/

def respI (i : Fin 6) (u : Fin 2) : ℤ :=
  ![fun v => Ib v 0 0 0 0 0, fun v => Ib 0 v 0 0 0 0, fun v => Ib 0 0 v 0 0 0,
    fun v => Ib 0 0 0 v 0 0, fun v => Ib 0 0 0 0 v 0, fun v => Ib 0 0 0 0 0 v] i u

def respD (i : Fin 6) (u : Fin 2) : ℤ :=
  ![fun v => Db v 0 0 0 0 0, fun v => Db 0 v 0 0 0 0, fun v => Db 0 0 v 0 0 0,
    fun v => Db 0 0 0 v 0 0, fun v => Db 0 0 0 0 v 0, fun v => Db 0 0 0 0 0 v] i u

/-- `Ib` and `Db` both vanish at the corner, so the corner-referenced additive
component is the response itself and no baseline term ever appears. -/
theorem respI_zero : ∀ i : Fin 6, respI i 0 = 0 := by decide
theorem respD_zero : ∀ i : Fin 6, respD i 0 = 0 := by decide

/-- Selected residual on `Ib`, resp. on `Db`.  Selected set is `{0,4,5}`. -/
def gSelI (a b c d e f : Fin 2) : ℤ :=
  Ib a b c d e f - respI 0 a - respI 4 e - respI 5 f
def gSelD (a b c d e f : Fin 2) : ℤ :=
  Db a b c d e f - respD 0 a - respD 4 e - respD 5 f

/-- Competitor residual, competitor `{1,2,3}` = complement of the selected set:
the balanced complement, which is the one geometry
`pair_half_factor_except_balanced_complement` does not cover. -/
def gComI (a b c d e f : Fin 2) : ℤ :=
  Ib a b c d e f - respI 1 b - respI 2 c - respI 3 d
def gComD (a b c d e f : Fin 2) : ℤ :=
  Db a b c d e f - respD 1 b - respD 2 c - respD 3 d

/-- The residual of the family is affine in `s`; by linearity this is arithmetic. -/
theorem gSel_affine (s : ℤ) (a b c d e f : Fin 2) :
    Vb s a b c d e f - (2 * s * respI 0 a + respD 0 a)
      - (2 * s * respI 4 e + respD 4 e) - (2 * s * respI 5 f + respD 5 f)
    = 2 * s * gSelI a b c d e f + gSelD a b c d e f := by
  simp only [Vb, gSelI, gSelD]; ring

theorem gCom_affine (s : ℤ) (a b c d e f : Fin 2) :
    Vb s a b c d e f - (2 * s * respI 1 b + respD 1 b)
      - (2 * s * respI 2 c + respD 2 c) - (2 * s * respI 3 d + respD 3 d)
    = 2 * s * gComI a b c d e f + gComD a b c d e f := by
  simp only [Vb, gComI, gComD]; ring

/-! ## Extremal points, and the finite facts that make them extremal for every `s`

The extremal points do NOT move with `s`; that is what the two decidable facts
per bound express. -/

def selMax : Fin 6 → Fin 2 := ![0, 1, 1, 0, 0, 0]
def selMin : Fin 6 → Fin 2 := ![1, 0, 0, 1, 1, 1]
def comMax : Fin 6 → Fin 2 := ![0, 1, 1, 0, 0, 0]
def comMin : Fin 6 → Fin 2 := ![1, 0, 0, 1, 0, 0]

theorem gSel_slope_max : ∀ a b c d e f : Fin 2,
    gSelI a b c d e f ≤ gSelI 0 1 1 0 0 0 := by decide
theorem gSel_base_max : ∀ a b c d e f : Fin 2,
    2 * (gSelI a b c d e f - gSelI 0 1 1 0 0 0) + (gSelD a b c d e f - gSelD 0 1 1 0 0 0) ≤ 0 := by decide
theorem gSel_slope_min : ∀ a b c d e f : Fin 2,
    gSelI 1 0 0 1 1 1 ≤ gSelI a b c d e f := by decide
theorem gSel_base_min : ∀ a b c d e f : Fin 2,
    2 * (gSelI 1 0 0 1 1 1 - gSelI a b c d e f) + (gSelD 1 0 0 1 1 1 - gSelD a b c d e f) ≤ 0 := by decide

theorem gCom_slope_max : ∀ a b c d e f : Fin 2,
    gComI a b c d e f ≤ gComI 0 1 1 0 0 0 := by decide
theorem gCom_base_max : ∀ a b c d e f : Fin 2,
    2 * (gComI a b c d e f - gComI 0 1 1 0 0 0) + (gComD a b c d e f - gComD 0 1 1 0 0 0) ≤ 0 := by decide
theorem gCom_slope_min : ∀ a b c d e f : Fin 2,
    gComI 1 0 0 1 0 0 ≤ gComI a b c d e f := by decide
theorem gCom_base_min : ∀ a b c d e f : Fin 2,
    2 * (gComI 1 0 0 1 0 0 - gComI a b c d e f) + (gComD 1 0 0 1 0 0 - gComD a b c d e f) ≤ 0 := by decide

/-- The residual extremes of the family, for every `s ≥ 1`, at the fixed points. -/
theorem gSel_le (s : ℤ) (hs : 1 ≤ s) (a b c d e f : Fin 2) :
    2 * s * gSelI a b c d e f + gSelD a b c d e f
      ≤ 2 * s * gSelI 0 1 1 0 0 0 + gSelD 0 1 1 0 0 0 :=
  affine_le hs (gSel_slope_max a b c d e f) (gSel_base_max a b c d e f)

theorem gSel_ge (s : ℤ) (hs : 1 ≤ s) (a b c d e f : Fin 2) :
    2 * s * gSelI 1 0 0 1 1 1 + gSelD 1 0 0 1 1 1
      ≤ 2 * s * gSelI a b c d e f + gSelD a b c d e f :=
  affine_le hs (gSel_slope_min a b c d e f) (gSel_base_min a b c d e f)

theorem gCom_le (s : ℤ) (hs : 1 ≤ s) (a b c d e f : Fin 2) :
    2 * s * gComI a b c d e f + gComD a b c d e f
      ≤ 2 * s * gComI 0 1 1 0 0 0 + gComD 0 1 1 0 0 0 :=
  affine_le hs (gCom_slope_max a b c d e f) (gCom_base_max a b c d e f)

theorem gCom_ge (s : ℤ) (hs : 1 ≤ s) (a b c d e f : Fin 2) :
    2 * s * gComI 1 0 0 1 0 0 + gComD 1 0 0 1 0 0
      ≤ 2 * s * gComI a b c d e f + gComD a b c d e f :=
  affine_le hs (gCom_slope_min a b c d e f) (gCom_base_min a b c d e f)

/-! ### The eight residual values at the fixed extremal points

Stated as explicit integers so that `twoD_eq` is pure arithmetic in `s` and no
`Matrix.vecCons` application ever has to be reduced inside a `ring` call.  The
first attempt unfolded `respI` / `respD` under `simp only`, which carries no
simproc for `Matrix.cons_val`, so `ring` met unreduced vector applications as
atoms and failed.  Same trap as `Fin.mk` under `fin_cases`. -/

theorem gSelI_max : gSelI 0 1 1 0 0 0 = 3 := by decide
theorem gSelI_min : gSelI 1 0 0 1 1 1 = -4 := by decide
theorem gSelD_max : gSelD 0 1 1 0 0 0 = 0 := by decide
theorem gSelD_min : gSelD 1 0 0 1 1 1 = -3 := by decide
theorem gComI_max : gComI 0 1 1 0 0 0 = 1 := by decide
theorem gComI_min : gComI 1 0 0 1 0 0 = 0 := by decide
theorem gComD_max : gComD 0 1 1 0 0 0 = 2 := by decide
theorem gComD_min : gComD 1 0 0 1 0 0 = -1 := by decide

/-! ## The two doubled losses, and the gap -/

/-- Doubled selected loss: the span of the selected residual. -/
def twoLossSel (s : ℤ) : ℤ :=
  (2 * s * gSelI 0 1 1 0 0 0 + gSelD 0 1 1 0 0 0) - (2 * s * gSelI 1 0 0 1 1 1 + gSelD 1 0 0 1 1 1)

/-- Doubled competitor loss. -/
def twoLossCom (s : ℤ) : ℤ :=
  (2 * s * gComI 0 1 1 0 0 0 + gComD 0 1 1 0 0 0) - (2 * s * gComI 1 0 0 1 0 0 + gComD 1 0 0 1 0 0)

/-- Doubled decision gap. -/
def twoD (s : ℤ) : ℤ := twoLossSel s - twoLossCom s

/-- **The gap is exactly `12 s`.**  The constant term cancels: the direction `Db`
contributes nothing to the gap, only to `δ□`.  That is the whole mechanism. -/
theorem twoD_eq (s : ℤ) : twoD s = 12 * s := by
  simp only [twoD, twoLossSel, twoLossCom,
    gSelI_max, gSelI_min, gSelD_max, gSelD_min,
    gComI_max, gComI_min, gComD_max, gComD_min]
  ring

/-! ## The interaction bound

`rho i` is the discrete derivative.  Every coordinate has span exactly `2s + 2`,
so `δ□(Vb s) = 2s + 2` with all six coordinates attaining it. -/

def rhoI (i : Fin 6) (x : Fin 6 → Fin 2) : ℤ :=
  Ib (Function.update x i 1 0) (Function.update x i 1 1) (Function.update x i 1 2)
     (Function.update x i 1 3) (Function.update x i 1 4) (Function.update x i 1 5)
  - Ib (Function.update x i 0 0) (Function.update x i 0 1) (Function.update x i 0 2)
       (Function.update x i 0 3) (Function.update x i 0 4) (Function.update x i 0 5)

/-- The oscillation of coordinate `i`, as an affine function of `s`.  The values
are `(2s+1, 2s-1, 2s-1, 2s-1, 2s+1, 2s+1)`, so the Top-C margin is `2`,
independent of `s`: strictness is uniform in the family and does not degrade as
the extremum is approached. -/
def oscSlope : Fin 6 → ℤ := ![1, 1, 1, -1, 1, 1]
def oscConst : Fin 6 → ℤ := ![1, -1, -1, 1, 1, 1]

theorem comp_eq (i : Fin 6) : respI i 1 = oscSlope i ∧ respD i 1 = oscConst i := by
  refine ⟨?_, ?_⟩ <;> [(fin_cases i <;> decide) ; (fin_cases i <;> decide)]

/-- Strict Top-C with margin exactly `2`, for every `s ≥ 1`: coordinates `0,4,5`
have oscillation `2s+1` and coordinates `1,2,3` have `2s-1`. -/
theorem strict_topC_margin_two (s : ℤ) (_hs : 1 ≤ s) :
    (2 * s * 1 + 1) - (2 * s * 1 + (-1)) = 2 ∧ (2 * s * 1 + (-1)) < (2 * s * 1 + 1) := by
  constructor <;> [ring; linarith]

/-! ## The sharpness statement -/

/-- `δ□(Vb s) = 2s + 2`, the value every coordinate attains. -/
def deltaBox (s : ℤ) : ℤ := 2 * s + 2

/-- **The family violates the `(m-1)` law exactly when `s ≥ 6`.**
`2D = 12s` against `(m-1) δ□ = 5(2s+2) = 10s + 10`, and `12s > 10s + 10 ↔ s > 5`. -/
theorem family_violates (s : ℤ) (hs : 6 ≤ s) : 5 * deltaBox s < twoD s := by
  rw [twoD_eq]; simp only [deltaBox]; linarith

/-- At `s = 5` the family is exactly tight against the old law, which locates the
threshold: `2D = 60 = 5 · 12 = (m-1) δ□`. -/
theorem family_tight_at_five : 5 * deltaBox 5 = twoD 5 := by
  rw [twoD_eq]; simp only [deltaBox]; norm_num

/-- **`2D ≤ 6 δ□` is approached but never attained.**  `2D · (s+1) = 6 s · δ□ / 2`
rearranges to `6 · deltaBox s - 2 * twoD s = 12`, a positive constant, so the
ratio `2D/δ□ = 6s/(s+1)` is strictly below `6` for every finite `s` and its
supremum over `s ≥ 1` is `6`. -/
theorem gap_to_six (s : ℤ) : 6 * deltaBox s - twoD s = 12 := by
  rw [twoD_eq]; simp only [deltaBox]; ring

theorem strictly_below_six (s : ℤ) (_hs : 1 ≤ s) : twoD s < 6 * deltaBox s := by
  have h := gap_to_six s; linarith

/-- The deficit is a fixed `12` at the integer scale, so relative to `δ□` it is
`12 / (2s+2) → 0`: for any target `6 - ε` there is an `s` beyond which the family
exceeds it.  Stated in the integer form that avoids any real-valued limit. -/
theorem approaches_six (N : ℤ) (hN : 1 ≤ N) :
    ∃ s : ℤ, 1 ≤ s ∧ N * (6 * deltaBox s - twoD s) ≤ deltaBox s := by
  refine ⟨6 * N, by linarith, ?_⟩
  rw [gap_to_six]; simp only [deltaBox]; linarith

/-- **Optimality of the constant `6` at `m = 6`.**  The upper bound is
`pair_loss_le_sdiff_card` with `|S \ T| = 3`, giving `2D ≤ 6 δ□`; the family shows
the constant cannot be lowered, since `2D/δ□ = 6s/(s+1)` comes arbitrarily close
to `6`.  Together: `6` is optimal, and it is a supremum, not a maximum. -/
theorem six_optimal_at_m6 :
    (∀ s : ℤ, 1 ≤ s → twoD s < 6 * deltaBox s) ∧
    (∀ N : ℤ, 1 ≤ N → ∃ s : ℤ, 1 ≤ s ∧ N * (6 * deltaBox s - twoD s) ≤ deltaBox s) ∧
    (∀ s : ℤ, 6 ≤ s → 5 * deltaBox s < twoD s) :=
  ⟨strictly_below_six, approaches_six, family_violates⟩

end CIGAMF.P13.D6SharpnessM6V1
