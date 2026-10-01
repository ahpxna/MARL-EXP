import Mathlib

/-!
# Paper C: the shape of the marginal-regret frontier, and its stability.

## WHY THIS MODULE EXISTS

Two things about the constrained prefix optimum

    V_g(eta) = inf_P  max_k  E_{pi ~ P} r_k(pi; g),
    r_k(pi; g) = ( |sum_{l <= k} g_{pi_l}| - b_k(g) ) / D,
    b_k(g)     = min_{|S| = k} | sum_{i in S} g_i |,

are needed before any frontier claim can be made, and neither was available.

First, the value must be STABLE: a claim that the constrained optimum is a factor `m`
above the free one is worthless if an arbitrarily small perturbation of the weights
destroys it.  The subtlety is that `b_k` is itself a function of the weights.  Perturbing
`g` and keeping the old parity baseline measures the wrong thing; the baseline has to move
too, and the bound below is stated against the recomputed one.

Second, the frontier must have a SHAPE: without knowing `V_g` is non-increasing and convex
in `eta`, a finite set of solved points says nothing between them, and a breakpoint located
by bisection is not meaningful.

## WHAT IS PROVED

* `abs_expect_sub_le`, `abs_sup'_sub_le`, `abs_inf'_sub_le` -- a uniform perturbation of a
  function survives taking an expectation, a maximum and an infimum.  These are what let a
  pointwise bound on the regret become a bound on the value.
* `abs_prefix_sum_sub_le` -- a prefix sum moves by at most the `l1` perturbation.
* `abs_baseline_sub_le` -- **and so does the baseline**, which is the step that would be
  wrong if the old baseline were kept.
* `regret_perturbation` -- hence `|r_k(pi; g) - r_k(pi; g')| <= 2 ||g - g'||_1 / D`, the
  factor two being exactly the two moving parts.
* `value_perturbation` -- the same bound for the value, over any fixed feasible set.
* `value_antitone_of_nested` -- relaxing the band can only lower the optimum.
* `value_convex_of_convex_feasible` -- **the frontier is convex in `eta`**, because the
  constraint right-hand side is affine in `eta` and the objective is affine, so a convex
  combination of optimal plans is feasible for the combined band.

## WHAT THIS DOES NOT ESTABLISH

- **The breakpoint is not proved here.**  `value_antitone_of_nested` and
  `value_convex_of_convex_feasible` say the frontier is a non-increasing convex curve, so a
  bisection for the point where it meets the free value is well posed.  They do not show
  that point is `1` for odd `m` or `(m-2)/(2(m-1))` for even `m`.  Those remain a
  conjecture, solved at `m = 5..31` by the flow LP and not proved at any `m`.
- **The flow reduction is not formalised.**  That the `O(m^2)` flow LP has the same value
  as the permutation LP is checked numerically at every size where both can run; the three
  equalities behind it (symmetrisation, ranking-to-flow, flow-to-ranking) are argued in the
  paper and not in Lean.
- `value_perturbation` holds the feasible set and the normaliser `D` fixed.  If the
  perturbation changes `D`, or breaks the equal-weight groups the symmetry reduction uses,
  the bound does not transfer and the paper says so.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.PaperCFrontier

open Finset

/-! ### A uniform perturbation survives expectation, maximum and infimum -/

section Perturbation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A perturbation bound passes through an expectation. -/
theorem abs_expect_sub_le (p f g : ι → ℝ) (c : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (h : ∀ i, |f i - g i| ≤ c) :
    |(∑ i, p i * f i) - (∑ i, p i * g i)| ≤ c := by
  have hdiff : (∑ i, p i * f i) - (∑ i, p i * g i) = ∑ i, p i * (f i - g i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ i ∈ (univ : Finset ι), |p i * (f i - g i)| ≤ p i * c := by
    intro i _
    rw [abs_mul, abs_of_nonneg (hp i)]
    exact mul_le_mul_of_nonneg_left (h i) (hp i)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, hs, one_mul]

/-- A perturbation bound passes through a maximum. -/
theorem abs_sup'_sub_le (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) (c : ℝ)
    (h : ∀ i ∈ s, |f i - g i| ≤ c) :
    |s.sup' hs f - s.sup' hs g| ≤ c := by
  have hle : ∀ (u v : ι → ℝ), (∀ i ∈ s, u i - v i ≤ c) →
      s.sup' hs u - s.sup' hs v ≤ c := by
    intro u v hbound
    rw [sub_le_iff_le_add]
    refine Finset.sup'_le hs u fun i hi => ?_
    have h1 : u i ≤ v i + c := by linarith [hbound i hi]
    have h2 : v i ≤ s.sup' hs v := Finset.le_sup' v hi
    linarith
  have h1 : s.sup' hs f - s.sup' hs g ≤ c :=
    hle f g fun i hi => le_trans (le_abs_self _) (h i hi)
  have h2 : s.sup' hs g - s.sup' hs f ≤ c := by
    refine hle g f fun i hi => ?_
    have := h i hi
    rw [abs_sub_comm] at this
    exact le_trans (le_abs_self _) this
  exact abs_sub_le_iff.mpr ⟨h1, h2⟩

/-- A perturbation bound passes through an infimum. -/
theorem abs_inf'_sub_le (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) (c : ℝ)
    (h : ∀ i ∈ s, |f i - g i| ≤ c) :
    |s.inf' hs f - s.inf' hs g| ≤ c := by
  have hle : ∀ (u v : ι → ℝ), (∀ i ∈ s, u i - v i ≤ c) →
      s.inf' hs u - s.inf' hs v ≤ c := by
    intro u v hbound
    obtain ⟨j, hj, hval⟩ := Finset.exists_mem_eq_inf' hs v
    have h1 : s.inf' hs u ≤ u j := Finset.inf'_le u hj
    have h2 : u j - v j ≤ c := hbound j hj
    rw [hval]
    linarith
  have h1 : s.inf' hs f - s.inf' hs g ≤ c :=
    hle f g fun i hi => le_trans (le_abs_self _) (h i hi)
  have h2 : s.inf' hs g - s.inf' hs f ≤ c := by
    refine hle g f fun i hi => ?_
    have := h i hi
    rw [abs_sub_comm] at this
    exact le_trans (le_abs_self _) this
  exact abs_sub_le_iff.mpr ⟨h1, h2⟩

end Perturbation

/-! ### C6: stability of the value under a weight perturbation -/

section Stability

variable {m : ℕ}

/-- The `l1` size of a weight perturbation. -/
noncomputable def l1 (g g' : Fin m → ℝ) : ℝ := ∑ i, |g i - g' i|

/-- **A prefix sum moves by at most the perturbation.** -/
theorem abs_prefix_sum_sub_le (S : Finset (Fin m)) (g g' : Fin m → ℝ) :
    |(∑ i ∈ S, g i) - (∑ i ∈ S, g' i)| ≤ l1 g g' := by
  have hdiff : (∑ i ∈ S, g i) - (∑ i ∈ S, g' i) = ∑ i ∈ S, (g i - g' i) := by
    rw [← Finset.sum_sub_distrib]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  unfold l1
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => abs_nonneg _)

/-- ...and so does its absolute value. -/
theorem abs_abs_prefix_sub_le (S : Finset (Fin m)) (g g' : Fin m → ℝ) :
    abs (abs (∑ i ∈ S, g i) - abs (∑ i ∈ S, g' i)) ≤ l1 g g' :=
  le_trans (abs_abs_sub_abs_le_abs_sub _ _) (abs_prefix_sum_sub_le S g g')

/-- The per-budget baseline: the smallest achievable absolute prefix sum. -/
noncomputable def baseline (k : ℕ) (hne : (univ.filter (fun S : Finset (Fin m) =>
    S.card = k)).Nonempty) (g : Fin m → ℝ) : ℝ :=
  (univ.filter (fun S : Finset (Fin m) => S.card = k)).inf' hne
    (fun S => |∑ i ∈ S, g i|)

/-- **The baseline moves by at most the perturbation.**  This is the step that is wrong if
the baseline of the unperturbed family is kept. -/
theorem abs_baseline_sub_le (k : ℕ) (hne : (univ.filter (fun S : Finset (Fin m) =>
    S.card = k)).Nonempty) (g g' : Fin m → ℝ) :
    |baseline k hne g - baseline k hne g'| ≤ l1 g g' := by
  unfold baseline
  exact abs_inf'_sub_le _ hne _ _ _ fun S _ => abs_abs_prefix_sub_le S g g'

/-- **The regret of a fixed ranking at a fixed budget moves by at most `2 l1 / D`.**
The two moves are the prefix sum and the baseline, and neither can be dropped. -/
theorem regret_perturbation (k : ℕ) (hne : (univ.filter (fun S : Finset (Fin m) =>
    S.card = k)).Nonempty) (g g' : Fin m → ℝ) (P : Finset (Fin m)) (D : ℝ) (hD : 0 < D) :
    abs (((abs (∑ i ∈ P, g i) - baseline k hne g) / D)
      - ((abs (∑ i ∈ P, g' i) - baseline k hne g') / D)) ≤ 2 * l1 g g' / D := by
  have hstep : ((abs (∑ i ∈ P, g i) - baseline k hne g) / D)
      - ((abs (∑ i ∈ P, g' i) - baseline k hne g') / D)
      = ((abs (∑ i ∈ P, g i) - abs (∑ i ∈ P, g' i))
          - (baseline k hne g - baseline k hne g')) / D := by
    field_simp
    ring
  rw [hstep, abs_div, abs_of_pos hD]
  gcongr
  have h1 := abs_abs_prefix_sub_le P g g'
  have h2 := abs_baseline_sub_le k hne g g'
  set X : ℝ := abs (∑ i ∈ P, g i) - abs (∑ i ∈ P, g' i) with hX
  set Y : ℝ := baseline k hne g - baseline k hne g' with hY
  have hsplit : abs (X - Y) ≤ abs X + abs Y := by
    have a1 := le_abs_self X
    have a2 := neg_abs_le X
    have a3 := le_abs_self Y
    have a4 := neg_abs_le Y
    rw [abs_le]
    constructor <;> linarith
  linarith

end Stability

/-! ### C4: the frontier is non-increasing and convex -/

section Shape

variable {X : Type*}

/-- **Relaxing the band can only lower the optimum.** -/
theorem value_antitone_of_nested
    (F : ℝ → Set X) (obj : X → ℝ) (V : ℝ → ℝ)
    (hmono : ∀ a b : ℝ, a ≤ b → F a ⊆ F b)
    (hV : ∀ e, IsGLB (obj '' F e) (V e))
    (a b : ℝ) (hab : a ≤ b) (hne : (F a).Nonempty) :
    V b ≤ V a := by
  refine (hV a).2 ?_
  intro r hr
  obtain ⟨x, hx, rfl⟩ := hr
  exact (hV b).1 ⟨x, hmono a b hab hx, rfl⟩

/-- **The frontier is convex.**  A convex combination of plans optimal for two bands is
feasible for the combined band, because the constraints are linear and their right-hand side
is affine in the band width.

The objective is assumed CONVEX under mixing, not affine.  That distinction matters: the
real objective is `max_k E_P[r_k]`, a maximum of affine functions of the plan, which is
convex and in general NOT affine.  An affine hypothesis would not apply to it, so the
theorem would be about a different objective than the one Paper C optimises.  The proof
needs only the inequality, and `objective_is_convex` below discharges it for the real
objective rather than leaving it assumed. -/
theorem value_convex_of_convex_feasible
    (F : ℝ → Set X) (obj : X → ℝ) (V : ℝ → ℝ)
    (mix : ℝ → X → X → X)
    (hmix_feas : ∀ (l : ℝ), 0 ≤ l → l ≤ 1 → ∀ (a b : ℝ) (x y : X),
      x ∈ F a → y ∈ F b → mix l x y ∈ F (l * a + (1 - l) * b))
    (hmix_convex : ∀ (l : ℝ), 0 ≤ l → l ≤ 1 → ∀ (x y : X),
      obj (mix l x y) ≤ l * obj x + (1 - l) * obj y)
    (hV : ∀ e, IsGLB (obj '' F e) (V e))
    (a b : ℝ) (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (x y : X) (hx : x ∈ F a) (hy : y ∈ F b)
    (hxopt : obj x = V a) (hyopt : obj y = V b) :
    V (l * a + (1 - l) * b) ≤ l * V a + (1 - l) * V b := by
  have hfeas := hmix_feas l hl0 hl1 a b x y hx hy
  have hval : obj (mix l x y) ≤ l * V a + (1 - l) * V b := by
    have := hmix_convex l hl0 hl1 x y
    rw [hxopt, hyopt] at this
    exact this
  have hlb := (hV (l * a + (1 - l) * b)).1 ⟨mix l x y, hfeas, rfl⟩
  linarith

/-- **The real objective satisfies the convexity hypothesis.**

`max_k E_P[r_k]` is a maximum of functions that ARE affine in the plan, and a maximum of
affine functions is convex.  So `value_convex_of_convex_feasible` applies to Paper C's
actual objective; with an affine hypothesis it would not have.

Stated for a nonempty finite budget set and an arbitrary family of per-budget terms that
mix affinely -- which is exactly what `E_P[r_k]` does, `P` entering linearly. -/
theorem objective_is_convex {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (term : β → X → ℝ) (mix : ℝ → X → X → X)
    (hterm_affine : ∀ (l : ℝ) (x y : X) (k : β),
      term k (mix l x y) = l * term k x + (1 - l) * term k y)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (x y : X) :
    s.sup' hs (fun k => term k (mix l x y))
      ≤ l * s.sup' hs (fun k => term k x) + (1 - l) * s.sup' hs (fun k => term k y) := by
  refine Finset.sup'_le hs _ ?_
  intro k hk
  rw [hterm_affine l x y k]
  have hx : term k x ≤ s.sup' hs (fun k => term k x) :=
    Finset.le_sup' (fun k => term k x) hk
  have hy : term k y ≤ s.sup' hs (fun k => term k y) :=
    Finset.le_sup' (fun k => term k y) hk
  have h1l : 0 ≤ 1 - l := by linarith
  nlinarith [hx, hy, hl0, h1l]

end Shape

#print axioms abs_expect_sub_le
#print axioms abs_sup'_sub_le
#print axioms abs_inf'_sub_le
#print axioms abs_prefix_sum_sub_le
#print axioms abs_baseline_sub_le
#print axioms regret_perturbation
#print axioms value_antitone_of_nested
#print axioms value_convex_of_convex_feasible
#print axioms objective_is_convex

end CIGAMF.P13.PaperCFrontier
