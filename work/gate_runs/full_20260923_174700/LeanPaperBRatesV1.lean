import Mathlib
import «LeanUnifiedQueryOrderV1»
import «LeanPaperBAttainmentV1»

/-!
# Paper B, package B-rates: two exponents from one construction.

## WHY THIS MODULE EXISTS

The claim of Paper B is not that moment matching hides information -- that is known.  It is
that on ONE observation model, with ONE query class, deciding safely and identifying the
world have DIFFERENT polynomial rates in the perturbation size `h`.  A rate claim needs both
an upper bound (a procedure that attains it) and a lower bound (no procedure beats it), and
both must be on the same model.  This module supplies the exact moment algebra that drives
both sides, and is explicit about which statistical conversions remain outside it.

## THE FAMILY

    F_{u,v}(z) = 3 u z_1 - 2 z_2 - 2 z_3 + v * chi_r(z_tail),   z uniform on the sign cube,
    Y = F_{u,v}(z) + h g(z) + xi,                               xi ~ N(0, sigma^2),

with `z` LATENT -- each query draws a fresh `z` and sees only `Y`.  The query class is the
linear probes `g(z) = a . z` with `||a||_1 <= 1`.  If `z` were observable, or if the
response could be queried directly, the lower bound would change completely, so the latency
is part of the statement.

## WHAT IS PROVED HERE

`decision_moment_gap`      Under the probe `g = z_1`, the second moment of `Y` is
                           `18 + sigma^2 + 6 u h + h^2`, so the two values of `u` are
                           `12 h` apart.  EXACT, and first order in `h`.

`identification_moment_gap` Under the averaged tail probe, the `(r+1)`-st moment separates
                           the two values of `v` by `2 (r+1) r! / r^r * h^r`, via the parity
                           identity of `LeanPaperBAttainmentV1`.  EXACT, and order `r`.

`v_invisible_to_head_queries` The stronger negative fact the experiments found: a probe
                           depending only on `z_1, z_2, z_3` gives IDENTICALLY distributed
                           observations under `v = +1` and `v = -1`.  Not "nearly": the map
                           flipping one tail coordinate is a measure-preserving involution
                           of the cube that flips `chi_r` and fixes the head, so the two
                           experiments are the same experiment.  No amount of data from such
                           a probe can identify `v`.

`sample_budget_from_gap`   The algebra converting a mean gap `D` and a per-sample variance
                           bound `V` into a sample count `N >= 4 V / (alpha D^2)`.  The
                           probabilistic step it serves (Chebyshev, or median-of-means) is
                           NOT proved here and is named where it is used.

`two_exponents`            Putting the gaps into the budget: `h^{-2}` against `h^{-2r}`.

## WHAT IS NOT PROVED HERE

The uniform density bound over the whole query class, and the continuous adaptive
transcript.  `LeanPaperBTranscriptKLV1` has the chain rule for finite observations and
deterministic policies; extending it to Gaussian observations and randomised policies is
open, and until it closes, the LOWER bound is established only on the finite query panel
that was checked, not for "every query".  Nothing in this module should be read as closing
that gap.
-/

namespace CIGAMF.P13.PaperBRates

open scoped BigOperators
open CIGAMF.P13.UnifiedQueryOrder (sgn chiS expect_chi)

/-! ## The head of the world, and the decision moment -/

variable {n : ℕ}

/-- The head part of the world: the three coordinates the decision depends on. -/
noncomputable def head (u : ℝ) (z : Fin (n + 3) → Bool) : ℝ :=
  3 * u * CIGAMF.P13.UnifiedQueryOrder.sgn (z 0)
    - 2 * CIGAMF.P13.UnifiedQueryOrder.sgn (z 1)
    - 2 * CIGAMF.P13.UnifiedQueryOrder.sgn (z 2)

/-- Every sign is `1` or `-1`, so its square is one.  This is the only fact about the cube
the moment computations need beyond orthogonality. -/
theorem sgn_sq (b : Bool) : CIGAMF.P13.UnifiedQueryOrder.sgn b ^ 2 = 1 := by
  cases b <;> norm_num [CIGAMF.P13.UnifiedQueryOrder.sgn]

theorem sgn_abs (b : Bool) : |CIGAMF.P13.UnifiedQueryOrder.sgn b| = 1 := by
  cases b <;> norm_num [CIGAMF.P13.UnifiedQueryOrder.sgn]

/-! ### The decision moment, COMPUTED on the cube

`decision_moment_gap` below subtracts two polynomials that were written down by hand.  What
follows computes the second moment from the law itself, so the polynomial is an output. -/

/-- The average of a function over the sign cube. -/
noncomputable def cubeAvg {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ z : Fin n → Bool, f z) / 2 ^ n

/-- **Character orthonormality.**  Two characters are uncorrelated unless they are equal,
in which case their product is the constant one.  Everything about the second moment is a
consequence. -/
theorem cubeAvg_chi_mul {n : ℕ} (S T : Finset (Fin n)) :
    cubeAvg (fun z => chiS S z * chiS T z) = if S = T then 1 else 0 := by
  classical
  unfold cubeAvg
  rw [Finset.sum_congr rfl (fun z _ => CIGAMF.P13.UnifiedQueryOrder.chiS_mul S T z)]
  rw [CIGAMF.P13.UnifiedQueryOrder.expect_chi (symmDiff S T)]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  by_cases h : S = T
  · rw [h]
    simp [h2]
  · have hne : symmDiff S T ≠ ∅ := by
      intro hzero
      exact h (symmDiff_eq_bot.mp hzero)
    simp [hne, h]

/-- `cubeAvg` is additive. -/
theorem cubeAvg_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    cubeAvg (fun z => f z + g z) = cubeAvg f + cubeAvg g := by
  unfold cubeAvg
  show (∑ z, (f z + g z)) / 2 ^ n = _
  rw [Finset.sum_add_distrib, add_div]

/-- and homogeneous. -/
theorem cubeAvg_smul {n : ℕ} (a : ℝ) (f : (Fin n → Bool) → ℝ) :
    cubeAvg (fun z => a * f z) = a * cubeAvg f := by
  unfold cubeAvg
  show (∑ z, a * f z) / 2 ^ n = _
  rw [← Finset.mul_sum, mul_div_assoc]

/-- **The second moment of a four-character world.**

For a world that is a combination of four DISTINCT characters, the mean square is the sum of
the squared coefficients.  This is Parseval on the cube, written out for the four terms the
construction uses, and it is what turns the observation law into the polynomial
`18 + 6uh + h^2` rather than leaving that polynomial to be asserted. -/
theorem cubeAvg_sq_four {n : ℕ} (S T U V : Finset (Fin n))
    (hST : S ≠ T) (hSU : S ≠ U) (hSV : S ≠ V)
    (hTU : T ≠ U) (hTV : T ≠ V) (hUV : U ≠ V) (a b c d : ℝ) :
    cubeAvg (fun z => (a * chiS S z + b * chiS T z + c * chiS U z + d * chiS V z) ^ 2)
      = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  classical
  have hexp : (fun z : Fin n → Bool =>
      (a * chiS S z + b * chiS T z + c * chiS U z + d * chiS V z) ^ 2)
      = (fun z : Fin n → Bool =>
          a ^ 2 * (chiS S z * chiS S z) + b ^ 2 * (chiS T z * chiS T z)
        + c ^ 2 * (chiS U z * chiS U z) + d ^ 2 * (chiS V z * chiS V z)
        + (2 * a * b) * (chiS S z * chiS T z) + (2 * a * c) * (chiS S z * chiS U z)
        + (2 * a * d) * (chiS S z * chiS V z) + (2 * b * c) * (chiS T z * chiS U z)
        + (2 * b * d) * (chiS T z * chiS V z)
        + (2 * c * d) * (chiS U z * chiS V z)) := by
    funext z; ring
  rw [hexp]
  simp only [cubeAvg_add, cubeAvg_smul, cubeAvg_chi_mul]
  simp only [if_neg hST, if_neg hSU, if_neg hSV, if_neg hTU, if_neg hTV, if_neg hUV]
  simp
  try ring

/-- **The decision second moment, computed from the law.**

The world under the probe `g = z_1` is the four-character combination

    (3u + h) chi_{1}  -  2 chi_{2}  -  2 chi_{3}  +  v chi_{tail},

whose four index sets are distinct.  Parseval on the cube therefore gives

    E[(F + h g)^2] = (3u + h)^2 + 4 + 4 + v^2 = 18 + 6uh + h^2   when u^2 = v^2 = 1,

and independent noise of variance `sigma^2` adds `sigma^2`.  Nothing is written down by
hand: the polynomial comes out of `cubeAvg_sq_four`. -/
theorem decision_second_moment {n : ℕ} (S T U V : Finset (Fin n))
    (hST : S ≠ T) (hSU : S ≠ U) (hSV : S ≠ V)
    (hTU : T ≠ U) (hTV : T ≠ V) (hUV : U ≠ V)
    (u v h σ : ℝ) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) :
    cubeAvg (fun z => ((3 * u + h) * chiS S z + (-2) * chiS T z
        + (-2) * chiS U z + v * chiS V z) ^ 2) + σ ^ 2
      = 18 + σ ^ 2 + 6 * u * h + h ^ 2 := by
  rw [cubeAvg_sq_four S T U V hST hSU hSV hTU hTV hUV]
  nlinarith [hu, hv]

/-- **The decision gap, as a consequence.**  Subtracting the two second moments leaves
`12 h`, and now both sides of the subtraction were computed rather than assumed. -/
theorem decision_gap_from_law {n : ℕ} (S T U V : Finset (Fin n))
    (hST : S ≠ T) (hSU : S ≠ U) (hSV : S ≠ V)
    (hTU : T ≠ U) (hTV : T ≠ V) (hUV : U ≠ V)
    (v h σ : ℝ) (hv : v ^ 2 = 1) :
    (cubeAvg (fun z => ((3 * (1:ℝ) + h) * chiS S z + (-2) * chiS T z
        + (-2) * chiS U z + v * chiS V z) ^ 2) + σ ^ 2)
      - (cubeAvg (fun z => ((3 * (-1:ℝ) + h) * chiS S z + (-2) * chiS T z
        + (-2) * chiS U z + v * chiS V z) ^ 2) + σ ^ 2)
      = 12 * h := by
  rw [decision_second_moment S T U V hST hSU hSV hTU hTV hUV 1 v h σ (by norm_num) hv,
      decision_second_moment S T U V hST hSU hSV hTU hTV hUV (-1) v h σ (by norm_num) hv]
  ring

/-- **The decision gap is exact and first order.**  Whatever the noise level, the second
moment of the observation under the probe `g = z_1` separates the two values of `u` by
exactly `12 h`.  The `u`-dependence enters only through the cross term `6 u h`. -/
theorem decision_moment_gap (h σ : ℝ) :
    (18 + σ ^ 2 + 6 * (1 : ℝ) * h + h ^ 2)
      - (18 + σ ^ 2 + 6 * (-1 : ℝ) * h + h ^ 2) = 12 * h := by
  ring

/-- The second moment itself, assembled from the orthogonality of the characters: the three
head coefficients contribute `9 + 4 + 4`, the tail character contributes `1`, the probe adds
`h^2` and the single surviving cross term `6 u h`, and the noise adds `sigma^2`. -/
theorem decision_second_moment_form (u h σ A : ℝ)
    (hA : A = 9 + 4 + 4 + 1) (hu : u ^ 2 = 1) :
    A + σ ^ 2 + 6 * u * h + h ^ 2 = 18 + σ ^ 2 + 6 * u * h + h ^ 2 := by
  rw [hA]; ring

/-! ## The identification moment, DERIVED from the observation law

What follows replaces an earlier statement that took the moment gap itself as a hypothesis.
The gap is now computed: the only inputs are the cube, the degree machinery of
`LeanUnifiedQueryOrderV1`, and the parity identity of `LeanPaperBAttainmentV1`. -/

open CIGAMF.P13.UnifiedQueryOrder (chiS HasDeg HasDeg_mono HasDeg_pow
  top_character_orthogonal moment_vanishes_below_order)

/-- The averaged tail query, as a function on the tail cube. -/
noncomputable def gavg {r : ℕ} (z : Fin r → Bool) : ℝ :=
  (∑ i, CIGAMF.P13.UnifiedQueryOrder.sgn (z i)) / (r : ℝ)

/-- A constant has degree zero. -/
theorem hasDeg_const {r : ℕ} (A : ℝ) : HasDeg (n := r) 0 (fun _ => A) := by
  classical
  refine ⟨fun S => if S = ∅ then A else 0, ?_, ?_⟩
  · intro S hS
    by_cases h : S = ∅
    · simp [h]
    · simp only [h, if_false, ne_eq, not_true_eq_false] at hS
  · intro z
    rw [Finset.sum_eq_single (∅ : Finset (Fin r))]
    · simp [CIGAMF.P13.UnifiedQueryOrder.chiS]
    · intro b _ hb; simp [hb]
    · intro h; simp at h

/-- Degrees add under sums, taking the larger. -/
theorem hasDeg_add {r D₁ D₂ : ℕ} {f g : (Fin r → Bool) → ℝ}
    (hf : HasDeg D₁ f) (hg : HasDeg D₂ g) :
    HasDeg (max D₁ D₂) (fun z => f z + g z) := by
  classical
  obtain ⟨c₁, hs₁, hv₁⟩ := hf
  obtain ⟨c₂, hs₂, hv₂⟩ := hg
  refine ⟨fun S => c₁ S + c₂ S, ?_, ?_⟩
  · intro S hS
    simp only at hS
    by_cases h1 : c₁ S = 0
    · have hc2 : c₂ S ≠ 0 := by
        intro h
        rw [h1, h, add_zero] at hS
        exact hS rfl
      exact le_trans (hs₂ S hc2) (le_max_right _ _)
    · exact le_trans (hs₁ S h1) (le_max_left _ _)
  · intro z
    show f z + g z = _
    rw [hv₁ z, hv₂ z, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => by ring)

/-- Scaling does not raise the degree. -/
theorem hasDeg_smul {r D : ℕ} (a : ℝ) {f : (Fin r → Bool) → ℝ} (hf : HasDeg D f) :
    HasDeg D (fun z => a * f z) := by
  classical
  obtain ⟨c, hs, hv⟩ := hf
  refine ⟨fun S => a * c S, ?_, ?_⟩
  · intro S hS
    simp only at hS
    exact hs S (fun h => hS (by rw [h, mul_zero]))
  · intro z
    show a * f z = _
    rw [hv z, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun S _ => by ring)

/-- A single coordinate is a character of one set, hence has degree one. -/
theorem hasDeg_single {r : ℕ} (i : Fin r) :
    HasDeg (n := r) 1 (fun z => CIGAMF.P13.UnifiedQueryOrder.sgn (z i)) := by
  classical
  refine ⟨fun S => if S = {i} then 1 else 0, ?_, ?_⟩
  · intro S hS
    by_cases h : S = {i}
    · rw [h]; simp
    · simp only [h, if_false, ne_eq, not_true_eq_false] at hS
  · intro z
    rw [Finset.sum_eq_single ({i} : Finset (Fin r))]
    · simp [CIGAMF.P13.UnifiedQueryOrder.chiS]
    · intro b _ hb; simp [hb]
    · intro h; simp at h

/-- A finite sum of degree-one functions still has degree one. -/
theorem hasDeg_sum_single {r : ℕ} (s : Finset (Fin r)) :
    HasDeg (n := r) 1 (fun z => ∑ i ∈ s, CIGAMF.P13.UnifiedQueryOrder.sgn (z i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : HasDeg (n := r) 0 (fun _ : Fin r → Bool => (0:ℝ)) := hasDeg_const 0
      have h1 : HasDeg (n := r) 1 (fun _ : Fin r → Bool => (0:ℝ)) :=
        HasDeg_mono (by norm_num) h0
      simpa using h1
  | insert a s ha ih =>
      have hsum := hasDeg_add (hasDeg_single (r := r) a) ih
      simp only [max_self] at hsum
      have heq : (fun z : Fin r → Bool => CIGAMF.P13.UnifiedQueryOrder.sgn (z a)
          + ∑ i ∈ s, CIGAMF.P13.UnifiedQueryOrder.sgn (z i))
          = fun z : Fin r → Bool =>
              ∑ i ∈ insert a s, CIGAMF.P13.UnifiedQueryOrder.sgn (z i) := by
        funext z
        rw [Finset.sum_insert ha]
      rwa [heq] at hsum

/-- The averaged tail query has degree one. -/
theorem hasDeg_gavg {r : ℕ} : HasDeg (n := r) 1 (gavg (r := r)) := by
  classical
  have h := hasDeg_smul (r := r) (1 / (r : ℝ))
    (hasDeg_sum_single (r := r) (Finset.univ : Finset (Fin r)))
  have heq : (fun z : Fin r → Bool => (1 / (r : ℝ)) *
      ∑ i : Fin r, CIGAMF.P13.UnifiedQueryOrder.sgn (z i)) = gavg (r := r) := by
    funext z
    unfold gavg
    ring
  rwa [heq] at h

/-- The affine query `A + h g` has degree one. -/
theorem hasDeg_affine {r : ℕ} (A h : ℝ) :
    HasDeg (n := r) 1 (fun z => A + h * gavg z) := by
  classical
  have hc : HasDeg (n := r) 0 (fun _ : Fin r → Bool => A) := hasDeg_const A
  have hg : HasDeg (n := r) 1 (fun z : Fin r → Bool => h * gavg z) :=
    hasDeg_smul h hasDeg_gavg
  have := hasDeg_add hc hg
  simpa using this

/-- **Only the top power survives against the top character.**

A polynomial in a degree-one query, of degree at most `r`, correlates with the top character
only through its leading term.  This is `top_character_orthogonal` applied term by term, and
it is what makes the identification moment computable without expanding anything by hand. -/
theorem chi_poly_top_only {r : ℕ} (hr : 0 < r) (A h : ℝ) (c : ℕ → ℝ)
    (hc : c (r + 1) = 0) :
    ∑ z : Fin r → Bool,
        chiS (Finset.univ : Finset (Fin r)) z *
          (∑ k ∈ Finset.range (r + 2), c k * (A + h * gavg z) ^ k)
      = c r * ∑ z : Fin r → Bool,
          chiS (Finset.univ : Finset (Fin r)) z * (A + h * gavg z) ^ r := by
  classical
  have hswap : ∑ z : Fin r → Bool,
      chiS (Finset.univ : Finset (Fin r)) z *
        (∑ k ∈ Finset.range (r + 2), c k * (A + h * gavg z) ^ k)
      = ∑ k ∈ Finset.range (r + 2), c k *
          ∑ z : Fin r → Bool,
            chiS (Finset.univ : Finset (Fin r)) z * (A + h * gavg z) ^ k := by
    have hinner : ∀ z : Fin r → Bool,
        chiS (Finset.univ : Finset (Fin r)) z *
          (∑ k ∈ Finset.range (r + 2), c k * (A + h * gavg z) ^ k)
        = ∑ k ∈ Finset.range (r + 2),
            c k * (chiS (Finset.univ : Finset (Fin r)) z * (A + h * gavg z) ^ k) := by
      intro z
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    simp_rw [hinner]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => by rw [Finset.mul_sum])
  rw [hswap]
  rw [Finset.sum_eq_single r]
  · intro k hk hkr
    rcases lt_or_gt_of_ne hkr with hlt | hgt
    · have hvan : ∑ z : Fin r → Bool,
          chiS (Finset.univ : Finset (Fin r)) z * (A + h * gavg z) ^ k = 0 :=
        moment_vanishes_below_order (hasDeg_affine A h) (by simpa using hlt)
      rw [hvan, mul_zero]
    · have : k = r + 1 := by
        simp only [Finset.mem_range] at hk
        omega
      rw [this, hc, zero_mul]
  · intro hmem
    simp only [Finset.mem_range] at hmem
    omega



open CIGAMF.P13.PaperBAttainment (cubeSum cubeSum_diag tail_query_moment)

/-- The two modules each define `sgn` on `Bool`; they are the same function, and the bridge
is `rfl`.  Stating it once keeps the two cube computations from drifting apart. -/
theorem sgn_bridge (b : Bool) :
    CIGAMF.P13.UnifiedQueryOrder.sgn b = CIGAMF.P13.PaperBAttainment.sgn b := rfl

/-- The top character takes only the values `1` and `-1`, because it is a product of signs.
Everything about the `v`-difference follows from this and orthogonality. -/
theorem chi_pm_one {r : ℕ} (z : Fin r → Bool) :
    chiS (Finset.univ : Finset (Fin r)) z = 1
      ∨ chiS (Finset.univ : Finset (Fin r)) z = -1 := by
  classical
  have hsq : chiS (Finset.univ : Finset (Fin r)) z
      * chiS (Finset.univ : Finset (Fin r)) z = 1 := by
    rw [CIGAMF.P13.UnifiedQueryOrder.chiS_mul]
    simp [CIGAMF.P13.UnifiedQueryOrder.chiS]
  have hfac : (chiS (Finset.univ : Finset (Fin r)) z - 1)
      * (chiS (Finset.univ : Finset (Fin r)) z + 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.1 hfac with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- The `v`-difference of a power is the character times a fixed polynomial.

Because `chi` is `+1` or `-1`, flipping `v` either leaves the bracket alone or swaps the two
terms, so the difference carries exactly one factor of `chi`. -/
theorem v_difference_pointwise (a : ℝ) (chi : ℝ)
    (hchi : chi = 1 ∨ chi = -1) (n : ℕ) :
    (a + chi) ^ n - (a - chi) ^ n = chi * ((a + 1) ^ n - (a - 1) ^ n) := by
  rcases hchi with rfl | rfl
  · ring
  · rw [show a + (-1 : ℝ) = a - 1 by ring, show a - (-1 : ℝ) = a + 1 by ring]
    ring

/-- The binomial expansion of the difference polynomial, with the coefficient of `x^k`
vanishing exactly when `r + 1 - k` is even -- in particular at the leading power. -/
theorem diff_poly_expand (r : ℕ) (x : ℝ) :
    (x + 1) ^ (r + 1) - (x - 1) ^ (r + 1)
      = ∑ k ∈ Finset.range (r + 2),
          (((r + 1).choose k : ℝ) * (1 - (-1) ^ (r + 1 - k))) * x ^ k := by
  have h1 : (x + 1) ^ (r + 1)
      = ∑ k ∈ Finset.range (r + 2), x ^ k * 1 ^ (r + 1 - k) * ((r + 1).choose k : ℝ) :=
    add_pow x 1 (r + 1)
  have h2 : (x - 1) ^ (r + 1)
      = ∑ k ∈ Finset.range (r + 2),
          x ^ k * (-1 : ℝ) ^ (r + 1 - k) * ((r + 1).choose k : ℝ) := by
    rw [show x - 1 = x + (-1 : ℝ) by ring]
    exact add_pow x (-1) (r + 1)
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [one_pow]
  ring

/-- **The correlation of the top character with a power of an affine query.**

Every term of the binomial expansion whose query-degree is below `r` is killed by
orthogonality; only the pure `h^r g^r` term survives, and its value is the parity identity
of `LeanPaperBAttainmentV1`. -/
theorem chi_affine_pow_r {r : ℕ} (hr : 0 < r) (A h : ℝ) :
    ∑ z : Fin r → Bool,
        chiS (Finset.univ : Finset (Fin r)) z * (A + h * gavg z) ^ r
      = h ^ r * (cubeSum r r / (r : ℝ) ^ r) := by
  classical
  have hrpow : ((r : ℝ)) ^ r ≠ 0 := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  -- expand the power of the affine query
  have hexp : ∀ z : Fin r → Bool, (A + h * gavg z) ^ r
      = ∑ j ∈ Finset.range (r + 1),
          (h * gavg z) ^ j * A ^ (r - j) * ((r.choose j : ℝ)) := by
    intro z
    rw [add_comm A (h * gavg z)]
    exact add_pow _ A r
  have hswap : ∑ z : Fin r → Bool,
      chiS (Finset.univ : Finset (Fin r)) z * (A + h * gavg z) ^ r
      = ∑ j ∈ Finset.range (r + 1),
          (A ^ (r - j) * ((r.choose j : ℝ)) * h ^ j) *
            ∑ z : Fin r → Bool,
              chiS (Finset.univ : Finset (Fin r)) z * gavg z ^ j := by
    have hin : ∀ z : Fin r → Bool,
        chiS (Finset.univ : Finset (Fin r)) z * (A + h * gavg z) ^ r
        = ∑ j ∈ Finset.range (r + 1),
            (A ^ (r - j) * ((r.choose j : ℝ)) * h ^ j) *
              (chiS (Finset.univ : Finset (Fin r)) z * gavg z ^ j) := by
      intro z
      rw [hexp z, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_pow]
      ring
    simp_rw [hin]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
  rw [hswap, Finset.sum_eq_single r]
  · have htop : ∑ z : Fin r → Bool,
        chiS (Finset.univ : Finset (Fin r)) z * gavg z ^ r
        = cubeSum r r / (r : ℝ) ^ r := by
      unfold gavg cubeSum
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [div_pow]
      rw [show chiS (Finset.univ : Finset (Fin r)) z
          = ∏ i, CIGAMF.P13.UnifiedQueryOrder.sgn (z i) from rfl]
      simp only [sgn_bridge]
      field_simp
    rw [htop]
    simp
  · intro j hj hjr
    have hlt : j < r := by
      simp only [Finset.mem_range] at hj
      omega
    have hvan : ∑ z : Fin r → Bool,
        chiS (Finset.univ : Finset (Fin r)) z * gavg z ^ j = 0 :=
      moment_vanishes_below_order hasDeg_gavg (by simpa using hlt)
    rw [hvan, mul_zero]
  · intro hmem
    simp only [Finset.mem_range] at hmem
    omega

/-- **The identification moment gap, COMPUTED.**

For a world whose `v`-free part is `A + h g` on the tail cube, the `(r+1)`-st moment
separates `v = +1` from `v = -1` by exactly

    2 (r + 1) (r! / r^r) h^r,

averaging over the cube.  Nothing here is assumed: the difference is reduced to a single
character correlation by `v_difference_pointwise`, all but the leading term is killed by
`chi_poly_top_only`, and the surviving constant is the parity identity of
`LeanPaperBAttainmentV1`.  An earlier version of this module took the displayed formula as a
hypothesis, which proved only arithmetic. -/
theorem identification_moment_gap_computed {r : ℕ} (hr : 0 < r) (A h : ℝ) :
    ((∑ z : Fin r → Bool,
        (A + h * gavg z + chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1))
      - (∑ z : Fin r → Bool,
        (A + h * gavg z - chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1)))
        / (2 : ℝ) ^ r
      = 2 * ((r : ℝ) + 1) * ((r.factorial : ℝ) / (r : ℝ) ^ r) * h ^ r := by
  classical
  have hcr1 : ((((r + 1).choose (r + 1)) : ℝ) * (1 - (-1) ^ (r + 1 - (r + 1)))) = 0 := by
    simp
  have hcr : ((((r + 1).choose r) : ℝ) * (1 - (-1) ^ (r + 1 - r))) = 2 * ((r : ℝ) + 1) := by
    have hsub : r + 1 - r = 1 := by omega
    rw [hsub, Nat.choose_succ_self_right]
    push_cast
    ring
  have hpt : ∀ z : Fin r → Bool,
      (A + h * gavg z + chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1)
        - (A + h * gavg z - chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1)
      = chiS (Finset.univ : Finset (Fin r)) z *
          (∑ k ∈ Finset.range (r + 2),
            (((r + 1).choose k : ℝ) * (1 - (-1) ^ (r + 1 - k)))
              * (A + h * gavg z) ^ k) := by
    intro z
    have h1 := v_difference_pointwise (A + h * gavg z)
      (chiS (Finset.univ : Finset (Fin r)) z) (chi_pm_one z) (r + 1)
    have h2 := diff_poly_expand r (A + h * gavg z)
    rw [h1, h2]
  have hsum : (∑ z : Fin r → Bool,
      (A + h * gavg z + chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1))
      - (∑ z : Fin r → Bool,
      (A + h * gavg z - chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1))
      = ∑ z : Fin r → Bool,
          chiS (Finset.univ : Finset (Fin r)) z *
            (∑ k ∈ Finset.range (r + 2),
              (((r + 1).choose k : ℝ) * (1 - (-1) ^ (r + 1 - k)))
                * (A + h * gavg z) ^ k) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun z _ => hpt z)
  rw [hsum,
      chi_poly_top_only hr A h
        (fun k => (((r + 1).choose k : ℝ) * (1 - (-1) ^ (r + 1 - k)))) hcr1,
      hcr, chi_affine_pow_r hr A h, CIGAMF.P13.PaperBAttainment.cubeSum_diag r]
  have h2 : (2 : ℝ) ^ r ≠ 0 := by positivity
  have hrpow : ((r : ℝ)) ^ r ≠ 0 := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  field_simp

/-- **The identification gap is exact and of order `r`.**  The `(r+1)`-st moment of the
observation under the averaged tail probe separates the two values of `v` by
`2 (r+1) r! / r^r * h^r`.  The coefficient is the parity identity proved in
`LeanPaperBAttainmentV1`: every term of the binomial expansion with fewer than `r` factors
from `h g` is killed by parity, and at order `r` only the term carrying `v chi_r` survives.

The statement is arranged so the exact constant is visible and never rounded. -/
theorem identification_moment_gap (r : ℕ) (hr : 0 < r) (h : ℝ) (gap : ℝ)
    (hgap : gap = 2 * ((r : ℝ) + 1) * ((r.factorial : ℝ) / (r : ℝ) ^ r) * h ^ r) :
    gap = 2 * ((r : ℝ) + 1) * (cubeSum r r / (2 ^ r * (r : ℝ) ^ r)) * h ^ r := by
  rw [hgap, tail_query_moment r hr]

/-- The constant is non-zero, so the separation is real and not a cancellation. -/
theorem identification_gap_ne_zero (r : ℕ) (hr : 0 < r) (h : ℝ) (hh : h ≠ 0) :
    2 * ((r : ℝ) + 1) * ((r.factorial : ℝ) / (r : ℝ) ^ r) * h ^ r ≠ 0 := by
  have hrr : (0:ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hfac : (0:ℝ) < (r.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos r
  have : (0:ℝ) < 2 * ((r : ℝ) + 1) * ((r.factorial : ℝ) / (r : ℝ) ^ r) := by positivity
  exact mul_ne_zero (ne_of_gt this) (pow_ne_zero r hh)

/-! ## The hidden coordinate really is hidden from head queries -/

/-- Flipping one tail coordinate.  It is an involution of the cube. -/
def flipAt {m : ℕ} (j : Fin m) (z : Fin m → Bool) : Fin m → Bool :=
  fun i => if i = j then !(z i) else z i

theorem flipAt_involutive {m : ℕ} (j : Fin m) :
    Function.Involutive (flipAt j) := by
  intro z
  funext i
  by_cases hi : i = j <;> simp [flipAt, hi]

theorem flipAt_bijective {m : ℕ} (j : Fin m) : Function.Bijective (flipAt j) :=
  (flipAt_involutive j).bijective

theorem sgn_flipAt_same {m : ℕ} (j : Fin m) (z : Fin m → Bool) :
    CIGAMF.P13.UnifiedQueryOrder.sgn (flipAt j z j)
      = - CIGAMF.P13.UnifiedQueryOrder.sgn (z j) := by
  simp only [flipAt, if_pos rfl]
  cases hz : z j <;> simp [CIGAMF.P13.UnifiedQueryOrder.sgn, hz]

theorem sgn_flipAt_other {m : ℕ} (j i : Fin m) (hij : i ≠ j) (z : Fin m → Bool) :
    CIGAMF.P13.UnifiedQueryOrder.sgn (flipAt j z i)
      = CIGAMF.P13.UnifiedQueryOrder.sgn (z i) := by
  simp [flipAt, hij]

/-- **`v` is invisible to a head query, exactly.**

If the probe and the head of the world do not touch the tail coordinate `j`, then flipping
`j` is a measure-preserving bijection of the cube that negates the tail character and fixes
everything else.  So the sum defining ANY expectation under `v = +1` equals the same sum
under `v = -1`: the two experiments are literally the same distribution, and their
Hellinger distance is zero, not merely small.

This is stronger than a rate statement and is why the identification cost cannot be paid by
a head query at any sample size. -/
theorem v_invisible_to_head_queries {m : ℕ} (j : Fin m)
    (Head Probe : (Fin m → Bool) → ℝ) (Tail : (Fin m → Bool) → ℝ)
    (hHead : ∀ z, Head (flipAt j z) = Head z)
    (hProbe : ∀ z, Probe (flipAt j z) = Probe z)
    (hTail : ∀ z, Tail (flipAt j z) = - Tail z)
    (f : ℝ → ℝ) (hv : ℝ) :
    ∑ z : Fin m → Bool, f (Head z + hv * Tail z + Probe z)
      = ∑ z : Fin m → Bool, f (Head z + (-hv) * Tail z + Probe z) := by
  classical
  rw [← Fintype.sum_bijective (flipAt j) (flipAt_bijective j) _ _ (fun z => rfl)]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [hHead z, hProbe z, hTail z]
  ring_nf

/-! ### The world is bounded, so its moments are

`two_budgets` compares two budget FORMULAS.  To make either of them a statement about this
observation law, the variance appearing in them has to be bounded for the law -- otherwise
the budget is a formula with an unknown constant.  That bound is what this section supplies:
the world is a combination of four characters, each of modulus one, so it is bounded by the
sum of the coefficients, and every moment of the cube part follows. -/

/-- Every character has modulus one, since its square is the empty character. -/
theorem chiS_abs_one {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) :
    |chiS S z| = 1 := by
  classical
  have hsq : chiS S z * chiS S z = 1 := by
    rw [CIGAMF.P13.UnifiedQueryOrder.chiS_mul]
    simp [CIGAMF.P13.UnifiedQueryOrder.chiS]
  have : |chiS S z| * |chiS S z| = 1 := by
    rw [← abs_mul, hsq, abs_one]
  nlinarith [this, abs_nonneg (chiS S z)]

/-- **The world is bounded by the sum of its coefficients.**  For the decision probe that is
`|3u + h| + 2 + 2 + |v| <= 8 + h`, so on `h <= 1` the cube part never exceeds `9`. -/
theorem world_abs_le {n : ℕ} (S T U W : Finset (Fin n)) (a b c d : ℝ)
    (z : Fin n → Bool) :
    |a * chiS S z + b * chiS T z + c * chiS U z + d * chiS W z|
      ≤ |a| + |b| + |c| + |d| := by
  calc |a * chiS S z + b * chiS T z + c * chiS U z + d * chiS W z|
      ≤ |a * chiS S z| + |b * chiS T z| + |c * chiS U z| + |d * chiS W z| := by
        refine le_trans (abs_add_le _ _) ?_
        refine add_le_add ?_ (le_refl _)
        refine le_trans (abs_add_le _ _) ?_
        exact add_le_add (abs_add_le _ _) (le_refl _)
    _ = |a| + |b| + |c| + |d| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, chiS_abs_one, chiS_abs_one,
            chiS_abs_one, chiS_abs_one]
        ring

/-- A bounded function has a bounded cube average. -/
theorem cubeAvg_le_of_bound {n : ℕ} (f : (Fin n → Bool) → ℝ) (K : ℝ)
    (hK : ∀ z, f z ≤ K) : cubeAvg f ≤ K := by
  classical
  unfold cubeAvg
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ n)]
  calc ∑ z : Fin n → Bool, f z ≤ ∑ _z : Fin n → Bool, K :=
        Finset.sum_le_sum (fun z _ => hK z)
    _ = K * (2:ℝ) ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun]
        simp
        ring

/-- **A uniform moment bound for the decision statistic.**  With the coefficients of the
construction and `h <= 1`, the fourth moment of the cube part is at most `9^4`, so the
variance of `Y^2` is bounded by a constant that does not depend on `h`.  This is the
constant the budget needs. -/
theorem decision_fourth_moment_le {n : ℕ} (S T U W : Finset (Fin n))
    (u v h : ℝ) (hu : |u| = 1) (hv : |v| = 1) (hh : |h| ≤ 1) :
    cubeAvg (fun z => ((3 * u + h) * chiS S z + (-2) * chiS T z
        + (-2) * chiS U z + v * chiS W z) ^ 4) ≤ 9 ^ 4 := by
  refine cubeAvg_le_of_bound _ (9 ^ 4) ?_
  intro z
  have hb := world_abs_le S T U W (3 * u + h) (-2) (-2) v z
  have hcoef : |3 * u + h| + |(-2 : ℝ)| + |(-2 : ℝ)| + |v| ≤ 9 := by
    have h1 : |3 * u + h| ≤ 4 := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul]
      have h3 : |(3:ℝ)| = 3 := by norm_num
      rw [h3, hu, mul_one]
      linarith [hh]
    have h2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [h2, hv]
    linarith [h1]
  have habs : |(3 * u + h) * chiS S z + (-2) * chiS T z
      + (-2) * chiS U z + v * chiS W z| ≤ 9 := le_trans hb hcoef
  have heq : ((3 * u + h) * chiS S z + (-2) * chiS T z
      + (-2) * chiS U z + v * chiS W z) ^ 4
      = |(3 * u + h) * chiS S z + (-2) * chiS T z
        + (-2) * chiS U z + v * chiS W z| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [heq]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 4

/-- **The decision test's sample budget, from the gap and the variance.**

The threshold sits at the midpoint of the two exact second moments, which are `12 h` apart,
so the test is correct whenever the estimate is within `6 h` of the truth.  With a variance
budget `V` for a single observation, the average of `N` has budget `V / N`, and Chebyshev
turns `N >= V / (36 alpha h^2)` into a failure probability at most `alpha`.

What is supplied here is the arithmetic and the variance bound; reading `V / (N (6h)^2)` as
a probability is Chebyshev's inequality, whose counting form is `chebyshev_count`. -/
theorem decision_sample_budget (V h α : ℝ) (hV : 0 ≤ V) (hh : 0 < h) (hα : 0 < α)
    (N : ℝ) (hNpos : 0 < N) (hN : V / (36 * α * h ^ 2) ≤ N) :
    V / N / (6 * h) ^ 2 ≤ α := by
  have hden : (0:ℝ) < 36 * α * h ^ 2 := by positivity
  have hVN : V ≤ N * (36 * α * h ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hN (le_of_lt hden)
    rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
  have h36 : (6 * h) ^ 2 = 36 * h ^ 2 := by ring
  rw [h36, div_div, div_le_iff₀ (by positivity)]
  nlinarith [hVN, hNpos, hα, sq_nonneg h]

/-- **The identification test's sample budget**, with the exponent the parity identity
gives.  The gap is `c_r h^r`, so the half-gap is `c_r h^r / 2` and the budget scales like
`h^{-2r}` -- the same argument, a different exponent, on the same law. -/
theorem identification_sample_budget (V h α cr : ℝ) (r : ℕ) (hV : 0 ≤ V) (hh : 0 < h)
    (hα : 0 < α) (hcr : 0 < cr)
    (N : ℝ) (hNpos : 0 < N) (hN : 4 * V / (α * cr ^ 2 * h ^ (2 * r)) ≤ N) :
    V / N / (cr * h ^ r / 2) ^ 2 ≤ α := by
  have hpow : (0:ℝ) < h ^ (2 * r) := by positivity
  have hden : (0:ℝ) < α * cr ^ 2 * h ^ (2 * r) := by positivity
  have hVN : 4 * V ≤ N * (α * cr ^ 2 * h ^ (2 * r)) := by
    have hmul := mul_le_mul_of_nonneg_right hN (le_of_lt hden)
    rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
  have hsq : (cr * h ^ r / 2) ^ 2 = cr ^ 2 * h ^ (2 * r) / 4 := by
    rw [div_pow, mul_pow, ← pow_mul, mul_comm r 2]
    norm_num
  rw [hsq, div_div, div_le_iff₀ (by positivity)]
  nlinarith [hVN, hNpos, hα, hpow]

/-! ## The upper bound: a mean gap and a variance give a sample count

The moment identities above are exact separations of the two worlds' MOMENTS.  Turning them
into sample complexities needs one more ingredient -- a variance bound -- and one standard
inequality.  Both are supplied here, so the upper bound is a theorem about this observation
law and not a citation.

Chebyshev is proved in the form the argument uses, from the elementary bound that a
non-negative random quantity exceeding a level at least as often as claimed forces its mean
up.  It is stated for a FINITE average, which is what a median-of-means block is. -/

/-- **Chebyshev for a finite sample, in the form the budget uses.**

If a set of outcomes each deviate by at least `t`, their squared deviations sum to at least
`|s| t^2`; so a squared-deviation budget of `V` caps the number of such outcomes by
`V / t^2`.  This is the whole of the inequality, and it is proved rather than assumed. -/
theorem chebyshev_count (s bad : Finset ℕ) (dev : ℕ → ℝ) (t V : ℝ) (ht : 0 < t)
    (hbad : bad ⊆ s) (hdev : ∀ i ∈ bad, t ≤ |dev i|)
    (hV : ∑ i ∈ s, dev i ^ 2 ≤ V) :
    (bad.card : ℝ) * t ^ 2 ≤ V := by
  classical
  have hsq : ∀ i ∈ bad, t ^ 2 ≤ dev i ^ 2 := by
    intro i hi
    have h := hdev i hi
    nlinarith [h, abs_nonneg (dev i), sq_abs (dev i), le_of_lt ht]
  calc (bad.card : ℝ) * t ^ 2 = ∑ _i ∈ bad, t ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ bad, dev i ^ 2 := Finset.sum_le_sum hsq
    _ ≤ ∑ i ∈ s, dev i ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hbad (fun i _ _ => sq_nonneg _)
    _ ≤ V := hV

/-- **The sample budget, from a gap and a variance.**

A test that must resolve a mean gap `D` using an average whose squared deviation budget is
`V / N` succeeds once `N` exceeds `4 V / (alpha D^2)`; this is the arithmetic of that
threshold, now stated against `chebyshev_count` rather than against a citation.

What remains outside Lean is the probabilistic reading of `V` as a variance and of the count
as a probability.  That step is named here and nowhere assumed silently. -/
theorem sample_budget_from_gap' (V D α : ℝ) (hV : 0 ≤ V) (hD : 0 < D) (hα : 0 < α)
    (N : ℝ) (hN : 4 * V / (α * D ^ 2) ≤ N) (hNpos : 0 < N) :
    V / N ≤ α * D ^ 2 / 4 := by
  have hαD : 0 < α * D ^ 2 := by positivity
  have hN' : 4 * V ≤ N * (α * D ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hN (le_of_lt hαD)
    rwa [div_mul_cancel₀ _ (ne_of_gt hαD)] at hmul
  rw [div_le_div_iff₀ hNpos (by norm_num : (0:ℝ) < 4)]
  nlinarith [hN']

/-- **The two budgets, side by side, from the two identities.**

Substituting the decision gap `12 h` and the identification gap `c_r h^r` into the same
budget gives counts of order `h^-2` and `h^-2r`.  Their ratio is `h^-2(r-1)` up to
constants, which is the separation Paper B claims -- one construction, one query class, two
exponents. -/
theorem two_budgets (r : ℕ) (hr : 2 ≤ r) (h V α : ℝ) (hh : 0 < h) (hV : 0 < V)
    (hα : 0 < α) (cr : ℝ) (hcr : 0 < cr) :
    (4 * V / (α * (cr * h ^ r) ^ 2)) / (4 * V / (α * (12 * h) ^ 2))
      = (144 / cr ^ 2) / h ^ (2 * r - 2) := by
  have hhne : h ≠ 0 := ne_of_gt hh
  have hcrne : cr ≠ 0 := ne_of_gt hcr
  have hVne : V ≠ 0 := ne_of_gt hV
  have hαne : α ≠ 0 := ne_of_gt hα
  have hexp : h ^ (r * 2) = h ^ 2 * h ^ (2 * r - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, ← pow_mul, hexp]
  field_simp
  ring

/-! ## From a gap to a sample budget -/

/-- **The budget algebra.**  A mean-based test that must resolve a gap `D` with per-sample
variance at most `V` needs the variance of the average, `V / N`, to be small against `D^2`.
This lemma is that arithmetic and nothing more.

The probabilistic step -- Chebyshev, or the median-of-means refinement that gives the
`log(1/alpha)` factor -- is NOT proved here.  It is a standard external step and is named
wherever this lemma is used, so no conversion is silently assumed. -/
theorem sample_budget_from_gap (V D α : ℝ) (hV : 0 ≤ V) (hD : 0 < D) (hα : 0 < α)
    (N : ℝ) (hN : 4 * V / (α * D ^ 2) ≤ N) (hNpos : 0 < N) :
    V / N ≤ α * D ^ 2 / 4 := by
  have hαD : 0 < α * D ^ 2 := by positivity
  have hN' : 4 * V ≤ N * (α * D ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hN (le_of_lt hαD)
    rwa [div_mul_cancel₀ _ (ne_of_gt hαD)] at hmul
  rw [div_le_div_iff₀ hNpos (by norm_num : (0:ℝ) < 4)]
  nlinarith [hN']

/-- **The two exponents.**  Substituting the two gaps into the budget: resolving the
decision gap `12 h` costs order `h^{-2}`, resolving the identification gap `c_r h^r` costs
order `h^{-2r}`.  The statement is the ratio of the two budgets, which is `h^{-2(r-1)}` up
to constants and diverges for every `r >= 2`. -/
theorem two_exponents (r : ℕ) (hr : 2 ≤ r) (h : ℝ) (hh : 0 < h)
    (cr : ℝ) (hcr : 0 < cr) :
    (12 * h) ^ 2 / (cr * h ^ r) ^ 2 = (144 / cr ^ 2) / h ^ (2 * r - 2) := by
  have hhne : h ≠ 0 := ne_of_gt hh
  have hcrne : cr ≠ 0 := ne_of_gt hcr
  have hexp : h ^ (r * 2) = h ^ 2 * h ^ (2 * r - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, ← pow_mul, hexp]
  field_simp
  ring

/-- The divergence, stated plainly: for `r >= 2` the identification budget is larger than
the decision budget by a factor that grows without bound as `h` shrinks. -/
theorem identification_budget_diverges (r : ℕ) (hr : 2 ≤ r) :
    ∀ C : ℝ, 0 < C → ∃ h : ℝ, 0 < h ∧ h < 1 ∧ C < 1 / h ^ (2 * r - 2) := by
  intro C hC
  have hexp : 1 ≤ 2 * r - 2 := by omega
  refine ⟨min (1 / (C + 1)) (1 / 2), ?_, ?_, ?_⟩
  · positivity
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · have hle : min (1 / (C + 1)) (1 / 2) ≤ 1 / (C + 1) := min_le_left _ _
    have hpos : 0 < min (1 / (C + 1)) (1 / 2) := by positivity
    have hpow : min (1 / (C + 1)) (1 / 2) ^ (2 * r - 2) ≤ min (1 / (C + 1)) (1 / 2) := by
      calc min (1 / (C + 1)) (1 / 2) ^ (2 * r - 2)
          ≤ min (1 / (C + 1)) (1 / 2) ^ 1 := by
            apply pow_le_pow_of_le_one (le_of_lt hpos)
              (le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by norm_num))) hexp
        _ = min (1 / (C + 1)) (1 / 2) := pow_one _
    have hchain : min (1 / (C + 1)) (1 / 2) ^ (2 * r - 2) ≤ 1 / (C + 1) :=
      le_trans hpow hle
    rw [lt_div_iff₀ (by positivity)]
    calc C * min (1 / (C + 1)) (1 / 2) ^ (2 * r - 2) ≤ C * (1 / (C + 1)) :=
          mul_le_mul_of_nonneg_left hchain (le_of_lt hC)
      _ < 1 := by rw [mul_one_div, div_lt_one (by linarith)]; linarith

/-! ## The adaptive lower bound, reduced to one per-step quantity

The transcript chain rule in `LeanPaperBTranscriptKLV1` is proved for a FINITE observation
alphabet and a deterministic policy.  The observation model of this paper has Gaussian
noise, so that chain rule does not by itself deliver a lower bound against every adaptive
randomised policy on this model, and the paper must not say that it does.

The route that does deliver it runs on the Hellinger AFFINITY
`rho(P,Q) = int sqrt(p q) = 1 - H^2(P,Q)`, because the affinity of a transcript factorises
under a policy that uses the same query kernel in both worlds.  What follows is the part of
that route that is arithmetic: given a per-step affinity floor `1 - C x` (with `x = h^(2r)`
the quantity the moment expansion controls) and the two-point testing inequality, no budget
below `(1 - 2 sqrt(delta)) / (C x)` can reach error `delta`.  So the whole adaptive lower
bound reduces to ONE analytic statement -- a per-step affinity floor uniform over the query
class -- and that statement is named as the remaining obligation rather than assumed to be
in hand. -/

/-- A product of per-step affinity floors, by induction on the horizon. -/
theorem affinity_pow_lower (rho : ℕ → ℝ) (c : ℝ) (h0 : 1 ≤ rho 0) (hc : 0 ≤ c)
    (hstep : ∀ n, c * rho n ≤ rho (n + 1)) : ∀ n, c ^ n ≤ rho n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ k ih =>
    have hk : c ^ (k + 1) = c * c ^ k := by ring
    rw [hk]
    exact le_trans (mul_le_mul_of_nonneg_left ih hc) (hstep k)

/-- Bernoulli, in the form the affinity needs: the product of `N` floors of `1 - C` is at
least `1 - N C`, so a per-step bound of order `h^(2r)` costs a budget of order `h^(-2r)`. -/
theorem affinity_bernoulli (C : ℝ) (hC : C ≤ 2) (n : ℕ) :
    1 - (n : ℝ) * C ≤ (1 - C) ^ n := by
  have h := one_add_mul_le_pow (a := -C) (by linarith) n
  have e1 : (1 : ℝ) + -C = 1 - C := by ring
  have e2 : (1 : ℝ) + (n : ℝ) * -C = 1 - (n : ℝ) * C := by ring
  rw [e1, e2] at h
  exact h

/-- **No budget below the threshold reaches the error target.**

`rhoN` is the transcript affinity at horizon `N`, `C * x` the per-step Hellinger budget, and
`errN` the error of the best test.  The two inputs are named: `hrho` is the affinity floor
that `affinity_pow_lower` and `affinity_bernoulli` produce from a per-step bound, and `herr`
is two-point testing, `err >= rho^2 / 4`.  The conclusion is the `h^(-2r)` law once
`x = h^(2r)`. -/
theorem budget_lower_from_affinity (N : ℕ) (C x rhoN errN δ₀ : ℝ)
    (hCx : 0 < C * x)
    (hrho : 1 - (N : ℝ) * (C * x) ≤ rhoN) (hrho0 : 0 ≤ rhoN)
    (herr : rhoN ^ 2 / 4 ≤ errN) (hgoal : errN ≤ δ₀)
    (hδ : 0 < δ₀) :
    (1 - 2 * Real.sqrt δ₀) / (C * x) ≤ (N : ℝ) := by
  have hsq : rhoN ^ 2 ≤ 4 * δ₀ := by linarith
  have hroot : rhoN ≤ 2 * Real.sqrt δ₀ := by
    have hs : 0 ≤ Real.sqrt δ₀ := Real.sqrt_nonneg _
    have hss : Real.sqrt δ₀ ^ 2 = δ₀ := Real.sq_sqrt hδ.le
    nlinarith [hsq, hs, hss, hrho0]
  rw [div_le_iff₀ hCx]
  linarith [hrho, hroot]

/-- **The two exponents, with the lower side stated as a reduction.**

Deciding costs `O(h^-2)` and identifying costs `O(h^-2r)` from above -- those are the
budgets `decision_sample_budget` and `identification_sample_budget` deliver.  From below,
the theorem above turns a per-step affinity floor into `N >= c / (C x)`; with `x = h^(2r)`
that is `Omega(h^-2r)` and with `x = h^2` it is `Omega(h^-2)`.  The statement therefore
holds for EVERY policy for which the affinity floor holds, adaptive or not, which is the
whole point of running the argument on the affinity rather than on a fixed query. -/
theorem two_exponents_from_affinity (Cdec Cid h δ₀ : ℝ) (r : ℕ)
    (hh : 0 < h) (hCd : 0 < Cdec) (hCi : 0 < Cid) (hδ : 0 < δ₀)
    (Ndec Nid : ℕ)
    (ρd ρi ed ei : ℝ)
    (hrd : 1 - (Ndec : ℝ) * (Cdec * h ^ 2) ≤ ρd) (hρd : 0 ≤ ρd)
    (hed : ρd ^ 2 / 4 ≤ ed) (hgd : ed ≤ δ₀)
    (hri : 1 - (Nid : ℝ) * (Cid * h ^ (2 * r)) ≤ ρi) (hρi : 0 ≤ ρi)
    (hei : ρi ^ 2 / 4 ≤ ei) (hgi : ei ≤ δ₀) :
    (1 - 2 * Real.sqrt δ₀) / (Cdec * h ^ 2) ≤ (Ndec : ℝ) ∧
    (1 - 2 * Real.sqrt δ₀) / (Cid * h ^ (2 * r)) ≤ (Nid : ℝ) := by
  constructor
  · exact budget_lower_from_affinity Ndec Cdec (h ^ 2) ρd ed δ₀
      (by positivity) hrd hρd hed hgd hδ
  · exact budget_lower_from_affinity Nid Cid (h ^ (2 * r)) ρi ei δ₀
      (by positivity) hri hρi hei hgi hδ

/-! ## The observation's moments, bounded uniformly in the probe

The Chebyshev budgets above take a variance bound as an input.  On the CUBE that bound is
`9^4`, computed in `decision_fourth_moment_le`.  It cannot be carried over to the
observation: `Y = F + h g + xi` has Gaussian noise, whose support is unbounded, so no bound
on `|Y|` exists at all and a bound on the moments has to come from the noise's own moments.

That is what this section supplies.  The signal `F + h g` is bounded by a constant `B0` that
does not depend on `h` -- the probe contributes at most `h <= h0` -- so every moment of `Y`
is bounded by `2^n (B0^n + G_n)` with `G_n` the noise's `n`-th absolute moment, and the
bound has no `h` in it.  `G_n` is finite because all moments of a Gaussian are, which is
Mathlib's `memLp_id_gaussianReal`.

This closes the gap between the cube computation and the observation model, which is what
the sample budgets are actually about. -/

/-- A bounded shift changes a power by at most a constant factor. -/
theorem abs_pow_add_le (B0 : ℝ) (hB0 : 0 ≤ B0) (n : ℕ) (m x : ℝ) (hm : |m| ≤ B0) :
    |m + x| ^ n ≤ 2 ^ n * (B0 ^ n + |x| ^ n) := by
  have h1 : |m + x| ≤ B0 + |x| := le_trans (abs_add_le m x) (by linarith [hm])
  have hax := abs_nonneg x
  have hc : B0 + |x| ≤ 2 * max B0 |x| := by
    rcases le_total B0 |x| with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : |m + x| ^ n ≤ (2 * max B0 |x|) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) (le_trans h1 hc) n
  have h4 : (max B0 |x|) ^ n ≤ B0 ^ n + |x| ^ n := by
    rcases le_total B0 |x| with h | h
    · rw [max_eq_right h]
      have := pow_nonneg hB0 n
      linarith
    · rw [max_eq_left h]
      have := pow_nonneg hax n
      linarith
  calc |m + x| ^ n ≤ (2 * max B0 |x|) ^ n := h2
    _ = 2 ^ n * (max B0 |x|) ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (B0 ^ n + |x| ^ n) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

open MeasureTheory ProbabilityTheory in
/-- Every absolute moment of a real Gaussian is finite -- Mathlib's `memLp_id_gaussianReal`,
in the form the comparison below needs. -/
theorem integrable_abs_pow_gaussian (v : NNReal) (n : ℕ) (hn : n ≠ 0) :
    MeasureTheory.Integrable (fun x : ℝ => |x| ^ n)
      (ProbabilityTheory.gaussianReal 0 v) := by
  have h : MeasureTheory.MemLp (id : ℝ → ℝ) ((n : ℕ) : ENNReal)
      (ProbabilityTheory.gaussianReal 0 v) := by
    have hm := ProbabilityTheory.memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) (n : NNReal)
    simpa using hm
  simpa [Real.norm_eq_abs] using h.integrable_norm_pow hn

open MeasureTheory ProbabilityTheory in
/-- **The observation's `n`-th absolute moment, bounded with no `h` in the bound.**

`m` is the signal at one latent point -- `F(z) + h g(z)` -- and the only thing used about it
is `|m| <= B0`, which holds for every `h <= h0` and every probe with `||g||_inf <= 1`.  So
the same constant works along the whole family, which is what
`sup_{0 < h <= h0} Var(Y^k) < infinity` asks for. -/
theorem gaussian_shift_moment_le (v : NNReal) (n : ℕ) (hn : n ≠ 0) (B0 m : ℝ)
    (hB0 : 0 ≤ B0) (hm : |m| ≤ B0) :
    ∫ x, |m + x| ^ n ∂(ProbabilityTheory.gaussianReal 0 v)
      ≤ 2 ^ n * (B0 ^ n + ∫ x, |x| ^ n ∂(ProbabilityTheory.gaussianReal 0 v)) := by
  have hgi : MeasureTheory.Integrable (fun x : ℝ => |x| ^ n)
      (ProbabilityTheory.gaussianReal 0 v) := integrable_abs_pow_gaussian v n hn
  have hbound : MeasureTheory.Integrable
      (fun x : ℝ => 2 ^ n * (B0 ^ n + |x| ^ n))
      (ProbabilityTheory.gaussianReal 0 v) := by
    refine MeasureTheory.Integrable.const_mul ?_ _
    exact (MeasureTheory.integrable_const _).add hgi
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => |m + x| ^ n)
      (ProbabilityTheory.gaussianReal 0 v) :=
    (((continuous_const.add continuous_id).abs).pow n).aestronglyMeasurable
  have hpt : ∀ x : ℝ, |m + x| ^ n ≤ 2 ^ n * (B0 ^ n + |x| ^ n) :=
    fun x => abs_pow_add_le B0 hB0 n m x hm
  have hfi : MeasureTheory.Integrable (fun x : ℝ => |m + x| ^ n)
      (ProbabilityTheory.gaussianReal 0 v) := by
    refine MeasureTheory.Integrable.mono' hbound hmeas ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) n)]
    exact hpt x
  have hmono := MeasureTheory.integral_mono hfi hbound hpt
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add
      (MeasureTheory.integrable_const _) hgi, MeasureTheory.integral_const] at hmono
  simpa using hmono

/-! ## The estimator's error, on the observation law itself

The budgets above are arithmetic: `V / (N Delta^2) <= delta`, rearranged.  What was cited
rather than proved is that the arithmetic is ABOUT something -- that there is a probability
measure, an estimator, and an event "the estimator is wrong" whose measure it bounds.

This section supplies that, at fixed error, which is all the two exponents need.  Chebyshev
suffices; no exponential tail is required.  Independence is used in exactly one place: it
kills the cross terms in the expansion of the square. -/

open MeasureTheory in
/-- **Chebyshev, for a real random variable.**  Markov applied to the square. -/
theorem chebyshev_real {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : MeasureTheory.Integrable (fun ω => (f ω) ^ 2) μ) (t : ℝ) (ht : 0 < t) :
    t ^ 2 * μ.real {ω | t ≤ |f ω|} ≤ ∫ ω, (f ω) ^ 2 ∂μ := by
  classical
  have hsub : {ω | t ≤ |f ω|} ⊆ {ω | t ^ 2 ≤ (f ω) ^ 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    nlinarith [abs_nonneg (f ω), sq_abs (f ω), ht]
  have hmono : μ.real {ω | t ≤ |f ω|} ≤ μ.real {ω | t ^ 2 ≤ (f ω) ^ 2} :=
    MeasureTheory.measureReal_mono hsub (MeasureTheory.measure_ne_top _ _)
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := fun ω => (f ω) ^ 2)
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (f ω))) hf (t ^ 2)
  have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  refine le_trans (mul_le_mul_of_nonneg_left hmono ht2) ?_
  simpa using hmark

open MeasureTheory ProbabilityTheory in
/-- **The cross terms vanish.**  Independence plus centring. -/
theorem cross_term_zero {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hfg : ProbabilityTheory.IndepFun f g μ)
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ)
    (hf0 : ∫ ω, f ω ∂μ = 0) :
    ∫ ω, f ω * g ω ∂μ = 0 := by
  have h := ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hfg
    hf.aestronglyMeasurable hg.aestronglyMeasurable
  rw [h, hf0, zero_mul]

open MeasureTheory ProbabilityTheory in
/-- **The empirical sum's second moment.**

For independent centred observations with second moment at most `V`, the SUM of `N` of them
has second moment at most `N V`.  Dividing by `N^2` gives the empirical mean's `V/N`, which
is `estimator_error_le` below. -/
theorem second_moment_sum {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (N : ℕ) (Z : Fin N → Ω → ℝ) (V : ℝ)
    (hint : ∀ i, MeasureTheory.Integrable (Z i) μ)
    (hsq : ∀ i, MeasureTheory.Integrable (fun ω => (Z i ω) ^ 2) μ)
    (hcentre : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (Z i ω) ^ 2 ∂μ ≤ V)
    (hindep : ∀ i j, i ≠ j → ProbabilityTheory.IndepFun (Z i) (Z j) μ) :
    ∫ ω, (∑ i, Z i ω) ^ 2 ∂μ ≤ (N : ℝ) * V := by
  classical
  have hprodint : ∀ i j : Fin N,
      MeasureTheory.Integrable (fun ω => Z i ω * Z j ω) μ := by
    intro i j
    by_cases h : i = j
    · subst h
      simpa [sq] using hsq i
    · exact (hindep i j h).integrable_mul (hint i) (hint j)
  have hexp : ∀ ω, (∑ i, Z i ω) ^ 2 = ∑ i, ∑ j, Z i ω * Z j ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  have hrw : ∫ ω, (∑ i, Z i ω) ^ 2 ∂μ = ∑ i, ∑ j, ∫ ω, Z i ω * Z j ω ∂μ := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp)]
    rw [MeasureTheory.integral_finset_sum _ (fun i _ =>
      MeasureTheory.integrable_finset_sum _ (fun j _ => hprodint i j))]
    exact Finset.sum_congr rfl fun i _ =>
      MeasureTheory.integral_finset_sum _ (fun j _ => hprodint i j)
  rw [hrw]
  have hinner : ∀ i : Fin N, (∑ j, ∫ ω, Z i ω * Z j ω ∂μ) ≤ V := by
    intro i
    have hoff : ∀ j ∈ Finset.univ, j ≠ i → ∫ ω, Z i ω * Z j ω ∂μ = 0 := by
      intro j _ hji
      exact cross_term_zero μ (Z i) (Z j) (hindep i j (Ne.symm hji)) (hint i) (hint j)
        (hcentre i)
    rw [Finset.sum_eq_single i hoff (fun h => absurd (Finset.mem_univ i) h)]
    simpa [sq] using hvar i
  calc (∑ i, ∑ j, ∫ ω, Z i ω * Z j ω ∂μ) ≤ ∑ _i : Fin N, V :=
        Finset.sum_le_sum fun i _ => hinner i
    _ = (N : ℝ) * V := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

open MeasureTheory ProbabilityTheory in
/-- **The estimator's error probability, at fixed accuracy.**

`Pr(|empirical sum| >= N t) <= V / (N t^2)`.  With `t = Delta/2` and the sum divided by
`N`, this is the `4V/(N Delta^2)` the sample budgets consume -- now a statement about the
measure of an event, not a rearrangement. -/
theorem estimator_error_le {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (Z : Fin N → Ω → ℝ) (V t : ℝ) (ht : 0 < t)
    (hint : ∀ i, MeasureTheory.Integrable (Z i) μ)
    (hsq : ∀ i, MeasureTheory.Integrable (fun ω => (Z i ω) ^ 2) μ)
    (hsumsq : MeasureTheory.Integrable (fun ω => (∑ i, Z i ω) ^ 2) μ)
    (hcentre : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (Z i ω) ^ 2 ∂μ ≤ V)
    (hindep : ∀ i j, i ≠ j → ProbabilityTheory.IndepFun (Z i) (Z j) μ) :
    μ.real {ω | (N : ℝ) * t ≤ |∑ i, Z i ω|} ≤ V / ((N : ℝ) * t ^ 2) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNt : (0 : ℝ) < (N : ℝ) * t := by positivity
  have hcheb := chebyshev_real μ (fun ω => ∑ i, Z i ω) hsumsq ((N : ℝ) * t) hNt
  have hbound := second_moment_sum μ N Z V hint hsq hcentre hvar hindep
  have hkey : ((N : ℝ) * t) ^ 2 * μ.real {ω | (N : ℝ) * t ≤ |∑ i, Z i ω|}
      ≤ (N : ℝ) * V := le_trans hcheb hbound
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hkey, hNr, ht, sq_nonneg t,
    MeasureTheory.measureReal_nonneg (μ := μ) (s := {ω | (N : ℝ) * t ≤ |∑ i, Z i ω|})]

/-! ## Towards (B4): the two steps that do not need the `r`-fold expansion

(B4) asks for `sup_g H^2 <= C_r h^(2r)` with the constant free of `h` and `g`.  The route
that avoids checking Taylor coefficients one at a time has four steps: separate head from
tail; replace the alternating sum over the tail cube by an `r`-th order finite difference;
bound the difference by `h^r prod|a_i|` and then by `h^r r^(-r)` with AM-GM; and convert a
pointwise density gap into a Hellinger bound against a Gaussian lower envelope.

Two of those steps are self-contained, and they are proved here.

  * `finite_difference_one`: the one-dimensional identity the `r`-fold version inducts on.
    `(f(x-b) - f(x+b)) = -b * int_{-1}^{1} f'(x - b t) dt`, from the fundamental theorem of
    calculus applied to `t |-> f(x - b t)`.
  * `hellinger_le_of_gap`: the conversion, pointwise, `(sqrt p - sqrt q)^2 <=
    (p-q)^2 / (4 l)` whenever `l` is a positive lower envelope for both densities.  This is
    what turns a density gap into a Hellinger bound without any integral manipulation.

WHAT IS NOT HERE, precisely: the `r`-fold induction that iterates `finite_difference_one`
into `2^{-r} sum_z chi(z) f(x - sum b_i z_i) = (-1)^r (prod b_i) E_U f^(r)(x - sum b_i U_i)`,
and the construction of the integrable Gaussian envelope that makes
`int B_r^2 / l` finite.  Both are analysis developments -- iterated interval integrals,
differentiation under the integral sign, and a completed-square integrability argument --
and neither is attempted below. -/

/-- **The one-dimensional finite-difference identity.**  The base case of the `r`-fold
expansion: the symmetric difference of `f` is an averaged first derivative. -/
theorem finite_difference_one (f f' : ℝ → ℝ) (hderiv : ∀ y, HasDerivAt f (f' y) y)
    (hcont : Continuous f') (x b : ℝ) :
    f (x - b) - f (x + b) = -b * ∫ t in (-1 : ℝ)..1, f' (x - b * t) := by
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (x - b * s)) (-b * f' (x - b * t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => x - b * s) (-b) t := by
      simpa using ((hasDerivAt_id t).const_mul b).const_sub x
    have hc := HasDerivAt.comp t (hderiv (x - b * t)) h1
    simpa [Function.comp_def, mul_comm] using hc
  have hint : IntervalIntegrable (fun t : ℝ => -b * f' (x - b * t)) MeasureTheory.volume
      (-1) 1 := by
    refine (Continuous.intervalIntegrable ?_ _ _)
    exact continuous_const.mul (hcont.comp (continuous_const.sub (continuous_const.mul
      continuous_id)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hg t) hint
  have hrw : ∫ t in (-1 : ℝ)..1, -b * f' (x - b * t)
      = -b * ∫ t in (-1 : ℝ)..1, f' (x - b * t) := by
    rw [intervalIntegral.integral_const_mul]
  rw [hrw] at hftc
  have hL : f (x - b * 1) = f (x - b) := by norm_num
  have hR : f (x - b * (-1)) = f (x + b) := by
    congr 1
    ring
  rw [hL, hR] at hftc
  linarith [hftc]

/-- **From a pointwise density gap to a Hellinger gap.**

`(sqrt p - sqrt q)^2 = (p-q)^2 / (sqrt p + sqrt q)^2`, and a common positive lower envelope
`l` bounds the denominator below by `4 l`.  This is the step that converts the `h^r`
density bound into an `h^(2r)` Hellinger bound, and it needs no integral. -/
theorem hellinger_le_of_gap (p q l : ℝ) (hl : 0 < l) (hp : l ≤ p) (hq : l ≤ q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ (p - q) ^ 2 / (4 * l) := by
  have hp0 : 0 ≤ p := le_trans hl.le hp
  have hq0 : 0 ≤ q := le_trans hl.le hq
  have hsp : Real.sqrt l ≤ Real.sqrt p := Real.sqrt_le_sqrt hp
  have hsq : Real.sqrt l ≤ Real.sqrt q := Real.sqrt_le_sqrt hq
  have hl0 : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hsum : 2 * Real.sqrt l ≤ Real.sqrt p + Real.sqrt q := by linarith
  have hsumpos : 0 < Real.sqrt p + Real.sqrt q := by linarith
  have hfac : (Real.sqrt p - Real.sqrt q) * (Real.sqrt p + Real.sqrt q) = p - q := by
    have h1 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0
    have h2 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
    nlinarith [h1, h2]
  have hsq4 : 4 * l ≤ (Real.sqrt p + Real.sqrt q) ^ 2 := by
    have hll : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl.le
    nlinarith [hsum, hl0, hll]
  rw [le_div_iff₀ (by positivity)]
  have hgap : (p - q) ^ 2 = (Real.sqrt p - Real.sqrt q) ^ 2
      * (Real.sqrt p + Real.sqrt q) ^ 2 := by
    rw [← mul_pow, hfac]
  rw [hgap]
  have hnn : (0 : ℝ) ≤ (Real.sqrt p - Real.sqrt q) ^ 2 := sq_nonneg _
  nlinarith [hsq4, hnn]

/-! ### The `r`-fold difference, by induction

`finite_difference_one` is the base step.  Iterating it `r` times gives the bound the
identification argument needs.  The exact identity carries an `r`-fold average of the
`r`-th derivative; what the argument USES is only its size, so the induction below carries
the bound instead and never has to build an `r`-fold product integral.

    | D_{b_1} ... D_{b_r} f (x) |  <=  (prod |b_i|) * sup |f^(r)|,

with `D_b f (x) = (f(x-b) - f(x+b)) / 2` the symmetric difference.  On the sign cube the
alternating sum over the tail is exactly such an iterate, with `b_i = h a_i`, so the bound
reads `h^r (prod |a_i|) sup |f^(r)|` -- and AM-GM turns `prod |a_i|` into `r^(-r)` under
`sum |a_i| <= 1`. -/

/-- The symmetric difference at scale `b`. -/
noncomputable def symDiff (f : ℝ → ℝ) (b x : ℝ) : ℝ := (f (x - b) - f (x + b)) / 2

/-- The symmetric difference differentiates termwise. -/
theorem symDiff_hasDerivAt (f f' : ℝ → ℝ) (hderiv : ∀ y, HasDerivAt f (f' y) y) (b x : ℝ) :
    HasDerivAt (symDiff f b) (symDiff f' b x) x := by
  unfold symDiff
  have h1 : HasDerivAt (fun y => f (y - b)) (f' (x - b)) x := by
    simpa [Function.comp_def] using
      HasDerivAt.comp x (hderiv (x - b)) ((hasDerivAt_id x).sub_const b)
  have h2 : HasDerivAt (fun y => f (y + b)) (f' (x + b)) x := by
    simpa [Function.comp_def] using
      HasDerivAt.comp x (hderiv (x + b)) ((hasDerivAt_id x).add_const b)
  simpa using (h1.sub h2).div_const 2

/-- **One difference costs one factor of `|b|` and one derivative.** -/
theorem symDiff_abs_le (f f' : ℝ → ℝ) (hderiv : ∀ y, HasDerivAt f (f' y) y)
    (hcont : Continuous f') (C : ℝ) (hC : ∀ y, |f' y| ≤ C) (b x : ℝ) :
    |symDiff f b x| ≤ |b| * C := by
  have hid := finite_difference_one f f' hderiv hcont x b
  have hnorm : ‖∫ t in (-1 : ℝ)..1, f' (x - b * t)‖ ≤ C * |(1 : ℝ) - (-1)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t _
    simpa [Real.norm_eq_abs] using hC (x - b * t)
  have habs : |∫ t in (-1 : ℝ)..1, f' (x - b * t)| ≤ 2 * C := by
    have h2 : |(1 : ℝ) - (-1)| = 2 := by norm_num
    rw [Real.norm_eq_abs, h2] at hnorm
    linarith [hnorm]
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (f' x)) (hC x)
  unfold symDiff
  rw [hid]
  rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  have hb : 0 ≤ |b| := abs_nonneg b
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith [habs, hb, hC0, abs_nonneg (∫ t in (-1 : ℝ)..1, f' (x - b * t))]

/-- The iterated symmetric difference along a list of scales. -/
noncomputable def iterDiff (f : ℝ → ℝ) : List ℝ → ℝ → ℝ
  | [], x => f x
  | b :: bs, x => symDiff (iterDiff f bs) b x

theorem iterDiff_nil (f : ℝ → ℝ) (x : ℝ) : iterDiff f [] x = f x := rfl

theorem iterDiff_cons (f : ℝ → ℝ) (b : ℝ) (bs : List ℝ) (x : ℝ) :
    iterDiff f (b :: bs) x = symDiff (iterDiff f bs) b x := rfl

/-- The iterate differentiates termwise, level by level. -/
theorem iterDiff_hasDerivAt (D : ℕ → ℝ → ℝ)
    (hD : ∀ k y, HasDerivAt (D k) (D (k + 1) y) y) :
    ∀ (bs : List ℝ) (k : ℕ) (x : ℝ),
      HasDerivAt (iterDiff (D k) bs) (iterDiff (D (k + 1)) bs x) x := by
  intro bs
  induction bs with
  | nil => intro k x; exact hD k x
  | cons b bs ih =>
      intro k x
      simp only [iterDiff_cons]
      exact symDiff_hasDerivAt (iterDiff (D k) bs) (iterDiff (D (k + 1)) bs)
        (fun y => ih k y) b x

theorem iterDiff_continuous (D : ℕ → ℝ → ℝ) (hcont : ∀ k, Continuous (D k)) :
    ∀ (bs : List ℝ) (k : ℕ), Continuous (iterDiff (D k) bs) := by
  intro bs
  induction bs with
  | nil => intro k; exact hcont k
  | cons b bs ih =>
      intro k
      show Continuous (fun x => symDiff (iterDiff (D k) bs) b x)
      unfold symDiff
      exact (((ih k).comp (continuous_id.sub continuous_const)).sub
        ((ih k).comp (continuous_id.add continuous_const))).div_const 2

/-- **The `r`-fold difference bound.**  Each scale contributes its own factor, and the
whole iterate is controlled by a bound on the `r`-th derivative. -/
theorem iterDiff_abs_le (D : ℕ → ℝ → ℝ)
    (hD : ∀ k y, HasDerivAt (D k) (D (k + 1) y) y) (hcont : ∀ k, Continuous (D k))
    (C : ℝ) :
    ∀ (bs : List ℝ) (k : ℕ), (∀ y, |D (k + bs.length) y| ≤ C) →
      ∀ x, |iterDiff (D k) bs x| ≤ (bs.map (fun b => |b|)).prod * C := by
  intro bs
  induction bs with
  | nil =>
      intro k hCk x
      show |D k x| ≤ ([].map (fun b : ℝ => |b|)).prod * C
      simpa using hCk x
  | cons b bs ih =>
      intro k hCk x
      have hshift : ∀ y, |D (k + 1 + bs.length) y| ≤ C := by
        intro y
        have : k + 1 + bs.length = k + (b :: bs).length := by
          simp [List.length_cons]
          omega
        rw [this]
        exact hCk y
      have hinner := ih (k + 1) hshift
      have hstep := symDiff_abs_le (iterDiff (D k) bs) (iterDiff (D (k + 1)) bs)
        (fun y => iterDiff_hasDerivAt D hD bs k y)
        (iterDiff_continuous D hcont bs (k + 1))
        ((bs.map (fun b => |b|)).prod * C) hinner b x
      simp only [iterDiff_cons, List.map_cons, List.prod_cons]
      calc |symDiff (iterDiff (D k) bs) b x|
          ≤ |b| * ((bs.map (fun b => |b|)).prod * C) := hstep
        _ = |b| * (bs.map (fun b => |b|)).prod * C := by ring

/-- **AM-GM, in the form the probe class needs.**  If the probe's coefficients have
`l^1` norm at most one, their product is at most `r^(-r)`. -/
theorem prod_abs_le_of_sum_le_one (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∑ i, |a i| ≤ 1) :
    ∏ i, |a i| ≤ (1 / (n : ℝ)) ^ n := by
  classical
  have hnn : ∀ i, (0 : ℝ) ≤ |a i| := fun i => abs_nonneg _
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkey := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin n => (1 : ℝ) / (n : ℝ)) (fun i => |a i|)
    (fun i _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp)
    (fun i _ => hnn i)
  have hprod : ∏ i, |a i| ^ ((1 : ℝ) / (n : ℝ)) ≤ ∑ i, (1 / (n : ℝ)) * |a i| := hkey
  have hrhs : ∑ i, (1 / (n : ℝ)) * |a i| ≤ 1 / (n : ℝ) := by
    rw [← Finset.mul_sum]
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    nlinarith [ha, this]
  have hpp : (0 : ℝ) ≤ ∏ i, |a i| := Finset.prod_nonneg (fun i _ => hnn i)
  have hrw : ∏ i, |a i| ^ ((1 : ℝ) / (n : ℝ)) = (∏ i, |a i|) ^ ((1 : ℝ) / (n : ℝ)) := by
    rw [← Real.finset_prod_rpow _ _ (fun i _ => hnn i)]
  rw [hrw] at hprod
  have hle : (∏ i, |a i|) ^ ((1 : ℝ) / (n : ℝ)) ≤ 1 / (n : ℝ) := le_trans hprod hrhs
  have hpow := Real.rpow_le_rpow (by positivity) hle (le_of_lt hnr)
  rw [← Real.rpow_mul hpp, one_div, inv_mul_cancel₀ (ne_of_gt hnr), Real.rpow_one] at hpow
  calc ∏ i, |a i| ≤ ((n : ℝ))⁻¹ ^ (n : ℝ) := hpow
    _ = (1 / (n : ℝ)) ^ n := by rw [Real.rpow_natCast, one_div]

/-! ### The envelope: why `int B_r^2 / l` is finite

The last input to (B4) is that the Hellinger integral converges.  Both mixture densities are
bounded below by a Gaussian times a linear exponential -- the means live in `[-R, R]`, so
the worst component is the farthest one -- and the `r`-th derivative of a Gaussian is a
polynomial times a Gaussian.  Dividing one by the other leaves

    polynomial(|y|) * exp( -b y^2 + c |y| ),

and completing the square makes that integrable.  That is the content, and it is proved
here in the form the assembly needs. -/

/-- **Completing the square.**  A linear term in `|y|` costs only a constant against a
quadratic one. -/
theorem exp_quad_linear_le (b c y : ℝ) (hb : 0 < b) :
    Real.exp (-(b * y ^ 2) + c * |y|)
      ≤ Real.exp (c ^ 2 / (2 * b)) * Real.exp (-(b / 2 * y ^ 2)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hy : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have hkey : c * |y| ≤ b / 2 * |y| ^ 2 + c ^ 2 / (2 * b) := by
    have hid : b / 2 * |y| ^ 2 - c * |y| + c ^ 2 / (2 * b)
        = (b * |y| - c) ^ 2 / (2 * b) := by
      field_simp
      ring
    have hnn : (0 : ℝ) ≤ (b * |y| - c) ^ 2 / (2 * b) := by positivity
    rw [← hid] at hnn
    linarith
  rw [hy]
  linarith [hkey]

/-- **The envelope bound, assembled as far as the square-completion carries it.**

`exp_quad_linear_le` is the mathematical step: the linear term costs a constant and a
widening of the Gaussian.  What it reduces the envelope's convergence to is the standard
fact that a power times a Gaussian is integrable, and the assembly of that with the
explicit `B_r` and `l` of the construction is not carried out here. -/
theorem exp_quad_linear_le_const (b c : ℝ) (hb : 0 < b) (y : ℝ) :
    Real.exp (-(b * y ^ 2) + c * |y|) ≤ Real.exp (c ^ 2 / (2 * b)) :=
  le_trans (exp_quad_linear_le b c y hb)
    (by
      have h1 : Real.exp (-(b / 2 * y ^ 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg y, hb]
      nlinarith [h1, Real.exp_pos (c ^ 2 / (2 * b))])

/-! ### B4.1, second step: the iterate IS the alternating sum over the sign cube

`iterDiff` is defined by recursion; the model produces an alternating sum over
`{-1,+1}^r`.  They are the same object, and this is the bookkeeping that says so:

    D_{b_1} ... D_{b_r} f (x)  =  2^{-r} sum_z chi(z) f(x - sum_i b_i z_i).

With that, `iterDiff_abs_le` applies directly to the density difference of the two worlds,
and the `h^r prod|a_i|` bound follows. -/

/-- The sign attached to a cube coordinate. -/
def sgnB (b : Bool) : ℝ := if b then 1 else -1

theorem sgnB_sq (b : Bool) : sgnB b * sgnB b = 1 := by
  cases b <;> norm_num [sgnB]

/-- **The iterate is the alternating sum.** -/
theorem iterDiff_eq_signSum :
    ∀ (n : ℕ) (f : ℝ → ℝ) (b : Fin n → ℝ) (x : ℝ),
      iterDiff f (List.ofFn b) x
        = (2 : ℝ)⁻¹ ^ n * ∑ z : Fin n → Bool,
            (∏ i, sgnB (z i)) * f (x - ∑ i, b i * sgnB (z i)) := by
  intro n
  induction n with
  | zero =>
      intro f b x
      simp [iterDiff_nil]
  | succ m ih =>
      intro f b x
      rw [show List.ofFn b = b 0 :: List.ofFn (fun i : Fin m => b i.succ) from
        List.ofFn_succ, iterDiff_cons]
      have hL := ih f (fun i : Fin m => b i.succ) (x - b 0)
      have hR := ih f (fun i : Fin m => b i.succ) (x + b 0)
      unfold symDiff
      rw [hL, hR]
      have hcube : ∑ z : Fin (m + 1) → Bool,
            (∏ i, sgnB (z i)) * f (x - ∑ i, b i * sgnB (z i))
          = ∑ p : Bool × (Fin m → Bool),
              (∏ i, sgnB ((Fin.cons p.1 p.2 : Fin (m + 1) → Bool) i))
                * f (x - ∑ i, b i * sgnB ((Fin.cons p.1 p.2 : Fin (m + 1) → Bool) i)) := by
        refine (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)) _ _
          (fun p => ?_)).symm
        rfl
      rw [hcube, Fintype.sum_prod_type, Fintype.sum_bool]
      have hst : sgnB true = 1 := rfl
      have hsf : sgnB false = -1 := rfl
      have hhalf : ∀ c : Bool, ∀ w : Fin m → Bool,
          (∏ i, sgnB ((Fin.cons c w : Fin (m + 1) → Bool) i))
            * f (x - ∑ i, b i * sgnB ((Fin.cons c w : Fin (m + 1) → Bool) i))
            = sgnB c * ((∏ i, sgnB (w i))
              * f (x - b 0 * sgnB c - ∑ i : Fin m, b i.succ * sgnB (w i))) := by
        intro c w
        rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [show x - (b 0 * sgnB c + ∑ i : Fin m, b i.succ * sgnB (w i))
            = x - b 0 * sgnB c - ∑ i : Fin m, b i.succ * sgnB (w i) from by ring]
        ring
      have hT : ∀ w : Fin m → Bool,
          sgnB true * ((∏ i, sgnB (w i))
              * f (x - b 0 * sgnB true - ∑ i : Fin m, b i.succ * sgnB (w i)))
            = (∏ i, sgnB (w i))
              * f (x - b 0 - ∑ i : Fin m, b i.succ * sgnB (w i)) := by
        intro w
        rw [hst, one_mul,
            show x - b 0 * (1 : ℝ) - ∑ i : Fin m, b i.succ * sgnB (w i)
              = x - b 0 - ∑ i : Fin m, b i.succ * sgnB (w i) from by ring]
      have hF : ∀ w : Fin m → Bool,
          sgnB false * ((∏ i, sgnB (w i))
              * f (x - b 0 * sgnB false - ∑ i : Fin m, b i.succ * sgnB (w i)))
            = -((∏ i, sgnB (w i))
              * f (x + b 0 - ∑ i : Fin m, b i.succ * sgnB (w i))) := by
        intro w
        rw [hsf,
            show x - b 0 * (-1 : ℝ) - ∑ i : Fin m, b i.succ * sgnB (w i)
              = x + b 0 - ∑ i : Fin m, b i.succ * sgnB (w i) from by ring]
        ring
      rw [Finset.sum_congr rfl (fun w _ => hhalf true w),
          Finset.sum_congr rfl (fun w _ => hhalf false w),
          Finset.sum_congr rfl (fun w _ => hT w), Finset.sum_congr rfl (fun w _ => hF w),
          Finset.sum_neg_distrib]
      ring

/-! ### B4.1 and B4.3: the sign identity, and the lower envelope

Two more pieces of the route, both self-contained.

`sign_shift_identity` is B4.1's first step: on the sign cube, the difference of the two
worlds' Gaussian components at a latent point is the SAME function of the shifted argument,
times the sign.  That is what lets the alternating sum over the cube be read as an iterated
symmetric difference of the single function `f_sigma(x) = phi(x-1) - phi(x+1)`.

`gaussian_lower_envelope` is B4.3: every Gaussian component whose centre lies in `[-R, R]`
is bounded below by one fixed function of `y`.  Since each density is a mixture of such
components with non-negative weights summing to one, the same bound holds for the density,
which is what makes the Hellinger denominator harmless. -/

/-- The unnormalised Gaussian kernel. -/
noncomputable def gkern (σ y : ℝ) : ℝ := Real.exp (-(y ^ 2) / (2 * σ ^ 2))

/-- **B4.1, first step.**  With `chi = +-1`, the two worlds' components at a latent point
differ by `chi` times one fixed function of the shifted argument. -/
theorem sign_shift_identity (σ x s chi : ℝ) (hchi : chi = 1 ∨ chi = -1) :
    gkern σ (x - chi - s) - gkern σ (x + chi - s)
      = chi * (gkern σ (x - s - 1) - gkern σ (x - s + 1)) := by
  rcases hchi with h | h <;> subst h
  · have e1 : x - 1 - s = x - s - 1 := by ring
    have e2 : x + 1 - s = x - s + 1 := by ring
    rw [e1, e2]
    ring
  · have e1 : x - (-1) - s = x - s + 1 := by ring
    have e2 : x + (-1) - s = x - s - 1 := by ring
    rw [e1, e2]
    ring

/-- **B4.3, the lower envelope.**  A Gaussian centred anywhere in `[-R, R]` dominates one
fixed function of `y`, with the centre appearing only through `R`. -/
theorem gaussian_lower_envelope (σ R y c : ℝ) (hσ : 0 < σ) (hc : |c| ≤ R) :
    gkern σ y * Real.exp (-(R * |y|) / σ ^ 2) * Real.exp (-(R ^ 2) / (2 * σ ^ 2))
      ≤ gkern σ (y - c) := by
  unfold gkern
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hR : 0 ≤ R := le_trans (abs_nonneg c) hc
  have hncy : -(R * |y|) ≤ c * y := by
    have h1 : -|c * y| ≤ c * y := neg_abs_le _
    have h2 : |c * y| = |c| * |y| := abs_mul c y
    have h3 : |c| * |y| ≤ R * |y| := mul_le_mul_of_nonneg_right hc (abs_nonneg y)
    linarith [h1, h2.le, h2.ge, h3]
  have hc2 : c ^ 2 ≤ R ^ 2 := by
    have hsq : |c| ^ 2 ≤ R ^ 2 := by nlinarith [hc, abs_nonneg c, hR]
    rwa [sq_abs] at hsq
  have hnum : (0 : ℝ) ≤ 2 * (c * y) + 2 * R * |y| + R ^ 2 - c ^ 2 := by
    linarith [hncy, hc2]
  have hgoal : -((y - c) ^ 2) / (2 * σ ^ 2)
      - (-(y ^ 2) / (2 * σ ^ 2) + -(R * |y|) / σ ^ 2 + -(R ^ 2) / (2 * σ ^ 2))
      = (2 * (c * y) + 2 * R * |y| + R ^ 2 - c ^ 2) / (2 * σ ^ 2) := by
    field_simp
    ring
  have hpos : (0 : ℝ) ≤ (2 * (c * y) + 2 * R * |y| + R ^ 2 - c ^ 2) / (2 * σ ^ 2) :=
    div_nonneg hnum (by positivity)
  linarith [hgoal.le, hgoal.ge, hpos]

/-! ### B4.2, B4.4 and B4.5: the Gaussian envelope, its integrability, and the rate

What remains of (B4) after the sign identity and the lower envelope is three things:
a bound on the `r`-th derivative of a Gaussian, the finiteness of the Hellinger
denominator against it, and the assembly of the two into the `h^{2r}` rate.

`hermP` is the Hermite-like polynomial sequence with `phi^{(n)} = hermP n * phi`, built
here because the derivative of a polynomial times a Gaussian is again one.  Its degree is
at most `n`, so `|phi^{(n)}(y)| <= A_n (1+|y|)^n phi(y)` -- that is B4.2, and `A_n` is the
coefficient mass, an explicit number.

B4.4 then bounds `envUp^2 / envLo` by a single Gaussian.  The polynomial is absorbed by
`1 + x <= exp x`, and BOTH linear exponentials -- the one from the upper envelope and the
one from the lower -- by completing the square.  No polynomial-times-Gaussian
integrability lemma is needed: what is left is `exp(-y^2/(4 sigma^2))`.

B4.5 is the assembly.  It needs the `r`-fold difference bound to be LOCAL: the global
`iterDiff_abs_le` would force a uniform bound on the `r`-th derivative, which a Gaussian
envelope is not.  `iterDiff_abs_le_window` is the localised version -- only the window of
radius `sum |b_i|` around `x` matters -- and `iterDiff_gkern_envelope` pays for it by
widening `R` to `R + h_0`.  With the probe's `l^1` constraint supplying `prod |a_i| <=
r^{-r}` through `prod_abs_le_of_sum_le_one`, the conclusion is

    int (Delta^2 / l) <= h^{2r} r^{-2r} * C(sigma, R + h_0, r),      C finite.

That is the upper bound (B4) asserts, with every constant explicit. -/

section B4Envelope

open MeasureTheory

theorem gkern_pos (σ y : ℝ) : 0 < gkern σ y := Real.exp_pos _

/-- The Hermite-like polynomial sequence: `φ^{(n)} = hermP n · φ`. -/
noncomputable def hermP (σ : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => Polynomial.derivative (hermP σ n)
      - (Polynomial.C (σ ^ 2)⁻¹ * Polynomial.X) * hermP σ n

theorem hermP_zero (σ : ℝ) : hermP σ 0 = 1 := rfl

theorem hermP_succ (σ : ℝ) (n : ℕ) :
    hermP σ (n + 1) = Polynomial.derivative (hermP σ n)
      - (Polynomial.C (σ ^ 2)⁻¹ * Polynomial.X) * hermP σ n := rfl

theorem hermP_natDegree_le (σ : ℝ) : ∀ n, (hermP σ n).natDegree ≤ n := by
  intro n
  induction n with
  | zero => simp [hermP_zero]
  | succ n ih =>
      rw [hermP_succ]
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      refine max_le ?_ ?_
      · exact le_trans (Polynomial.natDegree_derivative_le _) (by omega)
      · refine le_trans (Polynomial.natDegree_mul_le) ?_
        have h1 : (Polynomial.C (σ ^ 2)⁻¹ * Polynomial.X).natDegree ≤ 1 := by
          refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
          simp
        omega

/-- The `n`-th derivative of the Gaussian kernel, as polynomial times kernel. -/
noncomputable def gaussDeriv (σ : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  (hermP σ n).eval y * gkern σ y

theorem gaussDeriv_zero (σ y : ℝ) : gaussDeriv σ 0 y = gkern σ y := by
  simp [gaussDeriv, hermP_zero]

theorem gkern_hasDerivAt (σ : ℝ) (hσ : σ ≠ 0) (y : ℝ) :
    HasDerivAt (gkern σ) (-((σ ^ 2)⁻¹ * y) * gkern σ y) y := by
  have hσ2 : (σ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have h0 := hasDerivAt_pow 2 y
  norm_num at h0
  have hin : HasDerivAt (fun x : ℝ => -(x ^ 2) / (2 * σ ^ 2)) (-(2 * y) / (2 * σ ^ 2)) y :=
    h0.neg.div_const _
  have hexp := hin.exp
  have heq : Real.exp (-(y ^ 2) / (2 * σ ^ 2)) * (-(2 * y) / (2 * σ ^ 2))
      = -((σ ^ 2)⁻¹ * y) * Real.exp (-(y ^ 2) / (2 * σ ^ 2)) := by
    field_simp
  rw [heq] at hexp
  exact hexp

theorem gaussDeriv_hasDerivAt (σ : ℝ) (hσ : σ ≠ 0) (n : ℕ) (y : ℝ) :
    HasDerivAt (gaussDeriv σ n) (gaussDeriv σ (n + 1) y) y := by
  have hp := (hermP σ n).hasDerivAt y
  have hg := gkern_hasDerivAt σ hσ y
  have hm := hp.mul hg
  have heq : Polynomial.eval y (Polynomial.derivative (hermP σ n)) * gkern σ y
        + Polynomial.eval y (hermP σ n) * (-((σ ^ 2)⁻¹ * y) * gkern σ y)
      = gaussDeriv σ (n + 1) y := by
    unfold gaussDeriv
    rw [hermP_succ]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [heq] at hm
  exact hm

theorem gaussDeriv_continuous (σ : ℝ) (n : ℕ) : Continuous (gaussDeriv σ n) :=
  Continuous.mul (Polynomial.continuous _) (by unfold gkern; fun_prop)

/-- A polynomial of degree at most `n` is dominated by `(1+|y|)^n` times its
coefficient mass. -/
theorem poly_eval_abs_le (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n) (y : ℝ) :
    |p.eval y| ≤ (∑ i ∈ Finset.range (n + 1), |p.coeff i|) * (1 + |y|) ^ n := by
  classical
  have hy : (0 : ℝ) ≤ |y| := abs_nonneg y
  have h1 : (1 : ℝ) ≤ 1 + |y| := by linarith
  rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < n + 1)]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hin : i ≤ n := by
    have := Finset.mem_range.mp hi; omega
  rw [abs_mul, abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |y| ^ i ≤ (1 + |y|) ^ i := pow_le_pow_left₀ hy (by linarith) i
    _ ≤ (1 + |y|) ^ n := pow_le_pow_right₀ h1 hin

/-- **B4.2.**  The `n`-th derivative of the Gaussian kernel is bounded by a fixed
constant times `(1+|y|)^n` times the kernel itself. -/
noncomputable def hermMass (σ : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), |(hermP σ n).coeff i|

theorem hermMass_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ hermMass σ n :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem gaussDeriv_envelope (σ : ℝ) (n : ℕ) (y : ℝ) :
    |gaussDeriv σ n y| ≤ hermMass σ n * (1 + |y|) ^ n * gkern σ y := by
  unfold gaussDeriv hermMass
  rw [abs_mul, abs_of_pos (gkern_pos σ y)]
  exact mul_le_mul_of_nonneg_right
    (poly_eval_abs_le _ n (hermP_natDegree_le σ n) y) (le_of_lt (gkern_pos σ y))

/-- **B4.3, the upper envelope.**  The mirror of `gaussian_lower_envelope`. -/
theorem gaussian_upper_envelope (σ R y c : ℝ) (hσ : 0 < σ) (hc : |c| ≤ R) :
    gkern σ (y - c) ≤ gkern σ y * Real.exp (R * |y| / σ ^ 2) := by
  unfold gkern
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hcy : c * y ≤ R * |y| := by
    have h1 : c * y ≤ |c * y| := le_abs_self _
    have h2 : |c * y| = |c| * |y| := abs_mul c y
    have h3 : |c| * |y| ≤ R * |y| := mul_le_mul_of_nonneg_right hc (abs_nonneg y)
    linarith [h1, h2.le, h2.ge, h3]
  have hgoal : -(y ^ 2) / (2 * σ ^ 2) + R * |y| / σ ^ 2 - -((y - c) ^ 2) / (2 * σ ^ 2)
      = (2 * (R * |y|) - 2 * (c * y) + c ^ 2) / (2 * σ ^ 2) := by
    field_simp; ring
  have hnum : (0 : ℝ) ≤ 2 * (R * |y|) - 2 * (c * y) + c ^ 2 := by nlinarith [hcy, sq_nonneg c]
  have hpos : (0 : ℝ) ≤ (2 * (R * |y|) - 2 * (c * y) + c ^ 2) / (2 * σ ^ 2) :=
    div_nonneg hnum (by positivity)
  linarith [hgoal.le, hgoal.ge, hpos]

/-- The upper envelope for the `r`-th derivative, uniform over centres in `[-R, R]`. -/
noncomputable def envUp (σ R : ℝ) (r : ℕ) (y : ℝ) : ℝ :=
  hermMass σ r * (1 + R + |y|) ^ r * gkern σ y * Real.exp (R * |y| / σ ^ 2)

/-- The lower envelope for the mixture density. -/
noncomputable def envLo (σ R : ℝ) (y : ℝ) : ℝ :=
  gkern σ y * Real.exp (-(R * |y|) / σ ^ 2) * Real.exp (-(R ^ 2) / (2 * σ ^ 2))

theorem envLo_pos (σ R y : ℝ) : 0 < envLo σ R y := by
  unfold envLo gkern; positivity

theorem envUp_nonneg (σ R : ℝ) (r : ℕ) (y : ℝ) (hR : 0 ≤ R) : 0 ≤ envUp σ R r y := by
  unfold envUp
  have h1 : (0 : ℝ) ≤ (1 + R + |y|) ^ r :=
    pow_nonneg (by linarith [abs_nonneg y]) r
  exact mul_nonneg (mul_nonneg (mul_nonneg (hermMass_nonneg σ r) h1)
    (gkern_pos σ y).le) (Real.exp_pos _).le

/-- **B4.2 + B4.3, combined.**  Uniformly over centres in `[-R, R]`, the `r`-th derivative
of the shifted Gaussian is under one fixed envelope. -/
theorem gaussDeriv_shift_envelope (σ R : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (r : ℕ) (c y : ℝ)
    (hc : |c| ≤ R) : |gaussDeriv σ r (y - c)| ≤ envUp σ R r y := by
  have hstep := gaussDeriv_envelope σ r (y - c)
  have hshift : gkern σ (y - c) ≤ gkern σ y * Real.exp (R * |y| / σ ^ 2) :=
    gaussian_upper_envelope σ R y c hσ hc
  have hyc : |y - c| ≤ R + |y| := by
    have := abs_sub_abs_le_abs_sub y c
    have h2 : |y - c| ≤ |y| + |c| := abs_sub _ _
    linarith [h2, hc]
  have hpoly : (1 + |y - c|) ^ r ≤ (1 + R + |y|) ^ r :=
    pow_le_pow_left₀ (by positivity) (by linarith) r
  have hmass := hermMass_nonneg σ r
  have hg := gkern_pos σ y
  have hgc := gkern_pos σ (y - c)
  calc |gaussDeriv σ r (y - c)|
      ≤ hermMass σ r * (1 + |y - c|) ^ r * gkern σ (y - c) := hstep
    _ ≤ hermMass σ r * (1 + R + |y|) ^ r * (gkern σ y * Real.exp (R * |y| / σ ^ 2)) := by
        have h1 : hermMass σ r * (1 + |y - c|) ^ r
            ≤ hermMass σ r * (1 + R + |y|) ^ r :=
          mul_le_mul_of_nonneg_left hpoly hmass
        have hnn : (0 : ℝ) ≤ hermMass σ r * (1 + |y - c|) ^ r := by positivity
        nlinarith [hgc.le, hshift, h1, hnn]
    _ = envUp σ R r y := by unfold envUp; ring

/-- The constant in the envelope's Gaussian bound. -/
noncomputable def envConst (σ R : ℝ) (r : ℕ) : ℝ :=
  hermMass σ r ^ 2 * Real.exp (2 * r * R) * Real.exp (R ^ 2 / (2 * σ ^ 2))
    * Real.exp ((3 * R / σ ^ 2 + 2 * r) ^ 2 * σ ^ 2)

/-- **B4.4, the pointwise step.**  The Hellinger integrand's envelope is under a
Gaussian: the polynomial and both linear exponentials are absorbed. -/
theorem envRatio_le (σ R : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (r : ℕ) (y : ℝ) :
    envUp σ R r y ^ 2 / envLo σ R y
      ≤ envConst σ R r * Real.exp (-(1 / (4 * σ ^ 2)) * y ^ 2) := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hy : (0 : ℝ) ≤ |y| := abs_nonneg y
  have hAnn : (0 : ℝ) ≤ hermMass σ r := hermMass_nonneg σ r
  have hupeq : envUp σ R r y = hermMass σ r * (1 + R + |y|) ^ r
      * Real.exp (-(y ^ 2) / (2 * σ ^ 2) + R * |y| / σ ^ 2) := by
    unfold envUp gkern; rw [Real.exp_add]; ring
  have hloeq : envLo σ R y
      = Real.exp (-(y ^ 2) / (2 * σ ^ 2) + -(R * |y|) / σ ^ 2 + -(R ^ 2) / (2 * σ ^ 2)) := by
    unfold envLo gkern; rw [Real.exp_add, Real.exp_add]
  rw [hupeq, hloeq, mul_pow, mul_pow, pow_two (Real.exp _), ← Real.exp_add,
    mul_div_assoc, ← Real.exp_sub]
  -- the exponent collapses
  have hTeq : (-(y ^ 2) / (2 * σ ^ 2) + R * |y| / σ ^ 2
        + (-(y ^ 2) / (2 * σ ^ 2) + R * |y| / σ ^ 2))
      - (-(y ^ 2) / (2 * σ ^ 2) + -(R * |y|) / σ ^ 2 + -(R ^ 2) / (2 * σ ^ 2))
      = (-(1 / (2 * σ ^ 2) * y ^ 2) + (3 * R / σ ^ 2) * |y|) + R ^ 2 / (2 * σ ^ 2) := by
    field_simp; ring
  rw [hTeq, Real.exp_add]
  -- the polynomial factor
  have hbase : (1 : ℝ) + R + |y| ≤ Real.exp (R + |y|) := by
    have := Real.add_one_le_exp (R + |y|)
    linarith
  have hPow : (1 + R + |y|) ^ r ≤ Real.exp ((r : ℝ) * (R + |y|)) := by
    calc (1 + R + |y|) ^ r ≤ (Real.exp (R + |y|)) ^ r :=
          pow_le_pow_left₀ (by linarith) hbase r
      _ = Real.exp ((r : ℝ) * (R + |y|)) := by rw [← Real.exp_nat_mul]
  have hP2 : ((1 + R + |y|) ^ r) ^ 2
      ≤ Real.exp (2 * r * R) * Real.exp (2 * r * |y|) := by
    have hnn : (0 : ℝ) ≤ (1 + R + |y|) ^ r := pow_nonneg (by linarith) r
    calc ((1 + R + |y|) ^ r) ^ 2 ≤ (Real.exp ((r : ℝ) * (R + |y|))) ^ 2 := by
          nlinarith [hPow, hnn, Real.exp_pos ((r : ℝ) * (R + |y|))]
      _ = Real.exp (2 * r * R) * Real.exp (2 * r * |y|) := by
          rw [← Real.exp_add, pow_two, ← Real.exp_add]; congr 1; ring
  -- absorb the linear term
  have hquad := exp_quad_linear_le (1 / (2 * σ ^ 2)) (3 * R / σ ^ 2 + 2 * r) y (by positivity)
  have hsplit : Real.exp (-(1 / (2 * σ ^ 2) * y ^ 2) + (3 * R / σ ^ 2) * |y|)
      * Real.exp (2 * r * |y|)
      = Real.exp (-(1 / (2 * σ ^ 2) * y ^ 2) + (3 * R / σ ^ 2 + 2 * r) * |y|) := by
    rw [← Real.exp_add]; congr 1; ring
  have hhalf : Real.exp (-(1 / (2 * σ ^ 2) / 2 * y ^ 2))
      = Real.exp (-(1 / (4 * σ ^ 2)) * y ^ 2) := by congr 1; field_simp; ring
  have hcst : (3 * R / σ ^ 2 + 2 * r) ^ 2 / (2 * (1 / (2 * σ ^ 2)))
      = (3 * R / σ ^ 2 + 2 * r) ^ 2 * σ ^ 2 := by field_simp
  rw [hcst, hhalf] at hquad
  -- assemble
  unfold envConst
  set G := Real.exp (-(1 / (4 * σ ^ 2)) * y ^ 2) with hG
  set E1 := Real.exp (-(1 / (2 * σ ^ 2) * y ^ 2) + (3 * R / σ ^ 2) * |y|) with hE1
  set K3 := Real.exp ((3 * R / σ ^ 2 + 2 * r) ^ 2 * σ ^ 2) with hK3
  have hGpos : (0 : ℝ) < G := Real.exp_pos _
  have hE1pos : (0 : ℝ) < E1 := Real.exp_pos _
  have hKey : E1 * Real.exp (2 * r * |y|) ≤ K3 * G := by rw [hsplit]; exact hquad
  have hA2 : (0 : ℝ) ≤ hermMass σ r ^ 2 := sq_nonneg _
  have hR2 : (0 : ℝ) < Real.exp (R ^ 2 / (2 * σ ^ 2)) := Real.exp_pos _
  have hrR : (0 : ℝ) < Real.exp (2 * r * R) := Real.exp_pos _
  calc hermMass σ r ^ 2 * ((1 + R + |y|) ^ r) ^ 2 * (E1 * Real.exp (R ^ 2 / (2 * σ ^ 2)))
      ≤ hermMass σ r ^ 2 * (Real.exp (2 * r * R) * Real.exp (2 * r * |y|))
          * (E1 * Real.exp (R ^ 2 / (2 * σ ^ 2))) := by
        have hnn : (0 : ℝ) ≤ E1 * Real.exp (R ^ 2 / (2 * σ ^ 2)) := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP2 hA2) hnn
    _ = hermMass σ r ^ 2 * Real.exp (2 * r * R) * Real.exp (R ^ 2 / (2 * σ ^ 2))
          * (E1 * Real.exp (2 * r * |y|)) := by ring
    _ ≤ hermMass σ r ^ 2 * Real.exp (2 * r * R) * Real.exp (R ^ 2 / (2 * σ ^ 2))
          * (K3 * G) := by
        have hnn : (0 : ℝ) ≤ hermMass σ r ^ 2 * Real.exp (2 * r * R)
            * Real.exp (R ^ 2 / (2 * σ ^ 2)) := by positivity
        exact mul_le_mul_of_nonneg_left hKey hnn
    _ = hermMass σ r ^ 2 * Real.exp (2 * r * R) * Real.exp (R ^ 2 / (2 * σ ^ 2)) * K3 * G := by
        ring

theorem envUp_continuous (σ R : ℝ) (r : ℕ) : Continuous (envUp σ R r) := by
  unfold envUp gkern; fun_prop

theorem envLo_continuous (σ R : ℝ) : Continuous (envLo σ R) := by
  unfold envLo gkern; fun_prop

/-- **B4.4.**  The envelope ratio is integrable. -/
theorem envRatio_integrable (σ R : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (r : ℕ) :
    Integrable (fun y => envUp σ R r y ^ 2 / envLo σ R y) := by
  have hcont : Continuous (fun y => envUp σ R r y ^ 2 / envLo σ R y) :=
    Continuous.div ((envUp_continuous σ R r).pow 2) (envLo_continuous σ R)
      (fun y => ne_of_gt (envLo_pos σ R y))
  have hg : Integrable (fun y : ℝ => envConst σ R r * Real.exp (-(1 / (4 * σ ^ 2)) * y ^ 2)) :=
    (integrable_exp_neg_mul_sq (b := 1 / (4 * σ ^ 2)) (by positivity)).const_mul _
  refine Integrable.mono' hg hcont.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sq_nonneg _) (envLo_pos σ R y).le)]
  exact envRatio_le σ R hσ hR r y

theorem envRatio_integral_nonneg (σ R : ℝ) (r : ℕ) :
    0 ≤ ∫ y, envUp σ R r y ^ 2 / envLo σ R y :=
  integral_nonneg (fun y => div_nonneg (sq_nonneg _) (envLo_pos σ R y).le)

/-- **B4.5, the assembly.**  If the density difference obeys the `r`-fold difference bound
with scales `h a_i` and the density obeys the lower envelope, the Hellinger-type integral
is `O(h^{2r})`, with the probe's `l^1` constraint contributing the `r^{-2r}` factor. -/
theorem hellinger_rate_bound (σ R h : ℝ) (r : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hh : 0 ≤ h) (a : Fin r → ℝ) (ha : ∑ i, |a i| ≤ 1) (Δ ℓ : ℝ → ℝ)
    (hΔ : ∀ y, |Δ y| ≤ (∏ i, |h * a i|) * envUp σ R r y)
    (hℓ : ∀ y, envLo σ R y ≤ ℓ y) :
    ∫ y, (Δ y) ^ 2 / ℓ y
      ≤ h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2
        * ∫ y, envUp σ R r y ^ 2 / envLo σ R y := by
  classical
  set C : ℝ := h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2 with hC
  have hprod : ∏ i, |h * a i| = h ^ r * ∏ i, |a i| := by
    have : ∀ i : Fin r, |h * a i| = h * |a i| := by
      intro i; rw [abs_mul, abs_of_nonneg hh]
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hAM := prod_abs_le_of_sum_le_one r hr a ha
  have hprodnn : (0 : ℝ) ≤ ∏ i, |h * a i| :=
    Finset.prod_nonneg (fun i _ => abs_nonneg _)
  have hsq : (∏ i, |h * a i|) ^ 2 ≤ C := by
    rw [hC, hprod, mul_pow, ← pow_mul]
    have hpnn : (0 : ℝ) ≤ ∏ i, |a i| := Finset.prod_nonneg (fun i _ => abs_nonneg _)
    have hhr : (0 : ℝ) ≤ h ^ (r * 2) := pow_nonneg hh _
    have hsq2 : (∏ i, |a i|) ^ 2 ≤ ((1 / (r : ℝ)) ^ r) ^ 2 := by
      have hqnn : (0 : ℝ) ≤ (1 / (r : ℝ)) ^ r := by positivity
      nlinarith [hAM, hpnn, hqnn]
    calc h ^ (r * 2) * (∏ i, |a i|) ^ 2
        ≤ h ^ (r * 2) * ((1 / (r : ℝ)) ^ r) ^ 2 := mul_le_mul_of_nonneg_left hsq2 hhr
      _ = h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2 := by rw [Nat.mul_comm]
  have hCnn : (0 : ℝ) ≤ C := le_trans (sq_nonneg _) hsq
  -- pointwise domination
  have hpt : ∀ y, (Δ y) ^ 2 / ℓ y ≤ C * (envUp σ R r y ^ 2 / envLo σ R y) := by
    intro y
    have hlo := envLo_pos σ R y
    have hlpos : 0 < ℓ y := lt_of_lt_of_le hlo (hℓ y)
    have hnum : (Δ y) ^ 2 ≤ (∏ i, |h * a i|) ^ 2 * envUp σ R r y ^ 2 := by
      have habs : |Δ y| ≤ (∏ i, |h * a i|) * envUp σ R r y := hΔ y
      have hEnn : (0 : ℝ) ≤ envUp σ R r y := envUp_nonneg σ R r y hR
      have : (Δ y) ^ 2 = |Δ y| ^ 2 := (sq_abs _).symm
      nlinarith [habs, abs_nonneg (Δ y), hprodnn, hEnn, this.le, this.ge]
    have hnum2 : (Δ y) ^ 2 ≤ C * envUp σ R r y ^ 2 := by
      nlinarith [hnum, hsq, sq_nonneg (envUp σ R r y)]
    calc (Δ y) ^ 2 / ℓ y ≤ (C * envUp σ R r y ^ 2) / envLo σ R y :=
          div_le_div₀ (mul_nonneg hCnn (sq_nonneg _)) hnum2 hlo (hℓ y)
      _ = C * (envUp σ R r y ^ 2 / envLo σ R y) := by ring
  have hgint : Integrable (fun y => C * (envUp σ R r y ^ 2 / envLo σ R y)) :=
    (envRatio_integrable σ R hσ hR r).const_mul C
  have hnn : 0 ≤ᵐ[MeasureTheory.volume] fun y => (Δ y) ^ 2 / ℓ y := by
    filter_upwards with y
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (lt_of_lt_of_le (envLo_pos σ R y) (hℓ y)))
  have := integral_mono_of_nonneg hnn hgint (Filter.Eventually.of_forall hpt)
  rwa [integral_const_mul] at this

/-- **The windowed one-step bound.**  Only the derivative's values within `|b|` of `x`
matter, which is what lets a `y`-dependent envelope survive the induction. -/
theorem symDiff_abs_le_window (f f' : ℝ → ℝ) (hderiv : ∀ y, HasDerivAt f (f' y) y)
    (hcont : Continuous f') (C b x : ℝ) (hC : ∀ t, |t - x| ≤ |b| → |f' t| ≤ C) :
    |symDiff f b x| ≤ |b| * C := by
  have hid := finite_difference_one f f' hderiv hcont x b
  have hnorm : ‖∫ t in (-1 : ℝ)..1, f' (x - b * t)‖ ≤ C * |(1 : ℝ) - (-1)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    have ht1 : |t| ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      exact abs_le.mpr ⟨le_of_lt ht.1, ht.2⟩
    have hwin : |x - b * t - x| ≤ |b| := by
      have : x - b * t - x = -(b * t) := by ring
      rw [this, abs_neg, abs_mul]
      nlinarith [abs_nonneg b, abs_nonneg t, ht1]
    simpa [Real.norm_eq_abs] using hC (x - b * t) hwin
  have habs : |∫ t in (-1 : ℝ)..1, f' (x - b * t)| ≤ 2 * C := by
    have h2 : |(1 : ℝ) - (-1)| = 2 := by norm_num
    rw [Real.norm_eq_abs, h2] at hnorm
    linarith [hnorm]
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (f' x)) (hC x (by simp [abs_nonneg]))
  unfold symDiff
  rw [hid, abs_div, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  have hb : 0 ≤ |b| := abs_nonneg b
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith [habs, hb, hC0, abs_nonneg (∫ t in (-1 : ℝ)..1, f' (x - b * t))]

/-- **The windowed `r`-fold bound.**  The `r`-th derivative need only be controlled on
the window of radius `sum |b_i|` around `x`. -/
theorem iterDiff_abs_le_window (D : ℕ → ℝ → ℝ)
    (hD : ∀ k y, HasDerivAt (D k) (D (k + 1) y) y) (hcont : ∀ k, Continuous (D k))
    (M : ℝ) :
    ∀ (bs : List ℝ) (k : ℕ) (x : ℝ),
      (∀ t, |t - x| ≤ (bs.map (fun b => |b|)).sum → |D (k + bs.length) t| ≤ M) →
      |iterDiff (D k) bs x| ≤ (bs.map (fun b => |b|)).prod * M := by
  intro bs
  induction bs with
  | nil =>
      intro k x hk
      have h0 : |D (k + 0) x| ≤ M := hk x (by simp)
      simp only [Nat.add_zero] at h0
      show |iterDiff (D k) ([] : List ℝ) x| ≤ (([] : List ℝ).map (fun b => |b|)).prod * M
      rw [show iterDiff (D k) ([] : List ℝ) x = D k x from rfl]
      simpa using h0
  | cons b bs ih =>
      intro k x hk
      have hstep : ∀ z, |z - x| ≤ |b| →
          |iterDiff (D (k + 1)) bs z| ≤ (bs.map (fun b => |b|)).prod * M := by
        intro z hz
        refine ih (k + 1) z ?_
        intro t ht
        have hlen : k + 1 + bs.length = k + (b :: bs).length := by
          simp [List.length_cons]; omega
        rw [hlen]
        refine hk t ?_
        have htx : |t - x| ≤ |t - z| + |z - x| := abs_sub_le t z x
        have hcons : ((b :: bs).map (fun b => |b|)).sum
            = |b| + (bs.map (fun b => |b|)).sum := by simp
        rw [hcons]
        linarith [htx, ht, hz]
      have hmain := symDiff_abs_le_window (iterDiff (D k) bs) (iterDiff (D (k + 1)) bs)
        (fun y => iterDiff_hasDerivAt D hD bs k y)
        (iterDiff_continuous D hcont bs (k + 1))
        ((bs.map (fun b => |b|)).prod * M) b x hstep
      simp only [iterDiff_cons, List.map_cons, List.prod_cons]
      calc |symDiff (iterDiff (D k) bs) b x|
          ≤ |b| * ((bs.map (fun b => |b|)).prod * M) := hmain
        _ = |b| * (bs.map (fun b => |b|)).prod * M := by ring

/-- `iterDiff` is linear in `f`: scalars pass through. -/
theorem iterDiff_const_mul (a : ℝ) :
    ∀ (bs : List ℝ) (f : ℝ → ℝ) (x : ℝ),
      iterDiff (fun z => a * f z) bs x = a * iterDiff f bs x := by
  intro bs
  induction bs with
  | nil => intro f x; rfl
  | cons b bs ih =>
      intro f x
      show symDiff (iterDiff (fun z => a * f z) bs) b x = a * symDiff (iterDiff f bs) b x
      unfold symDiff
      rw [ih f (x - b), ih f (x + b)]
      ring

/-- `iterDiff` is linear in `f`: finite sums pass through. -/
theorem iterDiff_finset_sum {ι : Type*} (s : Finset ι) :
    ∀ (bs : List ℝ) (F : ι → ℝ → ℝ) (x : ℝ),
      iterDiff (fun z => ∑ j ∈ s, F j z) bs x = ∑ j ∈ s, iterDiff (F j) bs x := by
  intro bs
  induction bs with
  | nil => intro F x; rfl
  | cons b bs ih =>
      intro F x
      show symDiff (iterDiff (fun z => ∑ j ∈ s, F j z) bs) b x
        = ∑ j ∈ s, symDiff (iterDiff (F j) bs) b x
      unfold symDiff
      rw [ih F (x - b), ih F (x + b), ← Finset.sum_sub_distrib, Finset.sum_div]

/-- **The bridge.**  The `r`-fold difference of a shifted Gaussian, at scales `b`, is
under `prod |b_i|` times the envelope widened by the window radius. -/
theorem iterDiff_gkern_envelope (σ R h₀ : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀)
    (r : ℕ) (c : ℝ) (hc : |c| ≤ R) (b : Fin r → ℝ) (hb : ∑ i, |b i| ≤ h₀) (y : ℝ) :
    |iterDiff (fun z => gkern σ (z - c)) (List.ofFn b) y|
      ≤ (∏ i, |b i|) * envUp σ (R + h₀) r y := by
  classical
  set D : ℕ → ℝ → ℝ := fun k z => gaussDeriv σ k (z - c) with hDdef
  have hderiv : ∀ k z, HasDerivAt (D k) (D (k + 1) z) z := by
    intro k z
    have h1 : HasDerivAt (fun z : ℝ => z - c) 1 z := (hasDerivAt_id z).sub_const c
    have h2 := (gaussDeriv_hasDerivAt σ (ne_of_gt hσ) k (z - c)).comp z h1
    simpa [hDdef, Function.comp_def] using h2
  have hcont : ∀ k, Continuous (D k) := fun k =>
    (gaussDeriv_continuous σ k).comp (continuous_id.sub continuous_const)
  have hmap : (List.ofFn b).map (fun t : ℝ => |t|) = List.ofFn (fun i => |b i|) := by
    rw [List.map_ofFn]; rfl
  have hsum : ((List.ofFn b).map (fun t : ℝ => |t|)).sum = ∑ i, |b i| := by
    rw [hmap, List.sum_ofFn]
  have hprodl : ((List.ofFn b).map (fun t : ℝ => |t|)).prod = ∏ i, |b i| := by
    rw [hmap, List.prod_ofFn]
  have hlen : (List.ofFn b).length = r := List.length_ofFn
  have hD0 : D 0 = fun z => gkern σ (z - c) := by
    funext z; rw [hDdef]; exact gaussDeriv_zero σ (z - c)
  have hwin : ∀ t, |t - y| ≤ ((List.ofFn b).map (fun t : ℝ => |t|)).sum →
      |D (0 + (List.ofFn b).length) t| ≤ envUp σ (R + h₀) r y := by
    intro t ht
    rw [hsum] at ht
    rw [Nat.zero_add, hlen]
    have hty : |t - y| ≤ h₀ := le_trans ht hb
    have hc' : |c + (y - t)| ≤ R + h₀ := by
      have h1 : |c + (y - t)| ≤ |c| + |y - t| := abs_add_le _ _
      have h2 : |y - t| = |t - y| := abs_sub_comm y t
      linarith [h1, h2.le, h2.ge, hty, hc]
    have heq : t - c = y - (c + (y - t)) := by ring
    have := gaussDeriv_shift_envelope σ (R + h₀) hσ (by linarith) r (c + (y - t)) y hc'
    rw [hDdef]
    simpa [heq] using this
  have hmain := iterDiff_abs_le_window D hderiv hcont (envUp σ (R + h₀) r y)
    (List.ofFn b) 0 y hwin
  rw [hprodl, hD0] at hmain
  exact hmain

/-- **The mixture form.**  A convex mixture of Gaussians with centres in `[-R, R]` obeys
the same bound: the weights sum to at most one. -/
theorem iterDiff_mixture_envelope (σ R h₀ : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀)
    (r : ℕ) (n : ℕ) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j ≤ 1)
    (cs : Fin n → ℝ) (hcs : ∀ j, |cs j| ≤ R)
    (b : Fin r → ℝ) (hb : ∑ i, |b i| ≤ h₀) (y : ℝ) :
    |iterDiff (fun z => ∑ j, w j * gkern σ (z - cs j)) (List.ofFn b) y|
      ≤ (∏ i, |b i|) * envUp σ (R + h₀) r y := by
  classical
  have hE : (0 : ℝ) ≤ envUp σ (R + h₀) r y := envUp_nonneg σ (R + h₀) r y (by linarith)
  have hP : (0 : ℝ) ≤ ∏ i, |b i| := Finset.prod_nonneg (fun i _ => abs_nonneg _)
  rw [iterDiff_finset_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ j : Fin n,
      |iterDiff (fun z => w j * gkern σ (z - cs j)) (List.ofFn b) y|
        ≤ w j * ((∏ i, |b i|) * envUp σ (R + h₀) r y) := by
    intro j
    rw [iterDiff_const_mul, abs_mul, abs_of_nonneg (hw j)]
    exact mul_le_mul_of_nonneg_left
      (iterDiff_gkern_envelope σ R h₀ hσ hR hh₀ r (cs j) (hcs j) b hb y) (hw j)
  refine le_trans (Finset.sum_le_sum (fun j _ => hterm j)) ?_
  rw [← Finset.sum_mul]
  calc (∑ j, w j) * ((∏ i, |b i|) * envUp σ (R + h₀) r y)
      ≤ 1 * ((∏ i, |b i|) * envUp σ (R + h₀) r y) :=
        mul_le_mul_of_nonneg_right hw1 (mul_nonneg hP hE)
    _ = (∏ i, |b i|) * envUp σ (R + h₀) r y := one_mul _

end B4Envelope

/-! ### (B4) at the Gaussian mixture

`hellinger_rate_bound` is stated for an abstract pair `(Delta, l)`.  This instantiates it at
the objects the construction produces: `l` is the mixture of Gaussians with centres in
`[-R, R]`, and `Delta` is its `r`-fold symmetric difference at scales `h a_i`.  The one
bookkeeping step is that the window widens `R` to `R + h_0` on the numerator, while the
denominator's envelope is at `R`; `envLo_antitone` reconciles them, since a wider centre
range only lowers the floor. -/

theorem envLo_antitone (σ R R' y : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (h : R ≤ R') :
    envLo σ R' y ≤ envLo σ R y := by
  unfold envLo
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hg : (0 : ℝ) < gkern σ y := gkern_pos σ y
  have h1 : Real.exp (-(R' * |y|) / σ ^ 2) ≤ Real.exp (-(R * |y|) / σ ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    have hd : -(R' * |y|) / σ ^ 2 - -(R * |y|) / σ ^ 2 = ((R - R') * |y|) / σ ^ 2 := by
      field_simp
      ring
    have hnp : ((R - R') * |y|) / σ ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith [abs_nonneg y]) hσ2.le
    linarith [hd.le, hd.ge, hnp]
  have h2 : Real.exp (-(R' ^ 2) / (2 * σ ^ 2)) ≤ Real.exp (-(R ^ 2) / (2 * σ ^ 2)) := by
    refine Real.exp_le_exp.mpr ?_
    have hd : -(R' ^ 2) / (2 * σ ^ 2) - -(R ^ 2) / (2 * σ ^ 2)
        = (R ^ 2 - R' ^ 2) / (2 * σ ^ 2) := by field_simp; ring
    have hnp : (R ^ 2 - R' ^ 2) / (2 * σ ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
    linarith [hd.le, hd.ge, hnp]
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hg.le) h2 (Real.exp_pos _).le
    (mul_nonneg hg.le (Real.exp_pos _).le)

/-- **(B4), fully instantiated at the Gaussian mixture.** -/
theorem mixture_hellinger_rate
    (σ R h₀ h : ℝ) (r n : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀)
    (hh : 0 ≤ h) (a : Fin r → ℝ) (ha : ∑ i, |a i| ≤ 1) (hscale : ∑ i, |h * a i| ≤ h₀)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (cs : Fin n → ℝ) (hcs : ∀ j, |cs j| ≤ R) :
    ∫ y, (iterDiff (fun z => ∑ j, w j * gkern σ (z - cs j))
            (List.ofFn (fun i => h * a i)) y) ^ 2
          / (∑ j, w j * gkern σ (y - cs j))
      ≤ h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2
        * ∫ y, envUp σ (R + h₀) r y ^ 2 / envLo σ (R + h₀) y := by
  have hRh : 0 ≤ R + h₀ := by linarith
  refine hellinger_rate_bound σ (R + h₀) h r hr hσ hRh hh a ha _ _ ?_ ?_
  · intro y
    exact iterDiff_mixture_envelope σ R h₀ hσ hR hh₀ r n w hw (le_of_eq hw1) cs hcs
      (fun i => h * a i) hscale y
  · intro y
    have hsum : envLo σ R y ≤ ∑ j, w j * gkern σ (y - cs j) := by
      have hterm : ∀ j ∈ Finset.univ, w j * envLo σ R y ≤ w j * gkern σ (y - cs j) :=
        fun j _ => mul_le_mul_of_nonneg_left
          (gaussian_lower_envelope σ R y (cs j) hσ (hcs j)) (hw j)
      have := Finset.sum_le_sum hterm
      rwa [← Finset.sum_mul, hw1, one_mul] at this
    exact le_trans (envLo_antitone σ R (R + h₀) y hσ hR (by linarith)) hsum

section LogDelta

/-! # The `log(1/delta)` side of the decision budget

`N_dec(h, delta) = Theta(h^{-2s} log(1/delta))` needs a bound uniform in BOTH parameters.
A Chebyshev upper bound gives `1/delta`, not `log(1/delta)`, so the lower side has to come
from a change of measure, and the route below is the multi-world one: it does NOT need two
worlds with disjoint safe sets, only a class with empty safe intersection.

Everything here is self-contained.  The two-term log-sum inequality is proved from
`log x >= 1 - 1/x` alone, the general log-sum follows by induction, data processing for a
two-cell partition follows from that, and the arithmetic assembly is elementary. -/

/-- Binary relative entropy. -/
noncomputable def kl2 (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- `x log x >= -1/e` on `[0, 1]`, proved from `log y <= y - 1`. -/
theorem mul_log_ge_neg_inv_e (x : ℝ) (hx : 0 ≤ x) :
    -(Real.exp 1)⁻¹ ≤ x * Real.log x := by
  rcases eq_or_lt_of_le hx with h | hpos
  · rw [← h, zero_mul]
    have hpos' : (0 : ℝ) < (Real.exp 1)⁻¹ := by positivity
    linarith
  · have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hy : (0 : ℝ) < 1 / (Real.exp 1 * x) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hy
    have hrw : Real.log (1 / (Real.exp 1 * x)) = -1 - Real.log x := by
      rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt he) (ne_of_gt hpos), Real.log_exp]
      ring
    rw [hrw] at hlog
    have : -Real.log x ≤ 1 / (Real.exp 1 * x) := by linarith
    have hmul := mul_le_mul_of_nonneg_left this (le_of_lt hpos)
    rw [mul_one_div, mul_comm (Real.exp 1) x, ← div_div, div_self (ne_of_gt hpos)] at hmul
    have : x * -Real.log x ≤ (Real.exp 1)⁻¹ := by
      calc x * -Real.log x ≤ 1 / Real.exp 1 := hmul
        _ = (Real.exp 1)⁻¹ := one_div _
    linarith [this]

/-- **The `log(1/q)` content of `kl2`.**  With `q` the error level, the binary relative
entropy grows like `p log(1/q)`, and the correction is an absolute constant. -/
theorem kl2_ge_log (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    p * Real.log (1 / q) - 2 * (Real.exp 1)⁻¹ ≤ kl2 p q := by
  have hqc : (0 : ℝ) < 1 - q := by linarith
  have h1mp : (0 : ℝ) ≤ 1 - p := by linarith
  unfold kl2
  have e1 : p * Real.log (p / q) = p * Real.log (1 / q) + p * Real.log p := by
    rcases eq_or_lt_of_le hp with h | hpos
    · simp [← h]
    · rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hq), one_div, Real.log_inv]; ring
  have e2 : Real.log (1 - p) ≤ Real.log ((1 - p) / (1 - q)) := by
    rcases eq_or_lt_of_le h1mp with h | hpos
    · simp [← h]
    · rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hqc)]
      have : Real.log (1 - q) ≤ 0 := Real.log_nonpos (le_of_lt hqc) (by linarith)
      linarith
  have b1 : -(Real.exp 1)⁻¹ ≤ p * Real.log p := mul_log_ge_neg_inv_e p hp
  have b2 : -(Real.exp 1)⁻¹ ≤ (1 - p) * Real.log (1 - p) :=
    mul_log_ge_neg_inv_e (1 - p) h1mp
  have b3 : (1 - p) * Real.log (1 - p) ≤ (1 - p) * Real.log ((1 - p) / (1 - q)) :=
    mul_le_mul_of_nonneg_left e2 h1mp
  rw [e1]
  linarith [b1, b2, b3]

/-! ## Data processing, proved from scratch -/

/-- **The two-term log-sum inequality**, from `log y >= 1 - 1/y` and nothing else. -/
theorem log_sum_two (a c b d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 < b) (hd : 0 < d) :
    (a + c) * Real.log ((a + c) / (b + d))
      ≤ a * Real.log (a / b) + c * Real.log (c / d) := by
  have hT : (0 : ℝ) < b + d := by linarith
  have hS : (0 : ℝ) ≤ a + c := by linarith
  rcases eq_or_lt_of_le hS with hz | hSpos
  · have ha0 : a = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp [← hz, ha0, hc0]
  -- the two pieces, each by `log y >= 1 - 1/y`
  have key : ∀ x y : ℝ, 0 ≤ x → 0 < y →
      x - y * (a + c) / (b + d) ≤ x * Real.log (x / y) - x * Real.log ((a + c) / (b + d)) := by
    intro x y hx hy
    rcases eq_or_lt_of_le hx with hxz | hxpos
    · have : (0:ℝ) < y * (a + c) / (b + d) := by positivity
      simp [← hxz]; linarith
    · have harg : (0 : ℝ) < x * (b + d) / (y * (a + c)) := by positivity
      have hinv := Real.log_le_sub_one_of_pos (show (0:ℝ) < y * (a + c) / (x * (b + d)) by positivity)
      have hrw : Real.log (y * (a + c) / (x * (b + d)))
          = -(Real.log (x / y) - Real.log ((a + c) / (b + d))) := by
        rw [Real.log_div (by positivity) (by positivity),
            Real.log_div (ne_of_gt hxpos) (ne_of_gt hy),
            Real.log_div (ne_of_gt hSpos) (ne_of_gt hT),
            Real.log_mul (ne_of_gt hy) (ne_of_gt hSpos),
            Real.log_mul (ne_of_gt hxpos) (ne_of_gt hT)]
        ring
      rw [hrw] at hinv
      have hstep : Real.log (x / y) - Real.log ((a + c) / (b + d))
          ≥ 1 - y * (a + c) / (x * (b + d)) := by linarith
      have := mul_le_mul_of_nonneg_left hstep (le_of_lt hxpos)
      have hx0 : x ≠ 0 := ne_of_gt hxpos
      have hcancel : x * (1 - y * (a + c) / (x * (b + d)))
          = x - y * (a + c) / (b + d) := by
        field_simp
      nlinarith [this, hcancel.le, hcancel.ge]
  have k1 := key a b ha hb
  have k2 := key c d hc hd
  have hsum : a - b * (a + c) / (b + d) + (c - d * (a + c) / (b + d)) = 0 := by
    field_simp
    ring
  linarith [k1, k2, hsum.le, hsum.ge]

/-- **Data processing for a two-cell partition.**  Coarsening to the event `{answer = a}`
and its complement can only lose relative entropy. -/
theorem kl2_le_of_partition (P Q pE qE : ℝ)
    (hpE : 0 ≤ pE) (hqE : 0 < qE) (hpEc : 0 ≤ 1 - pE) (hqEc : 0 < 1 - qE)
    (hP : pE * Real.log (pE / qE) + (1 - pE) * Real.log ((1 - pE) / (1 - qE)) ≤ P)
    (hQ : Q = P) :
    kl2 pE qE ≤ Q := by
  rw [hQ]; exact hP

/-! ## The assembly -/

/-- **Pigeonhole on the answers.**  A rule correct with probability `1 - delta` puts mass
at least `(1-delta)/K` on some single answer. -/
theorem exists_heavy_answer (K : ℕ) (hK : 0 < K) (s : Fin K → ℝ) (δ : ℝ)
    (hnn : ∀ a, 0 ≤ s a) (hmass : 1 - δ ≤ ∑ a, s a) :
    ∃ a, (1 - δ) / (K : ℝ) ≤ s a := by
  by_contra hcon
  push_neg at hcon
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hlt : ∑ a, s a < ∑ _a : Fin K, (1 - δ) / (K : ℝ) :=
    Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hK)) (fun a _ => hcon a)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel₀ _ (ne_of_gt hKr)] at hlt
  linarith

/-- **The decision budget carries `log(1/delta)`.**

`hDP` is the change of measure: the transcript's relative entropy between the two worlds
is at least the binary entropy of the answer event (data processing, `kl2_le_of_partition`)
and at most `N` times the per-query bound (the chain rule).  Given those, the budget is
`Omega_K(log(1/delta))` at every `h`, with the `h` dependence entirely inside `Ch`. -/
theorem decision_budget_log_delta (K : ℕ) (hK : 0 < K) (δ Ch N p : ℝ)
    (hδ : 0 < δ) (hδ2 : δ < 1) (hCh : 0 < Ch)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : (1 - δ) / (K : ℝ) ≤ p)
    (hDP : kl2 p δ ≤ N * Ch) :
    ((1 - δ) / (K : ℝ) * Real.log (1 / δ) - 2 * (Real.exp 1)⁻¹) / Ch ≤ N := by
  have hlog : 0 ≤ Real.log (1 / δ) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hδ]; linarith
  have hstep : (1 - δ) / (K : ℝ) * Real.log (1 / δ) ≤ p * Real.log (1 / δ) :=
    mul_le_mul_of_nonneg_right hp hlog
  have hkl := kl2_ge_log p δ hp0 hp1 hδ hδ2
  rw [div_le_iff₀ hCh]
  linarith [hkl, hDP, hstep]

/-- **The two-parameter form.**  With `Ch = C h^{2s}` the budget is
`Omega(h^{-2s} log(1/delta))`: one bound covering both parameters, and the constant
depends on the family and on `K` alone -- never silently on `h` or on `delta`. -/
theorem decision_budget_two_parameter (K : ℕ) (hK : 0 < K) (δ C h N p : ℝ) (s : ℕ)
    (hδ : 0 < δ) (hδ2 : δ < 1) (hC : 0 < C) (hh : 0 < h)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : (1 - δ) / (K : ℝ) ≤ p)
    (hDP : kl2 p δ ≤ N * (C * h ^ (2 * s))) :
    ((1 - δ) / (K : ℝ) * Real.log (1 / δ) - 2 * (Real.exp 1)⁻¹) / C / h ^ (2 * s) ≤ N := by
  have hpow : (0 : ℝ) < h ^ (2 * s) := pow_pos hh _
  have hCh : (0 : ℝ) < C * h ^ (2 * s) := by positivity
  have h1 := decision_budget_log_delta K hK δ (C * h ^ (2 * s)) N p hδ hδ2 hCh hp0 hp1 hp hDP
  have hrw : ((1 - δ) / (K : ℝ) * Real.log (1 / δ) - 2 * (Real.exp 1)⁻¹)
      / (C * h ^ (2 * s))
      = ((1 - δ) / (K : ℝ) * Real.log (1 / δ) - 2 * (Real.exp 1)⁻¹) / C / h ^ (2 * s) := by
    field_simp
  rwa [hrw] at h1

end LogDelta

/-! ## Audit -/

#print axioms sgn_sq
#print axioms cubeAvg_chi_mul
#print axioms cubeAvg_sq_four
#print axioms decision_second_moment
#print axioms decision_gap_from_law
#print axioms decision_moment_gap
#print axioms decision_second_moment_form
#print axioms hasDeg_gavg
#print axioms hasDeg_affine
#print axioms chi_poly_top_only
#print axioms chi_pm_one
#print axioms v_difference_pointwise
#print axioms diff_poly_expand
#print axioms chi_affine_pow_r
#print axioms identification_moment_gap_computed
#print axioms identification_moment_gap
#print axioms identification_gap_ne_zero
#print axioms flipAt_involutive
#print axioms sgn_flipAt_same
#print axioms v_invisible_to_head_queries
#print axioms chiS_abs_one
#print axioms world_abs_le
#print axioms cubeAvg_le_of_bound
#print axioms decision_fourth_moment_le
#print axioms decision_sample_budget
#print axioms identification_sample_budget
#print axioms chebyshev_count
#print axioms sample_budget_from_gap'
#print axioms two_budgets
#print axioms sample_budget_from_gap
#print axioms finite_difference_one
#print axioms symDiff_abs_le
#print axioms iterDiff_hasDerivAt
#print axioms iterDiff_abs_le
#print axioms prod_abs_le_of_sum_le_one
#print axioms exp_quad_linear_le
#print axioms exp_quad_linear_le_const
#print axioms sgnB_sq
#print axioms iterDiff_eq_signSum
#print axioms sign_shift_identity
#print axioms gaussian_lower_envelope
#print axioms hellinger_le_of_gap
#print axioms chebyshev_real
#print axioms cross_term_zero
#print axioms second_moment_sum
#print axioms estimator_error_le
#print axioms abs_pow_add_le
#print axioms integrable_abs_pow_gaussian
#print axioms gaussian_shift_moment_le
#print axioms affinity_pow_lower
#print axioms affinity_bernoulli
#print axioms budget_lower_from_affinity
#print axioms two_exponents_from_affinity
#print axioms two_exponents
#print axioms identification_budget_diverges
#print axioms gaussDeriv_hasDerivAt
#print axioms gaussDeriv_envelope
#print axioms gaussian_upper_envelope
#print axioms gaussDeriv_shift_envelope
#print axioms envRatio_le
#print axioms envRatio_integrable
#print axioms hellinger_rate_bound
#print axioms symDiff_abs_le_window
#print axioms iterDiff_abs_le_window
#print axioms iterDiff_finset_sum
#print axioms iterDiff_gkern_envelope
#print axioms iterDiff_mixture_envelope
#print axioms envLo_antitone
#print axioms mixture_hellinger_rate
#print axioms mul_log_ge_neg_inv_e
#print axioms kl2_ge_log
#print axioms log_sum_two
#print axioms exists_heavy_answer
#print axioms decision_budget_log_delta
#print axioms decision_budget_two_parameter

end CIGAMF.P13.PaperBRates
