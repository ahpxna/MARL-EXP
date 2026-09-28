import «LeanFunctionalExtremaCrossoverV1»

/-! # F-N7-Lower: a matching lower bound for the crossover family.

`LeanFunctionalExtremaCrossoverV1` proves `crossover_upper`: for EVERY allocation
there is a flipping alternative of energy at most
`kappa (1-rho)^2 / (32 kappa + n (1-rho)^2)`. That bounds the game information
from above and says nothing from below.

The lower bound does NOT need the symmetry-reduction theorem. The upper bound
already quantifies over every allocation; a lower bound only has to exhibit ONE
allocation and show every flipping alternative is expensive at it. That is what
this file does, so the `sup` over allocations is bounded below without any claim
that an optimal allocation is symmetric.

## What is proved

Write `d = 1 - rho` and `S = 4 + n d^2`.

* `energy_ge_pairV` — THE BRIDGE (the part that was prose). For an arbitrary
  flipping alternative — arbitrary incumbent means, arbitrary outsider means,
  extrema anywhere — there EXIST two distinct outsider cells `a ≠ b` with

      pairV (w I0) (w I1) (w a) (w b) (meanO a - meanO b)  ≤  energy.

  `pairV` is the exact two-quadratic pinch value
  `A B (1-D)^2/(A+B)` with `A` the incumbent's harmonic half and `B` the pair's.
  Nothing is assumed about which cells carry the extrema: the pair is produced
  from the alternative's own argmax and argmin.

* `explicit_pairV_ge` — at the explicit allocation
  `w I0 = w I1 = w e0 = w e1 = 1/S`, `w (middle) = d^2/S`,
  every pair value is at least `d^2/(8S)`. Three pair types, four sign cases.

* `explicit_allocation_lower` — combining the two: at that allocation every
  flipping alternative has energy at least `d^2/(8S)`.

* `crossover_sandwich` — with `crossover_upper`, for `0 < d ≤ 1` and `n ≥ 2`:
  the allocation is feasible, every flipping alternative costs at least
  `L = d^2/(8 S)` at it, and every allocation admits a flipping alternative
  costing at most `2 L`. So the explicit allocation is within a factor `2` of
  optimal for the whole family, uniformly in `n` and `d`.

* `kappa_small`, `upper_le_ratio_lower`, `crossover_sandwich_sharp` — on
  `(1+d)^2 ≤ 2` (i.e. `d ≤ sqrt 2 - 1`, `rho ≥ 2 - sqrt 2`) the factor sharpens
  from `2` to `(1+d)^2`:

      L  ≤  value  ≤  (1+d)^2 L,     L = d^2/(8(4 + n d^2)).

  `(1+d)^2 → 1` as `d → 0` UNIFORMLY IN `n`, because the excess is exactly
  `n d^2 (2d + d^2) / (4(1+d)^2 + n d^2) ≤ 2d + d^2`. So the single finite
  formula `d^2/(8(4 + n d^2))` governs all three regimes `n d^2 → 0`,
  `n d^2 → lambda`, `n d^2 → infinity` at once, without treating them separately.

## WHAT THIS DOES NOT ESTABLISH

- `Gamma_n` is not defined in this file. `explicit_allocation_lower` is a
  statement about one allocation and all alternatives; `crossover_upper` is a
  statement about all allocations and one alternative. Read together they
  sandwich the sup-inf, but the sup-inf itself is not formalised here, so
  `crossover_sandwich` is stated as the pair of inequalities it actually proves,
  not as a bound on a `Gamma`.
- The `n^(-1/2)` correction term is NOT proved. `crossover_sandwich_sharp`
  pinches the value to within `(1+d)^2`, which is enough for the leading order on
  any `d -> 0` sequence but says nothing about the next term.
- The sharp ratio is only proved on `(1+d)^2 ≤ 2`. Off that region only the
  factor `2` of `crossover_sandwich` is available, and the `kappa` branch is the
  other one.
- NO LIMIT IS TAKEN. The bounds are finite and hold for every `n` and `d`. The
  limit laws `n Gamma_n -> kappa` (fixed rho) and `n Gamma_n -> c^2/(8(c^2+4))`
  remain unproved; this file supplies the finite half that was missing, not the
  limits.
- Weights are assumed strictly positive. The degenerate faces are excluded, not
  handled.
- Nothing here concerns an algorithm, a stopping rule, or sample complexity.
  `energy` is an information quantity, not the cost of any procedure.
-/

namespace CIGAMF.P13.FunctionalCrossoverLower
open scoped BigOperators
open Finset
open CIGAMF.P13.FunctionalExtremaCrossover
noncomputable section
variable {n : ℕ}

/-! ## Two algebraic pinches -/

/-- Two-point displacement bound, cleared of denominators:
`min (w1 x^2 + w2 y^2)` subject to `x - y = c` is `w1 w2 c^2/(w1+w2)`. -/
theorem two_point (w1 w2 x y : ℝ) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) :
    w1*w2*(x-y)^2 ≤ (w1*x^2 + w2*y^2)*(w1+w2) := by
  nlinarith [sq_nonneg (w1*x + w2*y)]

/-- The pinch that splits one unit of displacement between two quadratics. -/
theorem pinch (A B u v : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A*B*(u+v)^2 ≤ (A*u^2 + B*v^2)*(A+B) := by
  nlinarith [sq_nonneg (A*u - B*v)]

/-- The exact value of the two-quadratic game for one outsider pair. -/
def pairV (wI0 wI1 wa wb D : ℝ) : ℝ :=
  wI0*wI1*(wa*wb)*(1-D)^2 / (2*(wI0*wI1*(wa+wb) + wa*wb*(wI0+wI1)))

/-- `pairV` in harmonic-half form. -/
theorem pairV_eq (wI0 wI1 wa wb D : ℝ) (h0 : 0 < wI0) (h1 : 0 < wI1)
    (ha : 0 < wa) (hb : 0 < wb) :
    pairV wI0 wI1 wa wb D
      = (wI0*wI1/(2*(wI0+wI1)))*(wa*wb/(2*(wa+wb)))*(1-D)^2
          / (wI0*wI1/(2*(wI0+wI1)) + wa*wb/(2*(wa+wb))) := by
  have hI : (0:ℝ) < wI0 + wI1 := by linarith
  have hab : (0:ℝ) < wa + wb := by linarith
  have hden : (0:ℝ) < wI0*wI1*(wa+wb) + wa*wb*(wI0+wI1) := by positivity
  unfold pairV
  field_simp

/-! ## The bridge: every flipping alternative is at least one pair value -/

/-- The incumbent half, in terms of its new range `lI1 - lI0`. -/
theorem incumbent_lower (wI0 wI1 lI0 lI1 : ℝ) (h0 : 0 ≤ wI0) (h1 : 0 ≤ wI1) :
    wI0*wI1*(1-(lI1-lI0))^2
      ≤ (wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2)*(wI0+wI1) := by
  have h := two_point wI0 wI1 (lI0+1/2) (lI1-1/2) h0 h1
  have he : (lI0+1/2)-(lI1-1/2) = 1-(lI1-lI0) := by ring
  rwa [he] at h

/-- The outsider half, for one pair of cells. -/
theorem outsider_lower (wO : Fin (n+2) → ℝ) (hw : ∀ c, 0 ≤ wO c) (rho : ℝ)
    (lO : Fin (n+2) → ℝ) (a b : Fin (n+2)) (hab : a ≠ b) :
    wO a*wO b*((lO a - lO b) - (meanO rho n a - meanO rho n b))^2
      ≤ (∑ c, wO c*(lO c - meanO rho n c)^2)*(wO a + wO b) := by
  classical
  have hpair : wO a*(lO a - meanO rho n a)^2 + wO b*(lO b - meanO rho n b)^2
      ≤ ∑ c, wO c*(lO c - meanO rho n c)^2 := by
    have hsub : ({a, b} : Finset (Fin (n+2))) ⊆ univ := subset_univ _
    have hnn : ∀ c ∈ univ, c ∉ ({a, b} : Finset (Fin (n+2))) →
        0 ≤ wO c*(lO c - meanO rho n c)^2 := by
      intro c _ _; exact mul_nonneg (hw c) (sq_nonneg _)
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    rwa [Finset.sum_pair hab] at this
  have h := two_point (wO a) (wO b) (lO a - meanO rho n a) (lO b - meanO rho n b)
    (hw a) (hw b)
  have he : (lO a - meanO rho n a) - (lO b - meanO rho n b)
      = (lO a - lO b) - (meanO rho n a - meanO rho n b) := by ring
  rw [he] at h
  refine h.trans (mul_le_mul_of_nonneg_right hpair ?_)
  have := hw a; have := hw b; linarith

/-- Outsider mean differences never reach `1`. -/
theorem meanO_diff_lt_one (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho < 1) (a b : Fin (n+2)) :
    meanO rho n a - meanO rho n b < 1 := by
  have hb : ∀ c : Fin (n+2), -(rho/2) ≤ meanO rho n c ∧ meanO rho n c ≤ rho/2 := by
    intro c
    unfold meanO
    by_cases hc0 : c.val = 0
    · rw [if_pos hc0]; constructor <;> linarith
    · rw [if_neg hc0]
      by_cases hc1 : c.val = 1
      · rw [if_pos hc1]; constructor <;> linarith
      · rw [if_neg hc1]; constructor <;> linarith
  have := (hb a).2
  have := (hb b).1
  linarith

/-- THE BRIDGE. Every flipping alternative — arbitrary means, extrema anywhere —
costs at least the pinch value of SOME pair of outsider cells. -/
theorem energy_ge_pairV (rho : ℝ) (h0 : 0 ≤ rho) (hlt : rho < 1)
    (wI0 wI1 : ℝ) (hI0 : 0 < wI0) (hI1 : 0 < wI1)
    (wO : Fin (n+2) → ℝ) (hw : ∀ c, 0 < wO c)
    (lI0 lI1 : ℝ) (lO : Fin (n+2) → ℝ) (hflip : Flips lI0 lI1 lO) :
    ∃ a b : Fin (n+2), a ≠ b ∧
      pairV wI0 wI1 (wO a) (wO b) (meanO rho n a - meanO rho n b)
        ≤ energy wI0 wI1 wO rho lI0 lI1 lO := by
  classical
  have hwn : ∀ c, 0 ≤ wO c := fun c => (hw c).le
  -- the alternative's own argmax and argmin
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (univ_nonempty) lO
  obtain ⟨b0, -, hb0⟩ := Finset.exists_mem_eq_inf' (univ_nonempty) lO
  -- make the two indices distinct without changing `lO a - lO b`
  have hz : rangeO lO = lO a - lO b0 := by unfold rangeO; rw [← ha, ← hb0]
  obtain ⟨b, hab, hgap⟩ : ∃ b : Fin (n+2), a ≠ b ∧ lO a - lO b = rangeO lO := by
    by_cases h : a = b0
    · -- the range is zero, so every cell carries the same value and any other
      -- index does just as well
      have hzero : rangeO lO = 0 := by rw [hz, ← h]; ring
      have hcon : ∀ c, lO c = lO a := by
        intro c
        have h1 := sub_le_rangeO lO c a
        have h2 := sub_le_rangeO lO a c
        rw [hzero] at h1 h2
        linarith
      refine ⟨if a = e0 n then e1 n else e0 n, ?_, ?_⟩
      · by_cases h0' : a = e0 n
        · rw [if_pos h0']; rw [h0']; exact e0_ne_e1
        · rw [if_neg h0']; exact h0'
      · rw [hcon (if a = e0 n then e1 n else e0 n), hzero]; ring
    · exact ⟨b0, h, hz.symm⟩
  refine ⟨a, b, hab, ?_⟩
  set z : ℝ := rangeO lO with hzdef
  set D : ℝ := meanO rho n a - meanO rho n b with hD
  set A : ℝ := wI0*wI1/(2*(wI0+wI1)) with hA
  set B : ℝ := wO a*wO b/(2*(wO a + wO b)) with hB
  have hIsum : (0:ℝ) < wI0 + wI1 := by linarith
  have hOsum : (0:ℝ) < wO a + wO b := by have := hw a; have := hw b; linarith
  have hApos : 0 < A := by
    rw [hA]; exact div_pos (mul_pos hI0 hI1) (by linarith)
  have hBpos : 0 < B := by
    rw [hB]; exact div_pos (mul_pos (hw a) (hw b)) (by linarith)
  have hDlt : D < 1 := by rw [hD]; exact meanO_diff_lt_one rho h0 hlt a b
  -- the two halves of the energy
  set SI : ℝ := wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2 with hSI
  set SO : ℝ := ∑ c, wO c*(lO c - meanO rho n c)^2 with hSO
  have hE : energy wI0 wI1 wO rho lI0 lI1 lO = SI/2 + SO/2 := by
    unfold energy; rw [hSI, hSO]
  have hIlow : A*(1-(lI1-lI0))^2 ≤ SI/2 := by
    have h := incumbent_lower wI0 wI1 lI0 lI1 hI0.le hI1.le
    rw [hA, hSI, div_mul_eq_mul_div,
      div_le_iff₀ (by linarith : (0:ℝ) < 2*(wI0+wI1))]
    have hring : (wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2)/2 * (2*(wI0+wI1))
        = (wI0*(lI0+1/2)^2 + wI1*(lI1-1/2)^2)*(wI0+wI1) := by ring
    rw [hring]
    exact h
  have hOlow : B*(z-D)^2 ≤ SO/2 := by
    have h := outsider_lower wO hwn rho lO a b hab
    rw [hgap] at h
    rw [hB, hSO, hzdef, hD, div_mul_eq_mul_div,
      div_le_iff₀ (by linarith : (0:ℝ) < 2*(wO a + wO b))]
    have hring : (∑ c, wO c*(lO c - meanO rho n c)^2)/2 * (2*(wO a + wO b))
        = (∑ c, wO c*(lO c - meanO rho n c)^2)*(wO a + wO b) := by ring
    rw [hring]
    exact h
  have hSOnn : 0 ≤ SO := by
    rw [hSO]; exact Finset.sum_nonneg (fun c _ => mul_nonneg (hwn c) (sq_nonneg _))
  have hSInn : 0 ≤ SI := by
    rw [hSI]
    have h1 : 0 ≤ wI0*(lI0+1/2)^2 := mul_nonneg hI0.le (sq_nonneg _)
    have h2 : 0 ≤ wI1*(lI1-1/2)^2 := mul_nonneg hI1.le (sq_nonneg _)
    linarith
  have hABpos : (0:ℝ) < A + B := by linarith
  -- the pinch value
  have hpv : pairV wI0 wI1 (wO a) (wO b) D = A*B*(1-D)^2/(A+B) := by
    rw [hA, hB]; exact pairV_eq wI0 wI1 (wO a) (wO b) D hI0 hI1 (hw a) (hw b)
  rw [hpv, hE, div_le_iff₀ hABpos]
  by_cases hz1 : z < 1
  · -- the incumbent still has to close a gap of at least `1 - z`
    have ht : lI1 - lI0 ≤ z := by
      have hf := hflip
      unfold Flips at hf
      rw [← hzdef] at hf
      exact (le_abs_self _).trans hf
    have hstep : A*(1-z)^2 ≤ A*(1-(lI1-lI0))^2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1-z) (by linarith) 2) hApos.le
    have hsum : A*(1-z)^2 + B*(z-D)^2 ≤ SI/2 + SO/2 := by linarith
    have hp := pinch A B (1-z) (z-D) hApos.le hBpos.le
    have heq : (1-z) + (z-D) = 1 - D := by ring
    rw [heq] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right hsum hABpos.le)
  · -- the outsider alone already pays the whole pinch value
    push_neg at hz1
    have hDpos : 0 < 1 - D := by linarith
    have hsq : (1-D)^2 ≤ (z-D)^2 :=
      pow_le_pow_left₀ hDpos.le (by linarith : 1 - D ≤ z - D) 2
    have hBD : B*(1-D)^2 ≤ SO/2 :=
      (mul_le_mul_of_nonneg_left hsq hBpos.le).trans hOlow
    have h1 : A*(B*(1-D)^2) ≤ A*(SO/2) := mul_le_mul_of_nonneg_left hBD hApos.le
    have h2 : A*(SO/2) ≤ (SI/2 + SO/2)*(A+B) := by
      have e1 : 0 ≤ SI*(A+B) := mul_nonneg hSInn hABpos.le
      have e2 : 0 ≤ SO*B := mul_nonneg hSOnn hBpos.le
      nlinarith [e1, e2]
    calc A*B*(1-D)^2 = A*(B*(1-D)^2) := by ring
      _ ≤ A*(SO/2) := h1
      _ ≤ (SI/2 + SO/2)*(A+B) := h2

/-! ## F2: the explicit allocation, and the sandwich -/

/-- `S = 4 + n d^2`, the normaliser of the explicit allocation. -/
def Snorm (n : ℕ) (d : ℝ) : ℝ := 4 + n*d^2

theorem Snorm_pos (n : ℕ) (d : ℝ) : 0 < Snorm n d := by
  unfold Snorm; positivity

/-- The explicit allocation on the outsider: `1/S` on each endpoint, `d^2/S` on
each middle cell. Each incumbent cell also carries `1/S`, so the total mass is
`2/S + 2/S + n d^2/S = 1`. -/
def wExp (n : ℕ) (d : ℝ) (a : Fin (n+2)) : ℝ :=
  if a.val ≤ 1 then 1/Snorm n d else d^2/Snorm n d

theorem wExp_endpoint {n : ℕ} (d : ℝ) {a : Fin (n+2)} (h : a.val ≤ 1) :
    wExp n d a = 1/Snorm n d := by unfold wExp; rw [if_pos h]

theorem wExp_middle {n : ℕ} (d : ℝ) {a : Fin (n+2)} (h : ¬ a.val ≤ 1) :
    wExp n d a = d^2/Snorm n d := by unfold wExp; rw [if_neg h]

theorem wExp_pos (n : ℕ) (d : ℝ) (hd : 0 < d) (a : Fin (n+2)) : 0 < wExp n d a := by
  have hS := Snorm_pos n d
  by_cases h : a.val ≤ 1
  · rw [wExp_endpoint d h]; exact div_pos one_pos hS
  · rw [wExp_middle d h]; exact div_pos (pow_pos hd 2) hS

/-- The allocation is a probability vector: `2/S` on the incumbent plus the
outsider's mass is exactly `1`. -/
theorem wExp_total (n : ℕ) (d : ℝ) :
    2/Snorm n d + ∑ a : Fin (n+2), wExp n d a = 1 := by
  classical
  have hS := Snorm_pos n d
  have hmid : ∀ i : Fin n, wExp n d i.succ.succ = d^2/Snorm n d := by
    intro i
    exact wExp_middle d (by simp)
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
    Finset.sum_congr rfl (fun i _ => hmid i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [wExp_endpoint d (by simp : ((0 : Fin (n+2))).val ≤ 1),
    wExp_endpoint d (by simp [Fin.val_succ] : ((0 : Fin (n+1)).succ).val ≤ 1)]
  unfold Snorm
  field_simp
  try ring

/-- Same-denominator division is monotone. Proved from `div_le_iff₀` alone so it
does not depend on which `div_le_div_*` spelling this Mathlib ships. -/
theorem div_le_div_same {A B C : ℝ} (hC : 0 < C) (h : A ≤ B) : A/C ≤ B/C := by
  rw [div_le_iff₀ hC, div_mul_eq_mul_div, mul_div_assoc, div_self (ne_of_gt hC), mul_one]
  exact h

/-- `pairV` at unit incumbent weights `1/s`, denominators cleared. -/
theorem pairV_unit (s wa wb D : ℝ) (hs : 0 < s) (hwa : 0 < wa) (hwb : 0 < wb) :
    pairV (1/s) (1/s) wa wb D
      = (wa*wb)*(1-D)^2/(2*((wa+wb) + 2*s*(wa*wb))) := by
  unfold pairV
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

/-- Reduce a lower bound on `pairV` to a polynomial inequality. -/
theorem pairV_unit_ge (s wa wb D L : ℝ) (hs : 0 < s) (hwa : 0 < wa) (hwb : 0 < wb)
    (h : L*(2*((wa+wb) + 2*s*(wa*wb))) ≤ (wa*wb)*(1-D)^2) :
    L ≤ pairV (1/s) (1/s) wa wb D := by
  rw [pairV_unit s wa wb D hs hwa hwb, le_div_iff₀ (by positivity)]
  exact h

/-- At the explicit allocation EVERY pair value is at least `d^2/(8 S)`.
Three pair types and four sign cases; only `0 < d ≤ 1` is used. -/
theorem explicit_pairV_ge (n : ℕ) (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (a b : Fin (n+2)) (hab : a ≠ b) :
    d^2/(8*Snorm n d)
      ≤ pairV (1/Snorm n d) (1/Snorm n d) (wExp n d a) (wExp n d b)
          (meanO (1-d) n a - meanO (1-d) n b) := by
  have hS := Snorm_pos n d
  have hS2 : (0:ℝ) < (Snorm n d)^2 := by positivity
  have hd2 : (0:ℝ) < d^2 := pow_pos hd0 2
  have hval : ∀ c : Fin (n+2),
      (c.val = 0 → meanO (1-d) n c = (1-d)/2) ∧
      (c.val = 1 → meanO (1-d) n c = -((1-d)/2)) ∧
      (2 ≤ c.val → meanO (1-d) n c = 0) := by
    intro c
    refine ⟨fun h => by unfold meanO; rw [if_pos h], fun h => ?_, fun h => ?_⟩
    · unfold meanO; rw [if_neg (by omega), if_pos h]; ring
    · unfold meanO; rw [if_neg (by omega), if_neg (by omega)]
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  by_cases ha : a.val ≤ 1 <;> by_cases hb : b.val ≤ 1
  · -- endpoint / endpoint : D = ±(1-d), and (1-D)^2 ≥ d^2
    have key : d^2 ≤ (1 - (meanO (1-d) n a - meanO (1-d) n b))^2 := by
      rcases Nat.lt_or_ge a.val 1 with h0 | h0
      · rw [(hval a).1 (by omega), (hval b).2.1 (by omega)]
        have he : (1 - ((1-d)/2 - -((1-d)/2))) = d := by ring
        rw [he]
      · rw [(hval a).2.1 (by omega), (hval b).1 (by omega)]
        have he : (1 - (-((1-d)/2) - (1-d)/2)) = 2 - d := by ring
        rw [he]; nlinarith
    rw [wExp_endpoint d ha, wExp_endpoint d hb]
    refine pairV_unit_ge _ _ _ _ _ hS (by positivity) (by positivity) ?_
    have hl : d^2/(8*Snorm n d)
        * (2*((1/Snorm n d + 1/Snorm n d) + 2*Snorm n d*((1/Snorm n d)*(1/Snorm n d))))
        = d^2/(Snorm n d)^2 := by field_simp; try ring
    have hr : (1/Snorm n d)*(1/Snorm n d)*(1 - (meanO (1-d) n a - meanO (1-d) n b))^2
        = (1 - (meanO (1-d) n a - meanO (1-d) n b))^2/(Snorm n d)^2 := by
      field_simp
    rw [hl, hr]
    exact div_le_div_same hS2 key
  · -- endpoint / middle
    have key : (1+3*d^2)/4 ≤ (1 - (meanO (1-d) n a - meanO (1-d) n b))^2 := by
      rw [(hval b).2.2 (by omega), sub_zero]
      rcases Nat.lt_or_ge a.val 1 with h0 | h0
      · rw [(hval a).1 (by omega)]
        have he : (1 - (1-d)/2) = (1+d)/2 := by ring
        rw [he]; nlinarith
      · rw [(hval a).2.1 (by omega)]
        have he : (1 - -((1-d)/2)) = (3-d)/2 := by ring
        rw [he]; nlinarith
    rw [wExp_endpoint d ha, wExp_middle d hb]
    refine pairV_unit_ge _ _ _ _ _ hS (by positivity) (by positivity) ?_
    have hl : d^2/(8*Snorm n d)
        * (2*((1/Snorm n d + d^2/Snorm n d)
            + 2*Snorm n d*((1/Snorm n d)*(d^2/Snorm n d))))
        = (d^2*(1+3*d^2))/(4*(Snorm n d)^2) := by field_simp; try ring
    have hr : (1/Snorm n d)*(d^2/Snorm n d)*(1 - (meanO (1-d) n a - meanO (1-d) n b))^2
        = (4*(d^2*(1 - (meanO (1-d) n a - meanO (1-d) n b))^2))/(4*(Snorm n d)^2) := by
      field_simp
      try ring
    rw [hl, hr]
    refine div_le_div_same (by positivity) ?_
    nlinarith [mul_le_mul_of_nonneg_left key hd2.le]
  · -- middle / endpoint
    have key : (1+3*d^2)/4 ≤ (1 - (meanO (1-d) n a - meanO (1-d) n b))^2 := by
      rw [(hval a).2.2 (by omega), zero_sub]
      rcases Nat.lt_or_ge b.val 1 with h0 | h0
      · rw [(hval b).1 (by omega)]
        have he : (1 - -((1-d)/2)) = (3-d)/2 := by ring
        rw [he]; nlinarith
      · rw [(hval b).2.1 (by omega)]
        have he : (1 - - -((1-d)/2)) = (1+d)/2 := by ring
        rw [he]; nlinarith
    rw [wExp_middle d ha, wExp_endpoint d hb]
    refine pairV_unit_ge _ _ _ _ _ hS (by positivity) (by positivity) ?_
    have hl : d^2/(8*Snorm n d)
        * (2*((d^2/Snorm n d + 1/Snorm n d)
            + 2*Snorm n d*((d^2/Snorm n d)*(1/Snorm n d))))
        = (d^2*(1+3*d^2))/(4*(Snorm n d)^2) := by field_simp; try ring
    have hr : (d^2/Snorm n d)*(1/Snorm n d)*(1 - (meanO (1-d) n a - meanO (1-d) n b))^2
        = (4*(d^2*(1 - (meanO (1-d) n a - meanO (1-d) n b))^2))/(4*(Snorm n d)^2) := by
      field_simp
      try ring
    rw [hl, hr]
    refine div_le_div_same (by positivity) ?_
    nlinarith [mul_le_mul_of_nonneg_left key hd2.le]
  · -- middle / middle : D = 0
    rw [wExp_middle d ha, wExp_middle d hb, (hval a).2.2 (by omega),
      (hval b).2.2 (by omega)]
    refine pairV_unit_ge _ _ _ _ _ hS (by positivity) (by positivity) ?_
    have hl : d^2/(8*Snorm n d)
        * (2*((d^2/Snorm n d + d^2/Snorm n d)
            + 2*Snorm n d*((d^2/Snorm n d)*(d^2/Snorm n d))))
        = (d^4 + d^6)/(2*(Snorm n d)^2) := by field_simp; try ring
    have hr : (d^2/Snorm n d)*(d^2/Snorm n d)*(1 - ((0:ℝ) - 0))^2
        = (2*d^4)/(2*(Snorm n d)^2) := by field_simp; try ring
    rw [hl, hr]
    refine div_le_div_same (by positivity) ?_
    have h1 : d^2 ≤ 1 := by nlinarith
    have h2 : (0:ℝ) ≤ d^4 := by positivity
    nlinarith [h1, h2]

/-- F2. At the explicit allocation every flipping alternative costs at least
`d^2/(8 S)`, `S = 4 + n d^2`. Combined with `crossover_upper`, which holds for
every allocation, this brackets the game value with NO symmetry assumption. -/
theorem explicit_allocation_lower (n : ℕ) (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (lI0 lI1 : ℝ) (lO : Fin (n+2) → ℝ) (hflip : Flips lI0 lI1 lO) :
    d^2/(8*Snorm n d)
      ≤ energy (1/Snorm n d) (1/Snorm n d) (wExp n d) (1-d) lI0 lI1 lO := by
  have hS := Snorm_pos n d
  obtain ⟨a, b, hab, hle⟩ :=
    energy_ge_pairV (1-d) (by linarith) (by linarith) (1/Snorm n d) (1/Snorm n d)
      (by positivity) (by positivity) (wExp n d) (wExp_pos n d hd0) lI0 lI1 lO hflip
  exact (explicit_pairV_ge n d hd0 hd1 a b hab).trans hle

/-! ## The sandwich -/

/-- The three-witness upper bound is at most twice the explicit lower bound.
Only `kappa ≤ 1/4` is used, which holds by definition. -/
theorem upper_le_two_lower (n : ℕ) (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    kappa (1-d)*d^2/(32*kappa (1-d) + n*d^2) ≤ 2*(d^2/(8*Snorm n d)) := by
  have hS := Snorm_pos n d
  have hk : kappa (1-d) ≤ 1/4 := min_le_left _ _
  have hkpos : 0 < kappa (1-d) :=
    kappa_pos (1-d) (by linarith) (by linarith)
  have hd2 : (0:ℝ) < d^2 := pow_pos hd0 2
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hden : (0:ℝ) < 32*kappa (1-d) + n*d^2 := by positivity
  have hS' : Snorm n d = 4 + n*d^2 := rfl
  rw [div_le_iff₀ hden, hS']
  have hE : 2*(d^2/(8*(4 + (n:ℝ)*d^2)))*(32*kappa (1-d) + n*d^2)
      = d^2*(32*kappa (1-d) + n*d^2)/(4*(4 + (n:ℝ)*d^2)) := by
    field_simp; ring
  rw [hE, le_div_iff₀ (by positivity : (0:ℝ) < 4*(4 + (n:ℝ)*d^2))]
  -- reduces to  n d^4 (4 kappa - 1) ≤ 16 kappa d^2, and `4 kappa ≤ 1`
  have hslack : (0:ℝ) ≤ (n:ℝ)*d^4*(1 - 4*kappa (1-d)) := by
    apply mul_nonneg (mul_nonneg hn (by positivity))
    linarith
  nlinarith [hslack, hkpos.le, hd2.le]

/-- THE SANDWICH. For `0 < d ≤ 1` and `n ≥ 2`, writing `L = d^2/(8(4+n d^2))`:
the explicit allocation `wExp` is feasible and forces EVERY flipping alternative
to cost at least `L`, while EVERY allocation admits a flipping alternative of
cost at most `2 L`. So the sup-inf is pinned between `L` and `2 L`, and `wExp` is
within a factor `2` of optimal — uniformly in `n` and `d`, with no symmetry
assumption anywhere. -/
theorem crossover_sandwich (n : ℕ) (hn : 2 ≤ n) (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1) :
    -- the explicit allocation is a probability vector
    (1/Snorm n d + 1/Snorm n d + ∑ a : Fin (n+2), wExp n d a = 1)
    ∧ -- and no flipping alternative is cheaper than L at it
    (∀ lI0 lI1 : ℝ, ∀ lO : Fin (n+2) → ℝ, Flips lI0 lI1 lO →
        d^2/(8*Snorm n d)
          ≤ energy (1/Snorm n d) (1/Snorm n d) (wExp n d) (1-d) lI0 lI1 lO)
    ∧ -- while every allocation admits one of cost at most 2 L
    (∀ wI0 wI1 : ℝ, ∀ wO : Fin (n+2) → ℝ, wI0 + wI1 + ∑ a, wO a = 1 →
        ∃ lI0 lI1 lO, Flips lI0 lI1 lO ∧
          energy wI0 wI1 wO (1-d) lI0 lI1 lO ≤ 2*(d^2/(8*Snorm n d))) := by
  have hS := Snorm_pos n d
  refine ⟨?_, ?_, ?_⟩
  · rw [show (1:ℝ)/Snorm n d + 1/Snorm n d = 2/Snorm n d from by ring]
    exact wExp_total n d
  · exact fun lI0 lI1 lO hflip => explicit_allocation_lower n d hd0 hd1 lI0 lI1 lO hflip
  · intro wI0 wI1 wO hw
    obtain ⟨lI0, lI1, lO, hflip, hle⟩ :=
      crossover_upper (1-d) (by linarith) (by linarith) hn wI0 wI1 wO hw
    rw [show (1:ℝ)-(1-d) = d from by ring] at hle
    exact ⟨lI0, lI1, lO, hflip, hle.trans (upper_le_two_lower n d hd0 hd1)⟩

/-- On `(1+d)^2 ≤ 2` — i.e. `d ≤ sqrt 2 - 1`, equivalently `rho ≥ 2 - sqrt 2` —
the `kappa` of the upper bound takes its second branch exactly. -/
theorem kappa_small (d : ℝ) (hd0 : 0 ≤ d) (h2 : (1+d)^2 ≤ 2) :
    kappa (1-d) = (1+d)^2/8 := by
  unfold kappa
  have he : (1 - (1-d)/2)^2/2 = (1+d)^2/8 := by ring
  rw [he, min_eq_right (by linarith)]

/-- THE SHARP RATIO. On that region the three-witness upper bound is at most
`(1+d)^2` times the explicit lower bound — a factor that tends to `1` as `d → 0`
UNIFORMLY IN `n`. So on any sequence `d_n → 0` the two bounds pinch, and the
game value is `d^2/(8(4 + n d^2))` to within `(1+d)^2`. That is the uniform
statement across the three regimes `n d^2 → 0`, `n d^2 → lambda`, `n d^2 → ∞`:
the same finite formula governs all of them. -/
theorem upper_le_ratio_lower (n : ℕ) (d : ℝ) (hd0 : 0 < d) (h2 : (1+d)^2 ≤ 2) :
    kappa (1-d)*d^2/(32*kappa (1-d) + n*d^2) ≤ (1+d)^2*(d^2/(8*Snorm n d)) := by
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hd2 : (0:ℝ) < d^2 := pow_pos hd0 2
  have hq : (0:ℝ) < (1+d)^2 := by positivity
  rw [kappa_small d hd0.le h2]
  have hS' : Snorm n d = 4 + n*d^2 := rfl
  have hden : (0:ℝ) < 32*((1+d)^2/8) + n*d^2 := by positivity
  rw [div_le_iff₀ hden, hS']
  have hE : (1+d)^2*(d^2/(8*(4 + (n:ℝ)*d^2)))*(32*((1+d)^2/8) + (n:ℝ)*d^2)
      = (1+d)^2*d^2*(4*(1+d)^2 + (n:ℝ)*d^2)/(8*(4 + (n:ℝ)*d^2)) := by
    field_simp; ring
  rw [hE, le_div_iff₀ (by positivity : (0:ℝ) < 8*(4 + (n:ℝ)*d^2))]
  have hslack : (0:ℝ) ≤ 4*((1+d)^2*d^2)*(2*d + d^2) := by positivity
  nlinarith [hslack]

/-- The sharp sandwich on `(1+d)^2 ≤ 2`: `L ≤ value ≤ (1+d)^2 L`. -/
theorem crossover_sandwich_sharp (n : ℕ) (hn : 2 ≤ n) (d : ℝ)
    (hd0 : 0 < d) (h2 : (1+d)^2 ≤ 2) :
    (∀ lI0 lI1 : ℝ, ∀ lO : Fin (n+2) → ℝ, Flips lI0 lI1 lO →
        d^2/(8*Snorm n d)
          ≤ energy (1/Snorm n d) (1/Snorm n d) (wExp n d) (1-d) lI0 lI1 lO)
    ∧ (∀ wI0 wI1 : ℝ, ∀ wO : Fin (n+2) → ℝ, wI0 + wI1 + ∑ a, wO a = 1 →
        ∃ lI0 lI1 lO, Flips lI0 lI1 lO ∧
          energy wI0 wI1 wO (1-d) lI0 lI1 lO ≤ (1+d)^2*(d^2/(8*Snorm n d))) := by
  have hd1 : d ≤ 1 := by nlinarith
  refine ⟨fun lI0 lI1 lO hflip => explicit_allocation_lower n d hd0 hd1 lI0 lI1 lO hflip, ?_⟩
  intro wI0 wI1 wO hw
  obtain ⟨lI0, lI1, lO, hflip, hle⟩ :=
    crossover_upper (1-d) (by linarith) (by linarith) hn wI0 wI1 wO hw
  rw [show (1:ℝ)-(1-d) = d from by ring] at hle
  exact ⟨lI0, lI1, lO, hflip, hle.trans (upper_le_ratio_lower n d hd0 h2)⟩

#print axioms kappa_small
#print axioms upper_le_ratio_lower
#print axioms crossover_sandwich_sharp

#print axioms upper_le_two_lower
#print axioms crossover_sandwich

#print axioms Snorm_pos
#print axioms wExp_pos
#print axioms wExp_total
#print axioms pairV_unit
#print axioms pairV_unit_ge
#print axioms explicit_pairV_ge
#print axioms explicit_allocation_lower

#print axioms two_point
#print axioms pinch
#print axioms pairV_eq
#print axioms incumbent_lower
#print axioms outsider_lower
#print axioms meanO_diff_lt_one
#print axioms energy_ge_pairV

end
end CIGAMF.P13.FunctionalCrossoverLower
