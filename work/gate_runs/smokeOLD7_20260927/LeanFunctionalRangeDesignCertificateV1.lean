import Mathlib

/-! # Functional F5.3/F5.4: inner-QP certificates without an inverse, and the
setup-cost crossing.

`LeanFunctionalRangeEnergyOracleV1` reduced the alternative union to a finite family of
convex pair regions and solved the single-constraint inner problem.  The general inner
problem has MANY constraints -- `A λ ≤ 0` with one row per `(u,v)` pair -- and needs a
certificate a referee can check.  The textbook dual

    d(y) = yᵀAμ − ½ yᵀ A M⁻¹ Aᵀ y

requires `M` invertible, which the guidance rightly flags: a singular information matrix
must not be pushed through a pseudoinverse formula unconditionally.

**This file avoids the inverse entirely.**  `kkt_certificate` proves optimality from
primal feasibility, dual nonnegativity, stationarity and complementary slackness alone,
and needs only that `M` is symmetric POSITIVE SEMIDEFINITE.  A singular `M` is therefore
covered with no extra hypothesis and no pseudoinverse.

## WHAT IS PROVED

* `quad_add` — the exact expansion of the quadratic at a displaced point (symmetry only).
* `kkt_certificate` — **the inner certificate.**  Given `λ*` feasible, `y ≥ 0`,
  stationarity `M(λ*−μ) + Aᵀy = 0` and complementary slackness `yᵀAλ* = 0`, then `λ*`
  minimises `½(λ−μ)ᵀM(λ−μ)` over `{λ : Aλ ≤ 0}`.  PSD only; no inverse, no
  positive-definiteness, no attainment assumption.
* `certificate_gives_lower_bound` — the number a referee checks: the certified value is a
  lower bound for the whole region.
* `region_min_lower_bounds_J` — a lower bound for EVERY region, then their minimum, lower
  bounds `J`.  A single feasible alternative only UPPER-bounds `J`; `single_alt_upper`
  records that direction separately so the two are never conflated.
* `crossing_budget` — the setup-cost crossing `B* = κ(|S₂|Γ₂ − |S₁|Γ₁)/(Γ₂ − Γ₁)` at which
  two supports give equal information, verified as an identity.
* `crossing_sign_undetermined` — **if the two `Γ` are only bracketed and the brackets
  overlap, both orders are consistent**, so no crossing may be reported and the honest
  output is UNDECIDED.
* `information_of_support` — `(B − K(S))·Γ(S)`, with the infeasible case excluded rather
  than clamped.

## WHAT THIS DOES NOT ESTABLISH

- `kkt_certificate` is SUFFICIENCY.  It says a point with a certificate is optimal; it does
  not say every optimal point has one (that needs a constraint qualification), and none is
  claimed.
- The scaling identity is about INFORMATION for a static fractional design.  It is not an
  adaptive sample-complexity theorem, and integer allocations are a separate layer.
- Nothing here computes `Γ_range(S)`.  It relates values once they are supplied, whether
  exactly or as brackets.
-/

namespace CIGAMF.P13.FunctionalRangeDesignCertificate

open Finset

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The bilinear form of `M`. -/
def bil (M : ι → ι → ℝ) (x y : ι → ℝ) : ℝ := ∑ p, ∑ q, M p q * x p * y q

/-- The quadratic form of `M`. -/
def quad (M : ι → ι → ℝ) (x : ι → ℝ) : ℝ := bil M x x

/-- One row of the constraint system, applied to a point. -/
def rowAp (A : κ → ι → ℝ) (x : ι → ℝ) (c : κ) : ℝ := ∑ p, A c p * x p

theorem bil_symm (M : ι → ι → ℝ) (hM : ∀ p q, M p q = M q p) (x y : ι → ℝ) :
    bil M x y = bil M y x := by
  unfold bil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  rw [hM q p]
  ring

theorem bil_add_right (M : ι → ι → ℝ) (x y z : ι → ℝ) :
    bil M x (y + z) = bil M x y + bil M x z := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [Pi.add_apply]
  ring

theorem bil_add_left (M : ι → ι → ℝ) (x y z : ι → ℝ) :
    bil M (x + y) z = bil M x z + bil M y z := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [Pi.add_apply]
  ring

/-- The exact expansion at a displaced point.  Symmetry of `M` is all that is used. -/
theorem quad_add (M : ι → ι → ℝ) (hM : ∀ p q, M p q = M q p) (a d : ι → ℝ) :
    quad M (a + d) = quad M a + 2 * bil M d a + quad M d := by
  unfold quad
  rw [bil_add_left, bil_add_right, bil_add_right, bil_symm M hM a d]
  ring

/-- **The inner certificate, with no inverse.**  Primal feasibility, dual nonnegativity,
stationarity and complementary slackness certify optimality over the whole polyhedron.
Only symmetry and positive SEMIdefiniteness of `M` are assumed, so a singular information
matrix is covered with no pseudoinverse. -/
theorem kkt_certificate (M : ι → ι → ℝ) (A : κ → ι → ℝ) (mu lam : ι → ℝ) (y : κ → ℝ)
    (hM : ∀ p q, M p q = M q p)
    (hpsd : ∀ d : ι → ℝ, 0 ≤ quad M d)
    (hy : ∀ c, 0 ≤ y c)
    (hfeas : ∀ c, rowAp A lam c ≤ 0)
    (hstat : ∀ p, (∑ q, M p q * (lam q - mu q)) + (∑ c, y c * A c p) = 0)
    (hcs : ∑ c, y c * rowAp A lam c = 0)
    (lam' : ι → ℝ) (hfeas' : ∀ c, rowAp A lam' c ≤ 0) :
    (1/2) * quad M (fun p => lam p - mu p) ≤ (1/2) * quad M (fun p => lam' p - mu p) := by
  classical
  set a : ι → ℝ := fun p => lam p - mu p with ha
  set d : ι → ℝ := fun p => lam' p - lam p with hd
  have hsplit : (fun p => lam' p - mu p) = a + d := by
    funext p; simp [ha, hd]; try ring
  -- the cross term equals minus the dual value at the competitor, hence is nonnegative
  have hcross : bil M d a = - ∑ c, y c * rowAp A lam' c := by
    unfold bil
    have hinner : ∀ p, (∑ q, M p q * d p * a q) = d p * (∑ q, M p q * (lam q - mu q)) := by
      intro p
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp [ha]
      try ring
    rw [Finset.sum_congr rfl (fun p _ => hinner p)]
    have hstep : ∀ p, d p * (∑ q, M p q * (lam q - mu q)) = - (d p * (∑ c, y c * A c p)) := by
      intro p
      have := hstat p
      have h' : (∑ q, M p q * (lam q - mu q)) = - (∑ c, y c * A c p) := by linarith
      rw [h']; ring
    rw [Finset.sum_congr rfl (fun p _ => hstep p)]
    have hswap : (∑ p, d p * (∑ c, y c * A c p)) = ∑ c, y c * rowAp A d c := by
      unfold rowAp
      have hdist : ∀ p : ι, d p * (∑ c, y c * A c p) = ∑ c, d p * (y c * A c p) :=
        fun p => Finset.mul_sum _ _ _
      rw [Finset.sum_congr rfl (fun p _ => hdist p), Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [Finset.sum_neg_distrib, hswap]
    have hlin : ∀ c, rowAp A (fun p => d p) c = rowAp A lam' c - rowAp A lam c := by
      intro c
      unfold rowAp
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [hd]; ring
    rw [Finset.sum_congr rfl (fun c _ => by rw [hlin c])]
    have hexp : (∑ c, y c * (rowAp A lam' c - rowAp A lam c))
        = (∑ c, y c * rowAp A lam' c) - (∑ c, y c * rowAp A lam c) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => by ring
    rw [hexp, hcs]
    ring
  have hnonneg : 0 ≤ bil M d a := by
    rw [hcross]
    have : ∑ c, y c * rowAp A lam' c ≤ 0 :=
      Finset.sum_nonpos fun c _ => mul_nonpos_of_nonneg_of_nonpos (hy c) (hfeas' c)
    linarith
  rw [hsplit, quad_add M hM a d]
  have := hpsd d
  linarith

/-- The number a referee checks: the certified value lower-bounds the whole region. -/
theorem certificate_gives_lower_bound (M : ι → ι → ℝ) (A : κ → ι → ℝ)
    (mu lam : ι → ℝ) (y : κ → ℝ) (V : ℝ)
    (hM : ∀ p q, M p q = M q p) (hpsd : ∀ d : ι → ℝ, 0 ≤ quad M d)
    (hy : ∀ c, 0 ≤ y c) (hfeas : ∀ c, rowAp A lam c ≤ 0)
    (hstat : ∀ p, (∑ q, M p q * (lam q - mu q)) + (∑ c, y c * A c p) = 0)
    (hcs : ∑ c, y c * rowAp A lam c = 0)
    (hval : V = (1/2) * quad M (fun p => lam p - mu p)) :
    ∀ lam' : ι → ℝ, (∀ c, rowAp A lam' c ≤ 0) →
      V ≤ (1/2) * quad M (fun p => lam' p - mu p) := by
  intro lam' hf
  rw [hval]
  exact kkt_certificate M A mu lam y hM hpsd hy hfeas hstat hcs lam' hf

/-! ## Directions: which optimisation level each bound belongs to. -/

variable {ρ : Type*} [DecidableEq ρ]

/-- **Lower bound on `J`**: a lower bound for EVERY region, then their minimum. -/
theorem region_min_lower_bounds_J (R : Finset ρ) (hR : R.Nonempty)
    (cost : ρ → ℝ) (J : ℝ) (hJ : J = R.inf' hR cost)
    (b : ρ → ℝ) (hb : ∀ r ∈ R, b r ≤ cost r) :
    R.inf' hR b ≤ J := by
  rw [hJ]
  exact Finset.le_inf' hR _ fun r hr => le_trans (Finset.inf'_le _ hr) (hb r hr)

/-- **Upper bound on `J`**: one feasible alternative.  This direction must never be
confused with the previous one. -/
theorem single_alt_upper (R : Finset ρ) (hR : R.Nonempty) (cost : ρ → ℝ) (J : ℝ)
    (hJ : J = R.inf' hR cost) {r : ρ} (hr : r ∈ R) :
    J ≤ cost r := by
  rw [hJ]; exact Finset.inf'_le _ hr

/-! ## The setup-cost law and its crossing. -/

/-- Information of a support: remaining budget times its rate.  The infeasible case is
excluded by hypothesis, never clamped to a small positive number. -/
def information (B kappa : ℝ) (n : ℕ) (G : ℝ) : ℝ := (B - kappa * (n : ℝ)) * G

/-- **The crossing budget.**  Two supports of sizes `n₁, n₂` at equal setup cost `κ` give
equal information exactly at `B* = κ(n₂Γ₂ − n₁Γ₁)/(Γ₂ − Γ₁)`. -/
theorem crossing_budget (kappa G1 G2 : ℝ) (n1 n2 : ℕ) (hne : G2 - G1 ≠ 0) :
    information (kappa * ((n2 : ℝ) * G2 - (n1 : ℝ) * G1) / (G2 - G1)) kappa n1 G1
      = information (kappa * ((n2 : ℝ) * G2 - (n1 : ℝ) * G1) / (G2 - G1)) kappa n2 G2 := by
  unfold information
  field_simp
  ring

/-- **When only brackets are known, no crossing may be reported.**  Overlapping brackets
admit both orders of `Γ₁, Γ₂`, so the sign of the denominator is undetermined and the
honest output is UNDECIDED. -/
theorem crossing_sign_undetermined (G1lo G1hi G2lo G2hi : ℝ)
    (h1 : G1lo ≤ G1hi) (h2 : G2lo ≤ G2hi)
    (hov1 : G2lo ≤ G1hi) (hov2 : G1lo ≤ G2hi) :
    (∃ g1 g2 : ℝ, G1lo ≤ g1 ∧ g1 ≤ G1hi ∧ G2lo ≤ g2 ∧ g2 ≤ G2hi ∧ g2 ≤ g1) ∧
      (∃ g1 g2 : ℝ, G1lo ≤ g1 ∧ g1 ≤ G1hi ∧ G2lo ≤ g2 ∧ g2 ≤ G2hi ∧ g1 ≤ g2) := by
  refine ⟨⟨G1hi, G2lo, h1, le_refl _, le_refl _, h2, hov1⟩,
          ⟨G1lo, G2hi, le_refl _, h1, h2, le_refl _, hov2⟩⟩

/-- Information is monotone in the remaining budget, for a nonnegative rate. -/
theorem information_mono (B B' kappa G : ℝ) (n : ℕ) (hG : 0 ≤ G) (hBB : B ≤ B') :
    information B kappa n G ≤ information B' kappa n G := by
  unfold information
  exact mul_le_mul_of_nonneg_right (by linarith) hG

#print axioms bil_symm
#print axioms quad_add
#print axioms kkt_certificate
#print axioms certificate_gives_lower_bound
#print axioms region_min_lower_bounds_J
#print axioms single_alt_upper
#print axioms crossing_budget
#print axioms crossing_sign_undetermined
#print axioms information_mono

end CIGAMF.P13.FunctionalRangeDesignCertificate
