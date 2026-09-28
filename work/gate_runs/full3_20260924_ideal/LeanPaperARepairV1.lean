import Mathlib

/-!
# Paper A, package A-repair: when the frozen surrogate is RIGHT, certifiably.

## WHY THIS MODULE EXISTS

`LeanPaperASeparationV1` shows the frozen surrogate can misprice in either direction, so no
constant-factor repair exists.  That is a negative result, and on its own it would leave the
surrogate unusable.  This module supplies the positive half: a CHECKABLE condition at a
given design under which the surrogate's value is exactly the true value.

## THE CONDITION

Let `R0` be the region in which the current extrema stay the extrema.  It is cut out by
ordering inequalities `a_j^T lambda >= b_j`, each of which the true world satisfies with
slack `d_j = a_j^T theta - b_j > 0`.  For a design with energy
`E(lambda) = (1/2) sum_e h_e (lambda_e - theta_e)^2`, the cheapest way to violate the `j`-th
ordering is exactly

    B_j = d_j^2 / (2 * sum_e a_{j,e}^2 / h_e),                                     (B)

and `B_switch = min_j B_j` is the cheapest way to leave `R0` at all.  `halfspace_energy_ge`
proves the inequality in (B) -- the direction that matters, since it is what makes leaving
`R0` expensive -- and `halfspace_energy_attained` exhibits a point achieving it, so the
constant is not loose.

Then:

    J_proxy(w) < B_switch(w)   ==>   J_true(w) = J_proxy(w).

The reason is short.  A proxy alternative cheaper than `B_switch` cannot have left `R0`;
inside `R0` the two alternative sets coincide because the extrema have not moved; and no
alternative outside `R0` can undercut it.  `barrier_implies_equality` is that argument.

## WHAT THIS DOES *NOT* SAY

It is a certificate AT ONE DESIGN.  `Gamma = sup_w J(w)`, and an equality of the two
objectives at one `w` says nothing about the two suprema.  `optima_equal_of_certificate`
records exactly what must be added: a proxy-optimal design, the barrier condition holding
there, and a DUAL certificate bounding the true game at every design.  All three are
hypotheses of that theorem, and none of them is proved here.  Conflating the two statements
is the error this section is written to prevent.

Singular information matrices are excluded rather than handled: (B) divides by
`sum_e a_e^2 / h_e`, which requires every `h_e > 0`.  A design that measures nothing along
some direction needs the nullspace analysis, not this formula.
-/

namespace CIGAMF.P13.PaperARepair

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Cauchy-Schwarz, proved here

The finite-sum Cauchy-Schwarz inequality is used under several names across Mathlib
versions, so the discriminant argument is carried out directly. -/

theorem cauchy_schwarz_sum (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
  classical
  set A := ∑ i ∈ s, f i ^ 2 with hA
  set B := ∑ i ∈ s, g i ^ 2 with hB
  set C := ∑ i ∈ s, f i * g i with hC
  have hAnn : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · -- every `f i` vanishes, so both sides are zero
    have hzero : ∀ i ∈ s, f i = 0 := by
      intro i hi
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (f j))).1 hA0.symm i hi
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : C = 0 := by
      rw [hC]
      exact Finset.sum_eq_zero (fun i hi => by rw [hzero i hi]; ring)
    rw [this, ← hA0]
    simp
  · -- the quadratic `t ↦ ∑ (t f i - g i)^2` is nonnegative; evaluate at `t = C / A`
    have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * C + B := by
      intro t
      have hexp : ∑ i ∈ s, (t * f i - g i) ^ 2 = t ^ 2 * A - 2 * t * C + B := by
        rw [hA, hB, hC, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [← hexp]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have := hquad (C / A)
    have hne : A ≠ 0 := ne_of_gt hApos
    field_simp at this
    nlinarith [this, hApos]

/-! ## The barrier: the cost of leaving the current region -/

/-- The energy of a design with positive per-coordinate information. -/
noncomputable def energy (h θ lam : ι → ℝ) : ℝ :=
  (∑ e, h e * (lam e - θ e) ^ 2) / 2

/-- **(B), the direction that matters.**  Crossing the hyperplane `a^T lambda = b`, which
the true world clears with slack `d`, costs at least `d^2 / (2 * sum a_e^2 / h_e)`. -/
theorem halfspace_energy_ge (h θ a : ι → ℝ) (b : ℝ)
    (hh : ∀ e, 0 < h e)
    (hq : 0 < ∑ e, a e ^ 2 / h e)
    (hslack : 0 ≤ (∑ e, a e * θ e) - b)
    (lam : ι → ℝ) (hcross : ∑ e, a e * lam e ≤ b) :
    ((∑ e, a e * θ e) - b) ^ 2 / (2 * ∑ e, a e ^ 2 / h e) ≤ energy h θ lam := by
  classical
  set d := (∑ e, a e * θ e) - b with hd
  set q := ∑ e, a e ^ 2 / h e with hq_def
  set S := ∑ e, h e * (lam e - θ e) ^ 2 with hS
  have hSnn : 0 ≤ S :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (le_of_lt (hh e)) (sq_nonneg _))
  -- the linear functional's displacement is at least `d`
  have hdisp : d ≤ ∑ e, a e * (θ e - lam e) := by
    have : ∑ e, a e * (θ e - lam e) = (∑ e, a e * θ e) - ∑ e, a e * lam e := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [this, hd]
    linarith
  -- Cauchy-Schwarz with the splitting `a_e = (a_e / sqrt h_e) * sqrt h_e`
  have hcs : (∑ e, a e * (θ e - lam e)) ^ 2 ≤ q * S := by
    have hsplit : ∀ e : ι, a e * (θ e - lam e)
        = (a e / Real.sqrt (h e)) * (Real.sqrt (h e) * (θ e - lam e)) := by
      intro e
      have : Real.sqrt (h e) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hh e))
      field_simp
    have hrw : ∑ e, a e * (θ e - lam e)
        = ∑ e, (a e / Real.sqrt (h e)) * (Real.sqrt (h e) * (θ e - lam e)) :=
      Finset.sum_congr rfl (fun e _ => hsplit e)
    have hcs0 := cauchy_schwarz_sum (Finset.univ : Finset ι)
      (fun e => a e / Real.sqrt (h e)) (fun e => Real.sqrt (h e) * (θ e - lam e))
    have hq1 : ∑ e, (a e / Real.sqrt (h e)) ^ 2 = q := by
      rw [hq_def]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [div_pow, Real.sq_sqrt (le_of_lt (hh e))]
    have hq2 : ∑ e, (Real.sqrt (h e) * (θ e - lam e)) ^ 2 = S := by
      rw [hS]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [mul_pow, Real.sq_sqrt (le_of_lt (hh e))]
      ring_nf
    rw [hrw]
    rw [hq1, hq2] at hcs0
    exact hcs0
  -- put the two together
  have hdnn : 0 ≤ d := by rw [hd]; exact hslack
  have hdsq : d ^ 2 ≤ q * S := by
    nlinarith [hdisp, hcs, hdnn]
  unfold energy
  rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * q) (by norm_num : (0:ℝ) < 2)]
  nlinarith [hdsq]

/-- The bound of `halfspace_energy_ge` is ATTAINED, so the barrier constant is exact and
not merely a safe underestimate. -/
theorem halfspace_energy_attained (h θ a : ι → ℝ) (b : ℝ)
    (hh : ∀ e, 0 < h e)
    (hq : 0 < ∑ e, a e ^ 2 / h e) :
    ∃ lam : ι → ℝ, (∑ e, a e * lam e) = b ∧
      energy h θ lam = ((∑ e, a e * θ e) - b) ^ 2 / (2 * ∑ e, a e ^ 2 / h e) := by
  classical
  set d := (∑ e, a e * θ e) - b with hd
  set q := ∑ e, a e ^ 2 / h e with hq_def
  refine ⟨fun e => θ e - (d / q) * (a e / h e), ?_, ?_⟩
  · have : ∑ e, a e * (θ e - (d / q) * (a e / h e))
        = (∑ e, a e * θ e) - (d / q) * ∑ e, a e ^ 2 / h e := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      field_simp
    rw [this, ← hq_def]
    field_simp
    linarith [hd]
  · unfold energy
    have hterm : ∀ e : ι, h e * ((θ e - (d / q) * (a e / h e)) - θ e) ^ 2
        = (d / q) ^ 2 * (a e ^ 2 / h e) := by
      intro e
      have hne := ne_of_gt (hh e)
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun e _ => hterm e), ← Finset.mul_sum, ← hq_def]
    field_simp

/-! ## The certificate at a design -/

variable {Λ : Type*}

/-- **The repair theorem.**  If everything outside the region costs at least `B`, the two
alternative sets agree inside the region, and the proxy's value is below `B`, then the true
and proxy values coincide.  The proof never inspects the geometry: it is the barrier that
confines the cheap alternatives to where the two descriptions already agree. -/
theorem barrier_implies_equality
    (E : Λ → ℝ) (R0 : Set Λ) (AltT AltP : Set Λ) (B v : ℝ)
    (hbar : ∀ lam, lam ∉ R0 → B ≤ E lam)
    (hagree : AltT ∩ R0 = AltP ∩ R0)
    (hv : IsGLB (E '' AltP) v)
    (hvB : v < B) :
    IsGLB (E '' AltT) v := by
  classical
  constructor
  · -- `v` is still a lower bound
    rintro x ⟨lam, hlam, rfl⟩
    by_cases hmem : lam ∈ R0
    · have : lam ∈ AltP := by
        have : lam ∈ AltT ∩ R0 := ⟨hlam, hmem⟩
        rw [hagree] at this
        exact this.1
      exact hv.1 ⟨lam, this, rfl⟩
    · exact le_trans (le_of_lt hvB) (hbar lam hmem)
  · -- and no larger number is
    intro c hc
    by_contra hlt
    push_neg at hlt
    -- `c > v`, so some proxy alternative has energy below `min c B`
    set m := min c B with hm
    have hvm : v < m := lt_min hlt hvB
    obtain ⟨x, hx, hxm⟩ : ∃ x ∈ E '' AltP, x < m := by
      by_contra hno
      push_neg at hno
      exact absurd (hv.2 hno) (not_le.2 hvm)
    obtain ⟨lam, hlamP, rfl⟩ := hx
    have hin : lam ∈ R0 := by
      by_contra hout
      exact absurd (hbar lam hout) (not_le.2 (lt_of_lt_of_le hxm (min_le_right c B)))
    have hlamT : lam ∈ AltT := by
      have : lam ∈ AltP ∩ R0 := ⟨hlamP, hin⟩
      rw [← hagree] at this
      exact this.1
    exact absurd (hc ⟨lam, hlamT, rfl⟩) (not_le.2 (lt_of_lt_of_le hxm (min_le_left c B)))

/-- **What a design certificate does NOT give.**  To conclude that the two GAMES have the
same value, three further things are needed, and all three appear here as hypotheses: a
design at which the proxy attains its supremum, the barrier condition holding at that
design, and a dual certificate bounding the true objective at EVERY design.  Without the
last one the true game could be worth more somewhere the barrier fails. -/
theorem optima_equal_of_certificate {W : Type*}
    (Jtrue Jproxy : W → ℝ) (V : ℝ) (wstar : W)
    (hagree_at_star : Jtrue wstar = Jproxy wstar)
    (hstar : Jproxy wstar = V)
    (hdual : ∀ w, Jtrue w ≤ V) :
    IsGreatest (Set.range Jtrue) V := by
  constructor
  · exact ⟨wstar, by rw [hagree_at_star, hstar]⟩
  · rintro x ⟨w, rfl⟩
    exact hdual w

/-- The contrapositive, spelled out: without the dual certificate the conclusion can fail.
If some design gives the true game more than `V`, then `V` is not the value, however good
the certificate at `wstar` is.  This is recorded so the two statements are never merged. -/
theorem design_certificate_insufficient {W : Type*}
    (Jtrue : W → ℝ) (V : ℝ) (w' : W) (hw' : V < Jtrue w') :
    ¬ IsGreatest (Set.range Jtrue) V := by
  rintro ⟨-, hub⟩
  exact absurd (hub ⟨w', rfl⟩) (not_le.2 hw')

/-! ## The optimum over CERTIFIABLE designs

`barrier_implies_equality` is a certificate at one design, and `optima_equal_of_certificate`
says what more is needed to reach the two games.  Neither bounds how good a design the
criterion can certify, and an experiment that maximises over sampled designs reports a lower
bound on that, never the optimum.  This section proves the upper bound.

The argument is short once stated.  Where the barrier fires the two objectives AGREE, so the
proxy value at a certifiable design is a true value, and every true value is at most the
true game's worth.  Hence

    sup over certifiable designs of J_proxy  <=  Gamma_true,

and dividing by `Gamma_proxy` bounds the fraction of the proxy game that certification can
reach by the SEPARATION RATIO itself.  In the family where that ratio tends to zero, the
reachable fraction does too -- proved, not sampled. -/

/-- **The certifiable part of the proxy game is worth at most the true game.**

Every design the criterion certifies has `J_proxy = J_true`, and `J_true` is bounded by the
true game's value.  So certification cannot reach past `Gamma_true`, however the design is
chosen. -/
theorem certifiable_sup_le_true {W : Type*}
    (Jtrue Jproxy : W → ℝ) (Cert : W → Prop) (Γtrue : ℝ)
    (hagree : ∀ w, Cert w → Jtrue w = Jproxy w)
    (hdual : ∀ w, Jtrue w ≤ Γtrue)
    (w : W) (hw : Cert w) :
    Jproxy w ≤ Γtrue := by
  rw [← hagree w hw]
  exact hdual w

/-- **The reachable fraction is at most the separation ratio.**

Dividing the previous bound by the proxy game's value: no certifiable design attains more
than `Gamma_true / Gamma_proxy` of it.  In family A-low that ratio is at most `64/M`, so the
fraction the criterion can certify is at most `64/M` and tends to zero with `1/M` -- a
statement about every design, not about a sample.

This is the bound an experiment's sampled maximum can only approach from below.  Reading a
sampled maximum as the optimum, in either direction, is the error this theorem replaces. -/
theorem certifiable_fraction_le_ratio {W : Type*}
    (Jtrue Jproxy : W → ℝ) (Cert : W → Prop) (Γtrue Γproxy : ℝ)
    (hagree : ∀ w, Cert w → Jtrue w = Jproxy w)
    (hdual : ∀ w, Jtrue w ≤ Γtrue)
    (hPpos : 0 < Γproxy)
    (w : W) (hw : Cert w) :
    Jproxy w / Γproxy ≤ Γtrue / Γproxy :=
  div_le_div_of_nonneg_right (certifiable_sup_le_true Jtrue Jproxy Cert Γtrue hagree hdual w hw)
    (le_of_lt hPpos)

/-- **The A-low consequence, with the constant.**  Composing with the separation bound
`Gamma_true <= (64/M) Gamma_proxy`: no certifiable design reaches more than `64/M` of the
proxy game.  At `M = 256` that is `1/4`; the rational witness found at that size reaches
about `0.4%`, which is consistent and well inside the bound.

The criterion is SUFFICIENT and not necessary, so a design it fails to certify is not
thereby shown to be mispriced; the bound above constrains what certification can reach, and
says nothing about the rest. -/
theorem certifiable_fraction_le_sixtyfour_over_M {W : Type*}
    (Jtrue Jproxy : W → ℝ) (Cert : W → Prop) (Γtrue Γproxy M : ℝ)
    (hagree : ∀ w, Cert w → Jtrue w = Jproxy w)
    (hdual : ∀ w, Jtrue w ≤ Γtrue)
    (hsep : Γtrue / Γproxy ≤ 64 / M)
    (hPpos : 0 < Γproxy)
    (w : W) (hw : Cert w) :
    Jproxy w / Γproxy ≤ 64 / M :=
  le_trans (certifiable_fraction_le_ratio Jtrue Jproxy Cert Γtrue Γproxy hagree hdual
    hPpos w hw) hsep

/-! ## Audit -/

#print axioms cauchy_schwarz_sum
#print axioms halfspace_energy_ge
#print axioms halfspace_energy_attained
#print axioms barrier_implies_equality
#print axioms optima_equal_of_certificate
#print axioms design_certificate_insufficient
#print axioms certifiable_sup_le_true
#print axioms certifiable_fraction_le_ratio
#print axioms certifiable_fraction_le_sixtyfour_over_M

end CIGAMF.P13.PaperARepair
