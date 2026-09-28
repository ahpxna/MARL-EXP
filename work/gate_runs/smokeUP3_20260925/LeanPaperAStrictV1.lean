import «LeanPaperACentredModelV1»

/-!
# Paper A: the STRICT alternative game, and the Gaussian divergence on the whole class

Two obligations are discharged here, both of which the closed-set formulation left open.

**The strict game.**  `LeanPaperACentredModelV1` proves that retaining `A` is `eps`-unsafe
exactly when `range(lam_B) > range(lam_A) + 2 eps` --- a STRICT inequality.  The games of
`LeanPaperACentredV1` are solved over the CLOSED set `{range(lam_A) <= range(lam_B)}`, which
contains a tie, and a tie is safe.  So the closed game is an infimum over a strictly larger
set, and its bounds do not automatically say anything about the game the decision defines.
Naming a lemma "strict" does not fix that; the two infima have to be related.

They are, and in both directions, for a reason:

* the strict set is CONTAINED in the closed one, so the strict infimum is at least the
  closed one --- the LOWER bound transfers upward for free;
* the strict set contains, for every `delta > 0`, the pair shift by `1/2 + delta`, so the
  strict infimum is bounded above by that witness's energy --- and letting `delta` go to
  zero recovers the same `1/(8 M r)`.

**The divergence.**  `energy` is asserted throughout to be the information.  For a Gaussian
observation with a common variance the per-cell divergence is the squared gap over twice the
variance, and the log-likelihood ratio is AFFINE in the observation --- which is why its
expectation needs only the first moment and no second-moment computation.  That identity
holds for EVERY pair of parameters, not only inside `Theta_0`: the class restriction is what
makes the MARGINAL recover the coordinate, and is a separate matter from the divergence.
-/

namespace CIGAMF.P13.PaperAStrict

open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.PaperARPair
open CIGAMF.P13.PaperACentred

variable {r : ℕ}

/-! ## The Gaussian divergence, and `energy` as its weighted sum -/

/-- The divergence between two Gaussians of a common variance. -/
noncomputable def gaussKL (θ lam σ2 : ℝ) : ℝ := (θ - lam) ^ 2 / (2 * σ2)

/-- **The log-likelihood ratio is affine in the observation.**  This is the structural
reason the divergence needs only the first moment. -/
theorem logratio_affine (θ lam σ2 y : ℝ) :
    ((y - lam) ^ 2 - (y - θ) ^ 2) / (2 * σ2)
      = (θ - lam) * (2 * y - θ - lam) / (2 * σ2) := by
  have h : (y - lam) ^ 2 - (y - θ) ^ 2 = (θ - lam) * (2 * y - θ - lam) := by ring
  rw [h]

/-- **The divergence, computed from the first moment alone.**  The integrand is the affine
log-ratio above, and the Gaussian's mean is its own parameter. -/
theorem gaussKL_eq_integral (θ lam : ℝ) (v : NNReal) (hv : (0 : ℝ) < (v : ℝ)) :
    ∫ y : ℝ, (θ - lam) * (2 * y - θ - lam) / (2 * (v : ℝ)) ∂(gaussianReal θ v)
      = gaussKL θ lam (v : ℝ) := by
  have hfun : (fun y : ℝ => (θ - lam) * (2 * y - θ - lam) / (2 * (v : ℝ)))
      = fun y : ℝ => ((θ - lam) / (v : ℝ)) * y
          + (-((θ - lam) * (θ + lam)) / (2 * (v : ℝ))) := by
    funext y
    field_simp
    ring
  rw [hfun]
  have hint : Integrable (fun y : ℝ => ((θ - lam) / (v : ℝ)) * y) (gaussianReal θ v) :=
    (IsGaussian.integrable_fun_id).const_mul _
  have hconst : ∫ _y : ℝ, (-((θ - lam) * (θ + lam)) / (2 * (v : ℝ))) ∂(gaussianReal θ v)
      = -((θ - lam) * (θ + lam)) / (2 * (v : ℝ)) := by simp
  rw [integral_add hint (integrable_const _), integral_const_mul,
      integral_id_gaussianReal, hconst]
  unfold gaussKL
  field_simp
  ring

/-- **`energy` IS the weighted sum of per-cell Gaussian divergences**, for every candidate
and every design --- no membership of a class is used. -/
theorem energy_eq_sum_gaussKL (w var θ lam : Cell r → ℝ) :
    energy w var θ lam = ∑ e, w e * gaussKL (θ e) (lam e) (var e) := by
  unfold energy gaussKL
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-! ## The strict alternative game -/

/-- The alternatives at which retaining `A` is genuinely wrong: a STRICT range gap, inside
the class.  A tie is safe and is excluded. -/
def TrueAltStrict (r : ℕ) : Set (Cell r → ℝ) :=
  {lam | rangeA lam < rangeB lam} ∩ Centred r

theorem strict_subset_closed (lam : Cell r → ℝ) (h : lam ∈ TrueAltStrict r) :
    lam ∈ TrueAltC₀ r := by
  refine ⟨?_, h.2⟩
  show rangeA lam ≤ rangeB lam
  exact le_of_lt h.1

instance instNonemptyTrueAltStrict (r : ℕ) [NeZero r] : Nonempty (TrueAltStrict r) := by
  refine ⟨⟨pairShift (thetaC r) ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩ (1 / 2 + 1), ?_⟩⟩
  exact ⟨(pairShiftC_strict_alt _ 1 one_pos).1, pairShiftC_mem_centred _ _⟩

noncomputable def trueValueStrict (M : ℝ) (w : Cell r → ℝ) : ℝ :=
  ⨅ lam : TrueAltStrict r, energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ)

noncomputable def trueGameStrict (r : ℕ) (M : ℝ) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, trueValueStrict M (w : Cell r → ℝ)

theorem bddBelowStrict (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (Set.range (fun lam : TrueAltStrict r =>
      energy w (pairVar M) (thetaC r) (lam : Cell r → ℝ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨lam, rfl⟩
  exact energyC_nonneg M hM w _ hw

/-- **The lower bound transfers upward for free**, because the strict set is contained in
the closed one and an infimum over a smaller set is larger. -/
theorem trueValueC₀_le_trueValueStrict (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ)
    (hw : ∀ e, 0 ≤ w e) [NeZero r] :
    trueValueC₀ M w ≤ trueValueStrict M w :=
  le_ciInf (fun lam => ciInf_le (bddBelowTrueC₀ M hM w hw)
    (⟨(lam : Cell r → ℝ), strict_subset_closed _ lam.2⟩ : TrueAltC₀ r))

/-- **The strict game's lower bound**, inherited. -/
theorem trueValueStrict_wCert_ge (r : ℕ) (M : ℝ) (hM : 0 < M) [NeZero r] :
    (9 : ℝ) / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueValueStrict M (wCert r M) :=
  le_trans (trueValueC₀_wCert_ge r M hM)
    (trueValueC₀_le_trueValueStrict M hM (wCert r M) (wCert_isAlloc r M hM).1 )

/-- **The strict upper bound, at every positive margin.**  The shift by `1/2 + delta` is a
genuinely strict alternative inside the class, so it bounds the strict infimum. -/
theorem trueValueStrict_le_shift (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ)
    (hw : ∀ e, 0 ≤ w e) (j : Fin r) (δ : ℝ) (hδ : 0 < δ) [NeZero r] :
    trueValueStrict M w ≤ pairWeight w j * (1 / 2 + δ) ^ 2 / (2 * M) := by
  have hmem : pairShift (thetaC r) j (1 / 2 + δ) ∈ TrueAltStrict r :=
    ⟨(pairShiftC_strict_alt j δ hδ).1, pairShiftC_mem_centred j (1 / 2 + δ)⟩
  have h : trueValueStrict M w
      ≤ energy w (pairVar M) (thetaC r) (pairShift (thetaC r) j (1 / 2 + δ)) :=
    ciInf_le (bddBelowStrict M hM w hw)
      (⟨pairShift (thetaC r) j (1 / 2 + δ), hmem⟩ : TrueAltStrict r)
  rwa [pair_shift_energy w (pairVar M) (thetaC r) (pairShift (thetaC r) j (1 / 2 + δ)) j M
      (1 / 2 + δ) hM (pairVarC_pair M (j, true)) (pairVarC_pair M (j, false))
      (pairShift_true (thetaC r) j (1 / 2 + δ))
      (pairShift_false (thetaC r) j (1 / 2 + δ))
      (fun e h1 h2 => pairShift_rest (thetaC r) j (1 / 2 + δ) e h1 h2)] at h

/-- **Starvation holds on the strict game too.**  A design with no weight on the middles has
zero energy against every pair shift, strict ones included. -/
theorem starved_trueValueStrict_zero (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r) [NeZero r]
    (w : Cell r → ℝ) (hw : IsAlloc w)
    (hstarve : ∑ p : Fin r × Bool, w (Sum.inr p) = 0) :
    trueValueStrict M w = 0 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨j, hj⟩ := exists_light_pair_le r hr (pairWeight w) 0
      (by rw [← middle_eq_sum_pairWeight, hstarve])
    have hz : pairWeight w j ≤ 0 := by
      have h0 : (0 : ℝ) / (r : ℝ) = 0 := by simp
      rwa [h0] at hj
    have hnn : 0 ≤ pairWeight w j := pairWeight_nonneg w hw.1 j
    have heq : pairWeight w j = 0 := le_antisymm hz hnn
    have h := trueValueStrict_le_shift M hM w hw.1 j 1 one_pos
    rw [heq] at h
    simpa using h
  · exact le_ciInf (fun lam => energyC_nonneg M hM w _ hw.1)

/-- **The frozen optimum is uninformative for the STRICT game.**  This is the form the
decision actually defines. -/
theorem frozen_optimum_trueValueStrict_zero (M : ℝ) (hM : 0 < M) (r : ℕ) (hr : 0 < r)
    [NeZero r] (w : Cell r → ℝ) (hw : IsAlloc w)
    (hopt : (9 : ℝ) / 512 ≤ frozenValueC₀ M w) :
    trueValueStrict M w = 0 :=
  starved_trueValueStrict_zero M hM r hr w hw (starvation_at_optimum₀ M hM w hw hopt).2

/-! ## Audit -/

#print axioms logratio_affine
#print axioms gaussKL_eq_integral
#print axioms energy_eq_sum_gaussKL
#print axioms strict_subset_closed
#print axioms trueValueC₀_le_trueValueStrict
#print axioms trueValueStrict_wCert_ge
#print axioms trueValueStrict_le_shift
#print axioms starved_trueValueStrict_zero
#print axioms frozen_optimum_trueValueStrict_zero

end CIGAMF.P13.PaperAStrict
