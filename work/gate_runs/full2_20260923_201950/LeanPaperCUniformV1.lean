import «LeanPaperCMixV1»
import «LeanPaperCBreakpointV1»

/-!
# Paper C: the even mixture is feasible at uniform marginals

`LeanPaperCMixV1` computes the even mixture's VALUE at every budget and says in its own
header that the feasibility is not established there.  `THEOREM_MAP.md` recorded that as a
residual of C-H1.  It is a proof obligation, not a modelling choice, and this module
discharges it.

The mixture is the one the value theorem uses: the `m-1` insertion rankings and the flat
ranking, uniformly over the `m` of them, each further mixed half-and-half with its sign
flip.  Write `P_0 = ((m-1)/m) P_ins + (1/m) P_flat` for the unflipped part.

* The two heavy types already sit at `k/m` BEFORE the flip:

      C_{+3}(k) = ((m-1)/m)(k/(m-1)) + (1/m)(0)     = k/m,
      C_{-3}(k) = ((m-1)/m)((k-1)/(m-1)) + (1/m)(1) = k/m.

  The flat ranking contributes the single `-3` at position `0`, which is exactly the `1/m`
  the insertion mixture is short of.

* The two light types do NOT, and this is where the flip is needed:

      C_{+1}(k) = (m-2)/m * oddsBelow k,
      C_{-1}(k) = (m-2)/m * evensBelow k,

  which differ by `(m-2)/m` at odd budgets.  Averaging with the sign flip exchanges the two
  and `evens_add_odds` turns the pair into `(m-2) k / (2m)` -- that is `(m-2)/2` items, the
  multiplicity of each light type, each at marginal `k/m`.

So every type's expected count is its multiplicity times `k/m`, at every budget: the band
holds at `eta = 0`, not merely at `eta_*(m)`.  The per-ITEM statement follows from
`marginal_eq_occupancy_div_card` with the within-type constancy the uniform relabelling
supplies, and `uniform_marginals_from_relabelling` is that assembly.

NOTE FOR THE MAP.  `O1_even` records the band of the insertion mixture ALONE at
`eta_*(m) = (m-2)/(2(m-1))`.  Adding the flat ranking, which the value theorem already
mixes in, moves that to `0` without changing the value.  Whether the even breakpoint of
C-H2 should therefore be restated is a question about the claim, not about these
computations, and it is raised rather than answered here.
-/

namespace CIGAMF.P13.PaperCUniform

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCEven
open CIGAMF.P13.PaperCBreakpoint

/-! ## The flat ranking's type counts -/

/-- The flat ranking's weight at position `i`, indexed by a natural number. -/
noncomputable def flatW (m i : ℕ) : ℝ :=
  if i = 0 then -3 else if i = m - 1 then 3 else if i % 2 = 1 then 1 else -1

theorem flatEven_eq_flatW (m : ℕ) (i : Fin m) : flatEven m i = flatW m (i : ℕ) := rfl

/-- How many of the first `k` positions of the flat ranking carry weight `w`. -/
noncomputable def flatCount (m : ℕ) (w : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (if flatW m i = w then (1 : ℝ) else 0)

theorem flatCount_three (m k : ℕ) (hm : 1 < m) (hk : k ≤ m - 1) :
    flatCount m 3 k = 0 := by
  unfold flatCount
  refine Finset.sum_eq_zero (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hlt : i < m - 1 := by omega
  have hne : i ≠ m - 1 := by omega
  rw [if_neg]
  unfold flatW
  by_cases h0 : i = 0
  · rw [if_pos h0]; norm_num
  · rw [if_neg h0, if_neg hne]
    by_cases hp : i % 2 = 1
    · rw [if_pos hp]; norm_num
    · rw [if_neg hp]; norm_num

theorem flatCount_neg_three (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    flatCount m (-3) k = 1 := by
  unfold flatCount
  have hterm : ∀ i ∈ Finset.range k,
      (if flatW m i = -3 then (1 : ℝ) else 0) = (if i = 0 then (1 : ℝ) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hne : i ≠ m - 1 := by omega
    unfold flatW
    by_cases h0 : i = 0
    · rw [if_pos h0, if_pos h0, if_pos rfl]
    · rw [if_neg h0, if_neg hne, if_neg h0]
      by_cases hp : i % 2 = 1
      · rw [if_pos hp, if_neg (by norm_num : ¬((1 : ℝ) = -3))]
      · rw [if_neg hp, if_neg (by norm_num : ¬((-1 : ℝ) = -3))]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_ite_eq' (Finset.range k) 0 (fun _ => (1 : ℝ))]
  rw [if_pos (Finset.mem_range.mpr (by omega))]

theorem flatCount_one (m k : ℕ) (hm : 1 < m) (hk : k ≤ m - 1) :
    flatCount m 1 k = oddsBelow k := by
  unfold flatCount oddsBelow
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hne : i ≠ m - 1 := by omega
  unfold flatW
  by_cases h0 : i = 0
  · rw [if_pos h0, if_neg (by norm_num : ¬((-3 : ℝ) = 1)),
      if_neg (by simp [h0] : ¬ ¬ Even i)]
  · rw [if_neg h0, if_neg hne]
    by_cases hp : i % 2 = 1
    · rw [if_pos hp, if_pos rfl, if_pos (by rw [Nat.not_even_iff]; omega)]
    · rw [if_neg hp, if_neg (by norm_num : ¬((-1 : ℝ) = 1)),
        if_neg (by rw [not_not, Nat.even_iff]; omega)]

theorem flatCount_neg_one (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    flatCount m (-1) k = evensBelow k - 1 := by
  unfold flatCount
  have hterm : ∀ i ∈ Finset.range k,
      (if flatW m i = -1 then (1 : ℝ) else 0)
        = (if Even i then (1 : ℝ) else 0) - (if i = 0 then (1 : ℝ) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hne : i ≠ m - 1 := by omega
    unfold flatW
    by_cases h0 : i = 0
    · rw [if_pos h0, if_neg (by norm_num : ¬((-3 : ℝ) = -1)),
        if_pos (by simp [h0] : Even i), if_pos h0]
      norm_num
    · rw [if_neg h0, if_neg hne, if_neg h0]
      by_cases hp : i % 2 = 1
      · rw [if_pos hp, if_neg (by norm_num : ¬((1 : ℝ) = -1)),
          if_neg (by rw [Nat.even_iff]; omega)]
        norm_num
      · rw [if_neg hp, if_pos rfl, if_pos (by rw [Nat.even_iff]; omega)]
        norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (Finset.range k) 0 (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_range.mpr (by omega))]
  rfl

/-! ## The mixture that includes the flat ranking -/

/-- The unflipped mixture: the insertion mixture at weight `(m-1)/m`, the flat ranking at
weight `1/m`.  This is exactly the mixture whose value `evenMixture_value_at_D` computes. -/
noncomputable def mixFlat (m : ℕ) (w : ℝ) (k : ℕ) : ℝ :=
  (((m : ℝ) - 1) / (m : ℝ)) * mixCount m w k + (1 / (m : ℝ)) * flatCount m w k

/-- The mixture symmetrised by the sign flip. -/
noncomputable def uniformMix (m : ℕ) (w : ℝ) (k : ℕ) : ℝ :=
  (mixFlat m w k + mixFlat m (-w) k) / 2

theorem uniformMix_symm (m : ℕ) (w : ℝ) (k : ℕ) :
    uniformMix m w k = uniformMix m (-w) k := by
  unfold uniformMix
  rw [neg_neg]
  ring

/-- **The `+3` item's expected count is already `k/m`**, before any flip: the flat
ranking's single `-3` at position `0` supplies exactly what the insertion mixture lacks. -/
theorem mixFlat_three (m k : ℕ) (hm : 1 < m) (hk : k ≤ m - 1) :
    mixFlat m 3 k = (k : ℝ) / (m : ℝ) := by
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold mixFlat
  rw [mixCount_three m k hm hk, flatCount_three m k hm hk]
  field_simp
  ring

theorem mixFlat_neg_three (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    mixFlat m (-3) k = (k : ℝ) / (m : ℝ) := by
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold mixFlat
  rw [mixCount_neg_three m k hm hk1 hk, flatCount_neg_three m k hm hk1 hk]
  field_simp
  ring

theorem mixFlat_one (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    mixFlat m 1 k = ((m : ℝ) - 2) / (m : ℝ) * oddsBelow k := by
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold mixFlat
  rw [mixCount_one m k hm hk1 hk, flatCount_one m k hm hk]
  field_simp
  ring

theorem mixFlat_neg_one (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    mixFlat m (-1) k = ((m : ℝ) - 2) / (m : ℝ) * evensBelow k := by
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold mixFlat
  rw [mixCount_neg_one m k hm hk1 hk, flatCount_neg_one m k hm hk1 hk]
  field_simp
  ring

/-! ## Uniform marginals, exactly -/

/-- **The heavy types sit at `k/m` exactly.**  One item each, so this is the marginal. -/
theorem uniformMix_heavy (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    uniformMix m 3 k = 1 * ((k : ℝ) / (m : ℝ)) := by
  unfold uniformMix
  rw [mixFlat_three m k hm hk, show ((-3 : ℝ)) = -(3 : ℝ) from rfl,
    mixFlat_neg_three m k hm hk1 hk]
  ring

/-- **The light types sit at `(m-2)/2 * k/m` exactly.**  The flip is what does it:
`evens_add_odds` collapses the pair to the budget. -/
theorem uniformMix_light (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    uniformMix m 1 k = (((m : ℝ) - 2) / 2) * ((k : ℝ) / (m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold uniformMix
  rw [mixFlat_one m k hm hk1 hk, show ((-1 : ℝ)) = -(1 : ℝ) from rfl,
    mixFlat_neg_one m k hm hk1 hk]
  have hsum : evensBelow k + oddsBelow k = (k : ℝ) := evens_add_odds k
  field_simp
  nlinarith [hsum]

/-- **(C-H1 feasibility) The band holds at `eta = 0`**, at every budget and for every
weight type.  Not `eta_*(m)`: zero. -/
theorem uniform_band_zero (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |uniformMix m 3 k - 1 * ((k : ℝ) / (m : ℝ))| ≤ 0 ∧
    |uniformMix m (-3) k - 1 * ((k : ℝ) / (m : ℝ))| ≤ 0 ∧
    |uniformMix m 1 k - (((m : ℝ) - 2) / 2) * ((k : ℝ) / (m : ℝ))| ≤ 0 ∧
    |uniformMix m (-1) k - (((m : ℝ) - 2) / 2) * ((k : ℝ) / (m : ℝ))| ≤ 0 := by
  have h3 := uniformMix_heavy m k hm hk1 hk
  have h1 := uniformMix_light m k hm hk1 hk
  have hs3 : uniformMix m (-3) k = uniformMix m 3 k := (uniformMix_symm m 3 k).symm
  have hs1 : uniformMix m (-1) k = uniformMix m 1 k := (uniformMix_symm m 1 k).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h3, sub_self, abs_zero]
  · rw [hs3, h3, sub_self, abs_zero]
  · rw [h1, sub_self, abs_zero]
  · rw [hs1, h1, sub_self, abs_zero]

/-- **Per-item marginals, from the type counts.**  With the uniform relabelling inside each
weight type -- which is what supplies `hconst` -- every item of a type carries the type's
count divided by the type's multiplicity.  At the counts above that is `k/m` for every item,
which is the `eta = 0` band in its literal per-item form. -/
theorem uniform_marginals_from_relabelling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Grp : Finset ι) (hne : Grp.Nonempty) (marg : ι → ℝ) (mult : ℝ) (m k : ℕ)
    (hmult : ((Grp.card : ℝ)) = mult) (hmult0 : mult ≠ 0)
    (hconst : ∀ i ∈ Grp, ∀ j ∈ Grp, marg i = marg j)
    (hocc : ∑ i ∈ Grp, marg i = mult * ((k : ℝ) / (m : ℝ)))
    (i : ι) (hi : i ∈ Grp) :
    marg i = (k : ℝ) / (m : ℝ) := by
  have h := marginal_eq_occupancy_div_card Grp hne marg (mult * ((k : ℝ) / (m : ℝ)))
    hconst hocc i hi
  rw [h, hmult]
  field_simp

/-! ## Audit -/

#print axioms flatCount_three
#print axioms flatCount_neg_three
#print axioms flatCount_one
#print axioms flatCount_neg_one
#print axioms mixFlat_three
#print axioms mixFlat_neg_three
#print axioms mixFlat_one
#print axioms mixFlat_neg_one
#print axioms uniformMix_heavy
#print axioms uniformMix_light
#print axioms uniform_band_zero
#print axioms uniform_marginals_from_relabelling

end CIGAMF.P13.PaperCUniform
