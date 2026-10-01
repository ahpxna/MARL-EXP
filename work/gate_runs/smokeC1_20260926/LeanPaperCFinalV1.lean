import «LeanPaperCBreakpointV1»

/-!
# Paper C, C-FINAL: `hsec` discharged at the actual graph, and the strict gap

`pathDecomposition_discharged` closed E3 *given* a section `sec` taking a positive-mass
trajectory to a ranking that realises it.  That hypothesis carried the content, so this
module removes it.  The state space is the count vector, the ranking space is the
permutations of the items, the group is the type-preserving subgroup, and the section is
BUILT -- from `hsec_count_states` (trajectory to type sequence) composed with `matchPerm`
(type sequence to permutation).  `pathDecomposition_count_states` has no `hsec`.

The second half removes a separate gap the manuscript admitted: it said the lower side and
attainment were theorems at every `m`, yet also said the strict gap below the breakpoint
was open.  On a compact feasible set those are the same statement.  A continuous value
attains its minimum, so "no feasible distribution achieves `V_free`" upgrades at once to a
positive, uniform margin.  No further census is needed, and none is run.
-/


namespace CIGAMF.P13.CFinal

open Finset
open CIGAMF.P13.PaperCBreakpoint

variable {d m : ℕ}

/-! ### The group that preserves item types -/

/-- Permutations of the items that never move an item to a position of a different type.
This is the group the reduction may symmetrise over: it is exactly the redundancy the
count-state graph forgets. -/
def TypeStab (ty : Fin m → Fin d) : Subgroup (Equiv.Perm (Fin m)) where
  carrier := {g | ∀ j, ty (g j) = ty j}
  mul_mem' := by
    intro a b ha hb j
    simp only [Equiv.Perm.mul_apply]
    rw [ha, hb]
  one_mem' := by intro j; rfl
  inv_mem' := by
    intro a ha j
    have h := ha (a⁻¹ j)
    have hj : a (a⁻¹ j) = j := by
      change (a * a⁻¹) j = j
      rw [mul_inv_cancel]; rfl
    rw [hj] at h
    exact h.symm

noncomputable instance instFintypeTypeStab (ty : Fin m → Fin d) :
    Fintype (TypeStab ty) := Fintype.ofFinite _

/-! ### The layer map of a ranking, valued in the count states -/

/-- After `i` positions of the ranking `ω`, how many items of each type have been served. -/
def rankLayer (ty : Fin m → Fin d) (i : Fin (m + 1)) (ω : Equiv.Perm (Fin m)) : CState d m :=
  layerState (fun k => ty (ω k)) (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)

/-- **The layer map is invariant under the type-preserving group**, which is the hypothesis
`pathDecomposition_discharged` needs in order to symmetrise. -/
theorem rankLayer_smul (ty : Fin m → Fin d) (g : TypeStab ty) (i : Fin (m + 1))
    (ω : Equiv.Perm (Fin m)) : rankLayer ty i (g • ω) = rankLayer ty i ω := by
  have hg : ∀ j, ty ((g : Equiv.Perm (Fin m)) j) = ty j := g.2
  have hfun : (fun k => ty ((g • ω) k)) = (fun k => ty (ω k)) := by
    funext k
    show ty (((g : Equiv.Perm (Fin m)) * ω) k) = ty (ω k)
    exact hg (ω k)
  unfold rankLayer
  rw [hfun]

/-! ### Multiplicities -/

/-- How many items carry type `τ`. -/
def mult (ty : Fin m → Fin d) (τ : Fin d) : ℕ := (univ.filter (fun j => ty j = τ)).card

theorem card_filter_eq_layerCount (m : ℕ) (s : Fin m → Fin d) (τ : Fin d) :
    (univ.filter (fun k : Fin m => s k = τ)).card = layerCount m s m τ := by
  classical
  rw [layerCount, Finset.card_filter,
      ← Fin.sum_univ_eq_sum_range (fun k => if h : k < m then
        (if s ⟨k, h⟩ = τ then 1 else 0) else 0) m]
  exact Finset.sum_congr rfl (fun k _ => by simp [k.isLt])

/-! ### The section: a positive-mass trajectory IS a ranking -/

/-- **The section exists.**  A trajectory of positive mass that starts empty and ends at the
items' own multiplicities is the layer map of an actual permutation of the items.  This is
`hsec_count_states` (which produces a type SEQUENCE) composed with `matchPerm` (which turns a
type sequence of the right multiplicities into a PERMUTATION). -/
theorem exists_rank_section (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : ∀ k v w, ¬ StepC v w → F.f k v w = 0)
    (t : Fin (m + 1) → CState d m) (ht : F.trajLaw m t ≠ 0)
    (h0 : ∀ τ, ((t 0) τ : ℕ) = 0)
    (hend : ∀ τ, ((t (Fin.last m)) τ : ℕ) = mult ty τ) :
    ∃ ω : Equiv.Perm (Fin m), ∀ i : Fin (m + 1), rankLayer ty i ω = t i := by
  classical
  obtain ⟨s, hs⟩ := hsec_count_states F hF t ht h0
  have hsm : ∀ τ, layerCount m s m τ = mult ty τ := by
    intro τ
    have := congrFun (hs m le_rfl) τ
    have h2 : (layerState s m le_rfl τ : ℕ) = ((t ⟨m, by omega⟩) τ : ℕ) := by
      rw [this]
    have h3 : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
    rw [h3] at h2
    rw [← hend τ, ← h2]
    rfl
  have hcard : ∀ τ, Fintype.card {k : Fin m // s k = τ}
      = Fintype.card {j : Fin m // ty j = τ} := by
    intro τ
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rw [card_filter_eq_layerCount m s τ, hsm τ]
    rfl
  refine ⟨matchPerm m s ty hcard, ?_⟩
  intro i
  have hcomp : (fun k => ty (matchPerm m s ty hcard k)) = s := by
    funext k; exact matchPerm_type m s ty hcard k
  unfold rankLayer
  rw [hcomp]
  have := hs (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)
  rw [this]

/-- The section, as a total function: the choice on positive-mass trajectories, the identity
elsewhere (where its value is never read). -/
noncomputable def countSec (ty : Fin m → Fin d) (_F : LayeredFlow (CState d m))
    (t : Fin (m + 1) → CState d m) : Equiv.Perm (Fin m) :=
  letI : Decidable (∃ ω : Equiv.Perm (Fin m), ∀ i : Fin (m + 1), rankLayer ty i ω = t i) :=
    Classical.dec _
  if h : ∃ ω : Equiv.Perm (Fin m), ∀ i : Fin (m + 1), rankLayer ty i ω = t i
  then h.choose else 1

theorem countSec_layer (ty : Fin m → Fin d) (F : LayeredFlow (CState d m))
    (hF : ∀ k v w, ¬ StepC v w → F.f k v w = 0)
    (t : Fin (m + 1) → CState d m) (ht : F.trajLaw m t ≠ 0)
    (h0 : ∀ τ, ((t 0) τ : ℕ) = 0)
    (hend : ∀ τ, ((t (Fin.last m)) τ : ℕ) = mult ty τ)
    (i : Fin (m + 1)) : rankLayer ty i (countSec ty F t) = t i := by
  classical
  have hex := exists_rank_section ty F hF t ht h0 hend
  unfold countSec
  rw [dif_pos hex]
  exact hex.choose_spec i

/-! ### E3 at the count-state graph, with no `hsec` left -/

/-- The flows the reduction is about: unit mass, supported on legal one-item steps, and
every positive-mass trajectory starts empty and ends at the items' multiplicities. -/
def CountFeasible (ty : Fin m → Fin d) (F : LayeredFlow (CState d m)) : Prop :=
  ((∑ v, F.x 0 v = 1) ∧ ∀ j, ∑ v, F.x (j + 1) v = ∑ v, F.x j v)
  ∧ (∀ k v w, ¬ StepC v w → F.f k v w = 0)
  ∧ (∀ t : Fin (m + 1) → CState d m, F.trajLaw m t ≠ 0 →
       (∀ τ, ((t 0) τ : ℕ) = 0) ∧ (∀ τ, ((t (Fin.last m)) τ : ℕ) = mult ty τ))

/-- **E3, discharged at the actual graph.**

`pathDecomposition_discharged` took the section as a hypothesis.  Here there is no
hypothesis: the state space is the count vector, the ranking space is the permutations of
the items, and the section is built.  Every feasible unit flow is induced by a randomised
ranking with the same value, for every objective linear in the layer marginals. -/
theorem pathDecomposition_count_states (ty : Fin m → Fin d)
    (c : Fin (m + 1) → CState d m → ℝ) :
    PathDecompositionDebt
      (CountFeasible ty)
      (fun (P : Equiv.Perm (Fin m) → ℝ) (F : LayeredFlow (CState d m)) =>
        (∀ ω, 0 ≤ P ω) ∧ (∑ ω, P ω = 1) ∧
        ∀ (i : Fin (m + 1)) (v : CState d m),
          ∑ ω, P ω * (if rankLayer ty i ω = v then (1 : ℝ) else 0) = F.x (i : ℕ) v)
      (fun F : LayeredFlow (CState d m) =>
        ∑ i : Fin (m + 1), ∑ v : CState d m, c i v * F.x (i : ℕ) v)
      (fun P : Equiv.Perm (Fin m) → ℝ =>
        ∑ ω, P ω * (∑ i : Fin (m + 1), c i (rankLayer ty i ω))) := by
  classical
  rintro F ⟨⟨h0, hcons⟩, hstep, hends⟩
  have hsec : ∀ (t : Fin (m + 1) → CState d m), F.trajLaw m t ≠ 0 →
      ∀ i, rankLayer ty i (countSec ty F t) = t i := by
    intro t ht i
    exact countSec_layer ty F hstep t ht (hends t ht).1 (hends t ht).2 i
  refine ⟨flowRanking (TypeStab ty) m F (countSec ty F), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun ω => flowRanking_nonneg (TypeStab ty) m F (countSec ty F) ω
  · exact flowRanking_sum (TypeStab ty) m F (countSec ty F) h0 hcons
  · exact fun i v => flowRanking_marginal (TypeStab ty) m F (rankLayer ty)
      (fun g i ω => rankLayer_smul ty g i ω) (countSec ty F) hsec i v
  · exact linear_objective_from_marginals m F (rankLayer ty)
      (flowRanking (TypeStab ty) m F (countSec ty F)) c
      (fun i v => flowRanking_marginal (TypeStab ty) m F (rankLayer ty)
        (fun g i ω => rankLayer_smul ty g i ω) (countSec ty F) hsec i v)

/-! ### Strict gap below the breakpoint, from attainment -/

/-- **No attainment upgrades to a strict, uniform gap.**  On a compact feasible set a
continuous value attains its minimum, so "no feasible point achieves the free value"
is not merely a non-equality: there is a positive margin, uniform over the set.  This is
the step that turns the lower side into `V_m(eta) > V_free` below the breakpoint, with no
further census. -/
theorem strict_gap_of_compact {α : Type*} [TopologicalSpace α]
    (S : Set α) (hS : IsCompact S) (hne : S.Nonempty)
    (V : α → ℝ) (hV : ContinuousOn V S) (Vfree : ℝ)
    (hge : ∀ p ∈ S, Vfree ≤ V p) (hno : ∀ p ∈ S, V p ≠ Vfree) :
    ∃ ε > 0, ∀ p ∈ S, Vfree + ε ≤ V p := by
  obtain ⟨p0, hp0S, hp0⟩ := hS.exists_isMinOn hne hV
  refine ⟨V p0 - Vfree, by
    have := hge p0 hp0S
    have hne' := hno p0 hp0S
    cases lt_or_eq_of_le this with
    | inl h => linarith
    | inr h => exact absurd h.symm hne', ?_⟩
  intro p hp
  have : V p0 ≤ V p := hp0 hp
  linarith

/-- The simplex of randomised rankings is compact and nonempty. -/
theorem simplex_compact_nonempty (n : ℕ) (hn : 0 < n) :
    IsCompact (stdSimplex ℝ (Fin n)) ∧ (stdSimplex ℝ (Fin n)).Nonempty := by
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  refine ⟨isCompact_stdSimplex .., ⟨fun _ => 1 / (n : ℝ), ?_, ?_⟩⟩
  · intro i; positivity
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- **Strict gap on the BAND-FEASIBLE set.**

An earlier version of this theorem quantified over the whole simplex.  That was a mistake
and it is corrected here rather than quietly dropped: if `Vfree` is the free optimum, it is
*attained* somewhere on the full simplex, so `forall P in simplex, V P <> Vfree` cannot
hold and the theorem was vacuous exactly where Paper C wanted to use it.  The right domain
is the band-feasible subset `F`, which is closed inside the simplex and therefore compact,
and on which `Vfree` is genuinely unattained below the breakpoint. -/
theorem breakpoint_strict_below (n : ℕ) (hn : 0 < n)
    (F : Set (Fin n → ℝ)) (hFsub : F ⊆ stdSimplex ℝ (Fin n))
    (hFclosed : IsClosed F) (hFne : F.Nonempty)
    (V : (Fin n → ℝ) → ℝ) (hV : Continuous V) (Vfree : ℝ)
    (hge : ∀ p ∈ F, Vfree ≤ V p) (hno : ∀ p ∈ F, V p ≠ Vfree) :
    ∃ ε > 0, ∀ p ∈ F, Vfree + ε ≤ V p := by
  obtain ⟨hc, -⟩ := simplex_compact_nonempty n hn
  have hFc : IsCompact F := hc.of_isClosed_subset hFclosed hFsub
  exact strict_gap_of_compact F hFc hFne V hV.continuousOn Vfree hge hno

/-- **The hypotheses are satisfiable**, which is the point the corrected domain makes:
they hold exactly when `Vfree` sits strictly below the constrained minimum, and fail when
`Vfree` is the value attained on the set itself.  Here `F` is the whole (one-point)
simplex, `V` is constantly one and `Vfree` is zero. -/
theorem breakpoint_strict_below_nonvacuous :
    ∃ ε > 0, ∀ p ∈ stdSimplex ℝ (Fin 1), (0 : ℝ) + ε ≤ (fun _ => (1 : ℝ)) p := by
  refine breakpoint_strict_below 1 one_pos (stdSimplex ℝ (Fin 1)) (subset_refl _)
    (isCompact_stdSimplex ..).isClosed ?_ (fun _ => (1 : ℝ)) continuous_const 0
    (fun p _ => by norm_num) (fun p _ => by norm_num)
  exact (simplex_compact_nonempty 1 one_pos).2

/-! ## Audit -/

#print axioms rankLayer_smul
#print axioms card_filter_eq_layerCount
#print axioms exists_rank_section
#print axioms countSec_layer
#print axioms pathDecomposition_count_states
#print axioms strict_gap_of_compact
#print axioms simplex_compact_nonempty
#print axioms breakpoint_strict_below
#print axioms breakpoint_strict_below_nonvacuous

end CIGAMF.P13.CFinal
