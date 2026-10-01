import «LeanSupportCardinalityQueryLawV1»

/-! # U03: obstruction order does not determine query cost, in either direction

The two constructions and the two query laws are already proved upstream. What
is added here is a single definition of obstruction that both families are
measured against, so the comparison is a theorem rather than a remark in two
docstrings.

## The definition

A decision is a retained singleton `{j}`. It is SAFE for a world whose support
is `W` when `selectedRadius (components W) {j} = 0` — the exact zero-radius
notion already used throughout the Support modules, not a new surrogate. A set
of worlds is UNSAFE when no single decision is safe for all of them, and an
OBSTRUCTION is an unsafe set that is minimal FOR INCLUSION.

Minimality for inclusion matters. Exhibiting one unsafe set and calling its size
the obstruction order proves nothing about the family; the theorems below
characterise EVERY minimal obstruction of each family, so the order is a
property of the geometry rather than of a chosen witness.

## The two families, under one query primitive

| family | support of world `w` | every minimal obstruction | optimal query depth |
|---|---|---:|---:|
| sparse | `{w}` | `m` worlds | `1` |
| dense | `univ.erase w` | `2` worlds | `m - 1` |

`same_query_primitive` proves the two families are driven by the SAME physical
membership query: `SupportAdaptiveQuerySeparation.oracle w` is literally
`SupportCardinalityQueryLaw.oracle (denseSup w)`. Without that the comparison
would be between two different oracles and would show nothing.

## The conclusion

`obstruction_two_with_query_depth_gt` — a family whose every obstruction has
exactly two worlds can need arbitrarily many queries. So obstruction order gives
no upper bound on cost.

`obstruction_large_with_query_depth_one` — a family whose obstruction has
arbitrarily many worlds can be decided in one query. So obstruction order
supports no lower bound that grows with it. A lower bound still exists, and is
proved: `sparse_query_depth_lower` shows one query is necessary. What is refuted
is `depth ≥ g(obstruction order)` for unbounded `g`, in either direction.

Helly-type numbers therefore cannot serve as the complexity parameter for this
model on their own; the query structure has to enter. That is the U04 target and
is NOT attempted here.

## Limits kept

Deterministic adaptive zero-error trees, cost measured as worst-case depth. No
noisy queries, no randomised or expected cost, no stopping rules. The `1/2`
normalized-tolerance result of the sparse family lives in
`LeanSupportUnboundedObstructionV1` and is NOT transported to the dense family.
-/

namespace CIGAMF.P13.SupportObstructionQueryOrder
open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportUnboundedObstruction (tip)
open CIGAMF.P13.SupportMultiTipGeometry
open CIGAMF.P13.SupportAdaptiveQuerySeparation (Tree depth run)
noncomputable section
variable {m : ℕ}

/-! ## Families, safety, obstruction -/

/-- A family presents each world index with the support that world carries. -/
def CommonSafe (sup : Fin m → Finset (Fin m)) (W : Finset (Fin m)) : Prop :=
  ∃ j : Fin m, ∀ w ∈ W, selectedRadius (components (sup w)) {j} = 0

def Unsafe (sup : Fin m → Finset (Fin m)) (W : Finset (Fin m)) : Prop :=
  ¬ CommonSafe sup W

/-- An obstruction: unsafe, and minimal for inclusion. -/
def MinimalObstruction (sup : Fin m → Finset (Fin m)) (W : Finset (Fin m)) : Prop :=
  Unsafe sup W ∧ ∀ V ⊂ W, CommonSafe sup V

abbrev sparseSup (w : Fin m) : Finset (Fin m) := {w}
abbrev denseSup (w : Fin m) : Finset (Fin m) := univ.erase w

/-- Safety in the sparse family is exactly `j ≠ w`. Stated as a Prop about
indices so that no later proof has to rewrite underneath `components`, whose
`Points` index type DEPENDS on the support set: rewriting there makes the
motive ill-typed. Every use below goes through this lemma. -/
theorem sparse_safe_iff (hm : 2 ≤ m) (w j : Fin m) :
    selectedRadius (components (sparseSup w)) {j} = 0 ↔ j ≠ w := by
  constructor
  · intro h hjw
    exact ((zero_radius_iff hm ({w} : Finset (Fin m)) j).mp h) (by simp [hjw])
  · intro h
    exact (zero_radius_iff hm ({w} : Finset (Fin m)) j).mpr (by simp [h])

/-- Safety in the dense family is exactly `j = w`. -/
theorem dense_safe_iff (hm : 2 ≤ m) (w j : Fin m) :
    selectedRadius (components (denseSup w)) {j} = 0 ↔ j = w :=
  dense_unique_safe hm w j

/-- Both families are driven by the same physical membership query. -/
theorem same_query_primitive (w : Fin m) :
    CIGAMF.P13.SupportAdaptiveQuerySeparation.oracle w
      = CIGAMF.P13.SupportCardinalityQueryLaw.oracle (denseSup w) := rfl

/-! ## Sparse family: one obstruction, of size `m` -/

theorem sparse_commonSafe_iff (hm : 2 ≤ m) (W : Finset (Fin m)) :
    CommonSafe sparseSup W ↔ W ≠ univ := by
  classical
  constructor
  · rintro ⟨j, hj⟩ hW
    have hjW : j ∈ W := by rw [hW]; exact mem_univ j
    exact ((sparse_safe_iff hm j j).mp (hj j hjW)) rfl
  · intro hW
    have hex : ∃ j : Fin m, j ∉ W := by
      by_contra hc
      push_neg at hc
      exact hW (eq_univ_iff_forall.mpr hc)
    obtain ⟨j, hj⟩ := hex
    refine ⟨j, fun w hw => (sparse_safe_iff hm w j).mpr ?_⟩
    rintro rfl
    exact hj hw

theorem sparse_unsafe_iff (hm : 2 ≤ m) (W : Finset (Fin m)) :
    Unsafe sparseSup W ↔ W = univ := by
  unfold Unsafe
  rw [sparse_commonSafe_iff hm]
  exact not_not

/-- Every minimal obstruction of the sparse family is the whole world set. -/
theorem sparse_minimalObstruction_iff (hm : 2 ≤ m) (W : Finset (Fin m)) :
    MinimalObstruction sparseSup W ↔ W = univ := by
  constructor
  · rintro ⟨hU, -⟩
    exact (sparse_unsafe_iff hm W).mp hU
  · rintro rfl
    refine ⟨(sparse_unsafe_iff hm _).mpr rfl, ?_⟩
    intro V hV
    exact (sparse_commonSafe_iff hm V).mpr (ne_of_lt hV)

theorem sparse_obstruction_card (hm : 2 ≤ m) (W : Finset (Fin m))
    (h : MinimalObstruction sparseSup W) : W.card = m := by
  rw [(sparse_minimalObstruction_iff hm W).mp h]
  simp

/-! ## Sparse family: one query, and one is necessary -/

theorem sparse_query_depth_attained (hm : 2 ≤ m) (hm1 : 1 < m) (fallback : Fin m) :
    ∃ t : Tree m, depth t = 1 ∧ ∀ w : Fin m,
      selectedRadius (components (sparseSup w))
        {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle (sparseSup w)) t} = 0 := by
  obtain ⟨t, hd, hs⟩ :=
    CIGAMF.P13.SupportCardinalityQueryLaw.adaptive_cardinality_attained hm 1 hm1 fallback
  exact ⟨t, hd, fun w => hs (sparseSup w) (by simp)⟩

theorem sparse_query_depth_lower (hm : 2 ≤ m) (hm1 : 1 < m) (t : Tree m)
    (hsound : ∀ w : Fin m,
      selectedRadius (components (sparseSup w))
        {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle (sparseSup w)) t} = 0) :
    1 ≤ depth t := by
  classical
  apply CIGAMF.P13.SupportCardinalityQueryLaw.adaptive_cardinality_lower hm 1 hm1 t
  intro W hW
  obtain ⟨w, rfl⟩ := card_eq_one.mp hW
  exact hsound w

/-! ## Dense family: every obstruction has exactly two worlds -/

theorem dense_commonSafe_iff (hm : 2 ≤ m) (W : Finset (Fin m)) :
    CommonSafe denseSup W ↔ W.card ≤ 1 := by
  classical
  constructor
  · rintro ⟨j, hj⟩
    have hsub : W ⊆ {j} := by
      intro w hw
      rw [mem_singleton]
      exact ((dense_safe_iff hm w j).mp (hj w hw)).symm
    calc W.card ≤ ({j} : Finset (Fin m)).card := card_le_card hsub
      _ = 1 := card_singleton j
  · intro hW
    rcases Finset.eq_empty_or_nonempty W with rfl|⟨w, hw⟩
    · have hne : 0 < m := by omega
      exact ⟨⟨0, hne⟩, by simp⟩
    · refine ⟨w, ?_⟩
      intro x hx
      have hxw : x = w := card_le_one.mp hW x hx w hw
      subst hxw
      exact (dense_safe_iff hm x x).mpr rfl

theorem dense_unsafe_iff (hm : 2 ≤ m) (W : Finset (Fin m)) :
    Unsafe denseSup W ↔ 2 ≤ W.card := by
  unfold Unsafe
  rw [dense_commonSafe_iff hm]
  omega

/-- Every minimal obstruction of the dense family has exactly two worlds. -/
theorem dense_minimalObstruction_iff (hm : 2 ≤ m) (W : Finset (Fin m)) :
    MinimalObstruction denseSup W ↔ W.card = 2 := by
  classical
  constructor
  · rintro ⟨hU, hMin⟩
    have hge : 2 ≤ W.card := (dense_unsafe_iff hm W).mp hU
    by_contra hne
    have hgt : 2 < W.card := by omega
    obtain ⟨V, hVsub, hVcard⟩ := W.exists_subset_card_eq (show 2 ≤ W.card by omega)
    have hVne : V ≠ W := by
      intro h; rw [h] at hVcard; omega
    have hVss : V ⊂ W := Finset.ssubset_iff_subset_ne.mpr ⟨hVsub, hVne⟩
    have hsafe := hMin V hVss
    rw [dense_commonSafe_iff hm] at hsafe
    omega
  · intro hW
    refine ⟨(dense_unsafe_iff hm W).mpr (by omega), ?_⟩
    intro V hV
    rw [dense_commonSafe_iff hm]
    have := card_lt_card hV
    omega

/-! ## Dense family: `m - 1` queries, necessary and attained -/

theorem dense_query_depth_lower (hm : 2 ≤ m) (t : Tree m)
    (hsound : ∀ w : Fin m,
      selectedRadius (components (denseSup w))
        {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle (denseSup w)) t} = 0) :
    m-1 ≤ depth t :=
  -- `denseSup w` is `univ.erase w` and `SupportCardinalityQueryLaw.oracle
  -- (denseSup w)` is `SupportAdaptiveQuerySeparation.oracle w`, both by `rfl`
  -- (`same_query_primitive`), so this is the upstream lemma up to defeq.
  CIGAMF.P13.SupportAdaptiveQuerySeparation.adaptive_depth_lower hm t
    (fun w => hsound w)

theorem dense_query_depth_attained (hm : 2 ≤ m) (fallback : Fin m) :
    ∃ t : Tree m, depth t = m-1 ∧ ∀ w : Fin m,
      selectedRadius (components (denseSup w))
        {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle (denseSup w)) t} = 0 := by
  obtain ⟨t, hd, hs⟩ :=
    CIGAMF.P13.SupportAdaptiveQuerySeparation.adaptive_depth_attained hm fallback
  exact ⟨t, hd, fun w => hs w⟩

/-! ## U03: obstruction order bounds query cost in neither direction -/

/-- Obstruction order gives no UPPER bound on query cost: for every `K` there is
a family whose every minimal obstruction has exactly two worlds and which still
needs more than `K` queries. -/
theorem obstruction_two_with_query_depth_gt (K : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧
      (∀ W : Finset (Fin m), MinimalObstruction denseSup W ↔ W.card = 2) ∧
      (∀ t : Tree m,
        (∀ w : Fin m,
          selectedRadius (components (denseSup w))
            {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle (denseSup w)) t} = 0) →
        K < depth t) := by
  refine ⟨K+2, by omega, fun W => dense_minimalObstruction_iff (by omega) W, ?_⟩
  intro t hsound
  have h := dense_query_depth_lower (m := K+2) (by omega) t hsound
  omega

/-- And no lower bound that GROWS with obstruction order: for every `K` there is
a family whose minimal obstruction has more than `K` worlds and which is still
decided in a single query.

Stated this way on purpose. It does not say query cost has no lower bound at
all — one query is always needed here, and `sparse_query_depth_lower` proves
exactly that. What fails is any bound of the form `depth ≥ g(obstruction order)`
with `g` unbounded. -/
theorem obstruction_large_with_query_depth_one (K : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧
      (∀ W : Finset (Fin m), MinimalObstruction sparseSup W ↔ W = univ) ∧
      K < m ∧
      ∃ t : Tree m, depth t = 1 ∧ ∀ w : Fin m,
        selectedRadius (components (sparseSup w))
          {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle (sparseSup w)) t} = 0 := by
  refine ⟨K+2, by omega, fun W => sparse_minimalObstruction_iff (by omega) W, by omega, ?_⟩
  exact sparse_query_depth_attained (by omega) (by omega) ⟨0, by omega⟩

/-- U03, both directions in one statement. -/
theorem obstruction_order_determines_neither_bound :
    (∀ K : ℕ, ∃ m : ℕ, 2 ≤ m ∧
      (∀ W : Finset (Fin m), MinimalObstruction denseSup W ↔ W.card = 2) ∧
      (∀ t : Tree m,
        (∀ w : Fin m,
          selectedRadius (components (denseSup w))
            {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle (denseSup w)) t} = 0) →
        K < depth t))
    ∧ (∀ K : ℕ, ∃ m : ℕ, 2 ≤ m ∧
      (∀ W : Finset (Fin m), MinimalObstruction sparseSup W ↔ W = univ) ∧
      K < m ∧
      ∃ t : Tree m, depth t = 1 ∧ ∀ w : Fin m,
        selectedRadius (components (sparseSup w))
          {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle (sparseSup w)) t} = 0) :=
  ⟨obstruction_two_with_query_depth_gt, obstruction_large_with_query_depth_one⟩

#print axioms same_query_primitive
#print axioms sparse_safe_iff
#print axioms dense_safe_iff
#print axioms sparse_commonSafe_iff
#print axioms sparse_unsafe_iff
#print axioms sparse_minimalObstruction_iff
#print axioms sparse_obstruction_card
#print axioms sparse_query_depth_attained
#print axioms sparse_query_depth_lower
#print axioms dense_commonSafe_iff
#print axioms dense_unsafe_iff
#print axioms dense_minimalObstruction_iff
#print axioms dense_query_depth_lower
#print axioms dense_query_depth_attained
#print axioms obstruction_two_with_query_depth_gt
#print axioms obstruction_large_with_query_depth_one
#print axioms obstruction_order_determines_neither_bound

end
end CIGAMF.P13.SupportObstructionQueryOrder
