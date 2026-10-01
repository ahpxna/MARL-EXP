import «LeanSupportMultiTipGeometryV1»

/-! Sharp deterministic membership decision-tree cost in actual support geometry.
Dense supports (all tips but one) have pairwise incompatible safe decisions,
yet require m-1 queries. This contrasts with the one-query sparse family whose
minimal bad fibre has size m. Queries here are individual tip memberships. -/
namespace CIGAMF.P13.SupportAdaptiveQuerySeparation
open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportUnboundedObstruction (tip)
open CIGAMF.P13.SupportMultiTipGeometry
noncomputable section
variable {m : ℕ}

inductive Tree (m : ℕ) where
  | leaf : Fin m → Tree m
  | ask : Fin m → Tree m → Tree m → Tree m

def depth : Tree m → ℕ
  | .leaf _ => 0
  | .ask _ no yes => max (depth no) (depth yes)+1

def run (oracle : Fin m → Bool) : Tree m → Fin m
  | .leaf j => j
  | .ask a no yes => if oracle a then run oracle yes else run oracle no

def positiveQueries : Tree m → Finset (Fin m)
  | .leaf _ => ∅
  | .ask a _ yes => insert a (positiveQueries yes)

def positiveOutput : Tree m → Fin m
  | .leaf j => j
  | .ask _ _ yes => positiveOutput yes

def oracle (w a : Fin m) : Bool := decide (tip a ∈ support (univ.erase w))

lemma oracle_formula (hm : 2 ≤ m) (w a : Fin m) : oracle w a = decide (a ≠ w) := by
  simp [oracle,physical_membership_iff hm]

lemma positive_card_le_depth (t : Tree m) : (positiveQueries t).card ≤ depth t := by
  induction t with
  | leaf j => simp [positiveQueries,depth]
  | ask a no yes ihno ihyes =>
    change (insert a (positiveQueries yes)).card ≤ max (depth no) (depth yes)+1
    have h := card_insert_le a (positiveQueries yes)
    have hh := le_max_right (depth no) (depth yes)
    omega

lemma run_positive (hm : 2 ≤ m) (t : Tree m) (w : Fin m)
    (hw : w ∉ positiveQueries t) : run (oracle w) t = positiveOutput t := by
  induction t with
  | leaf j => rfl
  | ask a no yes ihno ihyes =>
    have ha : a ≠ w := by
      intro h; subst a
      exact hw (mem_insert_self _ _)
    have hy : w ∉ positiveQueries yes := by
      intro h; exact hw (mem_insert_of_mem h)
    simpa [run,oracle_formula hm,ha,positiveOutput] using ihyes hy

/-- Covers every deterministic adaptive finite tree, not merely a fixed batch
of queries: follow its all-positive branch and charge the remaining hole. -/
theorem adaptive_depth_lower (hm : 2 ≤ m) (t : Tree m)
    (hsound : ∀ w : Fin m,
      selectedRadius (components (univ.erase w)) {run (oracle w) t}=0) :
    m-1 ≤ depth t := by
  have hcover : (univ : Finset (Fin m)) ⊆ insert (positiveOutput t) (positiveQueries t) := by
    intro w _
    by_cases hw : w ∈ positiveQueries t
    · exact mem_insert_of_mem hw
    · have h := hsound w
      rw [run_positive hm t w hw] at h
      have he := (dense_unique_safe hm w (positiveOutput t)).mp h
      exact mem_insert.mpr (Or.inl he.symm)
  have hcard := card_le_card hcover
  have hset := card_insert_le (positiveOutput t) (positiveQueries t)
  have hdep := positive_card_le_depth t
  simp only [card_univ,Fintype.card_fin] at hcard
  omega

def search (fallback : Fin m) : List (Fin m) → Tree m
  | [] => .leaf fallback
  | a::rest => .ask a (.leaf a) (search fallback rest)

lemma depth_search (fallback : Fin m) (xs : List (Fin m)) :
    depth (search fallback xs)=xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [search,depth,ih]

lemma search_correct (hm : 2 ≤ m) (fallback w : Fin m) (xs : List (Fin m))
    (hw : w ∈ xs ∨ w=fallback) : run (oracle w) (search fallback xs)=w := by
  induction xs with
  | nil => simpa [search,run] using (hw.resolve_left (by simp)).symm
  | cons a xs ih =>
    by_cases h : a=w
    · subst a; simp [search,run,oracle_formula hm]
    · have htail : w ∈ xs ∨ w=fallback := by
        simpa [List.mem_cons,Ne.symm h] using hw
      simpa [search,run,oracle_formula hm,h] using ih htail

theorem adaptive_depth_attained (hm : 2 ≤ m) (fallback : Fin m) :
    ∃ t : Tree m, depth t=m-1 ∧ ∀ w : Fin m,
      selectedRadius (components (univ.erase w)) {run (oracle w) t}=0 := by
  let xs := (univ.erase fallback).toList
  refine ⟨search fallback xs,?_,?_⟩
  · simp [depth_search,xs]
  · intro w
    have hw : w ∈ xs ∨ w=fallback := by
      by_cases h : w=fallback
      · exact Or.inr h
      · exact Or.inl (by simp [xs,h])
    rw [search_correct hm fallback w xs hw]
    exact (dense_unique_safe hm w w).mpr rfl

#print axioms adaptive_depth_lower
#print axioms adaptive_depth_attained
end
end CIGAMF.P13.SupportAdaptiveQuerySeparation
