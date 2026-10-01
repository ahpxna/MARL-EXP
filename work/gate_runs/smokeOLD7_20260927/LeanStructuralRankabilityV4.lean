import Mathlib
import «LeanSupportGeometryV4»

/-! The proved structural implication; characterization work remains separate. -/

namespace CIGAMF.V4.StructuralRankability

open SupportGeometry

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
variable [Fintype ι] [DecidableEq ι]

def GloballyCoextremizable (f : ι → Ω → ℝ) : Prop :=
  ∃ amax amin : Ω,
    (∀ j, f j amax = componentMax f j) ∧
    (∀ j, f j amin = componentMin f j)

def AllSubsetsModular (f : ι → Ω → ℝ) : Prop :=
  ∀ T : Finset ι, supportOsc T f = modularSpan T f

theorem S1_global_coextremizable_implies_all_subsets_modular
    (f : ι → Ω → ℝ) :
    GloballyCoextremizable f → AllSubsetsModular f := by
  rintro ⟨amax, amin, hmax, hmin⟩ T
  exact BH4_coextremizable_exactness T f amax amin
    (fun j _ => hmax j) (fun j _ => hmin j)

/- A scalar-prefix ranking is one fixed duplicate-free list containing every
index.  Budget-k candidates are prefixes of that same list. -/
def IsFullRanking (ranking : List ι) : Prop :=
  ranking.Nodup ∧ ranking.toFinset = Finset.univ

def prefixSet (ranking : List ι) (k : Nat) : Finset ι :=
  (ranking.take k).toFinset

theorem prefixSet_nested (ranking : List ι) (k : Nat) :
    prefixSet ranking k ⊆ prefixSet ranking (k + 1) := by
  intro x hx
  have hp : ranking.take k <+: ranking.take (k + 1) :=
    List.take_prefix_take_left (Nat.le_succ k)
  have hxList : x ∈ ranking.take k := by simpa [prefixSet] using hx
  have : x ∈ ranking.take (k + 1) := hp.subset hxList
  simpa [prefixSet] using this

def TopCExactAllBudgets (objective : Finset ι → ℝ)
    (topC : Nat → Finset ι) : Prop :=
  ∀ k, k ≤ Fintype.card ι → ∀ S, S.card = k → objective (topC k) ≤ objective S

def ScalarPrefixRankable (objective : Finset ι → ℝ) : Prop :=
  ∃ ranking : List ι, IsFullRanking ranking ∧
    ∀ k, k ≤ Fintype.card ι → ∀ S, S.card = k →
      objective (prefixSet ranking k) ≤ objective S

theorem S1_topC_exact_implies_scalar_prefix
    (objective : Finset ι → ℝ) (topC : Nat → Finset ι)
    (ranking : List ι) (hfull : IsFullRanking ranking)
    (hprefix : ∀ k, topC k = prefixSet ranking k)
    (hExact : TopCExactAllBudgets objective topC) :
    ScalarPrefixRankable objective := by
  refine ⟨ranking, hfull, ?_⟩
  intro k hk S hcard
  rw [← hprefix k]
  exact hExact k hk S hcard

end CIGAMF.V4.StructuralRankability
