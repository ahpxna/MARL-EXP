import «LeanSupportCardinalityQueryLawV1»

/-!
# Z1 / PACKAGE 0: is the multi-tip support geometry anything more than a
re-encoding of a general finite decision-region problem?

`LeanSupportMultiTipGeometryV1.radius_formula` says the geometry reads a table:

  `selectedRadius (components W) {j} = ((m-1)/2) * indicator {j ∈ W}`,

and `LeanSupportPhysicalQueryContractV1.physical_membership_iff` says the
physical membership query at coordinate `a` returns the bit `a ∈ W`.  So a world
IS a subset of `Fin m`, safety of decision `j` IS `j ∉ W`, and the query at `a`
IS the bit `a ∈ W`.  The risk this file settles: given ANY finite problem with a
decision set `D`, a binary test set `E` and a world set, encode a world `θ` as

  `W θ = { d ∈ D : d unsafe at θ } ∪ { |D| + e : test e answers 1 at θ }`

and ask whether the encoded geometry instance has the SAME query cost.

## WHAT IS PROVED HERE (all statements below carry a `#print axioms` receipt)

* `safety_faithful`   — for a DECISION coordinate `d`, the real geometric radius
  `selectedRadius (components (encode P θ)) {Fin.castAdd nE d}` is `0` exactly when
  `d` is safe at `θ` in the abstract problem.
* `query_faithful`    — for a TEST coordinate `e`, the physical membership oracle
  of `LeanSupportCardinalityQueryLawV1` returns exactly the abstract test bit.
* `cost_preserving`   — THE MAIN THEOREM.  The set of achievable depths of correct
  adaptive strategies for the abstract problem equals the set of achievable depths
  of correct adaptive membership-query trees for the encoded geometry instance,
  RESTRICTED to trees that only query TEST coordinates and only output DECISION
  coordinates.  The reduction is therefore exactly cost-preserving, in both
  directions, with no slack: `embed` is a depth-preserving bijection between the
  two strategy classes (`embed_restricted`, `exists_embed_of_restricted`).
* `decision_restriction_necessary` — the restriction on the ALLOWED DECISION SET
  cannot be dropped.  An explicit two-world problem (`badDecision`) needs at least
  one test, but the UNRESTRICTED encoded geometry solves it with ZERO queries by
  selecting an auxiliary test coordinate that is absent from every world.
* `query_restriction_necessary` — the restriction on the ALLOWED QUERY SET cannot
  be dropped.  An explicit two-world problem with NO tests at all (`noTest`) has NO
  correct strategy whatsoever, while the UNRESTRICTED encoded geometry solves it
  with ONE query, because querying a DECISION coordinate is a direct safety oracle.
* `outputs_card_le`, `incompatible_worlds_lower`, `dense_counting_bound` — the
  generic counting bound: a depth-`k` tree has at most `2^k` distinct outputs, so a
  family of pairwise incompatible worlds of size `S` forces depth `≥ log2 S`.  For
  the dense family this gives only `m ≤ 2^depth`, whereas the membership primitive
  actually forces `depth ≥ m-1` (`CardinalityQueryLaw.adaptive_cardinality_lower`).
  The exponential gap between those two bounds is the whole content of "the query
  primitive is fixed".
* `unrestricted_exact_cost` — re-export: on the UNRESTRICTED geometry the exact
  zero-error adaptive query complexity of the promise `W.card ≤ s` is exactly `s`.

## VERDICT (stated plainly, as the supervisor asked)

The reduction HOLDS, and is exactly cost-preserving, PROVIDED both the allowed
decision set and the allowed query set are restricted to disjoint coordinate
blocks.  Consequently the class {multi-tip support geometry + physical membership
queries + a restricted decision/query set} is the SAME class as {finite
decision-region determination}, at the same query cost.  Adding one more witness
to `selectedRadius` is then a realization of an already-known problem — the
Decision Region Determination problem of Javdani, Chen, Karbasi, Krause, Bagnell
and Srinivasa, "Near Optimal Bayesian Active Learning for Decision Making",
AISTATS 2014 (and its `EC2` ancestor, Golovin-Krause-Ray 2010) — and confers no
theoretical advantage from the geometry.

If instead the restrictions are DROPPED, the geometry is not the general problem
either: it is strictly EASIER, because the query at coordinate `j` is literally the
safety test of decision `j`.  Its exact complexity is already known and pinned:
`s` queries for the promise `W.card ≤ s` (`unrestricted_exact_cost`).  There is no
residual hardness to discover.

## WHAT THIS DOES NOT ESTABLISH

- Nothing here is about statistical/sample cost, noise, or randomized strategies.
  `dCost`/`GeomCorrect` are ZERO-ERROR worst-case DETERMINISTIC depth.  The
  reduction is not claimed to preserve expected cost under a prior, nor
  approximation ratios of greedy policies, nor randomized-tree cost.
- The abstract problem is finite and its tests are BINARY and NOISELESS.  Nothing
  is claimed for many-valued tests, noisy tests, or infinite world sets.
- `cost_preserving` is an equality of SETS OF ACHIEVABLE DEPTHS, not a statement
  that an optimum exists; no `IsLeast` claim is made here (the sets may be empty,
  which is exactly what happens in `query_restriction_necessary`).
- The encoding inflates the coordinate count from `nD` to `nD+nE`.  Nothing here
  claims a dimension-preserving reduction, and `dense_counting_bound` is only a
  counting bound: no algorithm achieving `log2` many queries is constructed here.
- `incompatible_worlds_lower` assumes PAIRWISE incompatibility (`W ∪ V = univ`).
  It says nothing about families that merely fail to have a single common safe
  decision.
- The second part of the package (which restricted geometries could beat the
  general problem) and the third part (the Bshouty-Feldman 2002 collision with
  reference control) are NOT formalised here; they are argued in
  `research/worker_geometry_reduction_20260913/REPORT.md` and only the counting
  bound above is a Lean receipt.
-/

namespace CIGAMF.P13.SupportGeometryReduction

open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportMultiTipGeometry
open CIGAMF.P13.SupportAdaptiveQuerySeparation (Tree depth run)

noncomputable section

/-! ## The physical membership oracle, re-exported under an unambiguous name -/

/-- `memQuery W a` is the physical membership query of
`LeanSupportCardinalityQueryLawV1`: it asks whether the point `tip a` lies in the
actual support of the world `W`. -/
def memQuery {m : ℕ} (W : Finset (Fin m)) (a : Fin m) : Bool :=
  CIGAMF.P13.SupportCardinalityQueryLaw.oracle W a

lemma memQuery_formula {m : ℕ} (hm : 2 ≤ m) (W : Finset (Fin m)) (a : Fin m) :
    memQuery W a = decide (a ∈ W) :=
  CIGAMF.P13.SupportCardinalityQueryLaw.oracle_formula hm W a

/-! ## A general finite decision-region problem -/

/-- `nW` worlds, `nD` decisions, `nE` binary tests.  `unsafeAt θ d = true` means
decision `d` is unsafe in world `θ`; `testAt θ e` is the (noiseless, binary) answer
of test `e` in world `θ`.  This is the general finite decision-region problem: no
structure whatsoever is imposed on either table. -/
structure DRProblem (nW nD nE : ℕ) where
  unsafeAt : Fin nW → Fin nD → Bool
  testAt : Fin nW → Fin nE → Bool

/-- Adaptive deterministic strategies for a `DRProblem`: query a test, branch on the
answer, and finally output a decision. -/
inductive DTree (nD nE : ℕ) where
  | leaf : Fin nD → DTree nD nE
  | ask : Fin nE → DTree nD nE → DTree nD nE → DTree nD nE

variable {nW nD nE : ℕ}

def dDepth : DTree nD nE → ℕ
  | .leaf _ => 0
  | .ask _ no yes => max (dDepth no) (dDepth yes) + 1

def dRun (ans : Fin nE → Bool) : DTree nD nE → Fin nD
  | .leaf d => d
  | .ask e no yes => if ans e then dRun ans yes else dRun ans no

/-- A strategy is correct when, in EVERY world, the decision it outputs is safe. -/
def DCorrect (P : DRProblem nW nD nE) (t : DTree nD nE) : Prop :=
  ∀ θ : Fin nW, P.unsafeAt θ (dRun (P.testAt θ) t) = false

/-- The set of depths achievable by correct strategies. -/
def dCost (P : DRProblem nW nD nE) : Set ℕ :=
  {k | ∃ t : DTree nD nE, dDepth t = k ∧ DCorrect P t}

lemma dDepth_zero (t : DTree nD nE) (h : dDepth t = 0) : ∃ d, t = DTree.leaf d := by
  cases t with
  | leaf d => exact ⟨d, rfl⟩
  | ask e no yes => simp [dDepth] at h

/-! ## The encoding -/

/-- The world of `θ` as a subset of `Fin (nD+nE)`: the low block records the unsafe
decisions, the high block records the tests answering `1`. -/
def encode (P : DRProblem nW nD nE) (θ : Fin nW) : Finset (Fin (nD + nE)) :=
  ((univ.filter (fun d : Fin nD => P.unsafeAt θ d = true)).image (Fin.castAdd nE))
    ∪ ((univ.filter (fun e : Fin nE => P.testAt θ e = true)).image (Fin.natAdd nD))

lemma mem_encode_castAdd (P : DRProblem nW nD nE) (θ : Fin nW) (d : Fin nD) :
    Fin.castAdd nE d ∈ encode P θ ↔ P.unsafeAt θ d = true := by
  have hd := d.isLt
  simp only [encode, mem_union, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨d', hd', he⟩ | ⟨e, he', he⟩)
    · have hv : (d' : ℕ) = (d : ℕ) := by
        simpa using congrArg Fin.val he
      exact (Fin.ext hv : d' = d) ▸ hd'
    · exfalso
      have hv : nD + (e : ℕ) = (d : ℕ) := by simpa using congrArg Fin.val he
      omega
  · intro h
    exact Or.inl ⟨d, h, rfl⟩

lemma mem_encode_natAdd (P : DRProblem nW nD nE) (θ : Fin nW) (e : Fin nE) :
    Fin.natAdd nD e ∈ encode P θ ↔ P.testAt θ e = true := by
  have he := e.isLt
  simp only [encode, mem_union, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨d, hd, hv⟩ | ⟨e', he', hv⟩)
    · exfalso
      have hdd := d.isLt
      have : (d : ℕ) = nD + (e : ℕ) := by simpa using congrArg Fin.val hv
      omega
    · have hvv : (e' : ℕ) = (e : ℕ) := by
        have : nD + (e' : ℕ) = nD + (e : ℕ) := by simpa using congrArg Fin.val hv
        omega
      exact (Fin.ext hvv : e' = e) ▸ he'
  · intro h
    exact Or.inr ⟨e, h, rfl⟩

/-- FAITHFULNESS OF SAFETY.  The real geometric radius of a decision coordinate
vanishes exactly when the abstract table says the decision is safe. -/
theorem safety_faithful (hm : 2 ≤ nD + nE) (P : DRProblem nW nD nE) (θ : Fin nW)
    (d : Fin nD) :
    selectedRadius (components (encode P θ)) {Fin.castAdd nE d} = 0 ↔
      P.unsafeAt θ d = false := by
  rw [zero_radius_iff hm]
  have hmem := mem_encode_castAdd P θ d
  cases hb : P.unsafeAt θ d with
  | false => simp [hmem, hb]
  | true => simp [hmem, hb]

/-- FAITHFULNESS OF THE QUERY.  The physical membership oracle at a test coordinate
returns exactly the abstract test bit. -/
theorem query_faithful (hm : 2 ≤ nD + nE) (P : DRProblem nW nD nE) (θ : Fin nW)
    (e : Fin nE) :
    memQuery (encode P θ) (Fin.natAdd nD e) = P.testAt θ e := by
  rw [memQuery_formula hm]
  simp [mem_encode_natAdd P θ e]

/-! ## The strategy translation -/

def embed : DTree nD nE → Tree (nD + nE)
  | .leaf d => Tree.leaf (Fin.castAdd nE d)
  | .ask e no yes => Tree.ask (Fin.natAdd nD e) (embed no) (embed yes)

lemma depth_embed (t : DTree nD nE) : depth (embed t) = dDepth t := by
  induction t with
  | leaf d => rfl
  | ask e no yes ihn ihy => simp [embed, depth, dDepth, ihn, ihy]

lemma run_embed (hm : 2 ≤ nD + nE) (P : DRProblem nW nD nE) (θ : Fin nW)
    (t : DTree nD nE) :
    run (memQuery (encode P θ)) (embed t) = Fin.castAdd nE (dRun (P.testAt θ) t) := by
  induction t with
  | leaf d => rfl
  | ask e no yes ihn ihy =>
      show (if memQuery (encode P θ) (Fin.natAdd nD e) then
              run (memQuery (encode P θ)) (embed yes)
            else run (memQuery (encode P θ)) (embed no)) = _
      rw [query_faithful hm P θ e]
      cases hb : P.testAt θ e with
      | true => simpa [dRun, hb] using ihy
      | false => simpa [dRun, hb] using ihn

/-- A geometry tree is ALLOWED for the encoded problem when it only queries TEST
coordinates and only outputs DECISION coordinates.  This is exactly the pair of
restrictions the reduction needs. -/
def IsRestricted : Tree (nD + nE) → Prop
  | .leaf j => (j : ℕ) < nD
  | .ask a no yes => nD ≤ (a : ℕ) ∧ IsRestricted no ∧ IsRestricted yes

lemma embed_restricted (t : DTree nD nE) : IsRestricted (embed t) := by
  induction t with
  | leaf d => simpa [IsRestricted, embed] using d.isLt
  | ask e no yes ihn ihy =>
      refine ⟨by simp [embed], ihn, ihy⟩

lemma exists_embed_of_restricted :
    ∀ t : Tree (nD + nE), IsRestricted t → ∃ s : DTree nD nE, embed s = t := by
  intro t
  induction t with
  | leaf j =>
      intro h
      refine ⟨DTree.leaf ⟨(j : ℕ), h⟩, ?_⟩
      show Tree.leaf (Fin.castAdd nE (⟨(j : ℕ), h⟩ : Fin nD)) = Tree.leaf j
      exact congrArg Tree.leaf (Fin.ext (by simp))
  | ask a no yes ihn ihy =>
      rintro ⟨ha, hn, hy⟩
      obtain ⟨sn, hsn⟩ := ihn hn
      obtain ⟨sy, hsy⟩ := ihy hy
      have halt := a.isLt
      have hlt : (a : ℕ) - nD < nE := by omega
      refine ⟨DTree.ask ⟨(a : ℕ) - nD, hlt⟩ sn sy, ?_⟩
      show Tree.ask (Fin.natAdd nD (⟨(a : ℕ) - nD, hlt⟩ : Fin nE)) (embed sn) (embed sy)
        = Tree.ask a no yes
      have hv : Fin.natAdd nD (⟨(a : ℕ) - nD, hlt⟩ : Fin nE) = a :=
        Fin.ext (by simp; omega)
      rw [hv, hsn, hsy]

/-- Correctness in the encoded geometry, stated with the REAL `selectedRadius`. -/
def GeomCorrect (P : DRProblem nW nD nE) (t : Tree (nD + nE)) : Prop :=
  ∀ θ : Fin nW,
    selectedRadius (components (encode P θ)) {run (memQuery (encode P θ)) t} = 0

theorem correct_iff (hm : 2 ≤ nD + nE) (P : DRProblem nW nD nE) (t : DTree nD nE) :
    DCorrect P t ↔ GeomCorrect P (embed t) := by
  constructor
  · intro h θ
    rw [run_embed hm P θ t]
    exact (safety_faithful hm P θ _).mpr (h θ)
  · intro h θ
    have hθ := h θ
    rw [run_embed hm P θ t] at hθ
    exact (safety_faithful hm P θ _).mp hθ

/-- MAIN THEOREM.  The reduction is EXACTLY COST-PRESERVING: the achievable depths
of correct abstract strategies are exactly the achievable depths of correct
membership-query trees for the encoded geometry instance, over trees restricted to
query test coordinates and to output decision coordinates. -/
theorem cost_preserving (hm : 2 ≤ nD + nE) (P : DRProblem nW nD nE) :
    dCost P
      = {k | ∃ t : Tree (nD + nE), IsRestricted t ∧ depth t = k ∧ GeomCorrect P t} := by
  ext k
  constructor
  · rintro ⟨s, hd, hc⟩
    exact ⟨embed s, embed_restricted s, by rw [depth_embed]; exact hd,
      (correct_iff hm P s).mp hc⟩
  · rintro ⟨t, hr, hd, hc⟩
    obtain ⟨s, rfl⟩ := exists_embed_of_restricted t hr
    exact ⟨s, by rw [← depth_embed]; exact hd, (correct_iff hm P s).mpr hc⟩

/-! ## Both restrictions are necessary -/

/-- Two worlds, two decisions (each safe in exactly one world), two tests: test `0`
reveals the world, test `1` is constantly `0`. -/
def badDecision : DRProblem 2 2 2 where
  unsafeAt := fun θ d => decide ((θ : ℕ) = (d : ℕ))
  testAt := fun θ e => if e = 0 then decide ((θ : ℕ) = 1) else false

/-- THE ALLOWED DECISION SET MATTERS.  `badDecision` admits no zero-query abstract
strategy, but the UNRESTRICTED encoded geometry has a zero-query correct tree: it
simply selects the auxiliary coordinate of the constantly-`0` test, which is absent
from every encoded world and therefore has geometric radius `0` always.  So without
restricting the decision set the reduction does NOT preserve cost. -/
theorem decision_restriction_necessary :
    (0 ∉ dCost badDecision) ∧
      (∃ t : CIGAMF.P13.SupportAdaptiveQuerySeparation.Tree (2 + 2),
        depth t = 0 ∧ GeomCorrect badDecision t) := by
  constructor
  · rintro ⟨t, hd, hc⟩
    obtain ⟨d, rfl⟩ := dDepth_zero t hd
    have h := hc d
    simp [badDecision, dRun] at h
  · refine ⟨Tree.leaf (Fin.natAdd 2 (1 : Fin 2)), rfl, ?_⟩
    intro θ
    have hm : 2 ≤ 2 + 2 := by norm_num
    show selectedRadius (components (encode badDecision θ)) {Fin.natAdd 2 (1 : Fin 2)} = 0
    rw [zero_radius_iff hm]
    rw [mem_encode_natAdd badDecision θ (1 : Fin 2)]
    simp [badDecision]

/-- Two worlds, two decisions, and NO tests at all. -/
def noTest : DRProblem 2 2 0 where
  unsafeAt := fun θ d => decide ((θ : ℕ) = (d : ℕ))
  testAt := fun _ e => e.elim0

/-- THE ALLOWED QUERY SET MATTERS.  `noTest` has NO correct abstract strategy at any
depth, yet the UNRESTRICTED encoded geometry solves it with a single query, because
querying a DECISION coordinate is literally a safety oracle for that decision.  So
without restricting the query set the reduction does NOT preserve cost either. -/
theorem query_restriction_necessary :
    (∀ k, k ∉ dCost noTest) ∧
      (∃ t : CIGAMF.P13.SupportAdaptiveQuerySeparation.Tree (2 + 0),
        depth t = 1 ∧ GeomCorrect noTest t) := by
  have hm : 2 ≤ 2 + 0 := by norm_num
  constructor
  · rintro k ⟨t, -, hc⟩
    cases t with
    | ask e no yes => exact e.elim0
    | leaf d =>
        have h := hc d
        simp [noTest, dRun] at h
  · have hq0 : ∀ θ : Fin 2, (θ : ℕ) = 0 →
        memQuery (encode noTest θ) (Fin.castAdd 0 (0 : Fin 2)) = true := by
      intro θ h
      rw [memQuery_formula hm, decide_eq_true_eq]
      exact (mem_encode_castAdd noTest θ (0 : Fin 2)).mpr (by simp [noTest, h])
    have hq1 : ∀ θ : Fin 2, (θ : ℕ) = 1 →
        memQuery (encode noTest θ) (Fin.castAdd 0 (0 : Fin 2)) = false := by
      intro θ h
      rw [memQuery_formula hm, decide_eq_false_iff_not]
      intro hc
      have hcc := (mem_encode_castAdd noTest θ (0 : Fin 2)).mp hc
      simp [noTest, h] at hcc
    refine ⟨Tree.ask (Fin.castAdd 0 (0 : Fin 2)) (Tree.leaf (Fin.castAdd 0 (0 : Fin 2)))
      (Tree.leaf (Fin.castAdd 0 (1 : Fin 2))), rfl, ?_⟩
    intro θ
    have hθ : (θ : ℕ) = 0 ∨ (θ : ℕ) = 1 := by omega
    show selectedRadius (components (encode noTest θ))
      {if memQuery (encode noTest θ) (Fin.castAdd 0 (0 : Fin 2)) then
        Fin.castAdd 0 (1 : Fin 2) else Fin.castAdd 0 (0 : Fin 2)} = 0
    rcases hθ with h0 | h1
    · rw [hq0 θ h0]
      show selectedRadius (components (encode noTest θ)) {Fin.castAdd 0 (1 : Fin 2)} = 0
      rw [zero_radius_iff hm]
      intro hc
      have hcc := (mem_encode_castAdd noTest θ (1 : Fin 2)).mp hc
      simp [noTest, h0] at hcc
    · rw [hq1 θ h1]
      show selectedRadius (components (encode noTest θ)) {Fin.castAdd 0 (0 : Fin 2)} = 0
      rw [zero_radius_iff hm]
      intro hc
      have hcc := (mem_encode_castAdd noTest θ (0 : Fin 2)).mp hc
      simp [noTest, h1] at hcc

/-! ## What a FIXED query primitive buys: the generic counting bound -/

variable {m : ℕ}

/-- The decisions a tree can possibly output. -/
def outputs : Tree m → Finset (Fin m)
  | .leaf j => {j}
  | .ask _ no yes => outputs no ∪ outputs yes

lemma run_mem_outputs (o : Fin m → Bool) (t : Tree m) : run o t ∈ outputs t := by
  induction t with
  | leaf j => simp [outputs]; rfl
  | ask a no yes ihn ihy =>
      by_cases h : o a = true
      · show (if o a then run o yes else run o no) ∈ outputs no ∪ outputs yes
        rw [if_pos h]
        exact mem_union_right _ ihy
      · show (if o a then run o yes else run o no) ∈ outputs no ∪ outputs yes
        rw [if_neg h]
        exact mem_union_left _ ihn

lemma outputs_card_le (t : Tree m) : (outputs t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf j => simp [outputs, depth]
  | ask a no yes ihn ihy =>
      set M := max (depth no) (depth yes) with hM
      have h1 : (outputs no).card ≤ 2 ^ M :=
        ihn.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : (outputs yes).card ≤ 2 ^ M :=
        ihy.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have hu : (outputs (Tree.ask a no yes)).card ≤ (outputs no).card + (outputs yes).card :=
        card_union_le _ _
      have hpow : (2 : ℕ) ^ (M + 1) = 2 ^ M + 2 ^ M := by rw [pow_succ]; ring
      have hd : depth (Tree.ask a no yes) = M + 1 := rfl
      rw [hd, hpow]
      omega

/-- GENERIC LOWER BOUND.  If every two distinct worlds of a family share NO safe
decision, then a correct tree must output a different decision on each of them, and
a depth-`k` tree has at most `2^k` outputs. -/
theorem incompatible_worlds_lower (hm : 2 ≤ m) (fam : Finset (Finset (Fin m)))
    (hpair : ∀ W ∈ fam, ∀ V ∈ fam, W ≠ V → W ∪ V = univ) (t : Tree m)
    (hsound : ∀ W ∈ fam, selectedRadius (components W) {run (memQuery W) t} = 0) :
    fam.card ≤ 2 ^ depth t := by
  have hinj : ∀ W ∈ fam, ∀ V ∈ fam,
      run (memQuery W) t = run (memQuery V) t → W = V := by
    intro W hW V hV heq
    by_contra hne
    have hWs : run (memQuery W) t ∉ W := (zero_radius_iff hm W _).mp (hsound W hW)
    have hVs : run (memQuery V) t ∉ V := (zero_radius_iff hm V _).mp (hsound V hV)
    have hmemu : run (memQuery W) t ∈ W ∪ V := by
      rw [hpair W hW V hV hne]; exact mem_univ _
    rcases mem_union.mp hmemu with h | h
    · exact hWs h
    · exact hVs (heq ▸ h)
  have hmaps : ∀ W ∈ fam, run (memQuery W) t ∈ outputs t :=
    fun W _ => run_mem_outputs _ t
  have hcard : fam.card ≤ (outputs t).card :=
    card_le_card_of_injOn (fun W => run (memQuery W) t) hmaps
      (fun W hW V hV h => hinj W hW V hV h)
  exact hcard.trans (outputs_card_le t)

/-- Instantiation at the dense family `{univ.erase w}`.  Counting alone yields only
`m ≤ 2^depth`.  The membership primitive actually forces `depth ≥ m-1`
(`CardinalityQueryLaw.adaptive_cardinality_lower` with `s = m-1`); the exponential
gap between the two is exactly the price of the FIXED query primitive. -/
theorem dense_counting_bound (hm : 2 ≤ m) (t : Tree m)
    (hsound : ∀ w : Fin m,
      selectedRadius (components (univ.erase w)) {run (memQuery (univ.erase w)) t} = 0) :
    m ≤ 2 ^ depth t := by
  have hinj : Function.Injective (fun w : Fin m => (univ.erase w : Finset (Fin m))) := by
    intro w v h
    dsimp only at h
    by_contra hne
    have hw : w ∉ univ.erase w := by simp
    have hv : w ∈ univ.erase v := by simp [hne]
    rw [← h] at hv
    exact hw hv
  have hcard : (univ.image (fun w : Fin m => (univ.erase w : Finset (Fin m)))).card = m := by
    rw [card_image_of_injective _ hinj]
    simp
  have hbound := incompatible_worlds_lower hm
    (univ.image (fun w : Fin m => (univ.erase w : Finset (Fin m)))) ?_ t ?_
  · rwa [hcard] at hbound
  · intro W hW V hV hne
    obtain ⟨w, -, rfl⟩ := mem_image.mp hW
    obtain ⟨v, -, rfl⟩ := mem_image.mp hV
    have hwv : w ≠ v := by rintro rfl; exact hne rfl
    ext j
    simp only [mem_union, mem_erase, mem_univ, and_true, iff_true]
    by_cases hjw : j = w
    · exact Or.inr (by rw [hjw]; exact hwv)
    · exact Or.inl hjw
  · intro W hW
    obtain ⟨w, -, rfl⟩ := mem_image.mp hW
    exact hsound w

/-- Re-export of the exact law for the UNRESTRICTED geometry: `s` queries are
necessary and sufficient for the promise `W.card ≤ s`.  This is the sense in which
the unrestricted geometry has no residual hardness. -/
theorem unrestricted_exact_cost (hm : 2 ≤ m) (s : ℕ) (hs : s < m) (fallback : Fin m) :
    (∃ t : Tree m, depth t = s ∧ ∀ W : Finset (Fin m), W.card ≤ s →
        selectedRadius (components W) {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle W) t} = 0)
      ∧ (∀ t : Tree m, (∀ W : Finset (Fin m), W.card = s →
        selectedRadius (components W) {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle W) t} = 0)
        → s ≤ depth t) :=
  ⟨CIGAMF.P13.SupportCardinalityQueryLaw.adaptive_cardinality_attained hm s hs fallback,
   fun t ht => CIGAMF.P13.SupportCardinalityQueryLaw.adaptive_cardinality_lower hm s hs t ht⟩

#print axioms memQuery_formula
#print axioms dDepth_zero
#print axioms mem_encode_castAdd
#print axioms mem_encode_natAdd
#print axioms safety_faithful
#print axioms query_faithful
#print axioms depth_embed
#print axioms run_embed
#print axioms embed_restricted
#print axioms exists_embed_of_restricted
#print axioms correct_iff
#print axioms cost_preserving
#print axioms decision_restriction_necessary
#print axioms query_restriction_necessary
#print axioms run_mem_outputs
#print axioms outputs_card_le
#print axioms incompatible_worlds_lower
#print axioms dense_counting_bound
#print axioms unrestricted_exact_cost

end
end CIGAMF.P13.SupportGeometryReduction
