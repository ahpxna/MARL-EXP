import Mathlib
import «LeanPaperCCountReductionV1»

/-!
# Two ways to pay for non-nestedness: a MENU of rankings, or REVISION after the reveal

Any per-budget cost `r : Fin (m+1) → Finset (Fin m) → ℝ`, a budget set `K`, a tolerance `ε`.
Deterministic achievability predicates:
* `MenuAchieves r K n ε`: commit to `n` rankings; after the budget `k` is revealed, pick one;
  its prefix has cost `≤ ε` at every `k ∈ K`.  This is the object of Structural's
  prefix-cover dimension and of `models/kprefix_net.py`.
* `RevAchieves r K R ε`: commit to ONE ranking; after the reveal, replace at most `R` items of
  its prefix.
* `AwareAchieves r K ε`: every budget has some admissible set of cost `≤ ε`; the budget-aware
  benchmark.

## WHAT IS PROVED

* `menu_one_iff_rev_zero` — one ranking and no revision are the same thing.
* `menu_mono`, `rev_mono` — more rankings or more revisions never hurt.
* `aware_of_menu`, `aware_of_rev` — neither beats the budget-aware benchmark.
* `menu_of_aware` — `|K|` rankings always reach it.
* `rev_of_aware_full` — `R ≥ min(k, m − k)` at every budget always reaches it.
* `separation_three` — on three items with the XOR game's optimal structure (best singleton
  `{0}`, best pair `{1,2}`), TWO rankings and ONE revision both reach cost `0`, while one
  ranking without revision cannot get below cost `1`.
* `prefix_realises`, `prefixSet_mono` — every k-set is a prefix, and prefixes are nested.

## WHAT THIS DOES NOT ESTABLISH

- Randomised menus or banded laws.  The randomised XOR price `p(1−2p)` is paper-level and
  separate.
- A formal link to `LeanStructuralPrefixCoverDimensionV1` (it uses `List` rankings and all
  budgets).  The correspondence is by definition, but it is not written as a theorem here.
- Menu size against revision budget in general: which (n, R) pairs are equivalent.
-/

namespace CIGAMF.P13.MarlMenuRevision

open Finset
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCCountReduction CIGAMF.P13.PaperCBudgetAware

variable {m : ℕ}

def MenuAchieves (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1))) (n : ℕ)
    (ε : ℝ) : Prop :=
  ∃ M : Fin n → Equiv.Perm (Fin m), ∀ k ∈ K, ∃ j, r k (prefixSet (M j) k) ≤ ε

def RevAchieves (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1))) (R : ℕ)
    (ε : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), ∀ k ∈ K, ∃ S : Finset (Fin m),
    S.card = k.val ∧ (prefixSet σ k \ S).card ≤ R ∧ r k S ≤ ε

def AwareAchieves (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1)))
    (ε : ℝ) : Prop :=
  ∀ k ∈ K, ∃ S : Finset (Fin m), S.card = k.val ∧ r k S ≤ ε

theorem prefixSet_mono (σ : Equiv.Perm (Fin m)) (k k' : Fin (m + 1)) (h : k.val ≤ k'.val) :
    prefixSet σ k ⊆ prefixSet σ k' := by
  intro i hi
  unfold prefixSet at hi ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

/-- Every k-set is the prefix of some ranking. -/
theorem prefix_realises (S : Finset (Fin m)) (k : Fin (m + 1)) (hk : S.card = k.val) :
    ∃ σ : Equiv.Perm (Fin m), prefixSet σ k = S := by
  obtain ⟨σ, hσ⟩ := exists_prefix_perm S
  refine ⟨σ, ?_⟩
  ext i
  unfold prefixSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have := hσ (σ.symm i)
  rw [Equiv.apply_symm_apply] at this
  rw [← hk]
  exact this.symm

/-- A set of the prefix's size containing the prefix up to zero replacements IS the prefix. -/
theorem eq_prefix_of_zero (σ : Equiv.Perm (Fin m)) (k : Fin (m + 1)) (S : Finset (Fin m))
    (hS : S.card = k.val) (h0 : (prefixSet σ k \ S).card ≤ 0) : S = prefixSet σ k := by
  have he : prefixSet σ k \ S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp h0)
  have hsub : prefixSet σ k ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp he
  have hc : S.card ≤ (prefixSet σ k).card := by rw [prefixSet_card, hS]
  exact (Finset.eq_of_subset_of_card_le hsub hc).symm

theorem menu_one_iff_rev_zero (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1)))
    (ε : ℝ) : MenuAchieves r K 1 ε ↔ RevAchieves r K 0 ε := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M 0, fun k hk => ?_⟩
    obtain ⟨j, hj⟩ := hM k hk
    have : j = 0 := Subsingleton.elim j 0
    subst this
    exact ⟨prefixSet (M 0) k, prefixSet_card _ _, by simp, hj⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨fun _ => σ, fun k hk => ?_⟩
    obtain ⟨S, hS, h0, hr⟩ := hσ k hk
    refine ⟨0, ?_⟩
    rw [← eq_prefix_of_zero σ k S hS h0]
    exact hr

theorem rev_mono (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1))) (ε : ℝ)
    (R R' : ℕ) (hRR : R ≤ R') (h : RevAchieves r K R ε) : RevAchieves r K R' ε := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, fun k hk => by
    obtain ⟨S, hS, hd, hr⟩ := hσ k hk
    exact ⟨S, hS, hd.trans hRR, hr⟩⟩

theorem menu_mono (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1))) (ε : ℝ)
    (n n' : ℕ) (hn : n ≤ n') (h : MenuAchieves r K n ε) : MenuAchieves r K n' ε := by
  obtain ⟨M, hM⟩ := h
  refine ⟨fun j => if hj : j.val < n then M ⟨j.val, hj⟩ else 1, fun k hk => ?_⟩
  obtain ⟨j, hj⟩ := hM k hk
  refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hn⟩, ?_⟩
  simp only [j.isLt, dite_true]
  exact hj

theorem aware_of_rev (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1))) (ε : ℝ)
    (R : ℕ) (h : RevAchieves r K R ε) : AwareAchieves r K ε := by
  obtain ⟨σ, hσ⟩ := h
  intro k hk
  obtain ⟨S, hS, -, hr⟩ := hσ k hk
  exact ⟨S, hS, hr⟩

theorem aware_of_menu (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1))) (ε : ℝ)
    (n : ℕ) (h : MenuAchieves r K n ε) : AwareAchieves r K ε := by
  obtain ⟨M, hM⟩ := h
  intro k hk
  obtain ⟨j, hj⟩ := hM k hk
  exact ⟨prefixSet (M j) k, prefixSet_card _ _, hj⟩

/-- **`|K|` rankings reach the budget-aware benchmark.** -/
theorem menu_of_aware (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1))) (ε : ℝ)
    (n : ℕ) (hn : K.card ≤ n) (h : AwareAchieves r K ε) : MenuAchieves r K n ε := by
  classical
  have hpick : ∀ k : K, ∃ σ : Equiv.Perm (Fin m), r k (prefixSet σ k) ≤ ε := by
    intro k
    obtain ⟨S, hS, hr⟩ := h k.1 k.2
    obtain ⟨σ, hσ⟩ := prefix_realises S k.1 hS
    exact ⟨σ, by rw [hσ]; exact hr⟩
  choose pick hpick using hpick
  refine ⟨fun j => if hj : j.val < K.card then pick (K.equivFin.symm ⟨j.val, hj⟩) else 1,
    fun k hk => ?_⟩
  let e := K.equivFin ⟨k, hk⟩
  refine ⟨⟨e.val, lt_of_lt_of_le e.isLt hn⟩, ?_⟩
  simp only [e.isLt, dite_true]
  have he : K.equivFin.symm ⟨e.val, e.isLt⟩ = ⟨k, hk⟩ := by
    simp [e]
  rw [he]
  exact hpick ⟨k, hk⟩

/-- **`R ≥ min(k, m − k)` revisions reach the budget-aware benchmark.** -/
theorem rev_of_aware_full (r : Fin (m + 1) → Finset (Fin m) → ℝ) (K : Finset (Fin (m + 1)))
    (ε : ℝ) (R : ℕ) (hR : ∀ k ∈ K, min k.val (m - k.val) ≤ R) (h : AwareAchieves r K ε) :
    RevAchieves r K R ε := by
  refine ⟨1, fun k hk => ?_⟩
  obtain ⟨S, hS, hr⟩ := h k hk
  refine ⟨S, hS, ?_, hr⟩
  have := sdiff_card_le (prefixSet 1 k) S k.val (prefixSet_card _ _) hS
  exact le_trans (le_min this.1 this.2) (hR k hk)

/-! ## A separation on three items (the XOR game's optimal structure) -/

/-- Cost `0` exactly at the best singleton `{0}` (budget 1) and the best pair `{1,2}` (budget 2). -/
noncomputable def xorCost (k : Fin 4) (S : Finset (Fin 3)) : ℝ :=
  if (k.val = 1 ∧ S = {0}) ∨ (k.val = 2 ∧ S = {1, 2}) then 0 else 1

def budgets12 : Finset (Fin 4) := {1, 2}

theorem xorCost_ge (k : Fin 4) (S : Finset (Fin 3)) (h : xorCost k S ≤ 1 / 2) :
    (k.val = 1 ∧ S = {0}) ∨ (k.val = 2 ∧ S = {1, 2}) := by
  unfold xorCost at h
  by_contra hc
  rw [if_neg hc] at h
  norm_num at h

/-- **Separation.**  Two rankings reach cost `0`; one revision reaches cost `0`; but one
ranking with no revision cannot even reach cost `1/2`. -/
theorem separation_three :
    MenuAchieves xorCost budgets12 2 0 ∧ RevAchieves xorCost budgets12 1 0 ∧
      ¬ MenuAchieves xorCost budgets12 1 (1 / 2) ∧ ¬ RevAchieves xorCost budgets12 0 (1 / 2) := by
  classical
  obtain ⟨σ1, h1⟩ := prefix_realises ({0} : Finset (Fin 3)) (1 : Fin 4) (by decide)
  obtain ⟨σ2, h2⟩ := prefix_realises ({1, 2} : Finset (Fin 3)) (2 : Fin 4) (by decide)
  have c1 : xorCost 1 {0} = 0 := by unfold xorCost; simp
  have c2 : xorCost 2 {1, 2} = 0 := by unfold xorCost; simp
  have hnot : ¬ RevAchieves xorCost budgets12 0 (1 / 2) := by
    rintro ⟨σ, hσ⟩
    obtain ⟨S1, hS1, h01, hr1⟩ := hσ 1 (by decide)
    obtain ⟨S2, hS2, h02, hr2⟩ := hσ 2 (by decide)
    have e1 := eq_prefix_of_zero σ 1 S1 hS1 h01
    have e2 := eq_prefix_of_zero σ 2 S2 hS2 h02
    have g1 := xorCost_ge 1 S1 hr1
    have g2 := xorCost_ge 2 S2 hr2
    have s1 : S1 = {0} := by
      rcases g1 with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h (by decide)
    have s2 : S2 = {1, 2} := by
      rcases g2 with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h (by decide)
      · exact h
    have hmono := prefixSet_mono σ 1 2 (by decide)
    rw [← e1, ← e2, s1, s2] at hmono
    have : (0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := hmono (by simp)
    exact absurd this (by decide)
  refine ⟨⟨![σ1, σ2], fun k hk => ?_⟩, ⟨σ1, fun k hk => ?_⟩, ?_, hnot⟩
  · have hk' : k = 1 ∨ k = 2 := by simpa [budgets12] using hk
    rcases hk' with rfl | rfl
    · exact ⟨0, by simp [h1, c1]⟩
    · exact ⟨1, by simp [h2, c2]⟩
  · have hk' : k = 1 ∨ k = 2 := by simpa [budgets12] using hk
    rcases hk' with rfl | rfl
    · exact ⟨{0}, by decide, by rw [h1]; simp, by rw [c1]⟩
    · refine ⟨{1, 2}, by decide, ?_, by rw [c2]⟩
      have hsub : prefixSet σ1 2 \ {1, 2} ⊆ ({0} : Finset (Fin 3)) := by
        intro x hx
        have hx2 : x ∉ ({1, 2} : Finset (Fin 3)) := (Finset.mem_sdiff.mp hx).2
        fin_cases x <;> simp_all
      calc (prefixSet σ1 2 \ {1, 2}).card ≤ ({0} : Finset (Fin 3)).card := Finset.card_le_card hsub
        _ = 1 := by decide
  · rw [menu_one_iff_rev_zero]; exact hnot

end CIGAMF.P13.MarlMenuRevision

#print axioms CIGAMF.P13.MarlMenuRevision.prefix_realises
#print axioms CIGAMF.P13.MarlMenuRevision.menu_one_iff_rev_zero
#print axioms CIGAMF.P13.MarlMenuRevision.menu_mono
#print axioms CIGAMF.P13.MarlMenuRevision.rev_mono
#print axioms CIGAMF.P13.MarlMenuRevision.aware_of_menu
#print axioms CIGAMF.P13.MarlMenuRevision.aware_of_rev
#print axioms CIGAMF.P13.MarlMenuRevision.menu_of_aware
#print axioms CIGAMF.P13.MarlMenuRevision.rev_of_aware_full
#print axioms CIGAMF.P13.MarlMenuRevision.separation_three
