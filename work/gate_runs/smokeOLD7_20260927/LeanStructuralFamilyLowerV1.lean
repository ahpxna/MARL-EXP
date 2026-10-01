import Mathlib

/-! # Structural: the LOWER half of the all-`m` family law, with no saturation
hypothesis.

`LeanStructuralSaturationV1` proves the mechanism `pathVal = b · avgVal` but TAKES
the two conditions (`hconc`, `hbal`) as hypotheses, and its own "what this does not
establish" says the family `g_m = (-3, -1^p, +1^q, 3)` is only checked by script for
`m = 5..14`.  This file removes the hypotheses on the lower side: for the actual
family, EVERY ordering pays, and the two lower bounds follow for every mixture.

## THE FAMILY AND THE REGRET

`g_m = (-3, (-1)^p, (+1)^q, 3)` with `p = ⌈(m-2)/2⌉`, `q = ⌊(m-2)/2⌋`, so
`D = ∑|g_i| = m + 4` and the total `∑ g_i ∈ {0, -1}`.  An ordering is a permutation;
the retained prefix at budget `k` has sum `s_k`, and the normalised regret is
`(|s_k| - k mod 2)/D`, because `min_{|S| = k} |∑_{i∈S} g_i| = k mod 2` by parity
(every `g_i` is odd).

Because `|s_k| ≡ k (mod 2)`, that numerator is exactly `dfc s_k := |s_k| - |s_k| % 2`
-- the even part of `|s_k|` -- which needs no index bookkeeping.  `parity_bridge`
proves the two agree.

## WHAT IS PROVED

* `dfc_nonneg`, `dfc_even`, `dfc_eq_zero_iff`, `two_le_dfc` — a budget is free iff its
  prefix sum is in `{-1,0,1}`, and any defect is an even number `≥ 2`.
* `parity_bridge` — `dfc s_k = |s_k| - k mod 2`, so `dfc` IS the normalised numerator.
* `no_big_step` — **the mechanism**: if an ordering pays nothing at any budget then
  every single element moves the prefix sum by at most 2.
* `two_le_totalDefect` — hence an ordering containing a step of size 3 pays at least 2.
  This holds for EVERY permutation: no construction, no census, no hypothesis.
* `avg_lower` — every mixture has a budget with expected regret `≥ c / b`.
* `path_lower` — every mixture has expected max-regret `≥ c`.
* `avg_achieved`, `path_achieved` — the uniform mixture of `b` one-defect orderings
  attains both, so the two lower bounds are tight (the orderings themselves are built
  in `LeanStructuralFamilyUpperV1`).
* `ratio_card_concentrated_on_support` — the saturation lemma with `hconc` weakened to
  the SUPPORT of `P`, which is what any explicit mixture can supply.

## WHAT THIS DOES NOT ESTABLISH

- The existence of the `b` one-defect orderings is `LeanStructuralFamilyUpperV1`;
  here they are an input to `avg_achieved`/`path_achieved`.
- `dfc` is stated on the prefix sums of a list of integers.  That the list is a
  permutation of `g_m`, and that `D = m+4`, is arithmetic carried by the upper module
  and by `scripts/P14_structural_family_allm.py`.
- Nothing here is about an algorithm, a running time, or a fixed-ε separation: the
  level `2/(m+4)` DECREASES in `m` while the ratio `m-1` grows.
-/

namespace CIGAMF.P13.StructuralFamilyLower

open Finset

/-- The defect of a budget whose retained-prefix sum is `s`: the even part of `|s|`. -/
def dfc (s : ℤ) : ℤ := |s| - |s| % 2

theorem dfc_nonneg (s : ℤ) : 0 ≤ dfc s := by
  have h : 0 ≤ |s| := abs_nonneg s
  unfold dfc; omega

theorem dfc_even (s : ℤ) : dfc s % 2 = 0 := by
  have h : 0 ≤ |s| := abs_nonneg s
  unfold dfc; omega

theorem dfc_eq_zero_iff (s : ℤ) : dfc s = 0 ↔ |s| ≤ 1 := by
  have h : 0 ≤ |s| := abs_nonneg s
  unfold dfc; omega

theorem two_le_dfc (s : ℤ) (h : 2 ≤ |s|) : 2 ≤ dfc s := by
  unfold dfc; omega

theorem dfc_neg_three : dfc (-3) = 2 := by decide

theorem dfc_two : dfc 2 = 2 := by decide

theorem dfc_zero : dfc 0 = 0 := by decide

theorem dfc_one : dfc 1 = 0 := by decide

theorem dfc_neg_one : dfc (-1) = 0 := by decide

/-- `|s| % 2 = s % 2`, so the defect can be read off the sum itself. -/
theorem abs_emod_two (s : ℤ) : |s| % 2 = s % 2 := by
  rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

/-- The parity bridge: for a list of ODD steps the prefix sum after `k` steps has the
parity of `k`, so `dfc s_k = |s_k| - k mod 2` -- the normalised regret numerator. -/
theorem parity_bridge (s : ℤ) (k : ℕ) (h : s % 2 = (k : ℤ) % 2) :
    dfc s = |s| - (k : ℤ) % 2 := by
  have h2 := abs_emod_two s
  unfold dfc
  omega

/-- Every step defect of a run, one entry per element consumed. -/
def defects : ℤ → List ℤ → List ℤ
  | _, []     => []
  | s, x :: l => dfc (s + x) :: defects (s + x) l

/-- What the ordering pays in total. -/
def totalDefect (s : ℤ) (l : List ℤ) : ℤ := (defects s l).sum

theorem defects_length (s : ℤ) (l : List ℤ) : (defects s l).length = l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons x l ih => simp [defects, ih]

theorem defects_append (s : ℤ) (l₁ l₂ : List ℤ) :
    defects s (l₁ ++ l₂) = defects s l₁ ++ defects (s + l₁.sum) l₂ := by
  induction l₁ generalizing s with
  | nil => simp [defects]
  | cons x l ih =>
      have hassoc : s + (x + l.sum) = s + x + l.sum := by ring
      simp only [List.cons_append, defects, List.sum_cons, ih, hassoc, List.cons.injEq,
        true_and]

theorem totalDefect_nonneg (s : ℤ) (l : List ℤ) : 0 ≤ totalDefect s l := by
  unfold totalDefect
  induction l generalizing s with
  | nil => simp [defects]
  | cons x l ih =>
      have h1 := dfc_nonneg (s + x)
      have h2 := ih (s + x)
      simp only [defects, List.sum_cons]
      linarith

theorem totalDefect_even (s : ℤ) (l : List ℤ) : totalDefect s l % 2 = 0 := by
  unfold totalDefect
  induction l generalizing s with
  | nil => simp [defects]
  | cons x l ih =>
      have h1 := dfc_even (s + x)
      have h2 := ih (s + x)
      simp only [defects, List.sum_cons]
      omega

/-- **The mechanism.**  An ordering that pays nothing at any budget cannot move the
prefix sum by more than 2 in a single step. -/
theorem no_big_step (s : ℤ) (l : List ℤ) (hs : |s| ≤ 1) (he : |s + l.sum| ≤ 1)
    (h0 : totalDefect s l = 0) : ∀ x ∈ l, |x| ≤ 2 := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih =>
      intro y hy
      have hsplit : totalDefect s (x :: l) = dfc (s + x) + totalDefect (s + x) l := by
        simp [totalDefect, defects]
      have hA := dfc_nonneg (s + x)
      have hB := totalDefect_nonneg (s + x) l
      have hd : dfc (s + x) = 0 := by omega
      have hrest : totalDefect (s + x) l = 0 := by omega
      have hsx : |s + x| ≤ 1 := (dfc_eq_zero_iff _).1 hd
      have hend : |s + x + l.sum| ≤ 1 := by
        have : s + x + l.sum = s + (x :: l).sum := by simp [List.sum_cons]; ring
        rw [this]; exact he
      rcases List.mem_cons.1 hy with rfl | hy'
      · have h1 := abs_le.1 hs
        have h2 := abs_le.1 hsx
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      · exact ih (s + x) hsx hend hrest y hy'

/-- **Every** ordering of the family pays at least 2: the element `3` is a step of
size 3, so the prefix sums before and after it cannot both lie in `{-1,0,1}`, and the
defect is even. -/
theorem two_le_totalDefect (s : ℤ) (l : List ℤ) (hs : |s| ≤ 1) (he : |s + l.sum| ≤ 1)
    (h3 : ∃ x ∈ l, 2 < |x|) : 2 ≤ totalDefect s l := by
  have hn := totalDefect_nonneg s l
  have hev := totalDefect_even s l
  by_contra hlt
  push_neg at hlt
  have h0 : totalDefect s l = 0 := by omega
  obtain ⟨x, hx, hxb⟩ := h3
  have := no_big_step s l hs he h0 x hx
  omega

section Mixture

variable {Ord Bud : Type*} [Fintype Ord] [Fintype Bud] [Nonempty Ord] [Nonempty Bud]

/-- Lower bound on the average (per-budget) value: if every ordering pays at least
`c` in total, some budget carries expected regret `≥ c / b`. -/
theorem avg_lower (r : Ord → Bud → ℝ) (P : Ord → ℝ) (c : ℝ)
    (hr : ∀ pi k, 0 ≤ r pi k) (hP : ∀ pi, 0 ≤ P pi) (hsum : ∑ pi, P pi = 1)
    (hcost : ∀ pi, c ≤ ∑ k, r pi k) :
    c / (Fintype.card Bud : ℝ)
      ≤ (univ : Finset Bud).sup' univ_nonempty (fun k => ∑ pi, P pi * r pi k) := by
  classical
  set M := (univ : Finset Bud).sup' univ_nonempty (fun k => ∑ pi, P pi * r pi k) with hM
  have hcard : (0:ℝ) < (Fintype.card Bud : ℝ) := by
    have : 0 < Fintype.card Bud := Fintype.card_pos
    exact_mod_cast this
  have hswap : ∑ k, ∑ pi, P pi * r pi k = ∑ pi, P pi * (∑ k, r pi k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun pi _ => (Finset.mul_sum _ _ _).symm
  have hlow : c ≤ ∑ pi, P pi * (∑ k, r pi k) := by
    have : ∑ pi, P pi * c ≤ ∑ pi, P pi * (∑ k, r pi k) :=
      Finset.sum_le_sum fun pi _ => mul_le_mul_of_nonneg_left (hcost pi) (hP pi)
    have hc : ∑ pi, P pi * c = c := by rw [← Finset.sum_mul, hsum, one_mul]
    linarith [hc ▸ this]
  have hup : ∑ k, ∑ pi, P pi * r pi k ≤ (Fintype.card Bud : ℝ) * M := by
    have : ∀ k ∈ (univ : Finset Bud), (∑ pi, P pi * r pi k) ≤ M :=
      fun k hk => Finset.le_sup' (fun k => ∑ pi, P pi * r pi k) hk
    calc ∑ k, ∑ pi, P pi * r pi k
        ≤ ∑ _k : Bud, M := Finset.sum_le_sum this
      _ = (Fintype.card Bud : ℝ) * M := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [div_le_iff₀ hcard]
  have : c ≤ (Fintype.card Bud : ℝ) * M := by linarith [hswap ▸ hup]
  linarith [this]

/-- Lower bound on the execution (max-over-budgets) value. -/
theorem path_lower (r : Ord → Bud → ℝ) (P : Ord → ℝ) (c : ℝ)
    (hP : ∀ pi, 0 ≤ P pi) (hsum : ∑ pi, P pi = 1)
    (hcost : ∀ pi, ∃ k, c ≤ r pi k) :
    c ≤ ∑ pi, P pi * ((univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)) := by
  classical
  have hstep : ∀ pi : Ord, P pi * c
      ≤ P pi * ((univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)) := by
    intro pi
    obtain ⟨k, hk⟩ := hcost pi
    exact mul_le_mul_of_nonneg_left
      (le_trans hk (Finset.le_sup' (fun k => r pi k) (mem_univ k))) (hP pi)
  have := Finset.sum_le_sum (fun pi (_ : pi ∈ (univ : Finset Ord)) => hstep pi)
  have hc : ∑ pi, P pi * c = c := by rw [← Finset.sum_mul, hsum, one_mul]
  linarith [hc ▸ this]

/-- The uniform mixture of one-defect orderings attains the average lower bound. -/
theorem avg_achieved [DecidableEq Bud] (c : ℝ) (hc : 0 ≤ c) :
    (univ : Finset Bud).sup' univ_nonempty
        (fun k => ∑ j : Bud, (1 / (Fintype.card Bud : ℝ)) * (if k = j then c else 0))
      = c / (Fintype.card Bud : ℝ) := by
  classical
  have hval : ∀ k : Bud,
      (∑ j : Bud, (1 / (Fintype.card Bud : ℝ)) * (if k = j then c else 0))
        = c / (Fintype.card Bud : ℝ) := by
    intro k
    rw [← Finset.mul_sum]
    have : (∑ j : Bud, (if k = j then c else 0)) = c := by
      simp
    rw [this]; ring
  simp only [hval]
  exact le_antisymm (Finset.sup'_le _ _ fun k _ => le_rfl)
    (Finset.le_sup' (fun _ : Bud => c / (Fintype.card Bud : ℝ)) (mem_univ (Classical.arbitrary Bud)))

/-- …and the execution lower bound, so both are tight. -/
theorem path_achieved [DecidableEq Bud] (c : ℝ) (hc : 0 ≤ c) :
    (∑ j : Bud, (1 / (Fintype.card Bud : ℝ))
        * ((univ : Finset Bud).sup' univ_nonempty (fun k => if k = j then c else 0)))
      = c := by
  classical
  have hsup : ∀ j : Bud,
      (univ : Finset Bud).sup' univ_nonempty (fun k => if k = j then c else 0) = c := by
    intro j
    refine le_antisymm (Finset.sup'_le _ _ fun k _ => ?_) ?_
    · by_cases h : k = j <;> simp [h, hc]
    · have h : (if j = j then c else 0)
          ≤ (univ : Finset Bud).sup' univ_nonempty (fun k => if k = j then c else 0) :=
        Finset.le_sup' (fun k => if k = j then c else 0) (mem_univ j)
      rwa [if_pos rfl] at h
  have hcard : (Fintype.card Bud : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [hsup]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The saturation lemma with the concentration hypothesis weakened to the SUPPORT of
the mixture -- the form an explicit mixture can actually supply. -/
theorem ratio_card_concentrated_on_support
    (r : Ord → Bud → ℝ) (P : Ord → ℝ) (e : ℝ)
    (hP : ∀ pi, 0 ≤ P pi)
    (hbal : ∀ k, (∑ pi, P pi * r pi k) = e)
    (hconc : ∀ pi, P pi ≠ 0 →
      (∑ k, r pi k) = (univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)) :
    (∑ pi, P pi * ((univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)))
      = (Fintype.card Bud : ℝ)
        * (univ : Finset Bud).sup' univ_nonempty (fun k => ∑ pi, P pi * r pi k) := by
  classical
  have hleft : (∑ pi, P pi * ((univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)))
      = ∑ pi, P pi * (∑ k, r pi k) := by
    refine Finset.sum_congr rfl fun pi _ => ?_
    by_cases h : P pi = 0
    · rw [h]; ring
    · rw [hconc pi h]
  have hswap : ∑ pi, P pi * (∑ k, r pi k) = ∑ k, ∑ pi, P pi * r pi k := by
    have inner : ∀ pi : Ord, P pi * (∑ k, r pi k) = ∑ k, P pi * r pi k :=
      fun pi => Finset.mul_sum _ _ _
    simp_rw [inner]
    exact Finset.sum_comm
  have hright : ∑ k, ∑ pi, P pi * r pi k = (Fintype.card Bud : ℝ) * e := by
    simp only [hbal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmax : (univ : Finset Bud).sup' univ_nonempty (fun k => ∑ pi, P pi * r pi k) = e := by
    simp only [hbal]
    exact le_antisymm (Finset.sup'_le _ _ fun k _ => le_rfl)
      (Finset.le_sup' (fun _ : Bud => e) (mem_univ (Classical.arbitrary Bud)))
  rw [hleft, hswap, hright, hmax]

end Mixture

#print axioms dfc_nonneg
#print axioms dfc_even
#print axioms dfc_eq_zero_iff
#print axioms two_le_dfc
#print axioms parity_bridge
#print axioms defects_append
#print axioms totalDefect_nonneg
#print axioms totalDefect_even
#print axioms no_big_step
#print axioms two_le_totalDefect
#print axioms avg_lower
#print axioms path_lower
#print axioms avg_achieved
#print axioms path_achieved
#print axioms ratio_card_concentrated_on_support

end CIGAMF.P13.StructuralFamilyLower
