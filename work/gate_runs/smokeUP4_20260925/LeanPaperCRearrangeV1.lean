import «LeanPaperCFamilyV1»
import «LeanPaperCOddV1»

/-!
# Paper C: the rotation construction is a ranking of the family

The window sums of `LeanPaperCWindowV1` are about `oddBase` --- `(+3, -3, -1, +1, ...)` ---
while the value they support is a statement about rankings of

    g_m = (-3, -1 x p, +1 x q, +3).

Those are different sequences, and nothing in the corpus connected them.  If they were not
rearrangements of one another the window computation would be about the wrong object, so
this is load-bearing rather than cosmetic.

They are rearrangements, and the proof is by counting each weight on both sides.  Counting
turns into a sum over `Finset.range` and is evaluated with the same peel-and-split the
window sums use: the alternating indicator over `range (2s+1)` contributes `s+1` at the even
residues and `s` at the odd ones, and `g_m`'s block of light negatives contributes its
length.

The conclusion is equality of the counting function at EVERY real weight, which is equality
of the two multisets; at a weight outside `{-3,-1,1,3}` both counts are zero, and that case
is proved from the weight lemmas rather than waved at.
-/

namespace CIGAMF.P13.PaperCRearrange

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCOdd
open CIGAMF.P13.PaperCFamily

/-! ## Counting lemmas on `range` -/

theorem count_ge (a M : ℕ) (h : a ≤ M) :
    ∑ j ∈ Finset.range M, (if a ≤ j then (1 : ℕ) else 0) = M - a := by
  have hM : a + (M - a) = M := by omega
  have hs := Finset.sum_range_add (fun j => if a ≤ j then (1 : ℕ) else 0) a (M - a)
  rw [hM] at hs
  rw [hs]
  have h1 : ∑ j ∈ Finset.range a, (if a ≤ j then (1 : ℕ) else 0) = 0 :=
    Finset.sum_eq_zero (fun j hj => if_neg (by rw [Finset.mem_range] at hj; omega))
  have h2 : ∑ i ∈ Finset.range (M - a), (if a ≤ a + i then (1 : ℕ) else 0) = M - a := by
    rw [Finset.sum_congr rfl (fun i _ => if_pos (by omega)), Finset.sum_const,
      Finset.card_range, smul_eq_mul, mul_one]
  rw [h1, h2, zero_add]

theorem count_lt (b M : ℕ) (h : b ≤ M) :
    ∑ j ∈ Finset.range M, (if j < b then (1 : ℕ) else 0) = b := by
  have hM : b + (M - b) = M := by omega
  have hs := Finset.sum_range_add (fun j => if j < b then (1 : ℕ) else 0) b (M - b)
  rw [hM] at hs
  rw [hs]
  have h1 : ∑ j ∈ Finset.range b, (if j < b then (1 : ℕ) else 0) = b := by
    rw [Finset.sum_congr rfl (fun j hj => if_pos (by rw [Finset.mem_range] at hj; omega)),
      Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have h2 : ∑ i ∈ Finset.range (M - b), (if b + i < b then (1 : ℕ) else 0) = 0 :=
    Finset.sum_eq_zero (fun i _ => if_neg (by omega))
  rw [h1, h2, add_zero]

theorem count_even_range (s : ℕ) :
    ∑ i ∈ Finset.range (2 * s + 1), (if i % 2 = 0 then (1 : ℕ) else 0) = s + 1 := by
  induction s with
  | zero => rw [show 2 * 0 + 1 = 1 from by ring, Finset.sum_range_one]; norm_num
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 from by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      if_neg (by omega : ¬ (2 * n + 1) % 2 = 0), if_pos (by omega : (2 * n + 1 + 1) % 2 = 0)]

theorem count_odd_range (s : ℕ) :
    ∑ i ∈ Finset.range (2 * s + 1), (if i % 2 = 1 then (1 : ℕ) else 0) = s := by
  induction s with
  | zero => rw [show 2 * 0 + 1 = 1 from by ring, Finset.sum_range_one]; norm_num
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 from by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      if_pos (by omega : (2 * n + 1) % 2 = 1), if_neg (by omega : ¬ (2 * n + 1 + 1) % 2 = 1)]

/-! ## The two sequences, on `ℕ` indices -/

noncomputable def oddBaseN (j : ℕ) : ℝ :=
  if j = 0 then 3 else if j = 1 then -3 else if j % 2 = 0 then -1 else 1

theorem oddBase_apply (m : ℕ) (i : Fin m) : oddBase m i = oddBaseN (i : ℕ) := rfl

theorem oddBaseN_zero : oddBaseN 0 = 3 := by unfold oddBaseN; norm_num

theorem oddBaseN_one : oddBaseN 1 = -3 := by unfold oddBaseN; norm_num

theorem oddBaseN_mid (i : ℕ) : oddBaseN (i + 1 + 1) = if i % 2 = 0 then (-1 : ℝ) else 1 := by
  unfold oddBaseN
  rw [if_neg (by omega), if_neg (by omega), show (i + 1 + 1) % 2 = i % 2 from by omega]

theorem gN_mid (s i : ℕ) (hi : i < 2 * s + 1) :
    gN (2 * s + 3) (i + 1) = if i + 1 ≤ s + 1 then (-1 : ℝ) else 1 := by
  unfold gN
  rw [if_neg (by omega), if_neg (by omega), show (2 * s + 3 - 1) / 2 = s + 1 from by omega]

/-- How many positions carry the weight `w`. -/
noncomputable def countVal {m : ℕ} (f : Ranking m) (w : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => f i = w)).card

theorem countVal_oddBase (m : ℕ) (w : ℝ) :
    countVal (oddBase m) w
      = ∑ j ∈ Finset.range m, (if oddBaseN j = w then (1 : ℕ) else 0) := by
  classical
  unfold countVal
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun j => if oddBaseN j = w then (1 : ℕ) else 0) m

theorem countVal_gFamily (m : ℕ) (w : ℝ) :
    countVal (gFamily m) w
      = ∑ j ∈ Finset.range m, (if gN m j = w then (1 : ℕ) else 0) := by
  classical
  unfold countVal
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun j => if gN m j = w then (1 : ℕ) else 0) m

/-! ## The counts agree -/

/-- A `+-1`-valued indicator, summed: only the two admissible weights contribute. -/
theorem sum_ite_two (N : ℕ) (P : ℕ → Prop) [DecidablePred P] (w : ℝ) :
    ∑ i ∈ Finset.range N, (if (if P i then (-1 : ℝ) else 1) = w then (1 : ℕ) else 0)
      = if w = -1 then (∑ i ∈ Finset.range N, if P i then (1 : ℕ) else 0)
        else if w = 1 then (∑ i ∈ Finset.range N, if ¬ P i then (1 : ℕ) else 0) else 0 := by
  classical
  by_cases h1 : w = -1
  · subst h1
    rw [if_pos rfl]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hp : P i <;> norm_num [hp]
  · by_cases h2 : w = 1
    · subst h2
      rw [if_neg h1, if_pos rfl]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hp : P i <;> norm_num [hp]
    · rw [if_neg h1, if_neg h2]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_cases hp : P i <;> norm_num [hp, h1, h2] <;> tauto

/-- The middle block of `oddBase`, after peeling the two heavy positions. -/
theorem oddBase_mid_sum (s : ℕ) (w : ℝ) :
    ∑ j ∈ Finset.range (2 * s + 3), (if oddBaseN j = w then (1 : ℕ) else 0)
      = (∑ i ∈ Finset.range (2 * s + 1),
          (if (if i % 2 = 0 then (-1 : ℝ) else 1) = w then (1 : ℕ) else 0))
        + (if (-3 : ℝ) = w then 1 else 0) + (if (3 : ℝ) = w then 1 else 0) := by
  classical
  rw [show 2 * s + 3 = (2 * s + 1) + 1 + 1 from by ring,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.zero_add]
  have hmid : ∀ i ∈ Finset.range (2 * s + 1),
      (if oddBaseN (i + 1 + 1) = w then (1 : ℕ) else 0)
        = (if (if i % 2 = 0 then (-1 : ℝ) else 1) = w then (1 : ℕ) else 0) := by
    intro i _
    rw [oddBaseN_mid i]
  rw [Finset.sum_congr rfl hmid, oddBaseN_zero, oddBaseN_one]

/-- The middle block of `g_m`, after peeling the two heavy positions. -/
theorem gFamily_mid_sum (s : ℕ) (w : ℝ) :
    ∑ j ∈ Finset.range (2 * s + 3), (if gN (2 * s + 3) j = w then (1 : ℕ) else 0)
      = (∑ i ∈ Finset.range (2 * s + 1),
          (if (if i + 1 ≤ s + 1 then (-1 : ℝ) else 1) = w then (1 : ℕ) else 0))
        + (if (-3 : ℝ) = w then 1 else 0) + (if (3 : ℝ) = w then 1 else 0) := by
  classical
  rw [show 2 * s + 3 = (2 * s + 1) + 1 + 1 from by ring,
    Finset.sum_range_succ, Finset.sum_range_succ']
  have hlast : gN (2 * s + 3) (2 * s + 1 + 1) = 3 := by
    unfold gN; rw [if_neg (by omega), if_pos (by omega)]
  have hfirst : gN (2 * s + 3) 0 = -3 := by unfold gN; rw [if_pos rfl]
  have hmid : ∀ i ∈ Finset.range (2 * s + 1),
      (if gN (2 * s + 3) (i + 1) = w then (1 : ℕ) else 0)
        = (if (if i + 1 ≤ s + 1 then (-1 : ℝ) else 1) = w then (1 : ℕ) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [gN_mid s i hi]
  rw [Finset.sum_congr rfl hmid, hlast, hfirst]

/-- **The two sequences are rearrangements of one another**: every weight is carried by the
same number of positions.  So the rotation construction really is a law over rankings of
`g_m`, which is what the value statement is about. -/
theorem countVal_agree (s : ℕ) (w : ℝ) :
    countVal (oddBase (2 * s + 3)) w = countVal (gFamily (2 * s + 3)) w := by
  classical
  rw [countVal_oddBase, countVal_gFamily, oddBase_mid_sum, gFamily_mid_sum]
  have hL := sum_ite_two (2 * s + 1) (fun i => i % 2 = 0) w
  have hR := sum_ite_two (2 * s + 1) (fun i => i + 1 ≤ s + 1) w
  have hcountL : ∑ i ∈ Finset.range (2 * s + 1), (if i % 2 = 0 then (1 : ℕ) else 0) = s + 1 :=
    count_even_range s
  have hcountR : ∑ i ∈ Finset.range (2 * s + 1), (if i + 1 ≤ s + 1 then (1 : ℕ) else 0)
      = s + 1 := by
    have h : ∀ i ∈ Finset.range (2 * s + 1),
        (if i + 1 ≤ s + 1 then (1 : ℕ) else 0) = (if i < s + 1 then (1 : ℕ) else 0) := by
      intro i _
      congr 1
    rw [Finset.sum_congr rfl h, count_lt (s + 1) (2 * s + 1) (by omega)]
  have hcountL' : ∑ i ∈ Finset.range (2 * s + 1), (if ¬ (i % 2 = 0) then (1 : ℕ) else 0)
      = s := by
    have h : ∀ i ∈ Finset.range (2 * s + 1),
        (if ¬ (i % 2 = 0) then (1 : ℕ) else 0) = (if i % 2 = 1 then (1 : ℕ) else 0) := by
      intro i _
      congr 1
      simp only [eq_iff_iff]
      omega
    rw [Finset.sum_congr rfl h, count_odd_range s]
  have hcountR' : ∑ i ∈ Finset.range (2 * s + 1), (if ¬ (i + 1 ≤ s + 1) then (1 : ℕ) else 0)
      = s := by
    have h : ∀ i ∈ Finset.range (2 * s + 1),
        (if ¬ (i + 1 ≤ s + 1) then (1 : ℕ) else 0) = (if s + 1 ≤ i then (1 : ℕ) else 0) := by
      intro i _
      congr 1
      simp only [eq_iff_iff]
      omega
    rw [Finset.sum_congr rfl h, count_ge (s + 1) (2 * s + 1) (by omega)]
    omega
  rw [hL, hR, hcountL, hcountR, hcountL', hcountR']

/-! ## Audit -/

#print axioms count_ge
#print axioms count_lt
#print axioms count_even_range
#print axioms count_odd_range
#print axioms sum_ite_two
#print axioms countVal_oddBase
#print axioms countVal_gFamily
#print axioms countVal_agree

end CIGAMF.P13.PaperCRearrange
