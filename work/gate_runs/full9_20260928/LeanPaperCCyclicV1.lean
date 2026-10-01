import Mathlib

/-!
# Paper C: uniform cyclic rotations give uniform retained marginals

The odd-`m` construction mixes the `m` cyclic rotations of one fixed sequence uniformly.
Its feasibility rests on a single combinatorial fact: **across the `m` rotations, each item
occupies each position exactly once**, so every position marginal is `1/m` and the retained
marginal at budget `k` is exactly `k/m` --- the band's centre, with deviation zero.

That fact is the content, and it is a statement about the cyclic group acting on positions,
not about the sequence being rotated.  It is proved here in that form, so it applies to the
odd family and to any other rotation mixture.

WHAT THIS IS NOT.  The marginals, not the value.  What the odd family's rotations pay at
each budget --- `4/m` at odd budgets and `(k+4)/m` at even ones, with the maximum
`(m+3)/m` at `k = m-1` --- requires classifying circular windows by how many heavy items
they contain, and is not proved here.
-/

namespace CIGAMF.P13.PaperCCyclic

open Finset

variable {m : ℕ} [NeZero m]

/-- **Each item reaches each position under exactly one rotation.**  The rotation that does
it is `j - i`, and it is the only one. -/
theorem rotation_hits_once (i j : Fin m) :
    ∑ a : Fin m, (if i + a = j then (1 : ℝ) else 0) = 1 := by
  classical
  have hcond : ∀ a : Fin m, (i + a = j) ↔ (a = j - i) := by
    intro a
    constructor
    · intro h
      exact eq_sub_of_add_eq' h
    · intro h
      subst h
      abel
  rw [Finset.sum_congr rfl (fun a _ => by rw [if_congr (hcond a) rfl rfl])]
  rw [Finset.sum_ite_eq' Finset.univ (j - i) (fun _ => (1 : ℝ)),
      if_pos (Finset.mem_univ _)]

/-- **So every position marginal under the uniform rotation mixture is `1/m`.** -/
theorem uniform_position_marginal (i j : Fin m) :
    ∑ a : Fin m, (1 / (m : ℝ)) * (if i + a = j then (1 : ℝ) else 0) = 1 / (m : ℝ) := by
  rw [← Finset.mul_sum, rotation_hits_once i j, mul_one]

/-- **And the retained marginal at budget `k` is exactly `k/m`** --- the band's centre, so
the deviation is zero and every band of positive width is satisfied. -/
theorem retained_marginal (j : Fin m) (k : ℕ) (hk : k ≤ m) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < k),
        ∑ a : Fin m, (1 / (m : ℝ)) * (if i + a = j then (1 : ℝ) else 0)
      = (k : ℝ) / (m : ℝ) := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => uniform_position_marginal i j),
      Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)).card = k := by
    have himg : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)).image Fin.val
        = Finset.range k := by
      ext n
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hn
        exact ⟨⟨n, lt_of_lt_of_le hn hk⟩, hn, rfl⟩
    calc (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)).card
        = ((Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)).image Fin.val).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ = (Finset.range k).card := by rw [himg]
      _ = k := Finset.card_range k
  rw [hcard]
  ring

/-- **The deviation from the uniform band centre is zero**, which is the form the band
constraint is stated in. -/
theorem band_deviation_zero (j : Fin m) (k : ℕ) (hk : k ≤ m) :
    |(∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < k),
        ∑ a : Fin m, (1 / (m : ℝ)) * (if i + a = j then (1 : ℝ) else 0))
      - (k : ℝ) / (m : ℝ)| = 0 := by
  rw [retained_marginal j k hk]
  simp

/-! ## Audit -/

#print axioms rotation_hits_once
#print axioms uniform_position_marginal
#print axioms retained_marginal
#print axioms band_deviation_zero

end CIGAMF.P13.PaperCCyclic
