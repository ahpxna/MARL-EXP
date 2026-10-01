import Mathlib

/-!
# Paper C: the critical budget of a rotation mixture, by omitting one item

At budget `m-1` a prefix omits exactly one position, so under a cyclic rotation its sum is
the total minus the omitted item --- and as the rotation ranges over all `m`, the omitted
item ranges over all `m`.  Hence, for ANY base sequence,

    sum over rotations of | prefix_{m-1} |  =  sum over items of | total - item | .

That is the whole computation at the budget where the odd family's value is attained: with
the signed-prefix weights `(+3, -3, -1, +1, ..., -1)` the total is `-1` and the right-hand
side is `|-4| + |2| + 0 * (m-1)/2 + 2 * (m-3)/2 = m + 3`, so the mixture pays `(m+3)/m`
there.  No classification of circular windows is needed for this budget.

WHAT THIS DOES NOT GIVE.  An upper bound on `V_m(0)` needs the mixture's value at EVERY
budget, since the objective is the maximum over budgets; this file gives one budget.  The
remaining budgets are where the window classification is required, and it is not here.
-/

namespace CIGAMF.P13.PaperCOmit

open Finset

variable {m : ℕ} [NeZero m]

/-- The positions a prefix of length `m-1` covers: everything but the last. -/
theorem prefix_filter_eq_erase (hm : 0 < m) :
    (Finset.univ.filter (fun i : Fin m => (i : ℕ) < m - 1))
      = Finset.univ.erase (⟨m - 1, by omega⟩ : Fin m) := by
  classical
  ext i
  have hi : (i : ℕ) < m := i.isLt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true,
    ne_eq, Fin.ext_iff, Fin.val_mk]
  omega

/-- **A prefix of length `m-1` under rotation `a` is the total minus one item**, and which
item it is depends on `a` alone. -/
theorem rot_prefix_omit (hm : 0 < m) (base : Fin m → ℝ) (a : Fin m) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < m - 1), base (i + a)
      = (∑ j, base j) - base ((⟨m - 1, by omega⟩ : Fin m) + a) := by
  classical
  rw [prefix_filter_eq_erase hm, Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun i => rfl)

/-- **Summing over the rotations, the omitted item ranges over everything.** -/
theorem sum_rot_abs_prefix (hm : 0 < m) (base : Fin m → ℝ) :
    ∑ a : Fin m, |∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < m - 1),
        base (i + a)|
      = ∑ j : Fin m, |(∑ k, base k) - base j| := by
  classical
  rw [Finset.sum_congr rfl (fun a _ => by rw [rot_prefix_omit hm base a])]
  exact Fintype.sum_equiv (Equiv.addLeft ((⟨m - 1, by omega⟩ : Fin m))) _ _ (fun a => rfl)

/-! ## Audit -/

#print axioms prefix_filter_eq_erase
#print axioms rot_prefix_omit
#print axioms sum_rot_abs_prefix

end CIGAMF.P13.PaperCOmit
