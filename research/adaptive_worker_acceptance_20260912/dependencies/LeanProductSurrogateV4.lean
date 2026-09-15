import Mathlib

/-! Product-surrogate Chain D.  The product-reference objects are typed
separately from primitive-isolation kernels. -/

namespace CIGAMF.V4.ProductSurrogate

open scoped BigOperators

variable {ι U : Type*} [Fintype ι] [DecidableEq ι]

def surrogate (Q : ι → U → ℝ) (b : ℝ) (a : ι → U) : ℝ :=
  (∑ j, Q j (a j)) - ((Fintype.card ι : ℝ) - 1) * b

def mixedDifference
    (F : (ι → U) → ℝ) (i : ι) (x c : ι → U) : ℝ :=
  F x - F (Function.update x i (c i)) -
    F (Function.update c i (x i)) + F c

/- This lemma is the exact algebraic core after product expectations have
established the response identities.  It does not assume a `chi_iso` term. -/
theorem D1_exact_additive_surrogate_from_response_identities
    (f : ι → U → ℝ) (mu : ι → ℝ) (b0 b : ℝ)
    (Q : ι → U → ℝ) (a : ι → U)
    (hQ : ∀ j u, Q j u = b0 + f j u + (∑ l, mu l) - mu j)
    (hb : b = b0 + ∑ l, mu l) :
    surrogate Q b a = b0 + ∑ j, f j (a j) := by
  classical
  unfold surrogate
  simp_rw [hQ]
  rw [hb]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp
  ring

end CIGAMF.V4.ProductSurrogate
