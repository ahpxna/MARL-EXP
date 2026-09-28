import Mathlib

/-!
# Paper B, step B4: the order is ATTAINED, with the exact constant.

## WHY THIS MODULE EXISTS

`LeanUnifiedQueryOrderV1` proves the vanishing half of the order law: no admissible query of
degree `d` sees the hidden character before order `ceil(n/d)`.  That gives a lower bound on
cost and nothing else.  Without a query that actually attains the order, the rate is only
`Omega`, never `Theta`, and the paper could not claim a matching upper bound.

This module closes it.  For the tail character and the averaged tail query, the statement
reduces to the single cube identity

    cubeSum n k  =  sum over z in {-1,1}^n of  (prod_i z_i) * (sum_i z_i)^k
                 =  0             for k < n,
                 =  2^n * n!      for k = n,

and the second line is the non-zero leading coefficient the upper bound needs: dividing by
`2^n` (the cube's cardinality) and by `n^n` gives `E[chi_n g^n] = n!/n^n`.

## THE PROOF

Not by counting bijections, which needs fibre counting and a permutation bijection, but by a
recurrence.  Peeling one coordinate off the cube and expanding the binomial gives

    cubeSum (n+1) k = sum_j C(k,j) * (1 + (-1)^(j+1)) * cubeSum n (k-j),

and the parity factor kills every even `j`.  For odd `j` we have `j >= 1`, so the recursive
index drops strictly, and one induction gives both lines at once: below the diagonal every
term vanishes, and on the diagonal only `j = 1` survives, contributing `(n+1) * 2 * 2^n * n!`.

## WHAT IS PROVED

* `cubeSum_succ` -- the recurrence, from the cube splitting and the binomial theorem.
* `cubeSum_below_diag` -- `cubeSum n k = 0` for `k < n`.
* `cubeSum_diag` -- **`cubeSum n n = 2^n * n!`**, the attained leading coefficient.
* `tail_query_moment` -- the normalised form `E[chi_n g^n] = n!/n^n`.

## WHAT THIS DOES NOT ESTABLISH

- This is the moment identity, not the sample-complexity upper bound.  Turning a non-zero
  moment contrast into an estimator with an `h^(-2r) log(1/alpha)` guarantee needs a
  concentration argument for that estimator, which is standard and is not formalised.
- The query fixed here is the averaged tail; optimality among admissible queries is not
  claimed, only attainment of the order.
-/

set_option maxHeartbeats 4000000

namespace CIGAMF.P13.PaperBAttainment

open Finset

/-- A latent coordinate as a sign. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgn_true : sgn true = 1 := by simp [sgn]
@[simp] theorem sgn_false : sgn false = -1 := by simp [sgn]

/-- The cube sum of the top character against a power of the coordinate sum. -/
noncomputable def cubeSum (n k : ℕ) : ℝ :=
  ∑ z : Fin n → Bool, (∏ i, sgn (z i)) * (∑ i, sgn (z i)) ^ k

theorem cubeSum_zero_zero : cubeSum 0 0 = 1 := by
  unfold cubeSum
  simp

private theorem pfac_even {j : ℕ} (h : Even j) : (1 : ℝ) + (-1) ^ (j + 1) = 0 := by
  have ho : Odd (j + 1) := Even.add_one h
  rw [ho.neg_one_pow]
  ring

private theorem pfac_odd {j : ℕ} (h : Odd j) : (1 : ℝ) + (-1) ^ (j + 1) = 2 := by
  have he : Even (j + 1) := Odd.add_one h
  rw [he.neg_one_pow]
  ring

private theorem sum_sgn_pow (m : ℕ) : (∑ b : Bool, sgn b ^ m) = 1 + (-1) ^ m := by
  simp [Fintype.sum_bool, sgn]

/-- Splitting the cube into its first coordinate and the rest.  Defined explicitly so that
`toFun` is definitionally `Fin.cons`, which keeps the rewrite below elaborating. -/
private def consE (n : ℕ) : Bool × (Fin n → Bool) ≃ (Fin (n + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun z := (z 0, fun i => z i.succ)
  left_inv := by rintro ⟨b, z'⟩; simp
  right_inv := by
    intro z
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp

/-- **The recurrence.** -/
theorem cubeSum_succ (n k : ℕ) :
    cubeSum (n + 1) k
      = ∑ j ∈ range (k + 1),
          (k.choose j : ℝ) * (1 + (-1) ^ (j + 1)) * cubeSum n (k - j) := by
  classical
  -- split the cube into its first coordinate and the rest
  have hsplit : (∑ p : Bool × (Fin n → Bool),
        (sgn p.1 * ∏ i, sgn (p.2 i)) * (sgn p.1 + ∑ i, sgn (p.2 i)) ^ k)
      = cubeSum (n + 1) k := by
    unfold cubeSum
    refine Fintype.sum_equiv (consE n) _ _ ?_
    rintro ⟨b, z'⟩
    show (sgn b * ∏ i, sgn (z' i)) * (sgn b + ∑ i, sgn (z' i)) ^ k
        = (∏ i, sgn ((Fin.cons b z' : Fin (n + 1) → Bool) i))
          * (∑ i, sgn ((Fin.cons b z' : Fin (n + 1) → Bool) i)) ^ k
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    simp
  rw [← hsplit, Fintype.sum_prod_type]
  -- expand the binomial inside
  have hexp : ∀ (b : Bool) (z' : Fin n → Bool),
      (sgn b * ∏ i, sgn (z' i)) * (sgn b + ∑ i, sgn (z' i)) ^ k
        = ∑ j ∈ range (k + 1),
            sgn b ^ (j + 1) * ((k.choose j : ℝ)
              * ((∏ i, sgn (z' i)) * (∑ i, sgn (z' i)) ^ (k - j))) := by
    intro b z'
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  -- move the binomial index outermost
  have swap1 : ∀ b : Bool,
      (∑ z' : Fin n → Bool, ∑ j ∈ range (k + 1),
          sgn b ^ (j + 1) * ((k.choose j : ℝ)
            * ((∏ i, sgn (z' i)) * (∑ i, sgn (z' i)) ^ (k - j))))
        = ∑ j ∈ range (k + 1), ∑ z' : Fin n → Bool,
            sgn b ^ (j + 1) * ((k.choose j : ℝ)
              * ((∏ i, sgn (z' i)) * (∑ i, sgn (z' i)) ^ (k - j))) :=
    fun b => Finset.sum_comm
  rw [Finset.sum_congr rfl fun b _ => swap1 b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- factor the inner cube sum and the parity factor
  have hinner : ∀ b : Bool,
      (∑ z' : Fin n → Bool,
          sgn b ^ (j + 1) * ((k.choose j : ℝ)
            * ((∏ i, sgn (z' i)) * (∑ i, sgn (z' i)) ^ (k - j))))
        = sgn b ^ (j + 1) * ((k.choose j : ℝ) * cubeSum n (k - j)) := by
    intro b
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  rw [Finset.sum_congr rfl fun b _ => hinner b, ← Finset.sum_mul, sum_sgn_pow]
  ring

/-- **Below the diagonal everything vanishes, and on the diagonal the value is `2^n n!`.** -/
theorem cubeSum_main : ∀ n : ℕ,
    (∀ k, k < n → cubeSum n k = 0) ∧ cubeSum n n = 2 ^ n * (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun k hk => absurd hk (Nat.not_lt_zero k), ?_⟩
      simpa using cubeSum_zero_zero
  | succ n ih =>
      obtain ⟨ihzero, ihdiag⟩ := ih
      constructor
      · -- below the diagonal
        intro k hk
        rw [cubeSum_succ]
        refine Finset.sum_eq_zero fun j hj => ?_
        rcases Nat.even_or_odd j with he | ho
        · rw [pfac_even he]; ring
        · have hj1 : 1 ≤ j := ho.pos
          have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hlt : k - j < n := by omega
          rw [ihzero (k - j) hlt]
          ring
      · -- on the diagonal
        rw [cubeSum_succ]
        rw [Finset.sum_eq_single 1]
        · have hch : ((n + 1).choose 1 : ℝ) = (n : ℝ) + 1 := by
            rw [Nat.choose_one_right]; push_cast; ring
          have hpar : (1 : ℝ) + (-1) ^ (1 + 1) = 2 := by norm_num
          have hidx : n + 1 - 1 = n := by omega
          rw [hch, hpar, hidx, ihdiag]
          rw [Nat.factorial_succ]
          push_cast
          ring
        · intro j hj hne
          rcases Nat.even_or_odd j with he | ho
          · rw [pfac_even he]; ring
          · have hjk : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have hj2 : 2 ≤ j := by
              obtain ⟨t, ht⟩ := ho
              omega
            have hlt : n + 1 - j < n := by omega
            rw [ihzero (n + 1 - j) hlt]
            ring
        · intro hno
          exact absurd (Finset.mem_range.mpr (by omega)) hno

theorem cubeSum_below_diag (n k : ℕ) (h : k < n) : cubeSum n k = 0 :=
  (cubeSum_main n).1 k h

theorem cubeSum_diag (n : ℕ) : cubeSum n n = 2 ^ n * (n.factorial : ℝ) :=
  (cubeSum_main n).2

/-- **The normalised statement.**  Averaging over the cube and dividing by `n^n` -- the
normalisation of the averaged tail query `g = (1/n) sum_l z_l` -- gives the moment the
attainment argument needs, and it is non-zero for every `n >= 1`. -/
theorem tail_query_moment (n : ℕ) (hn : 0 < n) :
    cubeSum n n / (2 ^ n * (n : ℝ) ^ n) = (n.factorial : ℝ) / (n : ℝ) ^ n := by
  rw [cubeSum_diag]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hnn : (n : ℝ) ^ n ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  field_simp
  try ring

theorem tail_query_moment_ne_zero (n : ℕ) (hn : 0 < n) :
    cubeSum n n ≠ 0 := by
  rw [cubeSum_diag]
  have h1 : (0 : ℝ) < 2 ^ n := by positivity
  have h2 : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  positivity

#print axioms cubeSum_succ
#print axioms cubeSum_below_diag
#print axioms cubeSum_diag
#print axioms tail_query_moment
#print axioms tail_query_moment_ne_zero

end CIGAMF.P13.PaperBAttainment
