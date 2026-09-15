import «LeanD6CyclicOptimalV1»

/-! Exact integer allocation between two independent named block designs.
This is an optimum over mixtures of cyclic and three-group blocks, not over
all legal queries or adaptive procedures. The exchange condition includes
rounding loss; comparing information per query alone would not suffice. -/
namespace CIGAMF.P13.D6IntegerBlockAllocation
noncomputable section

/-- The greedy split is feasible and wastes fewer than three queries. -/
theorem greedy_feasible (N n : ℕ) (hn : 0 < n) :
    n*(N/n)+3*((N%n)/3) ≤ N ∧
    N-(n*(N/n)+3*((N%n)/3)) < 3 := by
  have h := Nat.mod_add_div N n
  have hr := Nat.mod_add_div (N%n) 3
  have hm := Nat.mod_lt (N%n) (by omega : 0 < 3)
  omega

/-- Removing one long block cannot pay for enough short blocks to improve
information, including the possible two-query rounding advantage. -/
theorem greedy_information_optimal (N n L b : ℕ) (hn : 0 < n)
    (Ic It : ℝ) (ht : 0 ≤ It) (hex : ((n:ℝ)+2)*It ≤ 3*Ic)
    (hbudget : n*L+3*b ≤ N) :
    (L:ℝ)*Ic+(b:ℝ)*It ≤ (N/n:ℕ)*Ic+((N%n)/3:ℕ)*It := by
  have hL : L ≤ N/n := (Nat.le_div_iff_mul_le hn).mpr (by nlinarith [hbudget])
  have hN : (n:ℝ)*(N/n:ℕ)+(N%n:ℕ)=N := by
    exact_mod_cast (show n*(N/n)+N%n=N by nlinarith [Nat.mod_add_div N n])
  have hr : (N%n:ℕ) ≤ (3:ℝ)*((N%n)/3:ℕ)+2 := by
    have hh := Nat.mod_add_div (N%n) 3
    have hm := Nat.mod_lt (N%n) (by omega : 0 < 3)
    exact_mod_cast (show N%n ≤ 3*((N%n)/3)+2 by omega)
  have hb : (n:ℝ)*(L:ℝ)+3*(b:ℝ) ≤ N := by exact_mod_cast hbudget
  by_cases he : L=N/n
  · have hsmall : b ≤ (N%n)/3 := by
      have hh := Nat.mod_add_div N n
      have hh' := Nat.mod_add_div (N%n) 3
      have hm := Nat.mod_lt (N%n) (by omega : 0 < 3)
      subst L
      omega
    have hh := mul_le_mul_of_nonneg_right (show (b:ℝ) ≤ ((N%n)/3:ℕ) by exact_mod_cast hsmall) ht
    rw [he]
    linarith
  · have hd : (1:ℝ) ≤ (N/n:ℕ)-(L:ℝ) := by
      have hh : L+1 ≤ N/n := by omega
      have hh' : (L:ℝ)+1 ≤ (N/n:ℕ) := by exact_mod_cast hh
      linarith
    have hgain : 3*((b:ℝ)-((N%n)/3:ℕ)) ≤ ((n:ℝ)+2)*((N/n:ℕ)-(L:ℝ)) := by
      nlinarith
    have hgain' := mul_le_mul_of_nonneg_right hgain ht
    have hex' := mul_le_mul_of_nonneg_right hex (by linarith : (0:ℝ) ≤ (N/n:ℕ)-(L:ℝ))
    nlinarith

def cyclicInformation (q : ℕ) : ℝ := (q:ℝ)^4/(2*q+1)
def threeInformation (q : ℕ) : ℝ := (q:ℝ)^2/3

/-- The actual D6 information coefficients satisfy the stronger exchange
condition, which accounts for wasted queries in the integer problem. -/
theorem d6_exchange (q : ℕ) (hq : 3 ≤ q) :
    (((2*q+1:ℕ):ℝ)+2)*threeInformation q ≤ 3*cyclicInformation q := by
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  unfold threeInformation cyclicInformation
  push_cast
  have hd : (0:ℝ) < 2*q+1 := by positivity
  simp only [← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  have hs : 0 ≤ ((q:ℝ)-3)^2 := sq_nonneg _
  have hf : 0 ≤ (q:ℝ)^2*(5*(q:ℝ)^2-8*q-3) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  nlinarith

/-- Global optimum at every integer budget, within the two named block
families. No finite-q or finite-budget enumeration is a hypothesis. -/
theorem d6_greedy_optimal (q N L b : ℕ) (hq : 3 ≤ q)
    (hbudget : (2*q+1)*L+3*b ≤ N) :
    (L:ℝ)*cyclicInformation q+(b:ℝ)*threeInformation q ≤
      (N/(2*q+1):ℕ)*cyclicInformation q+
        ((N%(2*q+1))/3:ℕ)*threeInformation q := by
  exact greedy_information_optimal N (2*q+1) L b (by omega)
    (cyclicInformation q) (threeInformation q) (by unfold threeInformation; positivity)
    (d6_exchange q hq) hbudget

#print axioms greedy_feasible
#print axioms greedy_information_optimal
#print axioms d6_exchange
#print axioms d6_greedy_optimal
end
end CIGAMF.P13.D6IntegerBlockAllocation
