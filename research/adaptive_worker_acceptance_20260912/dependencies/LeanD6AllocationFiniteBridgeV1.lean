import «LeanD6ExpandedMeasurementsV1»
import «LeanD6ExpandedAllocationV1»
import Aesop

/-! Finite-sum bridge from actual D6 worlds and queries to the analytic
allocation certificate. No averaging or observation identities are hypotheses. -/
namespace CIGAMF.P13.D6AllocationFiniteBridge
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

def hit (G : Finset (I n)) (i : I n) : ℝ := if i ∈ G then 1 else 0

theorem hit_sq (G : Finset (I n)) (i : I n) : (hit G i)^2=hit G i := by
  unfold hit; split <;> norm_num

theorem sum_hit (G H : Finset (I n)) : ∑ i ∈ H, hit G i = ((G ∩ H).card : ℝ) := by
  simp [hit, inter_comm]

/-- Exact second moment over the finite product A x B. -/
theorem product_second_moment (A B G : Finset (I n)) (u v : ℝ) :
    (∑ a ∈ A, ∑ b ∈ B, (u+v*(hit G a-hit G b))^2) =
      (A.card : ℝ)*B.card*u^2 + 2*u*v*((B.card : ℝ)*(G ∩ A).card-(A.card : ℝ)*(G ∩ B).card) +
        v^2*((B.card : ℝ)*(G ∩ A).card+(A.card : ℝ)*(G ∩ B).card-
          2*((G ∩ A).card : ℝ)*(G ∩ B).card) := by
  have he : ∀ a b, (u+v*(hit G a-hit G b))^2 =
      u^2+2*u*v*hit G a-2*u*v*hit G b+v^2*hit G a+v^2*hit G b-
        2*v^2*hit G a*hit G b := by
    intro a b
    by_cases ha : a ∈ G <;> by_cases hb : b ∈ G <;> simp [hit, ha, hb] <;> ring
  simp_rw [he]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul,
    sum_const, nsmul_eq_mul, sum_hit]
  ring

def swapped (A : Finset (I n)) (a b : I n) : Finset (I n) := insert b (A.erase a)

theorem others_not_mem (A : Finset (I n)) (j b : I n) (hb : b ∈ others A j) :
    b ∉ A ∧ b ≠ j := by simpa [others, and_comm] using hb

theorem swapped_j_not (A : Finset (I n)) (j a b : I n) (hj : j ∉ A)
    (hb : b ∈ others A j) : j ∉ swapped A a b := by
  have hh := others_not_mem A j b hb
  simp [swapped, hj, Ne.symm hh.2]

theorem swapped_card (A : Finset (I n)) (j a b : I n) (ha : a ∈ A)
    (hb : b ∈ others A j) : (swapped A a b).card=A.card := by
  have hh := others_not_mem A j b hb
  rw [swapped, card_insert_of_notMem (by simp [hh.1])]
  exact card_erase_add_one ha

theorem swapped_ne (A : Finset (I n)) (j a b : I n) (hb : b ∈ others A j) :
    swapped A a b ≠ A := by
  have hh := others_not_mem A j b hb
  intro he
  have hmem : b ∈ swapped A a b := by simp [swapped]
  rw [he] at hmem
  exact hh.1 hmem

theorem others_swapped (A : Finset (I n)) (j a b : I n) (hj : j ∉ A)
    (ha : a ∈ A) (hb : b ∈ others A j) :
    others (swapped A a b) j=insert a ((others A j).erase b) := by
  have hh := others_not_mem A j b hb
  have haj : a ≠ j := by intro he; subst a; exact hj ha
  have hab : a ≠ b := by intro he; subst a; exact hh.1 ha
  ext i
  by_cases hia : i=a
  · subst i
    simp [others, swapped, ha, haj, hab]
  · by_cases hib : i=b
    · subst i
      simp [others, swapped, hh.1, hh.2, hia]
    · simp [others, swapped, hia, hib]

/-- A world swap changes the actual B count by two membership indicators. -/
theorem swapped_query_count (A G : Finset (I n)) (j a b : I n) (hj : j ∉ A)
    (ha : a ∈ A) (hb : b ∈ others A j) :
    ((G ∩ others (swapped A a b) j).card : ℝ) =
      (G ∩ others A j).card+hit G a-hit G b := by
  rw [others_swapped A j a b hj ha hb, ← sum_hit]
  have han : a ∉ (others A j).erase b := by simp [others, ha]
  rw [sum_insert han]
  have he := sum_erase_add (others A j) (hit G) hb
  rw [sum_hit G (others A j)] at he
  linarith

def query (G : Finset (I n)) (j : I n) (h : Bool) : I n → Bool :=
  if h then jointCorner G j else plainCorner G

theorem actual_query_mean (A G : Finset (I n)) (j : I n) (h : Bool)
    (hj : j ∉ A) (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (mu : ℝ) :
    world A j mu (query G j h) =
      (if h then 0 else 1)+(1-mu)*(((G ∩ others A j).card : ℝ)-bit h) := by
  cases h
  · simp only [query, Bool.false_eq_true, ↓reduceIte, bit_false]
    rw [actual_unanchored_measurement A G j hjG (hG rfl)]
    ring
  · simp only [query, ↓reduceIte, bit_true]
    rw [joint_measurement A G j hj]
    ring

def queryKL (A A' G : Finset (I n)) (j : I n) (h : Bool) (mu nu : ℝ) : ℝ :=
  (world A j mu (query G j h)-world A' j nu (query G j h))^2/2

/-- Pointwise KL identity evaluated on the actual two threshold worlds. -/
theorem actual_swapped_query_KL (A G : Finset (I n)) (j a b : I n) (h : Bool)
    (hj : j ∉ A) (ha : a ∈ A) (hb : b ∈ others A j)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (z : ℝ) :
    8*queryKL A (swapped A a b) G j h (1/2) (1-(1+z)/2) =
      (z*(((G ∩ others A j).card : ℝ)-bit h)+(1+z)*(hit G a-hit G b))^2 := by
  unfold queryKL
  rw [actual_query_mean A G j h hj hjG hG,
    actual_query_mean (swapped A a b) G j h (swapped_j_not A j a b hj hb) hjG hG,
    swapped_query_count A G j a b hj ha hb]
  ring

/-- The analytic dual polynomial IS the sum over the actual adjacent worlds.
Each indexed world is a distinct-from-A, same-cardinality admissible swap. -/
theorem actual_dual_sum (A G : Finset (I n)) (j : I n) (h : Bool) (q z : ℝ)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) :
    8*(∑ a ∈ A, ∑ b ∈ others A j,
      queryKL A (swapped A a b) G j h (1/2) (1-(1+z)/2)) =
      CIGAMF.P13.D6ExpandedAllocation.dual q z (bit h)
        (G ∩ A).card (G ∩ others A j).card := by
  rw [mul_sum]
  have he : (∑ a ∈ A, 8*(∑ b ∈ others A j,
      queryKL A (swapped A a b) G j h (1/2) (1-(1+z)/2))) =
      ∑ a ∈ A, ∑ b ∈ others A j,
        (z*(((G ∩ others A j).card : ℝ)-bit h)+(1+z)*(hit G a-hit G b))^2 := by
    apply sum_congr rfl
    intro a ha
    rw [mul_sum]
    apply sum_congr rfl
    intro b hb
    exact actual_swapped_query_KL A G j a b h hj ha hb hjG hG z
  rw [he, product_second_moment, hA, hB]
  unfold CIGAMF.P13.D6ExpandedAllocation.dual
  ring

#print axioms product_second_moment
#print axioms swapped_query_count
#print axioms actual_query_mean
#print axioms actual_swapped_query_KL
#print axioms actual_dual_sum
end
end CIGAMF.P13.D6AllocationFiniteBridge
