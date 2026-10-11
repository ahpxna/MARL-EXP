import Mathlib

/-! N1: exact information rate for a two-action incumbent (0,1) and a
K-action flat outsider. Dual certificate uses the two least-sampled cells;
no informal symmetry/WLOG step or padded actions is assumed. -/
namespace CIGAMF.P13.FunctionalFlatOutsiderRate
open scoped BigOperators
open Finset
noncomputable section

lemma two_small_cells {K : ℕ} (hK : 2 ≤ K) (w : Fin K → ℝ) :
    ∃ a b, a ≠ b ∧ (K : ℝ)*(w a+w b) ≤ 2*∑ i,w i := by
  haveI : Nonempty (Fin K) := ⟨⟨0,by omega⟩⟩
  obtain ⟨a,ha,hmin⟩ := exists_min_image univ w univ_nonempty
  have hn : (univ.erase a : Finset (Fin K)).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem ha]
    simp only [card_univ,Fintype.card_fin]
    omega
  obtain ⟨b,hb,hminb⟩ := exists_min_image (univ.erase a) w hn
  have hba : b ≠ a := (mem_erase.mp hb).1
  have habw : w a ≤ w b := hmin b (mem_univ b)
  have hs := sum_le_sum (fun i (hi : i ∈ univ.erase a) => hminb i hi)
  have he := sum_erase_add univ w ha
  have hc : (univ.erase a : Finset (Fin K)).card=K-1 := by simp
  simp only [sum_const,nsmul_eq_mul,hc] at hs
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hcR : ((K-1 : ℕ) : ℝ)=(K:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hcR] at hs
  refine ⟨a,b,Ne.symm hba,?_⟩
  nlinarith [mul_nonneg (show (0:ℝ) ≤ K-2 by linarith) (sub_nonneg.mpr habw)]

def Alternative {K : ℕ} (x y : ℝ) (z : Fin K → ℝ) : Prop :=
  ∃ a b, a ≠ b ∧ |y-x| ≤ z a-z b

def energy {K : ℕ} (p t : ℝ) (w : Fin K → ℝ) (x y : ℝ) (z : Fin K → ℝ) : ℝ :=
  (p*x^2+t*(y-1)^2+∑ i,w i*(z i)^2)/2

def rate (s : ℝ) : ℝ := 1/(2*(2+s)^2)

def uniformEnergy {K : ℕ} (s x y : ℝ) (z : Fin K → ℝ) : ℝ :=
  (x^2+(y-1)^2)/(2*(2+s))+(∑ i,(z i)^2)/(s*(2+s))

lemma two_cell_square {K : ℕ} (z : Fin K → ℝ) (a b : Fin K) (hab : a ≠ b) :
    (z a-z b)^2/2 ≤ ∑ i,(z i)^2 := by
  have hh := sum_le_sum_of_subset_of_nonneg (s := ({a,b}:Finset (Fin K))) (t := univ)
    (subset_univ _) (fun i _ _ => sq_nonneg (z i))
  have hs : (z a)^2+(z b)^2 ≤ ∑ i,(z i)^2 := by simpa [hab] using hh
  nlinarith [sq_nonneg (z a+z b)]

lemma weighted_square_lower (s u d : ℝ) (hs : 0 < s) (h : 1 ≤ u+d) :
    rate s ≤ u^2/(4*(2+s))+d^2/(2*s*(2+s)) := by
  have hH : 0 < 2+s := by linarith
  have hn : 0 ≤ (u+d)^2-1 := by nlinarith
  have hpos := mul_nonneg (show 0 ≤ 2*s by positivity) hn
  unfold rate
  field_simp
  nlinarith [sq_nonneg (s*u-2*d)]

theorem uniform_lower {K : ℕ} (s : ℝ) (hs : 0 < s)
    (x y : ℝ) (z : Fin K → ℝ) (ha : Alternative x y z) :
    rate s ≤ uniformEnergy s x y z := by
  obtain ⟨a,b,hab,hgap⟩ := ha
  have hsum : 1 ≤ (x-(y-1))+(z a-z b) := by
    have hh := (le_abs_self (y-x)).trans hgap
    linarith
  have hi : (x-(y-1))^2/2 ≤ x^2+(y-1)^2 := by
    nlinarith [sq_nonneg (x+(y-1))]
  have hj := two_cell_square z a b hab
  have hH : 0 < 2+s := by linarith
  have hl := add_le_add (div_le_div_of_nonneg_right hi (by positivity : 0 ≤ 2*(2+s)))
    (div_le_div_of_nonneg_right hj (by positivity : 0 ≤ s*(2+s)))
  have hlo := weighted_square_lower s (x-(y-1)) (z a-z b) hs hsum
  have he : (x-(y-1))^2/2/(2*(2+s))+(z a-z b)^2/2/(s*(2+s)) =
      (x-(y-1))^2/(4*(2+s))+(z a-z b)^2/(2*s*(2+s)) := by field_simp <;> ring
  rw [he] at hl
  exact hlo.trans hl

lemma explicit_pair {K : ℕ} (a b : Fin K) (hab : a ≠ b) (s : ℝ) (hs : 0 < s) :
    let z : Fin K → ℝ := fun i => (if i=a then s/(2*(2+s)) else 0) -
      (if i=b then s/(2*(2+s)) else 0)
    Alternative (1/(2+s)) (1-1/(2+s)) z := by
  dsimp
  refine ⟨a,b,hab,?_⟩
  have hH : 0 < 2+s := by linarith
  have he : 1-1/(2+s)-1/(2+s)=s/(2+s) := by field_simp; ring
  rw [he,abs_of_nonneg (by positivity)]
  simp [hab,hab.symm]
  <;> field_simp
  <;> ring_nf
  <;> norm_num

lemma explicit_pair_energy {K : ℕ} (a b : Fin K) (hab : a ≠ b) (s p t : ℝ) (hs : 0 < s)
    (w : Fin K → ℝ) :
    let z : Fin K → ℝ := fun i => (if i=a then s/(2*(2+s)) else 0) -
      (if i=b then s/(2*(2+s)) else 0)
    energy p t w (1/(2+s)) (1-1/(2+s)) z =
      (p+t)/(2*(2+s)^2)+(w a+w b)*s^2/(8*(2+s)^2) := by
  dsimp [energy]
  have hH : 0 < 2+s := by linarith
  have hf : ∀ i : Fin K, w i*((if i=a then s/(2*(2+s)) else 0)-
      (if i=b then s/(2*(2+s)) else 0))^2 =
      (if i=a then w a*s^2/(4*(2+s)^2) else 0)+
      (if i=b then w b*s^2/(4*(2+s)^2) else 0) := by
    intro i
    by_cases hia : i=a
    · subst i; simp [hab]; field_simp <;> ring
    · by_cases hib : i=b
      · subst i; simp [hab.symm]; field_simp <;> ring
      · simp [hia,hib]
  simp_rw [hf]
  rw [sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true]
  field_simp
  <;> ring

theorem arbitrary_allocation_upper {K : ℕ} (hK : 2 ≤ K) (s : ℝ) (hs : 0 < s)
    (hsq : s^2=2*K) (p t : ℝ) (w : Fin K → ℝ) (hm : p+t+∑ i,w i=1) :
    ∃ x y z, Alternative x y z ∧ energy p t w x y z ≤ rate s := by
  obtain ⟨a,b,hab,hpair⟩ := two_small_cells hK w
  let z : Fin K → ℝ := fun i => (if i=a then s/(2*(2+s)) else 0)-
    (if i=b then s/(2*(2+s)) else 0)
  refine ⟨1/(2+s),1-1/(2+s),z,explicit_pair a b hab s hs,?_⟩
  rw [explicit_pair_energy a b hab s p t hs w]
  unfold rate
  have hH : 0 < (2+s)^2 := by positivity
  have he : (p+t)/(2*(2+s)^2)+(w a+w b)*s^2/(8*(2+s)^2) =
      (4*(p+t)+(w a+w b)*s^2)/(8*(2+s)^2) := by field_simp <;> ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [hsq]
  have hp : 4*(p+t)+2*(K:ℝ)*(w a+w b) ≤ 4 := by linarith
  nlinarith [mul_nonneg hH.le (show 0 ≤ 4-(4*(p+t)+2*(K:ℝ)*(w a+w b)) by linarith)]

theorem uniform_allocation {K : ℕ} (s : ℝ) (hs : 0 < s) (hsq : s^2=2*K) :
    0 < 1/(2+s) ∧ (∀ _i : Fin K,0 < 2/(s*(2+s))) ∧
      1/(2+s)+1/(2+s)+(∑ _i : Fin K,2/(s*(2+s)))=1 ∧
      (∀ x y z, energy (1/(2+s)) (1/(2+s)) (fun _ : Fin K => 2/(s*(2+s))) x y z =
        uniformEnergy s x y z) := by
  have hH : 0 < 2+s := by linarith
  refine ⟨by positivity,fun _ => by positivity,?_,?_⟩
  · simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    nlinarith [hsq]
  · intro x y z
    unfold energy uniformEnergy
    rw [← mul_sum]
    field_simp
    <;> ring

#print axioms two_small_cells
#print axioms uniform_lower
#print axioms arbitrary_allocation_upper
#print axioms uniform_allocation
end
end CIGAMF.P13.FunctionalFlatOutsiderRate
