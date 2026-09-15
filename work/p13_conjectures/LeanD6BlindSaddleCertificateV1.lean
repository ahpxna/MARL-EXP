import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

/-! Symbolic certificate pieces for the blind-allocation game. These formulas
still require a bridge from symmetric actual-query moments. No adaptive
minimax theorem or asymptotic claim is asserted here. -/
namespace CIGAMF.P13.D6BlindSaddleCertificate
noncomputable section

def scalar (q mu a : ℝ) := (q*a^2/2-mu*a+mu^2)/(2*q+1)
def jointTop (q lam a : ℝ) := q*(q^2+1)/(2*(2*q+1))*a^2/2+
  (q+1)/(2*(2*q+1))*(lam^2+lam*a)
def jointMoment (q u h : ℝ) := u*((q-1)*u+q+1)/(2*(2*q+1))-2*h*u*q/(2*q+1)+h
def crossing (q mu a : ℝ) := jointTop q (1-mu) a-scalar q mu a

lemma moment_off_difference (q u : ℝ) (hq : 2*q+1 ≠ 0) :
    q*(q^2+1)/(2*(2*q+1))-jointMoment q u 0 =
      (q-u)*((q-1)*(q+u)+q+1)/(2*(2*q+1)) := by
  unfold jointMoment
  field_simp
  <;> ring

lemma moment_on_difference (q u : ℝ) (hq : q ≠ 0) (hn : 2*q+1 ≠ 0) :
    q*(q^2+1)/(2*(2*q+1))-jointMoment q u 1 =
      (q-u)/q*(q*(q^2+1)/(2*(2*q+1))-1)+
      u/q*(2*q^2/(2*q+1)-1)+(q-1)*u*(q-u)/(2*(2*q+1)) := by
  unfold jointMoment
  field_simp
  <;> ring

/-- Every legal switch/size orbit is bounded by the q-off second moment. -/
theorem moment_upper (q u h : ℝ) (hq : 3 ≤ q) (hu : 0 ≤ u) (huq : u ≤ q)
    (hh : h=0 ∨ h=1) : jointMoment q u h ≤ q*(q^2+1)/(2*(2*q+1)) := by
  have hn : 0 < 2*q+1 := by linarith
  have hqu : 0 ≤ q-u := sub_nonneg.mpr huq
  have hqm : 0 ≤ q-1 := by linarith
  rcases hh with rfl | rfl
  · have he := moment_off_difference q u (ne_of_gt hn)
    have hp : 0 ≤ (q-u)*((q-1)*(q+u)+q+1)/(2*(2*q+1)) := by positivity
    linarith only [he,hp]
  · have ht : 1 ≤ q*(q^2+1)/(2*(2*q+1)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have hq2 : 9 ≤ q^2 := by nlinarith
      nlinarith [mul_nonneg (by linarith : 0 ≤ q) (by linarith : 0 ≤ q^2-9)]
    have hs : 1 ≤ 2*q^2/(2*q+1) := by
      apply (le_div_iff₀ hn).mpr
      nlinarith
    have ht0 : 0 ≤ q*(q^2+1)/(2*(2*q+1))-1 := sub_nonneg.mpr ht
    have hs0 : 0 ≤ 2*q^2/(2*q+1)-1 := sub_nonneg.mpr hs
    have he := moment_on_difference q u (by linarith) (ne_of_gt hn)
    have hp : 0 ≤ (q-u)/q*(q*(q^2+1)/(2*(2*q+1))-1)+
        u/q*(2*q^2/(2*q+1)-1)+(q-1)*u*(q-u)/(2*(2*q+1)) := by positivity
    linarith only [he,hp]

/-- The combinatorial variance coefficient is also maximized by size q. -/
theorem variance_upper (q u : ℝ) (hq : 3 ≤ q) (hu : 0 ≤ u) (huq : u ≤ q) :
    u*(2*q+1-u)/((2*q+1)*(2*q)) ≤ (q+1)/(2*(2*q+1)) := by
  have hn : 0 < (2*q+1)*(2*q) := by positivity
  have he : (q+1)/(2*(2*q+1))-u*(2*q+1-u)/((2*q+1)*(2*q)) =
      (q-u)*(q+1-u)/((2*q+1)*(2*q)) := by field_simp <;> ring
  have hqu : 0 ≤ q-u := sub_nonneg.mpr huq
  have hqu1 : 0 ≤ q+1-u := by linarith
  have hp : 0 ≤ (q-u)*(q+1-u)/((2*q+1)*(2*q)) := by positivity
  linarith only [he,hp]

/-- All legal joint-query losses lie below the candidate dual value. -/
theorem all_joint_upper (q lam a u h : ℝ) (hq : 3 ≤ q) (hl : 0 ≤ lam) (ha : 0 ≤ a)
    (hu : 0 ≤ u) (huq : u ≤ q) (hh : h=0 ∨ h=1) :
    jointMoment q u h*a^2/2+u*(2*q+1-u)/((2*q+1)*(2*q))*(lam^2+lam*a) ≤
      jointTop q lam a := by
  have ht := mul_le_mul_of_nonneg_right (moment_upper q u h hq hu huq hh) (sq_nonneg a)
  have hk := mul_le_mul_of_nonneg_right (variance_upper q u hq hu huq)
    (show 0 ≤ lam^2+lam*a by positivity)
  unfold jointTop
  linarith only [ht,hk]

/-- Completion of squares controls every alternative distance continuously. -/
theorem all_distances_lower (q V B C d z : ℝ) (hV : 0 < V)
    (hd : 1 ≤ d) (hdq : d ≤ q) (guard : (q+1)*B^2 ≤ 2*V*C) :
    C-B^2/(2*V) ≤ V*z^2/2+d*B*z+d*C := by
  have he : V*z^2/2+d*B*z+d*C-(C-B^2/(2*V)) =
      (V*z+d*B)^2/(2*V)+(d-1)*(C-(d+1)*B^2/(2*V)) := by
    field_simp
    <;> ring
  have hg : (d+1)*B^2 ≤ 2*V*C := by
    have h := mul_le_mul_of_nonneg_right hdq (sq_nonneg B)
    linarith only [h,guard]
  have hg' : 0 ≤ C-(d+1)*B^2/(2*V) := by
    have h : (d+1)*B^2/(2*V) ≤ C :=
      (div_le_iff₀ (by positivity : 0 < 2*V)).mpr (by nlinarith only [hg])
    linarith only [h]
  have hd0 : 0 ≤ d-1 := sub_nonneg.mpr hd
  have hp : 0 ≤ (V*z+d*B)^2/(2*V)+(d-1)*(C-(d+1)*B^2/(2*V)) := by positivity
  linarith only [he,hp]

lemma crossing_at_zero (q mu : ℝ) (hq : 3 ≤ q)
    (hm : (q+1)*(1-mu)^2 < 2*mu^2) : crossing q mu 0 < 0 := by
  unfold crossing jointTop scalar
  simp only [sq, mul_zero,zero_mul,zero_div,sub_zero,zero_add,add_zero]
  have hn : 0 < 2*(2*q+1) := by positivity
  have he : (q+1)/(2*(2*q+1))*((1-mu)*(1-mu))-mu*mu/(2*q+1) =
      ((q+1)*(1-mu)^2-2*mu^2)/(2*(2*q+1)) := by field_simp <;> ring
  rw [he]
  exact div_neg_of_neg_of_pos (by linarith) hn

lemma crossing_at_bracket (q mu : ℝ) (hq : 3 ≤ q) (hm : 0 < mu) (hm1 : mu < 1) :
    0 < crossing q mu (mu/q) := by
  have hn : 0 < 2*q+1 := by linarith
  have he : (2*q+1)*crossing q mu (mu/q) =
      mu^2*(q-1)*(q-3)/(4*q)+(1-mu)*mu*(q+1)/(2*q)+(1-mu)^2*(q+1)/2 := by
    unfold crossing jointTop scalar
    field_simp
    <;> ring
  have hqm1 : 0 ≤ q-1 := by linarith
  have hqm3 : 0 ≤ q-3 := by linarith
  have hmu1 : 0 < 1-mu := sub_pos.mpr hm1
  have h1 : 0 ≤ mu^2*(q-1)*(q-3)/(4*q) := by positivity
  have h2 : 0 < (1-mu)*mu*(q+1)/(2*q) := by positivity
  have h3 : 0 ≤ (1-mu)^2*(q+1)/2 := by positivity
  have hp : 0 < (2*q+1)*crossing q mu (mu/q) := by linarith only [he,h1,h2,h3]
  exact (mul_pos_iff.mp hp).resolve_right (by intro h; linarith [h.1]) |>.2

/-- A positive interior crossing exists on an entire high-margin interval. -/
theorem crossing_exists (q mu : ℝ) (hq : 3 ≤ q) (hm : 0 < mu) (hm1 : mu < 1)
    (hhigh : (q+1)*(1-mu)^2 < 2*mu^2) :
    ∃ a : ℝ, 0 < a ∧ a < mu/q ∧ jointTop q (1-mu) a=scalar q mu a := by
  have h0 := crossing_at_zero q mu hq hhigh
  have h1 := crossing_at_bracket q mu hq hm hm1
  have hcont : Continuous (crossing q mu) := by unfold crossing jointTop scalar; fun_prop
  obtain ⟨a,ha,he⟩ := intermediate_value_Icc
    (show (0:ℝ) ≤ mu/q by positivity) hcont.continuousOn ⟨h0.le,h1.le⟩
  refine ⟨a,?_,?_,?_⟩
  · have hne : a ≠ 0 := by intro hh; subst a; linarith only [he,h0]
    exact lt_of_le_of_ne ha.1 (Ne.symm hne)
  · have hne : a ≠ mu/q := by intro hh; rw [hh] at he; linarith only [he,h1]
    exact lt_of_le_of_ne ha.2 hne
  · unfold crossing at he
    linarith only [he]

#print axioms moment_upper
#print axioms variance_upper
#print axioms all_joint_upper
#print axioms all_distances_lower
#print axioms crossing_exists
end
end CIGAMF.P13.D6BlindSaddleCertificate
