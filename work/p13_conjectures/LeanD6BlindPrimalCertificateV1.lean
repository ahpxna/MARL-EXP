import «LeanD6BlindSaddleCertificateV1»

/-! Construct the blind two-orbit primal weight from the interior crossing.
The all-distances guard is proved, not assumed. Actual query averaging is
connected separately in LeanD6BlindActualMomentsV1. -/
namespace CIGAMF.P13.D6BlindPrimalCertificate
open CIGAMF.P13.D6BlindSaddleCertificate
noncomputable section

def v0 (q : ℝ) := q/(2*q+1)
def top (q : ℝ) := q*(q^2+1)/(2*(2*q+1))
def kap (q : ℝ) := (q+1)/(2*(2*q+1))
def den (q mu a : ℝ) := (top q-v0 q)*a+(1-mu)*kap q+mu/(2*q+1)
def weight (q mu a : ℝ) := (mu/(2*q+1)-v0 q*a)/den q mu a
def V (q w : ℝ) := (1-w)*v0 q+w*top q
def B (q mu w : ℝ) := (1-w)*mu/(2*q+1)-w*(1-mu)*kap q
def C (q mu w : ℝ) := (1-w)*mu^2/(2*q+1)+w*(1-mu)^2*kap q

theorem weight_properties (q mu a : ℝ) (hq : 3 ≤ q) (hm : 0 < mu) (hm1 : mu < 1)
    (ha : 0 < a) (haq : a < mu/q) :
    0 < weight q mu a ∧ weight q mu a < 1 ∧
      0 < V q (weight q mu a) ∧ B q mu (weight q mu a)=V q (weight q mu a)*a := by
  have hq0 : 0 < q := by linarith
  have hn : 0 < 2*q+1 := by linarith
  have hv : 0 < v0 q := by unfold v0; positivity
  have ht : 0 < top q := by unfold top; positivity
  have hk : 0 < kap q := by unfold kap; positivity
  have hdiff : 0 < top q-v0 q := by
    have he : top q-v0 q=q*(q^2-1)/(2*(2*q+1)) := by unfold top v0; field_simp; ring
    rw [he]
    have hq2 : 0 < q^2-1 := by nlinarith
    positivity
  have hlam : 0 < 1-mu := by linarith
  have hden : 0 < den q mu a := by unfold den; positivity
  have hnum : 0 < mu/(2*q+1)-v0 q*a := by
    have hqa : q*a < mu := by nlinarith only [(lt_div_iff₀ hq0).mp haq]
    have he : mu/(2*q+1)-v0 q*a=(mu-q*a)/(2*q+1) := by unfold v0; ring
    rw [he]; exact div_pos (sub_pos.mpr hqa) hn
  have hw : 0 < weight q mu a := div_pos hnum hden
  have hw1 : weight q mu a < 1 := by
    unfold weight
    apply (div_lt_one hden).mpr
    have he : den q mu a-(mu/(2*q+1)-v0 q*a)=top q*a+(1-mu)*kap q := by unfold den; ring
    have hp : 0 < top q*a+(1-mu)*kap q := by positivity
    linarith only [he,hp]
  have hvw : 0 < V q (weight q mu a) := by
    unfold V
    have hwc : 0 < 1-weight q mu a := by linarith
    positivity
  refine ⟨hw,hw1,hvw,?_⟩
  have he : weight q mu a*den q mu a=mu/(2*q+1)-v0 q*a :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  calc
    B q mu (weight q mu a) = V q (weight q mu a)*a+
        (mu/(2*q+1)-v0 q*a-weight q mu a*den q mu a) := by unfold B V den; ring
    _ = V q (weight q mu a)*a := by rw [he]; ring

/-- Every exchange distance is controlled by the constructed weight. -/
theorem constructed_guard (q mu a : ℝ) (hq : 3 ≤ q) (hm : 0 < mu) (hm1 : mu < 1)
    (ha : 0 < a) (haq : a < mu/q) :
    (q+1)*(B q mu (weight q mu a))^2 ≤
      2*V q (weight q mu a)*C q mu (weight q mu a) := by
  let w := weight q mu a
  have hp := weight_properties q mu a hq hm hm1 ha haq
  have hw : 0 ≤ w := hp.1.le
  have hwc : 0 ≤ 1-w := by dsimp [w]; linarith only [hp.2.1]
  have hv : 0 < V q w := hp.2.2.1
  have hbalance : B q mu w=V q w*a := hp.2.2.2
  have hn : 0 < 2*q+1 := by linarith
  have hlam : 0 ≤ 1-mu := by linarith
  have hk : 0 ≤ kap q := by unfold kap; positivity
  have hb : V q w*a ≤ (1-w)*mu/(2*q+1) := by
    rw [← hbalance]
    unfold B
    have ht : 0 ≤ w*(1-mu)*kap q := by positivity
    linarith only [ht]
  have hc : (1-w)*mu^2/(2*q+1) ≤ C q mu w := by
    unfold C
    have ht : 0 ≤ w*(1-mu)^2*kap q := by positivity
    linarith only [ht]
  have has : (q+1)*a ≤ 2*mu := by
    have hqa := (lt_div_iff₀ (by linarith : 0 < q)).mp haq
    nlinarith [mul_nonneg (by linarith : 0 ≤ q-1) ha.le]
  have hfirst := mul_le_mul_of_nonneg_left hb (show 0 ≤ (q+1)*a by positivity)
  have hsecond := mul_le_mul_of_nonneg_right has (show 0 ≤ (1-w)*mu/(2*q+1) by positivity)
  have hid : 2*mu*((1-w)*mu/(2*q+1))=2*((1-w)*mu^2/(2*q+1)) := by ring
  have hbnd : (q+1)*V q w*a^2 ≤ 2*C q mu w := by
    rw [hid] at hsecond
    nlinarith only [hfirst,hsecond,hc]
  have hh := mul_le_mul_of_nonneg_left hbnd hv.le
  rw [hbalance]
  nlinarith only [hh]

theorem value_identity (q mu a : ℝ) (hq : 3 ≤ q) (hm : 0 < mu) (hm1 : mu < 1)
    (ha : 0 < a) (haq : a < mu/q) (hcross : jointTop q (1-mu) a=scalar q mu a) :
    C q mu (weight q mu a)-(B q mu (weight q mu a))^2/(2*V q (weight q mu a))=
      scalar q mu a := by
  let w := weight q mu a
  have hp := weight_properties q mu a hq hm hm1 ha haq
  have he : (1-w)*scalar q mu a+w*jointTop q (1-mu) a=
      V q w*a^2/2-B q mu w*a+C q mu w := by
    unfold scalar jointTop V B C v0 top kap
    ring
  rw [hcross] at he
  have hbal : B q mu w=V q w*a := hp.2.2.2
  have hv : V q w ≠ 0 := ne_of_gt hp.2.2.1
  change C q mu w-(B q mu w)^2/(2*V q w)=_
  rw [hbal]
  have hd : (V q w*a)^2/(2*V q w)=V q w*a^2/2 := by field_simp
  rw [hd]
  rw [hbal] at he
  nlinarith only [he]

/-- Existence of a valid blind primal and a feasible adjacent nuisance, with
matching value against all continuous shifts and all distances 1 <= d <= q. -/
theorem constructed_primal (q mu : ℝ) (hq : 3 ≤ q) (hm : 0 < mu) (hm1 : mu < 1)
    (hhigh : (q+1)*(1-mu)^2 < 2*mu^2) :
    ∃ a w : ℝ,0 < a ∧ a < mu/q ∧ 0 < w ∧ w < 1 ∧ 0 < mu-a ∧ mu-a < 1 ∧
      jointTop q (1-mu) a=scalar q mu a ∧
      (∀ d z : ℝ,1 ≤ d → d ≤ q → scalar q mu a ≤ V q w*z^2/2+d*B q mu w*z+d*C q mu w) ∧
      V q w*(-a)^2/2+B q mu w*(-a)+C q mu w=scalar q mu a := by
  obtain ⟨a,ha,haq,hcross⟩ := crossing_exists q mu hq hm hm1 hhigh
  let w := weight q mu a
  have hp := weight_properties q mu a hq hm hm1 ha haq
  have hid := value_identity q mu a hq hm hm1 ha haq hcross
  have hguard := constructed_guard q mu a hq hm hm1 ha haq
  have hamu : a < mu := by
    have hqa := (lt_div_iff₀ (by linarith : 0 < q)).mp haq
    nlinarith [mul_nonneg (by linarith : 0 ≤ q-1) ha.le]
  refine ⟨a,w,ha,haq,hp.1,hp.2.1,by linarith,by linarith,hcross,?_,?_⟩
  · intro d z hd hdq
    rw [← hid]
    exact all_distances_lower q (V q w) (B q mu w) (C q mu w) d z hp.2.2.1 hd hdq hguard
  · have he : V q w*(-a)^2/2+B q mu w*(-a)+C q mu w=
        (1-w)*scalar q mu a+w*jointTop q (1-mu) a := by
      unfold V B C v0 top kap scalar jointTop
      ring
    rw [he,hcross]
    ring

#print axioms weight_properties
#print axioms constructed_guard
#print axioms value_identity
#print axioms constructed_primal
end
end CIGAMF.P13.D6BlindPrimalCertificate
