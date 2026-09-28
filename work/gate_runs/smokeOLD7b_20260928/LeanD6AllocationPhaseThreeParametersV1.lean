import «LeanD6AllocationPhaseThreeCoreV1»

/-! The phase-III radical formula satisfies the exact balance and stationarity
identities used by the all-distance core. Margin-interval feasibility bounds
are not claimed here; all assumptions are displayed. -/
namespace CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeCore
noncomputable section

def K (q : ℝ) := q*(q-2)^2-q+1
def radicand (q mu : ℝ) := q*(q-1)*(1-mu)^2+K q*mu^2
def D (q mu : ℝ) := Real.sqrt (radicand q mu)
def shift (q mu : ℝ) := (q*(1-mu)^2-mu^2)/(q*(q-2)*(1-mu)+D q mu)
def mass (q mu : ℝ) := (q-1)*shift q mu/D q mu

theorem K_pos (q : ℝ) (hq : 3 ≤ q) : 0 < K q := by
  have hp : 0 ≤ q*((q-2)^2-1) := mul_nonneg (by linarith) (by nlinarith)
  unfold K
  nlinarith

theorem radical_positive (q mu : ℝ) (hq : 3 ≤ q) (hmu : 0 < mu) : 0 < D q mu := by
  apply Real.sqrt_pos.mpr
  unfold radicand
  have hk := K_pos q hq
  have h1 : 0 ≤ q*(q-1)*(1-mu)^2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have h2 : 0 < K q*mu^2 := mul_pos hk (sq_pos_of_pos hmu)
  linarith

theorem radical_square (q mu : ℝ) (hq : 3 ≤ q) : (D q mu)^2=radicand q mu := by
  apply Real.sq_sqrt
  unfold radicand
  have hk := (K_pos q hq).le
  exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _))
    (mul_nonneg hk (sq_nonneg _))

theorem rationalized_shift (q mu : ℝ) (hq : 3 ≤ q) (hmu : 0 < mu) (hmu1 : mu ≤ 1) :
    K q*shift q mu=q*(q-2)*(1-mu)-D q mu := by
  have hd := radical_positive q mu hq hmu
  have hp : 0 ≤ q*(q-2)*(1-mu) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hn : q*(q-2)*(1-mu)+D q mu ≠ 0 := by linarith
  have hs := radical_square q mu hq
  dsimp [radicand,K] at hs
  unfold shift K
  field_simp [hn]
  nlinarith [hs]

theorem balance (q mu : ℝ) (hq : 3 ≤ q) (hmu : 0 < mu) (hmu1 : mu ≤ 1) :
    q*((1-mu)-(q-2)*shift q mu)^2=mu^2+(q-1)*(shift q mu)^2 := by
  have he := rationalized_shift q mu hq hmu hmu1
  have hs := radical_square q mu hq
  have hk := K_pos q hq
  have he2 := congrArg (fun x : ℝ => x^2) he
  have hid : K q*(q*((1-mu)-(q-2)*shift q mu)^2-mu^2-(q-1)*(shift q mu)^2) =
      (K q*shift q mu)^2-2*(K q*shift q mu)*(q*(q-2)*(1-mu))+
        (q*(q-2)*(1-mu))^2-(D q mu)^2 := by
    rw [hs]
    unfold radicand K
    ring
  rw [he] at hid
  have hzero : K q*(q*((1-mu)-(q-2)*shift q mu)^2-mu^2-(q-1)*(shift q mu)^2)=0 := by
    nlinarith [hid]
  have hz := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hk)
  linarith

theorem stationarity (q mu : ℝ) (hq : 3 ≤ q) (hmu : 0 < mu) (hmu1 : mu ≤ 1) :
    (1-mass q mu)*(q-1)*shift q mu =
      mass q mu*q*(q-2)*((1-mu)-(q-2)*shift q mu) := by
  have he := rationalized_shift q mu hq hmu hmu1
  have hd := radical_positive q mu hq hmu
  have hrel : D q mu-(q-1)*shift q mu=q*(q-2)*((1-mu)-(q-2)*shift q mu) := by
    unfold K at he
    nlinarith
  unfold mass
  field_simp [ne_of_gt hd]
  nlinarith [congrArg (fun x : ℝ => ((q-1)*shift q mu)*x) hrel]

#print axioms K_pos
#print axioms radical_positive
#print axioms rationalized_shift
#print axioms balance
#print axioms stationarity
end
end CIGAMF.P13.D6AllocationPhaseThreeParameters
