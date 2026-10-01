from mkcert import *
from fractions import Fraction as Fr
from sym import P
import gen
one=P.c(1)
lam=P.lin(1,-1)
ellL1={(1,0):-lam,(1,1):-lam,(1,2):lam,(1,3):lam}
muL1={1:Fr(1)}
l8=P.lin(Fr(1,8),Fr(-1,8))
muL2={2:Fr(1,8),3:Fr(1,4),4:Fr(1,4),5:Fr(1,4),6:Fr(1,8)}
ellL2={(2,0):l8,(2,1):l8,(2,2):-l8,(2,3):-l8,(6,0):-l8,(6,1):-l8,(6,2):l8,(6,3):l8}
def phis(mu,ell,reg,r1,r2,r0):
    phi,node,bad=gen.gen({k:P.c(v) for k,v in mu.items()},ell,reg,r1,r2,r0)
    assert not bad, bad[:3]
    return phi
phL1=phis(muL1,ellL1,'mid',Fr(2),Fr(3),Fr(5,2))
# L1 potentials must be region independent: check lo and hi give same
assert all((phis(muL1,ellL1,'lo',Fr(1),Fr(2),Fr(3,2))[v].t==phL1[v].t) for v in STATES)
phL2lo=phis(muL2,ellL2,'lo',Fr(1),Fr(2),Fr(3,2))
phL2mid=phis(muL2,ellL2,'mid',Fr(2),Fr(3),Fr(11,5))
print(phL1[(0,0,0,0)], phL2lo[(0,0,0,0)], phL2mid[(0,0,0,0)])

hdr='''import «LeanPaperCTwoMag2222BaseV1»

/-!
# Paper C, counts `(2,2,2,2)`: three dual certificates, at every band

`g = (a, a, -a, -a, b, b, -b, -b)`, `D = 4(a+b)`. Each certificate is a table of potentials on
the `81` count states whose edge inequalities (`EdgeOK`) are checked case by case; `cert8`
(weak duality through the flow equivalence) turns it into a lower bound on `V_g(η)`.

* `lower_L1` (every ratio): weight one on budget `1`, band at position `1`. An `a`-item comes
  first with probability at least `(1-η)/2`, and costs `a - b` there:
  `V_g(η) ≥ (a-b)(1-η)/(2D)`.
* `lower_L2lo` (`b < a ≤ 2b`): budget weights `(0, 1/8, 1/4, 1/4, 1/4, 1/8, 0)`, band terms
  `λ(#A₂ - 1) - λ(#A₆ - 3)` with `λ = (a-b)/8`: `V_g(η) ≥ (3(a-b)/4 - η(a-b)/8)/D`.
* `lower_L2mid` (`2b ≤ a ≤ 3b`): the same weights and band terms:
  `V_g(η) ≥ ((5b-a)/4 - η(a-b)/8)/D`.

The potential tables were produced by an exact shortest-path computation in rational arithmetic
and are checked here edge by edge; nothing numerical is trusted.
-/

namespace CIGAMF.P13.PaperCTwoMag2222

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFlowCert

variable {a b : ℝ}

theorem base8 : trueBaseline (g8 a b) 8 = 0 :=
  base_even 8 Finset.univ (by decide)
    (by simp [g8, typedG, ty8, wt, Fin.sum_univ_succ])

/-- The per-budget optima on `b < a ≤ 2b`. -/
noncomputable def βlo (a b : ℝ) : ℕ → ℝ
  | 1 => b | 3 => 2 * b - a | 5 => 2 * b - a | 7 => b | _ => 0

/-- The per-budget optima on `2b ≤ a ≤ 3b`. -/
noncomputable def βmid (a b : ℝ) : ℕ → ℝ
  | 1 => b | 3 => a - 2 * b | 5 => a - 2 * b | 7 => b | _ => 0

/-- The per-budget optima on `3b ≤ a`. -/
noncomputable def βhi (a b : ℝ) : ℕ → ℝ
  | 1 => b | 3 => b | 5 => b | 7 => b | _ => 0

theorem βlo_eq (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    ∀ k (hk : k < 9), trueBaseline (g8 a b) ⟨k, hk⟩ = βlo a b k := by
  intro k hk
  interval_cases k
  · exact base0
  · exact base1 hb hab
  · exact base2
  · exact base3_lo hb hab h2
  · exact base4
  · exact base5_lo hb hab h2
  · exact base6
  · exact base7 hb hab
  · exact base8

theorem βmid_eq (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    ∀ k (hk : k < 9), trueBaseline (g8 a b) ⟨k, hk⟩ = βmid a b k := by
  have hab : b < a := by linarith
  intro k hk
  interval_cases k
  · exact base0
  · exact base1 hb hab
  · exact base2
  · exact base3_mid hb h2 h3
  · exact base4
  · exact base5_mid hb h2 h3
  · exact base6
  · exact base7 hb hab
  · exact base8

theorem βhi_eq (hb : 0 < b) (h3 : 3 * b ≤ a) :
    ∀ k (hk : k < 9), trueBaseline (g8 a b) ⟨k, hk⟩ = βhi a b k := by
  have hab : b < a := by linarith
  intro k hk
  interval_cases k
  · exact base0
  · exact base1 hb hab
  · exact base2
  · exact base3_hi hb h3
  · exact base4
  · exact base5_hi hb h3
  · exact base6
  · exact base7 hb hab
  · exact base8
'''
body=[]
# L1
body.append('/-! ## 1. The band at the first position (every ratio) -/\n')
body.append(mu_def('μL1',muL1))
body.append('''
/-- Band multipliers of `L1`: at position `1`, `-(a-b)` on the `a`-types, `a-b` on the `b`-types. -/
noncomputable def ℓL1 (a b : ℝ) (k : ℕ) (τ : Fin 4) : ℝ :=
  if k = 1 then (if τ.val < 2 then -(a - b) else a - b) else 0
''')
body.append(phi_def('φL1',phL1))
body.append('''
theorem μL1_nonneg : ∀ k, 0 ≤ μL1 k := by
  intro k; unfold μL1; split <;> norm_num

set_option maxHeartbeats 2000000 in
theorem edge_L1_0 (hb : 0 < b) (hab : b < a) (v0 v1 v2 v3 : ℕ) (h0 : v0 < 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φL1 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) μL1 (ℓL1 a b) v0 v1 v2 v3 + φL1 a b (v0 + 1) v1 v2 v3 := by
  unfold nodeN
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sN, φL1, μL1, ℓL1, βmid, abs_of_pos (hb.trans hab), abs_of_pos hb] <;> linarith

set_option maxHeartbeats 2000000 in
theorem edge_L1_1 (hb : 0 < b) (hab : b < a) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 < 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φL1 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) μL1 (ℓL1 a b) v0 v1 v2 v3 + φL1 a b v0 (v1 + 1) v2 v3 := by
  unfold nodeN
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sN, φL1, μL1, ℓL1, βmid, abs_of_pos (hb.trans hab), abs_of_pos hb] <;> linarith

set_option maxHeartbeats 2000000 in
theorem edge_L1_2 (hb : 0 < b) (hab : b < a) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 < 2) (h3' : v3 ≤ 2) :
    φL1 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) μL1 (ℓL1 a b) v0 v1 v2 v3 + φL1 a b v0 v1 (v2 + 1) v3 := by
  unfold nodeN
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sN, φL1, μL1, ℓL1, βmid, abs_of_pos (hb.trans hab), abs_of_pos hb] <;> linarith

set_option maxHeartbeats 2000000 in
theorem edge_L1_3 (hb : 0 < b) (hab : b < a) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 < 2) :
    φL1 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) μL1 (ℓL1 a b) v0 v1 v2 v3 + φL1 a b v0 v1 v2 (v3 + 1) := by
  unfold nodeN
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sN, φL1, μL1, ℓL1, βmid, abs_of_pos (hb.trans hab), abs_of_pos hb] <;> linarith

theorem edge_L1 (hb : 0 < b) (hab : b < a) : EdgeOK a b (βmid a b) μL1 (ℓL1 a b) (φL1 a b) := by
  intro v0 v1 v2 v3 e0 e1 e2 e3
  exact ⟨fun h => edge_L1_0 hb hab v0 v1 v2 v3 h e1 e2 e3, fun h => edge_L1_1 hb hab v0 v1 v2 v3 e0 h e2 e3,
    fun h => edge_L1_2 hb hab v0 v1 v2 v3 e0 e1 h e3, fun h => edge_L1_3 hb hab v0 v1 v2 v3 e0 e1 e2 h⟩

/-- **The first-position band bound, at every ratio.** -/
theorem lower_L1 (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) :
    (a - b) * (1 - η) / 2 / (4 * (a + b)) ≤ trueValue (g8 a b) η K7 K7_ne := by
  have h := cert8 hb hab 1 one_pos (βmid a b) μL1 (ℓL1 a b) (φL1 a b) μL1_nonneg
    (by simp [μL1]) (by norm_num [μL1])
    (fun k hk hμ => by
      interval_cases k <;> simp [μL1] at hμ
      simpa [βmid] using base1 hb hab)
    (edge_L1 hb hab) (by simp [φL1]) η hη
  have e0 : φL1 a b 0 0 0 0 = (a - b) / 2 := by simp [φL1]; try ring
  have e1 : ∑ k ∈ range 8, ∑ τ, |ℓL1 a b k τ| = 4 * (a - b) := by
    simp [Finset.sum_range_succ, Fin.sum_univ_four, ℓL1, abs_of_pos (sub_pos.mpr hab), abs_of_neg (sub_neg.mpr hab)]; try ring
  rw [e0, e1, one_mul] at h
  convert h using 2; ring
''')
# L2
body.append('/-! ## 2. The band at positions `2` and `6` -/\n')
body.append(mu_def('μL2',muL2))
body.append('''
/-- Band multipliers of `L2`: `±(a-b)/8` at positions `2` and `6`. -/
noncomputable def ℓL2 (a b : ℝ) (k : ℕ) (τ : Fin 4) : ℝ :=
  if k = 2 then (if τ.val < 2 then (a - b) / 8 else -((a - b) / 8))
  else if k = 6 then (if τ.val < 2 then -((a - b) / 8) else (a - b) / 8) else 0
''')
body.append(phi_def('φL2lo',phL2lo))
body.append('')
body.append(phi_def('φL2mid',phL2mid))
body.append('''
theorem μL2_nonneg : ∀ k, 0 ≤ μL2 k := by
  intro k; unfold μL2; split <;> norm_num

theorem sum_ℓL2 (hab : b < a) : ∑ k ∈ range 8, ∑ τ, |ℓL2 a b k τ| = a - b := by
  have h : 0 < (a - b) / 8 := by linarith
  simp [Finset.sum_range_succ, Fin.sum_univ_four, ℓL2, abs_of_pos h]; try ring

set_option maxHeartbeats 2000000 in
theorem edge_L2lo_0 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 < 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φL2lo a b v0 v1 v2 v3 ≤ nodeN a b (βlo a b) μL2 (ℓL2 a b) v0 v1 v2 v3 + φL2lo a b (v0 + 1) v1 v2 v3 := by
  have habs := abs_sN_lo hb hab h2 v0 v1 v2 v3 (by omega) h1 h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgLo, sgHi, sN, φL2lo, μL2, ℓL2, βlo] <;> linarith

set_option maxHeartbeats 2000000 in
theorem edge_L2lo_1 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 < 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φL2lo a b v0 v1 v2 v3 ≤ nodeN a b (βlo a b) μL2 (ℓL2 a b) v0 v1 v2 v3 + φL2lo a b v0 (v1 + 1) v2 v3 := by
  have habs := abs_sN_lo hb hab h2 v0 v1 v2 v3 h0 (by omega) h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgLo, sgHi, sN, φL2lo, μL2, ℓL2, βlo] <;> linarith

set_option maxHeartbeats 2000000 in
theorem edge_L2lo_2 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 < 2) (h3' : v3 ≤ 2) :
    φL2lo a b v0 v1 v2 v3 ≤ nodeN a b (βlo a b) μL2 (ℓL2 a b) v0 v1 v2 v3 + φL2lo a b v0 v1 (v2 + 1) v3 := by
  have habs := abs_sN_lo hb hab h2 v0 v1 v2 v3 h0 h1 (by omega) h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgLo, sgHi, sN, φL2lo, μL2, ℓL2, βlo] <;> linarith

set_option maxHeartbeats 2000000 in
theorem edge_L2lo_3 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 < 2) :
    φL2lo a b v0 v1 v2 v3 ≤ nodeN a b (βlo a b) μL2 (ℓL2 a b) v0 v1 v2 v3 + φL2lo a b v0 v1 v2 (v3 + 1) := by
  have habs := abs_sN_lo hb hab h2 v0 v1 v2 v3 h0 h1 h2' (by omega)
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgLo, sgHi, sN, φL2lo, μL2, ℓL2, βlo] <;> linarith

theorem edge_L2lo (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) : EdgeOK a b (βlo a b) μL2 (ℓL2 a b) (φL2lo a b) := by
  intro v0 v1 v2 v3 e0 e1 e2 e3
  exact ⟨fun h => edge_L2lo_0 hb hab h2 v0 v1 v2 v3 h e1 e2 e3, fun h => edge_L2lo_1 hb hab h2 v0 v1 v2 v3 e0 h e2 e3,
    fun h => edge_L2lo_2 hb hab h2 v0 v1 v2 v3 e0 e1 h e3, fun h => edge_L2lo_3 hb hab h2 v0 v1 v2 v3 e0 e1 e2 h⟩

set_option maxHeartbeats 2000000 in
theorem edge_L2mid_0 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 < 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φL2mid a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) μL2 (ℓL2 a b) v0 v1 v2 v3 + φL2mid a b (v0 + 1) v1 v2 v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 (by omega) h1 h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φL2mid, μL2, ℓL2, βmid] <;> linarith

set_option maxHeartbeats 2000000 in
theorem edge_L2mid_1 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 < 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φL2mid a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) μL2 (ℓL2 a b) v0 v1 v2 v3 + φL2mid a b v0 (v1 + 1) v2 v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 (by omega) h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φL2mid, μL2, ℓL2, βmid] <;> linarith

set_option maxHeartbeats 2000000 in
theorem edge_L2mid_2 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 < 2) (h3' : v3 ≤ 2) :
    φL2mid a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) μL2 (ℓL2 a b) v0 v1 v2 v3 + φL2mid a b v0 v1 (v2 + 1) v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 h1 (by omega) h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φL2mid, μL2, ℓL2, βmid] <;> linarith

set_option maxHeartbeats 2000000 in
theorem edge_L2mid_3 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 < 2) :
    φL2mid a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) μL2 (ℓL2 a b) v0 v1 v2 v3 + φL2mid a b v0 v1 v2 (v3 + 1) := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 h1 h2' (by omega)
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φL2mid, μL2, ℓL2, βmid] <;> linarith

theorem edge_L2mid (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) : EdgeOK a b (βmid a b) μL2 (ℓL2 a b) (φL2mid a b) := by
  intro v0 v1 v2 v3 e0 e1 e2 e3
  exact ⟨fun h => edge_L2mid_0 hb h2 h3 v0 v1 v2 v3 h e1 e2 e3, fun h => edge_L2mid_1 hb h2 h3 v0 v1 v2 v3 e0 h e2 e3,
    fun h => edge_L2mid_2 hb h2 h3 v0 v1 v2 v3 e0 e1 h e3, fun h => edge_L2mid_3 hb h2 h3 v0 v1 v2 v3 e0 e1 e2 h⟩

/-- **The positions-`2`-and-`6` bound on `b < a ≤ 2b`.** -/
theorem lower_L2lo (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (η : ℝ) (hη : 0 ≤ η) :
    (3 * (a - b) / 4 - η * (a - b) / 8) / (4 * (a + b)) ≤ trueValue (g8 a b) η K7 K7_ne := by
  have h := cert8 hb hab 1 one_pos (βlo a b) μL2 (ℓL2 a b) (φL2lo a b) μL2_nonneg
    (by simp [μL2]) (by norm_num [μL2]) (fun k hk _ => βlo_eq hb hab h2 k hk)
    (edge_L2lo hb hab h2) (by simp [φL2lo]) η hη
  have e0 : φL2lo a b 0 0 0 0 = 3 * (a - b) / 4 := by simp [φL2lo]; try ring
  rw [e0, sum_ℓL2 hab, one_mul] at h
  convert h using 2; ring

/-- **The positions-`2`-and-`6` bound on `2b ≤ a ≤ 3b`.** -/
theorem lower_L2mid (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (η : ℝ) (hη : 0 ≤ η) :
    ((5 * b - a) / 4 - η * (a - b) / 8) / (4 * (a + b)) ≤ trueValue (g8 a b) η K7 K7_ne := by
  have hab : b < a := by linarith
  have h := cert8 hb hab 1 one_pos (βmid a b) μL2 (ℓL2 a b) (φL2mid a b) μL2_nonneg
    (by simp [μL2]) (by norm_num [μL2]) (fun k hk _ => βmid_eq hb h2 h3 k hk)
    (edge_L2mid hb h2 h3) (by simp [φL2mid]) η hη
  have e0 : φL2mid a b 0 0 0 0 = (5 * b - a) / 4 := by simp [φL2mid]; try ring
  rw [e0, sum_ℓL2 hab, one_mul] at h
  convert h using 2; ring

#print axioms βlo_eq
#print axioms βmid_eq
#print axioms βhi_eq
#print axioms lower_L1
#print axioms lower_L2lo
#print axioms lower_L2mid

end CIGAMF.P13.PaperCTwoMag2222
''')
open('lean/LeanPaperCTwoMag2222CertV1.lean','w').write(hdr+'\n'+'\n'.join(body))
print("written")
