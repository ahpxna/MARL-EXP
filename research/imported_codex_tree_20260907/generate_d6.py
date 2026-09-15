from pathlib import Path
from fractions import Fraction as Q
import json,itertools
p=json.load(open('/Users/phanan/cig-amf-main/research/d6_contrast_rank_falsification/D6_INTEGER_GRID_WITNESS_m6_20260906.json'))
tie=[round(Q(v,14)) for v in p['integer_world']]
S=(0,4,5);T=(1,2,3)
a=[16*v for v in tie];b=a.copy()
for i in range(6):b[1<<i]+=(1 if i in S else -1)*(1 if a[1<<i]>0 else -1)
w=[a,b]
resp=[[v[1<<i] for i in range(6)] for v in w]
res={key:[[v[j]-sum(v[1<<i]*((j>>i)&1) for i in sel) for j in range(64)] for v in w] for key,sel in [('sel',S),('com',T)]}
pts={}
for key,arrs in res.items():
 for kind,fn in [('Min',min),('Max',max)]:
  pts[key+kind]=min(set(j for j in range(64) if arrs[0][j]==fn(arrs[0]))&set(j for j in range(64) if arrs[1][j]==fn(arrs[1])))
print('points',pts,'ranges',{k:[(min(a),max(a)) for a in arr] for k,arr in res.items()})
lo=[[min(v[j|1<<i]-v[j&~(1<<i)] for j in range(64)) for i in range(6)] for v in w]
hi=[[max(v[j|1<<i]-v[j&~(1<<i)] for j in range(64)) for i in range(6)] for v in w]
print('lo',lo,'hi',hi,'resp',resp)
def table(v,prefix=()):
 if len(prefix)==6:return str(v[sum(x<<i for i,x in enumerate(prefix))])
 return '!['+', '.join(table(v,prefix+(x,)) for x in [0,1])+']'
def vec(a):return '!['+', '.join(map(str,a))+']'
def pt(j):return vec([(j>>i)&1 for i in range(6)])
s='''module
public import «LeanD6BinaryBridgeV1»
public import «LeanD6SmallSymmetricDifference»
public section
/-! Explicit interpolation from a tie world to a strict Top-3 world.
All finite endpoint certificates use kernel `decide` on explicit Fin arguments.
The endpoints are data; no LP output or numerical result is assumed. -/
namespace CIGAMF.P13.D6M6Sharpness
open scoped BigOperators
open CIGAMF.V4.SupportGeometry CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6BinaryBridgeV1 (cornerQ2 z6 cornerQ2_response cornerQ2_nonnegative cornerQ2_normalized)
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
'''
for name,v in [('baseF',a),('edgeF',b)]:s+=f'def {name} : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℤ :=\n  {table(v)}\n'
s+='''def raw (e : Fin 2) (z : Fin 6 → Fin 2) : ℤ :=
  (if e = 0 then baseF else edgeF) (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)
def S : Finset (Fin 6) := {0,4,5}
def T : Finset (Fin 6) := {1,2,3}
'''
for name,j in pts.items():s+=f'def {name} : Fin 6 → Fin 2 := {pt(j)}\n'
s+=f'def rlo (e : Fin 2) (i : Fin 6) : ℤ := (if e=0 then {vec(lo[0])} else {vec(lo[1])}) i\n'
s+=f'def rhi (e : Fin 2) (i : Fin 6) : ℤ := (if e=0 then {vec(hi[0])} else {vec(hi[1])}) i\n'
s+='''def response (e : Fin 2) (i : Fin 6) (u : Fin 2) : ℤ :=
  raw e (Function.update z6 i u)
def rs (e : Fin 2) (z : Fin 6 → Fin 2) : ℤ :=
  raw e z - response e 0 (z 0) - response e 4 (z 4) - response e 5 (z 5)
def rt (e : Fin 2) (z : Fin 6 → Fin 2) : ℤ :=
  raw e z - response e 1 (z 1) - response e 2 (z 2) - response e 3 (z 3)
private theorem eta (z : Fin 6 → Fin 2) : z = ![z 0,z 1,z 2,z 3,z 4,z 5] := by
  funext i; fin_cases i <;> rfl
private theorem lift6 {P : (Fin 6 → Fin 2) → Prop}
    (h : ∀ a b c d e f : Fin 2, P ![a,b,c,d,e,f]) (z : Fin 6 → Fin 2) : P z := by
  rw [eta z]; exact h _ _ _ _ _ _

theorem endpoint_derivative_bounds (e : Fin 2) (i : Fin 6) (z : Fin 6 → Fin 2) :
    rlo e i ≤ raw e (Function.update z i 1) - raw e (Function.update z i 0) ∧
    raw e (Function.update z i 1) - raw e (Function.update z i 0) ≤ rhi e i := by
  have h : ∀ (e : Fin 2) (i : Fin 6) (a b c d f g : Fin 2),
      rlo e i ≤ raw e (Function.update ![a,b,c,d,f,g] i 1) - raw e (Function.update ![a,b,c,d,f,g] i 0) ∧
      raw e (Function.update ![a,b,c,d,f,g] i 1) - raw e (Function.update ![a,b,c,d,f,g] i 0) ≤ rhi e i := by decide
  exact lift6 (h e i) z

theorem endpoint_spreads : ∀ i : Fin 6,
    rhi 0 i - rlo 0 i ≤ 16 ∧ rhi 1 i - rlo 1 i ≤ 18 := by decide

theorem endpoint_residual_bounds (e : Fin 2) (z : Fin 6 → Fin 2) :
    rs e selMin ≤ rs e z ∧ rs e z ≤ rs e selMax ∧
    rt e comMin ≤ rt e z ∧ rt e z ≤ rt e comMax := by
  have h : ∀ e a b c d f g : Fin 2,
      rs e selMin ≤ rs e ![a,b,c,d,f,g] ∧ rs e ![a,b,c,d,f,g] ≤ rs e selMax ∧
      rt e comMin ≤ rt e ![a,b,c,d,f,g] ∧ rt e ![a,b,c,d,f,g] ≤ rt e comMax := by decide
  exact lift6 (h e) z

def respMax : Fin 6 → Fin 2 := ![1,1,1,0,1,1]
def respMin : Fin 6 → Fin 2 := ![0,0,0,1,0,0]
theorem endpoint_response_bounds : ∀ (e : Fin 2) (i : Fin 6) (u : Fin 2),
    response e i (respMin i) ≤ response e i u ∧ response e i u ≤ response e i (respMax i) := by decide

theorem endpoint_spans : ∀ i : Fin 6,
    response 0 i (respMax i) - response 0 i (respMin i) = 16 ∧
    response 1 i (respMax i) - response 1 i (respMin i) = (if i ∈ S then 17 else 15) := by decide

theorem endpoint_gap : ∀ e : Fin 2,
    (rs e selMax - rs e selMin) - (rt e comMax - rt e comMin) = 96 := by decide

noncomputable def world (s : ℝ) (z : Fin 6 → Fin 2) : ℝ :=
  (1-s) * (raw 0 z : ℝ) + s * (raw 1 z : ℝ)
noncomputable def mix (s : ℝ) (a b : ℤ) : ℝ := (1-s)*(a:ℝ)+s*(b:ℝ)

theorem mix_le (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    {a b c d : ℤ} (h₀ : a ≤ c) (h₁ : b ≤ d) : mix s a b ≤ mix s c d := by
  have h₀' : (a:ℝ) ≤ c := by exact_mod_cast h₀
  have h₁' : (b:ℝ) ≤ d := by exact_mod_cast h₁
  exact add_le_add (mul_le_mul_of_nonneg_left h₀' (by linarith))
    (mul_le_mul_of_nonneg_left h₁' hs)

theorem world_response (s : ℝ) (i : Fin 6) (u : Fin 2) :
    productResponse cornerQ2 (world s) i u = mix s (response 0 i u) (response 1 i u) := by
  rw [cornerQ2_response]; rfl

theorem world_rs (s : ℝ) (z : Fin 6 → Fin 2) :
    retainedResidual cornerQ2 (world s) S z = mix s (rs 0 z) (rs 1 z) := by
  unfold retainedResidual
  simp [S, world_response, mix, world, rs, Finset.sum_insert]
  ring

theorem world_rt (s : ℝ) (z : Fin 6 → Fin 2) :
    retainedResidual cornerQ2 (world s) T z = mix s (rt 0 z) (rt 1 z) := by
  unfold retainedResidual
  simp [T, world_response, mix, world, rt, Finset.sum_insert]
  ring
'''
Path('work/lean_next/LeanD6M6SharpnessV1.lean').write_text(s)
Path('work/lean_next/d6_endpoint_data.json').write_text(json.dumps({'base':a,'edge':b,'points':pts,'lo':lo,'hi':hi},indent=2))
