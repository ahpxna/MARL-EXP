import «LeanD6BinaryBridgeV1»
import «LeanD6SmallSymmetricDifference»
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
def baseF : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℤ :=
  ![![![![![![0, 16], ![16, 16]], ![![-16, -16], ![-16, -16]]], ![![![16, 32], ![32, 32]], ![![0, 0], ![0, 0]]]], ![![![![16, 32], ![32, 32]], ![![0, 0], ![0, 16]]], ![![![48, 48], ![48, 48]], ![![16, 32], ![32, 32]]]]], ![![![![![16, 16], ![16, 16]], ![![-16, -16], ![-16, -16]]], ![![![32, 32], ![32, 32]], ![![0, 0], ![0, 0]]]], ![![![![32, 32], ![32, 32]], ![![0, 0], ![0, 16]]], ![![![48, 48], ![48, 48]], ![![32, 32], ![32, 32]]]]]]
def edgeF : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℤ :=
  ![![![![![![0, 17], ![17, 16]], ![![-15, -16], ![-16, -16]]], ![![![15, 32], ![32, 32]], ![![0, 0], ![0, 0]]]], ![![![![15, 32], ![32, 32]], ![![0, 0], ![0, 16]]], ![![![48, 48], ![48, 48]], ![![16, 32], ![32, 32]]]]], ![![![![![17, 16], ![16, 16]], ![![-16, -16], ![-16, -16]]], ![![![32, 32], ![32, 32]], ![![0, 0], ![0, 0]]]], ![![![![32, 32], ![32, 32]], ![![0, 0], ![0, 16]]], ![![![48, 48], ![48, 48]], ![![32, 32], ![32, 32]]]]]]
def raw (e : Fin 2) (z : Fin 6 → Fin 2) : ℤ :=
  (if e = 0 then baseF else edgeF) (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)
def S : Finset (Fin 6) := {0,4,5}
def T : Finset (Fin 6) := {1,2,3}
def selMin : Fin 6 → Fin 2 := ![1, 0, 0, 1, 1, 1]
def selMax : Fin 6 → Fin 2 := ![0, 1, 1, 0, 0, 0]
def comMin : Fin 6 → Fin 2 := ![1, 0, 0, 1, 0, 0]
def comMax : Fin 6 → Fin 2 := ![0, 1, 1, 0, 0, 0]
def rlo (e : Fin 2) (i : Fin 6) : ℤ := (if e=0 then ![0, 16, 16, -32, 0, 0] else ![-1, 15, 15, -33, -1, -1]) i
def rhi (e : Fin 2) (i : Fin 6) : ℤ := (if e=0 then ![16, 32, 32, -16, 16, 16] else ![17, 33, 33, -15, 17, 17]) i
def response (e : Fin 2) (i : Fin 6) (u : Fin 2) : ℤ :=
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

theorem mix_sub (s : ℝ) (a b c d : ℤ) :
    mix s a b - mix s c d = mix s (a-c) (b-d) := by
  unfold mix; push_cast; ring

theorem world_derivative_bounds (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (i : Fin 6) (z : Fin 6 → Fin 2) :
    mix s (rlo 0 i) (rlo 1 i) ≤ world s (Function.update z i 1) - world s (Function.update z i 0) ∧
    world s (Function.update z i 1) - world s (Function.update z i 0) ≤ mix s (rhi 0 i) (rhi 1 i) := by
  change mix s _ _ ≤ mix s _ _ - mix s _ _ ∧ mix s _ _ - mix s _ _ ≤ mix s _ _
  rw [mix_sub]
  exact ⟨mix_le s hs hs1 (endpoint_derivative_bounds 0 i z).1 (endpoint_derivative_bounds 1 i z).1,
    mix_le s hs hs1 (endpoint_derivative_bounds 0 i z).2 (endpoint_derivative_bounds 1 i z).2⟩

theorem world_mixed_bound (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (i : Fin 6) (x c : Fin 6 → Fin 2) :
    |mixedDifference (world s) i x c| ≤ 16 + 2*s := by
  obtain ⟨hxlo,hxhi⟩ := world_derivative_bounds s hs hs1 i x
  obtain ⟨hclo,hchi⟩ := world_derivative_bounds s hs hs1 i c
  have hwidth : mix s (rhi 0 i) (rhi 1 i) - mix s (rlo 0 i) (rlo 1 i) ≤ 16+2*s := by
    rw [mix_sub]
    have h := mix_le s hs hs1 (endpoint_spreads i).1 (endpoint_spreads i).2
    convert h using 1 <;> simp [mix] <;> ring
  have heq : mixedDifference (world s) i x c =
      (world s (Function.update x i (x i)) - world s (Function.update x i (c i))) -
      (world s (Function.update c i (x i)) - world s (Function.update c i (c i))) := by
    simp [mixedDifference, Function.update_eq_self]; ring
  rw [heq]
  generalize x i = u
  generalize c i = v
  fin_cases u <;> fin_cases v <;> rw [abs_le] <;> constructor <;> linarith

theorem world_residual_bounds (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (z : Fin 6 → Fin 2) :
    retainedResidual cornerQ2 (world s) S selMin ≤ retainedResidual cornerQ2 (world s) S z ∧
    retainedResidual cornerQ2 (world s) S z ≤ retainedResidual cornerQ2 (world s) S selMax ∧
    retainedResidual cornerQ2 (world s) T comMin ≤ retainedResidual cornerQ2 (world s) T z ∧
    retainedResidual cornerQ2 (world s) T z ≤ retainedResidual cornerQ2 (world s) T comMax := by
  simp only [world_rs,world_rt]
  have a := endpoint_residual_bounds 0 z
  have b := endpoint_residual_bounds 1 z
  exact ⟨mix_le s hs hs1 a.1 b.1, mix_le s hs hs1 a.2.1 b.2.1,
    mix_le s hs hs1 a.2.2.1 b.2.2.1, mix_le s hs hs1 a.2.2.2 b.2.2.2⟩

private theorem osc_of_extremes {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (lo hi : X) (hlo : ∀ x, f lo ≤ f x) (hhi : ∀ x, f x ≤ f hi) :
    osc f = f hi - f lo := by
  have hmax : maxVal f = f hi := le_antisymm (maxVal_le f hhi) (le_maxVal f hi)
  have hmin : minVal f = f lo := le_antisymm (minVal_le f lo) (le_minVal f hlo)
  simp [osc,hmax,hmin]

theorem world_osc_response (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (i : Fin 6) :
    osc (productResponse cornerQ2 (world s) i) = if i ∈ S then 16+s else 16-s := by
  have h := osc_of_extremes (productResponse cornerQ2 (world s) i) (respMin i) (respMax i)
    (fun u => by rw [world_response,world_response]; exact mix_le s hs hs1
      (endpoint_response_bounds 0 i u).1 (endpoint_response_bounds 1 i u).1)
    (fun u => by rw [world_response,world_response]; exact mix_le s hs hs1
      (endpoint_response_bounds 0 i u).2 (endpoint_response_bounds 1 i u).2)
  rw [h,world_response,world_response,mix_sub,(endpoint_spans i).1,(endpoint_spans i).2]
  by_cases hi : i ∈ S <;> simp [hi,mix] <;> ring

theorem world_top_three (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsTopKByScore (fun i => osc (productResponse cornerQ2 (world s) i)) S 3 := by
  rw [isTopKByScore_iff_pairwise]
  refine ⟨by decide, ?_⟩
  intro i hi j hj
  rw [world_osc_response s hs hs1,world_osc_response s hs hs1,if_pos hi,if_neg hj]
  linarith

theorem world_strict_top_three (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ i ∈ S, ∀ j ∉ S,
      osc (productResponse cornerQ2 (world s) j) < osc (productResponse cornerQ2 (world s) i) := by
  intro i hi j hj
  rw [world_osc_response s hs.le hs1,world_osc_response s hs.le hs1,if_pos hi,if_neg hj]
  linarith

theorem world_doubled_gap (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    2 * (productCompressionLoss (world s) (productResponse cornerQ2 (world s)) S -
      productCompressionLoss (world s) (productResponse cornerQ2 (world s)) T) = 96 := by
  have hS := osc_of_extremes (retainedResidual cornerQ2 (world s) S) selMin selMax
    (fun z => (world_residual_bounds s hs hs1 z).1)
    (fun z => (world_residual_bounds s hs hs1 z).2.1)
  have hT := osc_of_extremes (retainedResidual cornerQ2 (world s) T) comMin comMax
    (fun z => (world_residual_bounds s hs hs1 z).2.2.1)
    (fun z => (world_residual_bounds s hs hs1 z).2.2.2)
  change 2 * (osc (retainedResidual cornerQ2 (world s) S)/2 -
    osc (retainedResidual cornerQ2 (world s) T)/2) = 96
  rw [hS,hT,world_rs,world_rs,world_rt,world_rt]
  have h : (mix s (rs 0 selMax) (rs 1 selMax) - mix s (rs 0 selMin) (rs 1 selMin)) -
      (mix s (rt 0 comMax) (rt 1 comMax) - mix s (rt 0 comMin) (rt 1 comMin)) = 96 := by
    rw [mix_sub,mix_sub,mix_sub,endpoint_gap 0,endpoint_gap 1]
    unfold mix; norm_num; ring
  linarith

/-- Universal coefficient for the m=6, k=3 corner-reference comparison problem. -/
def ConstantAtMost (c : ℝ) : Prop :=
  ∀ (F : (Fin 6 → Fin 2) → ℝ) (delta : ℝ), 0 ≤ delta →
    (∀ i x z, |mixedDifference F i x z| ≤ delta) →
    ∀ (selected competitor : Finset (Fin 6)),
      IsTopKByScore (fun i => osc (productResponse cornerQ2 F i)) selected 3 →
      competitor.card = 3 →
      2 * (productCompressionLoss F (productResponse cornerQ2 F) selected -
        productCompressionLoss F (productResponse cornerQ2 F) competitor) ≤ c*delta

theorem constant_six_upper : ConstantAtMost 6 := by
  intro F delta hd hdelta selected competitor hTop hCard
  have h := CIGAMF.P13.D6SmallSymmetricDifference.pair_loss_le_sdiff_card
    cornerQ2 F delta cornerQ2_nonnegative cornerQ2_normalized hd hdelta selected competitor 3 hTop hCard
  have hc : (selected \ competitor).card ≤ 3 := by
    calc (selected \ competitor).card ≤ selected.card := Finset.card_le_card Finset.sdiff_subset
         _ = 3 := hTop.1
  have hcr : ((selected \ competitor).card : ℝ) ≤ 3 := by exact_mod_cast hc
  nlinarith

/-- Any smaller coefficient is violated by a strictly selected member of the explicit family.
This epsilon argument proves sharpness without assuming an optimizer or a limit theorem. -/
theorem every_smaller_constant_fails (c : ℝ) (hc : c < 6) :
    ∃ (s : ℝ), 0 < s ∧ s ≤ 1 ∧
      c * (16+2*s) < 2 * (productCompressionLoss (world s) (productResponse cornerQ2 (world s)) S -
        productCompressionLoss (world s) (productResponse cornerQ2 (world s)) T) := by
  by_cases hneg : c ≤ 0
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    rw [world_doubled_gap 1 (by norm_num) le_rfl]
    nlinarith
  · have hpos : 0 < c := lt_of_not_ge hneg
    let s := min 1 ((6-c)/(c+1))
    have hs : 0 < s := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsr : s ≤ (6-c)/(c+1) := min_le_right _ _
    have hm : s*(c+1) ≤ 6-c := (le_div_iff₀ (by linarith)).mp hsr
    refine ⟨s, hs, hs1, ?_⟩
    rw [world_doubled_gap s hs.le hs1]
    nlinarith

theorem constant_six_sharp : ConstantAtMost 6 ∧ ∀ c : ℝ, c < 6 → ¬ ConstantAtMost c := by
  refine ⟨constant_six_upper, ?_⟩
  intro c hc hBound
  obtain ⟨s,hs,hs1,hgap⟩ := every_smaller_constant_fails c hc
  have h := hBound (world s) (16+2*s) (by linarith)
    (world_mixed_bound s hs.le hs1) S T (world_top_three s hs.le hs1) (by decide)
  linarith

end CIGAMF.P13.D6M6Sharpness
