import «LeanD6BinaryBridgeV1»
import «LeanD6SmallSymmetricDifference»
import «LeanD6SharpnessM6V1»
/-! Explicit interpolation from a tie world to a strict Top-3 world.
All finite endpoint certificates use kernel `decide` on explicit Fin arguments.
The endpoints are data; no LP output or numerical result is assumed. -/
namespace CIGAMF.P13.D6M6SharpnessBridgeV1
open scoped BigOperators
open CIGAMF.V4.SupportGeometry CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6BinaryBridgeV1 (cornerQ2 z6 cornerQ2_response cornerQ2_nonnegative cornerQ2_normalized)
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open CIGAMF.P13.D6SharpnessM6V1 (Ib Db Vb)
def baseF (a b c d e f : Fin 2) : ℤ := 2 * Ib a b c d e f
def edgeF (a b c d e f : Fin 2) : ℤ := 2 * Ib a b c d e f + Db a b c d e f
def raw (e : Fin 2) (z : Fin 6 → Fin 2) : ℤ :=
  (if e = 0 then baseF else edgeF) (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)
def S : Finset (Fin 6) := {0,4,5}
def T : Finset (Fin 6) := {1,2,3}
def selMin : Fin 6 → Fin 2 := ![1, 0, 0, 1, 1, 1]
def selMax : Fin 6 → Fin 2 := ![0, 1, 1, 0, 0, 0]
def comMin : Fin 6 → Fin 2 := ![1, 0, 0, 1, 0, 0]
def comMax : Fin 6 → Fin 2 := ![0, 1, 1, 0, 0, 0]
def rlo (e : Fin 2) (i : Fin 6) : ℤ := (if e=0 then ![0,2,2,-4,0,0] else ![-1,1,1,-5,-1,-1]) i
def rhi (e : Fin 2) (i : Fin 6) : ℤ := (if e=0 then ![2,4,4,-2,2,2] else ![3,5,5,-1,3,3]) i
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
  rw [eta z]; exact h e i _ _ _ _ _ _

theorem endpoint_spreads : ∀ i : Fin 6,
    rhi 0 i - rlo 0 i ≤ 2 ∧ rhi 1 i - rlo 1 i ≤ 4 := by decide

theorem endpoint_residual_bounds (e : Fin 2) (z : Fin 6 → Fin 2) :
    rs e selMin ≤ rs e z ∧ rs e z ≤ rs e selMax ∧
    rt e comMin ≤ rt e z ∧ rt e z ≤ rt e comMax := by
  have h : ∀ e a b c d f g : Fin 2,
      rs e selMin ≤ rs e ![a,b,c,d,f,g] ∧ rs e ![a,b,c,d,f,g] ≤ rs e selMax ∧
      rt e comMin ≤ rt e ![a,b,c,d,f,g] ∧ rt e ![a,b,c,d,f,g] ≤ rt e comMax := by decide
  rw [eta z]; exact h e _ _ _ _ _ _

def respMax : Fin 6 → Fin 2 := ![1,1,1,0,1,1]
def respMin : Fin 6 → Fin 2 := ![0,0,0,1,0,0]
theorem endpoint_response_bounds : ∀ (e : Fin 2) (i : Fin 6) (u : Fin 2),
    response e i (respMin i) ≤ response e i u ∧ response e i u ≤ response e i (respMax i) := by decide

theorem endpoint_spans : ∀ i : Fin 6,
    response 0 i (respMax i) - response 0 i (respMin i) = 2 ∧
    response 1 i (respMax i) - response 1 i (respMin i) = (if i ∈ S then 3 else 1) := by decide

theorem endpoint_gap : ∀ e : Fin 2,
    (rs e selMax - rs e selMin) - (rt e comMax - rt e comMin) = 12 := by decide

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
    |mixedDifference (world s) i x c| ≤ 2 + 2*s := by
  obtain ⟨hxlo,hxhi⟩ := world_derivative_bounds s hs hs1 i x
  obtain ⟨hclo,hchi⟩ := world_derivative_bounds s hs hs1 i c
  have hwidth : mix s (rhi 0 i) (rhi 1 i) - mix s (rlo 0 i) (rlo 1 i) ≤ 2+2*s := by
    rw [mix_sub]
    have h := mix_le s hs hs1 (endpoint_spreads i).1 (endpoint_spreads i).2
    convert h using 1 <;> simp [mix] <;> ring
  have heq : mixedDifference (world s) i x c =
      (world s (Function.update x i (x i)) - world s (Function.update x i (c i))) -
      (world s (Function.update c i (x i)) - world s (Function.update c i (c i))) := by
    simp [mixedDifference, Function.update_eq_self]; ring
  have h01 : |world s (Function.update x i 0) - world s (Function.update x i 1) -
      (world s (Function.update c i 0) - world s (Function.update c i 1))| ≤ 2+2*s := by
    rw [abs_le]; constructor <;> linarith
  have h10 : |world s (Function.update x i 1) - world s (Function.update x i 0) -
      (world s (Function.update c i 1) - world s (Function.update c i 0))| ≤ 2+2*s := by
    rw [abs_le]; constructor <;> linarith
  rw [heq]
  generalize x i = u
  generalize c i = v
  fin_cases u <;> fin_cases v <;> first | exact h01 | exact h10 | (simp; linarith)

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
    osc (productResponse cornerQ2 (world s) i) = if i ∈ S then 2+s else 2-s := by
  have hlo : ∀ u, productResponse cornerQ2 (world s) i (respMin i) ≤ productResponse cornerQ2 (world s) i u := by
    intro u
    rw [world_response, world_response]
    exact mix_le s hs hs1 (endpoint_response_bounds 0 i u).1 (endpoint_response_bounds 1 i u).1
  have hhi : ∀ u, productResponse cornerQ2 (world s) i u ≤ productResponse cornerQ2 (world s) i (respMax i) := by
    intro u
    rw [world_response, world_response]
    exact mix_le s hs hs1 (endpoint_response_bounds 0 i u).2 (endpoint_response_bounds 1 i u).2
  have h := osc_of_extremes (productResponse cornerQ2 (world s) i) (respMin i) (respMax i) hlo hhi
  rw [h,world_response,world_response,mix_sub,(endpoint_spans i).1,(endpoint_spans i).2]
  by_cases hi : i ∈ S <;> simp [hi,mix] <;> ring

theorem world_top_three (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsTopKByScore (fun i => osc (productResponse cornerQ2 (world s) i)) S 3 := by
  rw [isTopKByScore_iff_pairwise]
  refine ⟨by decide, ?_⟩
  intro i hi j hj
  rw [world_osc_response s hs hs1,world_osc_response s hs hs1,ite_eq_left hi,ite_eq_right hj]
  linarith

theorem world_strict_top_three (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ i ∈ S, ∀ j ∉ S,
      osc (productResponse cornerQ2 (world s) j) < osc (productResponse cornerQ2 (world s) i) := by
  intro i hi j hj
  rw [world_osc_response s hs.le hs1,world_osc_response s hs.le hs1,ite_eq_left hi,ite_eq_right hj]
  linarith

theorem world_doubled_gap (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    2 * (productCompressionLoss (world s) (productResponse cornerQ2 (world s)) S -
      productCompressionLoss (world s) (productResponse cornerQ2 (world s)) T) = 12 := by
  have hS := osc_of_extremes (retainedResidual cornerQ2 (world s) S) selMin selMax
    (fun z => (world_residual_bounds s hs hs1 z).1)
    (fun z => (world_residual_bounds s hs hs1 z).2.1)
  have hT := osc_of_extremes (retainedResidual cornerQ2 (world s) T) comMin comMax
    (fun z => (world_residual_bounds s hs hs1 z).2.2.1)
    (fun z => (world_residual_bounds s hs hs1 z).2.2.2)
  change 2 * (osc (retainedResidual cornerQ2 (world s) S)/2 -
    osc (retainedResidual cornerQ2 (world s) T)/2) = 12
  rw [hS,hT,world_rs,world_rs,world_rt,world_rt]
  have h : (mix s (rs 0 selMax) (rs 1 selMax) - mix s (rs 0 selMin) (rs 1 selMin)) -
      (mix s (rt 0 comMax) (rt 1 comMax) - mix s (rt 0 comMin) (rt 1 comMin)) = 12 := by
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
      c * (2+2*s) < 2 * (productCompressionLoss (world s) (productResponse cornerQ2 (world s)) S -
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
  have h := hBound (world s) (2+2*s) (by linarith)
    (world_mixed_bound s hs.le hs1) S T (world_top_three s hs.le hs1) (by decide)
  linarith


open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6ContrastRankPhaseDefinitionsV2

def familyCell : ActiveDecisionCell 5 (Fin 2) where
  q := cornerQ2
  selected := S
  competitor := T
  selectedMax := selMax
  selectedMin := selMin
  competitorMax := comMax
  competitorMin := comMin
  responseMax := respMax
  responseMin := respMin

theorem familyCell_balanced : familyCell.BalancedComplement := by
  refine ⟨by decide, ?_, ?_⟩ <;> decide

theorem world_response_bounds (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 6) (u : Fin 2) :
    productResponse cornerQ2 (world t) i (respMin i) ≤ productResponse cornerQ2 (world t) i u ∧
    productResponse cornerQ2 (world t) i u ≤ productResponse cornerQ2 (world t) i (respMax i) := by
  simp only [world_response]
  exact ⟨mix_le t ht ht1 (endpoint_response_bounds 0 i u).1 (endpoint_response_bounds 1 i u).1,
    mix_le t ht ht1 (endpoint_response_bounds 0 i u).2 (endpoint_response_bounds 1 i u).2⟩

theorem world_span_eq_osc (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 6) :
    responseWitnessSpan familyCell (world t) i = osc (productResponse cornerQ2 (world t) i) := by
  exact (osc_of_extremes _ (respMin i) (respMax i)
    (fun u => (world_response_bounds t ht ht1 i u).1)
    (fun u => (world_response_bounds t ht ht1 i u).2)).symm

theorem world_valid (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : familyCell.Valid (world t) := by
  rw [activeDecisionCell_valid_iff_polyhedral]
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z; exact (world_residual_bounds t ht ht1 z).2.1
  · intro z; exact (world_residual_bounds t ht ht1 z).1
  · intro z; exact (world_residual_bounds t ht ht1 z).2.2.2
  · intro z; exact (world_residual_bounds t ht ht1 z).2.2.1
  · intro i u; exact (world_response_bounds t ht ht1 i u).2
  · intro i u; exact (world_response_bounds t ht ht1 i u).1
  · intro i hi j hj
    rw [world_span_eq_osc t ht ht1,world_span_eq_osc t ht ht1]
    have h := (isTopKByScore_iff_pairwise _ S 3).mp (world_top_three t ht ht1)
    exact h.2 i hi j hj

noncomputable def unitWorld (t : ℝ) (z : Fin 6 → Fin 2) : ℝ := world t z / (2+2*t)

theorem unit_response (t : ℝ) (i : Fin 6) (u : Fin 2) :
    productResponse cornerQ2 (unitWorld t) i u = productResponse cornerQ2 (world t) i u / (2+2*t) := by
  rw [cornerQ2_response,cornerQ2_response]; rfl

theorem unit_residual (t : ℝ) (A : Finset (Fin 6)) (z : Fin 6 → Fin 2) :
    retainedResidual cornerQ2 (unitWorld t) A z = retainedResidual cornerQ2 (world t) A z / (2+2*t) := by
  unfold retainedResidual
  simp only [unitWorld,unit_response]
  rw [← Finset.sum_div, ← sub_div]

theorem unit_span (t : ℝ) (i : Fin 6) :
    responseWitnessSpan familyCell (unitWorld t) i = responseWitnessSpan familyCell (world t) i / (2+2*t) := by
  change productResponse cornerQ2 (unitWorld t) i (respMax i) - productResponse cornerQ2 (unitWorld t) i (respMin i) = _
  rw [unit_response,unit_response,← sub_div]; rfl

theorem unit_valid (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : familyCell.Valid (unitWorld t) := by
  have hd : 0 < 2+2*t := by linarith
  have hp := (activeDecisionCell_valid_iff_polyhedral familyCell (world t)).mp (world_valid t ht ht1)
  rw [activeDecisionCell_valid_iff_polyhedral]
  refine ⟨hp.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z; change retainedResidual cornerQ2 (unitWorld t) S z ≤ retainedResidual cornerQ2 (unitWorld t) S selMax
    rw [unit_residual,unit_residual]; exact div_le_div_of_nonneg_right (hp.2.1 z) hd.le
  · intro z; change retainedResidual cornerQ2 (unitWorld t) S selMin ≤ retainedResidual cornerQ2 (unitWorld t) S z
    rw [unit_residual,unit_residual]; exact div_le_div_of_nonneg_right (hp.2.2.1 z) hd.le
  · intro z; change retainedResidual cornerQ2 (unitWorld t) T z ≤ retainedResidual cornerQ2 (unitWorld t) T comMax
    rw [unit_residual,unit_residual]; exact div_le_div_of_nonneg_right (hp.2.2.2.1 z) hd.le
  · intro z; change retainedResidual cornerQ2 (unitWorld t) T comMin ≤ retainedResidual cornerQ2 (unitWorld t) T z
    rw [unit_residual,unit_residual]; exact div_le_div_of_nonneg_right (hp.2.2.2.2.1 z) hd.le
  · intro i u; change productResponse cornerQ2 (unitWorld t) i u ≤ productResponse cornerQ2 (unitWorld t) i (respMax i)
    rw [unit_response,unit_response]; exact div_le_div_of_nonneg_right (hp.2.2.2.2.2.1 i u) hd.le
  · intro i u; change productResponse cornerQ2 (unitWorld t) i (respMin i) ≤ productResponse cornerQ2 (unitWorld t) i u
    rw [unit_response,unit_response]; exact div_le_div_of_nonneg_right (hp.2.2.2.2.2.2.1 i u) hd.le
  · intro i hi j hj
    rw [unit_span,unit_span]
    exact div_le_div_of_nonneg_right (hp.2.2.2.2.2.2.2 i hi j hj) hd.le

theorem unit_interaction (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : UnitInteractionBound (unitWorld t) := by
  intro i x c
  have hd : 0 < 2+2*t := by linarith
  have heq : mixedDifference (unitWorld t) i x c = mixedDifference (world t) i x c / (2+2*t) := by
    simp only [mixedDifference,unitWorld]; ring
  rw [heq,abs_div,abs_of_pos hd,div_le_one hd]
  exact world_mixed_bound t ht ht1 i x c

private theorem osc_div_pos {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (d : ℝ) (hd : 0 < d) : osc (fun x => f x/d) = osc f/d := by
  obtain ⟨lo,hlo⟩ := exists_eq_minVal f
  obtain ⟨hi,hhi⟩ := exists_eq_maxVal f
  rw [osc_of_extremes (fun x => f x/d) lo hi
    (fun x => div_le_div_of_nonneg_right (by rw [hlo]; exact minVal_le f x) hd.le)
    (fun x => div_le_div_of_nonneg_right (by rw [hhi]; exact le_maxVal f x) hd.le)]
  rw [hlo,hhi,← sub_div]; rfl

theorem unit_strict_top (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) : StrictTopC familyCell (unitWorld t) := by
  intro i hi j hj
  change osc (productResponse cornerQ2 (unitWorld t) j) < osc (productResponse cornerQ2 (unitWorld t) i)
  simp_rw [show ∀ k, productResponse cornerQ2 (unitWorld t) k = fun u => productResponse cornerQ2 (world t) k u / (2+2*t) from fun k => funext (unit_response t k)]
  rw [osc_div_pos _ _ (by linarith),osc_div_pos _ _ (by linarith)]
  exact (div_lt_div_iff_of_pos_right (by linarith)).mpr (world_strict_top_three t ht ht1 i hi j hj)

theorem unit_doubled_gap (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * (productCompressionLoss (unitWorld t) (productResponse cornerQ2 (unitWorld t)) S -
      productCompressionLoss (unitWorld t) (productResponse cornerQ2 (unitWorld t)) T) = 12/(2+2*t) := by
  change 2 * (osc (retainedResidual cornerQ2 (unitWorld t) S)/2 - osc (retainedResidual cornerQ2 (unitWorld t) T)/2) = _
  have h : ∀ A, retainedResidual cornerQ2 (unitWorld t) A = fun z => retainedResidual cornerQ2 (world t) A z / (2+2*t) := fun A => funext (unit_residual t A)
  rw [h,h,osc_div_pos _ _ (by linarith),osc_div_pos _ _ (by linarith)]
  have hg := world_doubled_gap t ht ht1
  change 2 * (osc (retainedResidual cornerQ2 (world t) S)/2 - osc (retainedResidual cornerQ2 (world t) T)/2) = 12 at hg
  calc _ = (2 * (osc (retainedResidual cornerQ2 (world t) S)/2 - osc (retainedResidual cornerQ2 (world t) T)/2))/(2+2*t) := by ring
       _ = _ := by rw [hg]

/-- The exact integer family from the existing compiled arithmetic module, normalized. -/
noncomputable def normalizedFamily (s : ℤ) (z : Fin 6 → Fin 2) : ℝ :=
  (Vb s (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) : ℝ) / (2*(s:ℝ)+2)

theorem world_affine (t : ℝ) (z : Fin 6 → Fin 2) :
    world t z = 2*(Ib (z 0) (z 1) (z 2) (z 3) (z 4) (z 5):ℝ) +
      t*(Db (z 0) (z 1) (z 2) (z 3) (z 4) (z 5):ℝ) := by
  change (1-t)*((2*Ib (z 0) (z 1) (z 2) (z 3) (z 4) (z 5):ℤ):ℝ) +
    t*((2*Ib (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)+Db (z 0) (z 1) (z 2) (z 3) (z 4) (z 5):ℤ):ℝ) = _
  push_cast; ring

theorem family_identification (s : ℤ) (hs : 1 ≤ s) : normalizedFamily s = unitWorld (1/(s:ℝ)) := by
  have hr : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hn : (s:ℝ) ≠ 0 := by linarith
  funext z
  simp only [normalizedFamily,unitWorld,world_affine,Vb]
  push_cast
  field_simp

/-- Whole-family bridge: Valid, strict selection, unit mixed-difference bound, and actual loss gap. -/
theorem normalized_family_bridge (s : ℤ) (hs : 1 ≤ s) :
    familyCell.Valid (normalizedFamily s) ∧ StrictTopC familyCell (normalizedFamily s) ∧
    UnitInteractionBound (normalizedFamily s) ∧
    2 * (productCompressionLoss (normalizedFamily s) (productResponse cornerQ2 (normalizedFamily s)) S -
      productCompressionLoss (normalizedFamily s) (productResponse cornerQ2 (normalizedFamily s)) T) = 6*(s:ℝ)/((s:ℝ)+1) := by
  have hr : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hp : 0 < 1/(s:ℝ) := one_div_pos.mpr (by linarith)
  have hu : 1/(s:ℝ) ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  rw [family_identification s hs]
  refine ⟨unit_valid _ hp.le hu,unit_strict_top _ hp hu,unit_interaction _ hp.le hu,?_⟩
  rw [unit_doubled_gap _ hp.le hu]
  field_simp
  <;> ring

/-- Sharpness in the existing chain definition, not merely arithmetic on two named sequences. -/
theorem chain_constant_six_sharp : DecisionInteractionConstantAtMost familyCell 6 ∧
    ∀ c : ℝ, c < 6 → ¬ DecisionInteractionConstantAtMost familyCell c := by
  constructor
  · intro F hValid hUnit
    have hTop : IsTopKByScore (fun i => osc (productResponse cornerQ2 F i)) S 3 := by
      simpa only [familyCell, show S.card = 3 from by decide] using hValid.2.1
    have h := constant_six_upper F 1 (by norm_num) hUnit S T hTop (by decide)
    simpa only [familyCell, mul_one] using h
  · intro c hc hBound
    obtain ⟨t,ht,ht1,hgap⟩ := every_smaller_constant_fails c hc
    have h := hBound (unitWorld t) (unit_valid t ht.le ht1) (unit_interaction t ht.le ht1)
    change 2 * (productCompressionLoss (unitWorld t) (productResponse cornerQ2 (unitWorld t)) S - productCompressionLoss (unitWorld t) (productResponse cornerQ2 (unitWorld t)) T) ≤ c at h
    rw [unit_doubled_gap t ht.le ht1] at h
    rw [world_doubled_gap t ht.le ht1] at hgap
    have hd : 0 < 2+2*t := by linarith
    have hh := (div_le_iff₀ hd).mp h
    linarith


/-- The normalization is exact: one explicit mixed difference attains the bound. -/
def interactionX : Fin 6 → Fin 2 := ![1,0,0,0,0,0]
def interactionC : Fin 6 → Fin 2 := ![0,0,0,0,1,0]
theorem endpoint_interaction_attained :
    raw 0 interactionX - raw 0 (Function.update interactionX 0 (interactionC 0)) -
      raw 0 (Function.update interactionC 0 (interactionX 0)) + raw 0 interactionC = 2 ∧
    raw 1 interactionX - raw 1 (Function.update interactionX 0 (interactionC 0)) -
      raw 1 (Function.update interactionC 0 (interactionX 0)) + raw 1 interactionC = 4 := by decide

theorem world_interaction_attained (t : ℝ) :
    mixedDifference (world t) 0 interactionX interactionC = 2+2*t := by
  have heq : mixedDifference (world t) 0 interactionX interactionC =
      mix t (raw 0 interactionX - raw 0 (Function.update interactionX 0 (interactionC 0)) -
        raw 0 (Function.update interactionC 0 (interactionX 0)) + raw 0 interactionC)
      (raw 1 interactionX - raw 1 (Function.update interactionX 0 (interactionC 0)) -
        raw 1 (Function.update interactionC 0 (interactionX 0)) + raw 1 interactionC) := by
    simp only [mixedDifference,world,mix]; push_cast; ring
  rw [heq,endpoint_interaction_attained.1,endpoint_interaction_attained.2]
  unfold mix; norm_num; ring

theorem normalized_family_interaction_attained (s : ℤ) (hs : 1 ≤ s) :
    mixedDifference (normalizedFamily s) 0 interactionX interactionC = 1 := by
  rw [family_identification s hs]
  have hr : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hd : 0 < 2+2*(1/(s:ℝ)) := by positivity
  calc _ = mixedDifference (world (1/(s:ℝ))) 0 interactionX interactionC / (2+2*(1/(s:ℝ))) := by
           simp only [mixedDifference,unitWorld]; ring
       _ = 1 := by rw [world_interaction_attained]; exact div_self (ne_of_gt hd)

/-- Exact interaction radius of the original, unnormalized integer family. -/
theorem integer_family_interaction_exact (s : ℤ) (hs : 1 ≤ s) :
    (∀ (i : Fin 6) (x c : Fin 6 → Fin 2), |mixedDifference (fun (z : Fin 6 → Fin 2) => (Vb s (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) : ℝ)) i x c| ≤ 2*(s:ℝ)+2) ∧
    mixedDifference (fun (z : Fin 6 → Fin 2) => (Vb s (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) : ℝ)) 0 interactionX interactionC = 2*(s:ℝ)+2 := by
  have hr : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hd : 0 < 2*(s:ℝ)+2 := by linarith
  have heq : ∀ i x c, mixedDifference (normalizedFamily s) i x c =
      mixedDifference (fun (z : Fin 6 → Fin 2) => (Vb s (z 0) (z 1) (z 2) (z 3) (z 4) (z 5):ℝ)) i x c / (2*(s:ℝ)+2) := by
    intro i x c; simp only [mixedDifference,normalizedFamily]; ring
  constructor
  · intro i x c
    have h := (normalized_family_bridge s hs).2.2.1 i x c
    rw [heq,abs_div,abs_of_pos hd,div_le_one hd] at h
    exact h
  · have h := normalized_family_interaction_attained s hs
    rw [heq,div_eq_one_iff_eq (ne_of_gt hd)] at h
    exact h

end CIGAMF.P13.D6M6SharpnessBridgeV1
