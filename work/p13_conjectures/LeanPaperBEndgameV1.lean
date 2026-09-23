import «LeanPaperBKernelV1»
import «LeanPaperBSafeOrderV1»
import «LeanPaperBTipV1»
import «LeanPaperBDecoderV1»

/-!
DRAFT ENDGAME — not compiled. Downstream of the density/transcript/decoder work already
assigned. The new work is the operational MINIMAX join, not another two-point calculation.
Both tasks use ONE Experiment, hence the same query restrictions, transcript law and cost.

An Experiment is a typed interface, NOT a proved realization of a Gaussian policy. The
worker must instantiate it from the concrete stopped-kernel protocol. In particular allowed
must enforce predictable queries and outputs measurable at the stopping time; do NOT use
allowed := True for arbitrary functions of a full future stream.

HardPairCertificate and DecoderWitness below are explicit remaining integration inputs.
Their existence is NOT asserted here. All statements depending on them remain conditional.
The lower certificate uses klDiv of the actual law in this interface, not a free real 'KL'.
-/
namespace CIGAMF.P13.PaperBEndgame
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.PaperBTip

variable {W A Pol Ω : Type*} [Fintype W] [Nonempty W] [MeasurableSpace Ω]

inductive Task where
  | safe
  | identify

structure Experiment (W A Pol Ω : Type*) [MeasurableSpace Ω] where
  law : ℝ → Pol → W → Measure Ω
  probability : ∀ h π w, IsProbabilityMeasure (law h π w)
  allowed : Pol → Prop
  tau : Pol → Ω → ℕ∞
  answer : Pol → Ω → A
  guess : Pol → Ω → W
  loss : W → A → ℝ
  tolerance : ℝ
  tau_measurable : ∀ π, Measurable (tau π)

noncomputable def wrong (E : Experiment W A Pol Ω) (task : Task) (π : Pol) (w : W) : Set Ω :=
  match task with
  | .safe => {ω | E.tolerance < E.loss w (E.answer π ω)}
  | .identify => {ω | E.guess π ω ≠ w}

/-- Nontermination is not silently removed by conditioning on the runs that stopped. -/
def Correct (E : Experiment W A Pol Ω) (task : Task) (h δ : ℝ) (π : Pol) : Prop :=
  E.allowed π ∧ ∀ w,
    E.law h π w {ω | E.tau π ω = ⊤} = 0 ∧
    E.law h π w (wrong E task π w) ≤ ENNReal.ofReal δ

noncomputable def costAt (E : Experiment W A Pol Ω) (h : ℝ) (π : Pol) (w : W) : ℝ≥0∞ :=
  ∫⁻ ω, (E.tau π ω).toENNReal ∂E.law h π w

noncomputable def worstCost (E : Experiment W A Pol Ω) (h : ℝ) (π : Pol) : ℝ≥0∞ :=
  ⨆ w, costAt E h π w

/-- ENNReal makes an empty admissible class have cost infinity, not the real sInf default 0. -/
noncomputable def complexity (E : Experiment W A Pol Ω) (task : Task) (h δ : ℝ) : ℝ≥0∞ :=
  ⨅ π : {π : Pol // Correct E task h δ π}, worstCost E h π.val

/-- Upstream continuous-transcript + safe-obstruction obligations, with the hard-pair set
made explicit. It need not contain all pairs of worlds. For safe decisions it must be
selected using an unsafe obstruction, not an arbitrary pair that shares a safe answer. -/
structure HardPairCertificate (E : Experiment W A Pol Ω) (task : Task) (h δ : ℝ)
    (info demand : ℝ≥0∞) where
  hard : W → W → Prop
  find_pair : ∀ π, Correct E task h δ π → ∃ w v, hard w v ∧
    demand ≤ klDiv (E.law h π w) (E.law h π v)
  stopped_information : ∀ π, E.allowed π → ∀ w v, hard w v →
    klDiv (E.law h π w) (E.law h π v) ≤ info * costAt E h π w

/-- Upstream decoder construction. ONE policy works at every hidden world; it is not chosen
using w. Its query count includes every query/test and any pilot stage. -/
structure DecoderWitness (E : Experiment W A Pol Ω) (task : Task) (h δ : ℝ) (budget : ℝ≥0∞) where
  code : Pol
  correct : Correct E task h δ code
  cost : ∀ w, costAt E h code w ≤ budget

/-- From the stopped change-of-measure to an operational lower bound for EVERY algorithm. -/
theorem every_policy_cost (E : Experiment W A Pol Ω) (task : Task) (h δ : ℝ)
    (info demand : ℝ≥0∞) (hi0 : info ≠ 0) (hiTop : info ≠ ⊤)
    (L : HardPairCertificate E task h δ info demand)
    (π : Pol) (hπ : Correct E task h δ π) :
    demand/info ≤ worstCost E h π := by
  obtain ⟨w,v,hwv,hd⟩ := L.find_pair π hπ
  have hinfo := hd.trans (L.stopped_information π hπ.1 w v hwv)
  have hdiv : demand/info ≤ costAt E h π w := by
    apply (ENNReal.div_le_iff hi0 hiTop).2
    simpa [mul_comm] using hinfo
  exact hdiv.trans (le_iSup (costAt E h π) w)

theorem minimax_sandwich (E : Experiment W A Pol Ω) (task : Task) (h δ : ℝ)
    (info demand budget : ℝ≥0∞) (hi0 : info ≠ 0) (hiTop : info ≠ ⊤)
    (L : HardPairCertificate E task h δ info demand)
    (U : DecoderWitness E task h δ budget) :
    demand/info ≤ complexity E task h δ ∧ complexity E task h δ ≤ budget := by
  constructor
  · exact le_iInf (fun π => every_policy_cost E task h δ info demand hi0 hiTop L π.val π.property)
  · exact (iInf_le _ ⟨U.code,U.correct⟩).trans (iSup_le U.cost)

noncomputable def scale (h δ : ℝ) (s : ℕ) : ℝ := Real.log (1/δ) / h^(2*s)

/-- Quantifiers are part of the endpoint: constants are uniform in h and delta on this
rectangle, but may depend on the FIXED model, query class, number of worlds and order. -/
def HasRate (E : Experiment W A Pol Ω) (task : Task) (s : ℕ) : Prop :=
  ∃ c C h₀ δ₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ 0<δ₀ ∧ δ₀<1 ∧
    ∀ h δ, 0 < h → h ≤ h₀ → 0<δ → δ≤δ₀ →
      ENNReal.ofReal (c*scale h δ s) ≤ complexity E task h δ ∧
      complexity E task h δ ≤ ENNReal.ofReal (C*scale h δ s)

/-- The final theorem must produce THESE two rates for the SAME E. This definition does
not assert that all arbitrary safe families admit such polynomial orders. -/
def SeparatedTasksFinish (E : Experiment W A Pol Ω) (s r : ℕ) : Prop :=
  s < r ∧ HasRate E .safe s ∧ HasRate E .identify r

/-- Exact algebra for the rate separation; this avoids presenting two unrelated fitted
slopes as a separation theorem. Costs here are positive finite minimax costs. -/
theorem rate_ratio_lower (Ns Ni c C h δ : ℝ) (s d : ℕ)
    (hNs : 0 < Ns) (hc : 0 < c) (hC : 0 < C) (hh : 0 < h) (hδ : 0<δ) (hδ1 : δ<1)
    (hU : Ns ≤ C*scale h δ s) (hL : c*scale h δ (s+d) ≤ Ni) :
    (c/C)/h^(2*d) ≤ Ni/Ns := by
  have hlog : 0 < Real.log (1/δ) := Real.log_pos ((one_lt_div hδ).2 hδ1)
  have hupper : 0 < C*scale h δ s := by unfold scale; positivity
  have hbase : (c*scale h δ (s+d))/(C*scale h δ s) ≤ Ni/Ns := by
    apply div_le_div₀ (le_trans (by unfold scale; positivity) hL) hL hNs hU
  have heq : (c*scale h δ (s+d))/(C*scale h δ s) = (c/C)/h^(2*d) := by
    unfold scale
    rw [Nat.mul_add, pow_add]
    field_simp; try ring
  rwa [heq] at hbase

/-- Actual support geometry join. This relates correctness of the output to selectedRadius;
it says NOTHING about which observation law realizes the resolving-order table. -/
noncomputable def tipLoss (m : ℕ) (w a : Fin m) : ℝ := selectedRadius (comp m w) {a}

theorem tip_wrong_iff (m : ℕ) (hm : 2 ≤ m) (ε : ℝ) (hε : 0≤ε)
    (hεmax : ε<((m:ℝ)-1)/2) (w a : Fin m) :
    ε < tipLoss m w a ↔ a=w := by
  have hs := safe_iff_ne m hm ε hε hεmax w a
  change ε < selectedRadius (comp m w) {a} ↔ a=w
  simpa only [not_le, not_ne_iff] using not_congr hs

/-- The finite decision geometry alone only licenses the output task; it cannot license
HasRate. To finish B, instantiate E.law from its continuous policy kernels, discharge
HardPairCertificate for the unresolved obstruction, and DecoderWitness for the actual
queries. Do not instantiate a different E for the identification inequality. -/
def TipFinish (m : ℕ) (hm : 3 ≤ m) (E : Experiment (Fin m) (Fin m) Pol Ω) : Prop :=
  (∀ w a, E.loss w a = tipLoss m w a) ∧
  0 ≤ E.tolerance ∧ E.tolerance < ((m:ℝ)-1)/2 ∧
  SeparatedTasksFinish E 1 (m-1)

/-- A law with a tolerance above the entire loss range has a zero-query safe solution.
This elementary endpoint prevents an unconditional positive-rate claim in that regime. -/
theorem zero_cost_endpoint (E : Experiment W A Pol Ω) (h δ : ℝ)
    (U : DecoderWitness E .safe h δ 0) : complexity E .safe h δ = 0 := by
  apply le_antisymm _ bot_le
  exact (iInf_le _ ⟨U.code,U.correct⟩).trans (iSup_le U.cost)

#print axioms every_policy_cost
#print axioms minimax_sandwich
#print axioms rate_ratio_lower
#print axioms tip_wrong_iff
#print axioms zero_cost_endpoint
end CIGAMF.P13.PaperBEndgame
