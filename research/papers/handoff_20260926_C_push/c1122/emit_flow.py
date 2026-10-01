"""Emit LeanPaperCTwoMag1122FlowV1.lean."""
import io, sys
_o = sys.stdout; sys.stdout = io.StringIO()
import genflow
sys.stdout = _o
from genflow import FLOWS, SEQ, N, OIDX, WDEG
from poly import *
flows_lean = open("flows_price.lean").read()
F = {
 'L0':  dict(hyps="(h2 : a ≤ 2 * b)", hn="h2", R="RL", hR="rawC_L hb hab h2", Q="6", eta="0", T="2 * (a - b) / 3", quad=None,
             doc="band `0`, budget costs at most `2(a-b)/3`, on `a ≤ 2b`"),
 'M0':  dict(hyps="(h2 : 2 * b ≤ a) (h5 : 2 * a ≤ 5 * b)", hn="h2 h5", R="RM", hR="rawC_M hb h2 (by linarith)", Q="12 * (3 * b - a)", eta="0", T="(4 * b - a) / 3",
             quad=("(sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b)", "(sub_nonneg.2 h5 : (0:ℝ) ≤ 5 * b - 2 * a)"),
             doc="band `0`, budget costs at most `(4b-a)/3`, on `2b ≤ a ≤ 5b/2`"),
 'H0M': dict(base='H0', hyps="(h5 : 5 * b ≤ 2 * a) (h3 : a ≤ 3 * b)", hn="h5 h3", R="RM", hR="rawC_M hb (by linarith) h3", Q="24", eta="0", T="(a - b) / 3", quad=None,
             doc="band `0`, budget costs at most `(a-b)/3`, on `5b/2 ≤ a ≤ 3b`"),
 'H0H': dict(base='H0', hyps="(h3 : 3 * b ≤ a)", hn="h3", R="RH", hR="rawC_H hb h3", Q="24", eta="0", T="(a - b) / 3", quad=None,
             doc="band `0`, budget costs at most `(a-b)/3`, on `3b ≤ a`"),
 'Lf':  dict(hyps="(h2 : a ≤ 2 * b)", hn="h2", R="RL", hR="rawC_L hb hab h2", Q="8", eta="1", T="(a - b) / 2", quad=None,
             doc="deviation `1`, budget costs at most `(a-b)/2`, on `a ≤ 2b`"),
 'M1f': dict(hyps="(h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b)", hn="h2 h7", R="RM", hR="rawC_M hb h2 (by linarith)", Q="8 * b", eta="1", T="(a - b) * (3 * b - a) / (2 * b)",
             quad=("(sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b)", "(sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a)"),
             doc="deviation `1`, budget costs at most `(a-b)(3b-a)/(2b)`, on `2b ≤ a ≤ 7b/3`"),
 'M23f': dict(hyps="(h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b)", hn="h7 h13", R="RM", hR="rawC_M hb (by linarith) (by linarith)", Q="4 * (11 * b - 3 * a)",
             eta="4 * (8 * b - 3 * a) / (11 * b - 3 * a)", T="2 * (a - b) * (3 * b - a) / (11 * b - 3 * a)",
             quad=("(sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b)", "(sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)"),
             doc="deviation `4(8b-3a)/(11b-3a)`, budget costs at most `2(a-b)(3b-a)/(11b-3a)`, on `7b/3 ≤ a ≤ 13b/5`"),
 'M4f': dict(hyps="(h13 : 13 * b ≤ 5 * a) (h3 : a ≤ 3 * b)", hn="h13 h3", R="RM", hR="rawC_M hb (by linarith) h3", Q="20 * (a - b)",
             eta="(5 * a - 11 * b) / (5 * (a - b))", T="2 * b / 5",
             quad=("(sub_nonneg.2 h13 : (0:ℝ) ≤ 5 * a - 13 * b)", "(sub_nonneg.2 h3 : (0:ℝ) ≤ 3 * b - a)"),
             doc="deviation `(5a-11b)/(5(a-b))`, budget costs at most `2b/5`, on `13b/5 ≤ a ≤ 3b`"),
 'Hf':  dict(hyps="(h3 : 3 * b ≤ a)", hn="h3", R="RH", hR="rawC_H hb h3", Q="10", eta="2 / 5", T="(a - b) / 5", quad=None,
             doc="deviation `2/5`, budget costs at most `(a-b)/5`, on `3b ≤ a`"),
}
def Estr(name):
    base = F[name].get('base', name)
    E = FLOWS[base][2]
    return fmt_hom(E, WDEG[base]) if trim(E) != [0] else "0"
def QTstr(name):
    base = F[name].get('base', name)
    QT = FLOWS[base][5]
    return fmt_hom(QT, WDEG[base] + 1)
out = []
out.append('''import «LeanPaperCTwoMag1122BaseV1»

/-!
# Paper C: counts `(1,1,2,2)` — the primal flows

Eighteen type sequences (six orbits under flipping all signs and reversing the order), their
prefix counts (`tq`, checked by `decide` in `tq_spec`), and eight weightings of them. Each
weighting is a count-feasible flow (`mixFlow` of `LeanPaperCPathMixV1`); for each we prove the
band it meets and a bound on every interior budget cost. The weights are `W_j / Q` with `W`, `Q`
polynomial in `a, b`; the checks are exact (`linarith`, with the products of the range constraints
for the quadratic ones).

The data come from `scratchpad/c1122/genflow.py`, which checks every weight, band and cost bound
exactly before emitting.
-/

namespace CIGAMF.P13.PaperCTwoMag1122

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCFlowBandJoin CIGAMF.P13.PaperCVacuity CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFreeBand CIGAMF.P13.PaperCFlowCert
open CIGAMF.P13.PaperCPathMix CIGAMF.P13.PaperCFrontier CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCTwoMagSix

variable {a b : ℝ}

/-! ## 1. The sequences -/
''')
out.append(flows_lean.split("/-- Weight numerators")[0])
out.append('''set_option maxRecDepth 20000 in
theorem sq_mult : ∀ j τ, mult (sq j) τ = mult ty6 τ := by
  intro j; fin_cases j <;> decide

set_option maxRecDepth 20000 in
theorem tq_spec : ∀ j : Fin 18, ∀ k : Fin 7, ∀ τ : Fin 4,
    ((stC (sq j) k τ : Fin 7) : ℕ) = tq j k τ := by
  intro j; fin_cases j <;> decide

set_option maxRecDepth 20000 in
theorem tq_sum : ∀ j : Fin 18, ∀ k : Fin 7, tq j k 0 + tq j k 1 + tq j k 2 + tq j k 3 = k.val := by
  decide

set_option maxRecDepth 20000 in
theorem tq_box : ∀ j : Fin 18, ∀ k : Fin 7,
    tq j k 0 ≤ 1 ∧ tq j k 1 ≤ 1 ∧ tq j k 2 ≤ 2 ∧ tq j k 3 ≤ 2 := by
  decide

/-! ## 2. Weighted mixtures of the sequences -/

theorem sum_wq (W : Fin 18 → ℝ) (Q : ℝ) (X : Fin 18 → ℝ) :
    ∑ j, W j / Q * X j = (∑ j, W j * X j) / Q := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem flow_feas (W : Fin 18 → ℝ) (Q : ℝ) (hQ : 0 < Q) (hw : ∀ j, 0 ≤ W j / Q)
    (hW : ∑ j, W j = Q) : CountFeasibleH ty6 (mixFlow sq (fun j => W j / Q) hw) := by
  refine mixFlow_feasible ty6 sq _ hw ?_ sq_mult
  rw [← Finset.sum_div, hW, div_self hQ.ne']

theorem flow_obj_le (hb : 0 < b) (hab : b < a) (R : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hR : ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      rawC a b x0 x1 x2 x3 = R x0 x1 x2 x3)
    (W : Fin 18 → ℝ) (Q : ℝ) (hQ : 0 < Q) (hw : ∀ j, 0 ≤ W j / Q) (T : ℝ) (k : Fin 7)
    (h : ∑ j, W j * R (tq j k 0) (tq j k 1) (tq j k 2) (tq j k 3) ≤ Q * T) :
    flowObj (typedCost ty6 (wt a b)) (mixFlow sq (fun j => W j / Q) hw) k
      ≤ T / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  rw [mix_cost hb hab sq tq tq_spec _ hw k (fun j => tq_sum j k)]
  apply div_le_div_of_nonneg_right _ hD.le
  have e : ∑ j, W j / Q * rawC a b (tq j k 0) (tq j k 1) (tq j k 2) (tq j k 3)
      = (∑ j, W j * R (tq j k 0) (tq j k 1) (tq j k 2) (tq j k 3)) / Q := by
    rw [sum_wq]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨b0, b1, b2, b3⟩ := tq_box j k
    rw [hR _ _ _ _ b0 b1 b2 b3]
  show ∑ j, W j / Q * rawC a b (tq j k 0) (tq j k 1) (tq j k 2) (tq j k 3) ≤ T
  rw [e, div_le_iff₀ hQ]
  linarith

theorem flow_band (W : Fin 18 → ℝ) (Q : ℝ) (hQ : 0 < Q) (hw : ∀ j, 0 ≤ W j / Q) (E : ℝ)
    (h : ∀ k : Fin 7, ∀ τ : Fin 4,
      |∑ j, W j * (tq j k τ : ℝ) - Q * (mult ty6 τ : ℝ) * (k.val : ℝ) / 6|
        ≤ (mult ty6 τ : ℝ) * E / 6) :
    FlowBand ty6 (mixFlow sq (fun j => W j / Q) hw) (E / Q) := by
  apply mix_band sq tq tq_spec
  intro k τ
  have hm : (0 : ℝ) < mult ty6 τ := by exact_mod_cast mult_pos τ
  have hQm : 0 < Q * (mult ty6 τ : ℝ) := mul_pos hQ hm
  show |(∑ j, W j / Q * (tq j k τ : ℝ)) / (mult ty6 τ : ℝ) - (k.val : ℝ) / 6| ≤ E / Q / 6
  rw [sum_wq]
  rw [show (∑ j, W j * (tq j k τ : ℝ)) / Q / (mult ty6 τ : ℝ) - (k.val : ℝ) / 6
      = (∑ j, W j * (tq j k τ : ℝ) - Q * (mult ty6 τ : ℝ) * (k.val : ℝ) / 6)
        / (Q * (mult ty6 τ : ℝ)) by first | (field_simp; ring) | field_simp]
  rw [abs_div, abs_of_pos hQm, div_le_iff₀ hQm]
  calc _ ≤ (mult ty6 τ : ℝ) * E / 6 := h k τ
    _ = E / Q / 6 * (Q * (mult ty6 τ : ℝ)) := by field_simp

/-! ## 3. The weightings -/
''')
wdefs = flows_lean.split("/-- Weight numerators")[1:]
for wd in wdefs:
    out.append("/-- Weight numerators" + wd)
axioms = []
for name, d in F.items():
    base = d.get('base', name)
    W = f"W_{base} a b"
    Q = d['Q']
    out.append(f"/-! ### `{name}`: {d['doc']} -/\n")
    # nonneg
    out.append("set_option maxHeartbeats 0 in")
    out.append(f"theorem flow_{name} (hb : 0 < b) (hab : b < a) {d['hyps']} :")
    out.append(f"    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F ({d['eta']})")
    out.append(f"      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ ({d['T']}) / (2 * a + 4 * b) := by")
    out.append(f"  have hQ : (0 : ℝ) < {Q} := by linarith")
    out.append(f"  have hbne : b ≠ 0 := hb.ne'")
    out.append(f"  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'")
    if name == 'M23f':
        out.append(f"  have h11 : 11 * b - 3 * a ≠ 0 := by apply ne_of_gt; linarith")
    out.append(f"  have hw : ∀ j, 0 ≤ {W} j / ({Q}) := by")
    out.append(f"    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_{base}] <;> linarith")
    out.append(f"  have hW : ∑ j, {W} j = {Q} := by simp [W_{base}, Fin.sum_univ_succ] <;> ring")
    out.append(f"  have hB := flow_band ({W}) ({Q}) hQ hw ({Estr(name)}) (by")
    out.append(f"    intro k τ")
    out.append(f"    fin_cases k <;> fin_cases τ <;>")
    out.append(f"      simp [Fin.sum_univ_succ, tq, W_{base}, mult0, mult1, mult2, mult3] <;>")
    out.append(f"      first | (rw [abs_le]; constructor <;> linarith) | linarith)")
    Tdiv = '/' in d['T'] and not d['T'].strip().endswith(('/ 3', '/ 2', '/ 5'))
    out.append(f"  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩")
    out.append(f"  · convert hB using 1")
    out.append(f"    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)")
    out.append(f"  · have hQT : ({Q}) * ({d['T']}) = {QTstr(name)} := by")
    out.append(f"      {'field_simp; ring' if Tdiv else 'ring'}")
    if d['quad']:
        lo, hi = d['quad']
        closer = f"nlinarith [mul_nonneg {lo} {hi}, mul_nonneg {lo} {lo}, mul_nonneg {hi} {hi}, hb]"
    else:
        closer = "linarith"
    out.append(f"    refine flow_obj_le hb hab ({d['R']} a b) ({d['hR']}) _ _ hQ hw _ k ?_")
    out.append(f"    rw [hQT]")
    out.append(f"    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk")
    out.append(f"    rcases hk with rfl | rfl | rfl | rfl | rfl <;>")
    out.append(f"      simp [Fin.sum_univ_succ, tq, W_{base}, {d['R']}] <;> {closer}")
    out.append("")
    axioms.append(f"flow_{name}")
for ax in ["sq_mult", "tq_spec", "flow_feas", "flow_obj_le", "flow_band"] + axioms:
    out.append(f"#print axioms {ax}")
out.append("\nend CIGAMF.P13.PaperCTwoMag1122")
open("/Users/phanan/cig-amf-main/work/p13_conjectures/LeanPaperCTwoMag1122FlowV1.lean", "x").write("\n".join(out))
print("emitted")
