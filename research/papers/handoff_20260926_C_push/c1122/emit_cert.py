"""Emit LeanPaperCTwoMag1122CertV1.lean from verified certificate data."""
import io, sys
_o = sys.stdout; sys.stdout = io.StringIO()
import gencert
from gencert import make, box
sys.stdout = _o
from fractions import Fraction as Fr
from poly import *

def hom(p, deg):
    return fmt_hom(p, deg)

# name, M, Lb, reg, t0, t1, deg, psi0, inf, degM, degPsi, q (lean), region hyps, R name, hR tactic, target, quadratic?
C = gencert.certs
meta = {
 'AL':   dict(q="4", hyps="(h2 : a ≤ 2 * b)", R="RL", hR="rawC_L hb hab h2", quad=False,
              doc="the line `(a-b)(2/3 - η/6)` on `a ≤ 2b`"),
 'AM':   dict(q="4", hyps="(h2 : 2 * b ≤ a) (h5 : 2 * a ≤ 5 * b)", R="RM", hR="rawC_M hb h2 (by linarith)", quad=False,
              doc="the line `(4b-a)/3 - η(a-b)/6` on `2b ≤ a ≤ 5b/2`"),
 'Band': dict(q="2", hyps="", R="RL", hR=None, quad=False,
              doc="the band line `(a-b)(1-η)/3` at every ratio"),
 'Lf':   dict(q="4", hyps="(h2 : a ≤ 2 * b)", R="RL", hR="rawC_L hb hab h2", quad=False,
              doc="the free value `(a-b)/2` on `a ≤ 2b`"),
 'M1f':  dict(q="4 * b", hyps="(h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b)", R="RM", hR="rawC_M hb h2 (by linarith)", quad=True,
              lo="(sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b)", hi="(sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a)",
              doc="the free value `(a-b)(3b-a)/(2b)` on `2b ≤ a ≤ 7b/3`"),
 'M23f': dict(q="11 * b - 3 * a", hyps="(h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b)", R="RM", hR="rawC_M hb (by linarith) (by linarith)", quad=True,
              lo="(sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b)", hi="(sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)",
              doc="the free value `2(a-b)(3b-a)/(11b-3a)` on `7b/3 ≤ a ≤ 13b/5`"),
 'M4f':  dict(q="5", hyps="(h13 : 13 * b ≤ 5 * a) (h3 : a ≤ 3 * b)", R="RM", hR="rawC_M hb (by linarith) h3", quad=False,
              doc="the free value `2b/5` on `13b/5 ≤ a ≤ 3b`"),
 'Hf':   dict(q="5", hyps="(h3 : 3 * b ≤ a)", R="RH", hR="rawC_H hb h3", quad=False,
              doc="the free value `(a-b)/5` on `3b ≤ a`"),
}
hypnames = {'AL': "h2", 'AM': "h2 h5", 'Band': "", 'Lf': "h2", 'M1f': "h2 h7", 'M23f': "h7 h13", 'M4f': "h13 h3", 'Hf': "h3"}

def ifchain(d, deg, var="k"):
    parts = []
    for k in range(1, 6):
        if k in d and trim(d[k]) != [0]:
            parts.append((k, hom(d[k], deg)))
    s = ""
    for k, e in parts:
        s += f"if {var} = {k} then {e} else "
    s += "0"
    return s

out = []
out.append('''import «LeanPaperCTwoMag1122BaseV1»

/-!
# Paper C: counts `(1,1,2,2)` — the dual certificates

Eight certificates for `cert6` (`LeanPaperCTwoMag1122BaseV1`), each with budget weights `M`, band
multipliers `L` on the two `a`-types and potentials `P` on the 36 count states, all polynomial in
`a, b`. Each edge inequality is checked on its ratio range by `linarith`; for the two
certificates with weights linear in `a/b` (`M1f`, `M23f`) the edge slacks are quadratic forms and
the check uses the three products of the range constraints (a Bernstein certificate), so it holds
on the whole range, not at sample points.

The generated tables come from `scratchpad/c1122/gencert.py`, which also checks every edge exactly
in rational arithmetic before emitting.

| cert | range | lower bound on `D·V_g(η)` |
|---|---|---|
| `AL` | `a ≤ 2b` | `(a-b)(2/3 - η/6)` |
| `AM` | `2b ≤ a ≤ 5b/2` | `(4b-a)/3 - η(a-b)/6` |
| `Band` | every ratio | `(a-b)(1-η)/3` |
| `Lf` | `a ≤ 2b` | `(a-b)/2` |
| `M1f` | `2b ≤ a ≤ 7b/3` | `(a-b)(3b-a)/(2b)` |
| `M23f` | `7b/3 ≤ a ≤ 13b/5` | `2(a-b)(3b-a)/(11b-3a)` |
| `M4f` | `13b/5 ≤ a ≤ 3b` | `2b/5` |
| `Hf` | `3b ≤ a` | `(a-b)/5` |
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
''')
axioms = []
for (name, M, Lb, reg, t0, t1, deg, psi0, inf, degM, degPsi) in C:
    Psi, ok = make(name, M, Lb, reg, t0, t1, deg, psi0, inf)
    assert ok
    md = meta[name]
    out.append(f"/-! ## Certificate `{name}`: {md['doc']} -/\n")
    out.append(f"noncomputable def M_{name} (a b : ℝ) (k : ℕ) : ℝ := {ifchain(M, degM)}\n")
    out.append(f"noncomputable def L_{name} (a b : ℝ) (k : ℕ) : ℝ := {ifchain(Lb, degPsi)}\n")
    out.append(f"noncomputable def P_{name} (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ")
    for v in box:
        out.append(f"  | {v[0]}, {v[1]}, {v[2]}, {v[3]} => {hom(Psi[v], degPsi)}")
    out.append("  | _, _, _, _ => 0\n")
    hyps = md['hyps']
    hn = hypnames[name]
    # edge lemma
    if md['quad']:
        closer = f"nlinarith [mul_nonneg {md['lo']} {md['hi']}, mul_nonneg {md['lo']} {md['lo']}, mul_nonneg {md['hi']} {md['hi']}]"
        closer = f"linarith [mul_nonneg {md['lo']} {md['hi']}, mul_nonneg {md['lo']} {md['lo']}, mul_nonneg {md['hi']} {md['hi']}]"
    else:
        closer = "linarith"
    out.append("set_option maxHeartbeats 8000000 in")
    out.append(f"theorem edge_{name} (hb : 0 < b) (hab : b < a) {hyps} :")
    out.append(f"    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →")
    out.append(f"      EdgeOK (M_{name} a b) (L_{name} a b) ({md['R']} a b) (P_{name} a b) x0 x1 x2 x3 := by")
    out.append(f"  intro x0 x1 x2 x3 h0 h1 h2' h3'")
    out.append(f"  unfold EdgeOK")
    out.append(f"  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>")
    out.append(f"    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>")
    out.append(f"    first")
    out.append(f"    | (exfalso; omega)")
    out.append(f"    | (norm_num [M_{name}, L_{name}, {md['R']}, P_{name}] <;> {closer})")
    out.append("")
    # hR
    if md['hR'] is None:
        hRproof = f"""by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    by_cases hk : x0 + x1 + x2 + x3 = 3
    · rw [hk]; simp [M_{name}]
    · rw [rawC_off3 hb hab _ _ _ _ h0 h1 h2' h3' hk]"""
    else:
        hRproof = f"""by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [{md['hR']} _ _ _ _ h0 h1 h2' h3']"""
    # penalty
    pen_terms = []
    for k in range(1, 6):
        if k in Lb and trim(Lb[k]) != [0]:
            pen_terms.append((k, hom(Lb[k], degPsi), Lb[k]))
    # lower lemma: returns the raw cert bound
    Mnn = "by intro k; simp only [M_" + name + "]; split_ifs <;> linarith"
    out.append(f"theorem cert_{name} (hb : 0 < b) (hab : b < a) {hyps} (η : ℝ) (hη : 0 ≤ η) :")
    out.append(f"    (P_{name} a b 0 0 0 0 - η / 3 * (|L_{name} a b 1| + |L_{name} a b 2| + |L_{name} a b 3|")
    out.append(f"      + |L_{name} a b 4| + |L_{name} a b 5|)) / (({md['q']}) * (2 * a + 4 * b))")
    out.append(f"      ≤ trueValue (g6 a b) η K5 K5_ne := by")
    out.append(f"  have hq : (0 : ℝ) < {md['q']} := by linarith")
    out.append(f"  refine cert6 hb hab _ hq (M_{name} a b) (L_{name} a b) ({md['R']} a b) (P_{name} a b)")
    out.append(f"    ({Mnn}) (by simp [M_{name}]) (by simp [L_{name}]) (by norm_num [M_{name}] <;> ring)")
    out.append(f"    ({hRproof})")
    out.append(f"    (edge_{name} hb hab {hn}) (by simp [P_{name}]) η hη")
    out.append("")
    axioms += [f"edge_{name}", f"cert_{name}"]
for ax in axioms:
    out.append(f"#print axioms {ax}")
out.append("\nend CIGAMF.P13.PaperCTwoMag1122")
open("/Users/phanan/cig-amf-main/work/p13_conjectures/LeanPaperCTwoMag1122CertV1.lean", "x").write("\n".join(out))
print("emitted")
