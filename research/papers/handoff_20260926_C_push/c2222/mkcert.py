"""Generate Lean certificate definitions + EdgeOK proofs from gen.py potentials."""
import itertools
from fractions import Fraction as Fr
from sym import P
import gen
STATES=[u for u in itertools.product(range(3),repeat=4)]
def lean_frac(x):
    x=Fr(x)
    if x.denominator==1: return "%d"%x.numerator if x>=0 else "(%d)"%x.numerator
    return "(%d / %d)"%(x.numerator,x.denominator) if x>=0 else "(-%d / %d)"%(-x.numerator,x.denominator)
def phi_def(nm, phi):
    lines=["noncomputable def %s (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ"%nm]
    for v in STATES:
        e=phi[v]
        lines.append("  | %d, %d, %d, %d => %s"%(v+(e.lean(),)))
    lines.append("  | _, _, _, _ => 0")
    return '\n'.join(lines)
def mu_def(nm, mu):
    lines=["noncomputable def %s : ℕ → ℝ"%nm]
    for k in sorted(mu):
        lines.append("  | %d => %s"%(k, lean_frac(mu[k])))
    lines.append("  | _ => 0")
    return '\n'.join(lines)
