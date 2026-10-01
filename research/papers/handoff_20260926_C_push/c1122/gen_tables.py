"""Emit Lean match tables for the raw cost per regime: coefficients (ca, cb) of a and b."""
import itertools
from fractions import Fraction as Fr
n = (1, 1, 2, 2)
box = [v for v in itertools.product(*[range(t + 1) for t in n])]
def cost_ab(v, reg):
    p, q = v[0] - v[1], v[2] - v[3]
    k = sum(v)
    samp = {'L': Fr(3, 2), 'M': Fr(5, 2), 'H': Fr(4)}[reg]
    s = p * samp + q
    sg = 1 if s > 0 else (-1 if s < 0 else 0)
    ca, cb = sg * p, sg * q
    bl = {1: (0, 1), 5: (0, 1), 3: {'L': (-1, 2), 'M': (1, -2), 'H': (0, 1)}[reg]}.get(k, (0, 0))
    return ca - bl[0], cb - bl[1]
def lin(ca, cb):
    parts = []
    if ca:
        parts.append(("" if ca == 1 else ("-" if ca == -1 else f"{ca} * ")) + "a")
    if cb:
        s = ("" if cb == 1 else ("-" if cb == -1 else f"{cb} * ")) + "b"
        parts.append(s)
    if not parts:
        return "0"
    out = parts[0]
    for p in parts[1:]:
        out += (" - " + p[1:]) if p.startswith("-") else (" + " + p)
    return out
for reg in "LMH":
    print(f"/-- The raw cost table on regime {reg}. -/")
    print(f"def R{reg} (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ")
    for v in box:
        print(f"  | {v[0]}, {v[1]}, {v[2]}, {v[3]} => {lin(*cost_ab(v, reg))}")
    print("  | _, _, _, _ => 0\n")
