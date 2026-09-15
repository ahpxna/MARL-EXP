from pathlib import Path
import re
p=Path('work/lean/LeanD6M6SharpnessBridgeV1.lean');s=p.read_text()
a=s.index('def baseF :');b=s.index('def raw ',a)
s=s[:a]+'''open CIGAMF.P13.D6SharpnessM6V1 (Ib Db Vb)
def baseF (a b c d e f : Fin 2) : ℤ := 2 * Ib a b c d e f
def edgeF (a b c d e f : Fin 2) : ℤ := 2 * Ib a b c d e f + Db a b c d e f
'''+s[b:]
s=re.sub(r'\b(16|18|17|15|96)\b',lambda m:{'16':'2','18':'4','17':'3','15':'1','96':'12'}[m[0]],s)
s=re.sub(r'def rlo .*\n', 'def rlo (e : Fin 2) (i : Fin 6) : ℤ := (if e=0 then ![0,2,2,-4,0,0] else ![-1,1,1,-5,-1,-1]) i\n',s)
s=re.sub(r'def rhi .*\n', 'def rhi (e : Fin 2) (i : Fin 6) : ℤ := (if e=0 then ![2,4,4,-2,2,2] else ![3,5,5,-1,3,3]) i\n',s)
a=s.index('  rw [heq]\n');b=s.index('\ntheorem world_residual_bounds',a)
s=s[:a]+'''  have h01 : |world s (Function.update x i 0) - world s (Function.update x i 1) -
      (world s (Function.update c i 0) - world s (Function.update c i 1))| ≤ 2+2*s := by
    rw [abs_le]; constructor <;> linarith
  have h10 : |world s (Function.update x i 1) - world s (Function.update x i 0) -
      (world s (Function.update c i 1) - world s (Function.update c i 0))| ≤ 2+2*s := by
    rw [abs_le]; constructor <;> linarith
  rw [heq]
  generalize x i = u
  generalize c i = v
  fin_cases u <;> fin_cases v <;> first | exact h01 | exact h10 | (simp; linarith)
''' +s[b:]
# A smaller epsilon parameter is sufficient for the new scale.
s=s.replace('let s := min 1 ((6-c)/(c+1))','let s := min 1 ((6-c)/(c+1))')
p.write_text(s)
