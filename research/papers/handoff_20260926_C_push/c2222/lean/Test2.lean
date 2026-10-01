import «LeanPaperCPathMixV1»

open CIGAMF.P13.PaperCHorizon CIGAMF.P13.CFinal CIGAMF.P13.PaperCBreakpoint

def s1 : Fin 8 → Fin 4 := ![0,1,2,3,2,3,0,1]

set_option maxHeartbeats 400000 in
example : ((stC s1 3 0 : Fin 9) : ℕ) = 1 := by simp [stC, cnt, s1, Fin.sum_univ_eight]

example : ((stC s1 3 0 : Fin 9) : ℕ) = 1 := by decide

example (a b : ℝ) : a * (((stC s1 3 0 : Fin 9) : ℕ) : ℝ) + b * (((stC s1 3 2 : Fin 9) : ℕ) : ℝ) = a + b := by
  have h : stC s1 3 = ![1,1,1,0] := by decide
  rw [h]; simp

example (a b : ℝ) : a * (((stC s1 5 0 : Fin 9) : ℕ) : ℝ) + b * (((stC s1 5 2 : Fin 9) : ℕ) : ℝ) = a + 2 * b := by
  rw [show stC s1 5 = ![1,1,2,1] by decide]; simp; ring
