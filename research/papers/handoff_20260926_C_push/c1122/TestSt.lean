import «LeanPaperCTwoMagSixV1»
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCBreakpoint CIGAMF.P13.CFinal CIGAMF.P13.PaperCTwoMagSix

def st (x0 x1 x2 x3 : Fin 7) : CState 4 6 := ![x0, x1, x2, x3]
def sX : Fin 6 → Fin 4 := ![0, 1, 2, 3, 2, 3]

set_option maxRecDepth 4000 in
theorem t1 : stC sX 3 = st 1 1 1 0 := by decide

theorem t2 : stC sX 3 = st 1 1 1 0 := by
  funext τ; fin_cases τ <;> simp [stC, cnt, st, sX, Fin.sum_univ_succ] <;> rfl

theorem t3 : mult sX 2 = 2 := by decide
