import «LeanPaperCPathMixV1»

open CIGAMF.P13.CFinal CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCBreakpoint

def s0 : Fin 6 → Fin 6 → Fin 4 :=
  ![![0, 1, 1, 0, 2, 3], ![0, 1, 2, 1, 3, 0], ![1, 0, 3, 2, 0, 1], ![1, 2, 0, 3, 1, 0],
    ![2, 3, 1, 0, 0, 1], ![3, 0, 0, 1, 1, 2]]
def ty : Fin 6 → Fin 4 := ![0, 0, 1, 1, 2, 3]

set_option maxRecDepth 10000 in
theorem hm : ∀ j τ, mult (s0 j) τ = mult ty τ := by decide

set_option maxRecDepth 10000 in
theorem t1 : stC (s0 2) 3 = ![1, 1, 1, 0] := by decide

set_option maxRecDepth 10000 in
theorem t2 : ∀ j : Fin 6, ∀ k : Fin 7, ∀ τ : Fin 4, ((stC (s0 j) k τ : Fin 7) : ℕ) = cnt (s0 j) k τ := by decide
