# Paper C sharpness / one-exchange (agent log)

## Numerical discovery (layers.py, mid.py)
- even m: B_1 = B_{m-1} = 4max(1-eta,0)/(mD); all middle layers 0 for all eta>=0.
  => B(eta) = 4 max(1-eta,0)/(mD) for all eta >= 0.
- odd m: B_{m-1} = max(m+3-(m+1)eta, m+1-(m-1)eta, 0)/(mD); B_1 <= it; odd middle layers 0;
  even middle layers 2j: max(2j - s eta,0)/(mD) (below B_{m-1}).
  => B(eta) = max(m+3-(m+1)eta, m+1-(m-1)eta, 0)/(mD).

## Plan
1. generic: symmetrised typed law over WPerm g -> layer upper bound.
2. drop laws for k=1,m-1.
3. middle layer laws (count vectors).
4. second odd certificate beta=2 on -1's, alpha=3-m.

## Status at STOP (coordinator request)
- Laws verified EXACTLY with fractions: check_laws.py (middle layers, 666 cases), check_drop.py (drop laws k=1,m-1, all regimes).
- Lean: /Users/phanan/cig-amf-main/work/p13_conjectures/LeanPaperCBudgetSymV1.lean written; last compile: ONE error
  at line ~152 (exists_sym_law, sum-to-one bullet: `rw [h1, sym_avg ...]` pattern mismatch because h1 already
  simplified `* 1`). Everything else elaborates; orbitCount_eq, sub_mix, layer_le_mix, layer_le_drop1,
  layer_le_dropc, typed_set clean [propext, Classical.choice, Quot.sound]; exists_sym_law/exists_counts_law carry
  sorryAx only through that one error. No olean written for this module (error).
  Fix: replace that bullet by
    `rw [symLaw_sum g T q (fun _ => 1) ▸ ...]` -- simplest: 
    `have h1 := symLaw_sum g T q (fun _ => 1); rw [show (∑ S, symLaw g T q S) = ∑ S, symLaw g T q S * 1 by simp, h1,
       sym_avg g T q (fun _ => 1) (fun _ => 1) (fun x => by simp)]; simpa using hq1`
- LeanPaperCBudgetSharpV1.lean NOT yet written (main theorems aware_even_exact / aware_odd_exact / sharpness).
