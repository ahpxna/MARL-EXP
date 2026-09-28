# P2 handoff (generic recourse layer, XOR game, menu vs revision) — 2026-09-27

## Files created
| File | Status |
|---|---|
| `work/p13_conjectures/LeanMarlGenericRecourseV1.lean` (M4) | COMPILES, exit 0, 0 warnings, 0 errors (log `$SCRATCH/p2/m4b.log`, 1:36 wall). Source sha256 `1323b55209cbfe3466303a29b7a38e64f67478122a10604b77db216a1a6daf5f`; olean `.lake/build/lib/lean/LeanMarlGenericRecourseV1.olean` (2026-09-27 11:57). 0 sorry, 0 native_decide. All 22 `#print axioms` = {propext, Classical.choice, Quot.sound}. Not in MODS, not gated. |
| `research/marl_budget/P2_generic_layer/PROGRESS.md` | progress log |
| `research/marl_budget/P2_generic_layer/HANDOFF.md` | this file |
| `research/marl_budget/P2_generic_layer/COMPACT.md` | NOT written: the Write was denied by the permission classifier; not retried |
| scratch: `$SCRATCH/p2/closure.py` (import-closure olean freshness check), `$SCRATCH/p2/m4.log` (compile log) | scratch only |

`$SCRATCH` = `/private/tmp/claude-502/-Users-phanan-cig-amf-main/f9537975-549f-4276-ad79-40f2fa3240e3/scratchpad`.
Not created: M3 `LeanMarlXorGameV1.lean` and M5 `LeanMarlMenuRevisionV1.lean` (stopped by the wrap-up order).

## M4 contents (`CIGAMF.P13.MarlGenericRecourse`, imports `LeanPaperCBudgetAwareV1`)
- Cost: `SetCost m := Fin (m+1) → Finset (Fin m) → ℝ`, arbitrary. Regret form
  `regretOf ℓ k S = ℓ k S − optLoss ℓ k` (`optLoss` = min over k-sets). Lemmas: `optLoss_le`,
  `exists_opt`, `regretOf_nonneg`, `optLoss_regretOf` (= 0).
- Values: `genObjective`, `genTrue` (U), `genLayer`, `genAware` (B), `genPlanCost`,
  `genRecourseSet`, `genRecourse` (V^(R)). They reuse C's band sets `FeasibleAt id η`,
  `SubFeasible`, `PlanFeasible` and C's cost-free plan tools (`push_sum`, `push_feasible`,
  `final_sum`, `final_feasible`, `idPlan*`, `indepPlan`, `indep_feasible`, `sub_nonempty`).
- Boundedness for an arbitrary real cost uses `costFloor` (min over all sets) and `le_expect`.
- Order relations for every cost: `aware_le_true`, `aware_le_recourse`, `recourse_le_true`,
  `recourse_zero`, `recourse_mono`, `recourse_full`.
- Vacuous band (η ≥ m, needs `[NeZero m]`): `band_vacuous`, `feasibleAt_vacuous_iff`,
  `subFeasible_vacuous_iff`, `planFeasible_vacuous_iff`, `genLayer_vacuous` (layer = `optLoss`),
  `genAware_vacuous_regret` (B = 0 for a regret cost), `genTrue_regret_nonneg`.
- C instance: `subCost_eq_regretOf` (subCost g = regretOf (|Σ_S g|/‖g‖₁));
  `objective_eq_gen`, `trueValue_eq_gen`, `layerValue_eq_gen`, `awareValue_eq_gen`,
  `planCost_eq_gen`, `recourseValue_eq_gen` (all `rfl`); `c_recourse_full_via_gen`,
  `c_recourse_zero_via_gen`.
- Witnesses: `interior`, `interior_nonempty`, `recourse_full_hyp_witness` (m=3, K={1,2}, R=1),
  `recourse_full_hyp_half` (R=⌊m/2⌋), `vacuous_band_witness`, `order_hyps_witness`.

## Background processes
None of mine. (The smokeOLD7 gate had its own 2 Lean processes running; not mine.)

## Next steps: M3 `LeanMarlXorGameV1.lean` (import `LeanMarlGenericRecourseV1`), designed, not written
1. Model. `World := Bool × Bool × Bool` = (X, Y, E). `wt p w := (if w.2.2 then p else 1 − p)/4`.
   `msg w i` = X⊕E, Y, X⊕Y for i = 0, 1, 2 (define by `if i.val = 0 … else if i.val = 1 …`, so it
   is kernel-decidable). `obs S w := fun i => if i ∈ S then msg w i else false` (masked transcript).
   `Dec := (Fin 3 → Bool) → Bool`.
   `teamFail p S d1 d2 := Σ_w wt p w · (if d1 (obs S w) = w.1 ∧ d2 (obs S w) = w.1 then 0 else 1)`.
   `ell p S := (univ : Finset (Dec × Dec)).inf' univ_nonempty (fun d => teamFail p S d.1 d.2)`.
2. Lower bounds by pairing, not by enumerating the 2^16 decoder pairs:
   - `teamFail ≥ fail1 d1`, where `fail1` is the single-decoder error.
   - Lemma: for an involution f with `obs S (f w) = obs S w` and `(f w).1 ≠ w.1`,
     `fail1 p S d ≥ ½ Σ_w min(wt w, wt (f w))`. Proof: reindex with `hf.toPerm` and
     `Equiv.sum_comp`, then use `e w + e (f w) ≥ 1` per world.
   - The side conditions for concrete S and f are `decide` over the 8 worlds.
   - Involutions:
     - ∅, {2}: flip X;
     - {3}: flip X, Y;
     - {1}, {1,2}: flip X, E;
     - {1,3}: flip X, Y, E.
   - An involution that keeps E gives ½·Σ wt = ½. One that flips E gives ½·8·(p/4) = p (needs p ≤ ½).
   - For {2,3} and {1,2,3} the lower bound is 0.
3. Attainment: decoders
   - const false, with error P(X = 1) = ½;
   - `v 0`, with error P(E = 1) = p;
   - `xor (v 1) (v 2)` = X, with error 0.
   Prove the per-world correctness characterisation by `decide`, then sum over the 8 worlds with
   `simp [Fintype.sum_prod_type, Fintype.sum_bool, wt]` and `ring`. Use `d1 = d2 = d`.
4. Indexing. Message j is index j−1. The best pair {2,3} is `{1,2}`. Budgets:
   `K = interior 3` = {1,2}. Regret: `regretOf (fun _ S => ell p S)`, with `optLoss` = p at k=1
   and 0 at k=2. For k=1 use `Finset.card_eq_one` and then `fin_cases`. For k=2, `ell ≥ 0`, and
   `{1,2}` attains.
5. Randomised price, lower bound for EVERY probability law P on `Equiv.Perm (Fin 3)`.
   Per σ:
   - `prefixSet σ 1 = {σ 0}`;
   - regret₁ = `if σ 0 = 0 then 0 else ½ − p`;
   - regret₂ = `if prefixSet σ 2 = {1,2} then 0 else p`, via `Finset.card_eq_two` and then
     `fin_cases`, with `decide` for literal pair equalities;
   - `σ 0 = 0 → prefixSet σ 2 ≠ {1,2}`, since σ 0 lies in the prefix.

   Then, with q = P(σ 0 = 0) and r = P(prefix₂ = {1,2}):
   - r ≤ 1 − q;
   - max(a, b) ≥ 2p·a + (1−2p)·b ≥ p(1−2p), where a = (1−q)(½−p) and b = p(1−r) ≥ pq.
6. Attainment and the U value.
   - Law: `(1−2p)·[σ = 1] + 2p·[σ = finRotate 3]`. `finRotate 3` is the order (2,3,1), and
     `1 ≠ finRotate 3` by `decide`.
   - Both budgets give expected regret p(1−2p).
   - With `feasibleAt_vacuous_iff` at η = 3, this gives
     `genTrue (regretOf ell) 3 (interior 3) _ = p(1−2p)`.
7. The rest.
   - Deterministic price: `univ.inf' (fun σ => (interior 3).sup' (regret at prefix))` =
     `min p (½ − p)`. The order (1,2,3) gives p; (2,3,1) gives ½ − p; per σ the value is ≥ one
     of the two.
   - V^(1) = B = 0: M4 `recourse_full` with `recourse_full_hyp_witness` and
     `genAware_vacuous_regret`.
   - V^(0) = U: M4 `recourse_zero`.
   - Strict gap B < U: 0 < p(1−2p).
   - Satisfiability witness: p = 1/4.

## Next steps: M5 `LeanMarlMenuRevisionV1.lean`, designed, not written
- Deterministic definitions, no band:
  - `menuDet c K n := inf over M : Fin n → Perm (Fin m) of K.sup' (fun k => inf_j c k (prefixSet (M j) k))`
    (with `n ≥ 1`);
  - `revDet c K R := inf_σ K.sup' (fun k => min over T with |T| = k, |prefix\T| ≤ R of c k T)`;
  - `awareDet c K := K.sup' (optLoss c)`.
- Theorems to prove:
  - `menuDet 1 = revDet 0`, both equal to `inf_σ max_k c(prefix)`;
  - `n ≥ K.card → menuDet = awareDet`: for each k ∈ K take σ_k with prefix_k = an optimal
    k-set (any k-set is a prefix: build σ from an ordering of S then Sᶜ), and index the menu by
    an injection K ↪ Fin n (`K.equivFin`);
  - `R ≥ min(k, m−k) ∀k → revDet = awareDet`, by C's `sdiff_card_le`;
  - `menuDet` is antitone in n.
- Randomised version with band, optional: a law on menus plus a selection rule. For n = 1 it
  collapses to `genTrue`. For n ≥ |K| it needs C's `exists_realisation`
  (`LeanPaperCCountReductionV1`) and a product law over `Fin n → Perm`. This is harder; do it
  only if needed.
- XOR separation (import M3):
  - the 2-menu {(1,2,3), (2,3,1)} with selection k=1 → first, k=2 → second has regret 0 =
    B = V^(1);
  - `menuDet 1 = min(p, ½−p) > 0`, and the randomised U = p(1−2p) > 0.
- Prefix-cover dimension: relate `menuDet` of a regret cost to Structural's χ_ε
  (`LeanStructuralPrefixCoverDimensionV1`): `menuDet ≤ ε` ⇔ `χ_ε ≤ n`, when Structural's
  ε-optimality is additive in the same regret. I have NOT read that module's definitions; if the
  notions do not match, record the relation as an open item.
- New context (coordinator): on m ≤ 6 every per-budget set system has a chain within 1 exchange
  (aa10ead), so on m ≤ 6 a menu/revision separation can only be between R = 0 and R = 1; m = 7
  fails. `LeanMarlRevisionFrontierV1` (the coordinator's) proves the D6 frontier (d_k − R)₊·δ.

## Lean pitfalls
- `baseline` lives in `CIGAMF.P13.PaperCFrontier`, which C's AwareV1 does not open. The first compile failed on
  `unfold … baseline`. Fixed by qualifying the name. `if_neg` is deprecated (use `simp [h]` or `ite_eq_right`).
- `lake env lean` loads oleans without a staleness check. In the closure of
  `LeanPaperCBudgetAwareV1`, `LeanPaperCEvenWitnessJoinV1` and `LeanPaperCFlowBandJoinV1` have
  local oleans OLDER than their sources. Both sources equal the smokeC1/C2 `report/SOURCES.sha256`
  entries (exit 0). I left the local oleans untouched, because `LeanPaperCBudgetAwareV1.olean` was
  built against them. A from-scratch gate settles it.
- `trueObjective`/`normalizedRegret` are definitionally `Σ P σ · subCost g k (prefixSet σ k)`,
  so the instance theorems are `rfl`.
- `obtain ⟨k0, hk0⟩ := id hK` avoids destructing `hK` while it still occurs in the goal (through
  `K.sup' hK`).
- The corpus decides finite Finset facts on `Fin 4` by kernel `decide` (FamiliesV1 `mixed_close`,
  `pre0..pre3`), so `∀ S : Finset (Fin 3), …` by `decide` is expected to be fast enough.
