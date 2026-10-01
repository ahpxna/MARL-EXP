import «LeanPaperASacrificeIdealV1»
import «LeanPaperBStoppedLawV1»

/-!
# Paper A: the sacrifice budget can be spread over any run length

`sacrifice_cost_law` (`LeanPaperASacrificeV1`) says every `delta`-correct policy has
`N * sacrifice(wbar) >= 8 r M D`: what must be given up is a BUDGET of surrogate value, not a
fraction.  This module proves that a budget, once paid, can be spread over an arbitrarily long
run: the relative sacrifice can be made as small as `N0 / (N0 + 4k)` without losing correctness,
while the budget stays where it was.

* `sacrifice_mix_le`: at the design level, mixing any allocation `w0` with weight `beta` into the
  surrogate optimum `wUnifC` gives up at most `beta * sacrifice(w0)` (concavity of the frozen
  value, `value_concave`, and `J_fr(wUnifC) >= 9/512`).
* `padPol pi0 n`: run `pi0` for `n` rounds, then query the four `A` cells round-robin.  The
  padding is surrogate-optimal and reads nothing.
* `pad_real`: the padded policy's first `n` rounds have the law of `pi0`, so it is correct with
  the same answer event read on the first `n` rounds.
* `lintegral_cnt_pad`, `expCnt_pad_A`, `expCnt_pad_mid`: after `4k` padded rounds every `A` cell
  has `k` more expected queries and every middle cell none.
* **`dilution`**: for every `k`, the padded policy is `delta`-correct, has `N = N0 + 4k`
  expected real queries, satisfies the law `8 r M D <= N * sacrifice(wbar)`, and spends no more
  budget than `pi0`: `N * sacrifice(wbar) <= N0 * sacrifice(wbar0)`.  Its relative sacrifice is
  therefore at most `N0 / (N0 + 4k)`.

Scope: Paper A's centred family (`thetaC r`, `famChan`), strict alternatives, finite-horizon
randomised adaptive `pi0`.  With `pi0` the truncated ideal learner (`ideal_sacrifice`),
`N0 <= E tau = O(r M log(1/delta))`, so for every run length `N >= N0` (in steps of four) there
is a `delta`-correct policy whose relative sacrifice is at most `N0 / N`.
-/

namespace CIGAMF.P13.PaperASacrificeDilute

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy
open CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperAActualDecisionBridge CIGAMF.P13.PaperAStrict
open CIGAMF.P13.PaperACentred CIGAMF.P13.PaperARPair CIGAMF.P13.PaperAGaussianKL
open CIGAMF.P13.PaperAFamilyLower CIGAMF.P13.PaperAFrontier CIGAMF.P13.PaperASacrifice

variable {r : ℕ}

/-! ## 1. Dilution at the design level -/

/-- **Mixing into the surrogate optimum gives up at most `beta` of the mixed-in sacrifice.** -/
theorem sacrifice_mix_le (M : ℝ) (hM : 0 < M) (w0 : Cell r → ℝ) (hw0 : IsAlloc w0) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    sacrifice M (mixW β (wUnifC r) w0) ≤ β * sacrifice M w0 := by
  have hconc := value_concave (FrozenAltC₀ r) M hM (wUnifC r) w0 (wUnifC_isAlloc r).1 hw0.1 β
    hβ0 hβ1
  have hufr : (9 : ℝ) / 512 ≤ frozenValueC₀ M (wUnifC r) :=
    le_trans (frozenValueC_unif_ge M hM)
      (frozenValueC_le_restricted M hM (wUnifC r) (wUnifC_isAlloc r).1)
  have hconc' : (1 - β) * frozenValueC₀ M (wUnifC r) + β * frozenValueC₀ M w0
      ≤ frozenValueC₀ M (mixW β (wUnifC r) w0) := hconc
  have h1 : (1 - β) * (9 / 512) ≤ (1 - β) * frozenValueC₀ M (wUnifC r) :=
    mul_le_mul_of_nonneg_left hufr (by linarith)
  unfold sacrifice
  nlinarith

/-! ## 2. The padded policy -/

/-- The `k`-th padding query: the `A` cells round-robin. -/
def padQ (k : ℕ) : Cell r ⊕ Unit := Sum.inl (Sum.inl ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩)

/-- **Run `pi0` for `n` rounds, then pad with the surrogate optimum, round-robin.** -/
noncomputable def padPol (π0 : Policy (Cell r ⊕ Unit)) (n : ℕ) : Policy (Cell r ⊕ Unit) where
  step k := if k < n then π0.step k
    else Kernel.deterministic (fun _ => padQ (r := r) (k - n)) measurable_const
  markov k := by
    split_ifs
    · exact π0.markov k
    · infer_instance

theorem padPol_lt (π0 : Policy (Cell r ⊕ Unit)) (n k : ℕ) (hk : k < n) :
    (padPol π0 n).step k = π0.step k := by
  show (if k < n then _ else _) = _
  rw [if_pos hk]

theorem padPol_ge (π0 : Policy (Cell r ⊕ Unit)) (n k : ℕ) (hk : n ≤ k) :
    (padPol π0 n).step k
      = Kernel.deterministic (fun _ => padQ (r := r) (k - n)) measurable_const := by
  show (if k < n then _ else _) = _
  rw [if_neg (by omega)]

theorem pad_hist_n {W : Type*} (C : Channel W (Cell r ⊕ Unit)) (π0 : Policy (Cell r ⊕ Unit))
    (n : ℕ) (w : W) : hist C (padPol π0 n) w n = hist C π0 w n :=
  CIGAMF.P13.PaperBStoppedLaw.hist_congr C _ _ w n fun k hk => padPol_lt π0 n k hk

/-- **The padded run's first `n` rounds have the law of `pi0`.** -/
theorem pad_real {W : Type*} (C : Channel W (Cell r ⊕ Unit)) (π0 : Policy (Cell r ⊕ Unit))
    (n m : ℕ) (w : W) (S : Set (Hist (Cell r ⊕ Unit) n)) (hS : MeasurableSet S) :
    (hist C (padPol π0 n) w (n + m)).real
        ((CIGAMF.P13.PaperBStoppedLaw.hRestr n (Nat.le_add_right n m)) ⁻¹' S)
      = (hist C π0 w n).real S := by
  rw [← map_measureReal_apply
    (CIGAMF.P13.PaperBStoppedLaw.measurable_hRestr n (Nat.le_add_right n m)) hS,
    CIGAMF.P13.PaperBStoppedLaw.hist_map_restr C _ w n m, pad_hist_n]

theorem measurableSet_pad (n m : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n)) (hS : MeasurableSet S) :
    MeasurableSet ((CIGAMF.P13.PaperBStoppedLaw.hRestr n (Nat.le_add_right n m)) ⁻¹' S) :=
  CIGAMF.P13.PaperBStoppedLaw.measurable_hRestr n (Nat.le_add_right n m) hS

/-! ## 3. The padded counts -/

/-- The number of padding rounds among the first `m` that query `q`. -/
noncomputable def padCnt (q : Cell r ⊕ Unit) (m : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range m, if padQ (r := r) j = q then 1 else 0

theorem lintegral_cnt_pad {W : Type*} (C : Channel W (Cell r ⊕ Unit))
    (π0 : Policy (Cell r ⊕ Unit)) (n : ℕ) (w : W) (q : Cell r ⊕ Unit) :
    ∀ m, ∫⁻ ω, cntQ q (n + m) ω ∂hist C (padPol π0 n) w (n + m)
      = ∫⁻ ω, cntQ q n ω ∂hist C π0 w n + padCnt q m
  | 0 => by
      simp only [Nat.add_zero, padCnt, Finset.range_zero, Finset.sum_empty, add_zero]
      rw [pad_hist_n]
  | m + 1 => by
      have ih := lintegral_cnt_pad C π0 n w q m
      have hq : ∀ k (ω : Hist (Cell r ⊕ Unit) k),
          cntQ q k ω = qsum (fun q' => if q' = q then 1 else 0) k ω := fun k ω => rfl
      simp_rw [hq] at ih ⊢
      rw [show n + (m + 1) = (n + m) + 1 from rfl, lintegral_qsum_succ, ih]
      haveI := hist_prob C (padPol π0 n) w (n + m)
      haveI := (padPol π0 n).markov (n + m)
      have hstep := padPol_ge π0 n (n + m) (Nat.le_add_right n m)
      have hf : Measurable fun x : Hist (Cell r ⊕ Unit) (n + m) × (Cell r ⊕ Unit) =>
          (if x.2 = q then (1 : ℝ≥0∞) else 0) :=
        (Measurable.of_discrete (f := fun q' : Cell r ⊕ Unit => if q' = q then (1 : ℝ≥0∞) else 0)).comp
          measurable_snd
      rw [Measure.lintegral_compProd hf]
      have hin : ∀ a : Hist (Cell r ⊕ Unit) (n + m),
          ∫⁻ q', (if q' = q then (1 : ℝ≥0∞) else 0) ∂((padPol π0 n).step (n + m) a)
            = if padQ (r := r) m = q then 1 else 0 := by
        intro a
        rw [hstep, Kernel.deterministic_apply, lintegral_dirac]
        simp
      simp_rw [hin]
      rw [lintegral_const, measure_univ, mul_one, padCnt, padCnt, Finset.sum_range_succ, add_assoc]

theorem padCnt_A (i : Fin 4) : ∀ k, padCnt (r := r) (Sum.inl (Sum.inl i)) (4 * k) = k
  | 0 => by simp [padCnt]
  | k + 1 => by
      rw [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by ring]
      unfold padCnt
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have ih := padCnt_A i k
      unfold padCnt at ih
      rw [ih]
      have e : ∀ t : ℕ, t < 4 → (padQ (r := r) (4 * k + t) = Sum.inl (Sum.inl i) ↔ t = i) := by
        intro t ht
        unfold padQ
        simp only [Sum.inl.injEq, Fin.ext_iff]
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt ht]
      have e0 := e 0 (by norm_num)
      have e1 := e 1 (by norm_num)
      have e2 := e 2 (by norm_num)
      have e3 := e 3 (by norm_num)
      simp only [add_zero] at e0
      rw [show 4 * k + 1 + 1 = 4 * k + 2 by ring, show 4 * k + 2 + 1 = 4 * k + 3 by ring]
      fin_cases i <;> simp_all <;> push_cast <;> ring

theorem padCnt_mid (p : Fin r × Bool) (m : ℕ) : padCnt (r := r) (Sum.inl (Sum.inr p)) m = 0 := by
  unfold padCnt padQ
  simp

theorem expCnt_pad (M : ℝ) (hM : 0 < M) (π0 : Policy (Cell r ⊕ Unit)) (n k : ℕ) (e : Cell r) :
    expCnt M hM (padPol π0 n) (n + 4 * k) e
      = expCnt M hM π0 n e + (padCnt (r := r) (Sum.inl e) (4 * k)).toReal := by
  unfold expCnt
  rw [lintegral_cnt_pad (famChan M hM) π0 n (lift (thetaC r)) (Sum.inl e) (4 * k),
    ENNReal.toReal_add (lintegral_cntQ_ne_top _ _ _ _ _)]
  unfold padCnt
  exact ENNReal.sum_ne_top.mpr fun j _ => by split_ifs <;> simp

theorem expCnt_pad_A (M : ℝ) (hM : 0 < M) (π0 : Policy (Cell r ⊕ Unit)) (n k : ℕ) (i : Fin 4) :
    expCnt M hM (padPol π0 n) (n + 4 * k) (Sum.inl i) = expCnt M hM π0 n (Sum.inl i) + k := by
  rw [expCnt_pad, padCnt_A]
  simp

theorem expCnt_pad_mid (M : ℝ) (hM : 0 < M) (π0 : Policy (Cell r ⊕ Unit)) (n k : ℕ)
    (p : Fin r × Bool) :
    expCnt M hM (padPol π0 n) (n + 4 * k) (Sum.inr p) = expCnt M hM π0 n (Sum.inr p) := by
  rw [expCnt_pad, padCnt_mid]
  simp

/-! ## 4. The dilution theorem -/

/-- **The budget can be spread over any run length.**  If `pi0` is `delta`-correct on its first
`n` rounds, then for every `k` the padded policy with `4k` surrogate-optimal rounds is
`delta`-correct, has `N0 + 4k` expected real queries, obeys the sacrifice law, and spends no more
budget than `pi0`. -/
theorem dilution [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (π0 : Policy (Cell r ⊕ Unit))
    (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n)) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hθ : 1 - δ ≤ (hist (famChan M hM) π0 (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π0 (lift lam) n).real S ≤ δ)
    (hD : 0 < demand δ) (k : ℕ) :
    (∑ e, expCnt M hM (padPol π0 n) (n + 4 * k) e = ∑ e, expCnt M hM π0 n e + 4 * k)
      ∧ 1 - δ ≤ (hist (famChan M hM) (padPol π0 n) (lift (thetaC r)) (n + 4 * k)).real
          ((CIGAMF.P13.PaperBStoppedLaw.hRestr n (Nat.le_add_right n (4 * k))) ⁻¹' S)
      ∧ (∀ lam ∈ TrueAltStrict r,
          (hist (famChan M hM) (padPol π0 n) (lift lam) (n + 4 * k)).real
            ((CIGAMF.P13.PaperBStoppedLaw.hRestr n (Nat.le_add_right n (4 * k))) ⁻¹' S) ≤ δ)
      ∧ 8 * (r : ℝ) * M * demand δ
          ≤ (∑ e, expCnt M hM (padPol π0 n) (n + 4 * k) e)
            * sacrifice M (fun e => expCnt M hM (padPol π0 n) (n + 4 * k) e
                / ∑ e', expCnt M hM (padPol π0 n) (n + 4 * k) e')
      ∧ (∑ e, expCnt M hM (padPol π0 n) (n + 4 * k) e)
            * sacrifice M (fun e => expCnt M hM (padPol π0 n) (n + 4 * k) e
                / ∑ e', expCnt M hM (padPol π0 n) (n + 4 * k) e')
          ≤ (∑ e, expCnt M hM π0 n e)
            * sacrifice M (fun e => expCnt M hM π0 n e / ∑ e', expCnt M hM π0 n e') := by
  classical
  set c0 := expCnt M hM π0 n with hc0
  set c := expCnt M hM (padPol π0 n) (n + 4 * k) with hc
  set N0 := ∑ e, c0 e with hN0
  have hsum : ∑ e, c e = N0 + 4 * k := by
    rw [hN0, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [hc, expCnt_pad_A, expCnt_pad_mid, Finset.sum_add_distrib, Fin.sum_univ_four]
    push_cast
    ring
  have hθ' : 1 - δ ≤ (hist (famChan M hM) (padPol π0 n) (lift (thetaC r)) (n + 4 * k)).real
      ((CIGAMF.P13.PaperBStoppedLaw.hRestr n (Nat.le_add_right n (4 * k))) ⁻¹' S) := by
    rw [pad_real _ π0 n (4 * k) _ S hS]; exact hθ
  have hl' : ∀ lam ∈ TrueAltStrict r,
      (hist (famChan M hM) (padPol π0 n) (lift lam) (n + 4 * k)).real
        ((CIGAMF.P13.PaperBStoppedLaw.hRestr n (Nat.le_add_right n (4 * k))) ⁻¹' S) ≤ δ := by
    intro lam hlam
    rw [pad_real _ π0 n (4 * k) _ S hS]; exact hl lam hlam
  have hlaw := sacrifice_cost_law M hM hr (padPol π0 n) (n + 4 * k) _
    (measurableSet_pad n (4 * k) S hS) δ hδ hδ1 hθ' hl' hD
  obtain ⟨hN0pos, halloc0, -⟩ := sacrifice_cost_law M hM hr π0 n S hS δ hδ hδ1 hθ hl hD
  refine ⟨hsum, hθ', hl', hlaw.2.2, ?_⟩
  -- the padded average design is a mixture of the surrogate optimum and pi0's average design
  set β := N0 / (N0 + 4 * k) with hβ
  have hden : 0 < N0 + 4 * (k : ℝ) := by positivity
  have hβ0 : 0 ≤ β := div_nonneg hN0pos.le hden.le
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one hden]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hN0p : 0 < N0 := hN0pos
  have hN0ne : N0 ≠ 0 := hN0p.ne'
  have hmix : (fun e => c e / ∑ e', c e') = mixW β (wUnifC r) (fun e => c0 e / N0) := by
    funext e
    rw [hsum]
    unfold mixW wUnifC
    rcases e with i | p
    · simp only [hc, expCnt_pad_A, Sum.elim_inl]
      rw [← hc0, hβ]
      field_simp
      ring
    · simp only [hc, expCnt_pad_mid, Sum.elim_inr]
      rw [← hc0, hβ, mul_zero, zero_add]
      field_simp
  rw [hmix, hsum]
  have hle := sacrifice_mix_le M hM (fun e => c0 e / N0) halloc0 β hβ0 hβ1
  have hNN : (N0 + 4 * k) * β = N0 := by rw [hβ]; field_simp
  calc (N0 + 4 * k) * sacrifice M (mixW β (wUnifC r) (fun e => c0 e / N0))
      ≤ (N0 + 4 * k) * (β * sacrifice M (fun e => c0 e / N0)) :=
        mul_le_mul_of_nonneg_left hle hden.le
    _ = N0 * sacrifice M (fun e => c0 e / N0) := by rw [← mul_assoc, hNN]

/-- **The relative sacrifice of the padded policy is at most `N0 / (N0 + 4k)`.** -/
theorem dilution_small [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (π0 : Policy (Cell r ⊕ Unit))
    (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n)) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hθ : 1 - δ ≤ (hist (famChan M hM) π0 (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π0 (lift lam) n).real S ≤ δ)
    (hD : 0 < demand δ) (k : ℕ) :
    sacrifice M (fun e => expCnt M hM (padPol π0 n) (n + 4 * k) e
        / ∑ e', expCnt M hM (padPol π0 n) (n + 4 * k) e')
      ≤ (∑ e, expCnt M hM π0 n e) / (∑ e, expCnt M hM π0 n e + 4 * k) := by
  obtain ⟨hsum, -, -, -, hbud⟩ := dilution M hM hr π0 n S hS δ hδ hδ1 hθ hl hD k
  obtain ⟨hN0pos, halloc0, -⟩ := sacrifice_cost_law M hM hr π0 n S hS δ hδ hδ1 hθ hl hD
  have hs1 := sacrifice_le_one M hM _ halloc0.1
  rw [hsum] at hbud ⊢
  have hden : 0 < ∑ e, expCnt M hM π0 n e + 4 * (k : ℝ) := by positivity
  rw [le_div_iff₀ hden, mul_comm]
  have := mul_le_mul_of_nonneg_left hs1 hN0pos.le
  linarith

#print axioms sacrifice_mix_le
#print axioms pad_real
#print axioms lintegral_cnt_pad
#print axioms padCnt_A
#print axioms dilution
#print axioms dilution_small

end CIGAMF.P13.PaperASacrificeDilute
