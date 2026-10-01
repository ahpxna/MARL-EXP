import «LeanPaperBChiStarV1»

/-!
# The sharing tournament: the upper law with `|Q|` in place of `|W|²`

`hellinger_tournament` gives every oriented pair its own block of `n` rounds, so it pays
`|W|² n` queries. Here every query of the menu gets one block of `n` rounds, round-robin, and
each pair's likelihood-ratio test reads the block of its best Hellinger query. All pairs
share samples.

* `beatS_error`: the test of a pair still errs with probability at most `e^{-n kH}`.
* `share_tournament`: with `n ≥ log(|W|/δ)/t` the output is safe with probability `1 - δ` at
  every world, and costs at most `|Q| n` queries.

`private_query_lower` shows that the factor `|Q|` cannot be removed.
-/

namespace CIGAMF.P13.PaperBShareTournament

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperBSchedule
open CIGAMF.P13.PaperBObstructionLaw CIGAMF.P13.PaperBHellingerTest CIGAMF.P13.PaperBSafe
open CIGAMF.P13.PaperBPrivateQuery

variable {W Q A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
  [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] [Fintype Q]

/-- The index of a query. -/
noncomputable def qidx (q : Q) : ℕ := (Fintype.equivFin Q q : ℕ)

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem qidx_lt (q : Q) : qidx q < Fintype.card Q := (Fintype.equivFin Q q).isLt

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem qidx_symm (q : Q) :
    (Fintype.equivFin Q).symm ⟨qidx q, qidx_lt q⟩ = q :=
  (Fintype.equivFin Q).symm_apply_apply q

/-- **The round-robin schedule**: round `i` asks the query of block `i / n`. -/
noncomputable def sSched (C : Channel W Q) (n : ℕ) (i : ℕ) : Q :=
  if h : i / n < Fintype.card Q then (Fintype.equivFin Q).symm ⟨i / n, h⟩ else C.dummy

/-- The block of query `q`. -/
def qblk (n : ℕ) (q : Q) : ℕ → Prop := fun i => i / n = qidx q

noncomputable instance (n : ℕ) (q : Q) : DecidablePred (qblk n q) :=
  fun i => inferInstanceAs (Decidable (i / n = qidx q))

/-- The query a pair is tested on: the best query of its oriented representative. -/
noncomputable def qS (C : Channel W Q) (u v : W) : Q := qStar C (canon u v).1 (canon u v).2

omit [Fintype A] [DecidableEq A] [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] in
theorem qS_symm (C : Channel W Q) {u v : W} (hne : u ≠ v) : qS C v u = qS C u v := by
  unfold qS; rw [canon_symm (Ne.symm hne)]

/-- The likelihood of world `x` on the block of the pair `{u, v}`. -/
noncomputable def likS (C : Channel W Q) (n : ℕ) (x u v : W)
    (ω : Hist Q (Fintype.card Q * n)) : ℝ :=
  ∏ i ∈ blockSet (Fintype.card Q * n) (qblk n (qS C u v)), C.dens x (sSched C n i) (ω i).2

/-- **`u` beats `v`**, on the shared block of their best query; ties to the lower rank. -/
noncomputable def beatS (C : Channel W Q) (n : ℕ) (u v : W) : Set (Hist Q (Fintype.card Q * n)) :=
  if rk u < rk v then {ω | likS C n v u v ω ≤ likS C n u u v ω}
  else {ω | likS C n v u v ω < likS C n u u v ω}

omit [Fintype A] [DecidableEq A] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem likS_symm (C : Channel W Q) (n : ℕ) (x : W) {u v : W} (hne : u ≠ v) :
    likS C n x v u = likS C n x u v := by
  funext ω
  unfold likS
  rw [qS_symm C hne]

omit [Fintype A] [DecidableEq A] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem beatS_anti (C : Channel W Q) (n : ℕ) {u v : W} (hne : u ≠ v) :
    beatS C n v u = (beatS C n u v)ᶜ := by
  unfold beatS
  have hr : rk u ≠ rk v := fun h => hne (rk_inj h)
  rw [likS_symm C n u hne, likS_symm C n v hne]
  by_cases h1 : rk u < rk v
  · have h2 : ¬ rk v < rk u := by omega
    rw [if_pos h1, if_neg h2]
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  · have h2 : rk v < rk u := by omega
    rw [if_neg h1, if_pos h2]
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]

omit [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A] [MeasurableSpace Q]
  [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
/-- A query's block has at least `n` rounds. -/
theorem card_qblock (n : ℕ) (q : Q) :
    n ≤ (blockSet (Fintype.card Q * n) (qblk n q)).card := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · omega
  set k := qidx q with hk
  have hkK : k < Fintype.card Q := qidx_lt q
  have hmap : ∀ j : Fin n, k * n + j < Fintype.card Q * n := by
    intro j
    have : (k + 1) * n ≤ Fintype.card Q * n := Nat.mul_le_mul_right _ hkK
    have := j.isLt
    nlinarith
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n)))
    (t := blockSet (Fintype.card Q * n) (qblk n q))
    (fun j => (⟨k * n + j, hmap j⟩ : Fin (Fintype.card Q * n)))
    (by
      intro j _
      rw [Finset.mem_coe]
      unfold blockSet
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show (k * n + (j : ℕ)) / n = k
      rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j.isLt, zero_add])
    (by
      intro a _ b _ hab
      have := congrArg Fin.val hab
      simp only at this
      exact Fin.ext (by omega))
  simpa using h

omit [Fintype A] [DecidableEq A] [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] in
theorem sSched_block (C : Channel W Q) (n : ℕ) (q : Q) (i : Fin (Fintype.card Q * n))
    (hi : i ∈ blockSet (Fintype.card Q * n) (qblk n q)) : sSched C n i = q := by
  have hi' : (i : ℕ) / n = qidx q := by
    unfold blockSet at hi
    exact (Finset.mem_filter.mp hi).2
  have hlt : (i : ℕ) / n < Fintype.card Q := by rw [hi']; exact qidx_lt q
  unfold sSched
  rw [dif_pos hlt]
  have : (⟨(i : ℕ) / n, hlt⟩ : Fin (Fintype.card Q)) = ⟨qidx q, qidx_lt q⟩ := Fin.ext hi'
  rw [this, qidx_symm]

omit [Fintype A] [DecidableEq A] [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] in
theorem hel_qS (C : Channel W Q) (w v : W) : hel C w v (qS C v w) = kH C w v := by
  unfold qS
  rcases canon_cases v w with h | h <;> rw [h]
  · simp only; rw [hel_symm, hel_qStar, kH_symm]
  · simp only; rw [hel_qStar]

omit [Fintype A] [DecidableEq A] in
/-- **A pair's shared test errs with probability at most `exp(-n kH)`.** -/
theorem beatS_error (C : Channel W Q) (n : ℕ) (w v : W) :
    hist C (schedPolicy (sSched C n)) w (Fintype.card Q * n) (beatS C n v w)
      ≤ ENNReal.ofReal (Real.exp (-(1 * n * (kH C w v : ℝ)))) := by
  set H := Fintype.card Q * n
  have hsub : beatS C n v w ⊆ {ω | ∏ i ∈ blockSet H (qblk n (qS C v w)),
      C.dens w (sSched C n i) (ω i).2
        ≤ ∏ i ∈ blockSet H (qblk n (qS C v w)), C.dens v (sSched C n i) (ω i).2} := by
    intro ω hω
    unfold beatS at hω
    split_ifs at hω
    · exact hω
    · exact le_of_lt (show likS C n w v w ω < likS C n v v w ω from hω)
  calc hist C (schedPolicy (sSched C n)) w H (beatS C n v w)
      ≤ ∏ i ∈ blockSet H (qblk n (qS C v w)), bc C w v (sSched C n i) :=
        (measure_mono hsub).trans (block_error C (sSched C n) w v H (qblk n (qS C v w)))
    _ = bc C w v (qS C v w) ^ (blockSet H (qblk n (qS C v w))).card := by
        rw [Finset.prod_congr rfl fun i hi => by rw [sSched_block C n _ i hi], Finset.prod_const]
    _ ≤ bc C w v (qS C v w) ^ n := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (card_qblock (Q := Q) n (qS C v w))
        rw [hk, pow_add]
        exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (bc_le_one _ _ _ _))
    _ ≤ ENNReal.ofReal (Real.exp (-(n * hel C w v (qS C v w)))) := bc_pow_le _ _ _ _ _
    _ = ENNReal.ofReal (Real.exp (-(1 * n * (kH C w v : ℝ)))) := by rw [hel_qS, one_mul]

omit [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A] in
theorem schedCost_le_H (C : Channel W Q) (n : ℕ) :
    schedCost (sSched C n) C.dummy (Fintype.card Q * n) ≤ Fintype.card Q * n := by
  unfold schedCost
  calc ∑ i : Fin (Fintype.card Q * n), (if sSched C n i = C.dummy then 0 else 1)
      ≤ ∑ _i : Fin (Fintype.card Q * n), 1 :=
        Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
    _ = Fintype.card Q * n := by simp

/-- **The sharing tournament.**  If every obstruction contains a pair whose best query has
Hellinger information at least `t > 0`, then with `n ≥ log(|W|/δ)/t` rounds per query the
output is safe with probability `≥ 1 - δ` at every world, within `|Q| n` queries. -/
theorem share_tournament (C : Channel W Q) (safe : W → Finset A) (t : ℝ≥0) (ht : 0 < t)
    (hres : Resolves (kH C) safe t) (a0 : A) (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (hn : Real.log ((Fintype.card W : ℝ) / δ) / t ≤ n) :
    (∀ w, hist C (schedPolicy (sSched C n)) w (Fintype.card Q * n)
        {ω | decode safe (pairSet (kH C) t) (beatS C n) a0 ω ∉ safe w} ≤ ENNReal.ofReal δ)
      ∧ (∀ w, MeasurableSet {ω | decode safe (pairSet (kH C) t) (beatS C n) a0 ω ∈ safe w})
      ∧ ∀ w, costN C (schedPolicy (sSched C n)) w (Fintype.card Q * n)
          ≤ ((Fintype.card Q * n : ℕ) : ℝ≥0∞) := by
  have hbm : ∀ u v, MeasurableSet (beatS C n u v) := by
    intro u v
    have hlik : ∀ x, Measurable (likS C n x u v) := fun x => by
      unfold likS
      exact Finset.measurable_prod _ fun i _ =>
        (C.meas x _).comp (measurable_snd.comp (measurable_pi_apply i))
    unfold beatS
    split_ifs
    · exact measurableSet_le (hlik v) (hlik u)
    · exact measurableSet_lt (hlik v) (hlik u)
  refine ⟨(tournament_law safe (kH C) (kH_symm C) t ht hres (beatS C n)
    (fun u v huv => beatS_anti C n (Finset.mem_filter.mp huv).2.1) a0
    (fun w => hist C (schedPolicy (sSched C n)) w (Fintype.card Q * n)) 1 δ n one_pos hδ
    (Nat.cast_nonneg n) (by rwa [one_mul])
    (fun w v _ => beatS_error C n w v)).1,
    fun w => measurableSet_decode_mem _ _ _ hbm a0 _, fun w => ?_⟩
  rw [costN_sched]
  exact_mod_cast schedCost_le_H C n

/-- **Not vacuous**: on the private-query channel, identification with `k + 1` worlds and
`k + 1` queries is done at level `δ` with `(k+1) ⌈log((k+1)/δ)/t⌉` queries, against
`(k+1)^2 ⌈log((k+1)/δ)/t⌉` for the pairwise tournament. -/
theorem share_tournament_satisfiable (k : ℕ) (h : ℝ) (hh : h ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ≥0, 0 < t ∧ ∃ n : ℕ,
      (∀ w, hist (pqChan k h) (schedPolicy (sSched (pqChan k h) n)) w
          (Fintype.card (Fin (k + 1)) * n)
          {ω | decode (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1))))
            (pairSet (kH (pqChan k h)) t) (beatS (pqChan k h) n) 0 ω
              ∉ ({w} : Finset (Fin (k + 1)))} ≤ ENNReal.ofReal δ)
        ∧ ∀ w, costN (pqChan k h) (schedPolicy (sSched (pqChan k h) n)) w
            (Fintype.card (Fin (k + 1)) * n) ≤ (((k + 1) * n : ℕ) : ℝ≥0∞) := by
  have hpos : 0 < 1 - Real.exp (-h ^ 2 / 8) := by
    have : Real.exp (-h ^ 2 / 8) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < h ^ 2 := by positivity
      linarith)
    linarith
  set n : ℕ := ⌈Real.log ((Fintype.card (Fin (k + 1)) : ℝ) / δ)
    / (1 - Real.exp (-h ^ 2 / 8))⌉₊ with hn
  refine ⟨⟨1 - Real.exp (-h ^ 2 / 8), hpos.le⟩, by exact_mod_cast hpos, n, ?_⟩
  obtain ⟨h1, -, h3⟩ := share_tournament (pqChan k h)
    (fun w : Fin (k + 1) => ({w} : Finset (Fin (k + 1)))) ⟨1 - Real.exp (-h ^ 2 / 8), hpos.le⟩
    (by exact_mod_cast hpos) (pq_resolves k h) 0 δ hδ n (Nat.le_ceil _)
  refine ⟨h1, fun w => (h3 w).trans (le_of_eq ?_)⟩
  rw [Fintype.card_fin]

#print axioms beatS_anti
#print axioms beatS_error
#print axioms share_tournament
#print axioms share_tournament_satisfiable

end CIGAMF.P13.PaperBShareTournament
