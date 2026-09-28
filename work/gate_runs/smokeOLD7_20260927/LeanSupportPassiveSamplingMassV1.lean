import «LeanSupportPassiveDecisionMassV1»
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.Pi

/-! # R4: the probability layer of passive certification.

`LeanSupportPassiveDecisionMassV1` closed the combinatorial core (`safe_of_unseen`,
`unsafe_of_seen`, `certification_exact`) against the REAL geometry, and supplied the
numeric miss budget (`one_minus_le_exp_neg_pow`, `sample_size_suffices`). Its own
docstring recorded the gap: those two are inequalities between real numbers, and the
probabilistic reading — a region of mass `>= gamma` is missed by `N` i.i.d. draws with
probability at most `(1-gamma)^N`, union-bounded over the present tips — was NOT
formalised. No measure space appeared in any statement there.

This module supplies exactly that layer, and nothing else is assumed.

THE MODEL. The actual support of world `W` is the finite point set `Points W =
Option {w // w ∈ W}` of `LeanSupportMultiTipGeometryV1`: `none` is the anchor `0` and
`some w` is the tip `tip w`. A sampling law is an honest probability mass function
`p : PMF (Points W)` on that support, and the observation of `N` i.i.d. draws is the
product measure `iid W p N = Measure.pi (fun _ : Fin N => p.toMeasure)` on
`Fin N → Points W`. `seen W x` is the finset of tips the sample exposed; `mem_seen_iff_point`
checks that it is exactly the set of tips whose POINT occurs among the drawn points,
so the learner is reading the real geometry, not a bookkeeping label.

WHAT IS PROVED HERE.

* `miss_probability` — `iid W p N (missed W w N) = (1 - p (some w))^N`, an EQUALITY,
  computed from `Measure.pi_pi`. This is the step that was missing.
* `miss_bound` / `miss_bound_exp` — under mass `>= gamma` for tip `w`, the miss
  probability is at most `ofReal ((1-gamma)^N)`, hence at most `ofReal (exp (-(gamma*N)))`
  via `one_minus_le_exp_neg_pow`.
* `incomplete_prob_le` — union bound over the present tips: the sample fails to be
  complete with probability at most `ofReal delta` once `log (M/delta) ≤ gamma*N`
  and `W.card ≤ M`, via `sample_size_suffices`.
* `complete_prob_ge` — completeness holds with probability at least `1-delta`.
* `passive_certified_safe_whp`, `certification_exact_whp`,
  `passive_certified_safe_exists_whp` and their `.real` forms — composition with
  `safe_of_unseen` / `certification_exact` / `exists_certified_safe`. The conclusion
  is about `selectedRadius (components W)`, the real geometric radius.

WHAT THIS DOES NOT ESTABLISH.

- Passive sampling only. Nothing here is an adaptive or query-driven procedure, and
  no stopping rule is analysed: `N` is fixed in advance.
- One tip per decision, as in `LeanSupportMultiTipGeometryV1`. Heterogeneous tips,
  correlated supports, and danger regions larger than one support point are untouched.
- The pmf is arbitrary subject to the tip masses; no minimax statement over laws, and
  no lower bound on `N` (this is the sufficiency direction only).
- The hypothesis `hmass` bounds the mass of PRESENT tips. It says nothing about the
  anchor `none`, which may carry all the remaining mass.
- The negative theorem of `PASSIVE_DECISION_MASS_PROOF.md` is untouched and
  uncontradicted: `gamma` is genuinely needed here. `gamma_zero_vacuous` proves that at
  `gamma = 0` the sample-size hypothesis forces `delta ≥ M ≥ 1`, so every conclusion
  below degenerates to `1-delta ≤ 0`, i.e. says nothing. No `N` rescues it.
-/

namespace CIGAMF.P13.SupportPassiveSamplingMass
open Finset MeasureTheory
open scoped ENNReal
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportUnboundedObstruction
open CIGAMF.P13.SupportMultiTipGeometry
open CIGAMF.P13.SupportPassiveDecisionMass
noncomputable section

variable {m : ℕ}

/-! ## The sampling model: `N` i.i.d. draws from a pmf on the actual support -/

/-- The support `Points W` is a finite point set; every subset is an event. -/
instance pointsMeasurableSpace (W : Finset (Fin m)) : MeasurableSpace (Points W) := ⊤

instance pointsSingletonClass (W : Finset (Fin m)) :
    MeasurableSingletonClass (Points W) := ⟨fun _ => trivial⟩

/-- `N` independent draws, each distributed by the pmf `p` on the support of `W`. -/
def iid (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ) :
    Measure (Fin N → Points W) :=
  Measure.pi (fun _ => p.toMeasure)

instance iid_isProbabilityMeasure (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ) :
    IsProbabilityMeasure (iid W p N) := by
  unfold iid; infer_instance

/-! ## What a sample reveals -/

/-- The tips exposed by the sample `x`. -/
def seen (W : Finset (Fin m)) {N : ℕ} (x : Fin N → Points W) : Finset (Fin m) :=
  univ.biUnion (fun i => (x i).elim ∅ (fun w => {w.val}))

theorem mem_seen {W : Finset (Fin m)} {N : ℕ} {x : Fin N → Points W} {j : Fin m} :
    j ∈ seen W x ↔ ∃ i, ∃ w : {w // w ∈ W}, x i = some w ∧ (w : Fin m) = j := by
  unfold seen
  simp only [mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    cases hxi : x i with
    | none => rw [hxi] at hi; simp at hi
    | some w =>
        rw [hxi] at hi
        simp only [Option.elim, mem_singleton] at hi
        exact ⟨w, rfl, hi.symm⟩
  · rintro ⟨i, w, hw, rfl⟩
    exact ⟨i, by rw [hw]; simp⟩

/-- The sample can only expose tips that are actually present: the observed set is
always a subset of the true world. -/
theorem seen_subset (W : Finset (Fin m)) {N : ℕ} (x : Fin N → Points W) :
    seen W x ⊆ W := by
  intro j hj
  obtain ⟨_, w, _, rfl⟩ := mem_seen.mp hj
  exact w.property

/-- `seen` is geometric, not bookkeeping: `j` is seen exactly when the point `tip j`
occurs among the drawn points. -/
theorem mem_seen_iff_point (hm : 2 ≤ m) (W : Finset (Fin m)) {N : ℕ}
    (x : Fin N → Points W) (j : Fin m) :
    j ∈ seen W x ↔ ∃ i, point W (x i) = tip j := by
  constructor
  · intro hj
    obtain ⟨i, w, hw, rfl⟩ := mem_seen.mp hj
    exact ⟨i, by rw [hw]; rfl⟩
  · rintro ⟨i, hi⟩
    refine mem_seen.mpr ⟨i, ?_⟩
    cases hxi : x i with
    | none =>
        rw [hxi] at hi
        exact absurd hi.symm (CIGAMF.P13.SupportPhysicalQueryContract.tip_ne_zero j)
    | some w =>
        rw [hxi] at hi
        exact ⟨w, rfl, CIGAMF.P13.SupportPhysicalQueryContract.tip_injective hm hi⟩

/-! ## The miss bound -/

/-- The event that no draw landed on the support point `some w`. -/
def missed (W : Finset (Fin m)) (w : {w // w ∈ W}) (N : ℕ) : Set (Fin N → Points W) :=
  {x | ∀ i, x i ≠ some w}

theorem missed_eq_pi (W : Finset (Fin m)) (w : {w // w ∈ W}) (N : ℕ) :
    missed W w N = Set.univ.pi (fun _ : Fin N => ({some w}ᶜ : Set (Points W))) := by
  ext x
  simp [missed, Set.mem_pi]

theorem missed_measurable (W : Finset (Fin m)) (w : {w // w ∈ W}) (N : ℕ) :
    MeasurableSet (missed W w N) := by
  rw [missed_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => trivial)

/-- THE PROBABILISTIC STEP, as an equality: under `N` i.i.d. draws the chance of
never hitting the point `some w` is exactly `(1 - p (some w))^N`. -/
theorem miss_probability (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ)
    (w : {w // w ∈ W}) :
    iid W p N (missed W w N) = (1 - p (some w))^N := by
  rw [missed_eq_pi]
  unfold iid
  rw [Measure.pi_pi]
  simp [prob_compl_eq_one_sub]

/-- A tip of mass at least `gamma` is missed with probability at most `(1-gamma)^N`. -/
theorem miss_bound (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ)
    (w : {w // w ∈ W}) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (hmass : ENNReal.ofReal gamma ≤ p (some w)) :
    iid W p N (missed W w N) ≤ ENNReal.ofReal ((1-gamma)^N) := by
  rw [miss_probability]
  have hsub : (1 : ℝ≥0∞) - p (some w) ≤ 1 - ENNReal.ofReal gamma :=
    tsub_le_tsub_left hmass 1
  have hone : (1 : ℝ≥0∞) - ENNReal.ofReal gamma = ENNReal.ofReal (1-gamma) := by
    rw [ENNReal.ofReal_sub 1 hg0, ENNReal.ofReal_one]
  rw [ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 1-gamma)]
  rw [hone] at hsub
  exact pow_le_pow_left' hsub N

/-- The exponential form, through `one_minus_le_exp_neg_pow`. -/
theorem miss_bound_exp (W : Finset (Fin m)) (p : PMF (Points W)) (N : ℕ)
    (w : {w // w ∈ W}) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (hmass : ENNReal.ofReal gamma ≤ p (some w)) :
    iid W p N (missed W w N) ≤ ENNReal.ofReal (Real.exp (-(gamma*(N:ℝ)))) :=
  (miss_bound W p N w gamma hg0 hg1 hmass).trans
    (ENNReal.ofReal_le_ofReal (one_minus_le_exp_neg_pow gamma hg0 hg1 N))

/-! ## Union bound over the present tips -/

/-- The sample is complete: every present tip has been exposed. -/
def complete (W : Finset (Fin m)) (N : ℕ) : Set (Fin N → Points W) :=
  {x | W ⊆ seen W x}

theorem compl_iUnion_missed_subset_complete (W : Finset (Fin m)) (N : ℕ) :
    (⋃ w : {w // w ∈ W}, missed W w N)ᶜ ⊆ complete W N := by
  intro x hx j hj
  have hw : x ∉ missed W ⟨j, hj⟩ N := fun h => hx (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, h⟩)
  simp only [missed, Set.mem_ofPred_eq, not_forall, not_not] at hw
  obtain ⟨i, hi⟩ := hw
  exact mem_seen.mpr ⟨i, ⟨j, hj⟩, hi, rfl⟩

theorem iUnion_missed_measurable (W : Finset (Fin m)) (N : ℕ) :
    MeasurableSet (⋃ w : {w // w ∈ W}, missed W w N) :=
  MeasurableSet.iUnion (fun w => missed_measurable W w N)

/-- Union bound: with every present tip carrying mass at least `gamma`, and
`log (M/delta) ≤ gamma*N` for some `M ≥ W.card`, the sample fails to be complete
with probability at most `delta`. -/
theorem incomplete_prob_le (W : Finset (Fin m)) (p : PMF (Points W)) (N M : ℕ)
    (gamma delta : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (hd : 0 < delta)
    (hM : 0 < M) (hcard : W.card ≤ M)
    (hmass : ∀ w : {w // w ∈ W}, ENNReal.ofReal gamma ≤ p (some w))
    (hN : Real.log ((M:ℝ)/delta) ≤ gamma*(N:ℝ)) :
    iid W p N (⋃ w : {w // w ∈ W}, missed W w N) ≤ ENNReal.ofReal delta := by
  have hsum := measure_iUnion_fintype_le (iid W p N) (fun w : {w // w ∈ W} => missed W w N)
  have hterm : ∀ w : {w // w ∈ W},
      iid W p N (missed W w N) ≤ ENNReal.ofReal ((1-gamma)^N) :=
    fun w => miss_bound W p N w gamma hg0 hg1 (hmass w)
  have hcount : ∑ _w : {w // w ∈ W}, ENNReal.ofReal ((1-gamma)^N)
      = (W.card : ℝ≥0∞) * ENNReal.ofReal ((1-gamma)^N) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  -- the real-number budget, imported from `sample_size_suffices`
  have hreal : (M:ℝ)*(1-gamma)^N ≤ delta :=
    sample_size_suffices gamma delta M N hg0 hg1 hd hM hN
  have hpow : (0:ℝ) ≤ (1-gamma)^N := pow_nonneg (by linarith) N
  have hcardR : (W.card : ℝ) ≤ (M:ℝ) := by exact_mod_cast hcard
  have hreal' : (W.card:ℝ)*(1-gamma)^N ≤ delta :=
    le_trans (mul_le_mul_of_nonneg_right hcardR hpow) hreal
  have hfinal : (W.card : ℝ≥0∞) * ENNReal.ofReal ((1-gamma)^N) ≤ ENNReal.ofReal delta := by
    have := ENNReal.ofReal_le_ofReal hreal'
    rwa [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (W.card:ℝ)),
      ENNReal.ofReal_natCast] at this
  calc iid W p N (⋃ w : {w // w ∈ W}, missed W w N)
      ≤ ∑ w : {w // w ∈ W}, iid W p N (missed W w N) := hsum
    _ ≤ ∑ _w : {w // w ∈ W}, ENNReal.ofReal ((1-gamma)^N) := Finset.sum_le_sum (fun w _ => hterm w)
    _ = (W.card : ℝ≥0∞) * ENNReal.ofReal ((1-gamma)^N) := hcount
    _ ≤ ENNReal.ofReal delta := hfinal

/-- With probability at least `1-delta`, `N` i.i.d. draws expose every present tip. -/
theorem complete_prob_ge (W : Finset (Fin m)) (p : PMF (Points W)) (N M : ℕ)
    (gamma delta : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (hd : 0 < delta)
    (hM : 0 < M) (hcard : W.card ≤ M)
    (hmass : ∀ w : {w // w ∈ W}, ENNReal.ofReal gamma ≤ p (some w))
    (hN : Real.log ((M:ℝ)/delta) ≤ gamma*(N:ℝ)) :
    ENNReal.ofReal (1-delta) ≤ iid W p N (complete W N) := by
  have hmeas := iUnion_missed_measurable W N
  have hcompl : iid W p N (⋃ w : {w // w ∈ W}, missed W w N)ᶜ
      = 1 - iid W p N (⋃ w : {w // w ∈ W}, missed W w N) := prob_compl_eq_one_sub hmeas
  have hbound := incomplete_prob_le W p N M gamma delta hg0 hg1 hd hM hcard hmass hN
  have hmono : ENNReal.ofReal (1-delta)
      ≤ iid W p N (⋃ w : {w // w ∈ W}, missed W w N)ᶜ := by
    rw [hcompl, ENNReal.ofReal_sub 1 hd.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hbound 1
  exact hmono.trans (measure_mono (compl_iUnion_missed_subset_complete W N))

/-! ## The certified decision -/

/-- MAIN THEOREM. `N` i.i.d. draws from any pmf on the actual support of the world
`W`, in which every present tip carries mass at least `gamma`; `M` any bound on the
number of present tips; `log (M/delta) ≤ gamma*N`. Then with probability at least
`1-delta` the sample is such that EVERY tip the learner did not see is a genuinely
safe decision: its real `selectedRadius` is `0`. -/
theorem passive_certified_safe_whp (hm : 2 ≤ m) (W : Finset (Fin m))
    (p : PMF (Points W)) (N M : ℕ) (gamma delta : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (hd : 0 < delta)
    (hM : 0 < M) (hcard : W.card ≤ M)
    (hmass : ∀ w : {w // w ∈ W}, ENNReal.ofReal gamma ≤ p (some w))
    (hN : Real.log ((M:ℝ)/delta) ≤ gamma*(N:ℝ)) :
    ENNReal.ofReal (1-delta) ≤
      iid W p N {x | ∀ j : Fin m, j ∉ seen W x → selectedRadius (components W) {j} = 0} := by
  refine (complete_prob_ge W p N M gamma delta hg0 hg1 hd hM hcard hmass hN).trans
    (measure_mono ?_)
  intro x hx j hj
  exact safe_of_unseen hm W (seen W x) hx j hj

/-- The same event, with probability read as a real number. -/
theorem passive_certified_safe_whp_real (hm : 2 ≤ m) (W : Finset (Fin m))
    (p : PMF (Points W)) (N M : ℕ) (gamma delta : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (hd : 0 < delta)
    (hM : 0 < M) (hcard : W.card ≤ M)
    (hmass : ∀ w : {w // w ∈ W}, ENNReal.ofReal gamma ≤ p (some w))
    (hN : Real.log ((M:ℝ)/delta) ≤ gamma*(N:ℝ)) :
    1 - delta ≤
      (iid W p N).real {x | ∀ j : Fin m, j ∉ seen W x → selectedRadius (components W) {j} = 0} := by
  have h := passive_certified_safe_whp hm W p N M gamma delta hg0 hg1 hd hM hcard hmass hN
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp h

/-- With probability at least `1-delta` the observed classification is EXACT, not
merely conservative: a decision is safe iff its tip was not seen. -/
theorem certification_exact_whp (hm : 2 ≤ m) (W : Finset (Fin m))
    (p : PMF (Points W)) (N M : ℕ) (gamma delta : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (hd : 0 < delta)
    (hM : 0 < M) (hcard : W.card ≤ M)
    (hmass : ∀ w : {w // w ∈ W}, ENNReal.ofReal gamma ≤ p (some w))
    (hN : Real.log ((M:ℝ)/delta) ≤ gamma*(N:ℝ)) :
    ENNReal.ofReal (1-delta) ≤
      iid W p N {x | ∀ j : Fin m, selectedRadius (components W) {j} = 0 ↔ j ∉ seen W x} := by
  refine (complete_prob_ge W p N M gamma delta hg0 hg1 hd hM hcard hmass hN).trans
    (measure_mono ?_)
  intro x hx j
  exact certification_exact hm W (seen W x) (seen_subset W x) hx j

/-- Whenever some tip is absent from the world, with probability at least `1-delta`
the learner can name a certified safe decision. -/
theorem passive_certified_safe_exists_whp (hm : 2 ≤ m) (W : Finset (Fin m))
    (hne : W ≠ univ) (p : PMF (Points W)) (N M : ℕ) (gamma delta : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (hd : 0 < delta)
    (hM : 0 < M) (hcard : W.card ≤ M)
    (hmass : ∀ w : {w // w ∈ W}, ENNReal.ofReal gamma ≤ p (some w))
    (hN : Real.log ((M:ℝ)/delta) ≤ gamma*(N:ℝ)) :
    ENNReal.ofReal (1-delta) ≤
      iid W p N {x | ∃ j : Fin m, j ∉ seen W x ∧ selectedRadius (components W) {j} = 0} := by
  refine (complete_prob_ge W p N M gamma delta hg0 hg1 hd hM hcard hmass hN).trans
    (measure_mono ?_)
  intro x hx
  have hseen : seen W x ≠ univ := by
    intro h
    exact hne (Finset.Subset.antisymm (Finset.subset_univ W) (h ▸ seen_subset W x))
  exact exists_certified_safe hm W (seen W x) hx hseen

/-! ## The mass hypothesis is doing real work -/

/-- The `gamma` hypothesis is not idle. At `gamma = 0` the sample-size hypothesis
`log (M/delta) ≤ gamma*N` forces `delta ≥ M ≥ 1` for every `N`, so `1-delta ≤ 0` and
every conclusion above is vacuous. This is the positive-side reflection of the
negative theorem: without a mass lower bound, no sample size helps. -/
theorem gamma_zero_vacuous (M N : ℕ) (delta : ℝ) (hM : 0 < M) (hd : 0 < delta)
    (hN : Real.log ((M:ℝ)/delta) ≤ 0*(N:ℝ)) : 1 - delta ≤ 0 := by
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hratio : (0:ℝ) < (M:ℝ)/delta := by positivity
  have hlog : Real.log ((M:ℝ)/delta) ≤ 0 := by simpa using hN
  have hle : (M:ℝ)/delta ≤ 1 := by
    have := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log hratio, Real.exp_zero] at this
  have := (div_le_one hd).mp hle
  linarith

#print axioms iid_isProbabilityMeasure
#print axioms mem_seen
#print axioms seen_subset
#print axioms mem_seen_iff_point
#print axioms missed_eq_pi
#print axioms missed_measurable
#print axioms miss_probability
#print axioms miss_bound
#print axioms miss_bound_exp
#print axioms compl_iUnion_missed_subset_complete
#print axioms iUnion_missed_measurable
#print axioms incomplete_prob_le
#print axioms complete_prob_ge
#print axioms passive_certified_safe_whp
#print axioms passive_certified_safe_whp_real
#print axioms certification_exact_whp
#print axioms passive_certified_safe_exists_whp
#print axioms gamma_zero_vacuous

end
end CIGAMF.P13.SupportPassiveSamplingMass
