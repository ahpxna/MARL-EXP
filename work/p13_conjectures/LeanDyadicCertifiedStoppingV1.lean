import Mathlib

/-! A concrete dyadic stopping-time construction and expected-work theorem.
A per-stage error envelope is sufficient even on paths where earlier estimates
were wrong. Work is infinite on nontermination; it is not silently set to zero. -/
namespace CIGAMF.P13.DyadicCertifiedStopping
open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

def alive (accept : ℕ → Ω → Prop) (s : ℕ) : Set Ω := {x | ∀ t ≤ s, ¬ accept t x}

def work (accept : ℕ → Ω → Prop) (x : Ω) : ℝ≥0∞ :=
  1+∑' s : ℕ, (alive accept s).indicator (fun _ => (2:ℝ≥0∞)^s) x

lemma alive_measurable (accept : ℕ → Ω → Prop) (ha : ∀ s, MeasurableSet {x | accept s x})
    (s : ℕ) : MeasurableSet (alive accept s) := by
  change MeasurableSet {x | ∀ t, t ≤ s → ¬ accept t x}
  simp only [Set.setOf_forall,← Set.compl_setOf]
  exact MeasurableSet.iInter (fun t => MeasurableSet.iInter (fun _ : t ≤ s => (ha t).compl))

lemma work_measurable (accept : ℕ → Ω → Prop) (ha : ∀ s, MeasurableSet {x | accept s x}) :
    Measurable (work accept) := by
  unfold work
  exact measurable_const.add (Measurable.ennreal_tsum (fun s =>
    measurable_const.indicator (alive_measurable accept ha s)))

lemma nontermination_work_top (accept : ℕ → Ω → Prop) (x : Ω)
    (hx : ¬ ∃ s, accept s x) : work accept x=∞ := by
  have he (s : ℕ) : x ∈ alive accept s := by
    intro t _ ht
    exact hx ⟨t,ht⟩
  simp [work,Set.indicator_of_mem (he _),ENNReal.tsum_geometric,
    tsub_eq_zero_of_le (by norm_num : (1:ℝ≥0∞) ≤ 2)]

/-- On first acceptance at s, normalized work is 2^s. Actual queries multiply
this quantity by the cost of the initial block. -/
theorem work_at_first_accept (accept : ℕ → Ω → Prop) (x : Ω) (s : ℕ)
    (hs : accept s x) (hbefore : ∀ t < s, ¬ accept t x) : work accept x=(2:ℝ≥0∞)^s := by
  have he (t : ℕ) : (alive accept t).indicator (fun _ => (2:ℝ≥0∞)^t) x =
      if t < s then (2:ℝ≥0∞)^t else 0 := by
    by_cases ht : t < s
    · have hx : x ∈ alive accept t := fun u hu => hbefore u (lt_of_le_of_lt hu ht)
      simp [Set.indicator_of_mem hx,ht]
    · have hx : x ∉ alive accept t := fun h => h s (by omega) hs
      simp [Set.indicator_of_notMem hx,ht]
  simp only [work,he]
  rw [tsum_eq_sum (s := Finset.range s) (by intro b hb;simp only [Finset.mem_range,not_lt] at hb; simp [not_lt.mpr hb])]
  have hsum : (∑ t ∈ Finset.range s, if t < s then (2:ℝ≥0∞)^t else 0) =
      ∑ t ∈ Finset.range s,(2:ℝ≥0∞)^t :=
    Finset.sum_congr rfl (fun t ht => if_pos (Finset.mem_range.mp ht))
  rw [hsum]
  have hh : 1+(∑ t ∈ Finset.range s,(2:ℝ≥0∞)^t)=(2:ℝ≥0∞)^s := by
    have hall : ∀ n : ℕ, 1+(∑ t ∈ Finset.range n,(2:ℝ≥0∞)^t)=(2:ℝ≥0∞)^n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ,← add_assoc,ih,pow_succ];ring
    exact hall s
  simpa using hh

theorem expected_work_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (accept : ℕ → Ω → Prop) (ha : ∀ s, MeasurableSet {x | accept s x})
    (bad : ℕ → Set Ω) (hgood : ∀ s x, x ∉ bad s → accept s x)
    (eta : ℝ≥0∞) (htail : ∀ s, P (bad s) ≤ eta*(4⁻¹:ℝ≥0∞)^s) :
    (∫⁻ x,work accept x ∂P) ≤ 1+2*eta := by
  have hb (s : ℕ) : P (alive accept s) ≤ eta*(4⁻¹:ℝ≥0∞)^s := by
    apply (measure_mono (show alive accept s ⊆ bad s from ?_)).trans (htail s)
    intro x hx
    by_contra h
    exact hx s le_rfl (hgood s x h)
  unfold work
  rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,
    lintegral_tsum (fun s => (measurable_const.indicator (alive_measurable accept ha s)).aemeasurable)]
  apply add_le_add le_rfl
  calc
    (∑' s : ℕ, ∫⁻ x,(alive accept s).indicator (fun _ => (2:ℝ≥0∞)^s) x ∂P)
        = ∑' s : ℕ,(2:ℝ≥0∞)^s*P (alive accept s) := by
          apply tsum_congr;intro s
          exact lintegral_indicator_const (alive_measurable accept ha s) _
    _ ≤ ∑' s : ℕ,(2:ℝ≥0∞)^s*(eta*(4⁻¹:ℝ≥0∞)^s) := ENNReal.tsum_le_tsum (fun s => mul_le_mul le_rfl (hb s) (by positivity) (by positivity))
    _ = eta*∑' s : ℕ,(2⁻¹:ℝ≥0∞)^s := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr;intro s
      have he : (2:ℝ≥0∞)*4⁻¹=2⁻¹ := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num
      calc
        _ = eta*((2:ℝ≥0∞)^s*(4⁻¹:ℝ≥0∞)^s) := by ac_rfl
        _ = _ := by rw [← mul_pow,he]
    _ = 2*eta := by rw [ENNReal.tsum_geometric_two,mul_comm]

theorem almost_sure_termination (P : Measure Ω) [IsProbabilityMeasure P]
    (accept : ℕ → Ω → Prop) (ha : ∀ s, MeasurableSet {x | accept s x})
    (bad : ℕ → Set Ω) (hgood : ∀ s x, x ∉ bad s → accept s x)
    (eta : ℝ≥0∞) (heta : eta ≠ ∞)
    (htail : ∀ s, P (bad s) ≤ eta*(4⁻¹:ℝ≥0∞)^s) :
    ∀ᵐ x ∂P, ∃ s, accept s x := by
  have hbound := expected_work_bound P accept ha bad hgood eta htail
  have hfinite : (∫⁻ x,work accept x ∂P) ≠ ∞ := ne_top_of_le_ne_top (by finiteness) hbound
  filter_upwards [ae_lt_top (work_measurable accept ha) hfinite] with x hx
  by_contra h
  rw [nontermination_work_top accept x h] at hx
  exact (lt_irrefl _) hx

theorem ever_error_bound (P : Measure Ω) (wrong bad : ℕ → Set Ω)
    (hsub : ∀ s, wrong s ⊆ bad s) (eta : ℝ≥0∞)
    (htail : ∀ s, P (bad s) ≤ eta*(4⁻¹:ℝ≥0∞)^s) :
    P (⋃ s,wrong s) ≤ eta*(1-(4⁻¹:ℝ≥0∞))⁻¹ := by
  calc
    _ ≤ ∑' s,P (wrong s) := measure_iUnion_le _
    _ ≤ ∑' s,eta*(4⁻¹:ℝ≥0∞)^s := ENNReal.tsum_le_tsum (fun s => (measure_mono (hsub s)).trans (htail s))
    _ = _ := by rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]

#print axioms work_at_first_accept
#print axioms expected_work_bound
#print axioms almost_sure_termination
#print axioms ever_error_bound
end
end CIGAMF.P13.DyadicCertifiedStopping
