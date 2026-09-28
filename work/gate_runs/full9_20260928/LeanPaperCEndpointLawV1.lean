import «LeanPaperCBaselineAttainV1»
import «LeanPaperCRelabelBandJoinV1»
import «LeanPaperCEvenRankSumV1»
import «LeanPaperCFam13V1»

/-!
# Paper C: the two endpoint laws, constructed

`OddEndpointData` (`LeanPaperCOddBreakpointEndgameV1`) and `EvenEndpointData`
(`LeanPaperCEndgameV1`) name one remaining input each: an ACTUAL law on all permutations of
`g_m` that is band-feasible at the breakpoint and whose objective reaches the free value.
This module constructs both laws and feeds them to the assemblies, so `odd_breakpoint_iff`
and `even_frontier` hold with no data argument left.

Nothing here re-proves an arithmetic fact.  The construction is the insertion mixture of
`LeanPaperCRankingV1`: the ordinary alternating sequence with the heavy pair `(+3, -3)`
inserted at `a, a+1`, `a` uniform on `{0, ..., m-2}` -- and, for even `m`, an independent
fair sign flip.  What was missing was the chain from that mixture of WEIGHT VECTORS to a law
on PERMUTATIONS whose per-ITEM marginals obey the band:

1. **Counts.**  `insRanking m a` and `g_m` carry every weight equally often.  Both sides are
   evaluated against one table `tcount m w`: the ranking side by the existing `countIns_*`
   formulas at `k = m` (with the count helpers of `LeanPaperCFam13V1`, which cover only even
   `m` for the light classes), the family side by the fibres `negSet`/`posSet` of
   `LeanPaperCBaselineAttainV1`.  `permOfCountEq` then gives a permutation `sigma_a` with
   `rankOf g_m sigma_a = insRanking m a` -- constructed, not assumed.
2. **Prefix counts.**  Through that identity the weight-`w` count in the prefix of length `k`
   under the law is exactly `mixCount m w k` (odd) or `mixCountEven m w k` (even).
3. **Band.**  `O1_odd` / `O1_even` bound `mixCount` against `c_w * k/m`, with `c_w` the class
   size; dividing by `c_w`, which is positive because it is the class of an ACTUAL item, gives
   `|P(i in prefix_k) - k/m| <= eta/m` for every item `i` and every interior budget.  The
   budgets `k = 0` and `k = m` are handled separately (the marginal is `0` and `1`).  For
   `m = 3` there is no `+1` item and that class is never divided by.
4. **Value.**  `insMixture_free_value` / `insMixtureEven_free_value` give expected regret
   `2/(D(m-1))` at every interior budget; `rankOf_permOfCountEq` makes that the regret of the
   law's own permutations.
5. `actual_banded_witness_of_counts` symmetrises within weight classes and pushes the law onto
   all permutations, keeping band and value; the SAME law fills both fields.

The even `rankSum` field is supplied by `evenEndpointData_of_law`.
-/

namespace CIGAMF.P13.PaperCEndpointLaw

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCPerm
open CIGAMF.P13.PaperCRelabelBandJoin CIGAMF.P13.PaperCFam13
open CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCOddBreakpointEndgame
open CIGAMF.P13.PaperCEvenRankSum CIGAMF.P13.PaperCBaselineAttain

/-! ## 1. One count table for both sides -/

/-- The number of items of each weight in `g_m` (and, as shown below, in every inserted
ranking): one `+3`, one `-3`, `(m-1)/2` light negatives and `m-2-(m-1)/2` light positives. -/
noncomputable def tcount (m : ℕ) (w : ℝ) : ℝ :=
  if w = 3 then 1 else if w = -3 then 1 else if w = -1 then (((m - 1) / 2 : ℕ) : ℝ)
  else if w = 1 then ((m - 2 - (m - 1) / 2 : ℕ) : ℝ) else 0

theorem tcount_three (m : ℕ) : tcount m 3 = 1 := by unfold tcount; norm_num

theorem tcount_neg_three (m : ℕ) : tcount m (-3) = 1 := by unfold tcount; norm_num

theorem tcount_neg_one (m : ℕ) : tcount m (-1) = (((m - 1) / 2 : ℕ) : ℝ) := by
  unfold tcount; norm_num

theorem tcount_one (m : ℕ) : tcount m 1 = ((m - 2 - (m - 1) / 2 : ℕ) : ℝ) := by
  unfold tcount; norm_num

theorem tcount_other (m : ℕ) (w : ℝ) (h3 : w ≠ 3) (h3' : w ≠ -3) (h1 : w ≠ 1)
    (h1' : w ≠ -1) : tcount m w = 0 := by
  unfold tcount
  rw [if_neg h3, if_neg h3', if_neg h1', if_neg h1]

/-- For even `m` the two light classes have the same size, so the table is symmetric. -/
theorem tcount_neg (m : ℕ) (hmo : m % 2 = 0) (w : ℝ) : tcount m (-w) = tcount m w := by
  have hc : m - 2 - (m - 1) / 2 = (m - 1) / 2 := by omega
  unfold tcount
  rw [hc]
  by_cases h3 : w = 3
  · subst h3; norm_num
  · by_cases h3' : w = -3
    · subst h3'; norm_num
    · by_cases h1 : w = 1
      · subst h1; norm_num
      · by_cases h1' : w = -1
        · subst h1'; norm_num
        · rw [if_neg h3, if_neg h3', if_neg h1', if_neg h1,
            if_neg (fun h => h3' (by linarith)), if_neg (fun h => h3 (by linarith)),
            if_neg (fun h => h1 (by linarith)), if_neg (fun h => h1' (by linarith))]

/-! ### The inserted ranking's side, at both parities -/

theorem evensBelow_sub_one (m : ℕ) (hm : 3 ≤ m) :
    evensBelow m - 1 = (((m - 1) / 2 : ℕ) : ℝ) := by
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · rw [evensBelow_two, show (2 * j - 1) / 2 = j - 1 from by omega,
      Nat.cast_sub (by omega : 1 ≤ j)]
    push_cast; ring
  · rw [evensBelow_two_succ, show (2 * j + 1 - 1) / 2 = j from by omega]
    ring

theorem oddsBelow_sub_one (m : ℕ) (hm : 3 ≤ m) :
    oddsBelow m - 1 = ((m - 2 - (m - 1) / 2 : ℕ) : ℝ) := by
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · rw [oddsBelow_two, show 2 * j - 2 - (2 * j - 1) / 2 = j - 1 from by omega,
      Nat.cast_sub (by omega : 1 ≤ j)]
    push_cast; ring
  · rw [oddsBelow_two_succ, show 2 * j + 1 - 2 - (2 * j + 1 - 1) / 2 = j - 1 from by omega,
      Nat.cast_sub (by omega : 1 ≤ j)]
    push_cast; ring

/-- **The inserted ranking's weight counts are the table**, for every insertion point and
both parities.  The `+-3` cases and the zero case are `LeanPaperCFam13V1`'s; the light
classes are redone here only because that module states them for even `m`. -/
theorem countIns_full (m : ℕ) (hm : 3 ≤ m) (a : ℕ) (ha : a + 1 < m) (w : ℝ) :
    countIns a w m = tcount m w := by
  by_cases h3 : w = 3
  · subst h3
    rw [insMult_three m a ha, tcount_three]
  by_cases h3' : w = -3
  · subst h3'
    rw [insMult_neg_three m a ha, tcount_neg_three]
  by_cases h1' : w = -1
  · subst h1'
    rw [countIns_neg_one, tcount_neg_one, ← evensBelow_sub_one m hm]
    linarith [ins_parity_pair m a ha]
  by_cases h1 : w = 1
  · subst h1
    rw [countIns_one, tcount_one, ← oddsBelow_sub_one m hm]
    have hA : (if a < m ∧ ¬ Even a then (1 : ℝ) else 0)
        = 1 - if a < m ∧ Even a then (1 : ℝ) else 0 := by
      by_cases he : Even a
      · rw [if_neg (fun h => h.2 he), if_pos ⟨by omega, he⟩]; ring
      · rw [if_pos ⟨by omega, he⟩, if_neg (fun h => he h.2)]; ring
    have hB : (if a + 1 < m ∧ ¬ Even (a + 1) then (1 : ℝ) else 0)
        = 1 - if a + 1 < m ∧ Even (a + 1) then (1 : ℝ) else 0 := by
      by_cases he : Even (a + 1)
      · rw [if_neg (fun h => h.2 he), if_pos ⟨ha, he⟩]; ring
      · rw [if_pos ⟨ha, he⟩, if_neg (fun h => he h.2)]; ring
    rw [hA, hB]
    linarith [ins_parity_pair m a ha]
  rw [tcount_other m w h3 h3' h1 h1']
  exact count_eq_zero_of_other (insWeight a) m w (insWeight_mem a) h3' h1' h1 h3

/-! ### The family's side, through the fibres of `LeanPaperCBaselineAttainV1` -/

theorem fibre_three (m : ℕ) (hm : 3 ≤ m) :
    (univ : Finset (Fin m)).filter (fun i => gFamily m i = 3) = {⟨m - 1, by omega⟩} := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
  show gN m i = 3 ↔ (i : ℕ) = m - 1
  constructor
  · intro h
    by_contra hne
    unfold gN at h
    split_ifs at h with h0 h1 h2 <;> norm_num at h <;> omega
  · intro h
    unfold gN
    rw [if_neg (by omega), if_pos h]

theorem fibre_neg_three (m : ℕ) (hm : 3 ≤ m) :
    (univ : Finset (Fin m)).filter (fun i => gFamily m i = -3) = {⟨0, by omega⟩} := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
  show gN m i = -3 ↔ (i : ℕ) = 0
  constructor
  · intro h
    by_contra hne
    unfold gN at h
    split_ifs at h with h0 h1 h2 <;> norm_num at h <;> omega
  · intro h
    unfold gN
    rw [if_pos h]

theorem fibre_neg_one (m : ℕ) (hm : 3 ≤ m) :
    (univ : Finset (Fin m)).filter (fun i => gFamily m i = -1) = negSet m := by
  ext i
  simp only [negSet, mem_filter, mem_univ, true_and]
  show gN m i = -1 ↔ 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ (m - 1) / 2
  have hi := i.isLt
  constructor
  · intro h
    by_contra hne
    unfold gN at h
    split_ifs at h with h0 h1 h2 <;> norm_num at h <;> omega
  · intro h
    unfold gN
    rw [if_neg (by omega), if_neg (by omega), if_pos h.2]

theorem fibre_one (m : ℕ) (hm : 3 ≤ m) :
    (univ : Finset (Fin m)).filter (fun i => gFamily m i = 1) = posSet m := by
  ext i
  simp only [posSet, mem_filter, mem_univ, true_and]
  show gN m i = 1 ↔ (m - 1) / 2 + 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ m - 2
  have hi := i.isLt
  constructor
  · intro h
    by_contra hne
    unfold gN at h
    split_ifs at h with h0 h1 h2 <;> norm_num at h <;> omega
  · intro h
    unfold gN
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **The family's weight counts are the same table.** -/
theorem card_weightClass (m : ℕ) (hm : 3 ≤ m) (w : ℝ) :
    ((weightClass (gFamily m) w).card : ℝ) = tcount m w := by
  unfold weightClass
  by_cases h3 : w = 3
  · subst h3
    rw [fibre_three m hm, card_singleton, tcount_three, Nat.cast_one]
  by_cases h3' : w = -3
  · subst h3'
    rw [fibre_neg_three m hm, card_singleton, tcount_neg_three, Nat.cast_one]
  by_cases h1' : w = -1
  · subst h1'
    rw [fibre_neg_one m hm, negSet_card m hm, tcount_neg_one]
  by_cases h1 : w = 1
  · subst h1
    rw [fibre_one m hm, posSet_card m hm, tcount_one]
  rw [tcount_other m w h3 h3' h1 h1']
  have hemp : (univ : Finset (Fin m)).filter (fun i => gFamily m i = w) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun i _ hw => ?_
    rcases gFamily_weights m i with h | h | h | h <;> rw [h] at hw
    · exact h3' hw.symm
    · exact h1' hw.symm
    · exact h1 hw.symm
    · exact h3 hw.symm
  rw [hemp, card_empty, Nat.cast_zero]

theorem card_gFamily_fibre (m : ℕ) (hm : 3 ≤ m) (w : ℝ) :
    ((Fintype.card {j : Fin m // gFamily m j = w} : ℕ) : ℝ) = tcount m w := by
  rw [Fintype.card_subtype]
  exact card_weightClass m hm w

/-- **Equal counts, so a permutation exists**: `insRanking m a` is a rearrangement of `g_m`. -/
theorem insRanking_count (m : ℕ) (hm : 3 ≤ m) (a : ℕ) (ha : a + 1 < m) :
    ∀ w : ℝ, Fintype.card {i : Fin m // insRanking m a i = w}
      = Fintype.card {j : Fin m // gFamily m j = w} := by
  intro w
  have h1 : ((Fintype.card {i : Fin m // insRanking m a i = w} : ℕ) : ℝ) = tcount m w :=
    (card_eq_count (insWeight a) m w).trans (countIns_full m hm a ha w)
  exact_mod_cast h1.trans (card_gFamily_fibre m hm w).symm

/-! ## 2. Generic steps -/

theorem sum_prefix_fin {m : ℕ} (k : ℕ) (hk : k ≤ m) (F : ℕ → ℝ) :
    ∑ p ∈ (univ : Finset (Fin m)).filter (fun p : Fin m => p.val < k), F p
      = ∑ j ∈ range k, F j := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun j => if j < k then F j else 0) m]
  have hsub : range k ⊆ range m := range_mono hk
  rw [← sum_subset hsub (fun i _ hni => by simp [not_lt.mpr (by simpa using hni)])]
  exact sum_congr rfl fun i hi => if_pos (mem_range.mp hi)

/-- From a count bound with the class size as coefficient, to the per-item band. -/
theorem ratio_band (X c K M η : ℝ) (hc : 0 < c) (h : |X - c * (K / M)| ≤ c * (η / M)) :
    |X / c - K / M| ≤ η / M := by
  have hid : X / c - K / M = (X - c * (K / M)) / c := by
    rw [sub_div, mul_div_cancel_left₀ _ hc.ne']
  rw [hid, abs_div, abs_of_pos hc, div_le_iff₀ hc]
  exact h.trans (le_of_eq (mul_comm _ _))

/-- The band hypothesis of `actual_banded_witness_of_counts`, from an explicit count function
`C`: the end budgets are automatic, the interior ones are the arithmetic. -/
theorem hcounts_of {m : ℕ} {R : Type*} [Fintype R] (hm0 : 0 < m) (g : Ranking m)
    (base : R → Equiv.Perm (Fin m)) (q : R → ℝ) (η : ℝ) (hη : 0 ≤ η) (C : ℝ → ℕ → ℝ)
    (hC : ∀ k, k ≤ m → ∀ w, prefixClassCount g base q k w = C w k)
    (h0 : ∀ w, C w 0 = 0)
    (hfull : ∀ i : Fin m, C (g i) m = ((weightClass g (g i)).card : ℝ))
    (hmid : ∀ k, 1 ≤ k → k ≤ m - 1 → ∀ i : Fin m,
      |C (g i) k / ((weightClass g (g i)).card : ℝ) - (k : ℝ) / (m : ℝ)| ≤ η / (m : ℝ)) :
    ∀ k, k ≤ m → ∀ i : Fin m,
      |prefixClassCount g base q k (g i) / ((weightClass g (g i)).card : ℝ)
        - (k : ℝ) / (m : ℝ)| ≤ η / (m : ℝ) := by
  intro k hk i
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hcard : (0 : ℝ) < ((weightClass g (g i)).card : ℝ) := by
    have : 0 < (weightClass g (g i)).card :=
      Finset.card_pos.mpr ⟨i, by simp [weightClass]⟩
    exact_mod_cast this
  rw [hC k hk]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, h0]
    simp only [zero_div, Nat.cast_zero, sub_self, abs_zero]
    exact div_nonneg hη hmR.le
  · rcases Nat.lt_or_ge k m with hlt | hge
    · exact hmid k hkpos (by omega) i
    · have hkm : k = m := by omega
      rw [hkm, hfull i, div_self hcard.ne', div_self hmR.ne', sub_self, abs_zero]
      exact div_nonneg hη hmR.le

theorem mixCount_zero (m : ℕ) (w : ℝ) : mixCount m w 0 = 0 := by
  unfold mixCount countIns
  simp

theorem mixCount_full (m : ℕ) (hm : 3 ≤ m) (w : ℝ) : mixCount m w m = tcount m w := by
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold mixCount
  rw [Finset.sum_congr rfl (fun a ha => by
    rw [countIns_full m hm a (by have := Finset.mem_range.mp ha; omega) w])]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ m)]
  push_cast
  field_simp

/-! ## 3. The odd endpoint law -/

/-- The permutation naming the inserted ranking `a`. -/
noncomputable def insPerm (m : ℕ) (hm : 3 ≤ m) (a : Fin (m - 1)) : Equiv.Perm (Fin m) :=
  permOfCountEq (insRanking m a) (gFamily m)
    (insRanking_count m hm a (by have := a.isLt; omega))

theorem insPerm_apply (m : ℕ) (hm : 3 ≤ m) (a : Fin (m - 1)) (p : Fin m) :
    gFamily m (insPerm m hm a p) = insRanking m a p :=
  permOfCountEq_apply _ _ _ p

theorem rankOf_insPerm (m : ℕ) (hm : 3 ≤ m) (a : Fin (m - 1)) :
    rankOf (gFamily m) (insPerm m hm a) = insRanking m a :=
  rankOf_permOfCountEq _ _ _

/-- The uniform law on insertion points. -/
noncomputable def insQ (m : ℕ) : Fin (m - 1) → ℝ := fun _ => 1 / ((m : ℝ) - 1)

theorem insQ_nonneg (m : ℕ) (hm : 3 ≤ m) : ∀ a, 0 ≤ insQ m a := by
  intro a
  have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact div_nonneg zero_le_one (by linarith)

theorem insQ_sum (m : ℕ) (hm : 3 ≤ m) : ∑ a, insQ m a = 1 := by
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold insQ
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ m)]
  push_cast
  field_simp

/-- **Prefix counts under the insertion law are `mixCount`.** -/
theorem prefixClassCount_ins (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (hk : k ≤ m) (w : ℝ) :
    prefixClassCount (gFamily m) (insPerm m hm) (insQ m) k w = mixCount m w k := by
  unfold prefixClassCount mixCount
  rw [← Fin.sum_univ_eq_sum_range (fun a => (1 / ((m : ℝ) - 1)) * countIns a w k) (m - 1)]
  refine Finset.sum_congr rfl fun a _ => ?_
  show (1 / ((m : ℝ) - 1)) * _ = (1 / ((m : ℝ) - 1)) * countIns a w k
  congr 1
  simp only [insPerm_apply]
  exact sum_prefix_fin k hk (fun j => if insWeight a j = w then (1 : ℝ) else 0)

/-- The odd class sizes, in the form `O1_odd` states its coefficients. -/
theorem odd_light_sizes (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) :
    (((m - 1) / 2 : ℕ) : ℝ) = ((m : ℝ) - 1) / 2 ∧
      ((m - 2 - (m - 1) / 2 : ℕ) : ℝ) = ((m : ℝ) - 3) / 2 := by
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 3 := ⟨(m - 3) / 2, by omega⟩
  rw [show (2 * s + 3 - 1) / 2 = s + 1 from by omega,
    show 2 * s + 3 - 2 - (s + 1) = s from by omega]
  push_cast
  constructor <;> ring

/-- **The band at `eta = 1`, for every item and every budget.** -/
theorem odd_hcounts (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) :
    ∀ k, k ≤ m → ∀ i : Fin m,
      |prefixClassCount (gFamily m) (insPerm m hm) (insQ m) k (gFamily m i)
          / ((weightClass (gFamily m) (gFamily m i)).card : ℝ) - (k : ℝ) / (m : ℝ)|
        ≤ 1 / (m : ℝ) := by
  refine hcounts_of (by omega) (gFamily m) (insPerm m hm) (insQ m) 1 zero_le_one
    (mixCount m) (fun k hk w => prefixClassCount_ins m hm k hk w)
    (fun w => mixCount_zero m w) (fun i => by rw [mixCount_full m hm, card_weightClass m hm])
    ?_
  intro k hk1 hk i
  have hcpos : (0 : ℝ) < ((weightClass (gFamily m) (gFamily m i)).card : ℝ) := by
    have : 0 < (weightClass (gFamily m) (gFamily m i)).card :=
      Finset.card_pos.mpr ⟨i, by simp [weightClass]⟩
    exact_mod_cast this
  obtain ⟨h3, hn3, h1, hn1⟩ := O1_odd m k hm hmo hk1 hk
  obtain ⟨sneg, spos⟩ := odd_light_sizes m hm hmo
  rcases gFamily_weights m i with hv | hv | hv | hv <;> rw [hv] at hcpos ⊢ <;>
    rw [card_weightClass m hm] at hcpos ⊢
  · rw [tcount_neg_three] at hcpos ⊢
    exact ratio_band _ _ _ _ _ hcpos hn3
  · rw [tcount_neg_one, sneg] at hcpos ⊢
    exact ratio_band _ _ _ _ _ hcpos hn1
  · rw [tcount_one, spos] at hcpos ⊢
    exact ratio_band _ _ _ _ _ hcpos h1
  · rw [tcount_three] at hcpos ⊢
    exact ratio_band _ _ _ _ _ hcpos h3

/-- **The value: the free value at every interior budget.** -/
theorem odd_hvalue (m : ℕ) (hm : 3 ≤ m) :
    ∀ k ∈ budgets m,
      (∑ a, insQ m a * regret (gFamily m) (insPerm m hm a) (denom m) k) ≤ freeValue m := by
  intro k hk
  have hk' : 1 ≤ k ∧ k ≤ m - 1 := by simpa [budgets] using hk
  have hD : denom m ≠ 0 := by unfold denom; positivity
  apply le_of_eq
  have hreg : ∀ a : Fin (m - 1), insQ m a * regret (gFamily m) (insPerm m hm a) (denom m) k
      = (1 / ((m : ℝ) - 1)) * (excess (insRanking m a) k / denom m) := by
    intro a
    show (1 / ((m : ℝ) - 1)) * (excess (rankOf (gFamily m) (insPerm m hm a)) k / denom m) = _
    rw [rankOf_insPerm]
  rw [Finset.sum_congr rfl (fun a _ => hreg a),
    Fin.sum_univ_eq_sum_range
      (fun a => (1 / ((m : ℝ) - 1)) * (excess (insRanking m a) k / denom m)) (m - 1),
    insMixture_free_value m (by omega) (denom m) hD k hk'.1 hk'.2]
  rfl

/-- **The odd endpoint law exists**: an actual law on all permutations of `g_m`, feasible at
`eta = 1`, whose objective is at most the free value. -/
theorem odd_endpoint_law (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) :
    ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) 1,
      objective m (by omega) P ≤ freeValue m :=
  actual_banded_witness_of_counts (gFamily m) (insPerm m hm) (insQ m) 1 (denom m)
    (freeValue m) (budgets m) (budgets_nonempty m (by omega)) (insQ_nonneg m hm)
    (insQ_sum m hm) (odd_hcounts m hm hmo) (odd_hvalue m hm)

/-- The endpoint data `odd_breakpoint_iff` consumes, filled by that law. -/
noncomputable def oddEndpointData (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) :
    OddEndpointData m hm where
  endpoint := (odd_endpoint_law m hm hmo).choose
  endpoint_band := (odd_endpoint_law m hm hmo).choose_spec.1
  endpoint_value := (odd_endpoint_law m hm hmo).choose_spec.2

/-- **The odd breakpoint, unconditional.**  For every odd `m >= 3` and every `eta >= 0`,
the band-constrained value equals the free value exactly when `eta >= 1`. -/
theorem odd_breakpoint (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (η : ℝ) (hη : 0 ≤ η) :
    value m (by omega) η = freeValue m ↔ 1 ≤ η :=
  odd_breakpoint_iff m hm hmo (oddEndpointData m hm hmo) η hη

/-- The target `LeanPaperCEndgameV1` left explicit, discharged for every odd size. -/
theorem oddBreakpointFinish_holds : OddBreakpointFinish :=
  odd_finish (fun s => oddEndpointData (2 * s + 3) (by omega) (by omega))

/-! ## 4. The even endpoint law: insertion point and an independent sign flip -/

/-- The two rankings of the even law: the inserted ranking, or its sign flip. -/
noncomputable def evenRk (m : ℕ) (x : Fin (m - 1) × Bool) : Ranking m :=
  cond x.2 (fun i => -(insRanking m x.1 i)) (insRanking m x.1)

theorem evenRk_count (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) (x : Fin (m - 1) × Bool) :
    ∀ w : ℝ, Fintype.card {i : Fin m // evenRk m x i = w}
      = Fintype.card {j : Fin m // gFamily m j = w} := by
  intro w
  have hm3 : 3 ≤ m := by omega
  obtain ⟨a, b⟩ := x
  have ha : (a : ℕ) + 1 < m := by have := a.isLt; omega
  cases b
  · exact insRanking_count m hm3 a ha w
  · have h1 : ((Fintype.card {i : Fin m // evenRk m (a, true) i = w} : ℕ) : ℝ)
        = tcount m w :=
      (card_eq_count (fun i => -(insWeight a i)) m w).trans
        ((wcount_neg (insWeight a) m w).trans
          ((countIns_full m hm3 a ha (-w)).trans (tcount_neg m hmo w)))
    exact_mod_cast h1.trans (card_gFamily_fibre m hm3 w).symm

noncomputable def evenPerm (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) (x : Fin (m - 1) × Bool) :
    Equiv.Perm (Fin m) :=
  permOfCountEq (evenRk m x) (gFamily m) (evenRk_count m hm hmo x)

theorem evenPerm_apply (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) (x : Fin (m - 1) × Bool)
    (p : Fin m) : gFamily m (evenPerm m hm hmo x p) = evenRk m x p :=
  permOfCountEq_apply _ _ _ p

theorem rankOf_evenPerm (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) (x : Fin (m - 1) × Bool) :
    rankOf (gFamily m) (evenPerm m hm hmo x) = evenRk m x :=
  rankOf_permOfCountEq _ _ _

noncomputable def evenQ (m : ℕ) : Fin (m - 1) × Bool → ℝ := fun _ => 1 / (2 * ((m : ℝ) - 1))

theorem evenQ_nonneg (m : ℕ) (hm : 4 ≤ m) : ∀ x, 0 ≤ evenQ m x := by
  intro x
  have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact div_nonneg zero_le_one (by linarith)

theorem evenQ_sum (m : ℕ) (hm : 4 ≤ m) : ∑ x, evenQ m x = 1 := by
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold evenQ
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)]
  push_cast
  field_simp
  try ring

/-- The inner prefix count of one ranking of the even law. -/
theorem even_inner (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) (x : Fin (m - 1) × Bool) (k : ℕ)
    (hk : k ≤ m) (w : ℝ) :
    ∑ p ∈ (univ : Finset (Fin m)).filter (fun p : Fin m => p.val < k),
        (if gFamily m (evenPerm m hm hmo x p) = w then (1 : ℝ) else 0)
      = cond x.2 (countIns x.1 (-w) k) (countIns x.1 w k) := by
  simp only [evenPerm_apply]
  obtain ⟨a, b⟩ := x
  cases b
  · exact sum_prefix_fin k hk (fun j => if insWeight a j = w then (1 : ℝ) else 0)
  · show _ = countIns a (-w) k
    rw [← countInsFlip_eq]
    exact sum_prefix_fin k hk (fun j => if -(insWeight a j) = w then (1 : ℝ) else 0)

/-- **Prefix counts under the even law are `mixCountEven`.** -/
theorem prefixClassCount_even (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) (k : ℕ) (hk : k ≤ m)
    (w : ℝ) :
    prefixClassCount (gFamily m) (evenPerm m hm hmo) (evenQ m) k w = mixCountEven m w k := by
  unfold prefixClassCount
  rw [Finset.sum_congr rfl (fun x _ => by rw [even_inner m hm hmo x k hk w]),
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, evenQ]
  unfold mixCountEven mixCount
  rw [← Fin.sum_univ_eq_sum_range (fun a => (1 / ((m : ℝ) - 1)) * countIns a w k) (m - 1),
    ← Fin.sum_univ_eq_sum_range (fun a => (1 / ((m : ℝ) - 1)) * countIns a (-w) k) (m - 1),
    ← Finset.sum_add_distrib, Finset.sum_div]
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  refine Finset.sum_congr rfl fun a _ => ?_
  beta_reduce
  field_simp
  ring

theorem mixCountEven_zero (m : ℕ) (w : ℝ) : mixCountEven m w 0 = 0 := by
  unfold mixCountEven
  rw [mixCount_zero, mixCount_zero]
  ring

theorem mixCountEven_full (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) (w : ℝ) :
    mixCountEven m w m = tcount m w := by
  unfold mixCountEven
  rw [mixCount_full m (by omega) w, mixCount_full m (by omega) (-w), tcount_neg m hmo w]
  ring

/-- The even class sizes, in the form `O1_even` states its coefficient. -/
theorem even_light_sizes (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) :
    (((m - 1) / 2 : ℕ) : ℝ) = ((m : ℝ) - 2) / 2 ∧
      ((m - 2 - (m - 1) / 2 : ℕ) : ℝ) = ((m : ℝ) - 2) / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 4 := ⟨(m - 4) / 2, by omega⟩
  rw [show (2 * j + 4 - 1) / 2 = j + 1 from by omega,
    show 2 * j + 4 - 2 - (j + 1) = j + 1 from by omega]
  push_cast
  constructor <;> ring

/-- **The band at `eta_* = (m-2)/(2(m-1))`, for every item and every budget.** -/
theorem even_hcounts (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) :
    ∀ k, k ≤ m → ∀ i : Fin m,
      |prefixClassCount (gFamily m) (evenPerm m hm hmo) (evenQ m) k (gFamily m i)
          / ((weightClass (gFamily m) (gFamily m i)).card : ℝ) - (k : ℝ) / (m : ℝ)|
        ≤ etaStar m / (m : ℝ) := by
  have hm3 : 3 ≤ m := by omega
  have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hes : 0 ≤ etaStar m := by
    unfold etaStar
    exact div_nonneg (by linarith) (by linarith)
  refine hcounts_of (by omega) (gFamily m) (evenPerm m hm hmo) (evenQ m) (etaStar m) hes
    (mixCountEven m) (fun k hk w => prefixClassCount_even m hm hmo k hk w)
    (fun w => mixCountEven_zero m w)
    (fun i => by rw [mixCountEven_full m hm hmo, card_weightClass m hm3]) ?_
  intro k hk1 hk i
  have hcpos : (0 : ℝ) < ((weightClass (gFamily m) (gFamily m i)).card : ℝ) := by
    have : 0 < (weightClass (gFamily m) (gFamily m i)).card :=
      Finset.card_pos.mpr ⟨i, by simp [weightClass]⟩
    exact_mod_cast this
  obtain ⟨h3, h1⟩ := O1_even m k hm hk1 hk
  obtain ⟨sneg, spos⟩ := even_light_sizes m hm hmo
  have hn3 : mixCountEven m (-3) k = mixCountEven m 3 k := (mixCountEven_symm m 3 k).symm
  have hn1 : mixCountEven m (-1) k = mixCountEven m 1 k := (mixCountEven_symm m 1 k).symm
  rcases gFamily_weights m i with hv | hv | hv | hv <;> rw [hv] at hcpos ⊢ <;>
    rw [card_weightClass m hm3] at hcpos ⊢
  · rw [tcount_neg_three] at hcpos ⊢
    rw [hn3]
    exact ratio_band _ _ _ _ _ hcpos h3
  · rw [tcount_neg_one, sneg] at hcpos ⊢
    rw [hn1]
    exact ratio_band _ _ _ _ _ hcpos h1
  · rw [tcount_one, spos] at hcpos ⊢
    exact ratio_band _ _ _ _ _ hcpos h1
  · rw [tcount_three] at hcpos ⊢
    exact ratio_band _ _ _ _ _ hcpos h3

/-- **The value of the even law: the free value at every interior budget.** -/
theorem even_hvalue (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) :
    ∀ k ∈ budgets m,
      (∑ x, evenQ m x * regret (gFamily m) (evenPerm m hm hmo x) (denom m) k)
        ≤ freeValue m := by
  intro k hk
  have hk' : 1 ≤ k ∧ k ≤ m - 1 := by simpa [budgets] using hk
  have hD : denom m ≠ 0 := by unfold denom; positivity
  apply le_of_eq
  have hreg : ∀ x : Fin (m - 1) × Bool,
      evenQ m x * regret (gFamily m) (evenPerm m hm hmo x) (denom m) k
        = (1 / (2 * ((m : ℝ) - 1))) * (excess (evenRk m x) k / denom m) := by
    intro x
    show (1 / (2 * ((m : ℝ) - 1)))
        * (excess (rankOf (gFamily m) (evenPerm m hm hmo x)) k / denom m) = _
    rw [rankOf_evenPerm]
  rw [Finset.sum_congr rfl (fun x _ => hreg x), Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, evenRk, Bool.cond_true, Bool.cond_false]
  rw [Fin.sum_univ_eq_sum_range (fun a => (1 / (2 * ((m : ℝ) - 1)))
      * (excess (fun i => -(insRanking m a i)) k / denom m)
      + (1 / (2 * ((m : ℝ) - 1))) * (excess (insRanking m a) k / denom m)) (m - 1)]
  unfold freeValue
  rw [← insMixtureEven_free_value m (by omega) (denom m) hD k hk'.1 hk'.2]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **The even endpoint law exists**: feasible at `etaStar m`, objective at most the free
value, on all permutations of `g_m`. -/
theorem even_endpoint_law (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) :
    ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) (etaStar m),
      objective m (by omega) P ≤ freeValue m :=
  actual_banded_witness_of_counts (gFamily m) (evenPerm m hm hmo) (evenQ m) (etaStar m)
    (denom m) (freeValue m) (budgets m) (budgets_nonempty m (by omega)) (evenQ_nonneg m hm)
    (evenQ_sum m hm) (even_hcounts m hm hmo) (even_hvalue m hm hmo)

/-- The endpoint data `even_frontier` consumes: the law above, and `rankSum` from the even
total-excess inequality. -/
noncomputable def evenEndpointData (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) :
    EvenEndpointData m hm :=
  evenEndpointData_of_law m hm hmo (even_endpoint_law m hm hmo).choose
    (even_endpoint_law m hm hmo).choose_spec.1 (even_endpoint_law m hm hmo).choose_spec.2

/-- **The even frontier, unconditional, for every even `m >= 4`.** -/
theorem even_frontier_all (m : ℕ) (hm : 4 ≤ m) (heven : Even m) (η : ℝ) (hη : 0 ≤ η) :
    value m (by omega) η = max (freeValue m) (4 * (1 - η) / ((m : ℝ) * denom m)) :=
  even_frontier m hm heven (evenEndpointData m hm (Nat.even_iff.mp heven)) η hη

/-! ## Audit -/

#print axioms countIns_full
#print axioms card_weightClass
#print axioms insRanking_count
#print axioms sum_prefix_fin
#print axioms ratio_band
#print axioms hcounts_of
#print axioms prefixClassCount_ins
#print axioms odd_hcounts
#print axioms odd_hvalue
#print axioms odd_endpoint_law
#print axioms odd_breakpoint
#print axioms oddBreakpointFinish_holds
#print axioms evenRk_count
#print axioms prefixClassCount_even
#print axioms even_hcounts
#print axioms even_hvalue
#print axioms even_endpoint_law
#print axioms even_frontier_all

end CIGAMF.P13.PaperCEndpointLaw
