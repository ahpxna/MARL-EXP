import «LeanPaperCUniformV1»
import «LeanPaperCPermV1»

/-!
# Paper C: the concrete even-`m` family, and its weight multiplicities

`witness_of_relabelled` reduces C-H1's even side to two computations about a CONCRETE family:
the per-weight-class occupancy `hclass`, and the family's own value `hvalue`.  Both are about
a family of rankings that must all be rearrangements of one base ranking, which is what
`permOfCountEq` needs, and that needs the weight multiplicities.  This module computes them.

The family is the one Paper C already uses: the `m-1` insertion rankings, the flat ranking,
and the sign flip of each.  The base is the flat ranking itself, which avoids introducing a
separate `g_m` and having to prove the two agree.

The multiplicities are the same for every member -- one `+3`, one `-3`, and `(m-2)/2` each of
`+1` and `-1` -- and the sign flip permutes the four classes among themselves, so it changes
no multiplicity.  `insMult` and `flatMult` compute them; `mult_agree` is the equality
`permOfCountEq` consumes.
-/

namespace CIGAMF.P13.PaperCFamily

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCUniform
open CIGAMF.P13.PaperCEven
open CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCPerm

/-! ## Cardinalities as real counts -/

/-- **A weight class's cardinality is the count of positions carrying that weight.**  The
bridge between `permOfCountEq`'s `Fintype.card` and the sums Paper C computes. -/
theorem card_eq_count (f : ℕ → ℝ) (m : ℕ) (w : ℝ) :
    ((Fintype.card {i : Fin m // f (i : ℕ) = w} : ℕ) : ℝ)
      = ∑ i ∈ Finset.range m, (if f i = w then (1 : ℝ) else 0) := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun i => if f i = w then (1 : ℝ) else 0) m]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

/-! ## The insertion ranking's multiplicities -/

theorem insMult_three (m a : ℕ) (ha : a + 1 < m) : countIns a 3 m = 1 := by
  rw [countIns_three a m, if_pos (by omega)]

theorem insMult_neg_three (m a : ℕ) (ha : a + 1 < m) : countIns a (-3) m = 1 := by
  rw [countIns_neg_three a m, if_pos (by omega)]

/-- Exactly one of `a`, `a+1` is even, so the two deletions cost exactly one. -/
theorem ins_parity_pair (m a : ℕ) (ha : a + 1 < m) :
    ((if a < m ∧ Even a then (1 : ℝ) else 0)
      + (if a + 1 < m ∧ Even (a + 1) then (1 : ℝ) else 0)) = 1 := by
  have h1 : a < m := by omega
  rcases Nat.even_or_odd a with he | ho
  · have h2 : ¬ Even (a + 1) := by simp [Nat.even_add_one, he]
    rw [if_pos ⟨h1, he⟩, if_neg (fun h => h2 h.2)]
    ring
  · have h2 : Even (a + 1) := by simpa [Nat.even_add_one] using ho
    rw [if_neg (fun h => (Nat.not_even_iff_odd.mpr ho) h.2), if_pos ⟨ha, h2⟩]
    ring

theorem insMult_neg_one (m a : ℕ) (hm : Even m) (ha : a + 1 < m) :
    countIns a (-1) m = ((m : ℝ) - 2) / 2 := by
  obtain ⟨j, hj⟩ := hm
  have hm2 : m = 2 * j := by omega
  rw [countIns_neg_one a m]
  have hev : evensBelow m = (j : ℝ) := by rw [hm2]; exact evensBelow_two j
  have hpair := ins_parity_pair m a ha
  rw [hev]
  have hjm : (m : ℝ) = 2 * (j : ℝ) := by rw [hm2]; push_cast; ring
  rw [hjm]
  linarith [hpair]

theorem insMult_one (m a : ℕ) (hm : Even m) (ha : a + 1 < m) :
    countIns a 1 m = ((m : ℝ) - 2) / 2 := by
  obtain ⟨j, hj⟩ := hm
  have hm2 : m = 2 * j := by omega
  rw [countIns_one a m]
  have hod : oddsBelow m = (j : ℝ) := by rw [hm2]; exact oddsBelow_two j
  have h1 : a < m := by omega
  have hpair : ((if a < m ∧ ¬ Even a then (1 : ℝ) else 0)
      + (if a + 1 < m ∧ ¬ Even (a + 1) then (1 : ℝ) else 0)) = 1 := by
    rcases Nat.even_or_odd a with he | ho
    · have h2 : ¬ Even (a + 1) := by simp [Nat.even_add_one, he]
      rw [if_neg (fun h => h.2 he), if_pos ⟨ha, h2⟩]
      ring
    · have hno : ¬ Even a := Nat.not_even_iff_odd.mpr ho
      have h2 : Even (a + 1) := by simpa [Nat.even_add_one] using ho
      rw [if_pos ⟨h1, hno⟩, if_neg (fun h => h.2 h2)]
      ring
  rw [hod]
  have hjm : (m : ℝ) = 2 * (j : ℝ) := by rw [hm2]; push_cast; ring
  rw [hjm]
  linarith [hpair]

/-! ## The flat ranking's multiplicities -/

theorem flatW_mem (m i : ℕ) :
    flatW m i = -3 ∨ flatW m i = -1 ∨ flatW m i = 1 ∨ flatW m i = 3 := by
  unfold flatW
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)

/-- The last position of the flat ranking carries `+3`. -/
theorem flatW_last (m : ℕ) (hm : 1 < m) : flatW m (m - 1) = 3 := by
  unfold flatW
  rw [if_neg (by omega), if_pos rfl]

/-- A weight outside the four the family uses is carried by no position. -/
theorem count_eq_zero_of_other (f : ℕ → ℝ) (m : ℕ) (w : ℝ)
    (hf : ∀ i, f i = -3 ∨ f i = -1 ∨ f i = 1 ∨ f i = 3)
    (h3 : w ≠ -3) (h1 : w ≠ -1) (h1' : w ≠ 1) (h3' : w ≠ 3) :
    ∑ i ∈ Finset.range m, (if f i = w then (1 : ℝ) else 0) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [if_neg]
  intro h
  rcases hf i with h' | h' | h' | h'
  · exact h3 (h' ▸ h).symm
  · exact h1 (h' ▸ h).symm
  · exact h1' (h' ▸ h).symm
  · exact h3' (h' ▸ h).symm

/-- Splitting the last position off the full range. -/
theorem flatCount_full (m : ℕ) (w : ℝ) (hm : 1 < m) :
    flatCount m w m = flatCount m w (m - 1) + (if flatW m (m - 1) = w then (1 : ℝ) else 0) := by
  have hm1 : m - 1 + 1 = m := by omega
  have h := Finset.sum_range_succ (fun i => if flatW m i = w then (1 : ℝ) else 0) (m - 1)
  rw [hm1] at h
  unfold flatCount
  exact h

theorem flatMult_three (m : ℕ) (hm : 1 < m) : flatCount m 3 m = 1 := by
  rw [flatCount_full m 3 hm, flatCount_three m (m - 1) hm le_rfl,
    flatW_last m hm, if_pos rfl]
  ring

theorem flatMult_neg_three (m : ℕ) (hm : 1 < m) : flatCount m (-3) m = 1 := by
  rw [flatCount_full m (-3) hm, flatCount_neg_three m (m - 1) hm (by omega) le_rfl,
    flatW_last m hm, if_neg (by norm_num)]
  ring

theorem flatMult_one (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) :
    flatCount m 1 m = ((m : ℝ) - 2) / 2 := by
  obtain ⟨j, hj⟩ := hm
  have hm2 : m = 2 * j := by omega
  have hmj : m - 1 = 2 * (j - 1) + 1 := by omega
  rw [flatCount_full m 1 (by omega), flatCount_one m (m - 1) (by omega) le_rfl,
    flatW_last m (by omega), if_neg (by norm_num), hmj, oddsBelow_two_succ (j - 1)]
  have hj1 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    have : 1 ≤ j := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hj1]
  have hjm : (m : ℝ) = 2 * (j : ℝ) := by rw [hm2]; push_cast; ring
  rw [hjm]
  ring

theorem flatMult_neg_one (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) :
    flatCount m (-1) m = ((m : ℝ) - 2) / 2 := by
  obtain ⟨j, hj⟩ := hm
  have hm2 : m = 2 * j := by omega
  have hmj : m - 1 = 2 * (j - 1) + 1 := by omega
  rw [flatCount_full m (-1) (by omega),
    flatCount_neg_one m (m - 1) (by omega) (by omega) le_rfl,
    flatW_last m (by omega), if_neg (by norm_num), hmj, evensBelow_two_succ (j - 1)]
  have hj1 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    have : 1 ≤ j := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hj1]
  have hjm : (m : ℝ) = 2 * (j : ℝ) := by rw [hm2]; push_cast; ring
  rw [hjm]
  ring

/-! ## The sign flip, and the family's common multiplicities

The remaining member type is the sign flip.  It needs no new counting: flipping sends the
positions of weight `w` to the positions of weight `-w`, and the four multiplicities are
symmetric under `w ↦ -w` (`1, 1` for `±3` and `(m-2)/2, (m-2)/2` for `±1`), so no
multiplicity moves.  That is why the whole family -- insertions, flat, and every flip --
consists of rearrangements of ONE ranking, which is what `permOfCountEq` requires. -/

/-- The number of positions below `m` carrying weight `w`. -/
noncomputable def wcount (f : ℕ → ℝ) (m : ℕ) (w : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, (if f i = w then (1 : ℝ) else 0)

theorem wcount_ins (a m : ℕ) (w : ℝ) : wcount (insWeight a) m w = countIns a w m := rfl

theorem wcount_flat (m : ℕ) (w : ℝ) : wcount (flatW m) m w = flatCount m w m := rfl

/-- **Flipping the sign reflects the weight classes.** -/
theorem wcount_neg (f : ℕ → ℝ) (m : ℕ) (w : ℝ) :
    wcount (fun i => -(f i)) m w = wcount f m (-w) := by
  unfold wcount
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show (if -(f i) = w then (1 : ℝ) else 0) = (if f i = -w then (1 : ℝ) else 0)
  by_cases h : f i = -w
  · rw [if_pos (by rw [h]; ring), if_pos h]
  · rw [if_neg (fun hc => h (by rw [← hc]; ring)), if_neg h]

theorem insWeight_mem (a i : ℕ) :
    insWeight a i = -3 ∨ insWeight a i = -1 ∨ insWeight a i = 1 ∨ insWeight a i = 3 := by
  unfold insWeight
  split_ifs with h1 h2 h3
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl rfl
  · rcases Nat.even_or_odd (i + 1) with he | ho
    · exact Or.inr (Or.inr (Or.inl he.neg_one_pow))
    · exact Or.inr (Or.inl ho.neg_one_pow)
  · rcases Nat.even_or_odd (i - 1) with he | ho
    · exact Or.inr (Or.inr (Or.inl he.neg_one_pow))
    · exact Or.inr (Or.inl ho.neg_one_pow)

theorem negWeight_mem (f : ℕ → ℝ) (i : ℕ)
    (hf : ∀ j, f j = -3 ∨ f j = -1 ∨ f j = 1 ∨ f j = 3) :
    -(f i) = -3 ∨ -(f i) = -1 ∨ -(f i) = 1 ∨ -(f i) = 3 := by
  rcases hf i with h | h | h | h <;> rw [h] <;> norm_num

/-- **Four multiplicities determine the whole count function**, because no other weight
occurs.  This is what makes `hcount` -- which quantifies over every real `w` -- a finite
check. -/
theorem wcount_agree_of_four (f g : ℕ → ℝ) (m : ℕ)
    (hf : ∀ i, f i = -3 ∨ f i = -1 ∨ f i = 1 ∨ f i = 3)
    (hg : ∀ i, g i = -3 ∨ g i = -1 ∨ g i = 1 ∨ g i = 3)
    (e3 : wcount f m 3 = wcount g m 3) (e3' : wcount f m (-3) = wcount g m (-3))
    (e1 : wcount f m 1 = wcount g m 1) (e1' : wcount f m (-1) = wcount g m (-1))
    (w : ℝ) : wcount f m w = wcount g m w := by
  by_cases h3 : w = 3
  · rw [h3]; exact e3
  by_cases h3' : w = -3
  · rw [h3']; exact e3'
  by_cases h1 : w = 1
  · rw [h1]; exact e1
  by_cases h1' : w = -1
  · rw [h1']; exact e1'
  unfold wcount
  rw [count_eq_zero_of_other f m w hf h3' h1' h1 h3,
    count_eq_zero_of_other g m w hg h3' h1' h1 h3]

/-! ## Every member is a rearrangement of the flat ranking -/

/-- **The insertion ranking has the flat ranking's multiplicities.** -/
theorem ins_agrees_flat (m a : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (ha : a + 1 < m) (w : ℝ) :
    wcount (insWeight a) m w = wcount (flatW m) m w := by
  refine wcount_agree_of_four _ _ m (insWeight_mem a) (flatW_mem m) ?_ ?_ ?_ ?_ w
  · rw [wcount_ins, wcount_flat, insMult_three m a ha, flatMult_three m (by omega)]
  · rw [wcount_ins, wcount_flat, insMult_neg_three m a ha, flatMult_neg_three m (by omega)]
  · rw [wcount_ins, wcount_flat, insMult_one m a hm ha, flatMult_one m hm hm4]
  · rw [wcount_ins, wcount_flat, insMult_neg_one m a hm ha, flatMult_neg_one m hm hm4]

/-- **The flat ranking's own flip is a rearrangement of it.** -/
theorem flatFlip_agrees_flat (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (w : ℝ) :
    wcount (fun i => -(flatW m i)) m w = wcount (flatW m) m w := by
  refine wcount_agree_of_four _ _ m
    (fun i => negWeight_mem (flatW m) i (flatW_mem m)) (flatW_mem m) ?_ ?_ ?_ ?_ w
  · rw [wcount_neg, wcount_flat, wcount_flat, flatMult_neg_three m (by omega),
      flatMult_three m (by omega)]
  · rw [wcount_neg, wcount_flat, wcount_flat, show -(-3 : ℝ) = 3 from by norm_num,
      flatMult_three m (by omega), flatMult_neg_three m (by omega)]
  · rw [wcount_neg, wcount_flat, wcount_flat, flatMult_neg_one m hm hm4,
      flatMult_one m hm hm4]
  · rw [wcount_neg, wcount_flat, wcount_flat, show -(-1 : ℝ) = 1 from by norm_num,
      flatMult_one m hm hm4, flatMult_neg_one m hm hm4]

/-- **The flat multiplicity profile is symmetric under `w ↦ -w`.** -/
theorem flat_symm (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (w : ℝ) :
    wcount (flatW m) m (-w) = wcount (flatW m) m w := by
  rw [← wcount_neg (flatW m) m w, flatFlip_agrees_flat m hm hm4 w]

/-- **A flipped insertion ranking is also a rearrangement of the flat ranking.** -/
theorem insFlip_agrees_flat (m a : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (ha : a + 1 < m) (w : ℝ) :
    wcount (fun i => -(insWeight a i)) m w = wcount (flatW m) m w := by
  rw [wcount_neg, ins_agrees_flat m a hm hm4 ha (-w), flat_symm m hm hm4 w]

/-! ## The family as one indexed object, and its weights

The mixture Paper C uses puts `(m-1)/m` on the uniform mixture of the `m-1` insertion
rankings, `1/m` on the flat ranking, and then averages with the sign flip.  Multiplying
those out, EVERY member carries the same weight `1/(2m)`, and there are `2m` of them.  So the
law is uniform, and `fam_avg_eq_uniformMix` is an algebraic rearrangement rather than a
convex-combination argument. -/

/-- The family index: which ranking, and whether it is sign-flipped. -/
abbrev FamIdx (m : ℕ) := (Fin (m - 1) ⊕ Unit) × Bool

/-- The family's rankings, as position-indexed weight functions. -/
noncomputable def famW (m : ℕ) (x : FamIdx m) : ℕ → ℝ :=
  match x with
  | (Sum.inl a, false) => insWeight (a : ℕ)
  | (Sum.inl a, true) => fun i => -(insWeight (a : ℕ) i)
  | (Sum.inr _, false) => flatW m
  | (Sum.inr _, true) => fun i => -(flatW m i)

/-- How many of the first `k` positions carry weight `w`. -/
noncomputable def cntBelow (f : ℕ → ℝ) (k : ℕ) (w : ℝ) : ℝ :=
  ∑ i ∈ Finset.range k, (if f i = w then (1 : ℝ) else 0)

theorem cntBelow_ins (a k : ℕ) (w : ℝ) : cntBelow (insWeight a) k w = countIns a w k := rfl

theorem cntBelow_flat (m k : ℕ) (w : ℝ) : cntBelow (flatW m) k w = flatCount m w k := rfl

theorem cntBelow_neg (f : ℕ → ℝ) (k : ℕ) (w : ℝ) :
    cntBelow (fun i => -(f i)) k w = cntBelow f k (-w) := by
  unfold cntBelow
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show (if -(f i) = w then (1 : ℝ) else 0) = (if f i = -w then (1 : ℝ) else 0)
  by_cases h : f i = -w
  · rw [if_pos (by rw [h]; ring), if_pos h]
  · rw [if_neg (fun hc => h (by rw [← hc]; ring)), if_neg h]

/-- **The uniform average over the family is exactly the mixture Paper C computes.** -/
theorem fam_avg_eq_uniformMix (m k : ℕ) (hm : 1 < m) (w : ℝ) :
    (∑ x : FamIdx m, (1 / (2 * (m : ℝ))) * cntBelow (famW m x) k w) = uniformMix m w k := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := by omega
    positivity
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hcard : ((Finset.range (m - 1)).card : ℝ) = (m : ℝ) - 1 := by
    rw [Finset.card_range]
    have h1 : 1 ≤ m := by omega
    push_cast [Nat.cast_sub h1]
    ring
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_bool, famW]
  simp only [cntBelow_neg, cntBelow_ins, cntBelow_flat]
  unfold uniformMix mixFlat mixCount
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range
      (fun a => 1 / (2 * (m : ℝ)) * countIns a (-w) k
        + 1 / (2 * (m : ℝ)) * countIns a w k) (m - 1),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  field_simp
  ring

/-! ## Every member is a permutation of the base ranking

`permOfCountEq` turns equal weight-multiplicities into an actual permutation.  The counts are
in hand for every member, so the family is a family of PERMUTATIONS of `flatEven m` and not
merely a list of weight vectors -- which is what Paper C's objective is defined over. -/

/-- The family's rankings, indexed by position rather than by natural number. -/
noncomputable def famRanking (m : ℕ) (x : FamIdx m) : Ranking m :=
  fun i => famW m x (i : ℕ)

/-- **Every member has the base ranking's multiplicities.** -/
theorem fam_agrees_flat (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (x : FamIdx m) (w : ℝ) :
    wcount (famW m x) m w = wcount (flatW m) m w := by
  obtain ⟨u, b⟩ := x
  cases u with
  | inl a =>
      have ha : (a : ℕ) + 1 < m := by
        have h := a.isLt
        omega
      cases b with
      | false => exact ins_agrees_flat m (a : ℕ) hm hm4 ha w
      | true => exact insFlip_agrees_flat m (a : ℕ) hm hm4 ha w
  | inr _ =>
      cases b with
      | false => rfl
      | true => exact flatFlip_agrees_flat m hm hm4 w

/-- **The multiplicity equality `permOfCountEq` consumes**, in its `Fintype.card` form. -/
theorem famRanking_card (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (x : FamIdx m) (w : ℝ) :
    Fintype.card {i : Fin m // famRanking m x i = w}
      = Fintype.card {j : Fin m // flatEven m j = w} := by
  have h1 : ((Fintype.card {i : Fin m // famRanking m x i = w} : ℕ) : ℝ)
      = wcount (famW m x) m w := card_eq_count (famW m x) m w
  have h2 : ((Fintype.card {j : Fin m // flatEven m j = w} : ℕ) : ℝ)
      = wcount (flatW m) m w := card_eq_count (flatW m) m w
  have h3 := fam_agrees_flat m hm hm4 x w
  have : ((Fintype.card {i : Fin m // famRanking m x i = w} : ℕ) : ℝ)
      = ((Fintype.card {j : Fin m // flatEven m j = w} : ℕ) : ℝ) := by
    rw [h1, h3, ← h2]
  exact_mod_cast this

/-! ## The weight classes of the base ranking -/

/-- The base ranking's four class sizes, as reals. -/
theorem flatClass_card (m : ℕ) (w : ℝ) :
    (((Finset.univ.filter (fun j : Fin m => flatEven m j = w)).card : ℕ) : ℝ)
      = flatCount m w m := by
  classical
  have h := card_eq_count (flatW m) m w
  rw [Fintype.card_subtype] at h
  exact h

theorem flatClass_three (m : ℕ) (hm : 1 < m) :
    (((Finset.univ.filter (fun j : Fin m => flatEven m j = 3)).card : ℕ) : ℝ) = 1 := by
  rw [flatClass_card m 3, flatMult_three m hm]

theorem flatClass_neg_three (m : ℕ) (hm : 1 < m) :
    (((Finset.univ.filter (fun j : Fin m => flatEven m j = -3)).card : ℕ) : ℝ) = 1 := by
  rw [flatClass_card m (-3), flatMult_neg_three m hm]

theorem flatClass_one (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) :
    (((Finset.univ.filter (fun j : Fin m => flatEven m j = 1)).card : ℕ) : ℝ)
      = ((m : ℝ) - 2) / 2 := by
  rw [flatClass_card m 1, flatMult_one m hm hm4]

theorem flatClass_neg_one (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) :
    (((Finset.univ.filter (fun j : Fin m => flatEven m j = -1)).card : ℕ) : ℝ)
      = ((m : ℝ) - 2) / 2 := by
  rw [flatClass_card m (-1), flatMult_neg_one m hm hm4]

/-! ## The family as a law over permutations -/

open scoped Classical in
/-- Each member, as an actual permutation of the base ranking. -/
noncomputable def basePerm (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (x : FamIdx m) :
    Equiv.Perm (Fin m) :=
  permOfCountEq (famRanking m x) (flatEven m) (famRanking_card m hm hm4 x)

open scoped Classical in
theorem basePerm_apply (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (x : FamIdx m) (p : Fin m) :
    flatEven m (basePerm m hm hm4 x p) = famRanking m x p :=
  permOfCountEq_apply (famRanking m x) (flatEven m) (famRanking_card m hm hm4 x) p

/-- The law: uniform on the `2m` members. -/
noncomputable def famQ (m : ℕ) : FamIdx m → ℝ := fun _ => 1 / (2 * (m : ℝ))

theorem famQ_nonneg (m : ℕ) (x : FamIdx m) : 0 ≤ famQ m x := by
  unfold famQ
  positivity

theorem famIdx_card (m : ℕ) (hm : 1 ≤ m) : Fintype.card (FamIdx m) = 2 * m := by
  simp [FamIdx, Fintype.card_prod, Fintype.card_sum]
  omega

theorem famQ_sum (m : ℕ) (hm : 1 ≤ m) : ∑ x : FamIdx m, famQ m x = 1 := by
  unfold famQ
  rw [Finset.sum_const, Finset.card_univ, famIdx_card m hm, nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := hm
    positivity
  push_cast
  field_simp

/-- **The prefix of a member's permutation carries the member's own weights.**  This is where
the permutation is discharged: the position count under `basePerm` is the position count of
the weight vector it was built from. -/
theorem prefix_count_eq (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (x : FamIdx m) (k : ℕ)
    (hk : k ≤ m) (w : ℝ) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k),
        (if flatEven m (basePerm m hm hm4 x p) = w then (1 : ℝ) else 0))
      = cntBelow (famW m x) k w := by
  classical
  have hval : ∀ p : Fin m,
      (if flatEven m (basePerm m hm hm4 x p) = w then (1 : ℝ) else 0)
        = (if famW m x (p : ℕ) = w then (1 : ℝ) else 0) := by
    intro p
    rw [basePerm_apply m hm hm4 x p]
    rfl
  have hstep : ∀ p : Fin m,
      (if (p : ℕ) < k then
          (if flatEven m (basePerm m hm hm4 x p) = w then (1 : ℝ) else 0) else 0)
        = (if (p : ℕ) < k then (if famW m x (p : ℕ) = w then (1 : ℝ) else 0) else 0) := by
    intro p
    rw [hval p]
  rw [Finset.sum_filter, Finset.sum_congr rfl (fun p _ => hstep p),
    Fin.sum_univ_eq_sum_range
      (fun i => if i < k then (if famW m x i = w then (1 : ℝ) else 0) else 0) m]
  have hsub : Finset.range k ⊆ Finset.range m := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  rw [← Finset.sum_subset hsub (fun i hi hni => ?_)]
  · unfold cntBelow
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [if_pos hi]
  · rw [Finset.mem_range] at hi
    rw [Finset.mem_range] at hni
    rw [if_neg (by omega)]

/-! ## Audit -/

#print axioms card_eq_count
#print axioms flatW_mem
#print axioms flatW_last
#print axioms count_eq_zero_of_other
#print axioms flatCount_full
#print axioms flatMult_three
#print axioms flatMult_neg_three
#print axioms flatMult_one
#print axioms flatMult_neg_one
#print axioms wcount_neg
#print axioms insWeight_mem
#print axioms wcount_agree_of_four
#print axioms ins_agrees_flat
#print axioms flatFlip_agrees_flat
#print axioms flat_symm
#print axioms insFlip_agrees_flat
#print axioms cntBelow_neg
#print axioms fam_avg_eq_uniformMix
#print axioms fam_agrees_flat
#print axioms famRanking_card
#print axioms flatClass_card
#print axioms flatClass_three
#print axioms flatClass_neg_three
#print axioms flatClass_one
#print axioms flatClass_neg_one
#print axioms basePerm_apply
#print axioms famIdx_card
#print axioms famQ_sum
#print axioms prefix_count_eq
#print axioms insMult_three
#print axioms insMult_neg_three
#print axioms ins_parity_pair
#print axioms insMult_neg_one
#print axioms insMult_one

end CIGAMF.P13.PaperCFamily
