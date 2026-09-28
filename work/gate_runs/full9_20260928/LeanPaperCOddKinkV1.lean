import «LeanPaperCEndpointLawV1»
import «LeanPaperCRelaxedJoinV1»

/-!
# Paper C: the odd frontier, part 1 -- the second line and the kink law's rankings

For odd `m` the band-constrained optimum is the maximum of two lines on `[0, 1]`:

    L1(eta) = (m+3-(m+1) eta) / (m(m+4))        (`relaxed_value_odd`)
    L2(eta) = V_free + (1-eta) / (m(m+4)).

They cross at `eta_t = 1 - 2/(m(m-1))`.  This module proves the lower side of `L2` at full
strength and writes down the rankings of the law that attains the crossing point.

**The second line.**  `odd_value_gap` (`LeanPaperCOddBreakpointEndgameV1`) counts only the
`+3` item in last position and so gets the margin `2(1-eta)/(m D (m-1))`.  Every POSITIVE
item in last position costs the same two units of total excess (`odd_total_excess`), and
there are `(m-1)/2` of them, each last with probability at least `(1-eta)/m` by the band's
upper side at `k = m-1`.  Aggregated, the margin is `(1-eta)/(m D)`, a factor `(m-1)/2`
larger, which is what the crossing needs.

**The kink law's rankings** (`m = 2s+3`, `s >= 2`).  Each is the inserted ranking
`insWeight t` of `LeanPaperCRankingV1`, or its negation, with at most three positions at the
end overwritten:

* `insWeight t` -- slot `t`, version A (the existing inserted ranking);
* `spB m t` -- slot `t`, version B: every light negated, the pair reversed, position `m-1`
  kept at `-1`;
* `r3W m` -- the lights of version A, then `(-3, +3)`: the `+3` last;
* `r1W m` -- slot `0`, version A, with its last two lights swapped: a `+1` last.

Each is proved a rearrangement of `g_m` here.
-/

namespace CIGAMF.P13.PaperCOddKink

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCPerm
open CIGAMF.P13.PaperCRelabelBandJoin CIGAMF.P13.PaperCFam13
open CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCOddBreakpointEndgame
open CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCRelaxedJoin

/-! ## 1. The second line, at full strength -/

/-- `g_m` at odd `m = 2s+3` has `s+1` positive items: the `+3` and `s` light positives. -/
theorem pos_count (s : ℕ) :
    ∑ i, (if 0 < gFamily (2 * s + 3) i then (1 : ℝ) else 0) = (s : ℝ) + 1 := by
  have h := sum_fn_gFamily (2 * s + 1) (by omega) (fun w => if 0 < w then (1 : ℝ) else 0)
  rw [show 2 * s + 1 + 2 = 2 * s + 3 from by omega] at h
  rw [h, show (2 * s + 1 + 1) / 2 = s + 1 from by omega,
    show 2 * s + 1 - (s + 1) = s from by omega]
  norm_num
  ring

/-- **Every positive item is last with probability at least `(1-eta)/m`**, so the positive
items together are last with probability at least their number times that. -/
theorem last_pos_mass (m : ℕ) (hm : 3 ≤ m) (η : ℝ) (P : Perm m → ℝ)
    (hP : P ∈ FeasibleAt (id : Perm m → _) η) :
    (∑ i, (if 0 < gFamily m i then (1 : ℝ) else 0)) * ((1 - η) / (m : ℝ)) ≤
      ∑ σ, P σ * (if 0 < gFamily m (σ ⟨m - 1, by omega⟩) then (1 : ℝ) else 0) := by
  classical
  have hlast : ∀ i : Fin m, (1 - η) / (m : ℝ) ≤
      ∑ σ, P σ * (if i = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) := by
    intro i
    apply endpoint_last_lower (by omega) P id i (m : ℝ) η (by positivity) hP.2.1
    have h := (abs_le.mp (hP.2.2 (m - 1) (by omega) i)).2
    rw [Nat.cast_sub (by omega : 1 ≤ m)] at h
    norm_num at h
    simp only [id_eq]
    linarith
  have hind : ∀ σ : Perm m,
      (if 0 < gFamily m (σ ⟨m - 1, by omega⟩) then (1 : ℝ) else 0)
        = ∑ i, (if 0 < gFamily m i then (1 : ℝ) else 0)
            * (if i = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) := by
    intro σ
    rw [Finset.sum_eq_single (σ ⟨m - 1, by omega⟩)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  calc (∑ i, (if 0 < gFamily m i then (1 : ℝ) else 0)) * ((1 - η) / (m : ℝ))
      = ∑ i, (if 0 < gFamily m i then (1 : ℝ) else 0) * ((1 - η) / (m : ℝ)) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ i, (if 0 < gFamily m i then (1 : ℝ) else 0)
          * ∑ σ, P σ * (if i = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hlast i) (by split_ifs <;> norm_num))
    _ = ∑ σ, P σ * (if 0 < gFamily m (σ ⟨m - 1, by omega⟩) then (1 : ℝ) else 0) := by
        symm
        calc ∑ σ, P σ * (if 0 < gFamily m (σ ⟨m - 1, by omega⟩) then (1 : ℝ) else 0)
            = ∑ σ, P σ * ∑ i, (if 0 < gFamily m i then (1 : ℝ) else 0)
                * (if i = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) :=
              Finset.sum_congr rfl (fun σ _ => by rw [hind σ])
          _ = ∑ σ, ∑ i, P σ * ((if 0 < gFamily m i then (1 : ℝ) else 0)
                * (if i = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0)) := by
              simp only [Finset.mul_sum]
          _ = ∑ i, ∑ σ, P σ * ((if 0 < gFamily m i then (1 : ℝ) else 0)
                * (if i = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0)) := Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun σ _ => by ring)

/-- (L2) with the last-position indicator of ANY positive item. -/
theorem odd_rank_total_pos (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (σ : Perm m) :
    2 + 2 * (if 0 < gFamily m (σ ⟨m - 1, by omega⟩) then (1 : ℝ) else 0)
      ≤ totalExcess (rankOf (gFamily m) σ) := by
  let j := σ.symm (plusItem m hm)
  have hj3 : rankOf (gFamily m) σ ⟨j.val, j.isLt⟩ = 3 := by
    simpa [rankOf, j] using plusItem_weight m hm
  exact odd_total_excess (by omega) hmo _ (ranked_odd m hm hmo σ) j.val j.isLt hj3

/-- **The second line at every feasible law.** -/
theorem odd_line2_law (s : ℕ) (η : ℝ) (P : Perm (2 * s + 3) → ℝ)
    (hP : P ∈ FeasibleAt (id : Perm (2 * s + 3) → _) η) :
    freeValue (2 * s + 3) + (1 - η) / (((2 * s + 3 : ℕ) : ℝ) * denom (2 * s + 3))
      ≤ objective (2 * s + 3) (by omega) P := by
  have hm : 3 ≤ 2 * s + 3 := by omega
  have hmo : (2 * s + 3) % 2 = 1 := by omega
  have hmass := last_pos_mass (2 * s + 3) hm η P hP
  rw [pos_count s] at hmass
  have htot := Finset.sum_le_sum (fun σ (_ : σ ∈ (univ : Finset (Perm (2 * s + 3)))) =>
    mul_le_mul_of_nonneg_left (odd_rank_total_pos (2 * s + 3) hm hmo σ) (hP.1 σ))
  have hsplit : ∑ σ, P σ * (2 + 2 * (if 0 < gFamily (2 * s + 3) (σ ⟨2 * s + 3 - 1, by omega⟩)
        then (1 : ℝ) else 0))
      = 2 * (∑ σ, P σ) + 2 * ∑ σ, P σ *
          (if 0 < gFamily (2 * s + 3) (σ ⟨2 * s + 3 - 1, by omega⟩) then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun σ _ => by ring)
  rw [hsplit, hP.2.1] at htot
  have hmean : 2 + 2 * (((s : ℝ) + 1) * ((1 - η) / ((2 * s + 3 : ℕ) : ℝ)))
      ≤ ∑ σ, P σ * totalExcess (rankOf (gFamily (2 * s + 3)) σ) := by linarith
  have h := objective_ge_mean_total (2 * s + 3) hm P _ hmean
  refine le_of_eq_of_le ?_ h
  have hx : ((2 * s + 3 : ℕ) : ℝ) = 2 * (s : ℝ) + 3 := by push_cast; ring
  unfold freeValue denom
  rw [hx]
  have h1 : (2 : ℝ) * s + 3 ≠ 0 := by positivity
  have h2 : (2 : ℝ) * s + 3 - 1 ≠ 0 := by
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    intro h; linarith
  have h3 : (2 : ℝ) * s + 3 + 4 ≠ 0 := by positivity
  field_simp
  ring

/-- **The second line at the value**: `V_m(eta) >= V_free + (1-eta)/(m(m+4))`. -/
theorem odd_line2_value (s : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    freeValue (2 * s + 3) + (1 - η) / (((2 * s + 3 : ℕ) : ℝ) * denom (2 * s + 3))
      ≤ value (2 * s + 3) (by omega) η :=
  value_lower (2 * s + 3) (by omega) η _ hη (fun P hP => odd_line2_law s η P hP)

/-! ## 2. The kink law's rankings, and why each is a rearrangement of `g_m` -/

/-- Version B at slot `t`. -/
noncomputable def spB (m t i : ℕ) : ℝ := if i = m - 1 then -1 else -insWeight t i

/-- The lights of version A, then `(-3, +3)`. -/
noncomputable def r3W (m i : ℕ) : ℝ :=
  if i = m - 2 then -3 else if i = m - 1 then 3 else insWeight (m - 2) i

/-- Slot `0`, version A, with its last two lights swapped. -/
noncomputable def r1W (m i : ℕ) : ℝ :=
  if i = m - 2 then -1 else if i = m - 1 then 1 else insWeight 0 i

/-- Weight counts of a sequence below `k`. -/
noncomputable def cnt (f : ℕ → ℝ) (w : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range k, (if f i = w then (1 : ℝ) else 0)

theorem cnt_insWeight (a : ℕ) (w : ℝ) (k : ℕ) : cnt (insWeight a) w k = countIns a w k := rfl

theorem cnt_succ (f : ℕ → ℝ) (w : ℝ) (k : ℕ) :
    cnt f w (k + 1) = cnt f w k + (if f k = w then (1 : ℝ) else 0) := by
  unfold cnt; rw [Finset.sum_range_succ]

theorem insWeight_after (t i : ℕ) (hi : t + 1 < i) : insWeight t i = (-1 : ℝ) ^ (i - 1) := by
  unfold insWeight
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem insWeight_before (t i : ℕ) (hi : i < t) : insWeight t i = (-1 : ℝ) ^ (i + 1) := by
  unfold insWeight
  rw [if_neg (by omega), if_neg (by omega), if_pos hi]

theorem neg_one_pow_even' (s : ℕ) : (-1 : ℝ) ^ (2 * s) = 1 :=
  Even.neg_one_pow (⟨s, by ring⟩ : Even (2 * s))

theorem neg_one_pow_odd' (s : ℕ) : (-1 : ℝ) ^ (2 * s + 1) = -1 :=
  Odd.neg_one_pow (⟨s, rfl⟩ : Odd (2 * s + 1))

/-- The last position of an inserted ranking with the pair before it carries `-1`. -/
theorem insWeight_last (s t : ℕ) (ht : t ≤ 2 * s) : insWeight t (2 * s + 2) = -1 := by
  rw [insWeight_after t _ (by omega), show 2 * s + 2 - 1 = 2 * s + 1 from by omega,
    neg_one_pow_odd']

/-- The odd count table is the negated table with one light moved across. -/
theorem tcount_flip (s : ℕ) (w : ℝ) :
    tcount (2 * s + 3) (-w) - (if -w = -1 then (1 : ℝ) else 0) + (if w = -1 then (1 : ℝ) else 0)
      = tcount (2 * s + 3) w := by
  have hn1 : (((2 * s + 3 - 1) / 2 : ℕ) : ℝ) = (s : ℝ) + 1 := by
    rw [show (2 * s + 3 - 1) / 2 = s + 1 from by omega]; push_cast; ring
  have hp1 : ((2 * s + 3 - 2 - (2 * s + 3 - 1) / 2 : ℕ) : ℝ) = (s : ℝ) := by
    rw [show 2 * s + 3 - 2 - (2 * s + 3 - 1) / 2 = s from by omega]
  by_cases h3 : w = 3
  · subst h3
    rw [show -(3 : ℝ) = -3 by ring, tcount_neg_three, tcount_three]; norm_num
  by_cases h3' : w = -3
  · subst h3'
    rw [show -(-3 : ℝ) = 3 by ring, tcount_three, tcount_neg_three]; norm_num
  by_cases h1 : w = 1
  · subst h1
    rw [tcount_neg_one, tcount_one, hn1, hp1]; norm_num
  by_cases h1' : w = -1
  · subst h1'
    rw [show -(-1 : ℝ) = 1 by ring, tcount_one, tcount_neg_one, hn1, hp1]; norm_num
  rw [tcount_other _ w h3 h3' h1 h1',
    tcount_other _ (-w) (fun h => h3' (by linarith)) (fun h => h3 (by linarith))
      (fun h => h1' (by linarith)) (fun h => h1 (by linarith)),
    if_neg (fun h => h1 (by linarith)), if_neg h1']
  ring

theorem cnt_spB (s t : ℕ) (ht : t ≤ 2 * s) (w : ℝ) :
    cnt (spB (2 * s + 3) t) w (2 * s + 3) = tcount (2 * s + 3) w := by
  have hfull := countIns_full (2 * s + 3) (by omega) t (by omega) (-w)
  have hsA : countIns t (-w) (2 * s + 3)
      = countIns t (-w) (2 * s + 2) + (if insWeight t (2 * s + 2) = -w then (1 : ℝ) else 0) :=
    Finset.sum_range_succ _ _
  have hsB : cnt (spB (2 * s + 3) t) w (2 * s + 3)
      = cnt (spB (2 * s + 3) t) w (2 * s + 2)
        + (if spB (2 * s + 3) t (2 * s + 2) = w then (1 : ℝ) else 0) :=
    Finset.sum_range_succ _ _
  have hbody : cnt (spB (2 * s + 3) t) w (2 * s + 2) = countIns t (-w) (2 * s + 2) := by
    unfold cnt countIns
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    unfold spB
    rw [if_neg (show i ≠ 2 * s + 3 - 1 by omega)]
    by_cases h : insWeight t i = -w
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (fun h' => h (by linarith))]
  have hlast : spB (2 * s + 3) t (2 * s + 2) = -1 := by
    unfold spB; rw [if_pos (show 2 * s + 2 = 2 * s + 3 - 1 by omega)]
  rw [hsB, hbody, hlast]
  rw [hsA, insWeight_last s t ht] at hfull
  have hflip := tcount_flip s w
  have e1 : (if -w = (-1 : ℝ) then (1 : ℝ) else 0) = (if (-1 : ℝ) = -w then 1 else 0) := by
    by_cases h : -w = (-1 : ℝ)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have e2 : (if w = (-1 : ℝ) then (1 : ℝ) else 0) = (if (-1 : ℝ) = w then 1 else 0) := by
    by_cases h : w = (-1 : ℝ)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  rw [e1, e2] at hflip
  linarith

theorem cnt_r3W (s : ℕ) (w : ℝ) :
    cnt (r3W (2 * s + 3)) w (2 * s + 3) = tcount (2 * s + 3) w := by
  have hfull := countIns_full (2 * s + 3) (by omega) (2 * s + 1) (by omega) w
  have hA : countIns (2 * s + 1) w (2 * s + 3)
      = countIns (2 * s + 1) w (2 * s + 1)
        + (if insWeight (2 * s + 1) (2 * s + 1) = w then (1 : ℝ) else 0)
        + (if insWeight (2 * s + 1) (2 * s + 2) = w then (1 : ℝ) else 0) := by
    rw [show countIns (2 * s + 1) w (2 * s + 3)
        = countIns (2 * s + 1) w (2 * s + 2)
          + (if insWeight (2 * s + 1) (2 * s + 2) = w then (1 : ℝ) else 0) from
          Finset.sum_range_succ _ _,
      show countIns (2 * s + 1) w (2 * s + 2)
        = countIns (2 * s + 1) w (2 * s + 1)
          + (if insWeight (2 * s + 1) (2 * s + 1) = w then (1 : ℝ) else 0) from
          Finset.sum_range_succ _ _]
  have h1 : insWeight (2 * s + 1) (2 * s + 1) = 3 := by unfold insWeight; rw [if_pos rfl]
  have h2 : insWeight (2 * s + 1) (2 * s + 2) = -3 := by
    unfold insWeight; rw [if_neg (by omega), if_pos rfl]
  have hB : cnt (r3W (2 * s + 3)) w (2 * s + 3)
      = cnt (r3W (2 * s + 3)) w (2 * s + 1)
        + (if r3W (2 * s + 3) (2 * s + 1) = w then (1 : ℝ) else 0)
        + (if r3W (2 * s + 3) (2 * s + 2) = w then (1 : ℝ) else 0) := by
    rw [show cnt (r3W (2 * s + 3)) w (2 * s + 3)
        = cnt (r3W (2 * s + 3)) w (2 * s + 2)
          + (if r3W (2 * s + 3) (2 * s + 2) = w then (1 : ℝ) else 0) from
          Finset.sum_range_succ _ _,
      show cnt (r3W (2 * s + 3)) w (2 * s + 2)
        = cnt (r3W (2 * s + 3)) w (2 * s + 1)
          + (if r3W (2 * s + 3) (2 * s + 1) = w then (1 : ℝ) else 0) from
          Finset.sum_range_succ _ _]
  have h3 : r3W (2 * s + 3) (2 * s + 1) = -3 := by
    unfold r3W; rw [if_pos (show 2 * s + 1 = 2 * s + 3 - 2 by omega)]
  have h4 : r3W (2 * s + 3) (2 * s + 2) = 3 := by
    unfold r3W
    rw [if_neg (show 2 * s + 2 ≠ 2 * s + 3 - 2 by omega),
      if_pos (show 2 * s + 2 = 2 * s + 3 - 1 by omega)]
  have hbody : cnt (r3W (2 * s + 3)) w (2 * s + 1) = countIns (2 * s + 1) w (2 * s + 1) := by
    unfold cnt countIns
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    unfold r3W
    rw [if_neg (show i ≠ 2 * s + 3 - 2 by omega), if_neg (show i ≠ 2 * s + 3 - 1 by omega),
      show 2 * s + 3 - 2 = 2 * s + 1 from by omega]
  rw [hB, hbody, h3, h4, ← hfull, hA, h1, h2]
  ring

theorem cnt_r1W (s : ℕ) (hs : 1 ≤ s) (w : ℝ) :
    cnt (r1W (2 * s + 3)) w (2 * s + 3) = tcount (2 * s + 3) w := by
  have hfull := countIns_full (2 * s + 3) (by omega) 0 (by omega) w
  have hA : countIns 0 w (2 * s + 3)
      = countIns 0 w (2 * s + 1) + (if insWeight 0 (2 * s + 1) = w then (1 : ℝ) else 0)
        + (if insWeight 0 (2 * s + 2) = w then (1 : ℝ) else 0) := by
    rw [show countIns 0 w (2 * s + 3)
        = countIns 0 w (2 * s + 2) + (if insWeight 0 (2 * s + 2) = w then (1 : ℝ) else 0) from
          Finset.sum_range_succ _ _,
      show countIns 0 w (2 * s + 2)
        = countIns 0 w (2 * s + 1) + (if insWeight 0 (2 * s + 1) = w then (1 : ℝ) else 0) from
          Finset.sum_range_succ _ _]
  have h1 : insWeight 0 (2 * s + 1) = 1 := by
    rw [insWeight_after 0 _ (by omega), show 2 * s + 1 - 1 = 2 * s from by omega,
      neg_one_pow_even']
  have h2 : insWeight 0 (2 * s + 2) = -1 := by
    rw [insWeight_after 0 _ (by omega), show 2 * s + 2 - 1 = 2 * s + 1 from by omega,
      neg_one_pow_odd']
  have hB : cnt (r1W (2 * s + 3)) w (2 * s + 3)
      = cnt (r1W (2 * s + 3)) w (2 * s + 1)
        + (if r1W (2 * s + 3) (2 * s + 1) = w then (1 : ℝ) else 0)
        + (if r1W (2 * s + 3) (2 * s + 2) = w then (1 : ℝ) else 0) := by
    rw [show cnt (r1W (2 * s + 3)) w (2 * s + 3)
        = cnt (r1W (2 * s + 3)) w (2 * s + 2)
          + (if r1W (2 * s + 3) (2 * s + 2) = w then (1 : ℝ) else 0) from
          Finset.sum_range_succ _ _,
      show cnt (r1W (2 * s + 3)) w (2 * s + 2)
        = cnt (r1W (2 * s + 3)) w (2 * s + 1)
          + (if r1W (2 * s + 3) (2 * s + 1) = w then (1 : ℝ) else 0) from
          Finset.sum_range_succ _ _]
  have h3 : r1W (2 * s + 3) (2 * s + 1) = -1 := by
    unfold r1W; rw [if_pos (show 2 * s + 1 = 2 * s + 3 - 2 by omega)]
  have h4 : r1W (2 * s + 3) (2 * s + 2) = 1 := by
    unfold r1W
    rw [if_neg (show 2 * s + 2 ≠ 2 * s + 3 - 2 by omega),
      if_pos (show 2 * s + 2 = 2 * s + 3 - 1 by omega)]
  have hbody : cnt (r1W (2 * s + 3)) w (2 * s + 1) = countIns 0 w (2 * s + 1) := by
    unfold cnt countIns
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    unfold r1W
    rw [if_neg (show i ≠ 2 * s + 3 - 2 by omega), if_neg (show i ≠ 2 * s + 3 - 1 by omega)]
  rw [hB, hbody, h3, h4, ← hfull, hA, h1, h2]
  ring

/-- From a count identity to the rearrangement `permOfCountEq` consumes. -/
theorem rearr_of_cnt (s : ℕ) (f : ℕ → ℝ)
    (h : ∀ w, cnt f w (2 * s + 3) = tcount (2 * s + 3) w) :
    ∀ w : ℝ, Fintype.card {i : Fin (2 * s + 3) // (fun i : Fin (2 * s + 3) => f (i : ℕ)) i = w}
      = Fintype.card {j : Fin (2 * s + 3) // gFamily (2 * s + 3) j = w} := by
  intro w
  have h1 : ((Fintype.card {i : Fin (2 * s + 3) // f (i : ℕ) = w} : ℕ) : ℝ)
      = tcount (2 * s + 3) w := (card_eq_count f (2 * s + 3) w).trans (h w)
  exact_mod_cast h1.trans (card_gFamily_fibre (2 * s + 3) (by omega) w).symm

end CIGAMF.P13.PaperCOddKink

#print axioms CIGAMF.P13.PaperCOddKink.odd_line2_value
#print axioms CIGAMF.P13.PaperCOddKink.cnt_spB
#print axioms CIGAMF.P13.PaperCOddKink.cnt_r3W
#print axioms CIGAMF.P13.PaperCOddKink.cnt_r1W
