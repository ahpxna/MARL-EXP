import «LeanSupportMinimaxCountingV1»

/-! # Support: the passive Bayes value, from the sampling law to `E[L_N/(a+L_N)]`.

`LeanSupportMinimaxCountingV1` proves the counting identity `posterior_ratio` and says
of itself that no probability space appears in it and that reading its cardinalities as a
posterior "is the step the wrapper must make, and it is NOT made here".
`LeanSupportPassiveAnswerMultiplicityV1` and `LeanSupportOccupancyMomentsV1` say the same:
`R_N^* = E[L_N/(a+L_N)]` is not theirs.

THIS FILE MAKES THAT STEP, over a finite joint mass -- no measure theory is needed because
the transcript space `Fin N -> Option (Fin m)` is finite.

THE MODEL, built from the sampling law and not written down.
* `draw b p W` is the per-observation law of world `W`: the anchor `none` has mass
  `1 - b p`, each tip of `W` has mass `p`, a label outside `W` has mass `0`.
* `lik b p W h = prod over i of draw b p W (h i)` -- the likelihood IS the product of the
  per-draw masses. `lik_eq` then DERIVES the closed form
  `1{seen h subset W} (1-bp)^{n_0} p^{N-n_0}`; it is a theorem, not a definition.
* `sum_lik_transcripts_eq_one` checks the law really is a law: for every world of the right
  size the likelihood sums to `1` over all transcripts, and `sum_mass_eq_one` then gives
  `sum_h mass = 1`.

WHAT IS PROVED.
* `joint_mul_unseen` -- the counting identity of `LeanSupportMinimaxCountingV1`, transported
  onto the joint mass: for an UNSEEN `j`,
  `joint h j * (m - s) = mass h * (b - s)`. Denominators stay cleared, so no positivity
  side condition is smuggled in.
* `joint_eq_mass_of_seen` -- for a SEEN `j` the error mass is the whole transcript mass.
* `risk_ge` -- EVERY randomised decoder, with no structure assumed beyond `alpha >= 0` and
  `sum_j alpha = 1`, has risk at least `bayesValue`. This is the lower bound and it quantifies
  over all decoders, not over a class.
* `risk_uniformUnseen` -- the uniform-on-unseen decoder attains it exactly.
* `bayes_minimax` -- `IsLeast`: `bayesValue` is attained AND is a lower bound, i.e. it is the
  Bayes value, not merely a bound.
* `bayesValue` is by definition `sum_h mass h * L/(a+L)` with `L = b - s(h)` and `a = m - b`,
  which is `E[L_N/(a+L_N)]` as a finite expectation over transcripts.

THE MINIMAX SECTION, added after the text above was first written. `worldRisk`,
`risk_mul_choose`, `relabel`, `lik_relabel`, `seen_relabel`, `uuAlpha_relabel`,
`transport`, `image_transport` and `worldRisk_uu_const` prove the equivariance, and
`passive_minimax` concludes: `bayesValue` is the least achievable WORST-CASE-over-worlds
risk, i.e. the MINIMAX value, not merely the Bayes value.

## WHAT THIS DOES NOT ESTABLISH

- The Bayes-to-minimax step IS now proved (`passive_minimax`); an earlier version of this
  header said it was not, and that sentence was stale.
- Equal tip masses `p` are a hypothesis of the model, in `draw`. With unequal masses the
  posterior is not uniform and nothing here transfers.
- The decoder declares ONE label safe. A decoder returning a set, or abstaining, is outside
  the statement.
- Nothing here computes `E[L_N/(a+L_N)]` in closed form; `LeanSupportOccupancyMomentsV1` has
  the moments of `L_N`, and the two are NOT joined -- the occupancy module works on a
  per-world product measure and this one on the world-averaged transcript mass.
- No active queries, no adaptivity, no sample-size law.
-/

namespace CIGAMF.P13.SupportBayesMinimax
open Finset
open scoped BigOperators
open CIGAMF.P13.SupportMinimaxCounting
noncomputable section
variable {m N : ℕ}

/-- One observation: the anchor, or a tip label. -/
abbrev Obs (m : ℕ) := Option (Fin m)

/-- A transcript of `N` draws. -/
abbrev Transcript (m N : ℕ) := Fin N → Obs m

/-- The labels the transcript exposed. -/
def seen (h : Transcript m N) : Finset (Fin m) :=
  univ.filter (fun j => ∃ i, h i = some j)

theorem mem_seen {h : Transcript m N} {j : Fin m} :
    j ∈ seen h ↔ ∃ i, h i = some j := by
  simp [seen]

/-- The number of anchor draws. -/
def emptyCount (h : Transcript m N) : ℕ := (univ.filter (fun i => h i = none)).card

/-- The number of tip draws. -/
def tipCount (h : Transcript m N) : ℕ := (univ.filter (fun i => ¬ (h i = none))).card

theorem count_add (h : Transcript m N) : emptyCount h + tipCount h = N := by
  classical
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
      (p := fun i => h i = none)
  simpa [emptyCount, tipCount] using this

/-! ## The sampling law -/

/-- The per-observation law of world `W`. -/
def draw (b : ℕ) (p : ℝ) (W : Finset (Fin m)) : Obs m → ℝ
  | none => 1 - b * p
  | some j => if j ∈ W then p else 0

/-- The likelihood of a transcript IS the product of the per-draw masses. -/
def lik (b : ℕ) (p : ℝ) (W : Finset (Fin m)) (h : Transcript m N) : ℝ :=
  ∏ i, draw b p W (h i)

/-- The value the likelihood takes on every consistent world. -/
def likC (b : ℕ) (p : ℝ) (h : Transcript m N) : ℝ :=
  (1 - b * p) ^ emptyCount h * p ^ tipCount h

/-- The closed form is DERIVED from the product, not assumed. -/
theorem lik_eq (b : ℕ) (p : ℝ) (W : Finset (Fin m)) (h : Transcript m N) :
    lik b p W h = if seen h ⊆ W then likC b p h else 0 := by
  classical
  by_cases hsub : seen h ⊆ W
  · rw [if_pos hsub]
    have hstep : ∀ i : Fin N, draw b p W (h i)
        = if h i = none then (1 - (b : ℝ) * p) else p := by
      intro i
      cases hi : h i with
      | none => simp [draw, hi]
      | some j =>
        have hj : j ∈ W := hsub (mem_seen.mpr ⟨i, hi⟩)
        simp [draw, hi, hj]
    rw [lik, Finset.prod_congr rfl (fun i _ => hstep i), Finset.prod_ite,
      Finset.prod_const, Finset.prod_const]
    rfl
  · rw [if_neg hsub]
    obtain ⟨j, hjs, hjW⟩ : ∃ j, j ∈ seen h ∧ j ∉ W := by
      by_contra hc
      push_neg at hc
      exact hsub hc
    obtain ⟨i, hi⟩ := mem_seen.mp hjs
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [draw, hi, hjW]

theorem lik_nonneg (b : ℕ) (p : ℝ) (hp : 0 ≤ p) (hbp : (b : ℝ) * p ≤ 1)
    (W : Finset (Fin m)) (h : Transcript m N) : 0 ≤ lik b p W h := by
  classical
  refine Finset.prod_nonneg (fun i _ => ?_)
  cases hi : h i with
  | none =>
    have hle : (0:ℝ) ≤ 1 - (b : ℝ) * p := by linarith
    simpa [draw] using hle
  | some j =>
    by_cases hj : j ∈ W <;> simp [draw, hj, hp]

/-! ## Worlds, and the joint mass -/

/-- The worlds: the `b`-subsets of `Fin m`. -/
def worlds (m b : ℕ) : Finset (Finset (Fin m)) :=
  (univ : Finset (Finset (Fin m))).filter (fun W => W.card = b)

/-- Worlds consistent with the seen set. -/
def adm (b : ℕ) (S : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  (univ : Finset (Finset (Fin m))).filter (fun W => W.card = b ∧ S ⊆ W)

/-- Consistent worlds that also contain `j`. -/
def admWith (b : ℕ) (S : Finset (Fin m)) (j : Fin m) : Finset (Finset (Fin m)) :=
  (univ : Finset (Finset (Fin m))).filter (fun W => W.card = b ∧ S ⊆ W ∧ j ∈ W)

theorem worlds_card (m b : ℕ) : (worlds m b).card = m.choose b := by
  classical
  have : worlds m b = (univ : Finset (Fin m)).powersetCard b := by
    ext W; simp [worlds, Finset.mem_powersetCard]
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem worlds_filter_subset (b : ℕ) (S : Finset (Fin m)) :
    (worlds m b).filter (fun W => S ⊆ W) = adm b S := by
  classical
  ext W; simp [worlds, adm, and_assoc]

theorem worlds_filter_subset_mem (b : ℕ) (S : Finset (Fin m)) (j : Fin m) :
    (worlds m b).filter (fun W => S ⊆ W ∧ j ∈ W) = admWith b S j := by
  classical
  ext W; simp [worlds, admWith, and_assoc]

theorem sum_lik (b : ℕ) (p : ℝ) (h : Transcript m N) :
    ∑ W ∈ worlds m b, lik b p W h = likC b p h * ((adm b (seen h)).card : ℝ) := by
  classical
  rw [Finset.sum_congr rfl (fun W _ => lik_eq b p W h), Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, worlds_filter_subset,
    nsmul_eq_mul, mul_comm]

theorem sum_lik_mem (b : ℕ) (p : ℝ) (h : Transcript m N) (j : Fin m) :
    ∑ W ∈ worlds m b, (if j ∈ W then lik b p W h else 0)
      = likC b p h * ((admWith b (seen h) j).card : ℝ) := by
  classical
  have hstep : ∀ W ∈ worlds m b, (if j ∈ W then lik b p W h else 0)
      = if (seen h ⊆ W ∧ j ∈ W) then likC b p h else 0 := by
    intro W _
    rw [lik_eq]
    by_cases h1 : seen h ⊆ W <;> by_cases h2 : j ∈ W <;> simp [h1, h2]
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, worlds_filter_subset_mem, nsmul_eq_mul, mul_comm]

/-- The transcript mass under the UNIFORM prior on `b`-subsets. -/
def mass (b : ℕ) (p : ℝ) (h : Transcript m N) : ℝ :=
  (∑ W ∈ worlds m b, lik b p W h) / (m.choose b : ℝ)

/-- The joint mass of "transcript `h`, and `j` is in fact unsafe" -- i.e. of the event that
declaring `j` safe on `h` is an ERROR. -/
def joint (b : ℕ) (p : ℝ) (h : Transcript m N) (j : Fin m) : ℝ :=
  (∑ W ∈ worlds m b, if j ∈ W then lik b p W h else 0) / (m.choose b : ℝ)

theorem mass_nonneg (b : ℕ) (p : ℝ) (hp : 0 ≤ p) (hbp : (b : ℝ) * p ≤ 1)
    (h : Transcript m N) : 0 ≤ mass b p h :=
  div_nonneg (Finset.sum_nonneg (fun W _ => lik_nonneg b p hp hbp W h))
    (by positivity)

theorem joint_nonneg (b : ℕ) (p : ℝ) (hp : 0 ≤ p) (hbp : (b : ℝ) * p ≤ 1)
    (h : Transcript m N) (j : Fin m) : 0 ≤ joint b p h j := by
  refine div_nonneg (Finset.sum_nonneg (fun W _ => ?_)) (by positivity)
  by_cases hj : j ∈ W
  · rw [if_pos hj]; exact lik_nonneg b p hp hbp W h
  · rw [if_neg hj]

/-! ## The two error masses -/

theorem admWith_eq_adm_of_mem (b : ℕ) (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S) :
    admWith b S j = adm b S := by
  classical
  ext W
  simp only [admWith, adm, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h2 hj⟩

/-- A SEEN label is unsafe on every consistent world, so declaring it safe is wrong with the
whole transcript mass. -/
theorem joint_eq_mass_of_seen (b : ℕ) (p : ℝ) (h : Transcript m N) (j : Fin m)
    (hj : j ∈ seen h) : joint b p h j = mass b p h := by
  rw [joint, mass, sum_lik_mem, sum_lik, admWith_eq_adm_of_mem b (seen h) j hj]

/-- THE TRANSPORT OF THE COUNTING IDENTITY onto the joint mass, denominators cleared. -/
theorem joint_mul_unseen (b : ℕ) (p : ℝ) (h : Transcript m N) (j : Fin m)
    (hj : j ∉ seen h) :
    joint b p h j * ((m - (seen h).card : ℕ) : ℝ)
      = mass b p h * ((b - (seen h).card : ℕ) : ℝ) := by
  classical
  have hcount := posterior_ratio (m := m) b (seen h) j hj
  have hc : ((seen h)ᶜ).card = m - (seen h).card := by
    rw [Finset.card_compl, Fintype.card_fin]
  rw [hc] at hcount
  have hR : ((m - (seen h).card : ℕ) : ℝ) * ((admWith b (seen h) j).card : ℝ)
      = ((adm b (seen h)).card : ℝ) * ((b - (seen h).card : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcount
  have key : likC b p h * ((admWith b (seen h) j).card : ℝ)
        * ((m - (seen h).card : ℕ) : ℝ)
      = likC b p h * ((adm b (seen h)).card : ℝ) * ((b - (seen h).card : ℕ) : ℝ) := by
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [mul_comm ((admWith b (seen h) j).card : ℝ)]
    exact hR
  rw [joint, mass, sum_lik_mem, sum_lik, div_mul_eq_mul_div, div_mul_eq_mul_div, key]

/-! ## The Bayes floor -/

/-- `L_N`, the unsafe tips still unseen. -/
def unseenUnsafe (b : ℕ) (h : Transcript m N) : ℕ := b - (seen h).card

/-- `L/(a+L)` with `a = m - b`. -/
def floorAt (m b : ℕ) (h : Transcript m N) : ℝ :=
  ((unseenUnsafe b h : ℕ) : ℝ) / (((m - b) + unseenUnsafe b h : ℕ) : ℝ)

/-- `(b-s)/(m-s)`, the form the counting identity produces. -/
def sFrac (m b : ℕ) (h : Transcript m N) : ℝ :=
  ((b - (seen h).card : ℕ) : ℝ) / ((m - (seen h).card : ℕ) : ℝ)

/-- `L/(a+L) = (b-s)/(m-s)`: the same number, in the two notations. -/
theorem floorAt_eq_sFrac (m b : ℕ) (hbm : b ≤ m) (h : Transcript m N) :
    floorAt m b h = sFrac m b h := by
  by_cases hs : (seen h).card ≤ b
  · unfold floorAt sFrac unseenUnsafe
    congr 1
    congr 1
    omega
  · have h0 : b - (seen h).card = 0 := by omega
    simp [floorAt, sFrac, unseenUnsafe, h0]

/-- THE PER-TRANSCRIPT FLOOR: declaring ANY label safe costs at least `mass * L/(a+L)`. -/
theorem joint_ge (b : ℕ) (p : ℝ) (hp : 0 ≤ p) (hbp : (b : ℝ) * p ≤ 1) (hbm : b ≤ m)
    (h : Transcript m N) (j : Fin m) :
    mass b p h * sFrac m b h ≤ joint b p h j := by
  classical
  have hm : (0:ℝ) ≤ mass b p h := mass_nonneg b p hp hbp h
  rcases Nat.eq_zero_or_pos (m - (seen h).card) with hz | hz
  · have : sFrac m b h = 0 := by simp [sFrac, hz]
    rw [this, mul_zero]
    exact joint_nonneg b p hp hbp h j
  have hpos : (0:ℝ) < ((m - (seen h).card : ℕ) : ℝ) := by
    exact_mod_cast hz
  by_cases hmem : j ∈ seen h
  · rw [joint_eq_mass_of_seen b p h j hmem]
    have h1 : sFrac m b h ≤ 1 := by
      rw [sFrac, div_le_one hpos]
      exact_mod_cast Nat.cast_le.mpr (by omega : b - (seen h).card ≤ m - (seen h).card)
    nlinarith
  · have key := joint_mul_unseen b p h j hmem
    rw [sFrac, mul_div_assoc', div_le_iff₀ hpos, key]

/-! ## Decoders, the lower bound, and attainment -/

/-- A randomised decoder declares one label safe. Nothing but `alpha >= 0` and
`sum_j alpha = 1` is assumed: no measurability, no structure, no symmetry. -/
structure Decoder (m N : ℕ) where
  alpha : Transcript m N → Fin m → ℝ
  nonneg : ∀ h j, 0 ≤ alpha h j
  sums : ∀ h, ∑ j, alpha h j = 1

/-- Bayes risk: the total joint mass of (transcript, wrong declaration). -/
def risk (b : ℕ) (p : ℝ) (D : Decoder m N) : ℝ :=
  ∑ h : Transcript m N, ∑ j, D.alpha h j * joint b p h j

/-- The Bayes value `E[L_N/(a+L_N)]`, as a finite expectation over transcripts. -/
def bayesValue (m b N : ℕ) (p : ℝ) : ℝ :=
  ∑ h : Transcript m N, mass b p h * floorAt m b h

/-- THE LOWER BOUND, over EVERY randomised decoder. -/
theorem risk_ge (b : ℕ) (p : ℝ) (hp : 0 ≤ p) (hbp : (b : ℝ) * p ≤ 1) (hbm : b ≤ m)
    (D : Decoder m N) : bayesValue m b N p ≤ risk b p D := by
  classical
  refine Finset.sum_le_sum (fun h _ => ?_)
  have hb : ∀ j, mass b p h * sFrac m b h ≤ joint b p h j :=
    fun j => joint_ge b p hp hbp hbm h j
  rw [floorAt_eq_sFrac m b hbm h]
  calc mass b p h * sFrac m b h
      = ∑ j, D.alpha h j * (mass b p h * sFrac m b h) := by
        rw [← Finset.sum_mul, D.sums h, one_mul]
    _ ≤ ∑ j, D.alpha h j * joint b p h j :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hb j) (D.nonneg h j))

/-- If more labels were seen than there are unsafe ones, no world is consistent. -/
theorem adm_eq_empty_of_lt (b : ℕ) (S : Finset (Fin m)) (hlt : b < S.card) :
    adm b S = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr (fun W hW => ?_)
  simp only [adm, Finset.mem_filter, Finset.mem_univ, true_and] at hW
  have := Finset.card_le_card hW.2
  omega

theorem mass_eq_zero_of_lt (b : ℕ) (p : ℝ) (h : Transcript m N)
    (hlt : b < (seen h).card) : mass b p h = 0 := by
  rw [mass, sum_lik, adm_eq_empty_of_lt b (seen h) hlt]
  simp

/-- The uniform-on-unseen decoder. The `seen h = univ` branch is a fallback that only fires
on transcripts of mass zero; `j0` exists because `b < m` forces `m > 0`. -/
def uuAlpha (j0 : Fin m) (h : Transcript m N) (j : Fin m) : ℝ :=
  if seen h = univ then (if j = j0 then 1 else 0)
  else (if j ∈ (seen h)ᶜ then (((seen h)ᶜ.card : ℝ))⁻¹ else 0)

theorem uuAlpha_nonneg (j0 : Fin m) (h : Transcript m N) (j : Fin m) :
    0 ≤ uuAlpha j0 h j := by
  unfold uuAlpha
  split
  · split <;> norm_num
  · split
    · positivity
    · norm_num

theorem uuAlpha_sums (j0 : Fin m) (h : Transcript m N) :
    ∑ j, uuAlpha j0 h j = 1 := by
  classical
  unfold uuAlpha
  by_cases hu : seen h = univ
  · simp [hu]
  · have hne : ((seen h)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      by_contra hc
      push_neg at hc
      have : m ≤ (seen h).card := by omega
      exact hu (Finset.eq_univ_of_card _ (le_antisymm
        (by simpa using Finset.card_le_univ (seen h)) (by simpa using this)))
    have hcpos : (0:ℝ) < (((seen h)ᶜ).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    simp only [hu, if_false]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    field_simp

def uniformUnseen (N : ℕ) (j0 : Fin m) : Decoder m N where
  alpha := uuAlpha j0
  nonneg := uuAlpha_nonneg j0
  sums := uuAlpha_sums j0

/-- ATTAINMENT. -/
theorem risk_uniformUnseen (b : ℕ) (p : ℝ) (hp : 0 ≤ p) (hbp : (b : ℝ) * p ≤ 1)
    (hbm : b < m) (j0 : Fin m) :
    risk b p (uniformUnseen N j0) = bayesValue m b N p := by
  classical
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [floorAt_eq_sFrac m b (le_of_lt hbm) h]
  by_cases hu : seen h = univ
  · have hlt : b < (seen h).card := by
      rw [hu, Finset.card_univ, Fintype.card_fin]; exact hbm
    have hm0 : mass b p h = 0 := mass_eq_zero_of_lt b p h hlt
    have hj0 : ∀ j, joint b p h j = 0 := by
      intro j
      rw [joint, sum_lik_mem]
      have : admWith b (seen h) j = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr (fun W hW => ?_)
        simp only [admWith, Finset.mem_filter, Finset.mem_univ, true_and] at hW
        have := Finset.card_le_card hW.2.1
        omega
      simp [this]
    simp [uniformUnseen, hj0, hm0]
  · have hne : ((seen h)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      by_contra hc
      push_neg at hc
      have hge : m ≤ (seen h).card := by omega
      exact hu (Finset.eq_univ_of_card _ (le_antisymm
        (by simpa using Finset.card_le_univ (seen h)) (by simpa using hge)))
    have hcard : ((seen h)ᶜ).card = m - (seen h).card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have hzpos : 0 < m - (seen h).card := by
      rw [← hcard]; exact Finset.card_pos.mpr hne
    have hpos : (0:ℝ) < ((m - (seen h).card : ℕ) : ℝ) := by exact_mod_cast hzpos
    have hterm : ∀ j ∈ ((seen h)ᶜ),
        joint b p h j = mass b p h * sFrac m b h := by
      intro j hjc
      have hj : j ∉ seen h := by simpa using hjc
      have key := joint_mul_unseen b p h j hj
      rw [sFrac, mul_div_assoc', eq_div_iff (ne_of_gt hpos)]
      exact key
    show ∑ j, uuAlpha j0 h j * joint b p h j = mass b p h * sFrac m b h
    unfold uuAlpha
    simp only [hu, if_false]
    rw [Finset.sum_congr rfl (fun j _ => by
        rw [ite_mul, zero_mul] :
      ∀ j ∈ (univ : Finset (Fin m)),
        (if j ∈ (seen h)ᶜ then (((seen h)ᶜ.card : ℝ))⁻¹ else 0) * joint b p h j
          = if j ∈ (seen h)ᶜ then (((seen h)ᶜ.card : ℝ))⁻¹ * joint b p h j else 0)]
    rw [Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_congr rfl (fun j hj => by rw [hterm j hj]),
      Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp

/-- THE BAYES VALUE: attained, and a lower bound over every randomised decoder. -/
theorem bayes_minimax (b : ℕ) (p : ℝ) (hp : 0 ≤ p) (hbp : (b : ℝ) * p ≤ 1)
    (hbm : b < m) (j0 : Fin m) :
    IsLeast {r : ℝ | ∃ D : Decoder m N, r = risk b p D} (bayesValue m b N p) := by
  constructor
  · exact ⟨uniformUnseen N j0, (risk_uniformUnseen b p hp hbp hbm j0).symm⟩
  · rintro r ⟨D, rfl⟩
    exact risk_ge b p hp hbp (le_of_lt hbm) D

/-! ## The law really is a law -/

theorem sum_draw (b : ℕ) (p : ℝ) (W : Finset (Fin m)) (hW : W.card = b) :
    ∑ o : Obs m, draw b p W o = 1 := by
  classical
  rw [Fintype.sum_option]
  have : ∑ j : Fin m, draw b p W (some j) = (b : ℝ) * p := by
    have : ∀ j : Fin m, draw b p W (some j) = if j ∈ W then p else 0 := fun j => rfl
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hW]
  rw [this]
  show (1 - (b:ℝ) * p) + (b:ℝ) * p = 1
  ring

theorem sum_lik_transcripts (b : ℕ) (p : ℝ) (W : Finset (Fin m)) (hW : W.card = b) :
    ∑ h : Transcript m N, lik b p W h = 1 := by
  classical
  have := Finset.sum_prod_piFinset (R := ℝ) (ι := Fin N) (univ : Finset (Obs m))
    (fun _ o => draw b p W o)
  rw [Fintype.piFinset_univ] at this
  rw [show (∑ h : Transcript m N, lik b p W h)
      = ∑ h ∈ (univ : Finset (Fin N → Obs m)), ∏ i, draw b p W (h i) from rfl, this]
  rw [Finset.prod_congr rfl (fun i _ => sum_draw b p W hW), Finset.prod_const, one_pow]

theorem sum_mass_eq_one (b : ℕ) (p : ℝ) (hbm : b ≤ m) :
    ∑ h : Transcript m N, mass b p h = 1 := by
  classical
  have hchoose : (0:ℝ) < (m.choose b : ℝ) := by
    exact_mod_cast Nat.choose_pos hbm
  unfold mass
  rw [← Finset.sum_div, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun W hW => sum_lik_transcripts b p W
      (by simpa [worlds] using hW))]
  rw [Finset.sum_const, worlds_card, nsmul_eq_mul, mul_one, div_self (ne_of_gt hchoose)]

/-! ## Equivariance: from the Bayes value to the MINIMAX value

Everything above is Bayes: the uniform prior is a hypothesis. The minimax value is
`min over decoders of max over worlds`, and the two agree once the optimal decoder's risk
is the SAME in every world. That is what this section proves, by relabelling. -/

/-- The risk of a decoder in a FIXED world: the chance it declares an unsafe label safe. -/
def worldRisk (b : ℕ) (p : ℝ) (W : Finset (Fin m)) (D : Decoder m N) : ℝ :=
  ∑ h : Transcript m N, lik b p W h * ∑ j ∈ W, D.alpha h j

theorem worldRisk_uu (b : ℕ) (p : ℝ) (W : Finset (Fin m)) (j0 : Fin m) :
    worldRisk b p W (uniformUnseen N j0)
      = ∑ h : Transcript m N, lik b p W h * ∑ j ∈ W, uuAlpha j0 h j := rfl

/-- The Bayes risk is the average of the world risks. -/
theorem risk_mul_choose (b : ℕ) (p : ℝ) (hbm : b ≤ m) (D : Decoder m N) :
    risk b p D * (m.choose b : ℝ) = ∑ W ∈ worlds m b, worldRisk b p W D := by
  classical
  have hC : ((m.choose b : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hbm).ne'
  have hterm : ∀ (h : Transcript m N) (j : Fin m),
      D.alpha h j * joint b p h j * (m.choose b : ℝ)
        = ∑ W ∈ worlds m b, (if j ∈ W then D.alpha h j * lik b p W h else 0) := by
    intro h j
    have hjc : joint b p h j * (m.choose b : ℝ)
        = ∑ W ∈ worlds m b, (if j ∈ W then lik b p W h else 0) := by
      rw [joint, div_mul_cancel₀ _ hC]
    calc D.alpha h j * joint b p h j * (m.choose b : ℝ)
        = D.alpha h j * (joint b p h j * (m.choose b : ℝ)) := by ring
      _ = D.alpha h j * ∑ W ∈ worlds m b, (if j ∈ W then lik b p W h else 0) := by
            rw [hjc]
      _ = ∑ W ∈ worlds m b, (if j ∈ W then D.alpha h j * lik b p W h else 0) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun W _ => by
              by_cases hjW : j ∈ W <;> simp [hjW])
  have hrow : ∀ h : Transcript m N,
      (∑ j, D.alpha h j * joint b p h j) * (m.choose b : ℝ)
        = ∑ W ∈ worlds m b, lik b p W h * ∑ j ∈ W, D.alpha h j := by
    intro h
    have h1 : (∑ j, D.alpha h j * joint b p h j) * (m.choose b : ℝ)
        = ∑ j : Fin m, ∑ W ∈ worlds m b,
            (if j ∈ W then D.alpha h j * lik b p W h else 0) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => hterm h j)
    have h2 : (∑ j : Fin m, ∑ W ∈ worlds m b,
          (if j ∈ W then D.alpha h j * lik b p W h else 0))
        = ∑ W ∈ worlds m b, ∑ j : Fin m,
            (if j ∈ W then D.alpha h j * lik b p W h else 0) := Finset.sum_comm
    have h3 : ∀ W : Finset (Fin m),
        (∑ j : Fin m, (if j ∈ W then D.alpha h j * lik b p W h else 0))
          = lik b p W h * ∑ j ∈ W, D.alpha h j := by
      intro W
      rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul, mul_comm]
    rw [h1, h2, Finset.sum_congr rfl (fun W _ => h3 W)]
  rw [risk, Finset.sum_mul, Finset.sum_congr rfl (fun h _ => hrow h)]
  simp only [worldRisk]
  exact Finset.sum_comm

/-- Relabelling a transcript by a permutation of the labels. -/
def relabel (σ : Equiv.Perm (Fin m)) (h : Transcript m N) : Transcript m N :=
  fun i => (h i).map σ

theorem relabel_left (σ : Equiv.Perm (Fin m)) (h : Transcript m N) :
    relabel σ.symm (relabel σ h) = h := by
  funext i
  cases hi : h i with
  | none => simp [relabel, hi]
  | some j => simp [relabel, hi]

theorem relabel_right (σ : Equiv.Perm (Fin m)) (h : Transcript m N) :
    relabel σ (relabel σ.symm h) = h := by
  funext i
  cases hi : h i with
  | none => simp [relabel, hi]
  | some j => simp [relabel, hi]

/-- Relabelling both the world and the transcript leaves the sampling law alone. -/
theorem draw_relabel (b : ℕ) (p : ℝ) (σ : Equiv.Perm (Fin m)) (W : Finset (Fin m))
    (o : Obs m) : draw b p (W.image σ) (o.map σ) = draw b p W o := by
  classical
  cases o with
  | none => rfl
  | some j =>
    have hiff : σ j ∈ W.image σ ↔ j ∈ W := by
      simp [Finset.mem_image, σ.injective.eq_iff]
    show (if σ j ∈ W.image σ then p else 0) = (if j ∈ W then p else 0)
    by_cases hj : j ∈ W
    · rw [if_pos (hiff.mpr hj), if_pos hj]
    · rw [if_neg (fun hc => hj (hiff.mp hc)), if_neg hj]

theorem lik_relabel (b : ℕ) (p : ℝ) (σ : Equiv.Perm (Fin m)) (W : Finset (Fin m))
    (h : Transcript m N) : lik b p (W.image σ) (relabel σ h) = lik b p W h :=
  Finset.prod_congr rfl (fun i _ => draw_relabel b p σ W (h i))

theorem seen_relabel (σ : Equiv.Perm (Fin m)) (h : Transcript m N) :
    seen (relabel σ h) = (seen h).image σ := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi⟩ := mem_seen.mp hj
    simp only [relabel] at hi
    rcases hx : h i with _ | j'
    · rw [hx] at hi; simp at hi
    · rw [hx] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      exact Finset.mem_image.mpr ⟨j', mem_seen.mpr ⟨i, hx⟩, hi⟩
  · intro hj
    obtain ⟨j', hj', hje⟩ := Finset.mem_image.mp hj
    obtain ⟨i, hi⟩ := mem_seen.mp hj'
    exact mem_seen.mpr ⟨i, by simp [relabel, hi, hje]⟩

theorem uuAlpha_relabel (j0 : Fin m) (σ : Equiv.Perm (Fin m)) (h : Transcript m N)
    (hne : seen h ≠ univ) (j : Fin m) :
    uuAlpha j0 (relabel σ h) (σ j) = uuAlpha j0 h j := by
  classical
  have hcard : (((seen h).image σ)).card = (seen h).card :=
    Finset.card_image_of_injective _ σ.injective
  have hs := seen_relabel (N := N) σ h
  have hne' : seen (relabel σ h) ≠ univ := by
    rw [hs]
    intro hc
    apply hne
    have h1 : ((seen h).image σ).card = m := by
      rw [hc, Finset.card_univ, Fintype.card_fin]
    rw [hcard] at h1
    exact Finset.eq_univ_of_card _ (by rw [h1, Fintype.card_fin])
  have hmem : (σ j ∈ ((seen h).image σ)ᶜ) ↔ (j ∈ (seen h)ᶜ) := by
    simp [Finset.mem_compl, Finset.mem_image, σ.injective.eq_iff]
  have hcc : (((seen h).image σ)ᶜ).card = ((seen h)ᶜ).card := by
    rw [Finset.card_compl, Finset.card_compl, hcard]
  unfold uuAlpha
  rw [if_neg hne', if_neg hne, hs]
  by_cases hj : j ∈ (seen h)ᶜ
  · rw [if_pos (hmem.mpr hj), if_pos hj, hcc]
  · rw [if_neg (fun hc => hj (hmem.mp hc)), if_neg hj]

/-- A transcript that exposed every label is impossible in a world of size `b < m`. -/
theorem lik_eq_zero_of_seen_univ (b : ℕ) (p : ℝ) (W : Finset (Fin m)) (hW : W.card = b)
    (hbm : b < m) (h : Transcript m N) (hu : seen h = univ) : lik b p W h = 0 := by
  classical
  rw [lik_eq, if_neg]
  intro hc
  rw [hu] at hc
  have hle : (univ : Finset (Fin m)).card ≤ W.card := Finset.card_le_card hc
  rw [Finset.card_univ, Fintype.card_fin, hW] at hle
  omega

/-- THE EQUIVARIANCE STEP: relabelling the world by `sigma` does not change the
uniform-unseen decoder's risk. -/
theorem worldRisk_uu_image (b : ℕ) (p : ℝ) (hbm : b < m) (j0 : Fin m)
    (σ : Equiv.Perm (Fin m)) (W : Finset (Fin m)) (hW : W.card = b) :
    worldRisk b p (W.image σ) (uniformUnseen N j0)
      = worldRisk b p W (uniformUnseen N j0) := by
  classical
  let e : Transcript m N ≃ Transcript m N :=
    { toFun := relabel σ, invFun := relabel σ.symm,
      left_inv := relabel_left σ, right_inv := relabel_right σ }
  have hre := Equiv.sum_comp e
    (fun h : Transcript m N =>
      lik b p (W.image σ) h * ∑ j ∈ W.image σ, uuAlpha j0 h j)
  have hpt : ∀ h : Transcript m N,
      lik b p (W.image σ) (relabel σ h)
          * (∑ j ∈ W.image σ, uuAlpha j0 (relabel σ h) j)
        = lik b p W h * ∑ j ∈ W, uuAlpha j0 h j := by
    intro h
    rw [lik_relabel, Finset.sum_image (fun x _ y _ hxy => σ.injective hxy)]
    by_cases hu : seen h = univ
    · rw [lik_eq_zero_of_seen_univ b p W hW hbm h hu, zero_mul, zero_mul]
    · exact congrArg _ (Finset.sum_congr rfl
        (fun j _ => uuAlpha_relabel j0 σ h hu j))
  rw [worldRisk_uu, worldRisk_uu, ← hre]
  exact Finset.sum_congr rfl (fun h _ => hpt h)

/-- A permutation of `Fin m` carrying `W` onto `W'` whenever they have the same size. -/
noncomputable def transport (W W' : Finset (Fin m)) (hc : W.card = W'.card) :
    Equiv.Perm (Fin m) :=
  ((Equiv.sumCompl (fun x : Fin m => x ∈ W)).symm.trans
    ((Fintype.equivOfCardEq (by simpa using hc)).sumCongr
      (Fintype.equivOfCardEq (by
        simp only [Fintype.card_subtype_compl, Fintype.card_coe, hc])))).trans
    (Equiv.sumCompl (fun x : Fin m => x ∈ W'))

theorem mem_of_subtype {W' : Finset (Fin m)} (v : {y : Fin m // y ∈ W'}) :
    (v : Fin m) ∈ W' := v.2

theorem notMem_of_subtype {W' : Finset (Fin m)} (v : {y : Fin m // y ∉ W'}) :
    (v : Fin m) ∉ W' := v.2

theorem transport_mem (W W' : Finset (Fin m)) (hc : W.card = W'.card) (x : Fin m) :
    (x ∈ W ↔ transport W W' hc x ∈ W') := by
  classical
  by_cases hx : x ∈ W
  · have h1 : (Equiv.sumCompl (fun y : Fin m => y ∈ W)).symm x = Sum.inl ⟨x, hx⟩ := by
      rw [Equiv.symm_apply_eq, Equiv.sumCompl_apply_inl]
    simp only [transport, Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    exact iff_of_true hx (mem_of_subtype _)
  · have h1 : (Equiv.sumCompl (fun y : Fin m => y ∈ W)).symm x = Sum.inr ⟨x, hx⟩ := by
      rw [Equiv.symm_apply_eq, Equiv.sumCompl_apply_inr]
    simp only [transport, Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    exact iff_of_false hx (notMem_of_subtype _)

theorem image_transport (W W' : Finset (Fin m)) (hc : W.card = W'.card) :
    W.image (transport W W' hc) = W' := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    exact hxy ▸ (transport_mem W W' hc x).mp hx
  · rw [Finset.card_image_of_injective _ (transport W W' hc).injective, hc]

/-- THE CONSTANT RISK: the uniform-unseen decoder has the same risk in EVERY world. -/
theorem worldRisk_uu_const (b : ℕ) (p : ℝ) (hbm : b < m) (j0 : Fin m)
    (W W' : Finset (Fin m)) (hW : W.card = b) (hW' : W'.card = b) :
    worldRisk b p W (uniformUnseen N j0)
      = worldRisk b p W' (uniformUnseen N j0) := by
  have hc : W.card = W'.card := by rw [hW, hW']
  rw [← image_transport W W' hc]
  exact (worldRisk_uu_image b p hbm j0 (transport W W' hc) W hW).symm

/-- THE PASSIVE MINIMAX VALUE. `bayesValue` is the least achievable worst-case-over-worlds
risk: the uniform-unseen decoder attains it, and no randomised decoder beats it. -/
theorem passive_minimax (b : ℕ) (p : ℝ) (hp : 0 ≤ p) (hbp : (b : ℝ) * p ≤ 1)
    (hbm : b < m) (j0 : Fin m) (hne : (worlds m b).Nonempty) :
    IsLeast {r : ℝ | ∃ D : Decoder m N,
        r = (worlds m b).sup' hne (fun W => worldRisk b p W D)}
      (bayesValue m b N p) := by
  classical
  have hble : b ≤ m := le_of_lt hbm
  have hCpos : (0:ℝ) < (m.choose b : ℝ) := by exact_mod_cast Nat.choose_pos hble
  obtain ⟨W0, hW0⟩ := id hne
  have hW0c : W0.card = b := by simpa [worlds] using hW0
  constructor
  · refine ⟨uniformUnseen N j0, ?_⟩
    have hconst : ∀ W ∈ worlds m b,
        worldRisk b p W (uniformUnseen N j0)
          = worldRisk b p W0 (uniformUnseen N j0) := fun W hW =>
      worldRisk_uu_const b p hbm j0 W W0 (by simpa [worlds] using hW) hW0c
    have hsup : (worlds m b).sup' hne (fun W => worldRisk b p W (uniformUnseen N j0))
        = worldRisk b p W0 (uniformUnseen N j0) :=
      Finset.sup'_eq_of_forall hne _ hconst
    have havg := risk_mul_choose b p hble (uniformUnseen N j0)
    have hsum : ∑ W ∈ worlds m b, worldRisk b p W (uniformUnseen N j0)
        = worldRisk b p W0 (uniformUnseen N j0) * (m.choose b : ℝ) := by
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, worlds_card,
        mul_comm]
    have h2 := mul_right_cancel₀ (ne_of_gt hCpos) (havg.trans hsum)
    rw [hsup, ← h2, risk_uniformUnseen b p hp hbp hbm j0]
  · rintro r ⟨D, rfl⟩
    have hb := risk_ge b p hp hbp hble D
    have havg := risk_mul_choose b p hble D
    have hle : ∑ W ∈ worlds m b, worldRisk b p W D
        ≤ (worlds m b).sup' hne (fun W => worldRisk b p W D) * ((worlds m b).card : ℝ) := by
      calc ∑ W ∈ worlds m b, worldRisk b p W D
          ≤ ∑ _W ∈ worlds m b, (worlds m b).sup' hne (fun W => worldRisk b p W D) :=
            Finset.sum_le_sum (fun W hW =>
              Finset.le_sup' (fun W => worldRisk b p W D) hW)
        _ = (worlds m b).sup' hne (fun W => worldRisk b p W D)
              * ((worlds m b).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [worlds_card] at hle
    rw [← havg] at hle
    exact le_trans hb (le_of_mul_le_mul_right hle hCpos)

#print axioms mem_seen
#print axioms count_add
#print axioms lik_eq
#print axioms lik_nonneg
#print axioms worlds_card
#print axioms sum_lik
#print axioms sum_lik_mem
#print axioms joint_eq_mass_of_seen
#print axioms joint_mul_unseen
#print axioms floorAt_eq_sFrac
#print axioms joint_ge
#print axioms risk_ge
#print axioms adm_eq_empty_of_lt
#print axioms mass_eq_zero_of_lt
#print axioms uuAlpha_sums
#print axioms risk_uniformUnseen
#print axioms bayes_minimax
#print axioms sum_draw
#print axioms sum_lik_transcripts
#print axioms sum_mass_eq_one
#print axioms risk_mul_choose
#print axioms lik_relabel
#print axioms seen_relabel
#print axioms uuAlpha_relabel
#print axioms worldRisk_uu_image
#print axioms transport_mem
#print axioms image_transport
#print axioms worldRisk_uu_const
#print axioms passive_minimax

end
end CIGAMF.P13.SupportBayesMinimax
