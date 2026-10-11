import «LeanPaperARPairV1»

/-!
# Paper A, A-R: the two information games, as games

`rpair_theta` pinned the ratio `Gtrue / Gproxy` but took `hlo`, `hhi`, `hproxy` as
hypotheses: the two values were inputs, so the theorem was arithmetic about two numbers,
not a statement about two games.

Here the objects are defined and the numbers are derived.  There is one concrete world
`theta0`, one alternative set (the worlds whose answer differs), two optimised games

    trueGame  = sup over allocations of inf over ALL alternatives,
    proxyGame = sup over allocations of inf over the alternatives the frozen surrogate
                can see at all -- those that move an anchor and leave the pairs alone,

and four bounds proved about them, with no value assumed.
-/

namespace CIGAMF.P13.ARGames

open Finset
open CIGAMF.P13.PaperARPair

variable {r : ℕ}

/-! ## The world -/

/-- The true world: arm `A`'s anchors a unit apart, all of arm `B` at zero. -/
noncomputable def theta0 (r : ℕ) : Cell r → ℝ :=
  Sum.elim (![-(1/2), 1/2, 0, 0] : Fin 4 → ℝ) (fun _ => 0)

theorem theta0_inl0 (r : ℕ) : theta0 r (Sum.inl 0) = -(1/2) := by simp [theta0]
theorem theta0_inl1 (r : ℕ) : theta0 r (Sum.inl 1) = 1/2 := by simp [theta0]

theorem theta0_inl2 (r : ℕ) : theta0 r (Sum.inl 2) = 0 := by simp [theta0]
theorem theta0_inl3 (r : ℕ) : theta0 r (Sum.inl 3) = 0 := by simp [theta0]
theorem theta0_pair (r : ℕ) (p : Fin r × Bool) : theta0 r (Sum.inr p) = 0 := rfl

/-- **The world is centred**, so `centered_additive_response` applies and the `energy`
the games optimise is the information the queries carry rather than a stand-in for it.
Arm `A` is the two anchors `inl 0, inl 1`; arm `B` is `inl 2, inl 3` and all the pairs. -/
theorem theta0_centered (r : ℕ) :
    theta0 r (Sum.inl 0) + theta0 r (Sum.inl 1) = 0
      ∧ theta0 r (Sum.inl 2) + theta0 r (Sum.inl 3)
          + ∑ p : Fin r × Bool, theta0 r (Sum.inr p) = 0 := by
  refine ⟨by rw [theta0_inl0, theta0_inl1]; ring, ?_⟩
  rw [theta0_inl2, theta0_inl3]
  have : ∑ _p : Fin r × Bool, theta0 r (Sum.inr _p) = 0 := by
    refine Finset.sum_eq_zero (fun p _ => theta0_pair r p)
  rw [this]; ring

theorem theta0_gap (r : ℕ) : theta0 r (Sum.inl 1) - theta0 r (Sum.inl 0) = 1 := by
  rw [theta0_inl0, theta0_inl1]; norm_num

theorem bAnchor3_mem (r : ℕ) : (Sum.inl 3 : Cell r) ∈ BCells r := by
  rw [BCells, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, rfl⟩

theorem theta0_B (r : ℕ) (e : Cell r) (he : e ∈ BCells r) : theta0 r e = 0 := by
  classical
  rcases e with a | p
  · have h : isBCell (Sum.inl a : Cell r) = true := (Finset.mem_filter.mp he).2
    simp only [isBCell, Sum.elim_inl, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | rfl
    · exact theta0_inl2 r
    · exact theta0_inl3 r
  · exact theta0_pair r p

theorem theta0_hB (r : ℕ) :
    ∀ e ∈ BCells r, ∀ e' ∈ BCells r, theta0 r e - theta0 r e' ≤ 3 / 4 := by
  intro e he e' he'
  rw [theta0_B r e he, theta0_B r e' he']
  norm_num

/-! ## The alternatives, and that there are some -/

/-- The alternatives: the worlds on which the answer is not `A`. -/
def AltSet (r : ℕ) : Set (Cell r → ℝ) := {lam | rangeA lam < rangeB lam}

/-- The surrogate has frozen the pair cells, so the only worlds it can separate from
`theta0` at all are those that move an anchor. -/
def ProxyAlt (r : ℕ) : Set (Cell r → ℝ) :=
  {lam | (∀ p : Fin r × Bool, lam (Sum.inr p) = 0) ∧ rangeA lam < rangeB lam}

/-- A witness alternative, so neither set is empty and neither infimum is junk. -/
noncomputable def lamW (r : ℕ) : Cell r → ℝ :=
  Sum.elim (![0, 1, 2, 0] : Fin 4 → ℝ) (fun _ => 0)

theorem lamW_proxy (r : ℕ) : lamW r ∈ ProxyAlt r := by
  have h0 : lamW r (Sum.inl 0) = 0 := by simp [lamW]
  have h1 : lamW r (Sum.inl 1) = 1 := by simp [lamW]
  have h2 : lamW r (Sum.inl 2) = 2 := by simp [lamW]
  have h3 : lamW r (Sum.inl 3) = 0 := by simp [lamW]
  refine ⟨fun p => rfl, ?_⟩
  have hA : rangeA (lamW r) = 1 := by
    unfold rangeA; rw [h0, h1]; norm_num
  have hsup : (2 : ℝ) ≤ (BCells r).sup' (BCells_nonempty r) (lamW r) := by
    have := Finset.le_sup' (lamW r) (bAnchor_mem r); rwa [h2] at this
  have hinf : (BCells r).inf' (BCells_nonempty r) (lamW r) ≤ 0 := by
    have := Finset.inf'_le (lamW r) (bAnchor3_mem r); rwa [h3] at this
  show rangeA (lamW r) < rangeB (lamW r)
  unfold rangeB; rw [hA]; linarith

theorem lamW_alt (r : ℕ) : lamW r ∈ AltSet r := (lamW_proxy r).2

instance instNonemptyAlt (r : ℕ) : Nonempty (AltSet r) := ⟨⟨lamW r, lamW_alt r⟩⟩
instance instNonemptyProxyAlt (r : ℕ) : Nonempty (ProxyAlt r) := ⟨⟨lamW r, lamW_proxy r⟩⟩

/-! ## Allocations -/

noncomputable def wUnif (r : ℕ) : Cell r → ℝ := Sum.elim (fun _ => 1 / 4) (fun _ => 0)

theorem wUnif_isAlloc (r : ℕ) : IsAlloc (wUnif r) := by
  constructor
  · intro e; cases e <;> norm_num [wUnif]
  · have hs : ∑ e : Cell r, wUnif r e
        = (∑ _a : Fin 4, (1 : ℝ) / 4) + ∑ _p : Fin r × Bool, (0 : ℝ) :=
      Fintype.sum_sum_type _
    rw [hs, Finset.sum_const, Finset.sum_const_zero, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, add_zero]
    norm_num

instance instNonemptyAlloc (r : ℕ) : Nonempty {w : Cell r → ℝ // IsAlloc w} :=
  ⟨⟨wUnif r, wUnif_isAlloc r⟩⟩

theorem pairVar_pos (M : ℝ) (hM : 0 < M) (e : Cell r) : 0 < pairVar M e := by
  cases e with
  | inl a => show (0 : ℝ) < 1; norm_num
  | inr p => exact hM

theorem energy_nonneg (M : ℝ) (hM : 0 < M) (w θ lam : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ energy w (pairVar M) θ lam := by
  unfold energy
  have h : 0 ≤ ∑ e, w e * (lam e - θ e) ^ 2 / pairVar M e :=
    Finset.sum_nonneg (fun e _ =>
      div_nonneg (mul_nonneg (hw e) (sq_nonneg _)) (pairVar_pos M hM e).le)
  linarith

/-! ## The two games -/

noncomputable def designValue (M : ℝ) (w : Cell r → ℝ) : ℝ :=
  ⨅ lam : AltSet r, energy w (pairVar M) (theta0 r) (lam : Cell r → ℝ)

noncomputable def trueGame (r : ℕ) (M : ℝ) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, designValue M (w : Cell r → ℝ)

noncomputable def proxyValue (M : ℝ) (w : Cell r → ℝ) : ℝ :=
  ⨅ lam : ProxyAlt r, energy w (pairVar M) (theta0 r) (lam : Cell r → ℝ)

noncomputable def proxyGame (r : ℕ) (M : ℝ) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, proxyValue M (w : Cell r → ℝ)

theorem bddBelow_alt (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (Set.range (fun lam : AltSet r =>
      energy w (pairVar M) (theta0 r) (lam : Cell r → ℝ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨lam, rfl⟩
  exact energy_nonneg M hM w _ _ hw

theorem bddBelow_proxy (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : ∀ e, 0 ≤ w e) :
    BddBelow (Set.range (fun lam : ProxyAlt r =>
      energy w (pairVar M) (theta0 r) (lam : Cell r → ℝ))) := by
  refine ⟨0, ?_⟩
  rintro x ⟨lam, rfl⟩
  exact energy_nonneg M hM w _ _ hw

/-! ## The true game: upper bound -/

theorem pairShift_mem_alt (r : ℕ) (j : Fin r) (d : ℝ) (hd : 1 / 2 < d) :
    pairShift (theta0 r) j d ∈ AltSet r := by
  have hA : rangeA (pairShift (theta0 r) j d) = 1 := by
    unfold rangeA
    rw [pairShift_rest (theta0 r) j d (Sum.inl 1) (by simp) (by simp),
        pairShift_rest (theta0 r) j d (Sum.inl 0) (by simp) (by simp),
        theta0_inl1, theta0_inl0]
    norm_num
  have ht : pairShift (theta0 r) j d (Sum.inr (j, true)) = d := by
    have h := pairShift_true (theta0 r) j d
    rw [theta0_pair] at h; linarith
  have hf : pairShift (theta0 r) j d (Sum.inr (j, false)) = -d := by
    have h := pairShift_false (theta0 r) j d
    rw [theta0_pair] at h; linarith
  have hsup : d ≤ (BCells r).sup' (BCells_nonempty r) (pairShift (theta0 r) j d) := by
    have := Finset.le_sup' (pairShift (theta0 r) j d) (bPair_mem r j true)
    rwa [ht] at this
  have hinf : (BCells r).inf' (BCells_nonempty r) (pairShift (theta0 r) j d) ≤ -d := by
    have := Finset.inf'_le (pairShift (theta0 r) j d) (bPair_mem r j false)
    rwa [hf] at this
  show rangeA (pairShift (theta0 r) j d) < rangeB (pairShift (theta0 r) j d)
  unfold rangeB; rw [hA]; linarith

theorem designValue_le (M : ℝ) (hM : 0 < M) (hr : 0 < r)
    (w : Cell r → ℝ) (hw : IsAlloc w) (d : ℝ) (hd : 1 / 2 < d) :
    designValue M w ≤ d ^ 2 / (2 * M * (r : ℝ)) := by
  obtain ⟨j, hj⟩ := light_pair_energy_le w (pairVar M) (theta0 r) hw hr M hM
    (fun j b => rfl) d (by linarith)
  exact le_trans (ciInf_le (bddBelow_alt M hM w hw.1)
    (⟨pairShift (theta0 r) j d, pairShift_mem_alt r j d hd⟩ : AltSet r)) hj

theorem trueGame_le_of (M : ℝ) (hM : 0 < M) (hr : 0 < r) (d : ℝ) (hd : 1 / 2 < d) :
    trueGame r M ≤ d ^ 2 / (2 * M * (r : ℝ)) :=
  ciSup_le (fun w => designValue_le M hM hr (w : Cell r → ℝ) w.2 d hd)

/-- **The true game is at most `1/(8Mr)`**, now about the game and not about a number. -/
theorem trueGame_le (M : ℝ) (hM : 0 < M) (hr : 0 < r) :
    trueGame r M ≤ 1 / (8 * M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hZ : (0 : ℝ) < 2 * M * (r : ℝ) := by positivity
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hmpos : 0 < min 1 (2 * M * (r : ℝ) * ε) := lt_min one_pos (by positivity)
  set δ := min 1 (2 * M * (r : ℝ) * ε) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδhalf : δ ≤ 1 / 2 := by
    have h1 : min 1 (2 * M * (r : ℝ) * ε) ≤ 1 := min_le_left _ _
    rw [hδdef]; linarith
  have h1 := trueGame_le_of M hM hr (1 / 2 + δ) (by linarith)
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hmin : min 1 (2 * M * (r : ℝ) * ε) ≤ 2 * M * (r : ℝ) * ε := min_le_right _ _
  have htwo : 2 * δ = min 1 (2 * M * (r : ℝ) * ε) := by rw [hδdef]; ring
  have h2δ : δ + δ ^ 2 ≤ 2 * M * (r : ℝ) * ε := by linarith
  have hkey : (1 / 2 + δ) ^ 2 / (2 * M * (r : ℝ)) ≤ 1 / (8 * M * (r : ℝ)) + ε := by
    rw [div_le_iff₀ hZ]
    have hrhs : (1 / (8 * M * (r : ℝ)) + ε) * (2 * M * (r : ℝ))
        = 1 / 4 + 2 * M * (r : ℝ) * ε := by field_simp; ring
    rw [hrhs]
    nlinarith [h2δ]
  linarith

theorem bddAbove_true (M : ℝ) (hM : 0 < M) (hr : 0 < r) :
    BddAbove (Set.range (fun w : {w : Cell r → ℝ // IsAlloc w} =>
      designValue M (w : Cell r → ℝ))) := by
  refine ⟨1 / (2 * M * (r : ℝ)), ?_⟩
  rintro x ⟨w, rfl⟩
  have h := designValue_le M hM hr (w : Cell r → ℝ) w.2 1 (by norm_num)
  simpa using h

/-! ## The true game: lower bound -/

/-- **The true game is at least `1/(128(4+2rM))`.** -/
theorem trueGame_ge (M : ℝ) (hM : 0 < M) (hr : 0 < r) :
    1 / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueGame r M := by
  have hanchor : 1 / (128 * (4 + 2 * (r : ℝ) * M))
      ≤ designValue M (anchorDesign r M) := by
    refine le_ciInf (fun lam => ?_)
    exact rpair_true_ge r M hM (theta0 r) (lam : Cell r → ℝ) (theta0_gap r)
      (theta0_hB r) lam.2
  exact le_trans hanchor
    (le_ciSup (bddAbove_true M hM hr) (⟨anchorDesign r M, anchorDesign_isAlloc r M hM⟩))

/-! ## The proxy game -/

noncomputable def anchorBump (r : ℕ) (a : Fin 4) (δ : ℝ) : Cell r → ℝ :=
  fun e => if e = Sum.inl a then theta0 r e + δ else theta0 r e

theorem anchorBump_mem (r : ℕ) (a b : Fin 4)
    (ha : (Sum.inl a : Cell r) ∈ BCells r) (hb : (Sum.inl b : Cell r) ∈ BCells r)
    (hab : a ≠ b) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (δ : ℝ) (hδ : 1 < δ) :
    anchorBump r a δ ∈ ProxyAlt r := by
  have hta : theta0 r (Sum.inl a) = 0 := theta0_B r _ ha
  have htb : theta0 r (Sum.inl b) = 0 := theta0_B r _ hb
  have hva : anchorBump r a δ (Sum.inl a) = δ := by
    unfold anchorBump; rw [if_pos rfl, hta]; ring
  have hvb : anchorBump r a δ (Sum.inl b) = 0 := by
    unfold anchorBump
    rw [if_neg (fun h => hab (Sum.inl.inj h).symm), htb]
  have hv1 : anchorBump r a δ (Sum.inl 1) = 1/2 := by
    unfold anchorBump
    rw [if_neg (fun h => ha1 (Sum.inl.inj h).symm), theta0_inl1]
  have hv0 : anchorBump r a δ (Sum.inl 0) = -(1/2) := by
    unfold anchorBump
    rw [if_neg (fun h => ha0 (Sum.inl.inj h).symm), theta0_inl0]
  refine ⟨fun p => ?_, ?_⟩
  · unfold anchorBump; rw [if_neg (by simp), theta0_pair]
  · have hA : rangeA (anchorBump r a δ) = 1 := by
      unfold rangeA; rw [hv1, hv0]; norm_num
    have hsup : δ ≤ (BCells r).sup' (BCells_nonempty r) (anchorBump r a δ) := by
      have := Finset.le_sup' (anchorBump r a δ) ha; rwa [hva] at this
    have hinf : (BCells r).inf' (BCells_nonempty r) (anchorBump r a δ) ≤ 0 := by
      have := Finset.inf'_le (anchorBump r a δ) hb; rwa [hvb] at this
    show rangeA (anchorBump r a δ) < rangeB (anchorBump r a δ)
    unfold rangeB; rw [hA]; linarith

theorem energy_anchorBump (M : ℝ) (w : Cell r → ℝ) (a : Fin 4) (δ : ℝ) :
    energy w (pairVar M) (theta0 r) (anchorBump r a δ) = w (Sum.inl a) * δ ^ 2 / 2 := by
  classical
  have hsum : ∑ e : Cell r, w e * (anchorBump r a δ e - theta0 r e) ^ 2 / pairVar M e
      = w (Sum.inl a) * δ ^ 2 := by
    rw [Finset.sum_eq_single (Sum.inl a : Cell r)]
    · have h1 : anchorBump r a δ (Sum.inl a) - theta0 r (Sum.inl a) = δ := by
        unfold anchorBump; rw [if_pos rfl]; ring
      rw [h1]; simp [pairVar]
    · intro e _ hne
      have h0 : anchorBump r a δ e - theta0 r e = 0 := by
        unfold anchorBump; rw [if_neg hne]; ring
      rw [h0]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold energy; rw [hsum]

/-- **The proxy game is at most `1`.**  Whatever the design, one of arm `B`'s two anchors
carries at most half the weight, and bumping that one already flips the answer. -/
theorem proxyValue_le (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAlloc w) :
    proxyValue M w ≤ 1 := by
  classical
  have hne23 : (Sum.inl 2 : Cell r) ≠ Sum.inl 3 := fun h => by
    exact absurd (Sum.inl.inj h) (by decide)
  have hsum2 : w (Sum.inl 2) + w (Sum.inl 3) ≤ 1 := by
    have hsub : ({Sum.inl 2, Sum.inl 3} : Finset (Cell r)) ⊆ univ := Finset.subset_univ _
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hw.1 e)
    rw [Finset.sum_pair hne23, hw.2] at h
    exact h
  have key : ∀ a b : Fin 4, (Sum.inl a : Cell r) ∈ BCells r →
      (Sum.inl b : Cell r) ∈ BCells r → a ≠ b → a ≠ 0 → a ≠ 1 →
      w (Sum.inl a) ≤ 1 / 2 → proxyValue M w ≤ 1 := by
    intro a b ha hb hab ha0 ha1 hwa
    have hmem := anchorBump_mem r a b ha hb hab ha0 ha1 2 (by norm_num)
    have hle : proxyValue M w ≤ energy w (pairVar M) (theta0 r) (anchorBump r a 2) :=
      ciInf_le (bddBelow_proxy M hM w hw.1) (⟨anchorBump r a 2, hmem⟩ : ProxyAlt r)
    rw [energy_anchorBump] at hle
    have : w (Sum.inl a) * (2 : ℝ) ^ 2 / 2 = 2 * w (Sum.inl a) := by ring
    rw [this] at hle
    linarith
  rcases le_total (w (Sum.inl 2)) (w (Sum.inl 3)) with h | h
  · exact key 2 3 (bAnchor_mem r) (bAnchor3_mem r) (by decide) (by decide) (by decide)
      (by linarith [hw.1 (Sum.inl 3)])
  · exact key 3 2 (bAnchor3_mem r) (bAnchor_mem r) (by decide) (by decide) (by decide)
      (by linarith [hw.1 (Sum.inl 2)])

theorem four_sq_ge (x₀ x₁ x₂ x₃ : ℝ) :
    (|x₀| + |x₁| + |x₂| + |x₃|) ^ 2 ≤ 4 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) := by
  have e0 := sq_abs x₀
  have e1 := sq_abs x₁
  have e2 := sq_abs x₂
  have e3 := sq_abs x₃
  nlinarith [sq_nonneg (|x₀| - |x₁|), sq_nonneg (|x₀| - |x₂|), sq_nonneg (|x₀| - |x₃|),
    sq_nonneg (|x₁| - |x₂|), sq_nonneg (|x₁| - |x₃|), sq_nonneg (|x₂| - |x₃|)]

set_option maxHeartbeats 1000000 in
/-- **The proxy game is at least `1/128`**, a constant: it does not decay with `r` or `M`,
because the surrogate's alternatives never touch the pair cells where the true game's
cheap alternatives live. -/
theorem proxyValue_unif_ge (M : ℝ) (hM : 0 < M) :
    1 / 128 ≤ proxyValue M (wUnif r) := by
  classical
  refine le_ciInf (fun lam => ?_)
  obtain ⟨hpair, hstrict⟩ := lam.2
  set L : Cell r → ℝ := (lam : Cell r → ℝ) with hLdef
  -- the energy at the uniform-anchor design is the anchors' squared displacement / 8
  have hE : energy (wUnif r) (pairVar M) (theta0 r) L
      = ((L (Sum.inl 0) - theta0 r (Sum.inl 0)) ^ 2
        + (L (Sum.inl 1) - theta0 r (Sum.inl 1)) ^ 2
        + (L (Sum.inl 2) - theta0 r (Sum.inl 2)) ^ 2
        + (L (Sum.inl 3) - theta0 r (Sum.inl 3)) ^ 2) / 8 := by
    unfold energy
    have hsplit : ∑ e : Cell r, wUnif r e * (L e - theta0 r e) ^ 2 / pairVar M e
        = (∑ a : Fin 4, wUnif r (Sum.inl a) * (L (Sum.inl a) - theta0 r (Sum.inl a)) ^ 2
            / pairVar M (Sum.inl a))
          + ∑ p : Fin r × Bool,
              wUnif r (Sum.inr p) * (L (Sum.inr p) - theta0 r (Sum.inr p)) ^ 2
                / pairVar M (Sum.inr p) := Fintype.sum_sum_type _
    have hzero : ∀ p : Fin r × Bool,
        wUnif r (Sum.inr p) * (L (Sum.inr p) - theta0 r (Sum.inr p)) ^ 2
          / pairVar M (Sum.inr p) = 0 := by
      intro p
      have hw : wUnif r (Sum.inr p) = 0 := rfl
      rw [hw, zero_mul, zero_div]
    have hanch : ∀ a : Fin 4,
        wUnif r (Sum.inl a) * (L (Sum.inl a) - theta0 r (Sum.inl a)) ^ 2
          / pairVar (r := r) M (Sum.inl a)
          = (L (Sum.inl a) - theta0 r (Sum.inl a)) ^ 2 / 4 := by
      intro a
      have hw : wUnif r (Sum.inl a) = 1 / 4 := rfl
      have hv : pairVar (r := r) M (Sum.inl a) = 1 := rfl
      rw [hw, hv]; ring
    rw [hsplit, Finset.sum_congr rfl (fun p _ => hzero p),
        Finset.sum_congr rfl (fun a _ => hanch a), Finset.sum_const_zero, add_zero,
        Fin.sum_univ_four]
    ring
  set d0 := L (Sum.inl 0) - theta0 r (Sum.inl 0) with hd0
  set d1 := L (Sum.inl 1) - theta0 r (Sum.inl 1) with hd1
  set d2 := L (Sum.inl 2) - theta0 r (Sum.inl 2) with hd2
  set d3 := L (Sum.inl 3) - theta0 r (Sum.inl 3) with hd3
  have hL0 : L (Sum.inl 0) = -(1/2) + d0 := by rw [hd0, theta0_inl0]; ring
  have hL1 : L (Sum.inl 1) = 1/2 + d1 := by rw [hd1, theta0_inl1]; ring
  have hL2 : L (Sum.inl 2) = d2 := by rw [hd2, theta0_inl2]; ring
  have hL3 : L (Sum.inl 3) = d3 := by rw [hd3, theta0_inl3]; ring
  -- arm A's range is unmoved to first order; arm B's is controlled by the two anchors
  have hA : rangeA L = |1 + d1 - d0| := by
    unfold rangeA; rw [hL0, hL1]; congr 1; ring
  have hrangeA : 1 - |d0| - |d1| ≤ rangeA L := by
    rw [hA]
    have h1 : 1 + d1 - d0 ≤ |1 + d1 - d0| := le_abs_self _
    have h2 : -|d1| ≤ d1 := neg_abs_le d1
    have h4 : d0 ≤ |d0| := le_abs_self d0
    linarith
  have ha2 : d2 ≤ |d2| + |d3| := by linarith [le_abs_self d2, abs_nonneg d3]
  have ha3 : d3 ≤ |d2| + |d3| := by linarith [le_abs_self d3, abs_nonneg d2]
  have ha0 : (0 : ℝ) ≤ |d2| + |d3| := by linarith [abs_nonneg d2, abs_nonneg d3]
  have hb2 : -(|d2| + |d3|) ≤ d2 := by linarith [neg_abs_le d2, abs_nonneg d3]
  have hb3 : -(|d2| + |d3|) ≤ d3 := by linarith [neg_abs_le d3, abs_nonneg d2]
  have hb0 : -(|d2| + |d3|) ≤ (0 : ℝ) := by linarith [abs_nonneg d2, abs_nonneg d3]
  have hBval : ∀ e ∈ BCells r,
      L e ≤ max d2 (max d3 0) ∧ min d2 (min d3 0) ≤ L e := by
    intro e he
    rcases e with a | p
    · have h : isBCell (Sum.inl a : Cell r) = true := (Finset.mem_filter.mp he).2
      simp only [isBCell, Sum.elim_inl, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with rfl | rfl
      · rw [hL2]; exact ⟨le_max_left _ _, min_le_left _ _⟩
      · rw [hL3]
        exact ⟨le_trans (le_max_left _ _) (le_max_right _ _),
          le_trans (min_le_right _ _) (min_le_left _ _)⟩
    · rw [hpair p]
      exact ⟨le_trans (le_max_right _ _) (le_max_right _ _),
        le_trans (min_le_right _ _) (min_le_right _ _)⟩
  have hsup : (BCells r).sup' (BCells_nonempty r) L ≤ max d2 (max d3 0) := by
    refine Finset.sup'_le _ _ ?_
    intro e he
    exact (hBval e he).1
  have hinf : min d2 (min d3 0) ≤ (BCells r).inf' (BCells_nonempty r) L := by
    refine Finset.le_inf' _ _ ?_
    intro e he
    exact (hBval e he).2
  have hPle : max d2 (max d3 0) ≤ |d2| + |d3| := max_le ha2 (max_le ha3 ha0)
  have hQge : -(|d2| + |d3|) ≤ min d2 (min d3 0) := le_min hb2 (le_min hb3 hb0)
  have hrangeB : rangeB L ≤ 2 * (|d2| + |d3|) := by
    unfold rangeB; linarith
  have habs : 1 / 2 < |d0| + |d1| + |d2| + |d3| := by
    linarith [hstrict, hrangeA, hrangeB, abs_nonneg d0, abs_nonneg d1]
  have hS : (0 : ℝ) ≤ |d0| + |d1| + |d2| + |d3| := by
    linarith [abs_nonneg d0, abs_nonneg d1, abs_nonneg d2, abs_nonneg d3]
  have hSq : (1 : ℝ) / 4 < (|d0| + |d1| + |d2| + |d3|) ^ 2 := by nlinarith [habs, hS]
  have h4 := four_sq_ge d0 d1 d2 d3
  rw [hE]
  linarith

theorem bddAbove_proxy (M : ℝ) (hM : 0 < M) :
    BddAbove (Set.range (fun w : {w : Cell r → ℝ // IsAlloc w} =>
      proxyValue M (w : Cell r → ℝ))) := by
  refine ⟨1, ?_⟩
  rintro x ⟨w, rfl⟩
  exact proxyValue_le M hM (w : Cell r → ℝ) w.2

theorem proxyGame_ge (M : ℝ) (hM : 0 < M) : 1 / 128 ≤ proxyGame r M :=
  le_trans (proxyValue_unif_ge M hM)
    (le_ciSup (bddAbove_proxy M hM) (⟨wUnif r, wUnif_isAlloc r⟩))

theorem proxyGame_le (M : ℝ) (hM : 0 < M) : proxyGame r M ≤ 1 :=
  ciSup_le (fun w => proxyValue_le M hM (w : Cell r → ℝ) w.2)

/-! ## A-R: the ratio of the two games -/

/-- **`Theta((rM)^{-1})`, on the games themselves.**

No value is assumed: `trueGame` and `proxyGame` are `sup-inf` over the actual allocations
and the actual alternatives of the actual world, and all four bounds are theorems above.
The proxy value stays bounded between two absolute constants while the true value falls
like `1/(rM)`, so the surrogate overstates the information available by a factor growing
without bound in `r` -- and it does so at UNIFORM variance, `M = 1`. -/
theorem rpair_games_theta (M : ℝ) (hM : 0 < M) (hr : 0 < r) :
    1 / (128 * (4 + 2 * (r : ℝ) * M)) ≤ trueGame r M / proxyGame r M
      ∧ trueGame r M / proxyGame r M ≤ 16 / (M * (r : ℝ)) := by
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hplo := proxyGame_ge (r := r) M hM
  have hphi := proxyGame_le (r := r) M hM
  have hppos : (0 : ℝ) < proxyGame r M := by linarith
  have htlo := trueGame_ge M hM hr
  have hthi := trueGame_le M hM hr
  have hZ : (0 : ℝ) < 4 + 2 * (r : ℝ) * M := by nlinarith
  have hZ128 : (0 : ℝ) < 128 * (4 + 2 * (r : ℝ) * M) := by linarith
  have hc : (0 : ℝ) ≤ 1 / (128 * (4 + 2 * (r : ℝ) * M)) := le_of_lt (div_pos one_pos hZ128)
  have hMr : (0 : ℝ) < M * (r : ℝ) := by positivity
  constructor
  · rw [le_div_iff₀ hppos]
    have h1 : 1 / (128 * (4 + 2 * (r : ℝ) * M)) * proxyGame r M
        ≤ 1 / (128 * (4 + 2 * (r : ℝ) * M)) * 1 :=
      mul_le_mul_of_nonneg_left hphi hc
    rw [mul_one] at h1
    linarith
  · rw [div_le_iff₀ hppos]
    have hk : 16 / (M * (r : ℝ)) * (1 / 128) = 1 / (8 * M * (r : ℝ)) := by
      field_simp; ring
    have h2 : 16 / (M * (r : ℝ)) * (1 / 128) ≤ 16 / (M * (r : ℝ)) * proxyGame r M :=
      mul_le_mul_of_nonneg_left hplo (le_of_lt (div_pos (by norm_num) hMr))
    rw [hk] at h2
    linarith

/-! ## Audit -/

#print axioms lamW_proxy
#print axioms wUnif_isAlloc
#print axioms pairShift_mem_alt
#print axioms trueGame_le
#print axioms trueGame_ge
#print axioms anchorBump_mem
#print axioms energy_anchorBump
#print axioms proxyValue_le
#print axioms proxyValue_unif_ge
#print axioms proxyGame_ge
#print axioms proxyGame_le
#print axioms rpair_games_theta

end CIGAMF.P13.ARGames
