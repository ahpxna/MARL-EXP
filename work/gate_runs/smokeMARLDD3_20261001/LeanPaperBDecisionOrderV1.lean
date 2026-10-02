import «LeanPaperBSafeOrderV1»

/-!
# Paper B: the decision order of a world, the characteristic game, and query design

**Setting.**
* Finite worlds `W`, finite queries `Q` and answers `A`, with a safe correspondence
  `safe : W → Finset A`.
* Per query and pair, a separation order `sq q u v ∈ ℕ`; the pair's order is
  `sepQ u v = min_q sq q u v`.
* A graded channel: `c h^{2 sq} ≤ κ_q(u,v) ≤ C h^{2 sq}` for `u ≠ v` and `0 < h ≤ 1`, where
  `κ_q` is the per-query information (KL, χ² or Hellinger).

**The decision order of a world** (`dOrder`). It is the least `s` such that `w` and the worlds
the observer cannot tell from `w` up to order `s` (`near w s`) share a safe answer.

**B-1, the characteristic game at order `dOrder w`.**
* The Degenne–Koolen value at `w` is
  `D(w) = max_{a safe at w} max_α min_{λ: a unsafe at λ} Σ_q α_q κ_q(w,λ)`.
* `decision_upper`: for every answer safe at `w` and every allocation, some alternative where
  that answer is unsafe carries at most `C h^{2 dOrder w}`. So `D(w) ≤ C h^{2 dOrder w}`.
* `decision_lower`: some answer safe at `w`, with the uniform allocation, carries at least
  `(c/|Q|) h^{2 dOrder w}` against every alternative where it is unsafe. So
  `D(w) ≥ (c/|Q|) h^{2 dOrder w}`.
* Both are statements about the game at one world (the per-world benchmark).
* `order_ge_obstruction`, and `obstruction_of_order` under the ultrametric property (U), give
  `max_w dOrder w = s* = max_{H obstruction} min_{u≠v∈H} sepQ u v` (`max_order_iff`). The hardest
  world's game (the minimax benchmark) is therefore of order `h^{2 s*}`.

**B-4, query design.**
* `dec_hitting`: a sub-menu `M` has decision order at most `s` if and only if it hits every
  obstruction with a query that separates one of its pairs at order `≤ s`.
* `id_implies_dec`: identification order `≤ s` implies decision order `≤ s`.
* `dec_mono`: adding queries never raises the decision order.
* `gap_example`: one query, three worlds; the decision order is `1` while the identification
  order is `5`.
-/

namespace CIGAMF.P13.PaperBDecisionOrder

open Finset CIGAMF.P13.PaperBSafe

variable {W Q A : Type*} [Fintype W] [DecidableEq W] [Fintype Q] [Nonempty Q]
  [Fintype A] [DecidableEq A]

/-! ## 1. Orders -/

/-- The separation order of a pair: the order of its best query. -/
noncomputable def sepQ (sq : Q → W → W → ℕ) (u v : W) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun q => sq q u v)

theorem sepQ_le (sq : Q → W → W → ℕ) (u v : W) (q : Q) : sepQ sq u v ≤ sq q u v :=
  Finset.inf'_le _ (Finset.mem_univ q)

theorem exists_best (sq : Q → W → W → ℕ) (u v : W) : ∃ q, sq q u v = sepQ sq u v := by
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun q => sq q u v)
  exact ⟨q, hq.symm⟩

/-- The worlds that the observer cannot tell from `w` up to order `s`, and `w` itself. -/
noncomputable def near (sq : Q → W → W → ℕ) (w : W) (s : ℕ) : Finset W :=
  Finset.univ.filter (fun l => l = w ∨ s < sepQ sq w l)

theorem mem_near_self (sq : Q → W → W → ℕ) (w : W) (s : ℕ) : w ∈ near sq w s := by
  simp [near]

/-- A set of worlds shares a safe answer. -/
def CommonSafe (safe : W → Finset A) (F : Finset W) : Prop := ∃ a, ∀ u ∈ F, a ∈ safe u

theorem commonSafe_exists (sq : Q → W → W → ℕ) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty) (w : W) : ∃ s, CommonSafe safe (near sq w s) := by
  classical
  refine ⟨Finset.univ.sup (fun p : W × W => sepQ sq p.1 p.2), ?_⟩
  obtain ⟨a, ha⟩ := hsafe w
  refine ⟨a, fun u hu => ?_⟩
  simp only [near, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with rfl | hlt
  · exact ha
  · exfalso
    have : sepQ sq w u ≤ Finset.univ.sup (fun p : W × W => sepQ sq p.1 p.2) :=
      Finset.le_sup (f := fun p : W × W => sepQ sq p.1 p.2) (Finset.mem_univ (w, u))
    omega

open Classical in
/-- **The decision order of a world.** -/
noncomputable def dOrder (sq : Q → W → W → ℕ) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty) (w : W) : ℕ :=
  Nat.find (commonSafe_exists sq safe hsafe w)

theorem dOrder_spec (sq : Q → W → W → ℕ) (safe : W → Finset A) (hsafe : ∀ w, (safe w).Nonempty)
    (w : W) : CommonSafe safe (near sq w (dOrder sq safe hsafe w)) := by
  classical
  exact Nat.find_spec (commonSafe_exists sq safe hsafe w)

theorem dOrder_min (sq : Q → W → W → ℕ) (safe : W → Finset A) (hsafe : ∀ w, (safe w).Nonempty)
    (w : W) (s : ℕ) (hs : s < dOrder sq safe hsafe w) : ¬ CommonSafe safe (near sq w s) := by
  classical
  exact Nat.find_min (commonSafe_exists sq safe hsafe w) hs

/-! ## 2. The characteristic game at the decision order -/

/-- **Upper side.**  If `dOrder w ≥ 1`, every answer safe at `w` is unsafe at some world that no
allocation separates from `w` by more than `C h^{2 dOrder w}`. -/
theorem decision_upper (sq : Q → W → W → ℕ) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty) (κ : Q → W → W → ℝ) (C h : ℝ) (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1) (hup : ∀ q u v, u ≠ v → κ q u v ≤ C * h ^ (2 * sq q u v))
    (w : W) (hw : 1 ≤ dOrder sq safe hsafe w) (a : A) (ha : a ∈ safe w)
    (α : Q → ℝ) (hα0 : ∀ q, 0 ≤ α q) (hα1 : ∑ q, α q = 1) :
    ∃ l, a ∉ safe l ∧ ∑ q, α q * κ q w l ≤ C * h ^ (2 * dOrder sq safe hsafe w) := by
  set d := dOrder sq safe hsafe w with hd
  have hnot := dOrder_min sq safe hsafe w (d - 1) (by omega)
  simp only [CommonSafe, not_exists, not_forall] at hnot
  obtain ⟨l, hl, hal⟩ := hnot a
  have hlw : l ≠ w := by rintro rfl; exact hal ha
  simp only [near, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  have hsep : d ≤ sepQ sq w l := by
    rcases hl with h | h
    · exact absurd h hlw
    · omega
  refine ⟨l, hal, ?_⟩
  have hq : ∀ q, κ q w l ≤ C * h ^ (2 * d) := by
    intro q
    refine (hup q w l (Ne.symm hlw)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC
    exact pow_le_pow_of_le_one hh0 hh1 (by have := sepQ_le sq w l q; omega)
  calc ∑ q, α q * κ q w l ≤ ∑ q, α q * (C * h ^ (2 * d)) :=
        Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hq q) (hα0 q)
    _ = C * h ^ (2 * d) := by rw [← Finset.sum_mul, hα1, one_mul]

/-- **Lower side.**  Some answer safe at `w`, with the uniform allocation, carries at least
`(c/|Q|) h^{2 dOrder w}` against every world where it is unsafe. -/
theorem decision_lower (sq : Q → W → W → ℕ) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty) (κ : Q → W → W → ℝ) (c h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hlo : ∀ q u v, u ≠ v → c * h ^ (2 * sq q u v) ≤ κ q u v) (hκ0 : ∀ q u v, 0 ≤ κ q u v)
    (hc : 0 ≤ c) (w : W) :
    ∃ a ∈ safe w, ∀ l, a ∉ safe l →
      c / Fintype.card Q * h ^ (2 * dOrder sq safe hsafe w)
        ≤ ∑ q, (1 / (Fintype.card Q : ℝ)) * κ q w l := by
  set d := dOrder sq safe hsafe w with hd
  obtain ⟨a, ha⟩ := dOrder_spec sq safe hsafe w
  refine ⟨a, ha w (mem_near_self sq w d), fun l hal => ?_⟩
  have hl : l ∉ near sq w d := fun h => hal (ha l h)
  simp only [near, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_lt] at hl
  obtain ⟨hlw, hsep⟩ := hl
  obtain ⟨q0, hq0⟩ := exists_best sq w l
  have hcard : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have hk : c * h ^ (2 * d) ≤ κ q0 w l := by
    refine le_trans ?_ (hlo q0 w l (Ne.symm hlw))
    apply mul_le_mul_of_nonneg_left _ hc
    exact pow_le_pow_of_le_one hh0 hh1 (by omega)
  calc c / Fintype.card Q * h ^ (2 * d) = (1 / (Fintype.card Q : ℝ)) * (c * h ^ (2 * d)) := by
        ring
    _ ≤ (1 / (Fintype.card Q : ℝ)) * κ q0 w l :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ ≤ ∑ q, (1 / (Fintype.card Q : ℝ)) * κ q w l :=
        Finset.single_le_sum (f := fun q => (1 / (Fintype.card Q : ℝ)) * κ q w l)
          (fun q _ => mul_nonneg (by positivity) (hκ0 q w l)) (Finset.mem_univ q0)

/-! ## 3. The decision order and the obstruction order -/

/-- **An obstruction whose pairs are all separated at order `≥ s₀` forces `dOrder ≥ s₀` at each
of its worlds.** -/
theorem order_ge_obstruction (sq : Q → W → W → ℕ) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty) (H : Finset W) (hH : Unsafe safe H) (w : W) (hw : w ∈ H)
    (s₀ : ℕ) (hsep : ∀ u ∈ H, ∀ v ∈ H, u ≠ v → s₀ ≤ sepQ sq u v) :
    s₀ ≤ dOrder sq safe hsafe w := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, ha⟩ := dOrder_spec sq safe hsafe w
  obtain ⟨u, hu, hau⟩ := hH a
  apply hau
  apply ha u
  simp only [near, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases huw : u = w
  · exact Or.inl huw
  · exact Or.inr (lt_of_lt_of_le hlt (hsep w hw u hu (Ne.symm huw)))

/-- **Under the ultrametric property, every world's decision order is attained by an
obstruction.** -/
theorem obstruction_of_order (sq : Q → W → W → ℕ) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty)
    (hsym : ∀ u v, sepQ sq u v = sepQ sq v u)
    (hU : ∀ u v x, min (sepQ sq u x) (sepQ sq x v) ≤ sepQ sq u v)
    (w : W) (hw : 1 ≤ dOrder sq safe hsafe w) :
    ∃ H, Unsafe safe H ∧ w ∈ H
      ∧ ∀ u ∈ H, ∀ v ∈ H, u ≠ v → dOrder sq safe hsafe w ≤ sepQ sq u v := by
  set d := dOrder sq safe hsafe w with hd
  refine ⟨near sq w (d - 1), ?_, mem_near_self sq w _, ?_⟩
  · have hnot := dOrder_min sq safe hsafe w (d - 1) (by omega)
    intro a
    simp only [CommonSafe, not_exists, not_forall] at hnot
    obtain ⟨u, hu, hau⟩ := hnot a
    exact ⟨u, hu, hau⟩
  · intro u hu v hv huv
    simp only [near, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    have hwu : u = w ∨ d ≤ sepQ sq w u := by rcases hu with h | h; exact Or.inl h; exact Or.inr (by omega)
    have hwv : v = w ∨ d ≤ sepQ sq w v := by rcases hv with h | h; exact Or.inl h; exact Or.inr (by omega)
    rcases hwu with rfl | hu'
    · rcases hwv with rfl | hv'
      · exact absurd rfl huv
      · exact hv'
    · rcases hwv with rfl | hv'
      · rw [hsym]; exact hu'
      · have := hU u v w
        rw [hsym u w] at this
        omega

/-- **The largest decision order is the obstruction order.**  For every `s ≥ 1`, some world has
decision order `≥ s` if and only if some obstruction has every pair separated at order `≥ s`.
So `max_w dOrder w = s*`. -/
theorem max_order_iff (sq : Q → W → W → ℕ) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty)
    (hsym : ∀ u v, sepQ sq u v = sepQ sq v u)
    (hU : ∀ u v x, min (sepQ sq u x) (sepQ sq x v) ≤ sepQ sq u v) (s : ℕ) (hs : 1 ≤ s) :
    (∃ w, s ≤ dOrder sq safe hsafe w)
      ↔ ∃ H, Unsafe safe H ∧ H.Nonempty ∧ ∀ u ∈ H, ∀ v ∈ H, u ≠ v → s ≤ sepQ sq u v := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨H, hH, hwH, hsep⟩ := obstruction_of_order sq safe hsafe hsym hU w (by omega)
    exact ⟨H, hH, ⟨w, hwH⟩, fun u hu v hv huv => hw.trans (hsep u hu v hv huv)⟩
  · rintro ⟨H, hH, ⟨w, hw⟩, hsep⟩
    exact ⟨w, order_ge_obstruction sq safe hsafe H hH w hw s hsep⟩

/-! ## 4. Query design: the decision order as an order-thresholded hitting set -/

/-- The separation order of a pair within a sub-menu `M`. -/
noncomputable def sepM (sq : Q → W → W → ℕ) (M : Finset Q) (hM : M.Nonempty) (u v : W) : ℕ :=
  M.inf' hM (fun q => sq q u v)

/-- The sub-menu's decision order is at most `s`. -/
def DecLE (sq : Q → W → W → ℕ) (safe : W → Finset A) (M : Finset Q) (hM : M.Nonempty)
    (s : ℕ) : Prop :=
  ∀ H, Unsafe safe H → ∃ u ∈ H, ∃ v ∈ H, u ≠ v ∧ sepM sq M hM u v ≤ s

/-- The sub-menu's identification order is at most `s`. -/
def IdLE (sq : Q → W → W → ℕ) (M : Finset Q) (hM : M.Nonempty) (s : ℕ) : Prop :=
  ∀ u v, u ≠ v → sepM sq M hM u v ≤ s

/-- **Hitting sets.**  Decision order `≤ s` means: every obstruction is hit by a query of `M` that
separates one of its pairs at order `≤ s`. -/
theorem dec_hitting (sq : Q → W → W → ℕ) (safe : W → Finset A) (M : Finset Q)
    (hM : M.Nonempty) (s : ℕ) :
    DecLE sq safe M hM s
      ↔ ∀ H, Unsafe safe H → ∃ q ∈ M, ∃ u ∈ H, ∃ v ∈ H, u ≠ v ∧ sq q u v ≤ s := by
  constructor
  · intro h H hH
    obtain ⟨u, hu, v, hv, huv, hle⟩ := h H hH
    obtain ⟨q, hq, hqe⟩ := Finset.exists_mem_eq_inf' hM (fun q => sq q u v)
    exact ⟨q, hq, u, hu, v, hv, huv, by unfold sepM at hle; rw [← hqe]; exact hle⟩
  · intro h H hH
    obtain ⟨q, hq, u, hu, v, hv, huv, hle⟩ := h H hH
    exact ⟨u, hu, v, hv, huv, (Finset.inf'_le _ hq).trans hle⟩

/-- **Identification is harder**: identification order `≤ s` implies decision order `≤ s`, since
every obstruction has two distinct worlds. -/
theorem id_implies_dec (sq : Q → W → W → ℕ) (safe : W → Finset A) (M : Finset Q)
    (hM : M.Nonempty) (s : ℕ) (hsafe : ∀ w, (safe w).Nonempty) [Nonempty A]
    (h : IdLE sq M hM s) : DecLE sq safe M hM s := by
  intro H hH
  obtain ⟨a⟩ := ‹Nonempty A›
  obtain ⟨u, hu, hau⟩ := hH a
  obtain ⟨b, hb⟩ := hsafe u
  obtain ⟨v, hv, hbv⟩ := hH b
  have huv : u ≠ v := by rintro rfl; exact hbv hb
  exact ⟨u, hu, v, hv, huv, h u v huv⟩

/-- **More queries never raise the decision order.** -/
theorem dec_mono (sq : Q → W → W → ℕ) (safe : W → Finset A) (M M' : Finset Q)
    (hM : M.Nonempty) (hM' : M'.Nonempty) (hsub : M ⊆ M') (s : ℕ)
    (h : DecLE sq safe M hM s) : DecLE sq safe M' hM' s := by
  rw [dec_hitting] at h ⊢
  intro H hH
  obtain ⟨q, hq, rest⟩ := h H hH
  exact ⟨q, hsub hq, rest⟩

/-- The gap example: three worlds, answers "not `w`", one query that separates world `0` from
the others at order `1` and worlds `1, 2` from each other at order `5`. -/
def gapSafe (w : Fin 3) : Finset (Fin 3) := Finset.univ.erase w

def gapSq (_q : Fin 1) (u v : Fin 3) : ℕ :=
  if u = v then 0 else if u = 0 ∨ v = 0 then 1 else 5

/-- **Decision order `1`, identification order `5`, with the same single query.** -/
theorem gap_example :
    DecLE gapSq gapSafe Finset.univ Finset.univ_nonempty 1
      ∧ ¬ IdLE gapSq Finset.univ Finset.univ_nonempty 4 := by
  refine ⟨?_, ?_⟩
  · rw [dec_hitting]
    intro H hH
    -- an obstruction of "not w" must contain every world, in particular 0 and 1
    have h0 : (0 : Fin 3) ∈ H := by
      obtain ⟨u, hu, hu0⟩ := hH 0
      have : u = 0 := by simpa [gapSafe, eq_comm] using hu0
      rw [← this]; exact hu
    have h1 : (1 : Fin 3) ∈ H := by
      obtain ⟨u, hu, hu1⟩ := hH 1
      have : u = 1 := by simpa [gapSafe, eq_comm] using hu1
      rw [← this]; exact hu
    exact ⟨0, Finset.mem_univ _, 0, h0, 1, h1, by decide, by decide⟩
  · intro h
    have := h 1 2 (by decide)
    unfold sepM at this
    simp [gapSq] at this

#print axioms decision_upper
#print axioms decision_lower
#print axioms order_ge_obstruction
#print axioms obstruction_of_order
#print axioms max_order_iff
#print axioms dec_hitting
#print axioms id_implies_dec
#print axioms dec_mono
#print axioms gap_example

end CIGAMF.P13.PaperBDecisionOrder
