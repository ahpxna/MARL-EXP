import «LeanPaperBDecisionOrderV1»
import «LeanPaperBParityChannelV1»

/-!
# Paper B: queries that cannot see a pair, and the parity cancellation

`decision_lower` (`LeanPaperBDecisionOrderV1`) assumes `c h^{2 sq q u v} ≤ κ_q(u,v)` for **every**
query and every pair `u ≠ v`. On the parity channel a query that names neither world gives the
same law in both, so `κ_q(u,v) = 0` and the assumption fails for `c, h > 0`. The endpoint parity
chain never used that theorem; the defect is in applying the general statement to the channel.

* `decision_lower_wit`: the lower side needs the bound only at **one witness query per pair**,
  at the pair's order.
* `visible_upper`, `visible_witness`: a channel whose queries are either *visible* for a pair
  (graded, `c h^{2 ord} ≤ κ ≤ C h^{2 ord}`) or *invisible* (`κ = 0`), and in which every pair has
  a visible query, satisfies the upper hypothesis of `decision_upper` for every query and the
  witness hypothesis of `decision_lower_wit`, with invisible queries given any order `N` above
  the visible ones.
* `decision_order_visible`: hence the two-sided law `D(w) ≍ h^{2 dOrder w}` on such channels.
* `par_vis_iff`, `par_cover`, `par_sep`: the parity channel is such a channel. Query `q ≥ 1` sees
  the pair `(w, w')` exactly when it names one of them; every pair is seen; and the pair's order
  is `min(w+1, w'+1)` (paper numbering).

**The parity cancellation** (`parity_moment_lt`, `parity_moment_eq`). For `z` uniform on
`{±1}^j`, `E[(∏ z_ℓ)(Σ z_ℓ)^k] = 0` for `k < j` and `= j!` for `k = j`. In the Taylor expansion
of the query-`j` density in `h`, this is the step that kills every order below `j` in the
difference `p_+ - p_-` and leaves the leading coefficient
`a_j(y) = (-1)^j j^{-j} (φ_σ^{(j)}(y-1) - φ_σ^{(j)}(y+1))`.
-/

namespace CIGAMF.P13.PaperBVisible

open Finset CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBDecisionOrder

section Orders

variable {W Q A : Type*} [Fintype W] [DecidableEq W] [Fintype Q] [Nonempty Q]
  [Fintype A] [DecidableEq A]

/-- **Lower side with one witness query per pair.** -/
theorem decision_lower_wit (sq : Q → W → W → ℕ) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty) (κ : Q → W → W → ℝ) (c h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hwit : ∀ u v, u ≠ v → ∃ q, c * h ^ (2 * sepQ sq u v) ≤ κ q u v)
    (hκ0 : ∀ q u v, 0 ≤ κ q u v) (hc : 0 ≤ c) (w : W) :
    ∃ a ∈ safe w, ∀ l, a ∉ safe l →
      c / Fintype.card Q * h ^ (2 * dOrder sq safe hsafe w)
        ≤ ∑ q, (1 / (Fintype.card Q : ℝ)) * κ q w l := by
  set d := dOrder sq safe hsafe w with hd
  obtain ⟨a, ha⟩ := dOrder_spec sq safe hsafe w
  refine ⟨a, ha w (mem_near_self sq w d), fun l hal => ?_⟩
  have hl : l ∉ near sq w d := fun h => hal (ha l h)
  simp only [near, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_lt] at hl
  obtain ⟨hlw, hsep⟩ := hl
  obtain ⟨q0, hq0⟩ := hwit w l (Ne.symm hlw)
  have hcard : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have hk : c * h ^ (2 * d) ≤ κ q0 w l := by
    refine le_trans ?_ hq0
    apply mul_le_mul_of_nonneg_left _ hc
    exact pow_le_pow_of_le_one hh0 hh1 (by omega)
  calc c / Fintype.card Q * h ^ (2 * d) = (1 / (Fintype.card Q : ℝ)) * (c * h ^ (2 * d)) := by
        ring
    _ ≤ (1 / (Fintype.card Q : ℝ)) * κ q0 w l :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ ≤ ∑ q, (1 / (Fintype.card Q : ℝ)) * κ q w l :=
        Finset.single_le_sum (f := fun q => (1 / (Fintype.card Q : ℝ)) * κ q w l)
          (fun q _ => mul_nonneg (by positivity) (hκ0 q w l)) (Finset.mem_univ q0)

/-- The order table of a channel with visible and invisible queries: a visible query has its
own order, an invisible one gets the order `N`. -/
def visSq (vis : Q → W → W → Prop) [∀ q u v, Decidable (vis q u v)] (ord : Q → W → W → ℕ)
    (N : ℕ) : Q → W → W → ℕ :=
  fun q u v => if vis q u v then ord q u v else N

variable (vis : Q → W → W → Prop) [∀ q u v, Decidable (vis q u v)] (ord : Q → W → W → ℕ)
  (N : ℕ) (κ : Q → W → W → ℝ) (c C h : ℝ)

/-- **Upper hypothesis for every query.** -/
theorem visible_upper (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hup : ∀ q u v, u ≠ v → vis q u v → κ q u v ≤ C * h ^ (2 * ord q u v))
    (hinv : ∀ q u v, ¬ vis q u v → κ q u v = 0) :
    ∀ q u v, u ≠ v → κ q u v ≤ C * h ^ (2 * visSq vis ord N q u v) := by
  intro q u v huv
  unfold visSq
  split_ifs with hv
  · exact hup q u v huv hv
  · rw [hinv q u v hv]; positivity

/-- **Witness hypothesis.**  The best query of the table is visible, or else a visible query has
the same order. -/
theorem visible_witness (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hlo : ∀ q u v, u ≠ v → vis q u v → c * h ^ (2 * ord q u v) ≤ κ q u v)
    (hcover : ∀ u v, u ≠ v → ∃ q, vis q u v) (hN : ∀ q u v, vis q u v → ord q u v ≤ N)
    (hc : 0 ≤ c) :
    ∀ u v, u ≠ v → ∃ q, c * h ^ (2 * sepQ (visSq vis ord N) u v) ≤ κ q u v := by
  intro u v huv
  obtain ⟨q1, hq1⟩ := exists_best (visSq vis ord N) u v
  by_cases hv : vis q1 u v
  · refine ⟨q1, ?_⟩
    rw [← hq1]; unfold visSq; rw [if_pos hv]
    exact hlo q1 u v huv hv
  · obtain ⟨q2, hq2⟩ := hcover u v huv
    refine ⟨q2, le_trans ?_ (hlo q2 u v huv hq2)⟩
    apply mul_le_mul_of_nonneg_left _ hc
    apply pow_le_pow_of_le_one hh0 hh1
    have : sepQ (visSq vis ord N) u v = N := by
      rw [← hq1]; unfold visSq; rw [if_neg hv]
    rw [this]
    have := hN q2 u v hq2
    omega

/-- **The two-sided law on channels with invisible queries.** -/
theorem decision_order_visible (safe : W → Finset A) (hsafe : ∀ w, (safe w).Nonempty)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hup : ∀ q u v, u ≠ v → vis q u v → κ q u v ≤ C * h ^ (2 * ord q u v))
    (hlo : ∀ q u v, u ≠ v → vis q u v → c * h ^ (2 * ord q u v) ≤ κ q u v)
    (hinv : ∀ q u v, ¬ vis q u v → κ q u v = 0)
    (hcover : ∀ u v, u ≠ v → ∃ q, vis q u v) (hN : ∀ q u v, vis q u v → ord q u v ≤ N)
    (hκ0 : ∀ q u v, 0 ≤ κ q u v) (w : W) :
    (∃ a ∈ safe w, ∀ l, a ∉ safe l →
      c / Fintype.card Q * h ^ (2 * dOrder (visSq vis ord N) safe hsafe w)
        ≤ ∑ q, (1 / (Fintype.card Q : ℝ)) * κ q w l)
    ∧ (1 ≤ dOrder (visSq vis ord N) safe hsafe w → ∀ a ∈ safe w, ∀ α : Q → ℝ,
        (∀ q, 0 ≤ α q) → ∑ q, α q = 1 →
        ∃ l, a ∉ safe l ∧ ∑ q, α q * κ q w l
          ≤ C * h ^ (2 * dOrder (visSq vis ord N) safe hsafe w)) := by
  refine ⟨decision_lower_wit _ safe hsafe κ c h hh0 hh1
    (visible_witness vis ord N κ c h hh0 hh1 hlo hcover hN hc) hκ0 hc w, ?_⟩
  intro hw a ha α hα0 hα1
  exact decision_upper _ safe hsafe κ C h hC hh0 hh1
    (visible_upper vis ord N κ C h hC hh0 hup hinv) w hw a ha α hα0 hα1

end Orders

/-! ## The parity channel has this structure -/

section Parity

open CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityChannel

variable (m : ℕ)

/-- Query `q` sees the pair `(w, w')` when it is informative and names one of them. -/
def parVis (q w w' : Fin m) : Prop := (q : ℕ) ≠ 0 ∧ ((q : ℕ) = w + 1 ∨ (q : ℕ) = w' + 1)

instance (q w w' : Fin m) : Decidable (parVis m q w w') := by unfold parVis; infer_instance

/-- **Visibility is the mask test.** -/
theorem par_vis_iff (q w w' : Fin m) (hww : w ≠ w') :
    maskR q (w + 1) ≠ maskR q (w' + 1) ↔ parVis m q w w' := by
  have hne : (w : ℕ) + 1 ≠ w' + 1 := by
    intro h; apply hww; exact Fin.ext (by omega)
  rw [masks_differ_iff q (w + 1) (w' + 1) hne]
  unfold parVis
  constructor
  · rintro (h | h) <;> refine ⟨by omega, ?_⟩ <;> simp [h]
  · rintro ⟨-, h | h⟩ <;> simp [h]

/-- **Every pair is seen by some query.** -/
theorem par_cover (w w' : Fin m) (hww : w ≠ w') : ∃ q : Fin m, parVis m q w w' := by
  have hw := w.isLt
  have hw' := w'.isLt
  have hne : (w : ℕ) ≠ w' := fun h => hww (Fin.ext h)
  by_cases h : (w : ℕ) + 1 < m
  · exact ⟨⟨w + 1, h⟩, by unfold parVis; simp⟩
  · have h' : (w' : ℕ) + 1 < m := by omega
    exact ⟨⟨w' + 1, h'⟩, by unfold parVis; simp⟩

/-- The parity order table: query `q` has order `q` on the pairs it sees, and `m` elsewhere. -/
def parSq (q w w' : Fin m) : ℕ := if parVis m q w w' then (q : ℕ) else m

/-- **The pair's order is the smaller paper index.** -/
theorem par_sep [NeZero m] (w w' : Fin m) (hww : w ≠ w') :
    sepQ (parSq m) w w' = min ((w : ℕ) + 1) ((w' : ℕ) + 1) := by
  have hw := w.isLt
  have hw' := w'.isLt
  have hne : (w : ℕ) ≠ w' := fun h => hww (Fin.ext h)
  apply le_antisymm
  · -- the query naming the smaller world, which exists
    rcases le_total ((w : ℕ) + 1) ((w' : ℕ) + 1) with hle | hle
    · have hlt : (w : ℕ) + 1 < m := by omega
      refine (sepQ_le _ w w' ⟨w + 1, hlt⟩).trans ?_
      unfold parSq parVis; simp [min_eq_left hle]
    · have hlt : (w' : ℕ) + 1 < m := by omega
      refine (sepQ_le _ w w' ⟨w' + 1, hlt⟩).trans ?_
      unfold parSq parVis; simp [min_eq_right hle]
  · obtain ⟨q, hq⟩ := exists_best (parSq m) w w'
    rw [← hq]
    unfold parSq
    split_ifs with hv
    · rcases hv.2 with h | h <;> omega
    · have := q.isLt; omega

end Parity

/-! ## The parity cancellation -/

section Moments

/-- A `±1` sign. -/
def sg (b : Bool) : ℤ := if b then -1 else 1

theorem pow_sum_expand {j : ℕ} (k : ℕ) (x : Fin j → ℤ) :
    (∑ l, x l) ^ k = ∑ f : Fin k → Fin j, ∏ i, x (f i) := by
  rw [← Fin.prod_const k (∑ l, x l)]
  exact Fintype.prod_sum (fun (_ : Fin k) l => x l)

theorem prod_fiber {j k : ℕ} (y : Fin j → ℤ) (f : Fin k → Fin j) :
    ∏ i, y (f i) = ∏ l, y l ^ (univ.filter (fun i => f i = l)).card := by
  rw [← Finset.prod_fiberwise univ f (fun i => y (f i))]
  refine Finset.prod_congr rfl fun l _ => ?_
  have : ∀ i ∈ univ.filter (fun i => f i = l), y (f i) = y l := fun i hi => by
    rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.prod_congr rfl this, Finset.prod_const]

/-- One term of the expansion: `Σ_z ∏_ℓ z_ℓ ∏_i z_{f i} = ∏_ℓ (1 + (-1)^{1 + #f⁻¹ℓ})`. -/
theorem term_eq {j k : ℕ} (f : Fin k → Fin j) :
    ∑ z : Fin j → Bool, (∏ l, sg (z l)) * ∏ i, sg (z (f i))
      = ∏ l, ((-1) ^ (1 + (univ.filter (fun i => f i = l)).card) + 1) := by
  have h1 : ∀ z : Fin j → Bool, (∏ l, sg (z l)) * ∏ i, sg (z (f i))
      = ∏ l, sg (z l) ^ (1 + (univ.filter (fun i => f i = l)).card) := by
    intro z
    rw [prod_fiber (fun l => sg (z l)) f, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [pow_add, pow_one]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun l b => sg b ^ (1 + (univ.filter (fun i => f i = l)).card))]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Fintype.sum_bool]
  simp [sg]

theorem moment_expand (j k : ℕ) :
    ∑ z : Fin j → Bool, (∏ l, sg (z l)) * (∑ l, sg (z l)) ^ k
      = ∑ f : Fin k → Fin j, ∏ l, ((-1) ^ (1 + (univ.filter (fun i => f i = l)).card) + 1) := by
  simp_rw [pow_sum_expand k, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun f _ => term_eq f

theorem factor_zero {j k : ℕ} (f : Fin k → Fin j) (hf : ¬ Function.Surjective f) :
    ∏ l, ((-1 : ℤ) ^ (1 + (univ.filter (fun i => f i = l)).card) + 1) = 0 := by
  simp only [Function.Surjective, not_forall, not_exists] at hf
  obtain ⟨l, hl⟩ := hf
  refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
  have : univ.filter (fun i => f i = l) = ∅ := by
    ext i; simp [hl i]
  rw [this]; norm_num

/-- **Orders below `j` cancel.** -/
theorem parity_moment_lt (j k : ℕ) (hk : k < j) :
    ∑ z : Fin j → Bool, (∏ l, sg (z l)) * (∑ l, sg (z l)) ^ k = 0 := by
  rw [moment_expand]
  refine Finset.sum_eq_zero fun f _ => factor_zero f fun hs => ?_
  have := Fintype.card_le_of_surjective f hs
  simp at this; omega

theorem card_surj (j : ℕ) :
    (univ.filter (fun f : Fin j → Fin j => Function.Surjective f)).card = j.factorial := by
  classical
  have : univ.filter (fun f : Fin j → Fin j => Function.Surjective f)
      = univ.map ⟨fun σ : Equiv.Perm (Fin j) => (σ : Fin j → Fin j), DFunLike.coe_injective⟩ := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hf
      exact ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hf, hf⟩, rfl⟩
    · rintro ⟨σ, rfl⟩; exact σ.surjective
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- **Order `j` survives with coefficient `j!`** (times `2^j` for the sum over signs). -/
theorem parity_moment_eq (j : ℕ) :
    ∑ z : Fin j → Bool, (∏ l, sg (z l)) * (∑ l, sg (z l)) ^ j = 2 ^ j * j.factorial := by
  classical
  rw [moment_expand]
  have hterm : ∀ f : Fin j → Fin j,
      ∏ l, ((-1 : ℤ) ^ (1 + (univ.filter (fun i => f i = l)).card) + 1)
        = if Function.Surjective f then 2 ^ j else 0 := by
    intro f
    split_ifs with hs
    · have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hs
      have hone : ∀ l, (univ.filter (fun i => f i = l)).card = 1 := by
        intro l
        obtain ⟨i0, hi0⟩ := hs l
        rw [Finset.card_eq_one]
        refine ⟨i0, ?_⟩
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hi; exact hinj (hi.trans hi0.symm)
        · rintro rfl; exact hi0
      simp_rw [hone]
      norm_num
    · exact factor_zero f hs
  simp_rw [hterm]
  rw [← Finset.sum_filter, Finset.sum_const, card_surj, nsmul_eq_mul]
  push_cast
  ring

end Moments

#print axioms decision_lower_wit
#print axioms visible_upper
#print axioms visible_witness
#print axioms decision_order_visible
#print axioms par_vis_iff
#print axioms par_cover
#print axioms par_sep
#print axioms parity_moment_lt
#print axioms parity_moment_eq

end CIGAMF.P13.PaperBVisible
