import «LeanSupportObstructionQueryOrderV1»

/-! # Paper B, geometry: the order needed to DECIDE and the order needed to IDENTIFY -/

namespace CIGAMF.P13.PaperBGeometry

open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportObstructionQueryOrder

variable {m : ℕ}

/-- Order-`s` indistinguishability: the first `s` worlds are resolved, the rest are not. -/
def IndistAt (s : ℕ) (θ lam : Fin m) : Prop := θ = lam ∨ (s ≤ (θ : ℕ) ∧ s ≤ (lam : ℕ))

theorem indistAt_refl (s : ℕ) (θ : Fin m) : IndistAt s θ θ := Or.inl rfl

theorem indistAt_symm {s : ℕ} {θ lam : Fin m} (h : IndistAt s θ lam) :
    IndistAt s lam θ := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨h2, h1⟩

theorem indistAt_trans {s : ℕ} {θ lam mu : Fin m}
    (h1 : IndistAt s θ lam) (h2 : IndistAt s lam mu) : IndistAt s θ mu := by
  rcases h1 with rfl | ⟨a1, _⟩
  · exact h2
  · rcases h2 with rfl | ⟨_, b2⟩
    · exact Or.inr ⟨a1, ‹s ≤ (lam : ℕ)›⟩
    · exact Or.inr ⟨a1, b2⟩

instance instDecIndistAt (s : ℕ) (θ : Fin m) : DecidablePred (IndistAt s θ) := by
  intro lam
  unfold IndistAt
  infer_instance

/-- The class of `θ` at order `s`. -/
def classAt (s : ℕ) (θ : Fin m) : Finset (Fin m) :=
  univ.filter (fun lam => IndistAt s θ lam)

theorem mem_classAt {s : ℕ} {θ lam : Fin m} :
    lam ∈ classAt s θ ↔ IndistAt s θ lam := by
  classical
  simp [classAt]

theorem classAt_zero (θ : Fin m) : classAt 0 θ = univ :=
  eq_univ_iff_forall.mpr fun _ => mem_classAt.mpr (Or.inr ⟨Nat.zero_le _, Nat.zero_le _⟩)

/-- From order one on, no class is the whole world set. -/
theorem classAt_ne_univ (hm : 2 ≤ m) {s : ℕ} (hs : 1 ≤ s) (θ : Fin m) :
    classAt s θ ≠ univ := by
  classical
  intro hcon
  have h0 : IndistAt s θ (⟨0, by omega⟩ : Fin m) :=
    mem_classAt.mp (by rw [hcon]; exact mem_univ _)
  have h1 : IndistAt s θ (⟨1, by omega⟩ : Fin m) :=
    mem_classAt.mp (by rw [hcon]; exact mem_univ _)
  have hθ0 : θ = (⟨0, by omega⟩ : Fin m) := by
    rcases h0 with h | ⟨_, h2⟩
    · exact h
    · simp only at h2; omega
  rcases h1 with h | ⟨h1', _⟩
  · rw [hθ0] at h
    exact absurd (congrArg Fin.val h) (by simp)
  · rw [hθ0] at h1'
    simp only at h1'
    omega

/-! ## The two orders -/

/-- Every class at order `s` has a common safe answer, in the ACTUAL `selectedRadius`
geometry of the sparse family. -/
def DecidableAt (s : ℕ) : Prop := ∀ θ : Fin m, CommonSafe (m := m) sparseSup (classAt s θ)

/-- Every class at order `s` is a singleton. -/
def IdentifiableAt (s : ℕ) : Prop := ∀ θ lam : Fin m, IndistAt s θ lam → θ = lam

theorem decidableAt_of_one_le (hm : 2 ≤ m) {s : ℕ} (hs : 1 ≤ s) :
    DecidableAt (m := m) s :=
  fun θ => (sparse_commonSafe_iff hm _).mpr (classAt_ne_univ hm hs θ)

theorem not_decidableAt_zero (hm : 2 ≤ m) : ¬ DecidableAt (m := m) 0 := by
  intro h
  have hc := h ⟨0, by omega⟩
  rw [classAt_zero] at hc
  exact ((sparse_commonSafe_iff hm univ).mp hc) rfl

theorem identifiableAt_iff (hm : 2 ≤ m) (s : ℕ) :
    IdentifiableAt (m := m) s ↔ m - 1 ≤ s := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hA : (m - 2 : ℕ) < m := by omega
    have hB : (m - 1 : ℕ) < m := by omega
    have heq := h ⟨m - 2, hA⟩ ⟨m - 1, hB⟩ (Or.inr ⟨by simp only; omega, by simp only; omega⟩)
    have := congrArg Fin.val heq
    simp only at this
    omega
  · intro hs θ lam hind
    rcases hind with h | ⟨h1, h2⟩
    · exact h
    · have ht := θ.isLt
      have hl := lam.isLt
      exact Fin.ext (by omega)

/-! ## The safe sets are the real ones, and they overlap

`CommonSafe` is defined upstream by `selectedRadius (components (sparseSup w)) {j} = 0`,
and `sparse_safe_iff` proves that holds exactly when `j != w`.  So the safe set of world
`w` IS `univ.erase w` --- read off the geometry, not assigned --- and the statements below
are phrased in that vocabulary.  At `m = 3` they read `{1,2}`, `{0,2}`, `{0,1}`. -/

/-- **Any two worlds share a safe answer.**  The safe sets genuinely overlap: no world's
safe set is contained in the complement of another's. -/
theorem safe_sets_overlap (hm : 3 ≤ m) (w w' : Fin m) :
    CommonSafe (m := m) sparseSup {w, w'} := by
  classical
  refine (sparse_commonSafe_iff (by omega) _).mpr ?_
  intro hc
  have hcard := congrArg Finset.card hc
  rw [card_univ, Fintype.card_fin] at hcard
  have hle : ({w, w'} : Finset (Fin m)).card ≤ 2 :=
    le_trans (card_insert_le _ _) (by simp)
  omega

/-- **But the whole family shares none.**  The total intersection of the safe sets is
empty, which is precisely the obstruction the budget theorem consumes. -/
theorem no_common_safe_all (hm : 2 ≤ m) : ¬ CommonSafe (m := m) sparseSup univ :=
  fun h => ((sparse_commonSafe_iff hm univ).mp h) rfl

/-! ## What the budget theorem consumes -/

/-- **At order zero the class is the whole world set, and its safe answers do not
intersect.**  That is exactly the hypothesis `decision_budget_log_delta` needs, with
`K = m`; the class is supplied by the geometry rather than assumed. -/
theorem obstruction_at_order_zero (hm : 2 ≤ m) (θ : Fin m) :
    Unsafe (m := m) sparseSup (classAt 0 θ) := by
  rw [classAt_zero]
  exact (sparse_unsafe_iff hm univ).mpr rfl

/-- **The two orders come apart, and the gap grows with the family.**

`s_dec = 1`: one bit of resolution already leaves every class with a common safe answer,
because the safe sets overlap.  `s_id = m - 1`: identification needs the whole family
resolved.  Deciding is cheaper than identifying, and the reason is the geometry of the
safe sets, not a nuisance coordinate bolted on. -/
theorem decide_order_lt_identify_order (hm : 3 ≤ m) :
    ¬ DecidableAt (m := m) 0 ∧ DecidableAt (m := m) 1 ∧
      ¬ IdentifiableAt (m := m) 1 ∧ IdentifiableAt (m := m) (m - 1) := by
  have hm2 : 2 ≤ m := by omega
  refine ⟨not_decidableAt_zero hm2, decidableAt_of_one_le hm2 le_rfl, ?_, ?_⟩
  · rw [identifiableAt_iff hm2]
    omega
  · rw [identifiableAt_iff hm2]


/-! ## The matching upper bound at order `s_safe` -/

/-- **The decoder at order `s_safe`.**  Resolve the class, answer in its common safe set.
The answer is safe for the TRUE world, because the true world lies in its own class --- so
the decoder is correct, not merely consistent with the class it identified.  By
`sparse_safe_iff` safety of `{j}` for world `w` is exactly `j != w`, so the conclusion is
stated that way. -/
theorem decoder_safe_at_truth (hm : 2 ≤ m) {s : ℕ} (hs : 1 ≤ s) (θ : Fin m) :
    ∃ j : Fin m, (∀ w ∈ classAt s θ, j ≠ w) ∧ j ≠ θ := by
  obtain ⟨j, hj⟩ := decidableAt_of_one_le hm hs θ
  refine ⟨j, fun w hw => (sparse_safe_iff hm w j).mp (hj w hw), ?_⟩
  exact (sparse_safe_iff hm θ j).mp (hj θ (mem_classAt.mpr (indistAt_refl s θ)))

/-- **The union bound the decoder's error obeys.**  With `K` pairwise tests each at level
`delta/K`, the decoder errs at most `delta`.  This is the only place the answer count
enters the upper bound. -/
theorem decoder_union_bound (K : ℕ) (hK : 0 < K) (δ : ℝ) (err : Fin K → ℝ)
    (hbd : ∀ i, err i ≤ δ / (K : ℝ)) : ∑ i, err i ≤ δ := by
  have hKr : ((K : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin K))) => hbd i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel₀ _ hKr] at hsum
  exact hsum

/-- **The two bounds are of the same order in BOTH parameters.**

The lower side is `decision_budget_log_delta` at the order-zero obstruction, of size
`((1-delta)/K) log(1/delta) - 2/e` over `C h^{2s}`.  The upper side is the decoder above
with `K` pairwise tests, of size `log K + log(1/delta)` over the same `C h^{2s}`.  Once
`log(1/delta)` clears a threshold depending on `K` alone, the second is at most a
`K`-dependent constant times the first: the exponent in `h` agrees exactly and the
dependence on `delta` agrees up to that constant. -/
theorem bounds_same_order (K : ℕ) (hK : 0 < K) (δ L : ℝ)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hL1 : 1 ≤ L)
    (hLK : 8 * (K : ℝ) ≤ L * Real.exp 1) :
    Real.log K + L
      ≤ 4 * (K : ℝ) * (Real.log K + 1)
        * ((1 - δ) / (K : ℝ) * L - 2 * (Real.exp 1)⁻¹) := by
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hA : (0 : ℝ) ≤ Real.log K := Real.log_natCast_nonneg K
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : L / (2 * (K : ℝ)) ≤ (1 - δ) / (K : ℝ) * L := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hK0]
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
    have hd : (0 : ℝ) ≤ 1 - δ - 1 / 2 := by linarith
    have hprod : (0 : ℝ) ≤ (1 - δ - 1 / 2) * (L * (K : ℝ)) :=
      mul_nonneg hd (le_of_lt (mul_pos hL0 hK0))
    nlinarith [hprod]
  have h2 : 2 * (Real.exp 1)⁻¹ ≤ L / (4 * (K : ℝ)) := by
    have key : 2 * (Real.exp 1)⁻¹ * (4 * (K : ℝ)) = 8 * (K : ℝ) / Real.exp 1 := by
      field_simp
      ring
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (K : ℝ)), key, div_le_iff₀ hE]
    linarith [hLK]
  have hhalf : L / (2 * (K : ℝ)) - L / (4 * (K : ℝ)) = L / (4 * (K : ℝ)) := by
    field_simp
    ring
  have h3 : L / (4 * (K : ℝ)) ≤ (1 - δ) / (K : ℝ) * L - 2 * (Real.exp 1)⁻¹ := by
    linarith [h1, h2, hhalf.le, hhalf.ge]
  have h4 : 4 * (K : ℝ) * (Real.log K + 1) * (L / (4 * (K : ℝ)))
      = (Real.log K + 1) * L := by
    field_simp
  have h5 : Real.log K + L ≤ (Real.log K + 1) * L := by nlinarith [hA, hL1]
  have hpos : (0 : ℝ) ≤ 4 * (K : ℝ) * (Real.log K + 1) :=
    mul_nonneg (by linarith) (by linarith)
  have h6 := mul_le_mul_of_nonneg_left h3 hpos
  linarith [h5, h6, h4.le, h4.ge]

/-! ## Audit -/

#print axioms indistAt_trans
#print axioms classAt_ne_univ
#print axioms decidableAt_of_one_le
#print axioms not_decidableAt_zero
#print axioms identifiableAt_iff
#print axioms safe_sets_overlap
#print axioms no_common_safe_all
#print axioms obstruction_at_order_zero
#print axioms decide_order_lt_identify_order
#print axioms decoder_safe_at_truth
#print axioms decoder_union_bound
#print axioms bounds_same_order

end CIGAMF.P13.PaperBGeometry
