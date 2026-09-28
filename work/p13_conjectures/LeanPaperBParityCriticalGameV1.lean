import «LeanPaperBParityCriticalV1»

/-!
# Paper B: the critical game of the parity channel (`parity_critical_game`)

The parity channel (`LeanPaperBParityChannelV1`) has
- worlds `w : Fin m`, paper world `w + 1`;
- queries `q : Fin m`, with `q = 0` the dummy.

Query `q ≥ 1` has mask `−1` exactly in paper world `q`.

## WHAT IS PROVED

* `chanKL` — the per-query KL divergence of the channel between worlds `w` and `l` at query
  `q`, written on the channel's own densities.  `chanKL_eq_channel` shows that it is the KL of
  `parChan`'s densities, by `rfl`.
* `kappa_eq_channel` — at a query `q ≥ 1` it is `parKL q σ (mask_w) (mask_l) h`;
  `kappa_blind` — it is `0` at the dummy and at every query naming neither world.
* **`parity_critical_game`** — for identification at world `w` with `m ≥ 2`, and
  `s = min(w + 1, m − 1)`:

      h^{-2s} · max_α min_{l ≠ w} Σ_q α_q κ_q(l; h)  →  c_s,

  where `c_s = cj s σ = (1/2) ∫ a_s² / p₀ > 0` (`cj_pos`).  So the critical game value is
  `G* = c_{w+1}` for paper worlds `w + 1 ≤ m − 1`, and `G* = c_{m−1}` for the last world.

  It is `critical_limit` fed by `expansion_hyps` (`LeanPaperBCriticalGameV1`), with the
  per-query expansions `kl_limit` (`LeanPaperBParityCriticalV1`).
-/

namespace CIGAMF.P13.PaperBParityCriticalGame

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBParityChannel
open CIGAMF.P13.PaperBParityCritical CIGAMF.P13.PaperBCriticalGame CIGAMF.P13.PaperBProtocol

variable (m : ℕ)

/-- The per-query KL divergence of the parity channel between worlds `w` and `l` at query `q`. -/
noncomputable def chanKL (σ h : ℝ) (w l q : Fin m) : ℝ :=
  ∫ y, parDens m σ h w q y * Real.log (parDens m σ h w q y / parDens m σ h l q y)

/-- It is the KL of the channel's own densities. -/
theorem chanKL_eq_channel (σ h : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hm : 0 < m) (w l q : Fin m) :
    chanKL m σ h w l q = ∫ y, (parChan m σ h hσ hh hm).dens w q y *
      Real.log ((parChan m σ h hσ hh hm).dens w q y / (parChan m σ h hσ hh hm).dens l q y) := rfl

/-- **At a parity query it is the two-mask KL.** -/
theorem kappa_eq_channel (σ h : ℝ) (w l q : Fin m) (hq : (q : ℕ) ≠ 0) :
    chanKL m σ h w l q = parKL q σ (maskR q ((w : ℕ) + 1)) (maskR q ((l : ℕ) + 1)) h := by
  unfold chanKL parKL klInt parDens
  simp only [hq, if_false]

theorem self_log_self (a : ℝ) : a * Real.log (a / a) = 0 := by
  rcases eq_or_ne a 0 with h | h
  · simp [h]
  · rw [div_self h, Real.log_one, mul_zero]

/-- **A blind query carries nothing**: the dummy, or equal masks. -/
theorem kappa_blind (σ h : ℝ) (w l q : Fin m)
    (hb : (q : ℕ) = 0 ∨ maskR q ((w : ℕ) + 1) = maskR q ((l : ℕ) + 1)) :
    chanKL m σ h w l q = 0 := by
  unfold chanKL
  have heq : ∀ y, parDens m σ h l q y = parDens m σ h w q y := by
    intro y
    unfold parDens
    rcases hb with h0 | hmask
    · simp [h0]
    · split_ifs
      · rfl
      · rw [hmask]
  simp_rw [heq, self_log_self]
  simp

theorem chanKL_nonneg (σ h : ℝ) (hσ : 0 < σ) (w l q : Fin m) : 0 ≤ chanKL m σ h w l q := by
  by_cases hq : (q : ℕ) = 0
  · rw [kappa_blind m σ h w l q (Or.inl hq)]
  · rw [kappa_eq_channel m σ h w l q hq]
    exact parKL_nonneg _ σ _ _ h hσ

/-! ## Visibility and orders -/

/-- Query `q` sees the pair `(w, l)`. -/
def Vis (w l q : Fin m) : Prop := (q : ℕ) ≠ 0 ∧ maskR q ((w : ℕ) + 1) ≠ maskR q ((l : ℕ) + 1)

theorem vis_iff (w l q : Fin m) (hwl : w ≠ l) :
    Vis m w l q ↔ (q : ℕ) ≠ 0 ∧ ((q : ℕ) = (w : ℕ) + 1 ∨ (q : ℕ) = (l : ℕ) + 1) := by
  unfold Vis
  have hne : (w : ℕ) + 1 ≠ (l : ℕ) + 1 := by
    intro e; apply hwl; exact Fin.ext (by omega)
  rw [masks_differ_iff _ _ _ hne]

theorem maskPair_of_vis (w l q : Fin m) (hv : Vis m w l q) :
    MaskPair (maskR q ((w : ℕ) + 1)) (maskR q ((l : ℕ) + 1)) := by
  rcases maskR_pm q ((w : ℕ) + 1) with h1 | h1 <;> rcases maskR_pm q ((l : ℕ) + 1) with h2 | h2
  · exact absurd (h1.trans h2.symm) hv.2
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hv.2

/-- The least visible query of an alternative. -/
def ord (w : Fin m) (l : Fin m) : ℕ :=
  if (w : ℕ) + 1 < m ∧ (l : ℕ) + 1 < m then min ((w : ℕ) + 1) ((l : ℕ) + 1)
  else if (w : ℕ) + 1 < m then (w : ℕ) + 1 else (l : ℕ) + 1

/-- The critical order. -/
def sOrd (w : Fin m) : ℕ := min ((w : ℕ) + 1) (m - 1)

theorem ord_pos (w l : Fin m) : 1 ≤ ord m w l := by
  unfold ord; split_ifs <;> omega

theorem ord_lt (w l : Fin m) (hwl : w ≠ l) : ord m w l < m := by
  have hwl' : (w : ℕ) ≠ (l : ℕ) := fun e => hwl (Fin.ext e)
  have := w.isLt; have := l.isLt
  unfold ord; split_ifs <;> omega

theorem ord_vis (w l : Fin m) (hwl : w ≠ l) :
    Vis m w l ⟨ord m w l, ord_lt m w l hwl⟩ := by
  rw [vis_iff m w l _ hwl]
  have hwl' : (w : ℕ) ≠ (l : ℕ) := fun e => hwl (Fin.ext e)
  have := w.isLt; have := l.isLt
  simp only
  unfold ord; split_ifs <;> omega

theorem ord_le_of_vis (w l q : Fin m) (hwl : w ≠ l) (hv : Vis m w l q) : ord m w l ≤ q := by
  rw [vis_iff m w l q hwl] at hv
  have := q.isLt
  unfold ord; split_ifs <;> omega

theorem ord_le_s (w l : Fin m) (hwl : w ≠ l) : ord m w l ≤ sOrd m w := by
  have hwl' : (w : ℕ) ≠ (l : ℕ) := fun e => hwl (Fin.ext e)
  have := w.isLt; have := l.isLt
  unfold ord sOrd; split_ifs <;> omega

theorem sOrd_pos (w : Fin m) (hm : 2 ≤ m) : 1 ≤ sOrd m w := by
  unfold sOrd; omega

theorem sOrd_lt (w : Fin m) : sOrd m w < m := by
  have := w.isLt; unfold sOrd; omega

/-! ## The expansion data -/

open Classical in
noncomputable def sqD (w : Fin m) (q : Fin m) (l : {l : Fin m // l ≠ w}) : ℕ :=
  if Vis m w l.1 q then (q : ℕ) else 0

open Classical in
noncomputable def cD (σ : ℝ) (w : Fin m) (q : Fin m) (l : {l : Fin m // l ≠ w}) : ℝ :=
  if Vis m w l.1 q then cj q σ else 0

theorem cD_nonneg (σ : ℝ) (hσ : 0 < σ) (w q : Fin m) (l : {l : Fin m // l ≠ w}) :
    0 ≤ cD m σ w q l := by
  classical
  unfold cD
  split_ifs with hv
  · exact (cj_pos q (Nat.pos_of_ne_zero hv.1) σ hσ).le
  · exact le_rfl

theorem cD_pos_iff (σ : ℝ) (hσ : 0 < σ) (w q : Fin m) (l : {l : Fin m // l ≠ w}) :
    0 < cD m σ w q l ↔ Vis m w l.1 q := by
  classical
  unfold cD
  split_ifs with hv
  · exact ⟨fun _ => hv, fun _ => cj_pos q (Nat.pos_of_ne_zero hv.1) σ hσ⟩
  · exact ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h hv⟩

theorem hexp_all (σ : ℝ) (hσ : 0 < σ) (w q : Fin m) (l : {l : Fin m // l ≠ w}) :
    Tendsto (fun h => chanKL m σ h w l.1 q / h ^ (2 * sqD m w q l)) (𝓝[>] 0)
      (𝓝 (cD m σ w q l)) := by
  classical
  unfold sqD cD
  split_ifs with hv
  · have hq : (q : ℕ) ≠ 0 := hv.1
    have := kl_limit q (Nat.pos_of_ne_zero hq) σ _ _ hσ (maskPair_of_vis m w l.1 q hv)
    refine this.congr fun h => ?_
    rw [kappa_eq_channel m σ h w l.1 q hq]
  · have h0 : ∀ h, chanKL m σ h w l.1 q = 0 := by
      intro h
      apply kappa_blind
      by_contra hc
      push Not at hc
      exact hv hc
    simp only [h0, zero_div]
    exact tendsto_const_nhds

/-! ## The critical game value -/

/-- For a critical alternative the critical coefficient is `c_s` at the query `s` and `0`
elsewhere. -/
theorem crit_coeff (σ : ℝ) (hm : 2 ≤ m) (w : Fin m) (l : {l : Fin m // l ≠ w})
    (hl : ord m w l.1 = sOrd m w) (q : Fin m) :
    (if sqD m w q l = sOrd m w then cD m σ w q l else 0)
      = if (q : ℕ) = sOrd m w then cj (sOrd m w) σ else 0 := by
  classical
  have hs1 := sOrd_pos m w hm
  unfold sqD cD
  by_cases hqs : (q : ℕ) = sOrd m w
  · have hv : Vis m w l.1 q := by
      rw [vis_iff m w l.1 q (Ne.symm l.2)]
      refine ⟨by omega, ?_⟩
      have hwl' : (w : ℕ) ≠ (l.1 : ℕ) := fun e => l.2 (Fin.ext e).symm
      have := w.isLt; have := l.1.isLt
      unfold ord sOrd at *
      split_ifs at hl <;> omega
    simp only [hv, if_true, hqs]
  · by_cases hv : Vis m w l.1 q
    · simp [hv, hqs]
    · simp only [hv, if_false, hqs]
      have : (0 : ℕ) ≠ sOrd m w := by omega
      simp [this]

/-- The value of a game whose coefficients are `C` at one query and `0` elsewhere, for every
alternative, is `C`. -/
theorem gval_single {Q L : Type*} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    (S : Finset L) (hS : S.Nonempty) (q0 : Q) (C : ℝ) (hC : 0 ≤ C) (f : Q → L → ℝ)
    (hf : ∀ l ∈ S, ∀ q, f q l = if q = q0 then C else 0) :
    gval S hS f = C := by
  apply le_antisymm
  · refine gval_le S hS f C fun α hα => ?_
    obtain ⟨l, hl⟩ := hS
    refine (inner_le_at S ⟨l, hl⟩ f α l hl).trans ?_
    have : ∑ q, α q * f q l = α q0 * C := by
      rw [Finset.sum_eq_single q0]
      · rw [hf l hl q0, if_pos rfl]
      · intro q _ hq; rw [hf l hl q, if_neg hq, mul_zero]
      · intro h; exact absurd (Finset.mem_univ q0) h
    rw [this]
    calc α q0 * C ≤ 1 * C := mul_le_mul_of_nonneg_right (alloc_le_one hα q0) hC
      _ = C := one_mul C
  · set α : Q → ℝ := fun q => if q = q0 then 1 else 0
    have hα : Alloc α := by
      refine ⟨fun q => by simp only [α]; split_ifs <;> norm_num, ?_⟩
      simp [α]
    refine le_trans ?_ (le_gval S hS f hα)
    unfold CIGAMF.P13.PaperBCriticalGame.inner
    refine Finset.le_inf' hS _ fun l hl => ?_
    have : ∑ q, α q * f q l = C := by
      rw [Finset.sum_eq_single q0]
      · simp [α, hf l hl q0]
      · intro q _ hq; simp [α, hq]
      · intro h; exact absurd (Finset.mem_univ q0) h
    rw [this]

/-- **The critical game of the parity channel.**  For identification at world `w` (paper world
`w + 1`), `m ≥ 2`, `s = min(w + 1, m − 1)`: the rescaled game value converges to `c_s`. -/
theorem parity_critical_game [NeZero m] (σ : ℝ) (hσ : 0 < σ) (hm : 2 ≤ m) (w : Fin m)
    (hS : (Finset.univ : Finset {l : Fin m // l ≠ w}).Nonempty) :
    Tendsto (fun h => gval (Finset.univ : Finset {l : Fin m // l ≠ w}) hS
        (fun q l => chanKL m σ h w l.1 q / h ^ (2 * sOrd m w)))
      (𝓝[>] 0) (𝓝 (cj (sOrd m w) σ)) := by
  classical
  -- the expansion hypotheses
  obtain ⟨hA, hB⟩ := expansion_hyps (Q := Fin m) (L := {l : Fin m // l ≠ w})
    (sqD m w) (cD m σ w) (fun h q l => chanKL m σ h w l.1 q)
    (fun q l => hexp_all m σ hσ w q l)
    (fun q l hc h => by
      apply kappa_blind
      by_contra hcon
      push Not at hcon
      have hv : Vis m w l.1 q := hcon
      have := (cD_pos_iff m σ hσ w q l).mpr hv
      rw [hc] at this
      exact lt_irrefl 0 this)
    (fun q l => cD_nonneg m σ hσ w q l)
    (fun l => ord m w l.1)
    (fun l => ⟨⟨ord m w l.1, ord_lt m w l.1 (Ne.symm l.2)⟩, by
      refine ⟨(cD_pos_iff m σ hσ w _ l).mpr (ord_vis m w l.1 (Ne.symm l.2)), ?_⟩
      unfold sqD
      simp [ord_vis m w l.1 (Ne.symm l.2)]⟩)
    (fun l q hc => by
      have hv := (cD_pos_iff m σ hσ w q l).mp hc
      unfold sqD
      simp only [hv, if_true]
      exact ord_le_of_vis m w l.1 q (Ne.symm l.2) hv)
    (sOrd m w) (fun l => ord_le_s m w l.1 (Ne.symm l.2))
  -- a critical alternative exists
  set Crit : Finset {l : Fin m // l ≠ w} :=
    Finset.univ.filter (fun l => ord m w l.1 = sOrd m w) with hCrit
  have hCne : Crit.Nonempty := by
    have := w.isLt
    by_cases hw : (w : ℕ) + 1 < m
    · refine ⟨⟨⟨(w : ℕ) + 1, hw⟩, fun e => by
        have := congrArg Fin.val e; simp at this⟩, ?_⟩
      simp only [hCrit, Finset.mem_filter, Finset.mem_univ, true_and]
      unfold ord sOrd
      split_ifs <;> simp_all <;> omega
    · refine ⟨⟨⟨m - 2, by omega⟩, fun e => by
        have := congrArg Fin.val e; simp at this; omega⟩, ?_⟩
      simp only [hCrit, Finset.mem_filter, Finset.mem_univ, true_and]
      unfold ord sOrd
      split_ifs <;> simp_all <;> omega
  -- the critical limit
  have hlim := critical_limit (Finset.univ : Finset {l : Fin m // l ≠ w}) hS Crit hCne
    (Finset.subset_univ _) (fun h q l => chanKL m σ h w l.1 q / h ^ (2 * sOrd m w))
    (fun h q l => div_nonneg (chanKL_nonneg m σ h hσ w l.1 q)
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg h) _))
    (fun q l => if sqD m w q l = sOrd m w then cD m σ w q l else 0)
    (fun q l => by split_ifs; exact cD_nonneg m σ hσ w q l; exact le_rfl)
    (fun l hl q => hA l (by simpa [hCrit] using hl) q)
    (fun l _ hl => hB l (lt_of_le_of_ne (ord_le_s m w l.1 (Ne.symm l.2))
      (by simpa [hCrit] using hl)))
  -- the critical value is c_s
  have hval : gval Crit hCne (fun q l => if sqD m w q l = sOrd m w then cD m σ w q l else 0)
      = cj (sOrd m w) σ :=
    gval_single Crit hCne ⟨sOrd m w, sOrd_lt m w⟩ (cj (sOrd m w) σ)
      (cj_pos _ (by have := sOrd_pos m w hm; omega) σ hσ).le _
      (fun l hl q => by
        rw [crit_coeff m σ hm w l (by simpa [hCrit] using hl) q]
        congr 1
        simp only [Fin.ext_iff])
  rw [hval] at hlim
  exact hlim

/-- The hypotheses are satisfiable: `m = 3`, `σ = 1`, every world. -/
theorem parity_critical_game_satisfiable :
    ∃ (m : ℕ) (_ : NeZero m) (σ : ℝ), 0 < σ ∧ 2 ≤ m ∧ ∀ w : Fin m,
      (Finset.univ : Finset {l : Fin m // l ≠ w}).Nonempty := by
  refine ⟨3, ⟨by norm_num⟩, 1, one_pos, by norm_num, fun w => ?_⟩
  by_cases hw : w = 0
  · exact ⟨⟨1, by rw [hw]; decide⟩, Finset.mem_univ _⟩
  · exact ⟨⟨0, fun e => hw e.symm⟩, Finset.mem_univ _⟩

end CIGAMF.P13.PaperBParityCriticalGame

#print axioms CIGAMF.P13.PaperBParityCriticalGame.kappa_eq_channel
#print axioms CIGAMF.P13.PaperBParityCriticalGame.kappa_blind
#print axioms CIGAMF.P13.PaperBParityCriticalGame.parity_critical_game
#print axioms CIGAMF.P13.PaperBParityCriticalGame.parity_critical_game_satisfiable
