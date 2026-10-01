import «LeanPaperBFamilyChannelV1»

/-!
# Paper B: the latent family's safe sets, derived from its losses

`famSafe` (`LeanPaperBFamilyChannelV1`) was STATED as the correspondence that
`EXP_paperB_construction` computes.  This module derives it in Lean from the definitions.

The family is `F_{u,v}(z) = 3u z_1 - 2 z_2 - 2 z_3 + v z_4 ... z_{r+3}` on the sign cube
`{±1}^{r+3}` with the uniform reference, and the deployment support is
`K = {(t,t,t,1,...,1) : t = ±1}`.

* `sum_zero_of_flip`: a cube sum vanishes when flipping one coordinate negates the summand.
* `resp_eq`: the single-coordinate response `Q_j(b) = E[F | z_j = b]` is `c_j * b`, with
  `c = (3u, -2, -2, 0, ..., 0)`, for `r >= 2`.  (For `r = 1` the tail response would carry `v`.)
* `loss_eq`: retaining coordinate `j`, the half-oscillation of the residual `F - Q_j` on `K` is
  `|3u - 4 - c_j|`: `4`, `|3u - 2|`, `|3u - 2|`, then `|3u - 4|`.  It does not depend on `v`.
* `safeOf`: the `eps`-safe coordinates, those within `eps` of every other loss.
* **`famSafe_derived`**: for `0 <= eps < 1` and `r >= 2`, `safeOf = famSafe`: at `u = +1` every
  coordinate but the first is safe, at `u = -1` only the first.
-/

namespace CIGAMF.P13.PaperBFamilySafe

open Finset
open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBFamilyChannel

variable {r : ℕ}

/-! ## 1. Flipping a coordinate -/

/-- Flip coordinate `k`. -/
def flip {n : ℕ} (k : Fin n) (z : Fin n → Bool) : Fin n → Bool := Function.update z k (!(z k))

theorem flip_flip {n : ℕ} (k : Fin n) (z : Fin n → Bool) : flip k (flip k z) = z := by
  funext i
  unfold flip
  by_cases h : i = k
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem flip_self {n : ℕ} (k : Fin n) (z : Fin n → Bool) : flip k z k = !(z k) := by
  simp [flip]

theorem flip_ne {n : ℕ} (k : Fin n) (z : Fin n → Bool) (i : Fin n) (h : i ≠ k) :
    flip k z i = z i := by
  simp [flip, Function.update_of_ne h]

/-- **A cube sum vanishes when flipping one coordinate negates the summand.** -/
theorem sum_zero_of_flip {n : ℕ} (k : Fin n) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ z, f (flip k z) = - f z) : ∑ z, f z = 0 := by
  have hinv : Function.Involutive (flip k) := flip_flip k
  have h := Fintype.sum_equiv hinv.toPerm (fun z => f (flip k z)) f (fun z => rfl)
  simp_rw [hf, Finset.sum_neg_distrib] at h
  linarith

/-! ## 2. The family and its single-coordinate responses -/

/-- The three head coordinates and the tail coordinates. -/
def c0 : Fin (r + 3) := ⟨0, by omega⟩
def c1 : Fin (r + 3) := ⟨1, by omega⟩
def c2 : Fin (r + 3) := ⟨2, by omega⟩
def tl (i : Fin r) : Fin (r + 3) := ⟨(i : ℕ) + 3, by omega⟩

/-- **The family** `F_{u,v}` on `{±1}^{r+3}`. -/
noncomputable def F (u v : ℝ) (z : Fin (r + 3) → Bool) : ℝ :=
  3 * u * sgnB (z c0) - 2 * sgnB (z c1) - 2 * sgnB (z c2) + v * ∏ i : Fin r, sgnB (z (tl i))

/-- The indicator of `z_j = b`. -/
noncomputable def ind (j : Fin (r + 3)) (b : Bool) (z : Fin (r + 3) → Bool) : ℝ :=
  if z j = b then 1 else 0

/-- The number of points with `z_j = b`. -/
noncomputable def cnt (j : Fin (r + 3)) (b : Bool) : ℝ := ∑ z, ind j b z

theorem cnt_pos (j : Fin (r + 3)) (b : Bool) : 0 < cnt j b := by
  unfold cnt
  have h1 : ind j b (fun _ => b) = 1 := by simp [ind]
  have hnn : ∀ z, 0 ≤ ind j b z := fun z => by unfold ind; split_ifs <;> norm_num
  have := Finset.single_le_sum (fun z _ => hnn z) (Finset.mem_univ (fun _ : Fin (r + 3) => b))
  rw [h1] at this
  linarith

/-- The single-coordinate response `E[F | z_j = b]`. -/
noncomputable def resp (u v : ℝ) (j : Fin (r + 3)) (b : Bool) : ℝ :=
  (∑ z, ind j b z * F u v z) / cnt j b

/-- The response coefficients `(3u, -2, -2, 0, ..., 0)`. -/
noncomputable def coef (u : ℝ) (j : Fin (r + 3)) : ℝ :=
  if (j : ℕ) = 0 then 3 * u else if (j : ℕ) = 1 ∨ (j : ℕ) = 2 then -2 else 0

theorem sgnB_not (b : Bool) : sgnB (!b) = - sgnB b := by cases b <;> simp [sgnB]

/-- A coordinate average: `sum_z [z_j = b] s(z_i)` is `cnt * s(b)` at `i = j` and `0` otherwise. -/
theorem sum_ind_coord (j i : Fin (r + 3)) (b : Bool) :
    ∑ z, ind j b z * sgnB (z i) = if i = j then cnt j b * sgnB b else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    unfold cnt
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold ind
    split_ifs with h
    · rw [h]
    · simp
  · rw [if_neg hij]
    refine sum_zero_of_flip i _ fun z => ?_
    unfold ind
    rw [flip_ne i z j (Ne.symm hij), flip_self, sgnB_not]
    ring

/-- The tail product averages to zero on `z_j = b`, when `r >= 2`. -/
theorem sum_ind_tail (hr : 2 ≤ r) (j : Fin (r + 3)) (b : Bool) :
    ∑ z, ind j b z * ∏ i : Fin r, sgnB (z (tl i)) = 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin r, tl i0 ≠ j := by
    by_cases h : tl (⟨0, by omega⟩ : Fin r) = j
    · refine ⟨⟨1, by omega⟩, fun h' => ?_⟩
      rw [← h] at h'
      simp [tl, Fin.ext_iff] at h'
    · exact ⟨⟨0, by omega⟩, h⟩
  refine sum_zero_of_flip (tl i0) _ fun z => ?_
  unfold ind
  rw [flip_ne (tl i0) z j (Ne.symm hi0)]
  have hprod : ∏ i : Fin r, sgnB (flip (tl i0) z (tl i))
      = - ∏ i : Fin r, sgnB (z (tl i)) := by
    have hpt : ∀ i : Fin r, sgnB (flip (tl i0) z (tl i))
        = (if i = i0 then -1 else 1) * sgnB (z (tl i)) := by
      intro i
      by_cases h : i = i0
      · subst h; rw [flip_self, sgnB_not, if_pos rfl]; ring
      · have : tl i ≠ tl i0 := by
          intro e; apply h; simp [tl, Fin.ext_iff] at e; exact Fin.ext e
        rw [flip_ne _ _ _ this, if_neg h, one_mul]
    rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  rw [hprod]
  ring

theorem c_ne (a b : ℕ) (ha : a < r + 3) (hb : b < r + 3) (j : Fin (r + 3)) (hj : (j : ℕ) = b)
    (hab : a ≠ b) : (⟨a, ha⟩ : Fin (r + 3)) ≠ j := by
  intro e; apply hab; rw [← hj, ← e]

/-- **The single-coordinate response is `c_j * b`.** -/
theorem resp_eq (hr : 2 ≤ r) (u v : ℝ) (j : Fin (r + 3)) (b : Bool) :
    resp u v j b = coef u j * sgnB b := by
  unfold resp
  have hsum : ∑ z, ind j b z * F u v z
      = 3 * u * (∑ z, ind j b z * sgnB (z c0)) - 2 * (∑ z, ind j b z * sgnB (z c1))
        - 2 * (∑ z, ind j b z * sgnB (z c2))
        + v * (∑ z, ind j b z * ∏ i : Fin r, sgnB (z (tl i))) := by
    unfold F
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => by ring
  rw [hsum, sum_ind_coord, sum_ind_coord, sum_ind_coord, sum_ind_tail hr]
  have hc := (cnt_pos j b).ne'
  have ne_of : ∀ (c : Fin (r + 3)) (k : ℕ), (c : ℕ) = k → (j : ℕ) ≠ k → c ≠ j :=
    fun c k hck hjk e => hjk (by rw [← e, hck])
  unfold coef
  by_cases h0 : (j : ℕ) = 0
  · have e0 : (c0 : Fin (r + 3)) = j := Fin.ext (by simp [c0, h0])
    rw [if_pos e0, if_neg (ne_of c1 1 rfl (by omega)), if_neg (ne_of c2 2 rfl (by omega)),
      if_pos h0]
    field_simp <;> ring
  · have e0 : (c0 : Fin (r + 3)) ≠ j := fun e => h0 (by rw [← e]; rfl)
    rw [if_neg e0, if_neg h0]
    by_cases h1 : (j : ℕ) = 1
    · have e1 : (c1 : Fin (r + 3)) = j := Fin.ext (by simp [c1, h1])
      rw [if_pos e1, if_neg (ne_of c2 2 rfl (by omega)), if_pos (Or.inl h1)]
      field_simp <;> ring
    · have e1 : (c1 : Fin (r + 3)) ≠ j := fun e => h1 (by rw [← e]; rfl)
      by_cases h2 : (j : ℕ) = 2
      · have e2 : (c2 : Fin (r + 3)) = j := Fin.ext (by simp [c2, h2])
        rw [if_neg e1, if_pos e2, if_pos (Or.inr h2)]
        field_simp <;> ring
      · have e2 : (c2 : Fin (r + 3)) ≠ j := fun e => h2 (by rw [← e]; rfl)
        rw [if_neg e1, if_neg e2, if_neg (by omega)]
        simp

/-! ## 3. The losses on the support, and the safe sets -/

/-- The support point `(t, t, t, 1, ..., 1)`. -/
def Kpt (t : Bool) : Fin (r + 3) → Bool := fun i => if (i : ℕ) < 3 then t else true

/-- The residual after retaining coordinate `j`, at a support point. -/
noncomputable def resid (u v : ℝ) (j : Fin (r + 3)) (t : Bool) : ℝ :=
  F (r := r) u v (Kpt (r := r) t) - resp u v j (Kpt (r := r) t j)

/-- **The loss of retaining `j`**: half the oscillation of the residual on the support. -/
noncomputable def loss (u v : ℝ) (j : Fin (r + 3)) : ℝ :=
  |resid u v j true - resid u v j false| / 2

theorem F_Kpt (u v : ℝ) (t : Bool) : F (r := r) u v (Kpt (r := r) t) = (3 * u - 4) * sgnB t + v := by
  have e0 : Kpt (r := r) t c0 = t := by simp [Kpt, c0]
  have e1 : Kpt (r := r) t c1 = t := by simp [Kpt, c1]
  have e2 : Kpt (r := r) t c2 = t := by simp [Kpt, c2]
  have et : ∀ i : Fin r, Kpt (r := r) t (tl i) = true := fun i => by simp [Kpt, tl]
  unfold F
  rw [e0, e1, e2]
  simp only [et]
  have : sgnB true = 1 := by simp [sgnB]
  rw [this, Finset.prod_const_one]
  ring

theorem coef_tail (u : ℝ) (j : Fin (r + 3)) (hj : ¬ (j : ℕ) < 3) : coef u j = 0 := by
  unfold coef
  rw [if_neg (by omega), if_neg (by omega)]

/-- **The loss is `|3u - 4 - c_j|`**, and it does not depend on `v`. -/
theorem loss_eq (hr : 2 ≤ r) (u v : ℝ) (j : Fin (r + 3)) :
    loss u v j = |3 * u - 4 - coef u j| := by
  unfold loss resid
  rw [F_Kpt, F_Kpt, resp_eq hr, resp_eq hr]
  have hK : ∀ t, coef u j * sgnB (Kpt (r := r) t j) = coef u j * sgnB t := by
    intro t
    unfold Kpt
    by_cases hj : (j : ℕ) < 3
    · rw [if_pos hj]
    · rw [if_neg hj, coef_tail u j hj]; ring
  rw [hK, hK]
  have ht : sgnB true = 1 := by simp [sgnB]
  have hf : sgnB false = -1 := by simp [sgnB]
  rw [ht, hf, show (3 * u - 4) * 1 + v - coef u j * 1 - ((3 * u - 4) * -1 + v - coef u j * -1)
      = 2 * (3 * u - 4 - coef u j) by ring, abs_mul]
  norm_num

/-- The loss by coordinate: `4`, then `|3u - 2|` twice, then `|3u - 4|`. -/
theorem loss_cases (hr : 2 ≤ r) (u v : ℝ) (j : Fin (r + 3)) :
    loss u v j = if (j : ℕ) = 0 then 4 else if (j : ℕ) = 1 ∨ (j : ℕ) = 2 then |3 * u - 2|
      else |3 * u - 4| := by
  rw [loss_eq hr]
  unfold coef
  split_ifs
  · rw [show 3 * u - 4 - 3 * u = -4 by ring]; norm_num
  · rw [show 3 * u - 4 - -2 = 3 * u - 2 by ring]
  · rw [sub_zero]

/-- **The `eps`-safe coordinates**: those within `eps` of every other loss. -/
noncomputable def safeOf (u v ε : ℝ) : Finset (Fin (r + 3)) :=
  Finset.univ.filter fun j => ∀ j' : Fin (r + 3), loss u v j ≤ loss u v j' + ε

/-- **The safe sets, derived from the losses.**  For `r >= 2` and `0 <= eps < 1`, the `eps`-safe
coordinates at world `w` are exactly `famSafe r w`: at `u = +1` every coordinate but the first,
at `u = -1` only the first.  The nuisance `v` does not move them. -/
theorem famSafe_derived (hr : 2 ≤ r) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (w : Bool × Bool) :
    safeOf (r := r) (uOf w) (vOf w) ε = famSafe r w := by
  ext j
  simp only [safeOf, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc0 : ((c0 : Fin (r + 3)) : ℕ) = 0 := rfl
  have hc1 : ((c1 : Fin (r + 3)) : ℕ) = 1 := rfl
  cases hw : w.1
  · -- `u = -1`: losses `4, 5, 5, 7, ...`; only the first is safe
    have hu : uOf w = -1 := by simp [uOf, hw, sgnB]
    simp only [famSafe, hw, Bool.false_eq_true, if_false, Finset.mem_singleton, Fin.ext_iff,
      Fin.val_zero]
    rw [hu]
    constructor
    · intro h
      by_contra hj
      have h0 := h c0
      rw [loss_cases hr, loss_cases hr, if_neg hj, hc0, if_pos rfl] at h0
      split_ifs at h0 <;> norm_num at h0 <;> linarith
    · intro hj j'
      rw [loss_cases hr, loss_cases hr, if_pos hj]
      split_ifs <;> norm_num <;> linarith
  · -- `u = +1`: losses `4, 1, 1, 1, ...`; all but the first are safe
    have hu : uOf w = 1 := by simp [uOf, hw, sgnB]
    simp only [famSafe, hw, if_true, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq,
      Fin.ext_iff, Fin.val_zero]
    rw [hu]
    constructor
    · intro h hj
      have h1 := h c1
      rw [loss_cases hr, loss_cases hr, if_pos hj, hc1] at h1
      norm_num at h1
      linarith
    · intro hj j'
      rw [loss_cases hr, loss_cases hr, if_neg hj]
      split_ifs <;> norm_num <;> linarith

#print axioms sum_zero_of_flip
#print axioms resp_eq
#print axioms loss_eq
#print axioms famSafe_derived

end CIGAMF.P13.PaperBFamilySafe
