import «LeanPaperASacrificeV1»

/-!
# Sacrifice duality: the surrogate's dual margins price the repair

A general form of the sacrifice law, the repair frontier and the value bound of paper A, for any
finite set of cells and any pair of games, frozen and true. The centred construction is an
instance (Section 3), and its constants come back.

**Setting.** Cells `e : ι`. Two design values `Jf`, `Jt : (ι → ℝ) → ℝ` (the frozen and the true
game at a design), and the frozen value `Γ > 0`. The relative sacrifice is
`sac(w) = 1 - Jf(w)/Γ`.

**A certificate pair.**
* A *frozen certificate* `c : ι → ℝ` with `Jf(w) ≤ Σ_e w_e c_e` at every allocation. A mixture
  of frozen alternatives gives one, with `c_e` its average information on cell `e`. The
  *margin* of a cell is `1 - c_e/Γ`.
* A *repair certificate*: finitely many true load vectors `L_j`, with `Jt(w) ≤ Σ_e w_e L_j(e)`
  (the information of a true alternative), and weights `ν_j ≥ 0` that the margins cover:
  `Σ_j ν_j L_j(e) ≤ 1 - c_e/Γ` for every cell.

**What it gives.**
* `exchange`: `sac(w) ≥ Σ_e w_e (1 - c_e/Γ)`.
* `frontier_upper`: `Jt(w) · Σν ≤ sac(w)`, so `R(β) ≤ β/Σν`.
* `value_upper`: `Jt(w) · Σν ≤ 1` when `c ≥ 0`, so `Γ_true ≤ 1/Σν`.
* `budget`: for counts meeting a demand `D` on every load, `Σν · D ≤ N · sac(N/ΣN)`.
* `weak_duality`: `Σν ≤ sac(v)/Jt(v)` for every design with `Jt(v) > 0`. Every certificate's
  constant is at most every design's repair ratio.
* `repair_mix`: mixing a surrogate optimum with any design `v` gives up at most `β sac(v)` and
  keeps at least `β Jt(v)`. So `R(β) ≥ β Jt(v)/sac(v)`.

All of it is weak LP duality: finite sums and one lower bound per game. The covering form
`max Σν` subject to `Σ ν_j L_j ≤ margins` is a cost-weighted covering constant whose costs are
the surrogate's own dual margins.
-/

namespace CIGAMF.P13.PaperASacrificeDuality

open Finset

section General

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- An allocation over the cells. -/
def IsAllocG (w : ι → ℝ) : Prop := (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1

/-- The relative sacrifice of a design. -/
noncomputable def sac (Jf : (ι → ℝ) → ℝ) (Γ : ℝ) (w : ι → ℝ) : ℝ := 1 - Jf w / Γ

/-- The margin of a cell under a frozen certificate. -/
noncomputable def margin (c : ι → ℝ) (Γ : ℝ) (e : ι) : ℝ := 1 - c e / Γ

/-- The average design of a count vector. -/
noncomputable def avgDesign (N : ι → ℝ) : ι → ℝ := fun e => N e / ∑ e', N e'

theorem avgDesign_alloc (N : ι → ℝ) (hN : ∀ e, 0 ≤ N e) (hpos : 0 < ∑ e, N e) :
    IsAllocG (avgDesign N) := by
  refine ⟨fun e => div_nonneg (hN e) hpos.le, ?_⟩
  unfold avgDesign
  rw [← Finset.sum_div, div_self hpos.ne']

theorem sum_margin (c : ι → ℝ) (Γ : ℝ) (w : ι → ℝ) (hw : ∑ e, w e = 1) :
    ∑ e, w e * margin c Γ e = 1 - (∑ e, w e * c e) / Γ := by
  unfold margin
  have h1 : ∑ e, w e * (1 - c e / Γ) = ∑ e, w e - ∑ e, (w e * c e) / Γ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [h1, hw, Finset.sum_div]

/-- **Exchange.**  Every design pays, in relative sacrifice, at least its mass weighted by the
margins of a frozen certificate. -/
theorem exchange (Jf : (ι → ℝ) → ℝ) (Γ : ℝ) (hΓ : 0 < Γ) (c : ι → ℝ)
    (hc : ∀ w, IsAllocG w → Jf w ≤ ∑ e, w e * c e) (w : ι → ℝ) (hw : IsAllocG w) :
    ∑ e, w e * margin c Γ e ≤ sac Jf Γ w := by
  rw [sum_margin c Γ w hw.2]
  unfold sac
  have : Jf w / Γ ≤ (∑ e, w e * c e) / Γ := div_le_div_of_nonneg_right (hc w hw) hΓ.le
  linarith

/-- The covered loads, summed against a design. -/
theorem sum_cover (L : κ → ι → ℝ) (ν : κ → ℝ) (w : ι → ℝ) :
    ∑ j, ν j * ∑ e, w e * L j e = ∑ e, w e * ∑ j, ν j * L j e := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The frontier.**  `Jt(w) · Σν ≤ sac(w)` for every allocation. -/
theorem frontier_upper (Jf Jt : (ι → ℝ) → ℝ) (Γ : ℝ) (hΓ : 0 < Γ) (c : ι → ℝ)
    (hc : ∀ w, IsAllocG w → Jf w ≤ ∑ e, w e * c e)
    (L : κ → ι → ℝ) (hL : ∀ j w, IsAllocG w → Jt w ≤ ∑ e, w e * L j e)
    (ν : κ → ℝ) (hν : ∀ j, 0 ≤ ν j) (hcover : ∀ e, ∑ j, ν j * L j e ≤ margin c Γ e)
    (w : ι → ℝ) (hw : IsAllocG w) :
    Jt w * ∑ j, ν j ≤ sac Jf Γ w := by
  calc Jt w * ∑ j, ν j = ∑ j, ν j * Jt w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ∑ j, ν j * ∑ e, w e * L j e :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hL j w hw) (hν j)
    _ = ∑ e, w e * ∑ j, ν j * L j e := sum_cover L ν w
    _ ≤ ∑ e, w e * margin c Γ e :=
        Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hcover e) (hw.1 e)
    _ ≤ sac Jf Γ w := exchange Jf Γ hΓ c hc w hw

/-- **The value bound.**  With a nonnegative frozen certificate, `Jt(w) · Σν ≤ 1`, so the true
game is at most `1/Σν`. -/
theorem value_upper (Jt : (ι → ℝ) → ℝ) (Γ : ℝ) (hΓ : 0 < Γ) (c : ι → ℝ) (hc0 : ∀ e, 0 ≤ c e)
    (L : κ → ι → ℝ) (hL : ∀ j w, IsAllocG w → Jt w ≤ ∑ e, w e * L j e)
    (ν : κ → ℝ) (hν : ∀ j, 0 ≤ ν j) (hcover : ∀ e, ∑ j, ν j * L j e ≤ margin c Γ e)
    (w : ι → ℝ) (hw : IsAllocG w) :
    Jt w * ∑ j, ν j ≤ 1 := by
  have hm : ∀ e, margin c Γ e ≤ 1 := fun e => by
    unfold margin
    have : 0 ≤ c e / Γ := div_nonneg (hc0 e) hΓ.le
    linarith
  calc Jt w * ∑ j, ν j = ∑ j, ν j * Jt w := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ∑ j, ν j * ∑ e, w e * L j e :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hL j w hw) (hν j)
    _ = ∑ e, w e * ∑ j, ν j * L j e := sum_cover L ν w
    _ ≤ ∑ e, w e * 1 :=
        Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ((hcover e).trans (hm e)) (hw.1 e)
    _ = 1 := by simp [hw.2]

/-- **The budget.**  Expected counts `N` that meet a demand `D` on every covered load pay
`Σν · D` in sacrifice: `Σν · D ≤ N · sac(N/ΣN)`. -/
theorem budget (Jf : (ι → ℝ) → ℝ) (Γ : ℝ) (hΓ : 0 < Γ) (c : ι → ℝ)
    (hc : ∀ w, IsAllocG w → Jf w ≤ ∑ e, w e * c e)
    (L : κ → ι → ℝ) (ν : κ → ℝ) (hν : ∀ j, 0 ≤ ν j)
    (hcover : ∀ e, ∑ j, ν j * L j e ≤ margin c Γ e)
    (N : ι → ℝ) (hN : ∀ e, 0 ≤ N e) (hpos : 0 < ∑ e, N e) (D : ℝ)
    (hdem : ∀ j, D ≤ ∑ e, N e * L j e) :
    (∑ j, ν j) * D ≤ (∑ e, N e) * sac Jf Γ (avgDesign N) := by
  have hbar := avgDesign_alloc N hN hpos
  have hex := exchange Jf Γ hΓ c hc (avgDesign N) hbar
  have hscale : ∑ e, N e * margin c Γ e = (∑ e, N e) * ∑ e, avgDesign N e * margin c Γ e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold avgDesign
    field_simp
  calc (∑ j, ν j) * D = ∑ j, ν j * D := by rw [Finset.sum_mul]
    _ ≤ ∑ j, ν j * ∑ e, N e * L j e :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hdem j) (hν j)
    _ = ∑ e, N e * ∑ j, ν j * L j e := sum_cover L ν N
    _ ≤ ∑ e, N e * margin c Γ e :=
        Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hcover e) (hN e)
    _ = (∑ e, N e) * ∑ e, avgDesign N e * margin c Γ e := hscale
    _ ≤ (∑ e, N e) * sac Jf Γ (avgDesign N) := mul_le_mul_of_nonneg_left hex hpos.le

/-- **Weak duality.**  Every certificate's constant is at most every design's repair ratio. -/
theorem weak_duality (Jf Jt : (ι → ℝ) → ℝ) (Γ : ℝ) (hΓ : 0 < Γ) (c : ι → ℝ)
    (hc : ∀ w, IsAllocG w → Jf w ≤ ∑ e, w e * c e)
    (L : κ → ι → ℝ) (hL : ∀ j w, IsAllocG w → Jt w ≤ ∑ e, w e * L j e)
    (ν : κ → ℝ) (hν : ∀ j, 0 ≤ ν j) (hcover : ∀ e, ∑ j, ν j * L j e ≤ margin c Γ e)
    (v : ι → ℝ) (hv : IsAllocG v) (hJ : 0 < Jt v) :
    ∑ j, ν j ≤ sac Jf Γ v / Jt v := by
  rw [le_div_iff₀ hJ, mul_comm]
  exact frontier_upper Jf Jt Γ hΓ c hc L hL ν hν hcover v hv

/-- The mixture of two designs. -/
def mixD (β : ℝ) (a b : ι → ℝ) : ι → ℝ := fun e => (1 - β) * a e + β * b e

theorem mixD_alloc (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (a b : ι → ℝ) (ha : IsAllocG a)
    (hb : IsAllocG b) : IsAllocG (mixD β a b) := by
  refine ⟨fun e => ?_, ?_⟩
  · unfold mixD
    have := ha.1 e; have := hb.1 e
    nlinarith
  · unfold mixD
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ha.2, hb.2]
    ring

/-- **Repair by mixing.**  Mixing a surrogate optimum `w*` with a design `v` at weight `β`
gives up at most `β sac(v)` and keeps at least `β Jt(v)`.  Hence `R(β sac(v)) ≥ β Jt(v)`. -/
theorem repair_mix (Jf Jt : (ι → ℝ) → ℝ) (Γ : ℝ) (hΓ : 0 < Γ)
    (hconcf : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jf a + β * Jf b ≤ Jf (mixD β a b))
    (hconct : ∀ a b, IsAllocG a → IsAllocG b → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      (1 - β) * Jt a + β * Jt b ≤ Jt (mixD β a b))
    (wstar v : ι → ℝ) (hws : IsAllocG wstar) (hv : IsAllocG v) (hopt : Jf wstar = Γ)
    (hJt0 : 0 ≤ Jt wstar) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    IsAllocG (mixD β wstar v) ∧ sac Jf Γ (mixD β wstar v) ≤ β * sac Jf Γ v
      ∧ β * Jt v ≤ Jt (mixD β wstar v) := by
  refine ⟨mixD_alloc β hβ0 hβ1 wstar v hws hv, ?_, ?_⟩
  · have h := hconcf wstar v hws hv β hβ0 hβ1
    rw [hopt] at h
    unfold sac
    have : ((1 - β) * Γ + β * Jf v) / Γ ≤ Jf (mixD β wstar v) / Γ :=
      div_le_div_of_nonneg_right h hΓ.le
    have heq : ((1 - β) * Γ + β * Jf v) / Γ = (1 - β) + β * (Jf v / Γ) := by
      field_simp
    rw [heq] at this
    nlinarith
  · have h := hconct wstar v hws hv β hβ0 hβ1
    have : 0 ≤ (1 - β) * Jt wstar := mul_nonneg (by linarith) hJt0
    linarith

end General

/-! ## 3. The centred construction is an instance

The frozen certificate is the single frozen alternative `lamStar`: it carries `9/512` on the
arm and anchor cells and nothing on the middle cells (`energy_lamStar`). The repair certificate
puts weight `8M/(1+2d)^2` on the shift of each middle pair by `1/2 + d`, whose load is
`(1/2+d)^2/(2M)` on that pair's two cells. The margins are `0` on the arm and anchors and `1` on
the middle cells, and the covering is tight. -/

section Instance

open MeasureTheory ProbabilityTheory
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy
open CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperAActualDecisionBridge CIGAMF.P13.PaperAStrict
open CIGAMF.P13.PaperACentred CIGAMF.P13.PaperARPair CIGAMF.P13.PaperAGaussianKL
open CIGAMF.P13.PaperAFamilyLower CIGAMF.P13.PaperAFrontier CIGAMF.P13.PaperASacrifice

variable {r : ℕ}

/-- The frozen certificate of the construction. -/
noncomputable def cStar : Cell r → ℝ := Sum.elim (fun _ => 9 / 512) (fun _ => 0)

/-- The load of the shift of pair `j` by `1/2 + d`. -/
noncomputable def pairLoad (M d : ℝ) (j : Fin r) : Cell r → ℝ :=
  Sum.elim (fun _ => 0) (fun p => if p.1 = j then (1 / 2 + d) ^ 2 / (2 * M) else 0)

/-- The repair weights of the construction. -/
noncomputable def nuStar (M d : ℝ) : Fin r → ℝ := fun _ => 8 * M / (1 + 2 * d) ^ 2

theorem isAllocG_iff (w : Cell r → ℝ) : IsAllocG w ↔ IsAlloc w := Iff.rfl

theorem sum_cStar (w : Cell r → ℝ) : ∑ e, w e * cStar e = 9 / 512 * aMass w := by
  rw [Fintype.sum_sum_type]
  unfold cStar aMass
  simp [Finset.mul_sum, mul_comm]

theorem sum_pairLoad (M d : ℝ) (j : Fin r) (w : Cell r → ℝ) :
    ∑ e, w e * pairLoad M d j e = pairWeight w j * (1 / 2 + d) ^ 2 / (2 * M) := by
  rw [Fintype.sum_sum_type]
  unfold pairLoad pairWeight
  simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true, Fintype.sum_bool]
    ring
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem cStar_cert (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) (hw : IsAllocG w) :
    frozenValueC₀ M w ≤ ∑ e, w e * cStar e := by
  rw [sum_cStar]
  exact frozenValueC₀_le M hM w hw

theorem pairLoad_cert [NeZero r] (M : ℝ) (hM : 0 < M) (d : ℝ) (hd : 0 < d) (j : Fin r)
    (w : Cell r → ℝ) (hw : IsAllocG w) :
    trueValueStrict M w ≤ ∑ e, w e * pairLoad M d j e := by
  rw [sum_pairLoad]
  exact trueValueStrict_le_shift M hM w hw.1 j d hd

theorem nuStar_cover (M : ℝ) (hM : 0 < M) (d : ℝ) (hd : 0 < d) (e : Cell r) :
    ∑ j, nuStar M d j * pairLoad M d j e ≤ margin cStar (9 / 512) e := by
  cases e with
  | inl i =>
      unfold pairLoad margin cStar
      simp
  | inr p =>
      unfold pairLoad margin cStar
      simp only [Sum.elim_inr, zero_div, sub_zero]
      rw [Finset.sum_eq_single p.1]
      · simp only [ite_true]
        unfold nuStar
        have h1 : (0 : ℝ) < 1 + 2 * d := by linarith
        have h2 : (1 / 2 + d) ^ 2 = (1 + 2 * d) ^ 2 / 4 := by ring
        rw [h2]
        field_simp
        ring_nf
        exact le_refl _
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_nuStar (M d : ℝ) : ∑ j : Fin r, nuStar M d j = r * (8 * M / (1 + 2 * d) ^ 2) := by
  unfold nuStar
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem sacrifice_eq_sac (M : ℝ) (w : Cell r → ℝ) :
    sacrifice M w = sac (frozenValueC₀ M) (9 / 512) w := by
  unfold sacrifice sac
  ring

/-- **The construction's frontier from the general law.**  For every `d > 0`,
`J_true(w) · 8rM/(1+2d)^2 ≤ sacrifice(w)`. -/
theorem construction_frontier [NeZero r] (M : ℝ) (hM : 0 < M) (d : ℝ) (hd : 0 < d)
    (w : Cell r → ℝ) (hw : IsAlloc w) :
    trueValueStrict M w * (r * (8 * M / (1 + 2 * d) ^ 2)) ≤ sacrifice M w := by
  rw [← sum_nuStar, sacrifice_eq_sac]
  exact frontier_upper (frozenValueC₀ M) (trueValueStrict M) (9 / 512) (by norm_num) cStar
    (cStar_cert M hM) (pairLoad M d) (fun j w hw => pairLoad_cert M hM d hd j w hw)
    (nuStar M d) (fun j => by unfold nuStar; positivity) (nuStar_cover M hM d hd) w hw

/-- **The construction's budget from the general law.**  Every `delta`-correct finite-horizon
policy pays `N · sacrifice(wbar) ≥ 8 r M D`: `sacrifice_cost_law`, rederived through the
certificate pair, with the shift margin `d → 0`. -/
theorem construction_budget [NeZero r] (M : ℝ) (hM : 0 < M)
    (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist (famChan M hM) π (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π (lift lam) n).real S ≤ δ)
    (hD : 0 < demand δ) (hpos : 0 < ∑ e, expCnt M hM π n e) :
    8 * (r : ℝ) * M * demand δ
      ≤ (∑ e, expCnt M hM π n e) * sacrifice M (avgDesign (expCnt M hM π n)) := by
  have hN := expCnt_nonneg M hM π n
  have hsac0 : 0 ≤ sacrifice M (avgDesign (expCnt M hM π n)) :=
    sacrifice_nonneg M hM _ (avgDesign_alloc _ hN hpos)
  have hP : 0 ≤ (∑ e, expCnt M hM π n e) * sacrifice M (avgDesign (expCnt M hM π n)) :=
    mul_nonneg hpos.le hsac0
  have key : ∀ d : ℝ, 0 < d → 8 * (r : ℝ) * M * demand δ
      ≤ (∑ e, expCnt M hM π n e) * sacrifice M (avgDesign (expCnt M hM π n))
        * (1 / 2 + d) ^ 2 / (2 * (1 / 8)) := by
    intro d hd
    have hb := budget (frozenValueC₀ M) (9 / 512) (by norm_num) cStar (cStar_cert M hM)
      (pairLoad M d) (nuStar M d) (fun j => by unfold nuStar; positivity)
      (nuStar_cover M hM d hd) (expCnt M hM π n) hN hpos (demand δ)
      (fun j => by
        rw [sum_pairLoad]
        exact demand_le_shift M hM π n S hS δ hδ hδ1 hθ hl hD.le j d hd)
    rw [sum_nuStar, ← sacrifice_eq_sac] at hb
    have h1 : (0 : ℝ) < 1 + 2 * d := by linarith
    have hsq : (0 : ℝ) < (1 + 2 * d) ^ 2 := by positivity
    have h2 : (∑ e, expCnt M hM π n e) * sacrifice M (avgDesign (expCnt M hM π n))
        * (1 / 2 + d) ^ 2 / (2 * (1 / 8))
        = (∑ e, expCnt M hM π n e) * sacrifice M (avgDesign (expCnt M hM π n))
          * (1 + 2 * d) ^ 2 := by ring
    rw [h2]
    have h3 : (r : ℝ) * (8 * M / (1 + 2 * d) ^ 2) * demand δ
        = 8 * (r : ℝ) * M * demand δ / (1 + 2 * d) ^ 2 := by ring
    rw [h3, div_le_iff₀ hsq] at hb
    exact hb
  have hlim := limit_shift (8 * (r : ℝ) * M * demand δ)
    ((∑ e, expCnt M hM π n e) * sacrifice M (avgDesign (expCnt M hM π n)))
    (1 / 8) (by norm_num) hP key
  linarith [hlim]

/-- **Satisfiability of the general law's hypotheses**: the construction's certificate pair
exists for every `M > 0`, `r ≥ 1` and `d > 0`, with constant `8rM/(1+2d)^2 > 0`. -/
theorem certificate_pair_satisfiable [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (d : ℝ)
    (hd : 0 < d) :
    (∀ w, IsAllocG w → frozenValueC₀ M w ≤ ∑ e, w e * cStar (r := r) e)
      ∧ (∀ j w, IsAllocG w → trueValueStrict M w ≤ ∑ e, w e * pairLoad (r := r) M d j e)
      ∧ (∀ e, ∑ j, nuStar (r := r) M d j * pairLoad M d j e ≤ margin cStar (9 / 512) e)
      ∧ 0 < ∑ j : Fin r, nuStar M d j := by
  refine ⟨cStar_cert M hM, fun j w hw => pairLoad_cert M hM d hd j w hw,
    nuStar_cover M hM d hd, ?_⟩
  rw [sum_nuStar]
  have : (0 : ℝ) < r := by exact_mod_cast hr
  positivity

end Instance

#print axioms exchange
#print axioms frontier_upper
#print axioms value_upper
#print axioms budget
#print axioms weak_duality
#print axioms repair_mix
#print axioms construction_frontier
#print axioms construction_budget
#print axioms certificate_pair_satisfiable

end CIGAMF.P13.PaperASacrificeDuality
