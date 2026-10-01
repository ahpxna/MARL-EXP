import «LeanFunctionalHeterogeneousInstanceV1»
import «LeanFunctionalGeometryDischargeV1»
import «LeanFunctionalHeterogeneousLowerV1»

/-! # Functional: the JOIN -- explicit allocation, every ordered pair discharged, the
bridge actually invoked, and a witness that attains the value.

The audit's F1: `instantiated_value` proves only an arithmetic identity -- no cell
type, no allocation, no quantifier over alternatives.  F2: the geometry discharge is
never applied to a named allocation, and a flipping alternative attaining the bound is
missing.  This file closes both, and CALLS `energyU_ge_pairV` instead of restating it.

## THE ALLOCATION

Outsider cells `Cell n = Fin 2 ⊕ Fin n`: two endpoints at `±(1-d)/2`, variance `1`,
and `n` middle cells at `z_i`, variance `v_i > 0`, with `g_i = 1/2 - |z_i| ≥ d/2`.
`S = ∑ v_i/g_i²`, `A = 1/(16 + d²S)`, and

    w(endpoint) = 4A   (the incumbent's two cells and the outsider's two),
    w(middle i) = d² v_i A / g_i².

## WHAT IS PROVED

* `budget`, `wt_pos` — a legal allocation summing to `1` over all `n + 4` cells.
* `resistance_identity` — `A·(σ_x/w_x) = gval(x)²/d²` with `gval(endpoint) = d/2`: an
  endpoint behaves exactly like a middle cell AT the domain boundary, which is why the
  three pair cases collapse into one.
* `mean_gap` — `gval a + gval b ≤ 1 - (mean a - mean b)` for every ordered pair of
  distinct cells (both endpoint orders, all four endpoint/middle orientations, both
  middle orders).
* `mean_diff_lt_one` — the hypothesis `energyU_ge_pairV` requires.
* `pairV_to_pairVal` — the bridge's `pairV` IS the instance module's `pairVal` at
  `A = W/4`: the two files are about the same quantity.
* `every_pair_ge` — `A d²/2 ≤ pairV` for every ordered pair.
* `gamma_lower` — **for EVERY flipping alternative, `energyU ≥ A d²/2`**, by invoking
  `energyU_ge_pairV` and discharging its conclusion with `every_pair_ge`.
* `witness_flips`, `witness_energy` — the explicit alternative moving the four
  endpoints to `±(1/2 - d/4)` and leaving the middle cells alone flips the decision and
  costs exactly `A d²/2`.
* `gamma_value` — both halves at once, with the closed form
  `A d²/2 = c²/(n(32 + 2c²H_n))`.
* `Splus_lower`, `sandwich_ratio` — the uniform law: with `g_min ≥ d/2` the
  known/unknown-variance sandwich is inside a factor `(1 + d/(2 g_min))² ≤ 4`, and it
  tends to `1` exactly when `d/g_min → 0`, NOT merely when `d → 0`.

## WHAT THIS DOES NOT ESTABLISH

- `FlipsU` uses `≤`, so the witness attains the minimum for THAT alternative set.  For
  strict rank inversion the same witness gives an infimum approached by perturbation.
- `A d²/2` is the value AT `w*`.  It is NOT shown optimal over the design polytope, so
  it must not be written `Γ* = sup_w J(w)`.
- `sandwich_ratio` bounds the width of the known/unknown-variance sandwich, not the
  ratio of the true optimum to `J(w*)`.
-/

namespace CIGAMF.P13.FunctionalAllocationJoin

open Finset
open CIGAMF.P13.FunctionalHeterogeneousInstance
open CIGAMF.P13.FunctionalCrossoverLower
open CIGAMF.P13.FunctionalHeterogeneousLower

noncomputable section

/-- The bridge's pair value IS the instance module's, at `A = W/4`. -/
theorem pairV_to_pairVal (W pa pb D : ℝ) (hW : 0 < W) (hpa : 0 < pa) (hpb : 0 < pb) :
    pairV W W pa pb D = pairVal (W / 4) (1 / (2 * (1 / pa + 1 / pb))) D := by
  have hs : (0:ℝ) < pa + pb := by linarith
  have hB : 1 / (2 * (1 / pa + 1 / pb)) = pa * pb / (2 * (pa + pb)) := by
    rw [div_add_div _ _ (ne_of_gt hpa) (ne_of_gt hpb)]
    field_simp
    ring
  have hlhs : pairV W W pa pb D
      = W * (pa * pb) * (1 - D) ^ 2 / (2 * (W * (pa + pb) + 2 * (pa * pb))) := by
    unfold pairV
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hrhs : pairVal (W / 4) (pa * pb / (2 * (pa + pb))) D
      = W * (pa * pb) * (1 - D) ^ 2 / (2 * (W * (pa + pb) + 2 * (pa * pb))) := by
    unfold pairVal
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  rw [hB, hlhs, hrhs]

variable {n : ℕ}

abbrev Cell (n : ℕ) := Sum (Fin 2) (Fin n)

variable (d : ℝ) (mid vr : Fin n → ℝ)

/-- `g` of a cell.  An endpoint sits exactly at the domain boundary `g = d/2`. -/
def gval : Cell n → ℝ := Sum.elim (fun _ => d / 2) (fun i => 1 / 2 - |mid i|)

def mean : Cell n → ℝ :=
  Sum.elim (fun k : Fin 2 => if k = 0 then (1 - d) / 2 else -((1 - d) / 2)) mid

def sigC : Cell n → ℝ := Sum.elim (fun _ => 1) vr

def bigS : ℝ := ∑ i : Fin n, vr i / (1 / 2 - |mid i|) ^ 2

def bigA : ℝ := 1 / (16 + d ^ 2 * bigS mid vr)

def wt : Cell n → ℝ :=
  Sum.elim (fun _ => 4 * bigA d mid vr)
    (fun i => d ^ 2 * vr i * bigA d mid vr / (1 / 2 - |mid i|) ^ 2)

/-- The flipping witness: all four endpoints move to `±(1/2 - d/4)`. -/
def lwit : Cell n → ℝ :=
  Sum.elim (fun k : Fin 2 => if k = 0 then 1 / 2 - d / 4 else -(1 / 2 - d / 4)) mid

section Hyp
variable (hd : 0 < d) (hd1 : d < 1) (hv : ∀ i, 0 < vr i)
  (hg : ∀ i : Fin n, d / 2 ≤ 1 / 2 - |mid i|)

include hd hv hg in
theorem mid_pos (i : Fin n) : 0 < 1 / 2 - |mid i| := lt_of_lt_of_le (by linarith) (hg i)

include hd hv hg in
theorem bigS_nonneg : 0 ≤ bigS mid vr := by
  refine Finset.sum_nonneg fun i _ => ?_
  have h1 := mid_pos d mid vr hd hv hg i
  have h2 := hv i
  positivity

include hd hv hg in
theorem denom_pos : (0:ℝ) < 16 + d ^ 2 * bigS mid vr := by
  have := bigS_nonneg d mid vr hd hv hg
  nlinarith [sq_nonneg d]

include hd hv hg in
theorem bigA_pos : 0 < bigA d mid vr :=
  div_pos one_pos (denom_pos d mid vr hd hv hg)

include hd hv hg in
theorem wt_pos : ∀ x : Cell n, 0 < wt d mid vr x := by
  intro x
  have hA := bigA_pos d mid vr hd hv hg
  cases x with
  | inl k => simp only [wt, Sum.elim_inl]; linarith
  | inr i =>
      have h1 := mid_pos d mid vr hd hv hg i
      have h2 := hv i
      simp only [wt, Sum.elim_inr]
      positivity

include hv in
theorem sigC_pos : ∀ x : Cell n, 0 < sigC vr x := by
  intro x
  cases x with
  | inl k => simp only [sigC, Sum.elim_inl]; norm_num
  | inr i => simpa only [sigC, Sum.elim_inr] using hv i

include hd hv hg in
/-- The budget: the two incumbent cells carry `4A` each, the `n+2` outsider cells the
rest, and the total is `1`. -/
theorem budget : 2 * (4 * bigA d mid vr) + ∑ x : Cell n, wt d mid vr x = 1 := by
  have hne := ne_of_gt (denom_pos d mid vr hd hv hg)
  have hsum : ∑ x : Cell n, wt d mid vr x
      = 2 * (4 * bigA d mid vr) + d ^ 2 * bigS mid vr * bigA d mid vr := by
    rw [Fintype.sum_sum_type]
    have h1 : (∑ _k : Fin 2, wt d mid vr (Sum.inl _k)) = 2 * (4 * bigA d mid vr) := by
      simp only [wt, Sum.elim_inl, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      norm_num
    have h2 : (∑ i : Fin n, wt d mid vr (Sum.inr i))
        = d ^ 2 * bigS mid vr * bigA d mid vr := by
      simp only [wt, Sum.elim_inr, bigS]
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h2]
  rw [hsum]
  unfold bigA
  field_simp
  ring

include hd hv hg in
theorem gval_ge : ∀ x : Cell n, d / 2 ≤ gval d mid x := by
  intro x
  cases x with
  | inl k => simp only [gval, Sum.elim_inl]; exact le_rfl
  | inr i => simpa only [gval, Sum.elim_inr] using hg i

include hd hv hg in
/-- **The identity the whole comparison rests on**: `A·(σ/w) = gval²/d²`, uniformly. -/
theorem resistance_identity : ∀ x : Cell n,
    bigA d mid vr * (sigC vr x / wt d mid vr x) = (gval d mid x) ^ 2 / d ^ 2 := by
  intro x
  have hA := bigA_pos d mid vr hd hv hg
  have hAne := ne_of_gt hA
  have hdne : d ≠ 0 := ne_of_gt hd
  cases x with
  | inl k =>
      simp only [sigC, wt, gval, Sum.elim_inl]
      field_simp
      try ring
  | inr i =>
      have h1 := mid_pos d mid vr hd hv hg i
      have h2 := hv i
      simp only [sigC, wt, gval, Sum.elim_inr]
      field_simp
      try ring

include hd hd1 hg in
/-- The geometry, for EVERY ordered pair of distinct cells. -/
theorem mean_gap : ∀ a b : Cell n, a ≠ b →
    gval d mid a + gval d mid b ≤ 1 - (mean d mid a - mean d mid b) := by
  intro a b hab
  cases a with
  | inl k =>
      cases b with
      | inl l =>
          have hkl : k ≠ l := fun h => hab (by rw [h])
          simp only [gval, mean, Sum.elim_inl]
          fin_cases k <;> fin_cases l <;> simp_all <;> linarith
      | inr j =>
          have h1 := neg_abs_le (mid j)
          have h2 := le_abs_self (mid j)
          have h3 := abs_nonneg (mid j)
          simp only [gval, mean, Sum.elim_inl, Sum.elim_inr]
          fin_cases k <;> norm_num <;> linarith
  | inr i =>
      have hi1 := neg_abs_le (mid i)
      have hi2 := le_abs_self (mid i)
      have hi3 := abs_nonneg (mid i)
      cases b with
      | inl l =>
          simp only [gval, mean, Sum.elim_inl, Sum.elim_inr]
          fin_cases l <;> norm_num <;> linarith
      | inr j =>
          have hj1 := neg_abs_le (mid j)
          have hj2 := le_abs_self (mid j)
          simp only [gval, mean, Sum.elim_inr]
          linarith

include hd hd1 hg in
/-- `mean a - mean b < 1` for every pair: the hypothesis the bridge asks for. -/
theorem mean_diff_lt_one : ∀ a b : Cell n, mean d mid a - mean d mid b < 1 := by
  intro a b
  have hbnd : ∀ i : Fin n, |mid i| ≤ 1 / 2 - d / 2 := fun i => by
    have := hg i; linarith [abs_nonneg (mid i)]
  cases a with
  | inl k =>
      cases b with
      | inl l =>
          simp only [mean, Sum.elim_inl]
          fin_cases k <;> fin_cases l <;> norm_num <;> linarith
      | inr j =>
          have h2 := le_abs_self (mid j)
          have h3 := neg_abs_le (mid j)
          have h4 := hbnd j
          simp only [mean, Sum.elim_inl, Sum.elim_inr]
          fin_cases k <;> norm_num <;> linarith
  | inr i =>
      have hi2 := le_abs_self (mid i)
      have hi4 := hbnd i
      cases b with
      | inl l =>
          simp only [mean, Sum.elim_inl, Sum.elim_inr]
          fin_cases l <;> norm_num <;> linarith
      | inr j =>
          have hj3 := neg_abs_le (mid j)
          have hj4 := hbnd j
          simp only [mean, Sum.elim_inr]
          linarith

include hd hd1 hv hg in
/-- **Every ordered pair clears the pinch bound**, in the bridge's own `pairV`. -/
theorem every_pair_ge : ∀ a b : Cell n, a ≠ b →
    bigA d mid vr * d ^ 2 / 2
      ≤ pairV (4 * bigA d mid vr) (4 * bigA d mid vr)
          (prec (wt d mid vr) (sigC vr) a) (prec (wt d mid vr) (sigC vr) b)
          (mean d mid a - mean d mid b) := by
  intro a b hab
  have hA := bigA_pos d mid vr hd hv hg
  have hpa := prec_pos (wt d mid vr) (sigC vr) (wt_pos d mid vr hd hv hg)
    (sigC_pos vr hv) a
  have hpb := prec_pos (wt d mid vr) (sigC vr) (wt_pos d mid vr hd hv hg)
    (sigC_pos vr hv) b
  have hW : (0:ℝ) < 4 * bigA d mid vr := by linarith
  rw [pairV_to_pairVal _ _ _ _ hW hpa hpb]
  have hA4 : 4 * bigA d mid vr / 4 = bigA d mid vr := by ring
  rw [hA4]
  -- the resistance sum
  have hinv : ∀ c : Cell n, 1 / prec (wt d mid vr) (sigC vr) c
      = sigC vr c / wt d mid vr c := by
    intro c
    have h1 := wt_pos d mid vr hd hv hg c
    have h2 := sigC_pos vr hv c
    unfold prec
    field_simp
  set R := sigC vr a / wt d mid vr a + sigC vr b / wt d mid vr b with hR
  have hRrw : 1 / prec (wt d mid vr) (sigC vr) a + 1 / prec (wt d mid vr) (sigC vr) b = R := by
    rw [hinv a, hinv b, hR]
  rw [hRrw]
  have hRpos : 0 < R := by
    have h1 := wt_pos d mid vr hd hv hg a
    have h2 := wt_pos d mid vr hd hv hg b
    have h3 := sigC_pos vr hv a
    have h4 := sigC_pos vr hv b
    rw [hR]; positivity
  have hga := gval_ge d mid vr hd hv hg a
  have hgb := gval_ge d mid vr hd hv hg b
  have hgapos : 0 < gval d mid a := lt_of_lt_of_le (by linarith) hga
  have hgbpos : 0 < gval d mid b := lt_of_lt_of_le (by linarith) hgb
  have hAR : bigA d mid vr * R = ((gval d mid a) ^ 2 + (gval d mid b) ^ 2) / d ^ 2 := by
    rw [hR, mul_add, resistance_identity d mid vr hd hv hg a,
      resistance_identity d mid vr hd hv hg b]
    ring
  rw [pairVal_ge_iff (bigA d mid vr) R _ d hA hRpos]
  exact middle_pair_ok (bigA d mid vr) R (mean d mid a - mean d mid b) d
    (gval d mid a) (gval d mid b) hd hgapos hgbpos hAR
    (mean_gap d mid hd hd1 hg a b hab) hga hgb

include hd hd1 hv hg in
/-- **The lower half, for EVERY flipping alternative.** -/
theorem gamma_lower (lI0 lI1 : ℝ) (l : Cell n → ℝ) (hflip : FlipsU lI0 lI1 l) :
    bigA d mid vr * d ^ 2 / 2
      ≤ energyU (4 * bigA d mid vr) (4 * bigA d mid vr) (wt d mid vr) (sigC vr)
          (mean d mid) lI0 lI1 l := by
  have hA := bigA_pos d mid vr hd hv hg
  have hW : (0:ℝ) < 4 * bigA d mid vr := by linarith
  obtain ⟨a, b, hab, hle⟩ := energyU_ge_pairV (4 * bigA d mid vr) (4 * bigA d mid vr)
    hW hW (wt d mid vr) (sigC vr) (mean d mid) (wt_pos d mid vr hd hv hg)
    (sigC_pos vr hv) (mean_diff_lt_one d mid hd hd1 hg) lI0 lI1 l hflip
  exact le_trans (every_pair_ge d mid vr hd hd1 hv hg a b hab) hle

include hd hd1 in
/-- The witness flips the decision: its outsider spread equals the incumbent's. -/
theorem witness_flips :
    FlipsU (-(1/2) + d/4) (1/2 - d/4) (lwit d mid) := by
  refine ⟨Sum.inl 0, Sum.inl 1, by simp, ?_⟩
  simp only [lwit, Sum.elim_inl]
  norm_num
  rw [abs_of_nonneg (by linarith)]
  linarith

include hd hv hg in
/-- …and it costs exactly `A d²/2`. -/
theorem witness_energy :
    energyU (4 * bigA d mid vr) (4 * bigA d mid vr) (wt d mid vr) (sigC vr)
        (mean d mid) (-(1/2) + d/4) (1/2 - d/4) (lwit d mid)
      = bigA d mid vr * d ^ 2 / 2 := by
  have hrest : (∑ c : Cell n, wt d mid vr c * (lwit d mid c - mean d mid c) ^ 2 / sigC vr c)
      = 2 * (4 * bigA d mid vr * (d/4) ^ 2) := by
    rw [Fintype.sum_sum_type]
    have h2 : (∑ i : Fin n, wt d mid vr (Sum.inr i)
        * (lwit d mid (Sum.inr i) - mean d mid (Sum.inr i)) ^ 2 / sigC vr (Sum.inr i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [lwit, mean, Sum.elim_inr]
      simp
    have h1 : (∑ k : Fin 2, wt d mid vr (Sum.inl k)
        * (lwit d mid (Sum.inl k) - mean d mid (Sum.inl k)) ^ 2 / sigC vr (Sum.inl k))
        = 2 * (4 * bigA d mid vr * (d/4) ^ 2) := by
      simp only [wt, lwit, mean, sigC, Sum.elim_inl]
      rw [Fin.sum_univ_two]
      norm_num
      ring
    rw [h1, h2, add_zero]
  unfold energyU
  rw [hrest]
  have e0 : -(1/2) + d/4 + 1/2 = d/4 := by ring
  have e1 : (1:ℝ)/2 - d/4 - 1/2 = -(d/4) := by ring
  rw [e0, e1]
  ring

include hd hd1 hv hg in
/-- **The two halves.**  Every flipping alternative costs at least `A d²/2`, and the
explicit witness costs exactly that. -/
theorem gamma_value :
    (∀ (lI0 lI1 : ℝ) (l : Cell n → ℝ), FlipsU lI0 lI1 l →
        bigA d mid vr * d ^ 2 / 2
          ≤ energyU (4 * bigA d mid vr) (4 * bigA d mid vr) (wt d mid vr) (sigC vr)
              (mean d mid) lI0 lI1 l)
    ∧ FlipsU (-(1/2) + d/4) (1/2 - d/4) (lwit d mid)
    ∧ energyU (4 * bigA d mid vr) (4 * bigA d mid vr) (wt d mid vr) (sigC vr)
        (mean d mid) (-(1/2) + d/4) (1/2 - d/4) (lwit d mid)
      = bigA d mid vr * d ^ 2 / 2 :=
  ⟨gamma_lower d mid vr hd hd1 hv hg, witness_flips d mid hd hd1,
    witness_energy d mid vr hd hv hg⟩

end Hyp

/-- The value, in the probe's own normalisation.  `n` must be carried: dropping it is
legitimate only when reporting `nJ`. -/
theorem value (c H nn dd A : ℝ) (hn : 0 < nn) (hH : 0 ≤ H) (hc : 0 < c)
    (hdd : dd ^ 2 = c ^ 2 / nn) (hAdef : A = 1 / (16 + c ^ 2 * H)) :
    A * dd ^ 2 / 2 = c ^ 2 / (nn * (32 + 2 * c ^ 2 * H)) :=
  instantiated_value c H nn dd A hn hH hc hdd hAdef

/-- Each unknown-variance term loses at most the factor `(1 + d/(2 g_min))²`. -/
theorem Splus_lower {m : ℕ} (d gmin : ℝ) (g v : Fin m → ℝ) (hd : 0 < d)
    (hgmin : 0 < gmin) (hg : ∀ i, gmin ≤ g i) (hv : ∀ i, 0 < v i) :
    (∑ i : Fin m, v i / (g i) ^ 2) / (1 + d / (2 * gmin)) ^ 2
      ≤ ∑ i : Fin m, v i / (g i + d / 2) ^ 2 := by
  have hk : (0:ℝ) < 1 + d / (2 * gmin) := by positivity
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have hgi : 0 < g i := lt_of_lt_of_le hgmin (hg i)
  have hpos : 0 < g i + d / 2 := by linarith
  have hkey : g i + d / 2 ≤ g i * (1 + d / (2 * gmin)) := by
    have hge : gmin ≤ g i := hg i
    have hstep : d / 2 ≤ g i * (d / (2 * gmin)) := by
      have heq : g i * (d / (2 * gmin)) = (g i / gmin) * (d / 2) := by
        field_simp
      rw [heq]
      have h1 : (1:ℝ) ≤ g i / gmin := (one_le_div hgmin).2 hge
      nlinarith [hd]
    nlinarith [hstep]
  have hsq : (g i + d / 2) ^ 2 ≤ (g i) ^ 2 * (1 + d / (2 * gmin)) ^ 2 := by
    have hexp : (g i * (1 + d / (2 * gmin))) ^ 2
        = (g i) ^ 2 * (1 + d / (2 * gmin)) ^ 2 := by ring
    nlinarith [hkey, hpos]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hsq, (hv i).le]

/-- The sandwich is ordered: the unknown-variance value is the larger. -/
theorem sandwich_order (d S Splus : ℝ) (hd : 0 < d) (hS : 0 ≤ S) (hSpnn : 0 ≤ Splus)
    (hle : Splus ≤ S) :
    d ^ 2 / (32 + 2 * d ^ 2 * S) ≤ d ^ 2 / (32 + 2 * d ^ 2 * Splus) := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hden1 : (0:ℝ) < 32 + 2 * d ^ 2 * Splus := by nlinarith
  have hden2 : (0:ℝ) < 32 + 2 * d ^ 2 * S := by nlinarith
  rw [div_le_div_iff₀ hden2 hden1]
  have hstep : d ^ 2 * Splus ≤ d ^ 2 * S := mul_le_mul_of_nonneg_left hle hd2.le
  have hstep2 : d ^ 2 * (d ^ 2 * Splus) ≤ d ^ 2 * (d ^ 2 * S) :=
    mul_le_mul_of_nonneg_left hstep hd2.le
  nlinarith [hstep2]

/-- **The uniform law**: with `S ≤ κ² S⁺` the sandwich width is at most `κ²`.  Taking
`κ = 1 + d/(2 g_min)` and `g_min ≥ d/2` gives `κ² ≤ 4` on the whole domain, and `κ → 1`
exactly when `d/g_min → 0` -- NOT merely when `d → 0`. -/
theorem sandwich_ratio (d S Splus kap : ℝ) (hd : 0 < d) (hS : 0 ≤ S) (hkap : 1 ≤ kap)
    (hSpnn : 0 ≤ Splus) (hSp : S ≤ Splus * kap ^ 2) :
    d ^ 2 / (32 + 2 * d ^ 2 * Splus) ≤ kap ^ 2 * (d ^ 2 / (32 + 2 * d ^ 2 * S)) := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hden1 : (0:ℝ) < 32 + 2 * d ^ 2 * Splus := by nlinarith
  have hden2 : (0:ℝ) < 32 + 2 * d ^ 2 * S := by nlinarith
  have h1 : (1:ℝ) ≤ kap ^ 2 := by nlinarith [hkap]
  rw [div_le_iff₀ hden1]
  have hrhs : kap ^ 2 * (d ^ 2 / (32 + 2 * d ^ 2 * S)) * (32 + 2 * d ^ 2 * Splus)
      = kap ^ 2 * d ^ 2 * (32 + 2 * d ^ 2 * Splus) / (32 + 2 * d ^ 2 * S) := by
    field_simp
    try ring
  rw [hrhs, le_div_iff₀ hden2]
  have hA : 2 * d ^ 4 * S ≤ 2 * d ^ 4 * (Splus * kap ^ 2) :=
    mul_le_mul_of_nonneg_left hSp (by positivity)
  have hB : 32 * d ^ 2 ≤ 32 * kap ^ 2 * d ^ 2 := by nlinarith [h1, hd2]
  nlinarith [hA, hB]

#print axioms pairV_to_pairVal
#print axioms budget
#print axioms wt_pos
#print axioms resistance_identity
#print axioms gval_ge
#print axioms mean_gap
#print axioms mean_diff_lt_one
#print axioms every_pair_ge
#print axioms gamma_lower
#print axioms witness_flips
#print axioms witness_energy
#print axioms gamma_value
#print axioms value
#print axioms Splus_lower
#print axioms sandwich_order
#print axioms sandwich_ratio

end
end CIGAMF.P13.FunctionalAllocationJoin
