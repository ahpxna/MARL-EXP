import «LeanD6ReferenceEndpointWorldsV1»

/-! # D05: physical bounds on the reference slopes.

`Region` currently carries `hp : 1/2 ≤ rho - 2*slopeBval t T j` as an ASSUMPTION.
That is not a modelling choice: it is a consequence of the reference geometry,
because the `others`-class slope of the gate can never exceed `1/4`.

In the `2q+1` coordinate instance (`|A| = q+1`, `|others A j| = q`) the slope is

    b = (q-1) * t * (1-t)^(2q),      0 ≤ t ≤ 1.

Writing `m = q-1`, `y = m*t`, `z = (1-t)^m`, the Bernoulli-type inequality
`z * (1+y) ≤ 1` (proved here by induction on `m`, no analysis) plus the
elementary `4*y ≤ (1+y)^2` give `y*z^2 ≤ 1/4`, and `b = y*z^2*(1-t)^2 ≤ 1/4`.
With `rho ≥ 1` this yields `rho - 2*b ≥ 1/2` outright.

`physicalRegion` is the resulting constructor: it builds a `Region` from the
physical parameters only, so `hp` is no longer an input anywhere downstream.

WHAT IS NOT REMOVED. The `strong` field `1 ≤ (q-1) * slopeBval t T j` stays an
assumption. It is NOT implied by anything here — indeed `slopeBval ≤ 1/4` forces
`q ≥ 5` before `strong` can hold at all, and the true threshold is larger. The
region is non-empty only from a definite size on; `strong_needs_size` records the
`q ≥ 5` half of that, which is what this file can prove. Do not read
`physicalRegion` as saying the region is non-empty for every `q`.

SIZE OF THE NON-EMPTY REGION (NUMERICAL EVIDENCE, not proved).
Maximising `t*(1-t)^(2q)` at `t = 1/(2q+1)` and then scanning `t` on a 2e5 grid
for the FULL region (`strong`, `c = a-b > 0`, and some `rho` in `[1,2]` with
`min(a,2b) ≤ (q+1)*(2a-rho)`) gives:

    q ≤ 7 : NO admissible `t` at all -- the region is EMPTY, so every D05
            theorem quantified over `Region q j T` is vacuous there;
    q = 8 : first witness, `t = 0.037818`, `(q-1)*b = 1.000`, `a = 0.6825`,
            `b = 0.1429`, admissible `rho` in `[1, 1.3333]`;
    q ≥ 9 : the admissible `rho` interval widens monotonically in the scan
            (q = 12 gives `rho` in `[1, 1.7127]`).

So the smallest size at which the region is inhabited is `q = 8`, i.e. `k = q+1 = 9` retained
coordinates on `I (2q+1) = Fin (2q+2) = 18` coordinates. This is a grid scan in
floating point,
NOT a proof, and in particular the emptiness for `q ≤ 7` is evidence, not a
theorem. `strong_needs_size` below is the only size statement proved here.
-/

namespace CIGAMF.P13.D6ReferencePhysicalBounds
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceRetainedOscillation CIGAMF.P13.D6ReferenceEndpointWorlds
noncomputable section

/-! ## A Bernoulli-type inequality, by induction only -/

/-- `(1-t)^m * (1 + m*t) ≤ 1` on `[0,1]`. Proved by induction: the successor
step loses exactly `(1-t)^m * (m+1) * t^2 ≥ 0`. No derivative, no analysis. -/
theorem bernoulli_tail_le_one (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) :
    (1-t)^m*(1+(m:ℝ)*t) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hz : (0:ℝ) ≤ (1-t)^m := pow_nonneg (by linarith) m
      have hstep : (1-t)^(m+1)*(1+((m+1:ℕ):ℝ)*t)
          = (1-t)^m*(1+(m:ℝ)*t)-(1-t)^m*(((m:ℝ)+1)*t^2) := by
        push_cast
        ring
      have hpos : 0 ≤ (1-t)^m*(((m:ℝ)+1)*t^2) :=
        mul_nonneg hz (mul_nonneg (by positivity) (sq_nonneg t))
      rw [hstep]
      linarith

/-- The quarter bound. `4*y*z^2 = (z*(1+y))^2 - z^2*(1-y)^2 ≤ 1 - 0`. -/
theorem tail_quarter (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ) :
    ((m:ℝ)*t)*((1-t)^m)^2 ≤ 1/4 := by
  have hz : (0:ℝ) ≤ (1-t)^m := pow_nonneg (by linarith) m
  have hy : (0:ℝ) ≤ (m:ℝ)*t := mul_nonneg (Nat.cast_nonneg _) ht0
  have hb : (1-t)^m*(1+(m:ℝ)*t) ≤ 1 := bernoulli_tail_le_one t ht0 ht1 m
  have hu0 : (0:ℝ) ≤ (1-t)^m*(1+(m:ℝ)*t) := mul_nonneg hz (by linarith)
  have hsq : ((1-t)^m*(1+(m:ℝ)*t))^2 ≤ 1 := by nlinarith [hu0, hb]
  have hgap : (0:ℝ) ≤ ((1-t)^m)^2*(1-(m:ℝ)*t)^2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hid : 4*(((m:ℝ)*t)*((1-t)^m)^2)
      = ((1-t)^m*(1+(m:ℝ)*t))^2-((1-t)^m)^2*(1-(m:ℝ)*t)^2 := by ring
  linarith

/-! ## The physical slope bound -/

/-- In the `2q+1` instance the `others`-class slope never exceeds `1/4`. -/
theorem slopeBval_le_quarter (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (q : ℕ) (hq : 2 ≤ q)
    {n : ℕ} (A : Finset (I n)) (j : I n)
    (hAc : A.card=q+1) (hBc : (others A j).card=q) :
    slopeBval t A j ≤ 1/4 := by
  obtain ⟨m,hm⟩ : ∃ m, q=m+1 := ⟨q-1,by omega⟩
  have hy : (0:ℝ) ≤ (m:ℝ)*t := mul_nonneg (Nat.cast_nonneg _) ht0
  have hprod : (0:ℝ) ≤ ((m:ℝ)*t)*((1-t)^m)^2 := mul_nonneg hy (sq_nonneg _)
  have hq4 := tail_quarter t ht0 ht1 m
  have hsq : (1-t)^2 ≤ 1 := by nlinarith
  have hval : slopeBval t A j = (((m:ℝ)*t)*((1-t)^m)^2)*(1-t)^2 := by
    unfold slopeBval
    rw [hAc,hBc,hm,show (m+1+1)+(m+1)-1 = m+m+2 by omega]
    push_cast
    ring
  have hfin : (((m:ℝ)*t)*((1-t)^m)^2)*(1-t)^2 ≤ (((m:ℝ)*t)*((1-t)^m)^2)*1 :=
    mul_le_mul_of_nonneg_left hsq hprod
  rw [hval]
  linarith

/-- Hence `hp` is a theorem, not a hypothesis. -/
theorem hp_from_physical (t rho : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : 1 ≤ rho)
    (q : ℕ) (hq : 2 ≤ q) (T : Finset (I (2*q+1))) (j : I (2*q+1))
    (hT : T ∈ worlds q j) : 1/2 ≤ rho-2*slopeBval t T j := by
  have hpar := world_parameters q j hq hT
  have hB : (others T j).card = q := by
    change (Tᶜ.erase j).card = q
    rw [Finset.card_erase_of_mem (by simp [hpar.1]),hpar.2.2.1,hpar.2.1]
    omega
  have h := slopeBval_le_quarter t ht0 ht1 q hq T j hpar.2.1 hB
  linarith

/-- A `Region` built from physical parameters only: `hp` is supplied internally. -/
def physicalRegion (q : ℕ) (j : I (2*q+1)) (T : Finset (I (2*q+1)))
    (t rho : ℝ) (hq : 2 ≤ q) (hT : T ∈ worlds q j) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : 1 ≤ rho) (hr2 : rho ≤ 2)
    (strong : 1 ≤ ((q:ℝ)-1)*slopeBval t T j) : Region q j T where
  t := t
  rho := rho
  hq := hq
  hT := hT
  ht0 := ht0
  ht1 := ht1
  hr := hr
  hr2 := hr2
  hp := hp_from_physical t rho ht0 ht1 hr q hq T j hT
  strong := strong

theorem physicalRegion_fields (q : ℕ) (j : I (2*q+1)) (T : Finset (I (2*q+1)))
    (t rho : ℝ) (hq : 2 ≤ q) (hT : T ∈ worlds q j) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : 1 ≤ rho) (hr2 : rho ≤ 2)
    (strong : 1 ≤ ((q:ℝ)-1)*slopeBval t T j) :
    (physicalRegion q j T t rho hq hT ht0 ht1 hr hr2 strong).t = t ∧
    (physicalRegion q j T t rho hq hT ht0 ht1 hr hr2 strong).rho = rho :=
  ⟨rfl,rfl⟩

/-- The `strong` field is NOT free: `slopeBval ≤ 1/4` forces `q ≥ 5`. This is a
necessary condition only; the true size threshold is larger and is not proved
here. -/
theorem strong_needs_size (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (q : ℕ) (hq : 2 ≤ q)
    (T : Finset (I (2*q+1))) (j : I (2*q+1)) (hT : T ∈ worlds q j)
    (strong : 1 ≤ ((q:ℝ)-1)*slopeBval t T j) : 5 ≤ q := by
  have hpar := world_parameters q j hq hT
  have hB : (others T j).card = q := by
    change (Tᶜ.erase j).card = q
    rw [Finset.card_erase_of_mem (by simp [hpar.1]),hpar.2.2.1,hpar.2.1]
    omega
  have hle := slopeBval_le_quarter t ht0 ht1 q hq T j hpar.2.1 hB
  have hb0 : 0 ≤ slopeBval t T j := slopeBval_nonneg t ht0 ht1 T j (by omega)
  by_contra hcon
  push_neg at hcon
  have hqR : ((q:ℝ)-1) ≤ 3 := by
    have : (q:ℝ) ≤ 4 := by exact_mod_cast (show q ≤ 4 by omega)
    linarith
  nlinarith [strong, hle, hb0, hqR]

#print axioms bernoulli_tail_le_one
#print axioms tail_quarter
#print axioms slopeBval_le_quarter
#print axioms hp_from_physical
#print axioms physicalRegion_fields
#print axioms strong_needs_size

end
end CIGAMF.P13.D6ReferencePhysicalBounds
