import «LeanPaperA7OracleSelectV1»

/-!
# Paper A7: information accumulation on a window, derived -- not assumed

`LeanPaperA7ChainV1` composes a window tail argument from hypotheses about abstract per-round
information increments (`hgood`, `hinit`).  Those are exactly the statements the operational
analysis must PRODUCE for the actual learner.  This module produces the deterministic core of
them, from the algorithm's own defining rules and the oracle's bracket contract, following the
A7 blueprint (sections 3 and 5):

1. `oracle_perturbation` -- a design returned by the oracle at the estimate `theta_hat`, with a
   certified lower bracket within `eps` of the estimated game value, has TRUE information at
   least `Gamma(theta) - 2(2B r) - eps` when `|theta_hat - theta| <= r`.  Both moves use the
   world-Lipschitz modulus (`J_lipschitz_in_world`, `Gamma_lipschitz`); nothing about the
   optimiser's continuity is used.
2. `forced_mixture` -- the forced-exploration mixture `(1-rho) w + rho u` loses at most the
   factor `1-rho`, because `J` is concave in the design and nonnegative.
3. `accumulation_window` -- on a window `[n, t)` of good rounds, with the actual tracking
   discrepancy `c`, the design the counts define satisfies
       J(N/t, theta) >= (1/t) sum_{s in [n,t)} (1 - rho_s)(Gamma - eta_s) - 2 B^2 c / t.
   The rounds before `n` contribute `J >= 0`, not an omitted term; the average is controlled
   by concavity (`J_concave_finite`) and the counts by the allocation modulus
   (`J_lipschitz_in_allocation`).  No convergence of the individual designs is assumed.

Coordinates are unit-variance (`pen`), as in `LeanPaperA7OracleSelectV1`; the variance-aware
statement is the same after rescaling each cell by `sqrt v_e`, with box `B / sqrt(min v)`.
What this module does NOT do: bound the confidence radius `r_s` (that is the Ville step) or
the stopping-certificate gap `nu_t`; both enter the final statement separately.
-/

namespace CIGAMF.P13.PaperA7Accumulation

open Finset
open CIGAMF.P13.PaperA7OracleSelect

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem Jval_nonneg (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w mu : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) : 0 ≤ Jval Alt w mu := by
  unfold Jval
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨nu, -, rfl⟩
  exact pen_nonneg w mu nu hw

/-! ## 1. The oracle's design, at the true world -/

/-- **Oracle perturbation.**  `lo` is the oracle's certified lower bracket at the estimate
(`lo <= J(w, theta_hat)`), within `eps` of the estimated game value `Gh`; `Gt` is the true
game value.  Then the design's TRUE information is at least `Gt - 2 (2 B r) - eps`. -/
theorem oracle_perturbation (B : ℝ) (hB : 0 ≤ B) (Alt : Set (E → ℝ)) (hne : Alt.Nonempty)
    (hbox : ∀ nu ∈ Alt, InBox B nu) (w θ θh : E → ℝ) (hw : IsAlloc w)
    (hθ : InBox B θ) (hθh : InBox B θh) (r : ℝ) (hr0 : 0 ≤ r) (hr : ∀ e, |θh e - θ e| ≤ r)
    (Gt Gh : ℝ)
    (hGt : IsLUB {v : ℝ | ∃ w' : E → ℝ, IsAlloc w' ∧ v = Jval Alt w' θ} Gt)
    (hGh : IsLUB {v : ℝ | ∃ w' : E → ℝ, IsAlloc w' ∧ v = Jval Alt w' θh} Gh)
    (lo ε : ℝ) (hlo : lo ≤ Jval Alt w θh) (hbr : Gh - ε ≤ lo) :
    Gt - 2 * (2 * B * r) - ε ≤ Jval Alt w θ := by
  have hGam : |Gh - Gt| ≤ 2 * B * r :=
    Gamma_lipschitz B Alt θh θ Gh Gt (2 * B * r) (by positivity) hGh hGt
      (fun w' hw' => J_lipschitz_in_world B Alt hne hbox w' θh θ hw' hθh hθ r hr0 hr)
      ⟨w, hw⟩
  have hJ := J_lipschitz_in_world B Alt hne hbox w θh θ hw hθh hθ r hr0 hr
  have h1 := (abs_le.mp hGam).1
  have h2 := (abs_le.mp hJ).2
  linarith

/-! ## 2. The forced-exploration mixture -/

/-- **The mixture costs at most the factor `1 - rho`.** -/
theorem forced_mixture (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w u θ : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hu : ∀ e, 0 ≤ u e) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (1 - ρ) * Jval Alt w θ ≤ Jval Alt (fun e => (1 - ρ) * w e + ρ * u e) θ := by
  have hc := J_concave_in_allocation Alt hne w u θ hw hu ρ hρ0 hρ1
  have hJu := Jval_nonneg Alt hne u θ hu
  nlinarith [mul_nonneg hρ0 hJu]

/-! ## 3. The window -/

/-- The target design at round `s`. -/
noncomputable def target (w : ℕ → E → ℝ) (ρ : ℕ → ℝ) (u : E → ℝ) (s : ℕ) : E → ℝ :=
  fun e => (1 - ρ s) * w s e + ρ s * u e

/-- The average target over the first `t` rounds. -/
noncomputable def avgTarget (w : ℕ → E → ℝ) (ρ : ℕ → ℝ) (u : E → ℝ) (t : ℕ) : E → ℝ :=
  fun e => ∑ s ∈ range t, (1 / (t : ℝ)) * target w ρ u s e

/-- **Information accumulation on a window of good rounds.**

Inputs are the algorithm's rules and certified quantities: designs `w s` that are
allocations, forced-exploration weights `rho s ∈ [0,1]` toward an allocation `u`, and on the
window `[n, t)` the per-round guarantee `Gamma - eta s <= J(w s, theta)` that
`oracle_perturbation` supplies; and the tracking discrepancy `c` between the counts and the
cumulative targets.  Output: a lower bound on the information of the design `N / t` the
counts actually define. -/
theorem accumulation_window (B : ℝ) (hB : 0 ≤ B) (Alt : Set (E → ℝ)) (hne : Alt.Nonempty)
    (hbox : ∀ nu ∈ Alt, InBox B nu) (θ : E → ℝ) (hθ : InBox B θ)
    (Γ : ℝ) (n t : ℕ) (hnt : n ≤ t) (ht : 0 < t)
    (w : ℕ → E → ℝ) (hw : ∀ s, IsAlloc (w s))
    (ρ : ℕ → ℝ) (hρ : ∀ s, 0 ≤ ρ s ∧ ρ s ≤ 1) (u : E → ℝ) (hu : IsAlloc u)
    (η : ℕ → ℝ) (hgood : ∀ s, n ≤ s → s < t → Γ - η s ≤ Jval Alt (w s) θ)
    (N : E → ℝ) (hN : ∀ e, 0 ≤ N e) (c : ℝ)
    (htrack : ∑ e, |N e / t - avgTarget w ρ u t e| ≤ c / t) :
    (1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s) - 2 * B ^ 2 * (c / t)
      ≤ Jval Alt (fun e => N e / t) θ := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have htarget_nn : ∀ s e, 0 ≤ target w ρ u s e := by
    intro s e
    exact add_nonneg (mul_nonneg (by linarith [(hρ s).2]) ((hw s).1 e))
      (mul_nonneg (hρ s).1 (hu.1 e))
  -- per-round information of the target
  have hround : ∀ s ∈ range t,
      (if n ≤ s then (1 - ρ s) * (Γ - η s) else 0) ≤ Jval Alt (target w ρ u s) θ := by
    intro s hs
    have hst : s < t := mem_range.mp hs
    split_ifs with hns
    · exact le_trans (mul_le_mul_of_nonneg_left (hgood s hns hst) (by linarith [(hρ s).2]))
        (forced_mixture Alt hne (w s) u θ (hw s).1 hu.1 (ρ s) (hρ s).1 (hρ s).2)
    · exact Jval_nonneg Alt hne _ θ (htarget_nn s)
  -- concavity: the average design is at least the average information
  have hconc := J_concave_finite (range t) Alt hne (target w ρ u) (fun _ => 1 / (t : ℝ)) θ
    htarget_nn (fun _ _ => by positivity)
    (fun e => sum_nonneg fun s _ => mul_nonneg (by positivity) (htarget_nn s e))
  have hsum : ∑ s ∈ range t, (1 / (t : ℝ)) * (if n ≤ s then (1 - ρ s) * (Γ - η s) else 0)
      ≤ ∑ s ∈ range t, (1 / (t : ℝ)) * Jval Alt (target w ρ u s) θ :=
    sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hround s hs) (by positivity)
  have hIco : ∑ s ∈ range t, (1 / (t : ℝ)) * (if n ≤ s then (1 - ρ s) * (Γ - η s) else 0)
      = (1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η s) := by
    rw [← mul_sum, ← sum_filter]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext s
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  -- tracking: the counts' design is close to the average target
  have havg_nn : ∀ e, 0 ≤ avgTarget w ρ u t e :=
    fun e => sum_nonneg fun s _ => mul_nonneg (by positivity) (htarget_nn s e)
  have hlip := J_lipschitz_in_allocation B hB Alt hne hbox (fun e => N e / t)
    (avgTarget w ρ u t) θ (fun e => div_nonneg (hN e) htR.le) havg_nn hθ (c / t) htrack
  have hlo := (abs_le.mp hlip).1
  have havg_eq : Jval Alt (avgTarget w ρ u t) θ
      = Jval Alt (fun e => ∑ s ∈ range t, (1 / (t : ℝ)) * target w ρ u s e) θ := rfl
  linarith [hconc, hsum, hIco, hlo]

#print axioms Jval_nonneg
#print axioms oracle_perturbation
#print axioms forced_mixture
#print axioms accumulation_window

end CIGAMF.P13.PaperA7Accumulation
