import Mathlib

/-!
# A self-defeating forecast in a reactive loop, and why the repair must be two-sided (city track, 05/10/2026 17:1x EDT)

Paper: research/papers/_tex/paper_two_population.tex (TSI); testbed evidence C-99, C-100, C-118, C-137 (grid4), C-138 (spider), W9-6
(MaxPressure prediction, PROTOCOL_CITY_WAVE9_20261005).  A finite model of the closed loop diagnosed in SUMO: a frozen signal that perceives
demand through a HALTING count, and a frozen eco-approaching fleet that, given a forecast, glides (moves slowly) instead of halting.

Model.  One agent car on the red approach.  Its behaviour `Car`: `halt` (no usable forecast: it drives up and stops, the base driver) or
`glide` (it acts on a forecast and approaches slowly).  The signal perceives demand `demand A c` = (halted count) + A · (slow count) with an
integer adapter weight A (A = 0 is the deployed signal's halting count; TSI's adapter has A ≥ 1).  It gives the approach its green at the
decision point iff it perceives demand there.  Cost of the car (abstract units, s, w > 0): halt → s (stop, then served); glide and served →
0 (no stop); glide and not served → s + w (stops anyway and waits a further cycle).

## WHAT IS PROVED (for every s, w > 0)
* `service_alone_harms` — with the deployed halting count (A = 0), publishing the forecast makes the car worse off than no forecast.
* `forecast_self_defeating` — the forecast learned from no-forecast logs ("the light serves you at the decision point": true there) is FALSE
  once the fleet acts on it under A = 0 and TRUE under any A ≥ 1: the forecast's own publication falsifies it unless the light side changes.
* `adapter_alone_no_gain` — without a forecast the car halts, and every adapter weight gives exactly the no-forecast cost.
* `two_sided_gain` — forecast + adapter (A ≥ 1) attains cost 0 < s, the minimum over all four configurations (`two_sided_min`).
* `no_fleet_side_fix` — with A = 0, NO car behaviour (whatever forecast it is given) attains cost 0; `no_light_side_fix` — without a
  forecast, NO adapter weight attains cost 0.  Each half is necessary in this model; together they suffice.
* `allspeed_sensor_service_suffices` — a signal whose own input counts slow vehicles (A = 1 built in, as MaxPressure's vehicle counts at
  every speed) needs no light-side change: the fleet-side half alone attains 0.  This is the W9-6 prediction, stated in the model.
* `chain_fwer`, `two_attempts_fwer` — union bound for a registered chain of attempts: if attempt i falsely passes with probability ≤ αᵢ,
  some attempt falsely passes with probability ≤ Σ αᵢ (0.05 + 0.025 = 0.075 for the two grid4 attempts).
* `hyps_satisfiable` — the instance s = 2, w = 3 meets the hypotheses and shows every inequality strictly.

## WHAT THIS DOES NOT ESTABLISH
- That SUMO's learned signals and fleets realise this instance; the testbed measures it (HYB harms agent time, ADP alone gives no fuel
  gain, TSI meets the limits: C-118, C-137).  The model has one car and one decision; it says nothing about magnitudes.
- That A ≥ 1 is the right adapter weight in SUMO (TSI calibrates it; W9-5 tests one global value).
- The validity of each bootstrap test at its nominal level: `chain_fwer` takes the per-attempt bounds as hypotheses.
-/

namespace CIGAMF.P13.CityTwoSidedV1

/-- The agent car's approach: drive up and halt (no usable forecast) or glide (act on a forecast). -/
inductive Car | halt | glide
  deriving DecidableEq

/-- Perceived demand on the red approach with adapter weight `A`: halted count + A · slow count. -/
def demand (A : ℕ) : Car → ℕ
  | Car.halt => 1
  | Car.glide => A

/-- The frozen signal serves the approach at the decision point iff it perceives demand there. -/
def serves (A : ℕ) (c : Car) : Prop := 1 ≤ demand A c

instance (A : ℕ) (c : Car) : Decidable (serves A c) := by unfold serves; infer_instance

/-- The car's cost. -/
def cost (s w A : ℕ) : Car → ℕ
  | Car.halt => s
  | Car.glide => if serves A Car.glide then 0 else s + w

/-- The fleet's behaviour with and without the forecast (the R arm reduces to the base driver, which halts). -/
def behaviour (forecast : Bool) : Car := if forecast then Car.glide else Car.halt

/-- Cost of a configuration: forecast published or not, adapter weight `A`. -/
def config (s w A : ℕ) (forecast : Bool) : ℕ := cost s w A (behaviour forecast)

theorem service_alone_harms (s w : ℕ) (hw : 0 < w) : config s w 0 false < config s w 0 true := by
  simp [config, behaviour, cost, serves, demand]; omega

theorem forecast_self_defeating (A : ℕ) (hA : 1 ≤ A) :
    serves 0 Car.halt ∧ ¬ serves 0 Car.glide ∧ serves A Car.glide := by
  simp [serves, demand]; omega

theorem adapter_alone_no_gain (s w A : ℕ) : config s w A false = config s w 0 false := by
  simp [config, behaviour, cost]

theorem two_sided_zero (s w A : ℕ) (hA : 1 ≤ A) : config s w A true = 0 := by
  have : serves A Car.glide := by simp [serves, demand]; omega
  simp [config, behaviour, cost, this]

theorem two_sided_gain (s w A : ℕ) (hs : 0 < s) (hA : 1 ≤ A) : config s w A true = 0 ∧ 0 < config s w 0 false :=
  ⟨two_sided_zero s w A hA, by simpa [config, behaviour, cost] using hs⟩

theorem two_sided_min (s w A A' : ℕ) (hA : 1 ≤ A) (f : Bool) : config s w A true ≤ config s w A' f := by
  rw [two_sided_zero s w A hA]; exact Nat.zero_le _

theorem no_fleet_side_fix (s w : ℕ) (hs : 0 < s) (c : Car) : 0 < cost s w 0 c := by
  cases c <;> simp [cost, serves, demand] <;> omega

theorem no_light_side_fix (s w : ℕ) (hs : 0 < s) (A : ℕ) : 0 < config s w A false := by
  simpa [config, behaviour, cost] using hs

/-- A signal whose own demand input counts slow vehicles at weight 1 (all-speed vehicle counts). -/
theorem allspeed_sensor_service_suffices (s w : ℕ) (hs : 0 < s) :
    config s w 1 true = 0 ∧ config s w 1 true < config s w 1 false := by
  have h := two_sided_gain s w 1 hs le_rfl
  refine ⟨h.1, ?_⟩; rw [h.1]; simpa [config, behaviour, cost] using hs

theorem hyps_satisfiable :
    config 2 3 0 false = 2 ∧ config 2 3 0 true = 5 ∧ config 2 3 1 false = 2 ∧ config 2 3 1 true = 0 := by
  decide

open MeasureTheory in
/-- Union bound for a registered chain of attempts. -/
theorem chain_fwer {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (I : Finset ι) (E : ι → Set Ω) (α : ι → ENNReal)
    (h : ∀ i ∈ I, μ (E i) ≤ α i) : μ (⋃ i ∈ I, E i) ≤ ∑ i ∈ I, α i :=
  (measure_biUnion_finset_le I E).trans (Finset.sum_le_sum h)

open MeasureTheory in
theorem two_attempts_fwer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E₁ E₂ : Set Ω) (a₁ a₂ : ENNReal)
    (h₁ : μ E₁ ≤ a₁) (h₂ : μ E₂ ≤ a₂) : μ (E₁ ∪ E₂) ≤ a₁ + a₂ :=
  (measure_union_le E₁ E₂).trans (add_le_add h₁ h₂)

end CIGAMF.P13.CityTwoSidedV1

#print axioms CIGAMF.P13.CityTwoSidedV1.service_alone_harms
#print axioms CIGAMF.P13.CityTwoSidedV1.forecast_self_defeating
#print axioms CIGAMF.P13.CityTwoSidedV1.adapter_alone_no_gain
#print axioms CIGAMF.P13.CityTwoSidedV1.two_sided_zero
#print axioms CIGAMF.P13.CityTwoSidedV1.two_sided_gain
#print axioms CIGAMF.P13.CityTwoSidedV1.two_sided_min
#print axioms CIGAMF.P13.CityTwoSidedV1.no_fleet_side_fix
#print axioms CIGAMF.P13.CityTwoSidedV1.no_light_side_fix
#print axioms CIGAMF.P13.CityTwoSidedV1.allspeed_sensor_service_suffices
#print axioms CIGAMF.P13.CityTwoSidedV1.hyps_satisfiable
#print axioms CIGAMF.P13.CityTwoSidedV1.chain_fwer
#print axioms CIGAMF.P13.CityTwoSidedV1.two_attempts_fwer
