import Mathlib

/-! # Support: the K-class SAMPLING law, derived from the IID draw law itself.

`LeanSupportTupleCountV1` proves the counting identity `∏_i L_i = #tuples` and
`LeanSupportDecideExponentV1` proves the pointwise bracket
`min_i L_i/(a_i+L_i) ≤ ∏_i L_i`.  Both are deterministic: they take the PROBABILITY
`Pr(τ unseen) = (1-s)^N` as given.  That probability is the step the audit flags as
missing, together with the posterior and the Bayes-to-minimax lift.  This file
supplies all three, from the product law, with no independence assumed between the
per-class unseen counts (they come from one categorical stream).

## THE MODEL

Draws are IID from `p` on a finite outcome space `Ω` with `∑ p = 1`.  Class `i` has
unsafe tips indexed by `κ i`, observed through an injection `u`, and every unsafe tip
of class `i` carries the same mass `pc i`; `s = ∑_i pc i < 1`.  `L_i(h)` is the number
of unsafe tips of class `i` that the length-`N` history `h` has not shown.

## WHAT IS PROVED

* `avoid_prob` — `Pr(all N draws land in A) = (∑_{x∈A} p x)^N`, by `Finset.prod_univ_sum`
  on the product law.  This is the step that must not be assumed.
* `transversal_mass` — a transversal (one unsafe tip per class) carries mass exactly
  `s`, so its complement carries `1 - s`.  Injectivity of `u` is what makes the classes
  disjoint; nothing assumes the `L_i` are independent.
* `expected_prod_unseen` — **`E ∏_i L_i = (∏_i b_i)(1-s)^N`**, by exchanging the sum
  over histories with the sum over transversals.  This is the upper end of the law.
* `good_event_lower` — `Pr(every class still has an unseen unsafe tip) ≥ (1-s)^N`,
  the lower end: fix one transversal and use monotonicity of indicators.
* `fixed_tip_unsafe_fraction` — **the posterior**: under the uniform prior over the
  `C(a+L, L)` labelings of a class's unexplored tips, a fixed tip is unsafe with
  probability exactly `L/(a+L)`.  Proved from `Nat.succ_mul_choose_eq`.
* `bayes_le_minimax`, `minimax_eq_of_constant` — the lift: a Bayes bound is a minimax
  bound, and for an equivariant rule (constant risk across worlds) the two coincide.

## WHAT THIS DOES NOT ESTABLISH

- The decision rule itself is not constructed here; `fixed_tip_unsafe_fraction` gives
  the risk of naming one tip, and `min_i` over classes is the pointwise step already
  in `LeanSupportDecideExponentV1`.
- The constants `k₀ = min_i 1/(a_i+1)` and `B = ∏_i b_i` are FIXED-K constants: a
  growing-`K` law does not follow from them.
- Recovery (`R_rec`) is not treated here.
-/

namespace CIGAMF.P13.SupportSamplingLaw

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The product law: the chance that all `N` draws land in `A` is `(mass A)^N`. -/
theorem avoid_prob (p : Ω → ℝ) (A : Finset Ω) (N : ℕ) :
    ∑ h : Fin N → Ω, (∏ k, p (h k)) * (if ∀ k, h k ∈ A then (1:ℝ) else 0)
      = (∑ x ∈ A, p x) ^ N := by
  classical
  have hset : (univ.filter (fun h : Fin N → Ω => ∀ k, h k ∈ A))
      = Fintype.piFinset (fun _ : Fin N => A) := by
    ext h; simp [Fintype.mem_piFinset]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hset, ← Finset.prod_univ_sum]
  simp

/-- One unsafe tip per class carries mass exactly `s`, so its complement carries
`1 - s`.  Disjointness of the classes is the injectivity of `u`. -/
theorem transversal_mass (p : Ω → ℝ) (u : (i : ι) → κ i → Ω)
    (hinj : Function.Injective (fun x : Σ i, κ i => u x.1 x.2))
    (pc : ι → ℝ) (hp : ∀ i j, p (u i j) = pc i) (htot : ∑ x, p x = 1)
    (τ : (i : ι) → κ i) :
    ∑ x ∈ univ \ (univ.image (fun i => u i (τ i))), p x = 1 - ∑ i, pc i := by
  classical
  have hinj' : ∀ a ∈ (univ : Finset ι), ∀ b ∈ (univ : Finset ι),
      u a (τ a) = u b (τ b) → a = b := by
    intro a _ b _ hab
    have h := hinj (a₁ := (⟨a, τ a⟩ : Σ i, κ i)) (a₂ := (⟨b, τ b⟩ : Σ i, κ i)) hab
    exact congrArg Sigma.fst h
  have himg : ∑ x ∈ univ.image (fun i => u i (τ i)), p x = ∑ i, pc i := by
    rw [Finset.sum_image hinj']
    exact Finset.sum_congr rfl fun i _ => hp i (τ i)
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _), htot, himg]

variable {N : ℕ}

/-- The unsafe tips of class `i` that the history has not shown. -/
def unseenSet (u : (i : ι) → κ i → Ω) (h : Fin N → Ω) (i : ι) : Finset (κ i) :=
  univ.filter (fun j => ∀ k, h k ≠ u i j)

theorem prod_unseen_card (u : (i : ι) → κ i → Ω) (h : Fin N → Ω) :
    ∏ i, (unseenSet u h i).card = (Fintype.piFinset (unseenSet u h)).card :=
  (Fintype.card_piFinset _).symm

theorem prod_unseen_as_sum (u : (i : ι) → κ i → Ω) (h : Fin N → Ω) :
    (∏ i, ((unseenSet u h i).card : ℝ))
      = ∑ τ : (i : ι) → κ i, (if ∀ i, τ i ∈ unseenSet u h i then (1:ℝ) else 0) := by
  classical
  have hset : (univ.filter (fun τ : (i : ι) → κ i => ∀ i, τ i ∈ unseenSet u h i))
      = Fintype.piFinset (unseenSet u h) := by
    ext τ; simp [Fintype.mem_piFinset]
  have h1 : ∑ τ : (i : ι) → κ i, (if ∀ i, τ i ∈ unseenSet u h i then (1:ℝ) else 0)
      = ((Fintype.piFinset (unseenSet u h)).card : ℝ) := by
    rw [← Finset.sum_filter, hset]
    simp
  rw [h1, ← prod_unseen_card u h]
  push_cast
  rfl

/-- **`E ∏_i L_i = (∏_i b_i)(1-s)^N`.**  The exchange of the sum over histories with
the sum over transversals; each transversal contributes `(1-s)^N` by `avoid_prob`. -/
theorem expected_prod_unseen (p : Ω → ℝ) (u : (i : ι) → κ i → Ω)
    (hinj : Function.Injective (fun x : Σ i, κ i => u x.1 x.2))
    (pc : ι → ℝ) (hp : ∀ i j, p (u i j) = pc i) (htot : ∑ x, p x = 1) (N : ℕ) :
    (∑ h : Fin N → Ω, (∏ k, p (h k)) * (∏ i, ((unseenSet u h i).card : ℝ)))
      = (∏ i, (Fintype.card (κ i) : ℝ)) * (1 - ∑ i, pc i) ^ N := by
  classical
  have step1 : (∑ h : Fin N → Ω, (∏ k, p (h k)) * (∏ i, ((unseenSet u h i).card : ℝ)))
      = ∑ τ : (i : ι) → κ i, ∑ h : Fin N → Ω,
          (∏ k, p (h k)) * (if ∀ i, τ i ∈ unseenSet u h i then (1:ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [prod_unseen_as_sum u h, Finset.mul_sum]
  have step2 : ∀ τ : (i : ι) → κ i,
      (∑ h : Fin N → Ω, (∏ k, p (h k)) * (if ∀ i, τ i ∈ unseenSet u h i then (1:ℝ) else 0))
        = (1 - ∑ i, pc i) ^ N := by
    intro τ
    have hcond : ∀ h : Fin N → Ω,
        (∀ i, τ i ∈ unseenSet u h i)
          ↔ (∀ k, h k ∈ (univ \ (univ.image (fun i => u i (τ i))) : Finset Ω)) := by
      intro h
      constructor
      · intro hh k
        refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
        intro hmem
        obtain ⟨i, _, hEq⟩ := Finset.mem_image.1 hmem
        have hi : ∀ k', h k' ≠ u i (τ i) := by
          have := hh i
          simpa [unseenSet] using this
        exact hi k hEq.symm
      · intro hh i
        have hall : ∀ k, h k ≠ u i (τ i) := by
          intro k hk
          have hk2 := (Finset.mem_sdiff.1 (hh k)).2
          exact hk2 (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hk.symm⟩)
        simpa [unseenSet] using hall
    have : (∑ h : Fin N → Ω, (∏ k, p (h k))
              * (if ∀ i, τ i ∈ unseenSet u h i then (1:ℝ) else 0))
        = ∑ h : Fin N → Ω, (∏ k, p (h k))
              * (if ∀ k, h k ∈ (univ \ (univ.image (fun i => u i (τ i))) : Finset Ω)
                 then (1:ℝ) else 0) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      congr 1
      exact if_congr (hcond h) rfl rfl
    rw [this, avoid_prob p _ N, transversal_mass p u hinj pc hp htot τ]
  rw [step1]
  simp only [step2]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi]
  push_cast
  ring

/-- The lower end: the event that every class still hides an unsafe tip has
probability at least `(1-s)^N`. -/
theorem good_event_lower (p : Ω → ℝ) (u : (i : ι) → κ i → Ω)
    (hinj : Function.Injective (fun x : Σ i, κ i => u x.1 x.2))
    (pc : ι → ℝ) (hp : ∀ i j, p (u i j) = pc i) (htot : ∑ x, p x = 1)
    (hpnn : ∀ x, 0 ≤ p x) (N : ℕ) (τ : (i : ι) → κ i) :
    (1 - ∑ i, pc i) ^ N
      ≤ ∑ h : Fin N → Ω, (∏ k, p (h k))
          * (if ∀ i, 1 ≤ (unseenSet u h i).card then (1:ℝ) else 0) := by
  classical
  have hwnn : ∀ h : Fin N → Ω, 0 ≤ ∏ k, p (h k) :=
    fun h => Finset.prod_nonneg fun k _ => hpnn (h k)
  have hmono : ∀ h : Fin N → Ω,
      (∏ k, p (h k)) * (if ∀ i, τ i ∈ unseenSet u h i then (1:ℝ) else 0)
        ≤ (∏ k, p (h k)) * (if ∀ i, 1 ≤ (unseenSet u h i).card then (1:ℝ) else 0) := by
    intro h
    refine mul_le_mul_of_nonneg_left ?_ (hwnn h)
    by_cases hA : ∀ i, τ i ∈ unseenSet u h i
    · have hB : ∀ i, 1 ≤ (unseenSet u h i).card := by
        intro i
        exact Finset.card_pos.2 ⟨τ i, hA i⟩
      simp [hA, hB]
    · simp only [hA, if_false]
      split <;> norm_num
  have hsum := Finset.sum_le_sum (fun h (_ : h ∈ (univ : Finset (Fin N → Ω))) => hmono h)
  have hleft : (∑ h : Fin N → Ω, (∏ k, p (h k))
      * (if ∀ i, τ i ∈ unseenSet u h i then (1:ℝ) else 0)) = (1 - ∑ i, pc i) ^ N := by
    have hcond : ∀ h : Fin N → Ω,
        (∀ i, τ i ∈ unseenSet u h i)
          ↔ (∀ k, h k ∈ (univ \ (univ.image (fun i => u i (τ i))) : Finset Ω)) := by
      intro h
      constructor
      · intro hh k
        refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
        intro hmem
        obtain ⟨i, _, hEq⟩ := Finset.mem_image.1 hmem
        have hi : ∀ k', h k' ≠ u i (τ i) := by
          have := hh i
          simpa [unseenSet] using this
        exact hi k hEq.symm
      · intro hh i
        have hall : ∀ k, h k ≠ u i (τ i) := by
          intro k hk
          have hk2 := (Finset.mem_sdiff.1 (hh k)).2
          exact hk2 (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hk.symm⟩)
        simpa [unseenSet] using hall
    have hrw : (∑ h : Fin N → Ω, (∏ k, p (h k))
              * (if ∀ i, τ i ∈ unseenSet u h i then (1:ℝ) else 0))
        = ∑ h : Fin N → Ω, (∏ k, p (h k))
              * (if ∀ k, h k ∈ (univ \ (univ.image (fun i => u i (τ i))) : Finset Ω)
                 then (1:ℝ) else 0) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      congr 1
      exact if_congr (hcond h) rfl rfl
    rw [hrw, avoid_prob p _ N, transversal_mass p u hinj pc hp htot τ]
  linarith [hleft ▸ hsum]

/-- **The posterior.**  Under the uniform prior over the `C(a+L,L)` labelings of a
class's unexplored tips (`a` safe, `L = L'+1` unsafe), a fixed unexplored tip is
unsafe with probability exactly `L/(a+L)`. -/
theorem fixed_tip_unsafe_fraction (a L' : ℕ) :
    (((a + L').choose L' : ℕ) : ℝ) / (((a + L' + 1).choose (L' + 1) : ℕ) : ℝ)
      = ((L' : ℝ) + 1) / ((a : ℝ) + (L' : ℝ) + 1) := by
  have hkey : (a + L' + 1) * ((a + L').choose L')
      = ((a + L' + 1).choose (L' + 1)) * (L' + 1) := by
    simpa using Nat.add_one_mul_choose_eq (a + L') L'
  have hpos : 0 < (a + L' + 1).choose (L' + 1) := Nat.choose_pos (by omega)
  have hd1 : (((a + L' + 1).choose (L' + 1) : ℕ) : ℝ) ≠ 0 := by
    have : (0:ℝ) < (((a + L' + 1).choose (L' + 1) : ℕ) : ℝ) := by exact_mod_cast hpos
    exact ne_of_gt this
  have hd2 : ((a : ℝ) + (L' : ℝ) + 1) ≠ 0 := by positivity
  have hcast : ((a : ℝ) + (L' : ℝ) + 1) * (((a + L').choose L' : ℕ) : ℝ)
      = (((a + L' + 1).choose (L' + 1) : ℕ) : ℝ) * ((L' : ℝ) + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hkey
  rw [div_eq_div_iff hd1 hd2]
  linear_combination hcast

/-- A Bayes bound is a minimax bound. -/
theorem bayes_le_minimax {World : Type*} [Fintype World] [Nonempty World]
    (pri R : World → ℝ) (hpi : ∀ w, 0 ≤ pri w) (hsum : ∑ w, pri w = 1) :
    (∑ w, pri w * R w) ≤ (univ : Finset World).sup' univ_nonempty R := by
  classical
  set M := (univ : Finset World).sup' univ_nonempty R with hM
  have hstep : ∀ w : World, pri w * R w ≤ pri w * M := fun w =>
    mul_le_mul_of_nonneg_left (Finset.le_sup' R (mem_univ w)) (hpi w)
  have := Finset.sum_le_sum (fun w (_ : w ∈ (univ : Finset World)) => hstep w)
  have hc : ∑ w, pri w * M = M := by rw [← Finset.sum_mul, hsum, one_mul]
  linarith [hc ▸ this]

/-- …and for an equivariant rule the two coincide, so the Bayes value IS the minimax
value. -/
theorem minimax_eq_of_constant {World : Type*} [Fintype World] [Nonempty World]
    (R : World → ℝ) (r : ℝ) (h : ∀ w, R w = r) :
    (univ : Finset World).sup' univ_nonempty R = r := by
  simp only [h]
  exact le_antisymm (Finset.sup'_le _ _ fun w _ => le_rfl)
    (Finset.le_sup' (fun _ : World => r) (mem_univ (Classical.arbitrary World)))

#print axioms avoid_prob
#print axioms transversal_mass
#print axioms prod_unseen_card
#print axioms prod_unseen_as_sum
#print axioms expected_prod_unseen
#print axioms good_event_lower
#print axioms fixed_tip_unsafe_fraction
#print axioms bayes_le_minimax
#print axioms minimax_eq_of_constant

end CIGAMF.P13.SupportSamplingLaw
