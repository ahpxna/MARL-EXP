import Mathlib

/-!
# The degree of an admissible measurement sets the order at which a world becomes visible.

## WHY THIS MODULE EXISTS

The corpus proves rate theorems for queries whose informativeness is supplied as a
hypothesis.  What is missing is a law saying WHICH queries are informative, and at what
order, from a property of the query itself.  This file supplies one, for the admissible
class in which the query is a bounded low-degree polynomial of a latent sign vector.

Fix the latent `z` uniform on `{-1,1}^n` and the two worlds distinguished by the top
character `chi(z) = prod_i z_i`.  A measurement of degree at most `d` returns a noisy
`h * g(z)` on top of the world's own contribution.  The claim is that the first moment
in which the two worlds differ is the `s`-th, with

    s = ceil(n / d),

and that this is attained.  Since a difference first visible at order `s` puts the two
observation laws `Theta(h^s)` apart in Hellinger, the sample cost is `Theta(h^(-2s))`.

## WHAT IS PROVED

* `expect_chi` -- `sum_z chi_S(z) = 0` for every non-empty `S`: the orthogonality that
  drives everything, proved by factorising the sum over coordinates.
* `chi_mul` -- `chi_S * chi_T = chi_(S symmDiff T)`, from `sgn b * sgn b = 1`.
* `HasDeg_mul` -- **the degree of a product adds**: this is the only real work, and it is
  done by reindexing the coefficient sum along the involution `U -> S symmDiff U`.
* `HasDeg_pow` -- hence `g^j` has degree at most `j * d`.
* `top_character_orthogonal` -- `sum_z chi_univ(z) h(z) = 0` whenever `h` has degree
  below `n`, because the only set that survives against the top character is `univ`.
* `moment_vanishes_below_order` -- **the law**: for every admissible `g` of degree at most
  `d` and every `j` with `j * d < n`, the `j`-th mixed moment `E[chi g^j]` is exactly `0`.
* `order_of_ceil_div` -- `(ceil (n/d) - 1) * d < n`, the arithmetic that turns the above
  into "every moment below `s` vanishes".
* `moment_vanishes_below_s` -- the two combined, stated in terms of `s`.

## WHAT THIS DOES NOT ESTABLISH

- **Attainment is not proved here.**  That the block query
  `g = (1/s) sum_l prod_(i in B_l) z_i` achieves `E[chi g^s] = s!/s^s` is checked in exact
  arithmetic in `scripts/EXP_unified_query_order.py` for every `(n,d)` in the evidence
  table, but it is not formalised.  Only the VANISHING half is proved here, so what this
  module supports is the lower bound on cost, not the matching upper bound.
- The step from vanishing moments to a Hellinger rate is not formalised either.  The
  measured log-log slopes agree with `2s` to within `0.06` in the same script, and that is
  evidence, not proof.
- `sgn` is real-valued and the sums are unnormalised: `expect_chi` is a sum, not an
  average, so the `2^n` factors are carried explicitly rather than divided out.
- Nothing here is claimed as new mechanism.  Higher algebraic degree postponing the first
  informative moment is exactly the phenomenon the masking literature describes, and the
  contribution claimed is the exact order law for THIS admissible class, which is what the
  downstream decision cost consumes.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.UnifiedQueryOrder

open Finset

variable {n : ℕ}

/-! ### Characters of the latent sign vector -/

/-- A latent coordinate as a sign. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

@[simp] theorem sgn_sum : ∑ b : Bool, sgn b = 0 := by
  simp [sgn]

/-- The character indexed by a set of coordinates. -/
def chiS (S : Finset (Fin n)) (z : Fin n → Bool) : ℝ := ∏ i ∈ S, sgn (z i)

@[simp] theorem chiS_empty (z : Fin n → Bool) : chiS (∅ : Finset (Fin n)) z = 1 := by
  simp [chiS]

/-- **Characters multiply to the character of the symmetric difference.** -/
theorem chiS_mul (S T : Finset (Fin n)) (z : Fin n → Bool) :
    chiS S z * chiS T z = chiS (symmDiff S T) z := by
  classical
  have hS : (S \ T) ∪ (S ∩ T) = S := Finset.sdiff_union_inter S T
  have hT : (T \ S) ∪ (T ∩ S) = T := Finset.sdiff_union_inter T S
  have hdS : Disjoint (S \ T) (S ∩ T) :=
    Finset.disjoint_left.2 fun a ha hb => (Finset.mem_sdiff.1 ha).2 (Finset.mem_inter.1 hb).2
  have hdT : Disjoint (T \ S) (T ∩ S) :=
    Finset.disjoint_left.2 fun a ha hb => (Finset.mem_sdiff.1 ha).2 (Finset.mem_inter.1 hb).2
  have hdD : Disjoint (S \ T) (T \ S) :=
    Finset.disjoint_left.2 fun a ha hb => (Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1
  have hsymm : symmDiff S T = (S \ T) ∪ (T \ S) := rfl
  have hTS : T ∩ S = S ∩ T := Finset.inter_comm T S
  calc chiS S z * chiS T z
      = (∏ i ∈ (S \ T) ∪ (S ∩ T), sgn (z i)) * (∏ i ∈ (T \ S) ∪ (T ∩ S), sgn (z i)) := by
        rw [hS, hT]; rfl
    _ = ((∏ i ∈ S \ T, sgn (z i)) * (∏ i ∈ S ∩ T, sgn (z i)))
          * ((∏ i ∈ T \ S, sgn (z i)) * (∏ i ∈ T ∩ S, sgn (z i))) := by
        rw [Finset.prod_union hdS, Finset.prod_union hdT]
    _ = ((∏ i ∈ S \ T, sgn (z i)) * (∏ i ∈ T \ S, sgn (z i)))
          * ∏ i ∈ S ∩ T, (sgn (z i) * sgn (z i)) := by
        rw [hTS, Finset.prod_mul_distrib]; ring
    _ = (∏ i ∈ S \ T, sgn (z i)) * (∏ i ∈ T \ S, sgn (z i)) := by
        simp
    _ = chiS (symmDiff S T) z := by
        rw [hsymm, chiS, Finset.prod_union hdD]

/-- **Orthogonality.**  Summed over the whole cube, every non-trivial character cancels.
Proved by factorising the sum over coordinates: each coordinate in `S` contributes
`sgn true + sgn false = 0`. -/
theorem expect_chi (S : Finset (Fin n)) :
    ∑ z : Fin n → Bool, chiS S z = if S = ∅ then (2 : ℝ) ^ n else 0 := by
  classical
  have key : ∀ z : Fin n → Bool,
      chiS S z = ∏ i : Fin n, (if i ∈ S then sgn (z i) else 1) := by
    intro z
    rw [chiS, ← Finset.prod_filter]
    congr 1
    ext a
    simp
  have hfac : (∑ z : Fin n → Bool, ∏ i : Fin n, (if i ∈ S then sgn (z i) else 1))
      = ∏ i : Fin n, ∑ b : Bool, (if i ∈ S then sgn b else 1) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [key]
  rw [hfac]
  by_cases hS : S = ∅
  · subst hS
    simp
  · rw [if_neg hS]
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hS
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [ha, sgn]

/-! ### Degree -/

/-- `HasDeg D h` : `h` is a real combination of characters of sets of at most `D`
coordinates.  This is the admissible class: bounded degree, arbitrary coefficients. -/
def HasDeg (D : ℕ) (h : (Fin n → Bool) → ℝ) : Prop :=
  ∃ c : Finset (Fin n) → ℝ,
    (∀ S, c S ≠ 0 → S.card ≤ D) ∧ ∀ z, h z = ∑ S : Finset (Fin n), c S * chiS S z

theorem HasDeg_one : HasDeg (n := n) 0 (fun _ => 1) := by
  classical
  refine ⟨fun S => if S = ∅ then 1 else 0, ?_, ?_⟩
  · intro S hS
    by_cases h : S = ∅
    · simp [h]
    · simp [h] at hS
  · intro z
    rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h

theorem HasDeg_mono {D D' : ℕ} {h : (Fin n → Bool) → ℝ} (hD : D ≤ D')
    (hh : HasDeg D h) : HasDeg D' h := by
  obtain ⟨c, hsupp, hval⟩ := hh
  exact ⟨c, fun S hS => le_trans (hsupp S hS) hD, hval⟩

private theorem card_symmDiff_le (S T : Finset (Fin n)) :
    (symmDiff S T).card ≤ S.card + T.card := by
  classical
  have hsub : symmDiff S T ⊆ S ∪ T := by
    intro a ha
    rcases Finset.mem_symmDiff.1 ha with ⟨h, _⟩ | ⟨h, _⟩
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le S T)

/-- **Degrees add under multiplication.**  The coefficient of `U` in the product is
`sum_S c1 S * c2 (S symmDiff U)`, and the value identity is obtained by reindexing that
sum along the involution `U -> S symmDiff U`. -/
theorem HasDeg_mul {D₁ D₂ : ℕ} {h₁ h₂ : (Fin n → Bool) → ℝ}
    (hh₁ : HasDeg D₁ h₁) (hh₂ : HasDeg D₂ h₂) :
    HasDeg (D₁ + D₂) (fun z => h₁ z * h₂ z) := by
  classical
  obtain ⟨c₁, hs₁, hv₁⟩ := hh₁
  obtain ⟨c₂, hs₂, hv₂⟩ := hh₂
  refine ⟨fun U => ∑ S : Finset (Fin n), c₁ S * c₂ (symmDiff S U), ?_, ?_⟩
  · -- support: a non-zero coefficient needs some S with both factors non-zero
    intro U hU
    by_contra hcard
    push_neg at hcard
    apply hU
    apply Finset.sum_eq_zero
    intro S _
    by_cases h1 : c₁ S = 0
    · simp [h1]
    by_cases h2 : c₂ (symmDiff S U) = 0
    · simp [h2]
    exfalso
    have e1 := hs₁ S h1
    have e2 := hs₂ (symmDiff S U) h2
    have hU' : U = symmDiff S (symmDiff S U) := (symmDiff_symmDiff_cancel_left S U).symm
    have : U.card ≤ D₁ + D₂ := by
      calc U.card = (symmDiff S (symmDiff S U)).card := by rw [← hU']
        _ ≤ S.card + (symmDiff S U).card := card_symmDiff_le _ _
        _ ≤ D₁ + D₂ := Nat.add_le_add e1 e2
    omega
  · -- value
    intro z
    show h₁ z * h₂ z
      = ∑ U : Finset (Fin n), (∑ S : Finset (Fin n), c₁ S * c₂ (symmDiff S U)) * chiS U z
    have step1 : (∑ U : Finset (Fin n),
          (∑ S : Finset (Fin n), c₁ S * c₂ (symmDiff S U)) * chiS U z)
        = ∑ U : Finset (Fin n), ∑ S : Finset (Fin n),
            c₁ S * c₂ (symmDiff S U) * chiS U z := by
      refine Finset.sum_congr rfl ?_
      intro U _
      rw [Finset.sum_mul]
    have step3 : ∀ S : Finset (Fin n),
        (∑ U : Finset (Fin n), c₁ S * c₂ (symmDiff S U) * chiS U z)
          = ∑ T : Finset (Fin n), (c₁ S * chiS S z) * (c₂ T * chiS T z) := by
      intro S
      refine Fintype.sum_bijective (fun U => symmDiff S U)
        (Function.Involutive.bijective (fun U => symmDiff_symmDiff_cancel_left S U))
        (fun U => c₁ S * c₂ (symmDiff S U) * chiS U z)
        (fun T => (c₁ S * chiS S z) * (c₂ T * chiS T z)) ?_
      intro U
      have hc : chiS S z * chiS (symmDiff S U) z = chiS U z := by
        rw [chiS_mul, symmDiff_symmDiff_cancel_left]
      calc c₁ S * c₂ (symmDiff S U) * chiS U z
          = c₁ S * c₂ (symmDiff S U) * (chiS S z * chiS (symmDiff S U) z) := by rw [hc]
        _ = c₁ S * chiS S z * (c₂ (symmDiff S U) * chiS (symmDiff S U) z) := by ring
    rw [step1, Finset.sum_comm]
    simp_rw [step3]
    rw [hv₁ z, hv₂ z, Finset.sum_mul_sum]

/-- **Degree under powers.** -/
theorem HasDeg_pow {D : ℕ} {h : (Fin n → Bool) → ℝ} (hh : HasDeg D h) :
    ∀ j : ℕ, HasDeg (j * D) (fun z => (h z) ^ j) := by
  intro j
  induction j with
  | zero => simpa using HasDeg_one (n := n)
  | succ k ih =>
      have := HasDeg_mul ih hh
      have heq : (fun z => (h z) ^ k * h z) = fun z => (h z) ^ (k + 1) := by
        funext z; ring
      rw [heq] at this
      have : HasDeg (k * D + D) (fun z => (h z) ^ (k + 1)) := this
      simpa [Nat.succ_mul] using this

/-! ### The order law -/

/-- **Nothing below the top degree survives against the top character.** -/
theorem top_character_orthogonal {D : ℕ} (hD : D < n)
    {h : (Fin n → Bool) → ℝ} (hh : HasDeg D h) :
    ∑ z : Fin n → Bool, chiS (univ : Finset (Fin n)) z * h z = 0 := by
  classical
  obtain ⟨c, hsupp, hval⟩ := hh
  have hstep : ∀ z : Fin n → Bool,
      chiS (univ : Finset (Fin n)) z * h z
        = ∑ S : Finset (Fin n), c S * chiS (symmDiff univ S) z := by
    intro z
    rw [hval z, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [show chiS (univ : Finset (Fin n)) z * (c S * chiS S z)
        = c S * (chiS (univ : Finset (Fin n)) z * chiS S z) by ring, chiS_mul]
  simp_rw [hstep]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro S _
  rw [← Finset.mul_sum, expect_chi]
  by_cases hc : c S = 0
  · simp [hc]
  · have hcard : S.card ≤ D := hsupp S hc
    have hne : symmDiff (univ : Finset (Fin n)) S ≠ ∅ := by
      intro hempty
      have heq : (univ : Finset (Fin n)) = S := symmDiff_eq_bot.1 (by simpa using hempty)
      rw [← heq] at hcard
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      omega
    simp [hne]

/-- The arithmetic behind the order: below `ceil (n/d)`, the accumulated degree is still
short of `n`. -/
theorem order_of_ceil_div (n d : ℕ) (hd : 0 < d) (j : ℕ) (hj : j < (n + d - 1) / d) :
    j * d < n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hz : (0 + d - 1) / d = 0 := Nat.div_eq_of_lt (by omega)
      rw [hz] at hj
      omega
    · exact h
  have h1 : (j + 1) * d ≤ n + d - 1 := (Nat.le_div_iff_mul_le hd).1 hj
  have h2 : (j + 1) * d = j * d + d := by ring
  rw [h2] at h1
  obtain ⟨k, hk⟩ : ∃ k, j * d = k := ⟨_, rfl⟩
  rw [hk] at h1 ⊢
  omega

/-- **The law.**  Every mixed moment of the top character against a power of an admissible
query vanishes, as long as the accumulated degree stays below `n`. -/
theorem moment_vanishes_below_order {d j : ℕ} {g : (Fin n → Bool) → ℝ}
    (hg : HasDeg d g) (hjd : j * d < n) :
    ∑ z : Fin n → Bool, chiS (univ : Finset (Fin n)) z * (g z) ^ j = 0 :=
  top_character_orthogonal hjd (HasDeg_pow hg j)

/-- **The same law, phrased at the order `s = ceil (n/d)`.**  Every moment strictly below
`s` vanishes, so the two worlds are invisible to an admissible degree-`d` query until the
`s`-th. -/
theorem moment_vanishes_below_s {d : ℕ} (hd : 0 < d) {g : (Fin n → Bool) → ℝ}
    (hg : HasDeg d g) (j : ℕ) (hj : j < (n + d - 1) / d) :
    ∑ z : Fin n → Bool, chiS (univ : Finset (Fin n)) z * (g z) ^ j = 0 :=
  moment_vanishes_below_order hg (order_of_ceil_div n d hd j hj)

/-- A degree-`n` query is informative immediately: the top character is itself admissible
at `d = n`, and its first moment is `2^n`, not `0`.  So the vanishing above is a statement
about the DEGREE BUDGET and not an artefact of the argument. -/
theorem top_query_is_informative_at_first_order :
    ∑ z : Fin n → Bool,
        chiS (univ : Finset (Fin n)) z * (chiS (univ : Finset (Fin n)) z) ^ 1
      = (2 : ℝ) ^ n := by
  classical
  have : ∀ z : Fin n → Bool,
      chiS (univ : Finset (Fin n)) z * (chiS (univ : Finset (Fin n)) z) ^ 1
        = chiS (symmDiff (univ : Finset (Fin n)) univ) z := by
    intro z; rw [pow_one, chiS_mul]
  simp_rw [this]
  rw [expect_chi]
  simp

#print axioms chiS_mul
#print axioms expect_chi
#print axioms HasDeg_mul
#print axioms HasDeg_pow
#print axioms top_character_orthogonal
#print axioms order_of_ceil_div
#print axioms moment_vanishes_below_order
#print axioms moment_vanishes_below_s
#print axioms top_query_is_informative_at_first_order

end CIGAMF.P13.UnifiedQueryOrder
