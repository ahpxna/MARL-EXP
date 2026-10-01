import «LeanPaperCPermV1»
import «LeanPaperCUniformV1»

/-!
# Paper C: the weight-preserving relabelling, and the band it DERIVES

`witness_for_Vm_eq_at_zero` (`LeanPaperCPermV1`) still takes the band `hband` as a
hypothesis: it assumes every item's prefix probability is exactly `k/m`.  That is the last
place where C-H1's even side rests on an assumption rather than a construction, and this
module removes it.

The construction is the uniform relabelling inside each weight group.  Let `Gamma` index a
set of permutations that leave every weight where it is, closed under left translation, and
acting transitively on each weight class.  Average the base family over `Gamma`.  Then

* `rankOf_relabel` -- the RANKING does not move at all: `rankOf g (rho * sigma) = rankOf g
  sigma` whenever `rho` preserves weights.  So the objective is untouched by the averaging
  (`regret_relabel_sum`), and no value has to be recomputed.
* `inPrefixInd_relabel` -- but the ITEM the prefix contains does move: relabelling by `rho`
  sends item `i`'s indicator to item `rho.symm i`'s.
* `relMarg_const_of_orbit` -- so the averaged marginal is constant along each orbit, by
  reindexing the average by left translation.
* `relMarg_class_sum` -- and the total over a weight class is unchanged, because each
  relabelling permutes that class.

Feeding those two facts to `marginal_eq_occupancy_div_card` gives `relMarg_eq_uniform`: if
the class occupancy is `|C| * k/m` -- which is exactly what `uniformMix_heavy` and
`uniformMix_light` compute -- then EVERY item sits at `k/m`.  `band_zero_of_relabelling`
states that as membership in `FeasibleAt ... 0`, with no band hypothesis.
-/

namespace CIGAMF.P13.PaperCRelabel

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCValueSet
open CIGAMF.P13.PaperCBreakpoint

variable {m : ℕ}

/-! ## What a weight-preserving relabelling does, and does not, move -/

/-- **The ranking does not move.**  A relabelling that fixes every weight composes into the
identity on the ranking itself, so the objective cannot change. -/
theorem rankOf_relabel (g : Ranking m) (ρ σ : Equiv.Perm (Fin m))
    (hρ : ∀ i, g (ρ i) = g i) : rankOf g (ρ * σ) = rankOf g σ := by
  funext p
  show g ((ρ * σ) p) = g (σ p)
  rw [Equiv.Perm.mul_apply]
  exact hρ (σ p)

/-- **But the item does.**  Relabelling by `rho` carries item `i`'s prefix indicator to
item `rho.symm i`'s. -/
theorem symm_mul_apply (a b : Equiv.Perm (Fin m)) (x : Fin m) :
    (a * b).symm x = b.symm (a.symm x) := rfl

theorem inPrefixInd_relabel (ρ σ : Equiv.Perm (Fin m)) (k : ℕ) (i : Fin m) :
    inPrefixInd (ρ * σ) k i = inPrefixInd σ k (ρ.symm i) := by
  unfold inPrefixInd
  rw [symm_mul_apply]

/-! ## The averaged law -/

variable {Γ R : Type*}

/-- The base family's own per-item marginal at budget `k`. -/
noncomputable def baseMarg [Fintype R] (base : R → Equiv.Perm (Fin m)) (q : R → ℝ)
    (k : ℕ) (j : Fin m) : ℝ :=
  ∑ x, q x * inPrefixInd (base x) k j

/-- The per-item marginal after averaging over the relabellings. -/
noncomputable def relMarg [Fintype Γ] [Fintype R] (act : Γ → Equiv.Perm (Fin m))
    (base : R → Equiv.Perm (Fin m)) (q : R → ℝ) (k : ℕ) (i : Fin m) : ℝ :=
  ∑ p : Γ × R, (q p.2 / (Fintype.card Γ : ℝ)) * inPrefixInd (act p.1 * base p.2) k i

/-- **The averaged marginal, rewritten as an average of base marginals at moved items.** -/
theorem relMarg_eq_avg [Fintype Γ] [Fintype R] (act : Γ → Equiv.Perm (Fin m))
    (base : R → Equiv.Perm (Fin m)) (q : R → ℝ) (k : ℕ) (i : Fin m) :
    relMarg act base q k i
      = (1 / (Fintype.card Γ : ℝ)) * ∑ c : Γ, baseMarg base q k ((act c).symm i) := by
  unfold relMarg baseMarg
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [inPrefixInd_relabel]
  ring

/-- **The averaged marginal is constant along each orbit.**  Left translation by `act c0`
is a bijection of the index, so the average does not see the shift. -/
theorem relMarg_const_of_orbit [Fintype Γ] [Fintype R] (act : Γ → Equiv.Perm (Fin m))
    (base : R → Equiv.Perm (Fin m)) (q : R → ℝ) (k : ℕ)
    (htrans : ∀ c : Γ, ∃ e : Γ ≃ Γ, ∀ c' : Γ, act (e c') = act c * act c')
    (c₀ : Γ) (i : Fin m) :
    relMarg act base q k (act c₀ i) = relMarg act base q k i := by
  rw [relMarg_eq_avg, relMarg_eq_avg]
  congr 1
  obtain ⟨e, he⟩ := htrans c₀
  rw [← Equiv.sum_comp e (fun c => baseMarg base q k ((act c).symm (act c₀ i)))]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  congr 1
  rw [he c', symm_mul_apply, Equiv.symm_apply_apply]

/-- **The total over a weight class is unchanged.**  Each relabelling permutes the class, so
averaging moves mass within it and never across. -/
theorem relMarg_class_sum [Fintype Γ] [Fintype R] [Nonempty Γ]
    (g : Ranking m) (act : Γ → Equiv.Perm (Fin m))
    (hw : ∀ c i, g (act c i) = g i)
    (base : R → Equiv.Perm (Fin m)) (q : R → ℝ) (k : ℕ) (w : ℝ) :
    ∑ i ∈ univ.filter (fun i : Fin m => g i = w), relMarg act base q k i
      = ∑ j ∈ univ.filter (fun j : Fin m => g j = w), baseMarg base q k j := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card Γ : ℝ) := by
    have : 0 < Fintype.card Γ := Fintype.card_pos
    exact_mod_cast this
  have hswap : ∀ c : Γ,
      ∑ i ∈ univ.filter (fun i : Fin m => g i = w), baseMarg base q k ((act c).symm i)
        = ∑ j ∈ univ.filter (fun j : Fin m => g j = w), baseMarg base q k j := by
    intro c
    refine Finset.sum_nbij' (fun i => (act c).symm i) (fun j => act c j) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      have := hw c ((act c).symm i)
      rw [Equiv.apply_symm_apply] at this
      rw [← this, hi]
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      rw [hw c j, hj]
    · intro i _; exact Equiv.apply_symm_apply _ _
    · intro j _; exact Equiv.symm_apply_apply _ _
    · intro i _; rfl
  calc ∑ i ∈ univ.filter (fun i : Fin m => g i = w), relMarg act base q k i
      = ∑ i ∈ univ.filter (fun i : Fin m => g i = w),
          (1 / (Fintype.card Γ : ℝ)) * ∑ c : Γ, baseMarg base q k ((act c).symm i) :=
        Finset.sum_congr rfl (fun i _ => relMarg_eq_avg act base q k i)
    _ = (1 / (Fintype.card Γ : ℝ)) * ∑ c : Γ,
          ∑ i ∈ univ.filter (fun i : Fin m => g i = w), baseMarg base q k ((act c).symm i) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (1 / (Fintype.card Γ : ℝ)) * ∑ _c : Γ,
          ∑ j ∈ univ.filter (fun j : Fin m => g j = w), baseMarg base q k j := by
        rw [Finset.sum_congr rfl (fun c _ => hswap c)]
    _ = ∑ j ∈ univ.filter (fun j : Fin m => g j = w), baseMarg base q k j := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        field_simp

/-- **(The band, derived.)**  Transitivity on each weight class plus a class occupancy of
`|C| * k/m` forces EVERY item to sit at exactly `k/m`. -/
theorem relMarg_eq_uniform [Fintype Γ] [Fintype R] [Nonempty Γ]
    (g : Ranking m) (act : Γ → Equiv.Perm (Fin m))
    (hw : ∀ c i, g (act c i) = g i)
    (htrans : ∀ c : Γ, ∃ e : Γ ≃ Γ, ∀ c' : Γ, act (e c') = act c * act c')
    (horbit : ∀ i j : Fin m, g i = g j → ∃ c : Γ, act c i = j)
    (base : R → Equiv.Perm (Fin m)) (q : R → ℝ) (k : ℕ)
    (hclass : ∀ w : ℝ,
      ∑ j ∈ univ.filter (fun j : Fin m => g j = w), baseMarg base q k j
        = ((univ.filter (fun j : Fin m => g j = w)).card : ℝ) * ((k : ℝ) / (m : ℝ)))
    (i : Fin m) :
    relMarg act base q k i = (k : ℝ) / (m : ℝ) := by
  classical
  set C : Finset (Fin m) := univ.filter (fun j : Fin m => g j = g i) with hC
  have hiC : i ∈ C := by simp [hC]
  have hCne : C.Nonempty := ⟨i, hiC⟩
  have hconst : ∀ a ∈ C, ∀ b ∈ C, relMarg act base q k a = relMarg act base q k b := by
    intro a ha b hb
    simp only [hC, mem_filter, mem_univ, true_and] at ha hb
    obtain ⟨c, hc⟩ := horbit a b (by rw [ha, hb])
    rw [← hc, relMarg_const_of_orbit act base q k htrans c a]
  have hocc : ∑ j ∈ C, relMarg act base q k j
      = ((C.card : ℝ)) * ((k : ℝ) / (m : ℝ)) := by
    rw [hC, relMarg_class_sum g act hw base q k (g i), hclass (g i)]
  have h := marginal_eq_occupancy_div_card C hCne (relMarg act base q k)
    (((C.card : ℝ)) * ((k : ℝ) / (m : ℝ))) hconst hocc i hiC
  rw [h]
  have hcard : ((C.card : ℝ)) ≠ 0 := by
    have : 0 < C.card := Finset.card_pos.mpr hCne
    positivity
  field_simp

/-! ## The objective is untouched -/

/-- **Averaging over relabellings changes no regret.**  Every term is the base term, because
the ranking itself is unmoved. -/
theorem regret_relabel_sum [Fintype Γ] [Fintype R] [Nonempty Γ]
    (g : Ranking m) (act : Γ → Equiv.Perm (Fin m))
    (hw : ∀ c i, g (act c i) = g i)
    (base : R → Equiv.Perm (Fin m)) (q : R → ℝ) (D : ℝ) (k : ℕ) :
    (∑ p : Γ × R, (q p.2 / (Fintype.card Γ : ℝ)) * regret g (act p.1 * base p.2) D k)
      = ∑ x, q x * regret g (base x) D k := by
  have hcard : (0 : ℝ) < (Fintype.card Γ : ℝ) := by
    have : 0 < Fintype.card Γ := Fintype.card_pos
    exact_mod_cast this
  have hterm : ∀ c : Γ, ∀ x : R,
      regret g (act c * base x) D k = regret g (base x) D k := by
    intro c x
    unfold regret
    rw [rankOf_relabel g (act c) (base x) (hw c)]
  rw [Fintype.sum_prod_type]
  calc ∑ c : Γ, ∑ x : R, (q x / (Fintype.card Γ : ℝ)) * regret g (act c * base x) D k
      = ∑ _c : Γ, (1 / (Fintype.card Γ : ℝ)) * ∑ x : R, q x * regret g (base x) D k := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hterm c x]
        ring
    _ = ∑ x : R, q x * regret g (base x) D k := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        field_simp

/-! ## The law is feasible at `eta = 0`, with nothing about the band assumed -/

/-- **(C-H1 feasibility, unconditional in the band.)**  The relabelled law is in
`FeasibleAt ... 0`: nonnegativity and total mass come from the base weights, and the band
comes from `relMarg_eq_uniform` rather than from a hypothesis. -/
theorem band_zero_of_relabelling [Fintype Γ] [Fintype R] [Nonempty Γ]
    (g : Ranking m) (act : Γ → Equiv.Perm (Fin m))
    (hw : ∀ c i, g (act c i) = g i)
    (htrans : ∀ c : Γ, ∃ e : Γ ≃ Γ, ∀ c' : Γ, act (e c') = act c * act c')
    (horbit : ∀ i j : Fin m, g i = g j → ∃ c : Γ, act c i = j)
    (base : R → Equiv.Perm (Fin m)) (q : R → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (hclass : ∀ (k : ℕ), k ≤ m → ∀ w : ℝ,
      ∑ j ∈ univ.filter (fun j : Fin m => g j = w), baseMarg base q k j
        = ((univ.filter (fun j : Fin m => g j = w)).card : ℝ) * ((k : ℝ) / (m : ℝ))) :
    (fun p : Γ × R => q p.2 / (Fintype.card Γ : ℝ))
      ∈ FeasibleAt (fun p : Γ × R => act p.1 * base p.2) (0 : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card Γ : ℝ) := by
    have : 0 < Fintype.card Γ := Fintype.card_pos
    exact_mod_cast this
  refine ⟨fun p => div_nonneg (hq p.2) hcard.le, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    calc ∑ _c : Γ, ∑ x : R, q x / (Fintype.card Γ : ℝ)
        = ∑ _c : Γ, (1 / (Fintype.card Γ : ℝ)) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [← Finset.sum_div, hq1]
      _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          field_simp
  · intro k hk i
    have h : (∑ p : Γ × R, (q p.2 / (Fintype.card Γ : ℝ))
        * inPrefixInd (act p.1 * base p.2) k i) = (k : ℝ) / (m : ℝ) :=
      relMarg_eq_uniform g act hw htrans horbit base q k (hclass k hk) i
    rw [h, sub_self, abs_zero]
    simp

/-! ## The hypotheses are satisfiable: the weight-preserving subgroup

`band_zero_of_relabelling` asks for an index `Gamma` that is weight-preserving, closed under
left translation, and transitive on each weight class.  A conditional whose hypotheses cannot
all hold at once proves nothing, so one index satisfying all three is exhibited here: the
full subgroup of permutations that fix every weight.  Transitivity is the transposition
`swap i j`, which preserves weights precisely when `g i = g j`. -/

/-- The relabellings that leave every weight where it is. -/
def WPerm (g : Ranking m) : Type :=
  {ρ : Equiv.Perm (Fin m) // ∀ i, g (ρ i) = g i}

instance (g : Ranking m) : Finite (WPerm g) := Subtype.finite

noncomputable instance (g : Ranking m) : Fintype (WPerm g) := Fintype.ofFinite _

instance (g : Ranking m) : Nonempty (WPerm g) := ⟨⟨1, fun _ => rfl⟩⟩

/-- A weight-preserving relabelling has a weight-preserving inverse. -/
theorem wperm_inv (g : Ranking m) (c : WPerm g) (i : Fin m) :
    g ((c.1⁻¹ : Equiv.Perm (Fin m)) i) = g i := by
  have h := c.2 ((c.1⁻¹ : Equiv.Perm (Fin m)) i)
  have hx : (c.1 : Equiv.Perm (Fin m)) ((c.1⁻¹ : Equiv.Perm (Fin m)) i) = i := by
    simp
  rw [hx] at h
  exact h.symm

/-- **Left translation is a bijection of the subgroup** -- the closure `htrans` asks for. -/
theorem wperm_trans (g : Ranking m) (c : WPerm g) :
    ∃ e : WPerm g ≃ WPerm g, ∀ c' : WPerm g,
      (Subtype.val (e c') : Equiv.Perm (Fin m)) = Subtype.val c * Subtype.val c' := by
  refine ⟨⟨fun c' => ⟨c.1 * c'.1, ?_⟩, fun c' => ⟨c.1⁻¹ * c'.1, ?_⟩, ?_, ?_⟩, fun _ => rfl⟩
  · intro i
    rw [Equiv.Perm.mul_apply, c.2, c'.2]
  · intro i
    rw [Equiv.Perm.mul_apply, wperm_inv g c, c'.2]
  · intro c'
    apply Subtype.ext
    show c.1⁻¹ * (c.1 * c'.1) = c'.1
    rw [inv_mul_cancel_left]
  · intro c'
    apply Subtype.ext
    show c.1 * (c.1⁻¹ * c'.1) = c'.1
    rw [mul_inv_cancel_left]

/-- **The subgroup is transitive on each weight class** -- the `horbit` hypothesis, by a
transposition. -/
theorem wperm_orbit (g : Ranking m) (i j : Fin m) (h : g i = g j) :
    ∃ c : WPerm g, (Subtype.val c : Equiv.Perm (Fin m)) i = j := by
  classical
  refine ⟨⟨Equiv.swap i j, fun x => ?_⟩, Equiv.swap_apply_left i j⟩
  rcases eq_or_ne x i with rfl | hxi
  · rw [Equiv.swap_apply_left]; exact h.symm
  · rcases eq_or_ne x j with rfl | hxj
    · rw [Equiv.swap_apply_right]; exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]

/-- **(The band, with nothing left to satisfy.)**  Instantiating `band_zero_of_relabelling`
at the weight-preserving subgroup: the only remaining input is the class occupancy, which is
what `uniformMix_heavy` and `uniformMix_light` compute.  No band, no transitivity and no
closure is assumed -- all three are discharged. -/
theorem band_zero_at_weight_group [Fintype R]
    (g : Ranking m) (base : R → Equiv.Perm (Fin m)) (q : R → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (hclass : ∀ (k : ℕ), k ≤ m → ∀ w : ℝ,
      ∑ j ∈ univ.filter (fun j : Fin m => g j = w), baseMarg base q k j
        = ((univ.filter (fun j : Fin m => g j = w)).card : ℝ) * ((k : ℝ) / (m : ℝ))) :
    (fun p : WPerm g × R => q p.2 / (Fintype.card (WPerm g) : ℝ))
      ∈ FeasibleAt (fun p : WPerm g × R => (Subtype.val p.1 : Equiv.Perm (Fin m)) * base p.2)
        (0 : ℝ) :=
  band_zero_of_relabelling g (fun c : WPerm g => (Subtype.val c : Equiv.Perm (Fin m)))
    (fun c => c.2) (wperm_trans g) (wperm_orbit g) base q hq hq1 hclass

/-! ## The witness, assembled: feasibility and value for ONE law

`band_zero_at_weight_group` gives feasibility and `regret_relabel_sum` gives the value, but
they are two statements about the same law and nothing yet says so.  This is that statement.
It is what `witness_for_Vm_eq_at_zero` needed `hband` for, and the band is no longer an
input: only the class occupancy and the base family's own value are, and both of those are
computations rather than assumptions. -/
theorem witness_of_relabelled [Fintype R]
    (g : Ranking m) (base : R → Equiv.Perm (Fin m)) (q : R → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (hclass : ∀ (k : ℕ), k ≤ m → ∀ w : ℝ,
      ∑ j ∈ univ.filter (fun j : Fin m => g j = w), baseMarg base q k j
        = ((univ.filter (fun j : Fin m => g j = w)).card : ℝ) * ((k : ℝ) / (m : ℝ)))
    (D V : ℝ) (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hvalue : ∀ k ∈ budgets, (∑ x, q x * regret g (base x) D k) = V) :
    (fun p : WPerm g × R => q p.2 / (Fintype.card (WPerm g) : ℝ))
        ∈ FeasibleAt (fun p : WPerm g × R =>
            (Subtype.val p.1 : Equiv.Perm (Fin m)) * base p.2) (0 : ℝ)
      ∧ maxRegret (fun p : WPerm g × R => q p.2 / (Fintype.card (WPerm g) : ℝ)) g
          (fun p : WPerm g × R => (Subtype.val p.1 : Equiv.Perm (Fin m)) * base p.2)
          D budgets hne = V := by
  refine ⟨band_zero_at_weight_group g base q hq hq1 hclass, ?_⟩
  have hterm : ∀ k ∈ budgets,
      (∑ p : WPerm g × R, (q p.2 / (Fintype.card (WPerm g) : ℝ))
        * regret g ((Subtype.val p.1 : Equiv.Perm (Fin m)) * base p.2) D k) = V := by
    intro k hk
    rw [regret_relabel_sum g (fun c : WPerm g => (Subtype.val c : Equiv.Perm (Fin m)))
      (fun c => c.2) base q D k]
    exact hvalue k hk
  unfold maxRegret
  refine le_antisymm (Finset.sup'_le hne _ (fun k hk => le_of_eq (hterm k hk))) ?_
  obtain ⟨k0, hk0⟩ := hne
  rw [← hterm k0 hk0]
  exact Finset.le_sup' (fun k => ∑ p : WPerm g × R,
    (q p.2 / (Fintype.card (WPerm g) : ℝ))
      * regret g ((Subtype.val p.1 : Equiv.Perm (Fin m)) * base p.2) D k) hk0

/-! ## The join: item marginals and position counts are the same number

Everything Paper C computes about the even mixture -- `countIns`, `mixCount`, `flatCount`,
`uniformMix` -- counts POSITIONS: how many of the first `k` slots of a ranking carry a given
weight.  Everything the band is about -- `inPrefixInd`, `baseMarg`, `hclass` -- counts ITEMS:
how likely a given item is to land in the prefix.  The two sides have never been connected,
which is why `hclass` was still an input.

`class_count_eq_prefix_count` connects them, and it is an identity, not an estimate:
reindexing the class sum by the permutation turns "the items of weight `w` that landed in the
prefix" into "the prefix positions carrying weight `w`".  `hclass_of_position_counts` then
converts any position-count computation into the band hypothesis, so the arithmetic already
proved elsewhere can discharge it. -/

/-- **The class occupancy equals the prefix's weight count.** -/
theorem class_count_eq_prefix_count (g : Ranking m) (σ : Equiv.Perm (Fin m)) (k : ℕ)
    (w : ℝ) :
    ∑ j ∈ univ.filter (fun j : Fin m => g j = w), inPrefixInd σ k j
      = ∑ p ∈ univ.filter (fun p : Fin m => (p : ℕ) < k),
          (if g (σ p) = w then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Equiv.sum_comp σ (fun j => if g j = w then inPrefixInd σ k j else 0)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hp : inPrefixInd σ k (σ p) = if ((p : Fin m) : ℕ) < k then (1 : ℝ) else 0 := by
    unfold inPrefixInd
    rw [Equiv.symm_apply_apply]
  rw [hp]
  split_ifs <;> rfl

/-- **(The band hypothesis, from a position count.)**  Anything proved about how many prefix
positions carry weight `w` -- which is the form every Paper C computation is already in --
discharges `hclass` for that weight. -/
theorem hclass_of_position_counts [Fintype R] (g : Ranking m)
    (base : R → Equiv.Perm (Fin m)) (q : R → ℝ) (k : ℕ) (w : ℝ)
    (hpos : (∑ x, q x * ∑ p ∈ univ.filter (fun p : Fin m => (p : ℕ) < k),
              (if g (base x p) = w then (1 : ℝ) else 0))
            = ((univ.filter (fun j : Fin m => g j = w)).card : ℝ) * ((k : ℝ) / (m : ℝ))) :
    ∑ j ∈ univ.filter (fun j : Fin m => g j = w), baseMarg base q k j
      = ((univ.filter (fun j : Fin m => g j = w)).card : ℝ) * ((k : ℝ) / (m : ℝ)) := by
  classical
  rw [← hpos]
  unfold baseMarg
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.mul_sum, class_count_eq_prefix_count g (base x) k w]

/-! ## Audit -/

#print axioms symm_mul_apply
#print axioms rankOf_relabel
#print axioms inPrefixInd_relabel
#print axioms relMarg_eq_avg
#print axioms relMarg_const_of_orbit
#print axioms relMarg_class_sum
#print axioms relMarg_eq_uniform
#print axioms regret_relabel_sum
#print axioms band_zero_of_relabelling
#print axioms wperm_inv
#print axioms wperm_trans
#print axioms wperm_orbit
#print axioms band_zero_at_weight_group
#print axioms witness_of_relabelled
#print axioms class_count_eq_prefix_count
#print axioms hclass_of_position_counts

end CIGAMF.P13.PaperCRelabel
