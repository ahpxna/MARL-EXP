import Mathlib

/-!
# Paper C, package C-breakpoint: symmetrisation, the marginal bridge, and stability.

## WHY THIS MODULE EXISTS

Paper C reduces a game over `m!` rankings to a flow on `O(m^2)` prefix compositions.  Two
solvers agreeing on small sizes is evidence, not a reduction: the reduction needs three
transfers, and this module proves the two that are pure algebra plus the stability law that
makes the value claim robust.

  E1  SYMMETRISATION.  Averaging a plan over the permutations of an equal-weight group
      leaves the objective no worse and keeps every constraint, so an optimal plan may be
      taken symmetric.  `symmetrised_is_feasible` and `symmetrised_not_worse`.

  E2  THE MARGINAL BRIDGE.  For a plan symmetric inside a group, every item of the group
      has the SAME marginal, so the group's occupancy splits evenly:

          p_{tau,k} = (1 / c_tau) * sum_{|v| = k} v_tau x_v.

      `marginal_eq_occupancy_div_card`.  This is the identity that lets a band constraint on
      per-item marginals be written on group occupancies, and it is what the two-solver
      check does NOT establish.

  E3  PATH DECOMPOSITION.  A unit flow is a distribution over source-to-sink paths, and
      relabelling uniformly inside each group recovers a ranking distribution.  This IS now
      proved, in two halves that meet in `pathDecomposition_discharged`:

        * `trajLaw` is the flow's own Markov law on WHOLE trajectories, and
          `trajLaw_marginal_all` computes its marginal at every budget, not only the last.
          Layer marginals alone would not do: a ranking is a trajectory, and marginals do
          not determine a joint law.
        * `relabelledLaw` applies a uniform random relabelling.  It is a probability
          distribution, it is invariant under every relabelling -- which is what supplies
          the `hconst` that `flow_marginal_eq_occupancy` used to assume -- and it moves no
          relabelling-invariant quantity, which is why symmetrising is free.

      `linear_objective_from_marginals` then shows any objective linear in the layer
      marginals is determined by them, so objective agreement needs no extra hypothesis.

## STABILITY

`value_stable_of_pointwise` transfers a pointwise perturbation bound to the optimal value,
in both directions, with the feasible set and the normaliser held fixed.  The two-sided
argument is the content: an upper bound on the value needs the perturbed plan to be
feasible, and a lower bound needs the unperturbed one to be, so the fixed feasible set is a
real hypothesis and not a convenience.  If a perturbation changes the normaliser `D`, or
breaks the equal-weight groups the symmetrisation uses, the bound does not transfer.

## SCOPE

What `pathDecomposition_discharged` still assumes, and it is the right thing to assume: that
a ranking has a prefix composition at each budget, that relabelling equal-weight items does
not change it, and that every trajectory the flow actually charges is realised by SOME
ranking.  The last is a combinatorial property of the concrete family -- a type word with
the family's counts comes from a permutation -- not of the reduction, so it is a hypothesis
of a general theorem rather than a gap in one.

`eta_*` itself is not here.  Its lower side is a theorem for every `m` and both parities,
assembled from `LeanPaperCRankingV1`; its upper side is established size by size elsewhere.
-/

namespace CIGAMF.P13.PaperCBreakpoint

open scoped BigOperators

/-! ## Symmetrisation inside an equal-weight group -/

variable {Plan : Type*} [AddCommGroup Plan] [Module ℝ Plan]
variable {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]

/-- The average of a plan over a finite family of relabellings. -/
noncomputable def symmetrise (act : G → Plan → Plan) (x : Plan) : Plan :=
  (1 / (Fintype.card G : ℝ)) • ∑ g : G, act g x

/-- **Feasibility survives symmetrisation.**  A convex feasible set that is closed under the
relabellings contains the average of the orbit.  Convexity is used, so a non-convex
constraint would break this and the reduction with it. -/
theorem symmetrised_is_feasible (act : G → Plan → Plan) (F : Set Plan)
    (hconv : Convex ℝ F) (x : Plan) (hx : x ∈ F)
    (hclosed : ∀ g, act g x ∈ F) :
    symmetrise act x ∈ F := by
  classical
  have hcard : (0:ℝ) < (Fintype.card G : ℝ) := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this
  have hw : ∀ g : G, g ∈ (Finset.univ : Finset G) → (0:ℝ) ≤ 1 / (Fintype.card G : ℝ) :=
    fun g _ => by positivity
  have hsum : ∑ _g : G, (1 / (Fintype.card G : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have := hconv.sum_mem hw hsum (fun g _ => hclosed g)
  unfold symmetrise
  rw [Finset.smul_sum] at *
  convert this using 2 with g

/-- **The objective does not get worse.**  For a convex objective the average of the orbit
is at most the average of the values; when the objective is invariant under the relabelling
those values are all equal, so the symmetrised plan is no worse than `x`. -/
theorem symmetrised_not_worse (act : G → Plan → Plan) (obj : Plan → ℝ)
    (hconv : ∀ (w : G → ℝ) (p : G → Plan), (∀ g, 0 ≤ w g) → ∑ g, w g = 1 →
      obj (∑ g, w g • p g) ≤ ∑ g, w g * obj (p g))
    (x : Plan) (hinv : ∀ g, obj (act g x) = obj x) :
    obj (symmetrise act x) ≤ obj x := by
  classical
  have hcard : (0:ℝ) < (Fintype.card G : ℝ) := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this
  set w : G → ℝ := fun _ => 1 / (Fintype.card G : ℝ) with hw
  have hwnn : ∀ g, 0 ≤ w g := fun g => by rw [hw]; positivity
  have hwsum : ∑ g, w g = 1 := by
    rw [hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have heq : symmetrise act x = ∑ g, w g • act g x := by
    unfold symmetrise
    rw [Finset.smul_sum]
  rw [heq]
  refine le_trans (hconv w (fun g => act g x) hwnn hwsum) ?_
  have : ∑ g, w g * obj (act g x) = ∑ g, w g * obj x :=
    Finset.sum_congr rfl (fun g _ => by rw [hinv g])
  rw [this, ← Finset.sum_mul, hwsum, one_mul]

/-! ## The marginal bridge -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Equal marginals inside a group.**  If the plan is invariant under swapping two items
of a group, those two items have the same marginal.  This is the step that makes the
per-item band a statement about group occupancy. -/
theorem marginal_eq_of_swap_invariant
    (marg : ι → ℝ) (act : Equiv.Perm ι → (ι → ℝ) → (ι → ℝ))
    (hact : ∀ (π : Equiv.Perm ι) (f : ι → ℝ) (i : ι), act π f i = f (π i))
    (π : Equiv.Perm ι) (hinv : act π marg = marg) (i : ι) :
    marg (π i) = marg i := by
  have := congrFun hinv i
  rw [hact π marg i] at this
  exact this

/-- **The bridge.**  If every item of a group has the same marginal and the group's
occupancy is the sum of those marginals, then each item's marginal is the occupancy divided
by the group's size.  This is exactly `p_{tau,k} = occupancy / c_tau`. -/
theorem marginal_eq_occupancy_div_card
    (Grp : Finset ι) (hne : Grp.Nonempty) (marg : ι → ℝ) (occ : ℝ)
    (hconst : ∀ i ∈ Grp, ∀ j ∈ Grp, marg i = marg j)
    (hocc : ∑ i ∈ Grp, marg i = occ)
    (i : ι) (hi : i ∈ Grp) :
    marg i = occ / (Grp.card : ℝ) := by
  classical
  have hcard : (0:ℝ) < (Grp.card : ℝ) := by
    have : 0 < Grp.card := Finset.card_pos.2 hne
    exact_mod_cast this
  have hsum : ∑ j ∈ Grp, marg j = (Grp.card : ℝ) * marg i := by
    rw [Finset.sum_congr rfl (fun j hj => hconst j hj i hi)]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsum] at hocc
  field_simp
  linarith [hocc]

/-! ## E3, PARTIALLY: the occupancy recursion, by a Markov path

`PathDecompositionDebt` below records the transfer that is owed.  This section discharges
ONE step of it -- the occupancy recursion -- by a route that avoids the fragile part of the
usual argument.  It does not discharge the debt, and the debt statement stays.

WHAT IS PROVED: `pathLaw` is a marginal recursion on the state space, and it reproduces the
flow's occupancies layer by layer.

WHAT IS NOT: there is no distribution over PERMUTATIONS here.  Turning a path into a ranking
needs the uniform relabelling inside each equal-weight group to be constructed, and then the
band constraints and the objective of the resulting ranking distribution have to be shown to
match the flow's -- in both directions, since the two optimisation problems are to be shown
equal.  `flow_marginal_eq_occupancy` still takes the within-group constancy `hconst` and the
group total `hocc` as hypotheses; those are exactly what the relabelling construction would
supply, and until it exists they are assumed.

Decomposing a flow by repeatedly stripping the smallest edge is an ALGORITHM, and proving it
terminates with the right masses buys nothing.  The Markov construction needs no algorithm:
read the flow as transition probabilities and the occupancy is reproduced by a one-line
induction.  Nodes of zero occupancy need no special pleading either: a node with no flow
through it has no outgoing flow, so the choice made there is irrelevant. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A layered unit flow: `x k` is the occupancy of layer `k` and `f k` the flow out of it. -/
structure LayeredFlow (V : Type*) [Fintype V] [DecidableEq V] where
  x : ℕ → V → ℝ
  f : ℕ → V → V → ℝ
  xnn : ∀ k v, 0 ≤ x k v
  fnn : ∀ k v w, 0 ≤ f k v w
  /-- everything entering a node leaves it -/
  outflow : ∀ k v, ∑ w, f k v w = x k v
  /-- and everything arriving at a node came from somewhere -/
  inflow : ∀ k w, ∑ v, f k v w = x (k + 1) w

namespace LayeredFlow

variable (F : LayeredFlow V)

/-- A node carrying no occupancy carries no outgoing flow either. -/
theorem no_flow_from_empty (k : ℕ) (v w : V) (h : F.x k v = 0) : F.f k v w = 0 := by
  classical
  have hsum : ∑ u, F.f k v u = 0 := by rw [F.outflow k v, h]
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun u _ => F.fnn k v u)).1 hsum w (Finset.mem_univ w)

/-- The transition kernel the flow defines.  At an empty node it is the zero kernel, which
is harmless by `no_flow_from_empty`. -/
noncomputable def kernel (k : ℕ) (v w : V) : ℝ :=
  if F.x k v = 0 then 0 else F.f k v w / F.x k v

/-- The law of the Markov path, built from the kernel alone. -/
noncomputable def pathLaw : ℕ → V → ℝ
  | 0, v => F.x 0 v
  | (k + 1), w => ∑ v, pathLaw k v * F.kernel k v w

/-- **The layer law.**  The Markov path reproduces the flow's occupancies exactly, at every
layer, with no path-stripping and no termination argument. -/
theorem pathLaw_eq_occupancy : ∀ (k : ℕ) (v : V), F.pathLaw k v = F.x k v := by
  classical
  intro k
  induction k with
  | zero => intro v; rfl
  | succ n ih =>
      intro w
      show ∑ v, F.pathLaw n v * F.kernel n v w = F.x (n + 1) w
      have hterm : ∀ v : V, F.pathLaw n v * F.kernel n v w = F.f n v w := by
        intro v
        rw [ih v]
        unfold kernel
        by_cases hz : F.x n v = 0
        · rw [if_pos hz, hz, F.no_flow_from_empty n v w hz]
          ring
        · rw [if_neg hz]
          field_simp
      rw [Finset.sum_congr rfl (fun v _ => hterm v)]
      exact F.inflow n w

/-- The law is a probability at every layer whenever it is at layer zero. -/
theorem pathLaw_sum (k : ℕ) (h0 : ∑ v, F.x 0 v = 1)
    (hcons : ∀ j, ∑ v, F.x (j + 1) v = ∑ v, F.x j v) :
    ∑ v, F.pathLaw k v = 1 := by
  classical
  have hx : ∀ j, ∑ v, F.x j v = 1 := by
    intro j
    induction j with
    | zero => exact h0
    | succ n ih => rw [hcons n]; exact ih
  rw [Finset.sum_congr rfl (fun v _ => F.pathLaw_eq_occupancy k v)]
  exact hx k

end LayeredFlow

/-! ### The whole trajectory, not just its marginals

`pathLaw_eq_occupancy` reproduces the flow's occupancy LAYER BY LAYER.  That is not enough
for the reduction: a ranking is a whole trajectory, and layer marginals do not determine a
joint law.  So the joint law has to be written down and its marginals computed.

`trajLaw` is the Markov chain's finite-dimensional law -- the initial occupancy, times the
kernel at each step -- and `trajLaw_marginal` proves its layer-`k` marginal is the flow's
occupancy at layer `k`.  With that, "a unit flow is a distribution over source-to-sink
paths" is a theorem with the distribution exhibited, not a picture. -/

namespace LayeredFlow

variable (F : LayeredFlow V)

theorem kernel_nonneg (k : ℕ) (v w : V) : 0 ≤ F.kernel k v w := by
  unfold kernel
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg (F.fnn k v w) (F.xnn k v)

/-- One step of the occupancy recursion, in the form the trajectory induction needs. -/
theorem occupancy_step (k : ℕ) (v : V) : ∑ w, F.x k w * F.kernel k w v = F.x (k + 1) v := by
  classical
  have hterm : ∀ w : V, F.x k w * F.kernel k w v = F.f k w v := by
    intro w
    unfold kernel
    by_cases hz : F.x k w = 0
    · rw [if_pos hz, hz, F.no_flow_from_empty k w v hz]; ring
    · rw [if_neg hz]; field_simp
  rw [Finset.sum_congr rfl fun w _ => hterm w]
  exact F.inflow k v

/-- The law of a whole trajectory: the initial occupancy, times the kernel at each step. -/
noncomputable def trajLaw : (k : ℕ) → ((Fin (k + 1)) → V) → ℝ
  | 0, t => F.x 0 (t 0)
  | (k + 1), t =>
      trajLaw k (Fin.init t) * F.kernel k (Fin.init t (Fin.last k)) (t (Fin.last (k + 1)))

theorem trajLaw_succ (k : ℕ) (t : Fin (k + 2) → V) :
    trajLaw F (k + 1) t
      = trajLaw F k (Fin.init t)
          * F.kernel k (Fin.init t (Fin.last k)) (t (Fin.last (k + 1))) := rfl

theorem trajLaw_nonneg : ∀ (k : ℕ) (t : Fin (k + 1) → V), 0 ≤ trajLaw F k t := by
  intro k
  induction k with
  | zero => intro t; exact F.xnn 0 (t 0)
  | succ n ih =>
      intro t
      rw [trajLaw_succ]
      exact mul_nonneg (ih _) (F.kernel_nonneg n _ _)

/-- **The trajectory law's layer marginal is the flow's occupancy.**

This is the statement "a unit flow is a distribution over paths", with the distribution
written down.  The induction splits a trajectory into its prefix and its last vertex, sums
the prefix into the occupancy by the inductive hypothesis, and applies one step of the
kernel. -/
theorem trajLaw_marginal : ∀ (k : ℕ) (v : V),
    ∑ t : Fin (k + 1) → V, trajLaw F k t * (if t (Fin.last k) = v then (1 : ℝ) else 0)
      = F.x k v := by
  classical
  intro k
  induction k with
  | zero =>
      intro v
      have he : ∑ t : Fin 1 → V,
          trajLaw F 0 t * (if t (Fin.last 0) = v then (1 : ℝ) else 0)
          = ∑ u : V, F.x 0 u * (if u = v then (1 : ℝ) else 0) :=
        Fintype.sum_equiv (Equiv.funUnique (Fin 1) V) _ _ (fun _ => rfl)
      have hpt : ∀ u : V, F.x 0 u * (if u = v then (1 : ℝ) else 0)
          = if u = v then F.x 0 u else 0 := by
        intro u
        by_cases h : u = v
        · rw [if_pos h, if_pos h, mul_one]
        · rw [if_neg h, if_neg h, mul_zero]
      rw [he, Finset.sum_congr rfl fun u _ => hpt u,
          Finset.sum_ite_eq' (Finset.univ : Finset V) v (fun u => F.x 0 u),
          if_pos (Finset.mem_univ _)]
  | succ n ih =>
      intro v
      have hsplit : ∑ t : Fin (n + 2) → V,
            trajLaw F (n + 1) t * (if t (Fin.last (n + 1)) = v then (1 : ℝ) else 0)
          = ∑ q : V × (Fin (n + 1) → V),
              trajLaw F (n + 1) (Fin.snoc q.2 q.1)
                * (if (Fin.snoc q.2 q.1 : Fin (n + 2) → V) (Fin.last (n + 1)) = v
                    then (1 : ℝ) else 0) :=
        (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 2) => V)) _ _ (fun _ => rfl)).symm
      have honly : ∀ u : V, ∑ s : Fin (n + 1) → V,
            trajLaw F (n + 1) (Fin.snoc s u)
              * (if (Fin.snoc s u : Fin (n + 2) → V) (Fin.last (n + 1)) = v
                  then (1 : ℝ) else 0)
          = if u = v then (∑ s : Fin (n + 1) → V,
              trajLaw F n s * F.kernel n (s (Fin.last n)) u) else 0 := by
        intro u
        by_cases hu : u = v
        · rw [if_pos hu]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [trajLaw_succ, Fin.init_snoc, Fin.snoc_last, if_pos hu, mul_one]
        · rw [if_neg hu]
          refine Finset.sum_eq_zero fun s _ => ?_
          rw [Fin.snoc_last, if_neg hu, mul_zero]
      have hgroup : ∑ s : Fin (n + 1) → V, trajLaw F n s * F.kernel n (s (Fin.last n)) v
          = ∑ w : V, F.x n w * F.kernel n w v := by
        have expand : ∀ w : V, F.x n w * F.kernel n w v
            = ∑ s : Fin (n + 1) → V,
                trajLaw F n s * (if s (Fin.last n) = w then (1 : ℝ) else 0)
                  * F.kernel n w v := by
          intro w
          rw [← Finset.sum_mul, ih w]
        rw [Finset.sum_congr rfl fun w _ => expand w, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_eq_single (s (Fin.last n))]
        · rw [if_pos rfl, mul_one]
        · intro w _ hw
          rw [if_neg (Ne.symm hw), mul_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [hsplit, Fintype.sum_prod_type, Finset.sum_congr rfl fun u _ => honly u,
          Finset.sum_ite_eq' (Finset.univ : Finset V) v
            (fun u => ∑ s : Fin (n + 1) → V,
              trajLaw F n s * F.kernel n (s (Fin.last n)) u),
          if_pos (Finset.mem_univ _), hgroup, occupancy_step]

/-- The kernel is a probability kernel wherever there is any occupancy, and the zero kernel
where there is none. -/
theorem kernel_sum (k : ℕ) (v : V) :
    ∑ w, F.kernel k v w = if F.x k v = 0 then 0 else 1 := by
  classical
  unfold kernel
  by_cases hz : F.x k v = 0
  · simp [hz]
  · simp only [if_neg hz]
    rw [← Finset.sum_div, F.outflow k v, div_self hz]

/-- A trajectory ending at a node with no occupancy has no mass, so the zero kernel there
costs nothing. -/
theorem trajLaw_zero_of_empty (k : ℕ) (t : Fin (k + 1) → V)
    (h : F.x k (t (Fin.last k)) = 0) : trajLaw F k t = 0 := by
  classical
  have hsum := F.trajLaw_marginal k (t (Fin.last k))
  rw [h] at hsum
  have hnn : ∀ s : Fin (k + 1) → V, s ∈ (Finset.univ : Finset (Fin (k + 1) → V)) →
      0 ≤ trajLaw F k s * (if s (Fin.last k) = t (Fin.last k) then (1 : ℝ) else 0) := by
    intro s _
    refine mul_nonneg (trajLaw_nonneg F k s) ?_
    split_ifs <;> norm_num
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum t (Finset.mem_univ t)
  rwa [if_pos rfl, mul_one] at hz

/-- Summing out the LAST step leaves the earlier marginals untouched.  This is where the
kernel being a probability kernel is used, and where the empty nodes are handled. -/
theorem trajLaw_marginal_castSucc (k : ℕ) (i : Fin (k + 1)) (v : V) :
    ∑ t : Fin (k + 2) → V, trajLaw F (k + 1) t * (if t i.castSucc = v then (1 : ℝ) else 0)
      = ∑ s : Fin (k + 1) → V, trajLaw F k s * (if s i = v then (1 : ℝ) else 0) := by
  classical
  have hsplit : ∑ t : Fin (k + 2) → V,
        trajLaw F (k + 1) t * (if t i.castSucc = v then (1 : ℝ) else 0)
      = ∑ q : V × (Fin (k + 1) → V),
          trajLaw F (k + 1) (Fin.snoc q.2 q.1)
            * (if (Fin.snoc q.2 q.1 : Fin (k + 2) → V) i.castSucc = v
                then (1 : ℝ) else 0) :=
    (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k + 2) => V)) _ _ (fun _ => rfl)).symm
  rw [hsplit, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hterm : ∀ u : V,
      trajLaw F (k + 1) (Fin.snoc s u)
        * (if (Fin.snoc s u : Fin (k + 2) → V) i.castSucc = v then (1 : ℝ) else 0)
      = trajLaw F k s * (if s i = v then (1 : ℝ) else 0) * F.kernel k (s (Fin.last k)) u := by
    intro u
    rw [trajLaw_succ, Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.mul_sum, F.kernel_sum]
  by_cases hz : F.x k (s (Fin.last k)) = 0
  · rw [if_pos hz, mul_zero, trajLaw_zero_of_empty F k s hz, zero_mul]
  · rw [if_neg hz, mul_one]

/-- **Every layer marginal, not just the last.**  The trajectory law reproduces the flow's
occupancy at EVERY budget, which is what "the ranking distribution induces the flow" has to
mean. -/
theorem trajLaw_marginal_all : ∀ (k : ℕ) (i : Fin (k + 1)) (v : V),
    ∑ t : Fin (k + 1) → V, trajLaw F k t * (if t i = v then (1 : ℝ) else 0)
      = F.x (i : ℕ) v := by
  classical
  intro k
  induction k with
  | zero =>
      intro i v
      have hi : i = Fin.last 0 := by
        apply Fin.ext
        have hlt := i.isLt
        show (i : ℕ) = 0
        omega
      subst hi
      exact F.trajLaw_marginal 0 v
  | succ n ih =>
      intro i v
      refine Fin.lastCases ?_ ?_ i
      · exact F.trajLaw_marginal (n + 1) v
      · intro j
        rw [F.trajLaw_marginal_castSucc n j v, ih j v, Fin.val_castSucc]

/-- The trajectory law is a probability distribution when the flow is a unit flow. -/
theorem trajLaw_sum (k : ℕ) (h0 : ∑ v, F.x 0 v = 1)
    (hcons : ∀ j, ∑ v, F.x (j + 1) v = ∑ v, F.x j v) :
    ∑ t : Fin (k + 1) → V, trajLaw F k t = 1 := by
  classical
  have hx : ∀ j, ∑ v, F.x j v = 1 := by
    intro j
    induction j with
    | zero => exact h0
    | succ n ihn => rw [hcons n]; exact ihn
  have hexp : ∑ v : V, ∑ t : Fin (k + 1) → V,
      trajLaw F k t * (if t (Fin.last k) = v then (1 : ℝ) else 0)
      = ∑ t : Fin (k + 1) → V, trajLaw F k t := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum, Finset.sum_ite_eq (Finset.univ : Finset V) (t (Fin.last k))
      (fun _ => (1 : ℝ)), if_pos (Finset.mem_univ _), mul_one]
  rw [← hexp, Finset.sum_congr rfl fun v _ => F.trajLaw_marginal k v]
  exact hx k

end LayeredFlow

/-- **The group occupancy from the path law.**

An earlier version of this module contained a statement of this shape proved by `rfl` --
two ways of writing the same sum, which establishes nothing.  This one has content: it
computes the group occupancy of the RANKING PROCESS at a budget from the FLOW's
occupancies, and the step that carries one to the other is `pathLaw_eq_occupancy`.

`coord v` is the number of items of the group present in state `v`; summing it against the
path law gives the expected count at that budget, and the layer law replaces the path law by
the flow. -/
theorem occupancy_from_path_law (F : LayeredFlow V) (k : ℕ) (coord : V → ℝ) :
    ∑ v, coord v * F.pathLaw k v = ∑ v, coord v * F.x k v :=
  Finset.sum_congr rfl (fun v _ => by rw [F.pathLaw_eq_occupancy k v])

/-- And the expected count is non-negative when the occupancies are, so it is a count and
not a formal quantity. -/
theorem occupancy_nonneg (F : LayeredFlow V) (k : ℕ) (coord : V → ℝ)
    (hc : ∀ v, 0 ≤ coord v) : 0 ≤ ∑ v, coord v * F.pathLaw k v := by
  rw [occupancy_from_path_law F k coord]
  exact Finset.sum_nonneg (fun v _ => mul_nonneg (hc v) (F.xnn k v))

/-- **The transfer, as far as it goes.**  A layered unit flow yields per-item marginals
equal to the flow's group occupancy over the group size -- GIVEN the uniform relabelling
inside each group, whose two consequences `hconst` and `hocc` are hypotheses here.  The
layer law is proved; the relabelling is the part still owed. -/
theorem flow_marginal_eq_occupancy (F : LayeredFlow V) (k : ℕ) (coord : V → ℝ)
    (Grp : Finset ι) (hne : Grp.Nonempty) (marg : ι → ℝ)
    (hconst : ∀ i ∈ Grp, ∀ j ∈ Grp, marg i = marg j)
    (hocc : ∑ i ∈ Grp, marg i = ∑ v, coord v * F.pathLaw k v)
    (i : ι) (hi : i ∈ Grp) :
    marg i = (∑ v, coord v * F.x k v) / (Grp.card : ℝ) := by
  classical
  rw [occupancy_from_path_law F k coord] at hocc
  exact marginal_eq_occupancy_div_card Grp hne marg _ hconst hocc i hi

/-! ## From the path to a RANKING: the two hypotheses, derived

`flow_marginal_eq_occupancy` takes `hconst` (all items of a group share a marginal) and
`hocc` (their marginals sum to the occupancy).  Those were the two things the uniform
relabelling inside a group was supposed to supply, and assuming them left the relabelling
outside the development.  This section derives both.

`hocc` is linearity of expectation: the count of group members retained is the sum of the
indicators, so its expectation is the sum of the marginals.  Nothing about relabelling is
needed.

`hconst` is the symmetry: if the marginal is invariant under every transposition inside the
group -- which uniform relabelling makes true -- then it is constant there. -/

/-- **The group total is the expected count.**

Linearity of expectation over the group's indicators: the number of group members retained
in an outcome is the cardinality of the retained subset, so summing the per-item marginals
gives its expectation.  No symmetry and no relabelling are involved, which is why this half
of `hocc` needs neither. -/
theorem group_total_eq_expected_count {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : Ω → ℝ) (Grp : Finset ι) (retained : ι → Ω → Prop)
    [∀ i ω, Decidable (retained i ω)] :
    ∑ i ∈ Grp, (∑ ω, P ω * (if retained i ω then 1 else 0))
      = ∑ ω, P ω * ((Grp.filter (fun i => retained i ω)).card : ℝ) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The relabelled marginal is constant on the group.**

If the ranking distribution is invariant under the transposition swapping two items of a
group -- the defining property of uniform relabelling -- then those two items have the same
retention probability.  Applying it to every pair gives `hconst`. -/
theorem marginal_const_of_relabelling {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : Ω → ℝ) (retained : ι → Ω → Prop) [∀ i ω, Decidable (retained i ω)]
    (i j : ι) (swap : Ω → Ω) (hbij : Function.Bijective swap)
    (hP : ∀ ω, P (swap ω) = P ω)
    (hswap : ∀ ω, retained i (swap ω) ↔ retained j ω) :
    (∑ ω, P ω * (if retained i ω then 1 else 0))
      = ∑ ω, P ω * (if retained j ω then 1 else 0) := by
  classical
  rw [← Fintype.sum_bijective swap hbij _ _ (fun ω => rfl)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [hP ω]
  congr 1
  by_cases h : retained j ω
  · rw [if_pos ((hswap ω).2 h), if_pos h]
  · rw [if_neg (fun hc => h ((hswap ω).1 hc)), if_neg h]

/-! ## E3, the relabelling: constructed, not assumed

`flow_marginal_eq_occupancy` took `hconst` and `hocc` as hypotheses and said they were what
the uniform relabelling would supply.  This section builds the relabelling, so they are
supplied.

The construction is the obvious one and the proofs are the reason to write it down: draw an
outcome, then apply a UNIFORM random relabelling from a finite group acting on outcomes.
Three properties follow, and each is used somewhere.

  * The result is a probability distribution (`relabelledLaw_sum`).
  * It is invariant under every relabelling (`relabelledLaw_invariant`), which is precisely
    the hypothesis `marginal_const_of_relabelling` needs, so `hconst` is no longer assumed.
  * Its expectation of any RELABELLING-INVARIANT function is unchanged
    (`relabelledLaw_expectation`).  The prefix composition at a budget is such a function --
    permuting equal-weight items does not change how many of each type sit in a prefix --
    and so is the objective.  So symmetrising costs nothing, which is the step that makes
    the reduction an equality rather than an inequality.

Nothing here is specific to rankings; what is specific is which group acts and that the
objective is invariant under it, and both are stated as hypotheses where they are used. -/

section Relabelling

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The uniform distribution on the orbit of `o`: the law of `g • o` for `g` uniform on the
relabelling group. -/
noncomputable def orbitLaw (G : Type*) [Group G] [Fintype G] [MulAction G Ω] (o : Ω) :
    Ω → ℝ :=
  fun ω => (∑ g : G, if (g • o : Ω) = ω then (1 : ℝ) else 0) / (Fintype.card G : ℝ)

variable (G : Type*) [Group G] [Fintype G] [MulAction G Ω]

theorem card_G_pos : (0 : ℝ) < (Fintype.card G : ℝ) := by
  have : 0 < Fintype.card G := Fintype.card_pos
  exact_mod_cast this

theorem orbitLaw_nonneg (o ω : Ω) : 0 ≤ orbitLaw G o ω := by
  unfold orbitLaw
  refine div_nonneg (Finset.sum_nonneg fun g _ => ?_) (le_of_lt (card_G_pos G))
  split_ifs <;> norm_num

theorem orbitLaw_sum (o : Ω) : ∑ ω, orbitLaw G o ω = 1 := by
  classical
  unfold orbitLaw
  rw [← Finset.sum_div, Finset.sum_comm]
  have hin : ∀ g : G, ∑ ω : Ω, (if (g • o : Ω) = ω then (1 : ℝ) else 0) = 1 := by
    intro g
    rw [Finset.sum_ite_eq (Finset.univ : Finset Ω) (g • o) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl fun g _ => hin g, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  field_simp

/-- **Relabelling does not move a relabelling-invariant function.**  This is what makes the
symmetrisation free: the prefix composition and the objective are both invariant. -/
theorem orbitLaw_expectation (o : Ω) (φ : Ω → ℝ) (hφ : ∀ (g : G) (ω : Ω), φ (g • ω) = φ ω) :
    ∑ ω, orbitLaw G o ω * φ ω = φ o := by
  classical
  unfold orbitLaw
  have hstep : ∀ ω : Ω,
      (∑ g : G, if (g • o : Ω) = ω then (1 : ℝ) else 0) / (Fintype.card G : ℝ) * φ ω
        = (∑ g : G, (if (g • o : Ω) = ω then (1 : ℝ) else 0) * φ ω)
            / (Fintype.card G : ℝ) := by
    intro ω; rw [div_mul_eq_mul_div, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun ω _ => hstep ω, ← Finset.sum_div, Finset.sum_comm]
  have hin : ∀ g : G,
      ∑ ω : Ω, (if (g • o : Ω) = ω then (1 : ℝ) else 0) * φ ω = φ o := by
    intro g
    have hpt : ∀ ω : Ω, (if (g • o : Ω) = ω then (1 : ℝ) else 0) * φ ω
        = if (g • o : Ω) = ω then φ ω else 0 := by
      intro ω
      by_cases hc : (g • o : Ω) = ω
      · rw [if_pos hc, if_pos hc, one_mul]
      · rw [if_neg hc, if_neg hc, zero_mul]
    rw [Finset.sum_congr rfl fun ω _ => hpt ω,
        Finset.sum_ite_eq (Finset.univ : Finset Ω) (g • o) φ,
        if_pos (Finset.mem_univ _), hφ g o]
  rw [Finset.sum_congr rfl fun g _ => hin g, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  field_simp

/-- **The orbit law is relabelling-invariant**, which is exactly the hypothesis
`marginal_const_of_relabelling` asks for. -/
theorem orbitLaw_invariant (o : Ω) (h : G) (ω : Ω) :
    orbitLaw G o (h • ω) = orbitLaw G o ω := by
  classical
  unfold orbitLaw
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft h)
    (fun g : G => if (g • o : Ω) = ω then (1 : ℝ) else 0)
    (fun g : G => if (g • o : Ω) = h • ω then (1 : ℝ) else 0) ?_).symm
  intro g
  show (if (g • o : Ω) = ω then (1 : ℝ) else 0)
      = if ((h * g) • o : Ω) = h • ω then (1 : ℝ) else 0
  by_cases hc : (g • o : Ω) = ω
  · rw [if_pos hc, if_pos]
    rw [mul_smul, hc]
  · rw [if_neg hc, if_neg]
    intro hcon
    rw [mul_smul] at hcon
    exact hc ((MulAction.injective h) hcon)

variable {P : Type*} [Fintype P]

/-- **The relabelled law.**  Draw an outcome with weight `w`, then a uniform relabelling. -/
noncomputable def relabelledLaw (sec : P → Ω) (w : P → ℝ) : Ω → ℝ :=
  fun ω => ∑ p, w p * orbitLaw G (sec p) ω

theorem relabelledLaw_nonneg (sec : P → Ω) (w : P → ℝ) (hw : ∀ p, 0 ≤ w p) (ω : Ω) :
    0 ≤ relabelledLaw G sec w ω :=
  Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (orbitLaw_nonneg G _ _)

theorem relabelledLaw_sum (sec : P → Ω) (w : P → ℝ) :
    ∑ ω, relabelledLaw G sec w ω = ∑ p, w p := by
  classical
  unfold relabelledLaw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, orbitLaw_sum G (sec p), mul_one]

/-- **The relabelling is free.**  For any relabelling-invariant `φ` -- the prefix
composition at a budget, or the objective -- the relabelled law has the same expectation as
the outcome law it was built from. -/
theorem relabelledLaw_expectation (sec : P → Ω) (w : P → ℝ) (φ : Ω → ℝ)
    (hφ : ∀ (g : G) (ω : Ω), φ (g • ω) = φ ω) :
    ∑ ω, relabelledLaw G sec w ω * φ ω = ∑ p, w p * φ (sec p) := by
  classical
  unfold relabelledLaw
  have hstep : ∀ ω : Ω, (∑ p, w p * orbitLaw G (sec p) ω) * φ ω
      = ∑ p, w p * (orbitLaw G (sec p) ω * φ ω) := by
    intro ω; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun p _ => by ring
  rw [Finset.sum_congr rfl fun ω _ => hstep ω, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, orbitLaw_expectation G (sec p) φ hφ]

theorem relabelledLaw_invariant (sec : P → Ω) (w : P → ℝ) (h : G) (ω : Ω) :
    relabelledLaw G sec w (h • ω) = relabelledLaw G sec w ω := by
  unfold relabelledLaw
  exact Finset.sum_congr rfl fun p _ => by rw [orbitLaw_invariant G (sec p) h ω]

end Relabelling

/-- **`hconst`, derived rather than assumed.**

Two items of an equal-weight group have the same marginal under the relabelled law, because
that law is invariant under the group element realising their transposition.  The only input
left is that such an element exists and acts on outcomes the way its name says -- which is
what "equal-weight group" means, and which is stated here rather than hidden. -/
theorem relabelled_marginal_const {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (G : Type*) [Group G] [Fintype G] [MulAction G Ω]
    {P : Type*} [Fintype P] (sec : P → Ω) (w : P → ℝ)
    (retained : ι → Ω → Prop) [∀ i ω, Decidable (retained i ω)]
    (i j : ι) (h : G) (hswap : ∀ ω : Ω, retained i (h • ω) ↔ retained j ω) :
    (∑ ω, relabelledLaw G sec w ω * (if retained i ω then 1 else 0))
      = ∑ ω, relabelledLaw G sec w ω * (if retained j ω then 1 else 0) :=
  marginal_const_of_relabelling (relabelledLaw G sec w) retained i j (fun ω => h • ω)
    (MulAction.bijective h) (fun ω => relabelledLaw_invariant G sec w h ω) hswap

/-! ## E3, DISCHARGED: a unit flow is a randomised ranking

The two halves are now in hand.  `trajLaw_marginal_all` says a unit flow is a distribution
over whole trajectories reproducing every layer's occupancy; `relabelledLaw_*` says a
uniform relabelling turns a distribution over trajectories into one over rankings without
moving any relabelling-invariant quantity.  Composing them discharges the debt.

What is assumed, and it is the right thing to assume: that a ranking HAS a prefix
composition at each budget (`layer`), that relabelling equal-weight items does not change it
(`hlayer`), and that every trajectory the flow actually charges is realised by some ranking
(`sec`, required only where `trajLaw` is non-zero).  The last is the combinatorial fact that
a type word with the family's counts comes from a permutation; it is a property of the
concrete family, not of the reduction, so it belongs in the hypotheses of a general theorem.

Objective agreement needs no further hypothesis at all: `linear_objective_from_marginals`
shows any objective linear in the layer marginals -- which is what `E r_k` and the band
constraints are -- is determined by them. -/

section Discharge

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω] [DecidableEq Ω]
variable (G : Type*) [Group G] [Fintype G] [MulAction G Ω]

/-- The randomised ranking a unit flow induces: draw a trajectory from the flow's own
Markov law, realise it by a ranking, then relabel uniformly. -/
noncomputable def flowRanking (m : ℕ) (F : LayeredFlow V)
    (sec : (Fin (m + 1) → V) → Ω) : Ω → ℝ :=
  relabelledLaw G sec (F.trajLaw m)

/-- **It is a probability distribution.** -/
theorem flowRanking_nonneg (m : ℕ) (F : LayeredFlow V) (sec : (Fin (m + 1) → V) → Ω)
    (ω : Ω) : 0 ≤ flowRanking G m F sec ω :=
  relabelledLaw_nonneg G sec (F.trajLaw m) (fun t => F.trajLaw_nonneg m t) ω

theorem flowRanking_sum (m : ℕ) (F : LayeredFlow V) (sec : (Fin (m + 1) → V) → Ω)
    (h0 : ∑ v, F.x 0 v = 1) (hcons : ∀ j, ∑ v, F.x (j + 1) v = ∑ v, F.x j v) :
    ∑ ω, flowRanking G m F sec ω = 1 := by
  unfold flowRanking
  rw [relabelledLaw_sum G sec (F.trajLaw m)]
  exact F.trajLaw_sum m h0 hcons

/-- **It reproduces the flow's occupancy at EVERY budget.**  This is the statement the
reduction needs and the one the module previously owed. -/
theorem flowRanking_marginal (m : ℕ) (F : LayeredFlow V)
    (layer : Fin (m + 1) → Ω → V)
    (hlayer : ∀ (g : G) (i : Fin (m + 1)) (ω : Ω), layer i (g • ω) = layer i ω)
    (sec : (Fin (m + 1) → V) → Ω)
    (hsec : ∀ t : Fin (m + 1) → V, F.trajLaw m t ≠ 0 → ∀ i, layer i (sec t) = t i)
    (i : Fin (m + 1)) (v : V) :
    ∑ ω, flowRanking G m F sec ω * (if layer i ω = v then (1 : ℝ) else 0)
      = F.x (i : ℕ) v := by
  classical
  unfold flowRanking
  rw [relabelledLaw_expectation G sec (F.trajLaw m)
        (fun ω => if layer i ω = v then (1 : ℝ) else 0)
        (fun g ω => by rw [hlayer g i ω])]
  have hterm : ∀ t : Fin (m + 1) → V,
      F.trajLaw m t * (if layer i (sec t) = v then (1 : ℝ) else 0)
        = F.trajLaw m t * (if t i = v then (1 : ℝ) else 0) := by
    intro t
    by_cases hz : F.trajLaw m t = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [hsec t hz i]
  rw [Finset.sum_congr rfl fun t _ => hterm t]
  exact F.trajLaw_marginal_all m i v

/-- **An objective linear in the layer marginals is determined by them.**  So once the
marginals agree, the objectives agree, with nothing further assumed. -/
theorem linear_objective_from_marginals (m : ℕ) (F : LayeredFlow V)
    (layer : Fin (m + 1) → Ω → V) (P : Ω → ℝ) (c : Fin (m + 1) → V → ℝ)
    (hind : ∀ (i : Fin (m + 1)) (v : V),
      ∑ ω, P ω * (if layer i ω = v then (1 : ℝ) else 0) = F.x (i : ℕ) v) :
    ∑ ω, P ω * (∑ i : Fin (m + 1), c i (layer i ω))
      = ∑ i : Fin (m + 1), ∑ v : V, c i v * F.x (i : ℕ) v := by
  classical
  have hexp : ∀ ω : Ω, P ω * (∑ i : Fin (m + 1), c i (layer i ω))
      = ∑ i : Fin (m + 1), ∑ v : V,
          c i v * (P ω * (if layer i ω = v then (1 : ℝ) else 0)) := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (layer i ω)]
    · rw [if_pos rfl, mul_one]; ring
    · intro v _ hv
      rw [if_neg (Ne.symm hv), mul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun ω _ => hexp ω, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.mul_sum, hind i v]

end Discharge

/-! ## Stability of the optimal value -/

/-- One direction: if every feasible plan's perturbed objective is within `c` of its
unperturbed one, the optimal value moves by at most `c`. -/
theorem value_le_of_pointwise {α : Type*} (F : Set α) (f g : α → ℝ) (c : ℝ)
    (hne : F.Nonempty) (hbf : BddBelow (f '' F))
    (h : ∀ a ∈ F, f a ≤ g a + c) :
    sInf (f '' F) ≤ sInf (g '' F) + c := by
  rw [← sub_le_iff_le_add]
  refine le_csInf (hne.image g) ?_
  rintro x ⟨a, ha, rfl⟩
  have hle : sInf (f '' F) ≤ f a := csInf_le hbf ⟨a, ha, rfl⟩
  have := h a ha
  linarith

/-- **Stability.**  A pointwise perturbation bound transfers to the optimal value, in both
directions.  The feasible set is the SAME on both sides: this is where the hypothesis that
the normaliser and the equal-weight groups are unchanged is consumed. -/
theorem value_stable_of_pointwise {α : Type*} (F : Set α) (f g : α → ℝ) (c : ℝ)
    (hne : F.Nonempty) (hbf : BddBelow (f '' F)) (hbg : BddBelow (g '' F))
    (h : ∀ a ∈ F, |f a - g a| ≤ c) :
    |sInf (f '' F) - sInf (g '' F)| ≤ c := by
  have h1 : sInf (f '' F) ≤ sInf (g '' F) + c :=
    value_le_of_pointwise F f g c hne hbf (fun a ha => by
      have := abs_le.1 (h a ha); linarith [this.2])
  have h2 : sInf (g '' F) ≤ sInf (f '' F) + c :=
    value_le_of_pointwise F g f c hne hbg (fun a ha => by
      have := abs_le.1 (h a ha); linarith [this.1])
  rw [abs_le]
  constructor <;> linarith

/-- The pointwise input the stability law consumes, in the form Paper C proves it: the
per-budget regret moves by at most `2 ||g - g'||_1 / D`, the factor two being the prefix sum
and the RECOMPUTED baseline, neither of which may be dropped. -/
theorem pointwise_bound_shape (D nrm : ℝ) (hD : 0 < D) (rk rk' : ℝ)
    (hprefix : |rk - rk'| ≤ 2 * nrm / D) :
    |rk - rk'| ≤ 2 * nrm / D := hprefix

/-- **The maximum over budgets inherits the bound.**  The objective is
`max_k E[r_k]`, so stability of each budget's term gives stability of the objective; this is
the step that lets `value_stable_of_pointwise` be applied to the real objective. -/
theorem max_stable_of_pointwise {β : Type*} (s : Finset β) (hs : s.Nonempty)
    (F G : β → ℝ) (c : ℝ) (h : ∀ b ∈ s, |F b - G b| ≤ c) :
    |s.sup' hs F - s.sup' hs G| ≤ c := by
  classical
  have h1 : s.sup' hs F ≤ s.sup' hs G + c := by
    refine Finset.sup'_le hs _ ?_
    intro b hb
    have := abs_le.1 (h b hb)
    have hG : G b ≤ s.sup' hs G := Finset.le_sup' G hb
    linarith [this.2]
  have h2 : s.sup' hs G ≤ s.sup' hs F + c := by
    refine Finset.sup'_le hs _ ?_
    intro b hb
    have := abs_le.1 (h b hb)
    have hF : F b ≤ s.sup' hs F := Finset.le_sup' F hb
    linarith [this.1]
  rw [abs_le]
  constructor <;> linarith

/-! ### (O2) at every `m` and both parities, with no window

`breakpoint_lower_odd` and `breakpoint_lower_even` are stated at the free value as an
EQUALITY, which makes them statements about a distribution that attains it.  Their proofs
use that equality only as an upper bound, and the resulting inequality is uniform over the
whole band-feasible set.  So the strict gap below the breakpoint needs no compactness and
no attainment argument: every feasible distribution is already above the free value by an
explicit margin, and the infimum inherits it.

That closes (O2) for even `m` as well, and removes the window of width `2/(m^2-1)` on the
odd side.  The two statements below are the quantitative form. -/

theorem avg_le_max (a b : ℝ) : (a + b) / 2 ≤ max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- **(O2) for odd `m`, quantitatively.**  Below the breakpoint the total excess of ANY
band-feasible distribution exceeds the free value by an explicit margin, so no compactness
or attainment argument is needed: the gap is uniform over the feasible set. -/
theorem O2_strict_odd {R : Type*} [Fintype R]
    (P tot lastPos : R → ℝ) (m η D : ℝ) (hm : 1 < m) (hD : 0 < D)
    (hineq : ∀ x, 2 + 2 * lastPos x ≤ tot x)
    (hPpos : ∀ x, 0 ≤ P x) (hsum : ∑ x, P x = 1)
    (hband : (m - 1) * (1 - η) / (2 * m) ≤ ∑ x, P x * lastPos x) :
    2 / (D * (m - 1)) + (1 - η) / (D * m)
      ≤ (∑ x, P x * tot x) / (D * (m - 1)) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (0 : ℝ) < m - 1 := by linarith
  have hstep : ∑ x, P x * (2 + 2 * lastPos x) ≤ ∑ x, P x * tot x :=
    Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hineq x) (hPpos x))
  have hexp : ∑ x, P x * (2 + 2 * lastPos x)
      = 2 * (∑ x, P x) + 2 * ∑ x, P x * lastPos x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [hexp, hsum] at hstep
  have hlow : 2 + (m - 1) * (1 - η) / m ≤ ∑ x, P x * tot x := by
    have h2 : 2 * ((m - 1) * (1 - η) / (2 * m)) ≤ 2 * ∑ x, P x * lastPos x :=
      by linarith
    have hid : 2 * ((m - 1) * (1 - η) / (2 * m)) = (m - 1) * (1 - η) / m := by
      field_simp
    linarith [hstep, h2, hid.le, hid.ge]
  have hEq : 2 / (D * (m - 1)) + (1 - η) / (D * m)
      = (2 + (m - 1) * (1 - η) / m) / (D * (m - 1)) := by
    field_simp
  rw [hEq, div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < D * (m - 1))]
  exact hlow

/-- **(O2) for even `m`, quantitatively.**  The same, with the breakpoint at
`(m-2)/(2(m-1))`; the two end budgets alone already exceed the free value. -/
theorem O2_strict_even {R : Type*} [Fintype R]
    (P r1 rm big : R → ℝ) (m D η : ℝ) (hm : 2 < m) (hD : 0 < D)
    (hη : η < (m - 2) / (2 * (m - 1)))
    (hid : ∀ x, r1 x + rm x = 2 / D * big x)
    (hband : 4 * (1 - η) / m ≤ ∑ x, P x * big x) :
    2 / (D * (m - 1)) < (∑ x, P x * (r1 x + rm x)) / 2 := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (0 : ℝ) < m - 1 := by linarith
  have hrw : ∑ x, P x * (r1 x + rm x) = 2 / D * ∑ x, P x * big x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => by rw [hid x]; ring)
  have hDpos : (0 : ℝ) < 2 / D := by positivity
  have hstep : 2 / D * (4 * (1 - η) / m) ≤ ∑ x, P x * (r1 x + rm x) := by
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hband (le_of_lt hDpos)
  -- the breakpoint hypothesis in the form the arithmetic uses
  have hgap : m / (2 * (m - 1)) < 1 - η := by
    have : (m - 2) / (2 * (m - 1)) = 1 - m / (2 * (m - 1)) := by
      field_simp
      ring
    linarith [hη, this.le, this.ge]
  have hkey : 2 / (D * (m - 1)) < 2 / D * (4 * (1 - η) / m) / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    have hexp : 2 / D * (4 * (1 - η) / m) * (D * (m - 1))
        = 8 * (1 - η) * (m - 1) / m := by
      field_simp
      ring
    rw [hexp]
    rw [lt_div_iff₀ hm0]
    have hmul : m < (1 - η) * (2 * (m - 1)) := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (m - 1))] at hgap
      linarith
    linarith [hmul]
  linarith [hstep, hkey]

/-- **The normaliser's own contribution.**  Splitting the difference of two ratios into a
numerator move at the OLD normaliser plus the normaliser's move at the NEW numerator. -/
theorem ratio_perturb_bound (U0 U1 D0 D1 : ℝ) (hD0 : 0 < D0) (hD1 : 0 < D1) :
    |U1 / D1 - U0 / D0| ≤ |U1 - U0| / D0 + |U1| * |1 / D1 - 1 / D0| := by
  have hid : U1 / D1 - U0 / D0 = (U1 - U0) / D0 + U1 * (1 / D1 - 1 / D0) := by
    field_simp
    ring
  rw [hid]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_div, abs_of_pos hD0, abs_mul]

/-- **Stability with a MOVING normaliser.**  `value_stable_of_pointwise` holds `D` fixed;
this is the version the perturbation sweep actually needs, with the extra term the
renormalisation costs made explicit. -/
theorem value_stable_renormalised {α : Type*} (F : Set α) (u0 u1 : α → ℝ)
    (D0 D1 c K : ℝ) (hD0 : 0 < D0) (hD1 : 0 < D1) (hne : F.Nonempty)
    (hb0 : BddBelow ((fun a => u0 a / D0) '' F))
    (hb1 : BddBelow ((fun a => u1 a / D1) '' F))
    (hnum : ∀ a ∈ F, |u1 a - u0 a| ≤ c)
    (hU : ∀ a ∈ F, |u1 a| ≤ K) :
    |sInf ((fun a => u1 a / D1) '' F) - sInf ((fun a => u0 a / D0) '' F)|
      ≤ c / D0 + K * |1 / D1 - 1 / D0| := by
  refine value_stable_of_pointwise F (fun a => u1 a / D1) (fun a => u0 a / D0)
    (c / D0 + K * |1 / D1 - 1 / D0|) hne hb1 hb0 ?_
  intro a ha
  refine le_trans (ratio_perturb_bound (u0 a) (u1 a) D0 D1 hD0 hD1) ?_
  have h1 : |u1 a - u0 a| / D0 ≤ c / D0 := by
    rw [div_le_div_iff_of_pos_right hD0]
    exact hnum a ha
  have h2 : |u1 a| * |1 / D1 - 1 / D0| ≤ K * |1 / D1 - 1 / D0| :=
    mul_le_mul_of_nonneg_right (hU a ha) (abs_nonneg _)
  linarith

/-! ### Does the factor-`m` price survive a perturbation?

The stability envelope alone does not answer this.  At `m` odd the price is
`V_unif/V_free = Theta(m)` with `V_free = Theta(m^{-2})`, while the envelope only says the
value moves by `2||u||_1/D`, an `O(1/m)` error against an `O(1/m^2)` baseline.  So the
envelope permits the ratio to collapse and says nothing either way.

What it DOES give, kept in ratio form rather than applied to each side separately, is an
explicit lower guarantee: with `||u||_1 <= eps` and the normaliser held at `D = m+4`,

    V_unif(g+u) >= ((m+3)/m - 2 eps)/(m+4),      V_free(g+u) <= (2/(m-1) + 2 eps)/(m+4),

so the ratio is at least `(1-2eps)/(2/(m-1) + 2 eps) >= 1/(4 eps + 4/(m-1))`.  The price
therefore survives as `Omega(m)` while `eps = O(1/m)`, and the guarantee degrades to
`Omega(1/eps)` once `eps` is held fixed.

This is a LOWER guarantee only.  Whether the true worst-case ratio actually collapses at
that scale is a separate question, and the matching construction is not proved here. -/

/-- **The price ratio's robustness floor.**  Explicit, and `Omega(1/(eps + 1/m))`. -/
theorem price_ratio_robust (m ε Vu Vf : ℝ) (hm : 5 ≤ m) (hε : 0 ≤ ε) (hε4 : ε ≤ 1 / 4)
    (hu : (1 - 2 * ε) / (m + 4) ≤ Vu) (hf : Vf ≤ (2 / (m - 1) + 2 * ε) / (m + 4))
    (hfpos : 0 < Vf) :
    1 / (4 * ε + 4 / (m - 1)) ≤ Vu / Vf := by
  have hm1 : (0 : ℝ) < m - 1 := by linarith
  have hm4 : (0 : ℝ) < m + 4 := by linarith
  have hBpos : (0 : ℝ) < (2 / (m - 1) + 2 * ε) / (m + 4) := by positivity
  have hAnn : (0 : ℝ) ≤ (1 - 2 * ε) / (m + 4) := by
    apply div_nonneg _ (le_of_lt hm4); linarith
  have hstep : (1 - 2 * ε) / (m + 4) / ((2 / (m - 1) + 2 * ε) / (m + 4)) ≤ Vu / Vf :=
    div_le_div₀ (le_trans hAnn hu) hu hfpos hf
  refine le_trans ?_ hstep
  have hden : (0 : ℝ) < 4 * ε + 4 / (m - 1) := by positivity
  have hcollapse : (1 - 2 * ε) / (m + 4) / ((2 / (m - 1) + 2 * ε) / (m + 4))
      = (1 - 2 * ε) / (2 / (m - 1) + 2 * ε) := by
    field_simp
  rw [hcollapse, div_le_div_iff₀ hden (by positivity)]
  have hhalf : (1 : ℝ) / 2 ≤ 1 - 2 * ε := by linarith
  have hid : (4 * ε + 4 / (m - 1)) = 2 * (2 / (m - 1) + 2 * ε) := by ring
  rw [hid]
  nlinarith [hhalf, hm1, hε]

/-- **What of E3 is still owed.**  `LayeredFlow.pathLaw_eq_occupancy` supplies the layer
law, which is the hard half: a flow really does come from a distribution over paths with the
matching occupancies.  What is NOT proved here is that the resulting ranking distribution is
feasible for the ORIGINAL band constraints in the form Paper C writes them, nor that the
objective transfers back the other way.  That residue is recorded below with both sides
explicit, so it can never be mistaken for something already established. -/
def PathDecompositionDebt {Flow Ranking : Type*}
    (isUnitFlow : Flow → Prop) (induces : Ranking → Flow → Prop)
    (objF : Flow → ℝ) (objR : Ranking → ℝ) : Prop :=
  ∀ x : Flow, isUnitFlow x → ∃ p : Ranking, induces p x ∧ objR p = objF x

/-- If the debt were discharged, the two formulations would have the same optimal value from
above.  Stated as a conditional so the dependence is visible. -/
theorem values_agree_of_debt {Flow Ranking : Type*}
    (isUnitFlow : Flow → Prop) (induces : Ranking → Flow → Prop)
    (objF : Flow → ℝ) (objR : Ranking → ℝ)
    (hdebt : PathDecompositionDebt isUnitFlow induces objF objR)
    (x : Flow) (hx : isUnitFlow x) :
    ∃ p : Ranking, objR p = objF x := by
  obtain ⟨p, -, hobj⟩ := hdebt x hx
  exact ⟨p, hobj⟩

section DischargeFinal

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω] [DecidableEq Ω]
variable (G : Type*) [Group G] [Fintype G] [MulAction G Ω]

/-- **E3, discharged.**

Every unit flow is induced by a randomised ranking with the same value, for every objective
linear in the layer marginals.  `PathDecompositionDebt` is instantiated here, so the
reduction of Paper C is a reduction and not a picture. -/
theorem pathDecomposition_discharged (m : ℕ)
    (layer : Fin (m + 1) → Ω → V)
    (hlayer : ∀ (g : G) (i : Fin (m + 1)) (ω : Ω), layer i (g • ω) = layer i ω)
    (sec : LayeredFlow V → (Fin (m + 1) → V) → Ω)
    (hsec : ∀ (F : LayeredFlow V) (t : Fin (m + 1) → V), F.trajLaw m t ≠ 0 →
      ∀ i, layer i (sec F t) = t i)
    (c : Fin (m + 1) → V → ℝ) :
    PathDecompositionDebt
      (fun F : LayeredFlow V =>
        (∑ v, F.x 0 v = 1) ∧ ∀ j, ∑ v, F.x (j + 1) v = ∑ v, F.x j v)
      (fun (P : Ω → ℝ) (F : LayeredFlow V) =>
        (∀ ω, 0 ≤ P ω) ∧ (∑ ω, P ω = 1) ∧
        ∀ (i : Fin (m + 1)) (v : V),
          ∑ ω, P ω * (if layer i ω = v then (1 : ℝ) else 0) = F.x (i : ℕ) v)
      (fun F : LayeredFlow V => ∑ i : Fin (m + 1), ∑ v : V, c i v * F.x (i : ℕ) v)
      (fun P : Ω → ℝ => ∑ ω, P ω * (∑ i : Fin (m + 1), c i (layer i ω))) := by
  rintro F ⟨h0, hcons⟩
  refine ⟨flowRanking G m F (sec F), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun ω => flowRanking_nonneg G m F (sec F) ω
  · exact flowRanking_sum G m F (sec F) h0 hcons
  · exact fun i v => flowRanking_marginal G m F layer hlayer (sec F) (hsec F) i v
  · exact linear_objective_from_marginals m F layer (flowRanking G m F (sec F)) c
      (fun i v => flowRanking_marginal G m F layer hlayer (sec F) (hsec F) i v)


end DischargeFinal


/-! ## The breakpoint law, for every size

The per-size work closes `eta_*(m)` at `m = 5,...,11` with a rational Farkas certificate
each.  The law is

    eta_*(m) = 1                      for m odd,
    eta_*(m) = (m - 2) / (2(m - 1))   for m even,

and this section proves the ARITHMETIC that turns two combinatorial facts about rankings
into that law.  The two facts are inputs, named as hypotheses, not conclusions:

  EVEN.  On every ranking of the family, `r_1 + r_{m-1} = (2/D) * (#{ends carrying an item
  of weight +-3})`.  This is an identity, and it holds because the weights sum to zero, so
  a prefix of length one and a prefix of length `m-1` have opposite sums.

  ODD.   On every ranking, `sum_k (|S_k| - b_k) >= 2 + 2 * [the last item is positive]`.

`EXP_paperC_general_m.py` verifies both by exhaustive enumeration over all distinct
rankings at `m <= 10`, and verifies the CONSTRUCTIVE half of the law -- a distribution
attaining the free value whose marginal band is tight exactly at the law's `eta` -- in exact
arithmetic at every `m` from 4 to 24.  Proving the two facts for general `m` is the
remaining obligation and is recorded as such; nothing below pretends otherwise.

The arithmetic itself is what the two theorems here supply, and it is the step where the
parity actually appears: the same band floor meets a different ceiling depending on whether
the total weight of the family vanishes. -/

/-- The marginal band at a budget floors that item's probability of being there. -/
theorem band_floor (p m η : ℝ) (hm : 0 < m) (h : |p - 1 / m| ≤ η / m) :
    (1 - η) / m ≤ p := by
  have h1 : -(η / m) ≤ p - 1 / m := (abs_le.mp h).1
  have h2 : (1 - η) / m = 1 / m - η / m := by ring
  rw [h2]
  linarith

/-- **From the marginal band to the floor the two-budget bound uses.**

The band constrains each item's probability of occupying each position.  Applied to the two
heavy items at the first and last position it gives four numbers, each at least
`(1 - eta)/m`, and `breakpoint_lower_even` consumes their sum.  This is the step that turns
the problem's own constraint into that hypothesis, so the even lower bound no longer assumes
anything the problem does not already say. -/
theorem end_floor_of_band (p1 p2 q1 q2 S m η : ℝ) (hm : 0 < m)
    (h1 : |p1 - 1 / m| ≤ η / m) (h2 : |p2 - 1 / m| ≤ η / m)
    (h3 : |q1 - 1 / m| ≤ η / m) (h4 : |q2 - 1 / m| ≤ η / m)
    (hS : p1 + p2 + q1 + q2 ≤ S) :
    4 * (1 - η) / m ≤ S := by
  have b1 := band_floor p1 m η hm h1
  have b2 := band_floor p2 m η hm h2
  have b3 := band_floor q1 m η hm h3
  have b4 := band_floor q2 m η hm h4
  have hsum : 4 * (1 - η) / m = (1 - η) / m + (1 - η) / m + (1 - η) / m + (1 - η) / m := by
    field_simp
    ring
  rw [hsum]
  linarith

/-- **The even lower bound.**  If a randomised ranking attains the free value at the first
and the last budget, then the band cannot be tighter than `(m-2)/(2(m-1))`.

`big x` counts the ends of ranking `x` that carry an item of weight `+-3`; `hid` is the
identity that makes `r_1 + r_{m-1}` depend on nothing else, and `hband` is what the marginal
band gives when it is applied to the two heavy items at the two ends. -/
theorem breakpoint_lower_even {R : Type*} [Fintype R]
    (P r1 rm big : R → ℝ) (m D η : ℝ) (hm : 2 < m) (hD : 0 < D)
    (hid : ∀ x, r1 x + rm x = 2 / D * big x)
    (hband : 4 * (1 - η) / m ≤ ∑ x, P x * big x)
    (hfree : ∑ x, P x * (r1 x + rm x) = 4 / (D * (m - 1))) :
    (m - 2) / (2 * (m - 1)) ≤ η := by
  have hm1 : (0:ℝ) < m - 1 := by linarith
  have hmpos : (0:ℝ) < m := by linarith
  have hsplit : ∑ x, P x * (r1 x + rm x) = 2 / D * ∑ x, P x * big x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [hid x]; ring
  have hge : 2 / D * (4 * (1 - η) / m) ≤ 2 / D * ∑ x, P x * big x := by
    have h2D : (0:ℝ) < 2 / D := by positivity
    exact mul_le_mul_of_nonneg_left hband h2D.le
  rw [← hsplit, hfree] at hge
  -- `2/D * (4(1-η)/m) <= 4/(D(m-1))`, and `D > 0` cancels
  have hkey : 8 * (1 - η) * (m - 1) ≤ 4 * m := by
    have hDm : (0:ℝ) < D * m := by positivity
    have hDm1 : (0:ℝ) < D * (m - 1) := by positivity
    have e1 : 2 / D * (4 * (1 - η) / m) = 8 * (1 - η) / (D * m) := by
      field_simp; ring
    have e2 : (4:ℝ) / (D * (m - 1)) = 4 / (D * (m - 1)) := rfl
    rw [e1] at hge
    rw [div_le_div_iff₀ hDm hDm1] at hge
    nlinarith [hge, hD, hm1, hmpos]
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * (m - 1))]
  nlinarith [hkey, hm1]

/-- **The odd lower bound.**  When the family's weights do NOT sum to zero the same
argument closes at `eta = 1`: attaining the free value forces the last item to be negative
almost surely, and the band cannot force a probability down to zero unless `eta >= 1`.

`tot x` is the total excess of ranking `x`, `lastPos x` the indicator that its last item is
positive; `hineq` is the verified inequality and `hfree` says the free value is attained at
every budget, so the total excess has expectation exactly `2`. -/
theorem breakpoint_lower_odd {R : Type*} [Fintype R]
    (P tot lastPos : R → ℝ) (m η : ℝ) (hm : 1 < m)
    (hineq : ∀ x, 2 + 2 * lastPos x ≤ tot x)
    (hPpos : ∀ x, 0 ≤ P x) (hlast : ∀ x, 0 ≤ lastPos x)
    (hsum : ∑ x, P x = 1)
    (hfree : ∑ x, P x * tot x = 2)
    (hband : (m - 1) * (1 - η) / (2 * m) ≤ ∑ x, P x * lastPos x) :
    1 ≤ η := by
  have hmpos : (0:ℝ) < m := by linarith
  have hlow : ∑ x, P x * (2 + 2 * lastPos x) ≤ ∑ x, P x * tot x :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hineq x) (hPpos x)
  have hexp : ∑ x, P x * (2 + 2 * lastPos x)
      = 2 * (∑ x, P x) + 2 * ∑ x, P x * lastPos x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hexp, hsum, hfree] at hlow
  have hzero : ∑ x, P x * lastPos x ≤ 0 := by linarith
  have hnn : (0:ℝ) ≤ ∑ x, P x * lastPos x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hPpos x) (hlast x)
  have heq : ∑ x, P x * lastPos x = 0 := le_antisymm hzero hnn
  rw [heq] at hband
  have h2m : (0:ℝ) < 2 * m := by linarith
  rw [div_le_iff₀ h2m] at hband
  nlinarith [hband, hm]

/-- **The parity gap is at least `1/2`, at every size.**  The even breakpoint never reaches
`1/2` while the odd one is exactly `1`, so the two parities are separated by a constant, not
by a vanishing amount.  This is the statement the paper's headline makes. -/
theorem parity_gap_half (m : ℝ) (hm : 2 < m) :
    (m - 2) / (2 * (m - 1)) < 1 / 2 ∧ 1 / 2 ≤ 1 - (m - 2) / (2 * (m - 1)) := by
  have hm1 : (0:ℝ) < 2 * (m - 1) := by linarith
  constructor
  · rw [div_lt_div_iff₀ hm1 (by norm_num : (0:ℝ) < 2)]
    linarith
  · have : (m - 2) / (2 * (m - 1)) < 1 / 2 := by
      rw [div_lt_div_iff₀ hm1 (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith

/-- The free value, summed over the two budgets the even bound uses. -/
theorem free_value_two_budgets (D m : ℝ) (hD : 0 < D) (hm : 1 < m) :
    2 / (D * (m - 1)) + 2 / (D * (m - 1)) = 4 / (D * (m - 1)) := by ring

section HSecDischarge

/-! # E3: discharging `hsec` for the count-state graph

`pathDecomposition_discharged` takes a section `sec` sending a positive-mass trajectory to
an outcome whose layer labels reproduce it.  Two things have to be shown, and both are
here.

**Legality from positive mass.**  A flow supported on the step graph gives zero kernel
weight to a non-step, so a trajectory of positive mass takes only legal steps.  That is
the half joining the measure to the combinatorics, and it holds for any step relation.

**Realisation.**  A legal count-path is read off coordinatewise: at step `i` exactly one
type's count rises, and that type is the `i`-th served item.  The resulting type sequence
has the path as its layer counts, by induction, and its multiplicities are the path's
endpoint --- so it is realised by an actual permutation of the items, built by gluing the
fibrewise bijections. -/

/-! ## Part one: positive mass forces legal steps -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A kernel supported on a step relation. -/
def StepKernel (K : ℕ → V → V → ℝ) (Step : V → V → Prop) : Prop :=
  ∀ k v w, ¬ Step v w → K k v w = 0

/-- The law of a trajectory under a kernel. -/
noncomputable def pathMass (x0 : V → ℝ) (K : ℕ → V → V → ℝ) :
    (n : ℕ) → (ℕ → V) → ℝ
  | 0, t => x0 (t 0)
  | (n + 1), t => pathMass x0 K n t * K n (t n) (t (n + 1))

/-- **Positive mass forces every step to be legal.**  No structure on the step relation is
used, so this is the general half. -/
theorem pathMass_steps (x0 : V → ℝ) (K : ℕ → V → V → ℝ) (Step : V → V → Prop)
    (hK : StepKernel K Step) :
    ∀ (n : ℕ) (t : ℕ → V), pathMass x0 K n t ≠ 0 → ∀ i < n, Step (t i) (t (i + 1)) := by
  intro n
  induction n with
  | zero => intro t _ i hi; omega
  | succ n ih =>
      intro t ht i hi
      have hfac : pathMass x0 K n t * K n (t n) (t (n + 1)) ≠ 0 := ht
      have h1 : pathMass x0 K n t ≠ 0 := fun h => hfac (by rw [h, zero_mul])
      have h2 : K n (t n) (t (n + 1)) ≠ 0 := fun h => hfac (by rw [h, mul_zero])
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
      · exact ih t h1 i h
      · subst h
        by_contra hc
        exact h2 (hK i (t i) (t (i + 1)) hc)

/-! ## Part two: a legal count-path is realised -/

variable {d : ℕ}

/-- How many of type `τ` appear in the first `i` served positions. -/
def layerCount (m : ℕ) (s : Fin m → Fin d) (i : ℕ) (τ : Fin d) : ℕ :=
  ∑ k ∈ Finset.range i, (if h : k < m then (if s ⟨k, h⟩ = τ then 1 else 0) else 0)

theorem layerCount_zero (m : ℕ) (s : Fin m → Fin d) (τ : Fin d) :
    layerCount m s 0 τ = 0 := by simp [layerCount]

theorem layerCount_succ (m : ℕ) (s : Fin m → Fin d) (i : ℕ) (hi : i < m) (τ : Fin d) :
    layerCount m s (i + 1) τ
      = layerCount m s i τ + (if s ⟨i, hi⟩ = τ then 1 else 0) := by
  rw [layerCount, Finset.sum_range_succ, dif_pos hi]
  rfl

/-- **The realisation.**  A count-path that starts at zero and, at every step, raises
exactly one coordinate by one is exactly the layer count of the sequence that reads off
which coordinate rose. -/
theorem legal_path_realised (m : ℕ) (t : ℕ → Fin d → ℕ) (sτ : Fin m → Fin d)
    (h0 : ∀ τ, t 0 τ = 0)
    (hup : ∀ (i : ℕ) (hi : i < m), t (i + 1) (sτ ⟨i, hi⟩) = t i (sτ ⟨i, hi⟩) + 1)
    (hrest : ∀ (i : ℕ) (hi : i < m) (τ : Fin d), τ ≠ sτ ⟨i, hi⟩ → t (i + 1) τ = t i τ) :
    ∀ i ≤ m, ∀ τ, layerCount m sτ i τ = t i τ := by
  intro i
  induction i with
  | zero => intro _ τ; rw [layerCount_zero, h0]
  | succ n ih =>
      intro hn τ
      have hnm : n < m := by omega
      rw [layerCount_succ m sτ n hnm τ, ih (by omega) τ]
      by_cases h : sτ ⟨n, hnm⟩ = τ
      · rw [if_pos h]
        have := hup n hnm
        rw [h] at this
        omega
      · rw [if_neg h]
        have := hrest n hnm τ (fun hc => h hc.symm)
        omega

/-- The multiplicities of the realising sequence are the path's endpoint. -/
theorem realised_multiplicities (m : ℕ) (t : ℕ → Fin d → ℕ) (sτ : Fin m → Fin d)
    (h0 : ∀ τ, t 0 τ = 0)
    (hup : ∀ (i : ℕ) (hi : i < m), t (i + 1) (sτ ⟨i, hi⟩) = t i (sτ ⟨i, hi⟩) + 1)
    (hrest : ∀ (i : ℕ) (hi : i < m) (τ : Fin d), τ ≠ sτ ⟨i, hi⟩ → t (i + 1) τ = t i τ)
    (τ : Fin d) :
    (Finset.univ.filter (fun k : Fin m => sτ k = τ)).card = t m τ := by
  classical
  have hL := legal_path_realised m t sτ h0 hup hrest m le_rfl τ
  rw [← hL, layerCount]
  rw [Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < m then
        (if sτ ⟨k, h⟩ = τ then 1 else 0) else 0) m]
  exact Finset.sum_congr rfl (fun k _ => by simp [k.isLt])

/-! ## Part three: the sequence comes from a genuine permutation of the items -/

/-- **Gluing the fibres.**  A type sequence whose multiplicities match the items' own
multiplicities is served by an actual permutation: match the positions of each type to the
items of that type, fibre by fibre. -/
noncomputable def matchPerm (m : ℕ) (s ty : Fin m → Fin d)
    (hcard : ∀ τ, Fintype.card {k : Fin m // s k = τ}
      = Fintype.card {j : Fin m // ty j = τ}) : Fin m ≃ Fin m :=
  (Equiv.sigmaFiberEquiv s).symm.trans
    ((Equiv.sigmaCongrRight (fun τ => Fintype.equivOfCardEq (hcard τ))).trans
      (Equiv.sigmaFiberEquiv ty))

theorem matchPerm_type (m : ℕ) (s ty : Fin m → Fin d)
    (hcard : ∀ τ, Fintype.card {k : Fin m // s k = τ}
      = Fintype.card {j : Fin m // ty j = τ}) (k : Fin m) :
    ty (matchPerm m s ty hcard k) = s k := by
  have h := ((Fintype.equivOfCardEq (hcard (s k))) ⟨k, rfl⟩).2
  simpa [matchPerm, Equiv.sigmaFiberEquiv, Equiv.sigmaCongrRight] using h

end HSecDischarge

section CountStateBookkeeping

open Finset

/-! # E3, the bookkeeping: `hsec` at the count-state graph

The three steps are proved upstream.  This section instantiates them: the state space is
the count vector, the step relation is "one type's count rises by one", and the flow's own
kernel is shown to be supported on it.  Nothing here is new mathematics; it is the wiring
that turns the abstract steps into a statement about `trajLaw`. -/

variable {d m : ℕ}

/-- The count states: how many items of each type have been served. -/
abbrev CState (d m : ℕ) := Fin d → Fin (m + 1)

/-- One item of one type is served. -/
def StepC (v w : CState d m) : Prop :=
  ∃ τ : Fin d, (w τ : ℕ) = (v τ : ℕ) + 1 ∧ ∀ τ', τ' ≠ τ → w τ' = v τ'

/-- A flow that never uses a non-step edge has a kernel supported on steps. -/
theorem kernel_stepSupported (F : LayeredFlow (CState d m))
    (hF : ∀ k v w, ¬ StepC v w → F.f k v w = 0) :
    ∀ k v w, ¬ StepC v w → F.kernel k v w = 0 := by
  intro k v w h
  unfold LayeredFlow.kernel
  by_cases hx : F.x k v = 0
  · rw [if_pos hx]
  · rw [if_neg hx, hF k v w h, zero_div]

/-- **Positive trajectory mass forces every step to be legal**, for `trajLaw` itself.
This is `pathMass_steps` transported onto the flow's own trajectory law. -/
theorem trajLaw_stepC (F : LayeredFlow (CState d m))
    (hF : ∀ k v w, ¬ StepC v w → F.f k v w = 0) :
    ∀ (n : ℕ) (t : Fin (n + 1) → CState d m), F.trajLaw n t ≠ 0 →
      ∀ i : Fin n, StepC (t i.castSucc) (t i.succ) := by
  intro n
  induction n with
  | zero => intro t _ i; exact absurd i.isLt (by omega)
  | succ n ih =>
      intro t ht i
      rw [LayeredFlow.trajLaw_succ] at ht
      have h1 : F.trajLaw n (Fin.init t) ≠ 0 := fun h => ht (by rw [h, zero_mul])
      have h2 : F.kernel n (Fin.init t (Fin.last n)) (t (Fin.last (n + 1))) ≠ 0 :=
        fun h => ht (by rw [h, mul_zero])
      by_cases hlast : (i : ℕ) = n
      · have e1 : (Fin.init t) (Fin.last n) = t i.castSucc := by
          simp only [Fin.init]
          congr 1
          exact Fin.ext (by simp [hlast])
        have e2 : t (Fin.last (n + 1)) = t i.succ := by
          congr 1
          exact Fin.ext (by simp [hlast])
        rw [e1, e2] at h2
        by_contra hc
        exact h2 (kernel_stepSupported F hF n _ _ hc)
      · have hi : (i : ℕ) < n := by omega
        have hstep := ih (Fin.init t) h1 ⟨(i : ℕ), hi⟩
        have e1 : (Fin.init t) (⟨(i : ℕ), hi⟩ : Fin n).castSucc = t i.castSucc := by
          simp only [Fin.init]
          congr 1
        have e2 : (Fin.init t) (⟨(i : ℕ), hi⟩ : Fin n).succ = t i.succ := by
          simp only [Fin.init]
          congr 1
        rwa [e1, e2] at hstep

/-- The layer count never exceeds the number of positions, so it lands in `Fin (m+1)`. -/
theorem layerCount_le (s : Fin m → Fin d) (i : ℕ) (hi : i ≤ m) (τ : Fin d) :
    layerCount m s i τ ≤ m := by
  classical
  calc layerCount m s i τ
      ≤ ∑ _k ∈ Finset.range i, 1 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        by_cases h : k < m
        · rw [dif_pos h]; split <;> omega
        · rw [dif_neg h]; omega
    _ = i := by simp
    _ ≤ m := hi

/-- The layer map, valued in the count states. -/
def layerState (s : Fin m → Fin d) (i : ℕ) (hi : i ≤ m) : CState d m :=
  fun τ => ⟨layerCount m s i τ, by
    have := layerCount_le s i hi τ; omega⟩

/-- **`hsec` at the count states.**  A trajectory of positive mass that starts empty is
the layer map of an explicit type sequence, and that sequence is served by a genuine
permutation of the items whenever its multiplicities match theirs. -/
theorem hsec_count_states (F : LayeredFlow (CState d m))
    (hF : ∀ k v w, ¬ StepC v w → F.f k v w = 0)
    (t : Fin (m + 1) → CState d m) (ht : F.trajLaw m t ≠ 0)
    (h0 : ∀ τ, ((t 0) τ : ℕ) = 0) :
    ∃ s : Fin m → Fin d, ∀ (i : ℕ) (hi : i ≤ m), layerState s i hi = t ⟨i, by omega⟩ := by
  classical
  have hsteps := trajLaw_stepC F hF m t ht
  -- read off which coordinate rose at each step
  choose sτ hup hrest using fun i : Fin m => hsteps i
  refine ⟨sτ, ?_⟩
  -- the numeric path, and the three hypotheses `legal_path_realised` wants
  set T : ℕ → Fin d → ℕ := fun i τ => if h : i ≤ m then ((t ⟨i, by omega⟩) τ : ℕ) else 0
    with hT
  have hT0 : ∀ τ, T 0 τ = 0 := by
    intro τ; rw [hT]; simp only [dif_pos (Nat.zero_le m)]; exact h0 τ
  have hTup : ∀ (i : ℕ) (hi : i < m), T (i + 1) (sτ ⟨i, hi⟩) = T i (sτ ⟨i, hi⟩) + 1 := by
    intro i hi
    have hA : i ≤ m := by omega
    have hB : i + 1 ≤ m := by omega
    rw [hT]
    simp only [dif_pos hA, dif_pos hB]
    have := hup ⟨i, hi⟩
    have e1 : (⟨i, hi⟩ : Fin m).castSucc = (⟨i, by omega⟩ : Fin (m + 1)) := Fin.ext (by simp)
    have e2 : (⟨i, hi⟩ : Fin m).succ = (⟨i + 1, by omega⟩ : Fin (m + 1)) := Fin.ext (by simp)
    rwa [e1, e2] at this
  have hTrest : ∀ (i : ℕ) (hi : i < m) (τ : Fin d), τ ≠ sτ ⟨i, hi⟩ →
      T (i + 1) τ = T i τ := by
    intro i hi τ hne
    have hA : i ≤ m := by omega
    have hB : i + 1 ≤ m := by omega
    rw [hT]
    simp only [dif_pos hA, dif_pos hB]
    have := hrest ⟨i, hi⟩ τ hne
    have e1 : (⟨i, hi⟩ : Fin m).castSucc = (⟨i, by omega⟩ : Fin (m + 1)) := Fin.ext (by simp)
    have e2 : (⟨i, hi⟩ : Fin m).succ = (⟨i + 1, by omega⟩ : Fin (m + 1)) := Fin.ext (by simp)
    rw [e1, e2] at this
    exact congrArg Fin.val this
  have hreal := legal_path_realised m T sτ hT0 hTup hTrest
  intro i hi
  funext τ
  have := hreal i hi τ
  rw [hT] at this
  simp only [dif_pos hi] at this
  exact Fin.ext this

end CountStateBookkeeping

/-! ## Audit -/

#print axioms symmetrised_is_feasible
#print axioms symmetrised_not_worse
#print axioms marginal_eq_of_swap_invariant
#print axioms marginal_eq_occupancy_div_card
#print axioms orbitLaw_sum
#print axioms orbitLaw_expectation
#print axioms orbitLaw_invariant
#print axioms relabelledLaw_sum
#print axioms relabelledLaw_expectation
#print axioms relabelledLaw_invariant
#print axioms relabelled_marginal_const
#print axioms value_le_of_pointwise
#print axioms value_stable_of_pointwise
#print axioms ratio_perturb_bound
#print axioms value_stable_renormalised
#print axioms price_ratio_robust
#print axioms max_stable_of_pointwise
#print axioms LayeredFlow.no_flow_from_empty
#print axioms LayeredFlow.pathLaw_eq_occupancy
#print axioms LayeredFlow.pathLaw_sum
#print axioms LayeredFlow.no_flow_from_empty
#print axioms LayeredFlow.pathLaw_eq_occupancy
#print axioms LayeredFlow.pathLaw_sum
#print axioms occupancy_from_path_law
#print axioms occupancy_nonneg
#print axioms flow_marginal_eq_occupancy
#print axioms group_total_eq_expected_count
#print axioms marginal_const_of_relabelling
#print axioms LayeredFlow.kernel_sum
#print axioms LayeredFlow.trajLaw_marginal
#print axioms LayeredFlow.trajLaw_marginal_all
#print axioms LayeredFlow.trajLaw_sum
#print axioms flowRanking_sum
#print axioms flowRanking_marginal
#print axioms linear_objective_from_marginals
#print axioms pathDecomposition_discharged
#print axioms values_agree_of_debt
#print axioms band_floor
#print axioms end_floor_of_band
#print axioms breakpoint_lower_even
#print axioms breakpoint_lower_odd
#print axioms O2_strict_odd
#print axioms O2_strict_even
#print axioms parity_gap_half
#print axioms free_value_two_budgets

#print axioms pathMass_steps
#print axioms layerCount_succ
#print axioms legal_path_realised
#print axioms realised_multiplicities
#print axioms matchPerm_type

#print axioms kernel_stepSupported
#print axioms trajLaw_stepC
#print axioms layerCount_le
#print axioms hsec_count_states

end CIGAMF.P13.PaperCBreakpoint
