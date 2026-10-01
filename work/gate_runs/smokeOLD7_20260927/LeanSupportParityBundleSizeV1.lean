import «LeanSupportPassiveDecisionMassV1»

/-! # R5: how large a BUNDLE of evidence items must be before acquisition works.

The question is not "does greedy fail on XOR" (Krause-Guestrin 2005 already
exhibit an XOR counterexample for information gain, and Feige-Raghavan-Peleg-Upfal
1994 study noisy parity). The question here is POSITIVE and geometric: on a given
support geometry with a given query class, how many queries must be ACQUIRED
TOGETHER before any of them moves the decision at all? Call that the bundle size.

The answer proved below is that the bundle size is set by how the danger region
sits relative to the query class, not by the query primitive. The primitive is
the same in both halves — a physical membership test against the actual support.

* Multi-tip geometry (`multitip_single_query_determines`): the danger region of
  decision `j` is the single tip `j`, so ONE membership query already determines
  `selectedRadius (components W) {j} = 0`. Bundle size 1.
* Parity geometry (`parity_bundle_insufficient`, `adaptive_balanced`): the danger
  region of decision `b` is a parity class of the `d` auxiliary tips, so EVERY
  bundle of fewer than `d` queries leaves the loss exactly at its prior value.
  Bundle size `d`.

The parity construction is the one the supervisor specified:
  `S ⊆ Fin d` is the set of ones, `par S` is its parity,
  `Wof S = {decIdx (!par S)} ∪ auxIdx '' S ⊆ Fin (d+2)`,
and the loss of retaining the singleton decision `b ∈ Bool` is the ACTUAL
normalised multi-tip radius `(2/(m-1)) * selectedRadius (components (Wof S)) {decIdx b}`
with `m = d+2`.  `loss_indicator` proves — it does not assume — that this equals
`indicator (b ≠ par S)`.

WHAT IS PROVED HERE (all Lean, axiom-audited).

1. `radius_indicator` / `loss_indicator` — the radius bridge. The normalised
   selected radius of decision `b` in world `Wof S` is `1` if `b ≠ par S` and `0`
   otherwise. Proved from `radius_formula`, not stipulated.
2. `par_flipAt`, `flipAt_involutive`, `mem_flipAt_of_ne` — a single-bit flip is an
   involution that preserves every other bit and reverses the parity.
3. `adaptive_balanced` — the posterior pairing, for FULLY ADAPTIVE acquisition.
   For any transcript-measurable rule `(Q, g)` whose queried set is never all of
   `Fin d`, exactly half of the `2^d` worlds are answered wrongly.
4. `adaptive_risk_half` — the same statement in the actual normalised radius:
   `2 * ∑ S, loss S (g S) = 2^d`, i.e. average loss exactly `1/2`.
5. `bundle_risk_half`, `single_bit_gain_zero` — the non-adaptive corollary and the
   one-step greedy gain: a bundle of fewer than `d` bit queries has gain `0`.
6. `parity_decision_zero_loss`, `parity_determined_by_all` — the other side of the
   cliff: knowing the parity gives loss `0`, and all `d` bits determine the parity.
7. `greedy_ratio_unbounded` — `M/d` is unbounded over `M ≥ d`.
8. `multitip_single_query_determines`, `multitip_single_query_certifies` — bundle
   size 1 in the multi-tip geometry, against the same `selectedRadius`.

WHAT THIS DOES NOT ESTABLISH.

- No probability space appears. "Uniform prior" is encoded as counting over
  `Finset (Fin d)`, and "risk 1/2" is the counting statement `2 * #errors = 2^d`
  (and its real-valued image under `loss`). No measure, no expectation operator.
- COST is not formalised. The budget `B`, the auxiliary cost `1`, and the direct
  cost `M` appear only through the hypotheses `(Q S).card < d` (you cannot afford
  `d` bit queries) and through `Q S : Finset (Fin d)` (no direct query is in the
  transcript at all). That the hard-budget value function equals `1/2` for
  `B < min (d, M)` and `0` for `B ≥ min (d, M)` is NOT a Lean theorem; it is
  numerical evidence from `research/worker_distinct_completion_20260913/`
  `parity_bundle_probe.json` (exact-fraction Bellman DP, full-state cross-check
  for `d ≤ 6`) plus `R5_bundle_size_separation.json`. The Lean theorems here are
  the two halves of the cliff at the level of a single transcript.
- `Transcript` is a HYPOTHESIS, not a construction. It says the queried set and
  the answer depend on the world only through the answers already received. No
  decision tree is built, and no claim is made that every implementable strategy
  satisfies it (it is the standard measurability requirement; strategies that
  peek at the world do not satisfy it and are not covered).
- `single_bit_gain_zero` says the gain of a one-bit bundle is zero. It does NOT
  say every greedy rule fails. Entropy-based acquisition on the WORLD posterior
  has strictly positive gain for every bit and reaches cost `d`; that comparison
  is numerical (`R5_bundle_size_separation.json`), not proved here.
- The multi-tip half proves that one query DETERMINES the safety of one decision.
  It does not quantify the risk reduction over any particular prior on `W`; the
  exact dense-family gain is numerical only.
- Nothing here covers laminar or interval danger families. They were not
  formalised; the only two geometries treated are multi-tip and parity.
-/

namespace CIGAMF.P13.SupportParityBundleSize
open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportUnboundedObstruction
open CIGAMF.P13.SupportMultiTipGeometry
noncomputable section

variable {m d : ℕ}

/-! ## Part 0. Bundle size 1 in the multi-tip geometry.

The danger region of decision `j` is the single tip `j`. One physical membership
query against the actual support therefore pins `selectedRadius … {j}` exactly. -/

/-- ONE membership query determines the safety of decision `j`: two worlds that
answer the query at tip `j` alike have the same safety verdict for `j`. -/
theorem multitip_single_query_determines (hm : 2 ≤ m) (j : Fin m) (W W' : Finset (Fin m))
    (h : tip j ∈ support W ↔ tip j ∈ support W') :
    selectedRadius (components W) {j} = 0 ↔ selectedRadius (components W') {j} = 0 := by
  rw [zero_radius_iff hm, zero_radius_iff hm, ← physical_membership_iff hm W j,
    ← physical_membership_iff hm W' j]
  exact not_congr h

/-- And a negative answer to that single query certifies decision `j` outright. -/
theorem multitip_single_query_certifies (hm : 2 ≤ m) (W : Finset (Fin m)) (j : Fin m)
    (h : tip j ∉ support W) : selectedRadius (components W) {j} = 0 := by
  rw [zero_radius_iff hm]
  exact fun hj => h ((physical_membership_iff hm W j).mpr hj)

/-! ## Part 1. The parity construction on the real support. -/

/-- A world is the set of auxiliary bits that are on. -/
abbrev World (d : ℕ) := Finset (Fin d)

/-- The parity bit of a world. -/
def par (S : World d) : Bool := decide (S.card % 2 = 1)

/-- The two feasible retained decisions sit at tips `0` and `1`. -/
def decIdx (b : Bool) : Fin (d + 2) := if b then ⟨1, by omega⟩ else ⟨0, by omega⟩

/-- Auxiliary bit `i` sits at tip `i+2`. -/
def auxIdx (i : Fin d) : Fin (d + 2) := ⟨i.val + 2, by have := i.isLt; omega⟩

/-- `W_x = {1 - b(x)} ∪ {i+2 : x_i = 1}`. -/
def Wof (S : World d) : Finset (Fin (d + 2)) := insert (decIdx (!par S)) (S.image auxIdx)

lemma decIdx_val_lt (b : Bool) : (decIdx (d := d) b).val < 2 := by
  cases b <;> simp [decIdx]

lemma auxIdx_val (i : Fin d) : (auxIdx i).val = i.val + 2 := rfl

lemma decIdx_inj {b c : Bool} (h : (decIdx (d := d) b) = decIdx c) : b = c := by
  cases b <;> cases c <;> first
    | rfl
    | (exfalso; have := congrArg Fin.val h; simp [decIdx] at this)

lemma decIdx_not_mem_image (S : World d) (b : Bool) : decIdx b ∉ S.image auxIdx := by
  simp only [mem_image, not_exists]
  rintro i ⟨-, he⟩
  have h1 := decIdx_val_lt (d := d) b
  have h2 : (decIdx (d := d) b).val = i.val + 2 := by rw [← he, auxIdx_val]
  omega

/-- Decision `b` is present as a tip exactly when it disagrees with the parity. -/
lemma mem_Wof_decIdx (S : World d) (b : Bool) : decIdx b ∈ Wof S ↔ b ≠ par S := by
  rw [Wof, mem_insert]
  constructor
  · rintro (h | h)
    · have hb := decIdx_inj h
      subst hb
      exact Bool.not_ne_self (par S)
    · exact absurd h (decIdx_not_mem_image S b)
  · intro h
    left
    have : b = !par S := by cases b <;> cases hb : par S <;> simp_all
    rw [this]

/-! ### The radius bridge. Proved from `radius_formula`, not assumed. -/

/-- The ACTUAL multi-tip selected radius of decision `b` in world `Wof S`. -/
theorem radius_indicator (S : World d) (b : Bool) :
    selectedRadius (components (Wof S)) {decIdx b}
      = if b = par S then 0 else ((d : ℝ) + 1) / 2 := by
  rw [radius_formula (by omega) (Wof S) (decIdx b)]
  by_cases h : b = par S
  · have hn : decIdx b ∉ Wof S := by
      rw [mem_Wof_decIdx]
      simpa using h
    rw [if_neg hn, if_pos h]
  · have hp : decIdx b ∈ Wof S := (mem_Wof_decIdx S b).mpr h
    rw [if_pos hp, if_neg h]
    push_cast
    ring

/-- The normalised loss: `(2/(m-1)) * selectedRadius`, with `m = d+2`. -/
def loss (S : World d) (b : Bool) : ℝ :=
  (2 / ((d : ℝ) + 1)) * selectedRadius (components (Wof S)) {decIdx b}

/-- **Radius bridge.** The normalised loss is the indicator of `b ≠ par S`. -/
theorem loss_indicator (S : World d) (b : Bool) :
    loss S b = if b ≠ par S then 1 else 0 := by
  have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
  rw [loss, radius_indicator]
  by_cases h : b = par S
  · simp [h]
  · rw [if_neg h, if_pos h]
    field_simp

/-! ### Single-bit flips. -/

/-- Flip auxiliary bit `i`. -/
def flipAt (S : World d) (i : Fin d) : World d := if i ∈ S then S.erase i else insert i S

lemma mem_flipAt_of_ne (S : World d) (i k : Fin d) (h : k ≠ i) :
    k ∈ flipAt S i ↔ k ∈ S := by
  unfold flipAt
  by_cases hi : i ∈ S <;> simp [hi, mem_erase, mem_insert, h]

lemma flipAt_involutive (S : World d) (i : Fin d) : flipAt (flipAt S i) i = S := by
  unfold flipAt
  by_cases hi : i ∈ S
  · simp only [hi, if_pos]
    rw [if_neg (Finset.notMem_erase i S), Finset.insert_erase hi]
  · simp only [hi, if_false]
    rw [if_pos (Finset.mem_insert_self i S), Finset.erase_insert hi]

lemma par_flipAt (S : World d) (i : Fin d) : par (flipAt S i) = !(par S) := by
  unfold flipAt par
  by_cases hi : i ∈ S
  · simp only [hi, if_pos]
    have hc : S.card = (S.erase i).card + 1 := by
      rw [Finset.card_erase_of_mem hi]
      have : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    rw [hc]
    rcases Nat.mod_two_eq_zero_or_one (S.erase i).card with h | h
    · have h' : ((S.erase i).card + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : ((S.erase i).card + 1) % 2 = 0 := by omega
      simp [h, h']
  · simp only [hi, if_false]
    rw [Finset.card_insert_of_notMem hi]
    rcases Nat.mod_two_eq_zero_or_one S.card with h | h
    · have h' : (S.card + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (S.card + 1) % 2 = 0 := by omega
      simp [h, h']

/-! ## Part 2. The posterior pairing, for fully adaptive acquisition. -/

/-- `(Q, g)` is transcript-measurable: the set of bits queried and the decision
returned depend on the world only through the answers already received. This is
the ONLY thing adaptivity is allowed to use; no decision tree is constructed. -/
def Transcript (Q : World d → Finset (Fin d)) (g : World d → Bool) : Prop :=
  ∀ S S' : World d, (∀ i ∈ Q S, (i ∈ S ↔ i ∈ S')) → Q S' = Q S ∧ g S' = g S

/-- A canonical unqueried bit. It is a function of the queried SET, so two worlds
with the same transcript get the same one. -/
def freeBit (hd : 0 < d) (T : Finset (Fin d)) : Fin d :=
  if h : (Tᶜ : Finset (Fin d)).Nonempty then h.choose else ⟨0, hd⟩

lemma freeBit_not_mem (hd : 0 < d) (T : Finset (Fin d)) (h : (Tᶜ : Finset (Fin d)).Nonempty) :
    freeBit hd T ∉ T := by
  simp only [freeBit, dif_pos h]
  have hc := h.choose_spec
  simpa using hc

lemma compl_nonempty_of_card_lt (T : Finset (Fin d)) (h : T.card < d) :
    (Tᶜ : Finset (Fin d)).Nonempty := by
  rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
  omega

/-- **Adaptive posterior pairing.** If the acquisition rule never queries all `d`
bits, then on EVERY transcript the parity stays uniform: exactly half of the
`2^d` worlds are answered wrongly. -/
theorem adaptive_balanced (hd : 0 < d) (Q : World d → Finset (Fin d)) (g : World d → Bool)
    (htr : Transcript Q g) (hfree : ∀ S, ((Q S)ᶜ : Finset (Fin d)).Nonempty) :
    2 * (univ.filter (fun S : World d => g S ≠ par S)).card = 2 ^ d := by
  classical
  set φ : World d → World d := fun S => flipAt S (freeBit hd (Q S)) with hφ
  have step : ∀ S : World d,
      g (φ S) = g S ∧ par (φ S) = !(par S) ∧ φ (φ S) = S := by
    intro S
    have hi : freeBit hd (Q S) ∉ Q S := freeBit_not_mem hd _ (hfree S)
    have hagree : ∀ i ∈ Q S, (i ∈ S ↔ i ∈ φ S) := by
      intro i hiQ
      have hne : i ≠ freeBit hd (Q S) := by rintro rfl; exact hi hiQ
      exact (mem_flipAt_of_ne S _ i hne).symm
    obtain ⟨hQ, hg⟩ := htr S (φ S) hagree
    refine ⟨hg, par_flipAt S _, ?_⟩
    show flipAt (φ S) (freeBit hd (Q (φ S))) = S
    rw [hQ]
    exact flipAt_involutive S _
  have hEC : (univ.filter (fun S : World d => g S ≠ par S)).card
      = (univ.filter (fun S : World d => ¬ (g S ≠ par S))).card := by
    refine Finset.card_bij' (fun S _ => φ S) (fun S _ => φ S) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_univ, true_and, not_not] at hS ⊢
      obtain ⟨hg, hp, -⟩ := step S
      rw [hg, hp]
      cases hb : g S <;> cases hc : par S <;> simp_all
    · intro S hS
      simp only [mem_filter, mem_univ, true_and, not_not] at hS ⊢
      obtain ⟨hg, hp, -⟩ := step S
      rw [hg, hp]
      cases hb : g S <;> cases hc : par S <;> simp_all
    · intro S _; exact (step S).2.2
    · intro S _; exact (step S).2.2
  have h2 : (univ.filter (fun S : World d => g S ≠ par S)).card
      + (univ.filter (fun S : World d => ¬ (g S ≠ par S))).card = 2 ^ d := by
    rw [Finset.card_filter_add_card_filter_not]
    simp [Fintype.card_finset]
  rw [← hEC] at h2
  rw [← h2]
  ring

/-- The same statement in the ACTUAL normalised radius: average loss is `1/2`. -/
theorem adaptive_risk_half (hd : 0 < d) (Q : World d → Finset (Fin d)) (g : World d → Bool)
    (htr : Transcript Q g) (hfree : ∀ S, ((Q S)ᶜ : Finset (Fin d)).Nonempty) :
    2 * (∑ S : World d, loss S (g S)) = (2 : ℝ) ^ d := by
  have hL : ∀ S ∈ (univ : Finset (World d)),
      loss S (g S) = if g S ≠ par S then (1 : ℝ) else 0 := fun S _ => loss_indicator S (g S)
  rw [Finset.sum_congr rfl hL, Finset.sum_boole]
  have hcount := adaptive_balanced hd Q g htr hfree
  exact_mod_cast hcount

/-! ## Part 3. Bundle size in the parity geometry. -/

/-- Non-adaptive corollary: a FIXED bundle of fewer than `d` bit queries leaves
the loss exactly at its prior value. -/
theorem bundle_risk_half (hd : 0 < d) (Q : Finset (Fin d)) (hQ : Q.card < d)
    (g : World d → Bool) (hg : ∀ S S', (∀ i ∈ Q, (i ∈ S ↔ i ∈ S')) → g S = g S') :
    2 * (univ.filter (fun S : World d => g S ≠ par S)).card = 2 ^ d := by
  refine adaptive_balanced hd (fun _ => Q) g ?_ (fun _ => compl_nonempty_of_card_lt Q hQ)
  intro S S' h
  exact ⟨rfl, (hg S S' h).symm⟩

/-- One-step greedy gain of a single bit query is exactly zero (`d ≥ 2`). -/
theorem single_bit_gain_zero (hd : 1 < d) (i : Fin d) (g : World d → Bool)
    (hg : ∀ S S', (i ∈ S ↔ i ∈ S') → g S = g S') :
    2 * (univ.filter (fun S : World d => g S ≠ par S)).card = 2 ^ d := by
  refine bundle_risk_half (by omega) {i} (by simpa using hd) g ?_
  intro S S' h
  exact hg S S' (h i (mem_singleton_self i))

/-- Fewer than `d` bits never determine the parity: the bundle is uninformative. -/
theorem parity_bundle_insufficient (Q : Finset (Fin d)) (hQ : Q.card < d) :
    ∃ S S' : World d, (∀ i ∈ Q, (i ∈ S ↔ i ∈ S')) ∧ par S ≠ par S' := by
  obtain ⟨i, hi⟩ := compl_nonempty_of_card_lt Q hQ
  rw [mem_compl] at hi
  refine ⟨∅, flipAt ∅ i, ?_, ?_⟩
  · intro k hk
    have hne : k ≠ i := by rintro rfl; exact hi hk
    exact (mem_flipAt_of_ne _ _ _ hne).symm
  · rw [par_flipAt]
    exact Bool.self_ne_not _

/-- All `d` bits DO determine the parity: bundle size `d` is enough. -/
theorem parity_determined_by_all (S S' : World d)
    (h : ∀ i ∈ (univ : Finset (Fin d)), (i ∈ S ↔ i ∈ S')) : par S = par S' := by
  have hEq : S = S' := Finset.ext fun i => h i (mem_univ i)
  rw [hEq]

/-- The other side of the cliff: a decision that knows the parity has zero loss. -/
theorem parity_decision_zero_loss (S : World d) : loss S (par S) = 0 := by
  rw [loss_indicator]
  simp

/-- The greedy overspend `M / d` is unbounded over direct-query costs `M ≥ d`. -/
theorem greedy_ratio_unbounded (hd : 0 < d) (K : ℝ) :
    ∃ M : ℕ, d ≤ M ∧ K ≤ (M : ℝ) / (d : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (K * (d : ℝ))
  refine ⟨max d n, le_max_left _ _, ?_⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ hdR]
  have hmax : (n : ℝ) ≤ ((max d n : ℕ) : ℝ) := by exact_mod_cast le_max_right d n
  linarith

#print axioms multitip_single_query_determines
#print axioms multitip_single_query_certifies
#print axioms radius_indicator
#print axioms loss_indicator
#print axioms par_flipAt
#print axioms flipAt_involutive
#print axioms adaptive_balanced
#print axioms adaptive_risk_half
#print axioms bundle_risk_half
#print axioms single_bit_gain_zero
#print axioms parity_bundle_insufficient
#print axioms parity_determined_by_all
#print axioms parity_decision_zero_loss
#print axioms greedy_ratio_unbounded

end
end CIGAMF.P13.SupportParityBundleSize
