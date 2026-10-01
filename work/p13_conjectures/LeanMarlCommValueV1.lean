import Mathlib

/-!
# The value of communication is a Bayes risk on acceptable sets, not a disagreement rate

Direction A of paper_marl_v2 (ledger L-198): predict the value of runtime communication before any communication is
learned.  A receiver acts on an observation `obs : World → O` (its local view, or a decoded view).  Under a law `p` on
worlds and acceptable sets `safe`, the best achievable unacceptable-action probability on `obs` is the BAYES RISK

    bayesRisk obs = Σ_o min_a Σ_{F : obs F = o, a ∉ safe F} p F,

and the value of communication for the risk is the drop of this Bayes risk when the view is refined.

## WHAT IS PROVED
* `risk_ge_bayes` — every randomised policy on `obs` has risk at least `bayesRisk obs`.
* `bayes_attained` — the per-class argmin policy attains it, so it is the exact optimum.
* `bayes_refine` — a finer view never has larger Bayes risk (`obs F = obs G` whenever `fine F = fine G`).
* `comm_gain_le_headroom` — hence the best risk improvement any message can buy over the best zero-byte policy is at
  most `bayesRisk loc`: the zero-byte Bayes risk is the communication HEADROOM (and the full view attains it when every
  world has an acceptable action).
* `disagreement_not_risk` — agreement with a reference policy is NOT this quantity: with acceptable sets "any answer but
  the world's own index" on two worlds, the answer `2` disagrees with the reference answer `0` in EVERY world yet is
  acceptable in both (disagreement 1, risk 0), while the reference answer itself is unacceptable in world `0` (agreement
  1, risk 1/2 under the uniform law).  So a teacher-agreement diagnostic can rank receivers in the wrong order.

## WHAT THIS DOES NOT ESTABLISH
- That the E3 teacher's acceptable set or law is the right `safe`/`p`; the V-D probe estimates a teacher-specific proxy.
- That a learned receiver attains the Bayes risk of its view; the relay gain is an empirical quantity.
-/

namespace CIGAMF.P13.MarlCommValue

open Finset

variable {World Act O : Type*} [Fintype World] [DecidableEq World] [Fintype Act] [DecidableEq Act]
  [Fintype O] [DecidableEq O] [Nonempty Act]

variable (safe : World → Finset Act) (p : World → ℝ)

/-- Unacceptable mass of action `a` inside the class of observation `o`. -/
noncomputable def badMass (obs : World → O) (o : O) (a : Act) : ℝ :=
  ∑ F ∈ univ.filter (fun F => obs F = o ∧ a ∉ safe F), p F

/-- The Bayes risk of an observation: the best unacceptable mass, class by class. -/
noncomputable def bayesRisk (obs : World → O) : ℝ :=
  ∑ o, univ.inf' univ_nonempty (badMass safe p obs o)

/-- The risk of a randomised policy `q o a` on `obs`. -/
noncomputable def risk (obs : World → O) (q : O → Act → ℝ) : ℝ :=
  ∑ o, ∑ a, q o a * badMass safe p obs o a

theorem badMass_nonneg (hp : ∀ F, 0 ≤ p F) (obs : World → O) (o : O) (a : Act) :
    0 ≤ badMass safe p obs o a :=
  Finset.sum_nonneg fun F _ => hp F

/-- **Every randomised policy pays at least the Bayes risk.** -/
theorem risk_ge_bayes (obs : World → O) (q : O → Act → ℝ) (hq : ∀ o a, 0 ≤ q o a)
    (hqs : ∀ o, ∑ a, q o a = 1) : bayesRisk safe p obs ≤ risk safe p obs q := by
  unfold bayesRisk risk
  refine Finset.sum_le_sum fun o _ => ?_
  set m := univ.inf' univ_nonempty (badMass safe p obs o)
  calc m = ∑ a, q o a * m := by rw [← Finset.sum_mul, hqs o, one_mul]
    _ ≤ ∑ a, q o a * badMass safe p obs o a :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (Finset.inf'_le _ (mem_univ a)) (hq o a)

/-- **The per-class argmin attains it.** -/
theorem bayes_attained (obs : World → O) :
    ∃ pol : O → Act, ∑ o, badMass safe p obs o (pol o) = bayesRisk safe p obs := by
  classical
  choose pol hpol using fun o : O =>
    (Finset.exists_mem_eq_inf' univ_nonempty (badMass safe p obs o))
  exact ⟨fun o => pol o, by unfold bayesRisk; exact Finset.sum_congr rfl fun o _ => (hpol o).2.symm⟩

/-- The Bayes risk written over worlds: the argmin policy's unacceptable mass. -/
theorem badMass_sum_eq (obs : World → O) (pol : O → Act) :
    ∑ o, badMass safe p obs o (pol o) = ∑ F ∈ univ.filter (fun F => pol (obs F) ∉ safe F), p F := by
  classical
  unfold badMass
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext F
    simp only [mem_biUnion, mem_univ, mem_filter, true_and]
    constructor
    · rintro ⟨o, ho, hF⟩; rw [ho]; exact hF
    · intro hF; exact ⟨obs F, rfl, hF⟩
  · intro o _ o' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro F hF hF'
    simp only [mem_filter, mem_univ, true_and] at hF hF'
    exact hne (hF.1.symm.trans hF'.1)

/-- **A finer view never has larger Bayes risk.** -/
theorem bayes_refine {L : Type*} [Fintype L] [DecidableEq L] (hp : ∀ F, 0 ≤ p F)
    (coarse : World → O) (fine : World → L)
    (hfine : ∀ F G, fine F = fine G → coarse F = coarse G) :
    bayesRisk safe p fine ≤ bayesRisk safe p coarse := by
  classical
  -- the coarse argmin, read through the fine view, is a fine policy
  obtain ⟨pol, hpol⟩ := bayes_attained safe p coarse
  let polF : L → Act := fun l =>
    if h : ∃ F, fine F = l then pol (coarse h.choose) else Classical.arbitrary Act
  have hsame : ∀ F, polF (fine F) = pol (coarse F) := fun F => by
    have h : ∃ G, fine G = fine F := ⟨F, rfl⟩
    simp only [polF, dif_pos h]
    rw [hfine _ _ h.choose_spec]
  -- the fine Bayes risk is at most that policy's risk, which equals the coarse Bayes risk
  have h1 : bayesRisk safe p fine ≤ ∑ l, badMass safe p fine l (polF l) := by
    unfold bayesRisk
    exact Finset.sum_le_sum fun l _ => Finset.inf'_le _ (mem_univ _)
  rw [badMass_sum_eq] at h1
  rw [← hpol, badMass_sum_eq]
  refine h1.trans (le_of_eq ?_)
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext F; simp only [mem_filter, mem_univ, true_and]; rw [hsame]

/-- **The communication headroom.**  Whatever a finer (message-augmented) view buys over the best zero-byte policy,
it is at most the zero-byte Bayes risk. -/
theorem comm_gain_le_headroom {L : Type*} [Fintype L] [DecidableEq L] (hp : ∀ F, 0 ≤ p F)
    (loc : World → O) (view : World → L) (hfine : ∀ F G, view F = view G → loc F = loc G) :
    0 ≤ bayesRisk safe p loc - bayesRisk safe p view ∧
      bayesRisk safe p loc - bayesRisk safe p view ≤ bayesRisk safe p loc := by
  have h1 := bayes_refine safe p hp loc view hfine
  have h2 : 0 ≤ bayesRisk safe p view := by
    unfold bayesRisk
    exact Finset.sum_nonneg fun l _ => by
      obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' univ_nonempty (badMass safe p view l)
      rw [ha]; exact badMass_nonneg safe p hp view l a
  constructor <;> linarith

/-! ## Agreement with a reference is not risk -/

/-- Three answers; the reference (teacher) answers `0` everywhere; every answer but the world's own index is
acceptable ("any world but the true one"). -/
def W2safe (w : Fin 2) : Finset (Fin 3) := univ.erase (w.castSucc)

/-- **Disagreement is not risk.**  With acceptable sets "any answer but the world's own index": the answer `2` differs from
the reference answer `0` in every world and is acceptable in every world; the reference answer `0` is unacceptable in
world `0` and acceptable in world `1`. -/
theorem disagreement_not_risk :
    (∀ w : Fin 2, (2 : Fin 3) ≠ 0 ∧ (2 : Fin 3) ∈ W2safe w) ∧
    ((0 : Fin 3) ∉ W2safe 0 ∧ (0 : Fin 3) ∈ W2safe 1) := by
  refine ⟨fun w => ⟨by decide, ?_⟩, by decide, by decide⟩
  fin_cases w <;> decide

end CIGAMF.P13.MarlCommValue

#print axioms CIGAMF.P13.MarlCommValue.risk_ge_bayes
#print axioms CIGAMF.P13.MarlCommValue.bayes_attained
#print axioms CIGAMF.P13.MarlCommValue.badMass_sum_eq
#print axioms CIGAMF.P13.MarlCommValue.bayes_refine
#print axioms CIGAMF.P13.MarlCommValue.comm_gain_le_headroom
#print axioms CIGAMF.P13.MarlCommValue.disagreement_not_risk
