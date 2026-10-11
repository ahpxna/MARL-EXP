import Mathlib
import LeanMarlSupportV1

/-!
# The frozen-receiver floor is not monotone in the channel; the task floor is (G7, candidate L2)

Three objects must not be confused (research/papers/audits/G7_FLOORS_SCOPE_20261003.md):
* **knowledge / reconstruction** — what ANY decoder can hold or recover from the channel (`LeanMarlReceiverFloorV1/V2`,
  `NetFloorV1`, `HoldFloorV1`): a channel quantity, monotone in the channel;
* **task (decision)** — whether SOME decision-adaptive policy on the view is acceptable (`LeanMarlDecisionDepthV1`,
  `LeanMarlCommValueV1.bayes_refine`): monotone in the information of the view;
* **frozen receiver** — whether ONE FIXED trained receiver keeps its performance when the channel changes
  (`LeanMarlSupportV1`, `LeanCityReceiverContractV1.no_receiver_free_certificate`).
This file makes the difference between the last two formal, on the finite instance of `LeanMarlSupportV1` (message bit ×
copy age; a one-step-old copy reports the opposite of the current state).

## WHAT IS PROVED
* `task_upward_closed` (§1) — if the coarse observation factors through the fine one, every policy that is acceptable in
  every world on the coarse observation lifts to one on the fine observation: the set of channels on which the TASK is
  feasible is upward closed under refinement.  (Policy form of `LeanUnifiedObstructionOrderV1.resolution_refines` /
  `LeanMarlCompiledSilenceV1.messages_keep_safety`, which state it for common-safe classes.)  Witness:
  `task_upward_witness`.
* `emulation_repairs` (§2) — for ANY finite input space, loss and garbling `γ`, under the two named hypotheses
  - `hpush : pushLaw Q γ = P` (the garbling maps the DEPLOYMENT law EXACTLY onto the TRAINING law, as a joint law on the
    whole input) and
  - `hsem : ∀ x a, loss (γ x) a = loss x a` (the garbling does not change what the input means for the task),
  the frozen receiver composed with the garbling has deployment risk EQUAL to its training risk:
  `risk Q loss (r ∘ γ) = risk P loss r`.
* `deploy_dominates_train`, `frozen_floor_not_monotone` (§3) — on the `LeanMarlSupportV1` instance with the garbling
  `gam (m, 0) = (1 − m, 1)`, identity on age-1 inputs: `gam` preserves the state everywhere and pushes `Qdeploy` exactly
  onto `Ptrain` (the deployment channel Blackwell-dominates the training channel for this task); the task floor is met on
  both channels (`f` has risk 0 on each); the age-blind receiver `g` is training-optimal (risk 0, every rule ≥ 0) and as
  good as silence in training (0 ≤ 1/2), yet on the FRESHER deployment channel `g` has risk 1 > 1/2 = silence; and
  `g ∘ gam` has deployment risk 0 (emulation repairs, by `emulation_repairs`).  So the set of channels on which a fixed
  receiver is adequate is NOT upward closed, while task feasibility is (§1); emulation restores upward closure for this
  receiver.
* `marginal_match_insufficient` (§4) — the hypothesis `hpush` is about the JOINT law and cannot be weakened to per-slot
  marginals: on a two-slot input whose deployment law has the SAME two single-slot marginals as the training law but a
  different joint law, the frozen receiver (trained to predict slot 2 from slot 1) has training risk 0 and deployment risk 1
  when the channel is left as it is (identity garbling: marginals already match), while the joint garbling
  `gJ (b₁, b₂) = (1 − b₁, b₂)` satisfies `hpush` and `hsem` and repairs it exactly (risk 0).

## Reading for E3 (stated, not proved here)
`emulation_repairs` is the formal content of "an upgrade can be emulated" UNDER the named hypothesis `hpush`: a garbling
that reproduces the TRAINING JOINT LAW of the receiver's input (and keeps its task meaning, `hsem`) recovers the training
performance exactly.  `hpush` is a hypothesis, not a property of E3; the E3 evidence so far indicates that the
garblings tried there do not meet it:
* the per-slot / per-rank age remaps (ledger L-295) match marginals, not the joint law of the view, and
  `marginal_match_insufficient` shows that marginal matching alone can fail completely;
* the joint-throttle test (PROTOCOL_E3_JOINT_THROTTLE_20261003, ledger L-296) changed the actor's INPUT only (the protocol
  state and the sender-side age mirror followed the unthrottled stream); it does not test whether a coordinated
  sender / cache / mirror / actor garbling satisfies `hpush` (ledger L-302: the mirror explanation is a hypothesis).
So in E3 the theorem explains why emulation is the right repair target and names exactly what must be achieved (a
producer- or protocol-side garbling satisfying `hpush`); it does not say that any implemented E3 garbling achieves it.
`LeanMarlEmulationV1.upgrade_emulation` is the knowledge-level counterpart (decode sets of the poorer budget are subsets of
the richer one's for the SAME committed orders), which is a statement about decode sets, not about the law of the view
under a different order schedule.

## WHAT THIS DOES NOT ESTABLISH
- Anything about the trained CityFlow receivers: the instances are finite models; that the E3 receivers behave like `g`
  (an age-blind extrapolation learned on the poor channel) is the empirical claim (L-249, L-250, L-258).
- Closed-loop return: risks here are one-step expected losses under fixed input laws.  In closed loop the deployment law
  of the view depends on the policy, so `hpush` would have to hold for the law the emulated system induces.
- That `hpush` holds for any implemented E3 garbling: it is a named hypothesis; the per-slot / per-rank remaps (L-295)
  match marginals only, and the input-only throttle of L-296 was not a test of `hpush` (L-302).
- That `hsem` holds for E3's throttling: throttling changes which copies are fresh, and the task meaning of a copy may
  depend on the traffic state; the theorem needs the garbled input to carry the same task information as the original.
- Knowledge-level statements (those are `LeanMarlReceiverFloorV1/V2`, `LeanMarlEmulationV1`) and Bayes-risk statements
  (`LeanMarlCommValueV1`).
-/

namespace CIGAMF.P13.MarlFrozenFloorV1

open Finset CIGAMF.P13.MarlSupportV1

/-! ## 1. Task feasibility is upward closed under refinement -/

/-- **Task feasibility is upward closed.**  If `obs` factors through `fine` (equal fine observations give equal coarse
observations), a policy acceptable in every world on `obs` lifts to one on `fine`. -/
theorem task_upward_closed {World Act O M : Type*} [Nonempty Act] (safe : World → Finset Act) (obs : World → O)
    (fine : World → M) (hfac : ∀ F G, fine F = fine G → obs F = obs G)
    (h : ∃ pol : O → Act, ∀ F, pol (obs F) ∈ safe F) :
    ∃ pol' : M → Act, ∀ F, pol' (fine F) ∈ safe F := by
  classical
  obtain ⟨pol, hpol⟩ := h
  refine ⟨fun l => if hl : ∃ G, fine G = l then pol (obs hl.choose) else Classical.arbitrary Act, fun F => ?_⟩
  have hex : ∃ G, fine G = fine F := ⟨F, rfl⟩
  dsimp only
  rw [dite_eq_left hex]
  show pol (obs hex.choose) ∈ safe F
  rw [hfac _ _ hex.choose_spec]
  exact hpol F

/-- The hypotheses of `task_upward_closed` are satisfiable (Bool worlds, identification, identity observations). -/
theorem task_upward_witness :
    (∀ F G : Bool, (id F : Bool) = id G → (id F : Bool) = id G) ∧
      ∃ pol : Bool → Bool, ∀ F : Bool, pol (id F) ∈ ({F} : Finset Bool) :=
  ⟨fun _ _ h => h, ⟨id, fun F => by simp⟩⟩

/-! ## 2. Emulation repairs a frozen receiver when the garbling reproduces the training JOINT law -/

/-- The law of `γ x` when `x ∼ Q` (pushforward on a finite input space). -/
noncomputable def pushLaw {X : Type*} [Fintype X] [DecidableEq X] (Q : X → ℝ) (γ : X → X) (y : X) : ℝ :=
  ∑ x, if γ x = y then Q x else 0

/-- **Emulation repairs exactly under two named hypotheses**: `hpush` (the garbling maps the deployment law EXACTLY onto
the training law, as a joint law on the whole input — the hypothesis that the E3 receiver-side garblings do not achieve,
ledger L-295 / L-296) and `hsem` (the garbling keeps the task meaning of the input).  Then the frozen receiver `r`
composed with the garbling has deployment risk equal to its training risk. -/
theorem emulation_repairs {X Y : Type*} [Fintype X] [DecidableEq X] (Q P : X → ℝ) (loss : X → Y → ℝ) (γ : X → X)
    (hpush : pushLaw Q γ = P) (hsem : ∀ x a, loss (γ x) a = loss x a) (r : X → Y) :
    risk Q loss (r ∘ γ) = risk P loss r := by
  rw [← hpush]
  unfold risk pushLaw
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (γ x)]
  · simp [hsem]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The emulated frozen receiver keeps the training optimum: if `r` is optimal on the training law, `r ∘ γ` attains the
training optimum on the deployment law (same hypotheses). -/
theorem emulation_keeps_training_optimum {X Y : Type*} [Fintype X] [DecidableEq X] (Q P : X → ℝ)
    (loss : X → Y → ℝ) (γ : X → X) (hpush : pushLaw Q γ = P) (hsem : ∀ x a, loss (γ x) a = loss x a) (r : X → Y)
    (hopt : ∀ r' : X → Y, risk P loss r ≤ risk P loss r') :
    ∀ r' : X → Y, risk Q loss (r ∘ γ) ≤ risk P loss r' := by
  intro r'
  rw [emulation_repairs Q P loss γ hpush hsem r]
  exact hopt r'

/-! ## 3. The `LeanMarlSupportV1` instance: the task floor is met, the frozen receiver fails, emulation repairs -/

/-- The garbling: a fresh copy `(m, 0)` is re-labelled as the equivalent one-step-old copy `(1 − m, 1)` (an old copy
reports the opposite of the current state); age-1 inputs are unchanged. -/
def gam (x : Fin 2 × Fin 2) : Fin 2 × Fin 2 := if x.2 = 0 then (1 - x.1, 1) else x

/-- The garbling preserves the current state everywhere. -/
theorem state_gam : ∀ x : Fin 2 × Fin 2, state (gam x) = state x := by decide

/-- Hence it preserves the task loss. -/
theorem loss01_gam (x : Fin 2 × Fin 2) (a : Fin 2) : loss01 (gam x) a = loss01 x a := by
  simp only [loss01, state_gam]

/-- The garbling maps the deployment law exactly onto the training law. -/
theorem push_gam : pushLaw Qdeploy gam = Ptrain := by
  funext y
  rcases y with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [pushLaw, gam, Qdeploy, Ptrain, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **The deployment channel Blackwell-dominates the training channel for this task**: the training input is a
state-preserving garbling of the deployment input. -/
theorem deploy_dominates_train :
    ∃ γ : Fin 2 × Fin 2 → Fin 2 × Fin 2, pushLaw Qdeploy γ = Ptrain ∧ ∀ x, state (γ x) = state x :=
  ⟨gam, push_gam, state_gam⟩

/-- Silence in training: the constant rule is wrong on half of the old copies. -/
theorem risk_train_silent : risk Ptrain loss01 silent = 1 / 2 := by
  norm_num [risk, Ptrain, loss01, silent, state, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **The frozen-receiver floor is not monotone in the channel; the task floor is; emulation repairs.** -/
theorem frozen_floor_not_monotone :
    -- the garbling preserves the task and maps the deployment law onto the training law
    (∀ x, state (gam x) = state x) ∧ pushLaw Qdeploy gam = Ptrain ∧
    -- the task floor is met on BOTH channels (some rule has risk 0)
    risk Ptrain loss01 f = 0 ∧ risk Qdeploy loss01 f = 0 ∧
    -- `g` is training-optimal and at least as good as silence in training
    risk Ptrain loss01 g = 0 ∧ (∀ r : Fin 2 × Fin 2 → Fin 2, 0 ≤ risk Ptrain loss01 r) ∧
    risk Ptrain loss01 g ≤ risk Ptrain loss01 silent ∧
    -- on the FRESHER deployment channel `g` is worse than silence
    risk Qdeploy loss01 g = 1 ∧ risk Qdeploy loss01 silent = 1 / 2 ∧
    risk Qdeploy loss01 silent < risk Qdeploy loss01 g ∧
    -- emulation repairs it exactly
    risk Qdeploy loss01 (g ∘ gam) = 0 := by
  obtain ⟨hf, hg, hnn, hqf, hqg, hqs⟩ := upgrade_hazard
  have hrep : risk Qdeploy loss01 (g ∘ gam) = risk Ptrain loss01 g :=
    emulation_repairs Qdeploy Ptrain loss01 gam push_gam loss01_gam g
  refine ⟨state_gam, push_gam, hf, hqf, hg, hnn, ?_, hqg, hqs, ?_, ?_⟩
  · rw [hg, risk_train_silent]; norm_num
  · rw [hqg, hqs]; norm_num
  · rw [hrep, hg]

/-! ## 4. The joint law is needed: matching every single-slot marginal is not enough -/

/-- Two slots (bits).  Training law: the slots agree (each pair with probability 1/2). -/
noncomputable def P2o (x : Fin 2 × Fin 2) : ℝ := if x.1 = x.2 then 1 / 2 else 0
/-- Deployment law: the slots disagree. -/
noncomputable def P2n (x : Fin 2 × Fin 2) : ℝ := if x.1 = x.2 then 0 else 1 / 2
/-- Single-slot marginals. -/
noncomputable def marg1 (P : Fin 2 × Fin 2 → ℝ) (a : Fin 2) : ℝ := ∑ b : Fin 2, P (a, b)
noncomputable def marg2 (P : Fin 2 × Fin 2 → ℝ) (b : Fin 2) : ℝ := ∑ a : Fin 2, P (a, b)
/-- The frozen receiver: predicts slot 2 from slot 1 (what the training joint law taught it). -/
def rho (x : Fin 2 × Fin 2) : Fin 2 := x.1
/-- Task: predict slot 2. -/
def lossB (x : Fin 2 × Fin 2) (y : Fin 2) : ℝ := if y = x.2 then 0 else 1
/-- The joint garbling: flip slot 1 (maps the deployment joint law onto the training joint law). -/
def gJ (x : Fin 2 × Fin 2) : Fin 2 × Fin 2 := (1 - x.1, x.2)

theorem lossB_gJ (x : Fin 2 × Fin 2) (a : Fin 2) : lossB (gJ x) a = lossB x a := by
  unfold lossB gJ
  rfl

theorem push_gJ : pushLaw P2n gJ = P2o := by
  funext y
  rcases y with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [pushLaw, gJ, P2n, P2o, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **Marginal matching is insufficient; the joint pushforward repairs.** -/
theorem marginal_match_insufficient :
    -- the two single-slot marginals of deployment and training agree, the joint laws differ
    marg1 P2n = marg1 P2o ∧ marg2 P2n = marg2 P2o ∧ P2n ≠ P2o ∧
    -- the frozen receiver is perfect in training and always wrong on the unchanged deployment channel
    risk P2o lossB rho = 0 ∧ risk P2n lossB rho = 1 ∧
    -- the joint garbling satisfies both hypotheses of `emulation_repairs` and repairs exactly
    pushLaw P2n gJ = P2o ∧ (∀ x a, lossB (gJ x) a = lossB x a) ∧ risk P2n lossB (rho ∘ gJ) = 0 := by
  have h1 : marg1 P2n = marg1 P2o := by
    funext a; fin_cases a <;> norm_num [marg1, P2o, P2n, Fin.sum_univ_two]
  have h2 : marg2 P2n = marg2 P2o := by
    funext b; fin_cases b <;> norm_num [marg2, P2o, P2n, Fin.sum_univ_two]
  have hne : P2n ≠ P2o := by
    intro h
    have := congrFun h (0, 0)
    norm_num [P2n, P2o] at this
  have hr0 : risk P2o lossB rho = 0 := by
    norm_num [risk, P2o, lossB, rho, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hr1 : risk P2n lossB rho = 1 := by
    norm_num [risk, P2n, lossB, rho, Fintype.sum_prod_type, Fin.sum_univ_two]
  refine ⟨h1, h2, hne, hr0, hr1, push_gJ, lossB_gJ, ?_⟩
  rw [emulation_repairs P2n P2o lossB gJ push_gJ lossB_gJ rho, hr0]

end CIGAMF.P13.MarlFrozenFloorV1

#print axioms CIGAMF.P13.MarlFrozenFloorV1.task_upward_closed
#print axioms CIGAMF.P13.MarlFrozenFloorV1.task_upward_witness
#print axioms CIGAMF.P13.MarlFrozenFloorV1.emulation_repairs
#print axioms CIGAMF.P13.MarlFrozenFloorV1.emulation_keeps_training_optimum
#print axioms CIGAMF.P13.MarlFrozenFloorV1.state_gam
#print axioms CIGAMF.P13.MarlFrozenFloorV1.push_gam
#print axioms CIGAMF.P13.MarlFrozenFloorV1.deploy_dominates_train
#print axioms CIGAMF.P13.MarlFrozenFloorV1.risk_train_silent
#print axioms CIGAMF.P13.MarlFrozenFloorV1.frozen_floor_not_monotone
#print axioms CIGAMF.P13.MarlFrozenFloorV1.push_gJ
#print axioms CIGAMF.P13.MarlFrozenFloorV1.marginal_match_insufficient
