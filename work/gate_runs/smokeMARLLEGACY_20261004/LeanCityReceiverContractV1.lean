import Mathlib
import LeanMarlSupportV1

/-!
# Compatibility is receiver-relative and may be higher-order (city track, 02/10/2026 23:0x EDT)

research/papers/audits/CITY_TWO_POPULATION_NOVELTY_20261002.md §7 (two external reviews, verified): targets T1 and T3.

## WHAT IS PROVED
* `no_receiver_free_certificate` (T1) — no verdict computed from the partner / channel distributions alone (the training law
  `Ptrain` and the deployment law `Qdeploy` of `LeanMarlSupportV1`) can say, for every training-optimal frozen receiver,
  whether the upgrade makes it worse than silence: the two training-optimal receivers `f` and `g` of `upgrade_hazard` face the
  same pair of laws and get opposite answers.  A corollary of `LeanMarlSupportV1.upgrade_hazard`, nothing more.
* `order1_blind_pair` (T3, s = 2: the Q4 shape) — an update of a two-component system that leaves BOTH single-component laws
  unchanged turns the frozen receiver's risk from 0 into 1 (silence: 1/2 under both); every order-1 certificate (any function
  of the component marginals) returns the same verdict before and after, while the pair law changes completely.
* `order2_blind_triple` (T3, s = 3) — the same with three components: all THREE pair laws are unchanged, the triple law flips
  parity, the frozen receiver (which learned "b₃ = b₁ xor b₂") goes from risk 0 to risk 1.  So the interaction order a
  compatibility certificate must inspect (s_compat) can exceed 2: pairwise certification is not sufficient in general.

## WHAT THIS DOES NOT ESTABLISH
- That the trained SUMO / CityFlow components realise these instances (Q4 is the empirical s = 2 witness; no s = 3 witness
  has been run).  The parity construction is the classical k-wise-independence example (cf. t-way interaction testing in
  software, Kuhn & Wallace); the content here is only its reading as a compatibility statement for frozen learned receivers.
- Anything about how large a sufficient contract must be in general (no upper bound on s_compat is proved).
-/

namespace CIGAMF.P13.CityReceiverContractV1

open Finset CIGAMF.P13.MarlSupportV1

/-- the upgrade harms receiver r: worse than the silent rule on the deployment law -/
def harmed (r : Fin 2 × Fin 2 → Fin 2) : Prop := risk Qdeploy loss01 silent < risk Qdeploy loss01 r

/-- T1.  Any proposition `K Ptrain Qdeploy` (a certificate that sees only the two laws) cannot equal `harmed r` for both
training-optimal receivers `f` and `g`. -/
theorem no_receiver_free_certificate (K : ((Fin 2 × Fin 2) → ℝ) → ((Fin 2 × Fin 2) → ℝ) → Prop) :
    risk Ptrain loss01 f = 0 ∧ risk Ptrain loss01 g = 0 ∧
    ¬ ((K Ptrain Qdeploy ↔ harmed f) ∧ (K Ptrain Qdeploy ↔ harmed g)) := by
  obtain ⟨hf, hg, _, hqf, hqg, hqs⟩ := upgrade_hazard
  refine ⟨hf, hg, fun ⟨h1, h2⟩ => ?_⟩
  have nf : ¬ harmed f := by unfold harmed; rw [hqf, hqs]; norm_num
  have yg : harmed g := by unfold harmed; rw [hqg, hqs]; norm_num
  exact nf (h1.mp (h2.mpr yg))

/-! ### T3, s = 2: two components, a bit each (e.g. the offset of each light of a corridor) -/

/-- before: the two bits agree (coordinated corridor) -/
noncomputable def P2old (x : Fin 2 × Fin 2) : ℝ := if x.1 = x.2 then 1 / 2 else 0
/-- after: the two bits disagree (one light re-timed against the other) -/
noncomputable def P2new (x : Fin 2 × Fin 2) : ℝ := if x.1 = x.2 then 0 else 1 / 2
/-- marginal laws of each component -/
noncomputable def marg1 (P : Fin 2 × Fin 2 → ℝ) (a : Fin 2) : ℝ := ∑ b : Fin 2, P (a, b)
noncomputable def marg2 (P : Fin 2 × Fin 2 → ℝ) (b : Fin 2) : ℝ := ∑ a : Fin 2, P (a, b)
/-- the frozen receiver: predicts the second bit from the first (it learned the coordination) -/
def rho2 (x : Fin 2 × Fin 2) : Fin 2 := x.1
/-- 0-1 loss on predicting the second bit -/
def loss2 (x : Fin 2 × Fin 2) (y : Fin 2) : ℝ := if y = x.2 then 0 else 1
def silent2 (_ : Fin 2 × Fin 2) : Fin 2 := 0

theorem order1_blind_pair :
    marg1 P2old = marg1 P2new ∧ marg2 P2old = marg2 P2new ∧
    risk P2old loss2 rho2 = 0 ∧ risk P2new loss2 rho2 = 1 ∧
    risk P2old loss2 silent2 = 1 / 2 ∧ risk P2new loss2 silent2 = 1 / 2 ∧
    (∀ C : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop, (C (marg1 P2old) (marg2 P2old) ↔ C (marg1 P2new) (marg2 P2new))) := by
  have h1 : marg1 P2old = marg1 P2new := by
    funext a; fin_cases a <;> norm_num [marg1, P2old, P2new, Fin.sum_univ_two]
  have h2 : marg2 P2old = marg2 P2new := by
    funext b; fin_cases b <;> norm_num [marg2, P2old, P2new, Fin.sum_univ_two]
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, fun C => by rw [h1, h2]⟩
  · norm_num [risk, P2old, loss2, rho2, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [risk, P2new, loss2, rho2, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [risk, P2old, loss2, silent2, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [risk, P2new, loss2, silent2, Fintype.sum_prod_type, Fin.sum_univ_two]

/-! ### T3, s = 3: three components; every pair law unchanged, the triple flips parity -/

/-- parity of three bits as a natural number mod 2 -/
def par3 (x : Fin 2 × Fin 2 × Fin 2) : ℕ := (x.1.val + x.2.1.val + x.2.2.val) % 2
noncomputable def P3old (x : Fin 2 × Fin 2 × Fin 2) : ℝ := if par3 x = 0 then 1 / 4 else 0
noncomputable def P3new (x : Fin 2 × Fin 2 × Fin 2) : ℝ := if par3 x = 0 then 0 else 1 / 4
/-- the three pair laws -/
noncomputable def m12 (P : Fin 2 × Fin 2 × Fin 2 → ℝ) (a b : Fin 2) : ℝ := ∑ c : Fin 2, P (a, b, c)
noncomputable def m13 (P : Fin 2 × Fin 2 × Fin 2 → ℝ) (a c : Fin 2) : ℝ := ∑ b : Fin 2, P (a, b, c)
noncomputable def m23 (P : Fin 2 × Fin 2 × Fin 2 → ℝ) (b c : Fin 2) : ℝ := ∑ a : Fin 2, P (a, b, c)
/-- the frozen receiver: predicts the third bit as the xor of the first two (what the old joint law taught it) -/
def rho3 (x : Fin 2 × Fin 2 × Fin 2) : Fin 2 := ⟨(x.1.val + x.2.1.val) % 2, Nat.mod_lt _ (by norm_num)⟩
def loss3 (x : Fin 2 × Fin 2 × Fin 2) (y : Fin 2) : ℝ := if y = x.2.2 then 0 else 1

theorem order2_blind_triple :
    m12 P3old = m12 P3new ∧ m13 P3old = m13 P3new ∧ m23 P3old = m23 P3new ∧
    risk P3old loss3 rho3 = 0 ∧ risk P3new loss3 rho3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext a b; fin_cases a <;> fin_cases b <;> norm_num [m12, P3old, P3new, par3, Fin.sum_univ_two]
  · funext a c; fin_cases a <;> fin_cases c <;> norm_num [m13, P3old, P3new, par3, Fin.sum_univ_two]
  · funext b c; fin_cases b <;> fin_cases c <;> norm_num [m23, P3old, P3new, par3, Fin.sum_univ_two]
  · simp only [risk, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num [P3old, loss3, rho3, par3, Fin.ext_iff]
  · simp only [risk, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num [P3new, loss3, rho3, par3, Fin.ext_iff]

end CIGAMF.P13.CityReceiverContractV1

#print axioms CIGAMF.P13.CityReceiverContractV1.no_receiver_free_certificate
#print axioms CIGAMF.P13.CityReceiverContractV1.order1_blind_pair
#print axioms CIGAMF.P13.CityReceiverContractV1.order2_blind_triple
