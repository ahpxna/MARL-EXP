import «LeanD6AdaptiveOracleRegretV1»

/-! Deterministic tracking bridge for actual D6 information. Uniform finite
bounds imply an L1 allocation modulus and a raw-count rounding penalty. This
module does not assume a stochastic information-growth theorem. -/
namespace CIGAMF.P13.D6AllocationTrackingStability
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6GaussianQueryDominance
open CIGAMF.P13.D6MovingNuisanceRegret CIGAMF.P13.D6AllocationRiskBridge
open CIGAMF.P13.D6LocalOracleRegret
noncomputable section
variable {n : ℕ}

def informationCap (q : ℝ) := (q+2)^2/2

lemma actual_mean_interval (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (q mu : ℝ) (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (e : Measurement n) (he : Legal j q e) : -1 ≤ actualMean A j mu e ∧ actualMean A j mu e ≤ q+1 := by
  cases e with
  | inl i =>
    rw [actual_mean_affine A j hj q mu (.inl i) he]
    simp only [meanOffset,meanSlope]
    split_ifs <;> constructor <;> linarith
  | inr p =>
    change -1 ≤ world A j mu (query p.1 j p.2) ∧ world A j mu (query p.1 j p.2) ≤ q+1
    rw [actual_query_mean A p.1 j p.2 hj he.1 he.2.2]
    have hc0 : (0:ℝ) ≤ (p.1 ∩ others A j).card := by positivity
    have hc : ((p.1 ∩ others A j).card:ℝ) ≤ q :=
      (show ((p.1 ∩ others A j).card:ℝ) ≤ (p.1.card:ℝ) by
        exact_mod_cast card_le_card (inter_subset_left : p.1 ∩ others A j ⊆ p.1)).trans he.2.1
    have hnon := mul_nonneg (by linarith : 0 ≤ 1-mu) hc0
    have hup := mul_nonneg hm hc0
    cases p.2 <;> simp only [Bool.false_eq_true,↓reduceIte,bit_false,bit_true,sub_zero] <;>
      constructor <;> nlinarith

theorem actual_information_cap (A A' : Finset (I n)) (j : I n) (hj : j ∉ A) (hj' : j ∉ A')
    (q mu nu : ℝ) (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (hn : 0 ≤ nu) (hn1 : nu ≤ 1) (e : Measurement n) (he : Legal j q e) :
    |information A A' j mu nu e| ≤ informationCap q := by
  have h := actual_mean_interval A j hj q mu hq hm hm1 e he
  have h' := actual_mean_interval A' j hj' q nu hq hn hn1 e he
  have hb : |actualMean A j mu e-actualMean A' j nu e| ≤ q+2 := by
    apply abs_le.mpr;constructor <;> linarith
  have hs := (sq_le_sq₀ (abs_nonneg _) (by linarith : 0 ≤ q+2)).mpr hb
  rw [sq_abs] at hs
  rw [abs_of_nonneg (information_nonnegative _ _ _ _ _ _),information_eq_mean]
  unfold informationCap
  linarith

lemma value_nonempty (A : Finset (I n)) (j : I n)
    (halt : ∃ A' nu,Admissible A A' j nu) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) :
    (valueSet A j mu E w).Nonempty := by
  obtain ⟨A',nu,ha⟩ := halt
  exact ⟨_,A',nu,ha,rfl⟩

lemma allocation_one_sided (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (E : Finset (Measurement n)) (w v : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hv : ∀ e ∈ E,0 ≤ v e) :
    allocationValue A j mu E w ≤ allocationValue A j mu E v +
      informationCap q*(∑ e ∈ E,|w e-v e|) := by
  have hpoint (A' : Finset (I n)) (nu : ℝ) (ha : Admissible A A' j nu) :
      (∑ e ∈ E,w e*information A A' j mu nu e) ≤
      (∑ e ∈ E,v e*information A A' j mu nu e)+informationCap q*(∑ e ∈ E,|w e-v e|) := by
    have hb : (∑ e ∈ E,(w e-v e)*information A A' j mu nu e) ≤
        ∑ e ∈ E,|w e-v e| *informationCap q := by
      apply sum_le_sum
      intro e he
      calc
        _ ≤ |(w e-v e)*information A A' j mu nu e| := le_abs_self _
        _ = |w e-v e| *|information A A' j mu nu e| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (actual_information_cap A A' j hj ha.2.2.1 q mu nu hq hm hm1 ha.2.2.2.1 ha.2.2.2.2 e (hl e he)) (abs_nonneg _)
    simp only [sub_mul,sum_sub_distrib,← sum_mul] at hb
    rw [mul_comm] at hb
    linarith
  have hinf : allocationValue A j mu E w-informationCap q*(∑ e ∈ E,|w e-v e|) ≤
      allocationValue A j mu E v := by
    apply le_csInf (value_nonempty A j halt mu E v)
    rintro z ⟨A',nu,ha,rfl⟩
    have ha' := allocationValue_le_actual A A' j mu nu E w hw ha
    have hb := hpoint A' nu ha
    linarith
  linarith

theorem allocation_l1_modulus (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (E : Finset (Measurement n)) (w v : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hv : ∀ e ∈ E,0 ≤ v e) :
    |allocationValue A j mu E w-allocationValue A j mu E v| ≤
      informationCap q*(∑ e ∈ E,|w e-v e|) := by
  have h1 := allocation_one_sided A j hj halt q mu hq hm hm1 E w v hl hw hv
  have h2 := allocation_one_sided A j hj halt q mu hq hm hm1 E v w hl hv hw
  have he : (∑ e ∈ E,|v e-w e|)=∑ e ∈ E,|w e-v e| := sum_congr rfl (fun e _ => abs_sub_comm _ _)
  rw [he] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- If counts track an intended cumulative allocation within D per query,
its normalized information rate loses at most cap(q)*|E| *D/N. -/
theorem tracked_counts_regret (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) (counts : Measurement n → ℕ)
    (N : ℕ) (hN : 0 < N) (D : ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e)
    (htrack : ∀ e ∈ E, |(counts e:ℝ)-(N:ℝ)*w e| ≤ D) :
    oracleRegret A j q mu E (fun e => (counts e:ℝ)/(N:ℝ)) ≤
      oracleRegret A j q mu E w+informationCap q*(E.card:ℝ)*D/(N:ℝ) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have h1 := allocation_one_sided A j hj halt q mu hq hm hm1 E w
    (fun e => (counts e:ℝ)/(N:ℝ)) hl hw (fun e _ => by positivity)
  have hsum : (∑ e ∈ E,|w e-(counts e:ℝ)/(N:ℝ)|) ≤ (E.card:ℝ)*D/(N:ℝ) := by
    calc
      _ ≤ ∑ _e ∈ E,D/(N:ℝ) := by
        apply sum_le_sum;intro e he
        have h := (div_le_div_of_nonneg_right (htrack e he) hNp.le)
        have hid : |w e-(counts e:ℝ)/(N:ℝ)|=|(counts e:ℝ)-(N:ℝ)*w e|/(N:ℝ) := by
          have heq : w e-(counts e:ℝ)/(N:ℝ) = -(((counts e:ℝ)-(N:ℝ)*w e)/(N:ℝ)) := by field_simp;ring
          rw [heq,abs_neg,abs_div,abs_of_pos hNp]
        rw [hid]
        exact h
      _ = _ := by simp;ring
  have hcap : 0 ≤ informationCap q := by unfold informationCap;positivity
  have hb := mul_le_mul_of_nonneg_left hsum hcap
  have halg : informationCap q*((E.card:ℝ)*D/(N:ℝ))=informationCap q*(E.card:ℝ)*D/(N:ℝ) := by ring
  rw [halg] at hb
  have hD : 0 ≤ informationCap q*(E.card:ℝ)*D/(N:ℝ) := by
    have hn := sum_nonneg (fun e (_ : e ∈ E) => abs_nonneg (w e-(counts e:ℝ)/(N:ℝ)))
    have hz : 0 ≤ (E.card:ℝ)*D/(N:ℝ) := hn.trans hsum
    have hh := mul_nonneg (by unfold informationCap;positivity : 0 ≤ informationCap q) hz
    simpa only [mul_div_assoc,mul_assoc] using hh
  unfold oracleRegret
  apply max_le
  · exact add_nonneg (le_max_left _ _) hD
  · have hh := le_max_right (0:ℝ) (oracleValue A j q mu-allocationValue A j mu E w)
    nlinarith only [h1,hb,hh]

#print axioms actual_mean_interval
#print axioms actual_information_cap
#print axioms allocation_l1_modulus
#print axioms tracked_counts_regret
end
end CIGAMF.P13.D6AllocationTrackingStability
