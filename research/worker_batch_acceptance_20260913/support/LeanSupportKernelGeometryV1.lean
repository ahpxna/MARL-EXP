import «LeanSupportGeometryV4»

/-! A kernel realized by actual support points and coordinate components.
Column separation and nonzero columns are explicit, checkable kernel premises. -/
namespace CIGAMF.P13.SupportKernelGeometry
open Finset
open scoped BigOperators
open CIGAMF.V4.SupportGeometry
noncomputable section
variable {m : ℕ}

def center (phi : Fin m → Fin m → ℝ) (w : Fin m) := (∑ j,phi j w)/((m:ℝ)-1)
def tip (phi : Fin m → Fin m → ℝ) (w : Fin m) (j : Fin m) := center phi w-phi j w

def support (phi : Fin m → Fin m → ℝ) (W : Finset (Fin m)) : Finset (Fin m → ℝ) :=
  insert 0 (W.image (tip phi))
abbrev Points (W : Finset (Fin m)) := Option {w // w ∈ W}
def point (phi : Fin m → Fin m → ℝ) (W : Finset (Fin m)) : Points W → (Fin m → ℝ)
  | none => 0
  | some w => tip phi w.val
def components (phi : Fin m → Fin m → ℝ) (W : Finset (Fin m)) (j : Fin m) (x : Points W) := point phi W x j

lemma total_tip (hm : 2 ≤ m) (phi : Fin m → Fin m → ℝ) (w : Fin m) :
    (∑ j,tip phi w j)=center phi w := by
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  simp only [tip,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,center]
  field_simp [show (m:ℝ)-1 ≠ 0 by linarith]
  <;> ring

/-- The intended kernel is recovered exactly by discarding every coordinate
except j, rather than being assumed as an abstract geometry contract. -/
theorem kernel_residual (hm : 2 ≤ m) (phi : Fin m → Fin m → ℝ) (w j : Fin m) :
    (∑ i ∈ univ.erase j,tip phi w i)=phi j w := by
  rw [sum_erase_eq_sub (mem_univ j),total_tip hm]
  unfold tip
  ring

lemma residual_none (phi : Fin m → Fin m → ℝ) (W : Finset (Fin m)) (j : Fin m) :
    sumComponent ({j}ᶜ) (components phi W) none=0 := by simp [sumComponent,components,point]
lemma residual_some (hm : 2 ≤ m) (phi : Fin m → Fin m → ℝ)
    (W : Finset (Fin m)) (w : {w // w ∈ W}) (j : Fin m) :
    sumComponent ({j}ᶜ) (components phi W) (some w)=phi j w.val := by
  have he : ({j}ᶜ : Finset (Fin m))=univ.erase j := by ext i;simp [eq_comm]
  simp only [sumComponent,components,point,he]
  exact kernel_residual hm phi w.val j

theorem kernel_radius (hm : 2 ≤ m) (phi : Fin m → Fin m → ℝ) (hphi : ∀ j w,0 ≤ phi j w)
    (W : Finset (Fin m)) (j : Fin m) :
    selectedRadius (components phi W) {j}=
      maxVal (fun x : Points W => match x with | none => 0 | some w => phi j w.val)/2 := by
  let f := sumComponent ({j}ᶜ) (components phi W)
  have hn : minVal f=0 := by
    apply le_antisymm
    · simpa [f,residual_none] using minVal_le f none
    · apply le_minVal
      intro x
      cases x with
      | none => simp [f,residual_none]
      | some w => simpa [f,residual_some hm] using hphi j w.val
  change (maxVal f-minVal f)/2=_
  rw [hn,sub_zero]
  congr 2
  funext x
  cases x with
  | none => exact residual_none phi W j
  | some w => exact residual_some hm phi W w j

/-- Empty supports and constant kernels are not discarded. -/
theorem kernel_radius_le_iff (hm : 2 ≤ m) (phi : Fin m → Fin m → ℝ)
    (hphi : ∀ j w,0 ≤ phi j w) (W : Finset (Fin m)) (j : Fin m) (eps : ℝ) (heps : 0 ≤ eps) :
    selectedRadius (components phi W) {j} ≤ eps ↔ ∀ w ∈ W,phi j w ≤ 2*eps := by
  rw [kernel_radius hm phi hphi]
  rw [div_le_iff₀ (by norm_num : (0:ℝ)<2)]
  constructor
  · intro h w hw
    have hh := le_maxVal (fun x : Points W => match x with | none => (0:ℝ) | some w => phi j w.val) (some ⟨w,hw⟩)
    dsimp only at hh
    linarith
  · intro h
    apply maxVal_le
    intro x
    cases x with
    | none => dsimp;linarith
    | some w => dsimp;have := h w.val w.property;linarith

/-- Residual recovery turns column separation into physical point injection. -/
theorem tip_injective (hm : 2 ≤ m) (phi : Fin m → Fin m → ℝ)
    (hsep : Function.Injective (fun w => fun j => phi j w)) : Function.Injective (tip phi) := by
  intro w v he
  apply hsep
  funext j
  have h := congrArg (fun p : Fin m → ℝ => ∑ i ∈ univ.erase j,p i) he
  simpa only [kernel_residual hm] using h

lemma tip_ne_zero (hm : 2 ≤ m) (phi : Fin m → Fin m → ℝ)
    (hnon : ∀ w,∃ j,phi j w ≠ 0) (w : Fin m) : tip phi w ≠ 0 := by
  intro he
  obtain ⟨j,hj⟩ := hnon w
  have h := congrArg (fun p : Fin m → ℝ => ∑ i ∈ univ.erase j,p i) he
  simp only [kernel_residual hm,Pi.zero_apply,sum_const_zero] at h
  exact hj h

/-- Membership at the actual point tip(a) returns exactly the bit a in W. -/
theorem physical_membership_iff (hm : 2 ≤ m) (phi : Fin m → Fin m → ℝ)
    (hsep : Function.Injective (fun w => fun j => phi j w))
    (hnon : ∀ w,∃ j,phi j w ≠ 0) (W : Finset (Fin m)) (a : Fin m) :
    tip phi a ∈ support phi W ↔ a ∈ W := by
  simp only [support,mem_insert,mem_image]
  constructor
  · rintro (h | ⟨w,hw,he⟩)
    · exact False.elim (tip_ne_zero hm phi hnon a h)
    · exact tip_injective hm phi hsep he ▸ hw
  · intro h
    exact Or.inr ⟨a,h,rfl⟩

#print axioms kernel_residual
#print axioms kernel_radius
#print axioms kernel_radius_le_iff
#print axioms tip_injective
#print axioms physical_membership_iff
end
end CIGAMF.P13.SupportKernelGeometry
