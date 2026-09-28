import «LeanD6ThresholdConstructionV1»

/-! Literal support sets in a fixed real coordinate space. The coordinate
functions are projections, independent of A. Only the support set changes.
The interaction coordinate `none` is always omitted from feasible selections. -/
namespace CIGAMF.P13.D6Geometry
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold
open CIGAMF.V4.SupportGeometry CIGAMF.V4.ProductMixedDifference
variable {n : ℕ}

noncomputable def supportSet (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ) :
    Finset (Option (I n) → ℝ) := Finset.univ.image (supportPoint F Q)

abbrev Geometry (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ) :=
  {z // z ∈ supportSet F Q}

noncomputable def embed (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ)
    (x : I n → Bool) : Geometry F Q :=
  ⟨supportPoint F Q x, mem_image.mpr ⟨x, mem_univ _, rfl⟩⟩

instance (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ) : Nonempty (Geometry F Q) :=
  ⟨embed F Q zero⟩

/-- The same ambient linear projection is used for every possible support. -/
def projection (i : Option (I n)) (z : Option (I n) → ℝ) : ℝ := z i

def restrictedProjection (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ)
    (i : Option (I n)) (z : Geometry F Q) : ℝ := projection i z.val

theorem embed_surjective (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ) :
    Function.Surjective (embed F Q) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, _, hx⟩ := mem_image.mp hz
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

theorem osc_pullback {Ω Θ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Θ] [Nonempty Θ]
    (f : Θ → ℝ) (g : Ω → Θ) (hg : Function.Surjective g) :
    osc (fun x => f (g x)) = osc f := by
  have hmax : maxVal (fun x => f (g x)) = maxVal f := by
    apply le_antisymm
    · exact maxVal_le _ (fun x => le_maxVal f (g x))
    · apply maxVal_le
      intro y
      obtain ⟨x, rfl⟩ := hg y
      exact le_maxVal (fun x => f (g x)) x
  have hmin : minVal (fun x => f (g x)) = minVal f := by
    apply le_antisymm
    · apply le_minVal
      intro y
      obtain ⟨x, rfl⟩ := hg y
      exact minVal_le (fun x => f (g x)) x
    · exact le_minVal _ (fun x => minVal_le f (g x))
  simp [osc, hmax, hmin]

/-- The old loss is the radius on an actual finite subset of real space,
using fixed ambient coordinate functions. Repeated indexed states are removed
by taking an image; surjectivity proves this does not change any extrema. -/
theorem actual_geometric_radius (F : (I n → Bool) → ℝ) (Q : I n → Bool → ℝ)
    (S : Finset (I n)) :
    selectedRadius (restrictedProjection F Q) (liftedSelection S) =
      productCompressionLoss F Q S := by
  rw [← actual_support_bridge F Q S]
  unfold selectedRadius supportOsc
  congr 1
  rw [← osc_pullback (sumComponent (liftedSelection S)ᶜ (restrictedProjection F Q))
    (embed F Q) (embed_surjective F Q)]
  rfl

/-- In the indistinguishable D6 family, projection to all observed coordinates
has exactly the same geometric image; only the omitted coordinate varies. -/
theorem observed_support_image (A A' : Finset (I n)) (j : I n)
    (hj : j ∉ A) (hj' : j ∉ A') :
    (supportSet (world A j 0) (productResponse corner (world A j 0))).image
      (fun z => fun i : I n => z (some i)) =
    (supportSet (world A' j 0) (productResponse corner (world A' j 0))).image
      (fun z => fun i : I n => z (some i)) := by
  classical
  simp only [supportSet, image_image]
  congr 1
  funext x i
  exact support_observed_coordinates_equal A A' j hj hj' x i


/-- Same randomized information lower bound, now for literal support geometry
and fixed ambient projections, with the original cardinality constraint. -/
theorem geometric_randomized_lower (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (p : Finset (I (2*r+1)) → ℝ)
    (hp : ∀ S ∈ actions r, 0 ≤ p S) (hnorm : ∑ S ∈ actions r, p S = 1) :
    ∃ A ∈ worlds r j,
      (r : ℝ)*(r+1)/(2*r+1) ≤ ∑ S ∈ actions r, p S *
        (selectedRadius (restrictedProjection (world A j 0)
          (productResponse corner (world A j 0))) (liftedSelection S) -
         selectedRadius (restrictedProjection (world A j 0)
          (productResponse corner (world A j 0))) (liftedSelection Aᶜ)) := by
  simp_rw [actual_geometric_radius]
  exact randomized_actual_lower r j hr p hp hnorm

#print axioms actual_geometric_radius
#print axioms observed_support_image
#print axioms geometric_randomized_lower
end CIGAMF.P13.D6Geometry
