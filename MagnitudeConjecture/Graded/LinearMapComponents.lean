import MagnitudeConjecture.Graded.FiniteVectorGrading

/-!
# Homogeneous components of linear maps

For an internally graded finite-dimensional source, each degree component
of a linear map is a finite sum of source and target projections.
-/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace MagnitudeConjecture.Graded.VectorGrading

variable {k M N : Type*} [Field k]
variable [AddCommGroup M] [Module k M] [FiniteDimensional k M]
variable [AddCommGroup N] [Module k N]
variable (G : VectorGrading k M) (H : VectorGrading k N)

/-- The degree `d` part of a linear map. -/
def mapPart (d : ℤ) (f : M →ₗ[k] N) : M →ₗ[k] N :=
  ∑ i ∈ G.degreeSupport, (H.projection (i + d)).comp (f.comp (G.projection i))

/-- On a vector of degree `i`, the component takes the target projection
in degree `i+d`. -/
theorem mapPart_apply_of_mem (d : ℤ) (f : M →ₗ[k] N)
    {i : ℤ} {x : M} (hx : x ∈ G.component i) :
    G.mapPart H d f x = H.projection (i + d) (f x) := by
  classical
  change (∑ j ∈ G.degreeSupport,
    (H.projection (j + d)).comp (f.comp (G.projection j))) x = _
  rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply]
  calc
    _ = H.projection (i + d) (f (G.projection i x)) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        rw [G.projection_of_mem_ne hx hji.symm, map_zero, map_zero]
      · intro hi
        rw [G.projection_eq_zero_outside hi]
        simp
    _ = _ := by rw [G.projection_of_mem hx]

theorem mapPart_mem (d : ℤ) (f : M →ₗ[k] N)
    {i : ℤ} {x : M} (hx : x ∈ G.component i) :
    G.mapPart H d f x ∈ H.component (i + d) := by
  rw [G.mapPart_apply_of_mem H d f hx]
  exact H.projection_mem _ _

variable [FiniteDimensional k N]

/-- The possible degrees of a map are target degrees minus source degrees. -/
def mapDegreeSupport : Finset ℤ :=
  G.degreeSupport.biUnion fun i ↦ H.degreeSupport.image (fun j ↦ j - i)

theorem mapPart_eq_zero_outside (d : ℤ) (f : M →ₗ[k] N)
    (hd : d ∉ G.mapDegreeSupport H) : G.mapPart H d f = 0 := by
  classical
  apply LinearMap.ext
  intro x
  simp only [mapPart, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hout : i + d ∉ H.degreeSupport := by
    intro hj
    apply hd
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, Finset.mem_image.mpr ⟨i + d, hj, ?_⟩⟩
    omega
  rw [H.projection_eq_zero_outside hout]
  rfl

theorem sum_shifted_projections (i : ℤ) (hi : i ∈ G.degreeSupport) (y : N) :
    ∑ d ∈ G.mapDegreeSupport H, H.projection (i + d) y = y := by
  classical
  have hinj : Set.InjOn (fun d : ℤ ↦ i + d) (G.mapDegreeSupport H) := by
    intro d _ e _ hde
    exact add_left_cancel hde
  have hsub : H.degreeSupport ⊆ (G.mapDegreeSupport H).image (fun d ↦ i + d) := by
    intro j hj
    apply Finset.mem_image.mpr
    refine ⟨j - i, ?_, by omega⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  calc
    _ = ∑ j ∈ (G.mapDegreeSupport H).image (fun d ↦ i + d), H.projection j y :=
      (Finset.sum_image hinj).symm
    _ = ∑ j ∈ H.degreeSupport, H.projection j y := by
      symm
      apply Finset.sum_subset hsub
      intro j _ hj
      rw [H.projection_eq_zero_outside hj]
      rfl
    _ = y := H.sum_projection y

/-- The finite homogeneous components reconstruct every linear map. -/
theorem sum_mapPart (f : M →ₗ[k] N) :
    ∑ d ∈ G.mapDegreeSupport H, G.mapPart H d f = f := by
  classical
  apply LinearMap.ext
  intro x
  simp only [mapPart, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i ∈ G.degreeSupport, f (G.projection i x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact G.sum_shifted_projections H i hi _
    _ = f (∑ i ∈ G.degreeSupport, G.projection i x) := (map_sum _ _ _).symm
    _ = f x := by rw [G.sum_projection x]

end MagnitudeConjecture.Graded.VectorGrading
