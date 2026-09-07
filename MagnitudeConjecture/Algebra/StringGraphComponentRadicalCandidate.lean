import MagnitudeConjecture.Algebra.StringGraphComponentComposition

/-!
# The proper-component subspace of a string endomorphism ring

The graph-component basis splits into the diagonal identity component and the
remaining proper self-overlap components.  This file packages the span of the
proper components and identifies it with the kernel of the diagonal basis
coordinate.  Closure under multiplication and nilpotence remain separate
combinatorial obligations.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Boundary-free self-components other than the diagonal component. -/
def ProperBoundaryFreeMorphismCoefficientComponent
    (C : Word R) :=
  {component : C.BoundaryFreeMorphismCoefficientComponent C //
    component.1 ≠ C.diagonalMorphismCoefficientComponent}

instance properBoundaryFreeMorphismCoefficientComponent_finite
    (C : Word R) :
    Finite (C.ProperBoundaryFreeMorphismCoefficientComponent) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance properBoundaryFreeMorphismCoefficientComponent_fintype
    (C : Word R) :
    Fintype (C.ProperBoundaryFreeMorphismCoefficientComponent) :=
  Fintype.ofFinite _

/-- The endomorphism carried by one proper self-component. -/
def properBoundaryFreeMorphismCoefficientComponentMap
    (C : Word R) (hmono : IsMonomial R)
    (component : C.ProperBoundaryFreeMorphismCoefficientComponent) :
    C.rightModule hmono ⟶ C.rightModule hmono :=
  C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono component.1

/-- The scalar coordinate in the diagonal graph-component direction. -/
def diagonalMorphismCoefficientLinearMap
    (C : Word R) (hmono : IsMonomial R) :
    (C.rightModule hmono ⟶ C.rightModule hmono) →ₗ[k] k where
  toFun f := C.morphismCoefficientAt C hmono hmono f
    C.diagonalMorphismCoefficientComponent.representative
  map_add' f g := C.morphismCoefficientAt_add C hmono hmono f g
    C.diagonalMorphismCoefficientComponent.representative
  map_smul' c f := C.morphismCoefficientAt_smul C hmono hmono c f
    C.diagonalMorphismCoefficientComponent.representative

@[simp]
theorem diagonalMorphismCoefficientLinearMap_apply
    (C : Word R) (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ C.rightModule hmono) :
    C.diagonalMorphismCoefficientLinearMap hmono f =
      C.morphismCoefficientAt C hmono hmono f
        C.diagonalMorphismCoefficientComponent.representative :=
  rfl

/-- The diagonal coordinate sends the identity to one. -/
@[simp]
theorem diagonalMorphismCoefficientLinearMap_id
    (C : Word R) (hmono : IsMonomial R) :
    C.diagonalMorphismCoefficientLinearMap hmono
        (𝟙 (C.rightModule hmono)) = 1 :=
  C.morphismCoefficientAt_id_diagonalComponent_representative hmono

/-- Every proper component map lies in the kernel of the diagonal
coordinate. -/
theorem diagonalMorphismCoefficientLinearMap_properComponentMap
    (C : Word R) (hmono : IsMonomial R)
    (component : C.ProperBoundaryFreeMorphismCoefficientComponent) :
    C.diagonalMorphismCoefficientLinearMap hmono
        (C.properBoundaryFreeMorphismCoefficientComponentMap
          hmono component) = 0 := by
  rw [C.diagonalMorphismCoefficientLinearMap_apply,
    C.morphismCoefficientAt_diagonalComponent_representative_eq_source]
  exact C.morphismCoefficientAt_boundaryFreeComponentMap_diagonal_eq_zero
    hmono component.1 component.2 C.sourcePosition

/-- The candidate radical: the span of all proper self-component maps. -/
def properMorphismCoefficientComponentSubspace
    (C : Word R) (hmono : IsMonomial R) :
    Submodule k (C.rightModule hmono ⟶ C.rightModule hmono) :=
  Submodule.span k
    (Set.range (C.properBoundaryFreeMorphismCoefficientComponentMap hmono))

/-- The proper-component span is contained in the kernel of the diagonal
coordinate. -/
theorem properMorphismCoefficientComponentSubspace_le_ker
    (C : Word R) (hmono : IsMonomial R) :
    C.properMorphismCoefficientComponentSubspace hmono ≤
      LinearMap.ker (C.diagonalMorphismCoefficientLinearMap hmono) := by
  apply Submodule.span_le.mpr
  rintro f ⟨component, rfl⟩
  change C.diagonalMorphismCoefficientLinearMap hmono
      (C.properBoundaryFreeMorphismCoefficientComponentMap
        hmono component) = 0
  exact C.diagonalMorphismCoefficientLinearMap_properComponentMap
    hmono component

/-- A zero diagonal graph coordinate is a linear combination of proper
self-component maps. -/
theorem mem_properMorphismCoefficientComponentSubspace_of_diagonal_eq_zero
    (C : Word R) (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ C.rightModule hmono)
    (hf : C.diagonalMorphismCoefficientLinearMap hmono f = 0) :
    f ∈ C.properMorphismCoefficientComponentSubspace hmono := by
  classical
  let b := C.boundaryFreeMorphismCoefficientBasis C hmono hmono
  rw [← b.sum_repr f]
  apply Submodule.sum_mem
  intro component _
  by_cases hdiag : component.1 = C.diagonalMorphismCoefficientComponent
  · have hcomponent :
        component = C.diagonalBoundaryFreeMorphismCoefficientComponent hmono := by
      apply Subtype.ext
      exact hdiag
    subst component
    have hcoord :
        b.repr f (C.diagonalBoundaryFreeMorphismCoefficientComponent hmono) =
          0 := by
      rw [C.boundaryFreeMorphismCoefficientBasis_repr_apply]
      exact hf
    rw [hcoord, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨(⟨component, hdiag⟩ :
      C.ProperBoundaryFreeMorphismCoefficientComponent), ?_⟩
    simp only [properBoundaryFreeMorphismCoefficientComponentMap]
    exact Module.Basis.mk_apply _ _ component |>.symm

/-- The proper-component span is exactly the kernel of the diagonal basis
coordinate. -/
theorem properMorphismCoefficientComponentSubspace_eq_ker
    (C : Word R) (hmono : IsMonomial R) :
    C.properMorphismCoefficientComponentSubspace hmono =
      LinearMap.ker (C.diagonalMorphismCoefficientLinearMap hmono) := by
  apply le_antisymm
  · exact C.properMorphismCoefficientComponentSubspace_le_ker hmono
  · intro f hf
    exact C.mem_properMorphismCoefficientComponentSubspace_of_diagonal_eq_zero
      hmono f hf

/-- Every string endomorphism is its diagonal scalar times the identity plus
a member of the proper-component subspace. -/
theorem exists_eq_smul_id_add_mem_properComponentSubspace
    (C : Word R) (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ C.rightModule hmono) :
    ∃ r ∈ C.properMorphismCoefficientComponentSubspace hmono,
      f = C.diagonalMorphismCoefficientLinearMap hmono f •
          𝟙 (C.rightModule hmono) + r := by
  let c := C.diagonalMorphismCoefficientLinearMap hmono f
  let r := f - c • 𝟙 (C.rightModule hmono)
  refine ⟨r, ?_, ?_⟩
  · rw [C.properMorphismCoefficientComponentSubspace_eq_ker]
    change C.diagonalMorphismCoefficientLinearMap hmono r = 0
    rw [show r = f - c • 𝟙 (C.rightModule hmono) by rfl,
      map_sub, map_smul, C.diagonalMorphismCoefficientLinearMap_id]
    simp [c]
  · simp [r, c]

end MagnitudeConjecture.BoundQuiver.StringWord.Word
