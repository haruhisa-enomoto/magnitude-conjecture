import MagnitudeConjecture.Algebra.StringGraphComponentSpanning

/-!
# The diagonal component of the string endomorphism basis

For a self-word, all diagonal coefficient positions lie in one component.
This file identifies the corresponding component-indicator map with the
identity endomorphism and proves that every other boundary-free component map
has zero diagonal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Every diagonal coefficient of the identity is one. -/
@[simp]
theorem morphismCoefficientAt_id_diagonal
    (C : Word R) (hmono : IsMonomial R)
    {x : Q} (i : C.PositionAt x) :
    C.morphismCoefficientAt C hmono hmono
        (𝟙 (C.rightModule hmono))
        (C.diagonalMorphismCoefficientPosition i) = 1 := by
  change (Finsupp.single i 1 : C.Space x) i = 1
  exact Finsupp.single_eq_same

/-- An off-diagonal coefficient of the identity is zero. -/
theorem morphismCoefficientAt_id_eq_zero_of_ne
    (C : Word R) (hmono : IsMonomial R)
    {x : Q} (i j : C.PositionAt x) (hij : i ≠ j) :
    C.morphismCoefficientAt C hmono hmono
        (𝟙 (C.rightModule hmono))
        (⟨x, i, j⟩ : C.MorphismCoefficientPosition C) = 0 := by
  classical
  change (Finsupp.single i 1 : C.Space x) j = 0
  simp [hij]

/-- The equality component containing all diagonal positions of a self-word. -/
def diagonalMorphismCoefficientComponent (C : Word R) :
    C.MorphismCoefficientComponent C :=
  C.morphismCoefficientComponentOf C
    (C.diagonalMorphismCoefficientPosition C.sourcePosition)

/-- Every diagonal coefficient position represents the diagonal component. -/
@[simp]
theorem morphismCoefficientComponentOf_diagonal
    (C : Word R) {x : Q} (i : C.PositionAt x) :
    C.morphismCoefficientComponentOf C
        (C.diagonalMorphismCoefficientPosition i) =
      C.diagonalMorphismCoefficientComponent := by
  apply (C.morphismCoefficientComponentOf_eq_iff C _ _).mpr
  exact C.diagonalMorphismCoefficientPosition_eqvGen_source i

/-- The chosen representative of the diagonal component is connected to the
source diagonal position. -/
theorem diagonalMorphismCoefficientComponent_representative_eqvGen_source
    (C : Word R) :
    Relation.EqvGen (C.MorphismCoefficientStep C)
      C.diagonalMorphismCoefficientComponent.representative
      (C.diagonalMorphismCoefficientPosition C.sourcePosition) := by
  apply (C.morphismCoefficientComponentOf_eq_iff C _ _).mp
  rw [C.morphismCoefficientComponentOf_representative]
  rfl

/-- Every endomorphism has the same coefficient at the chosen diagonal
component representative and at the source diagonal position. -/
theorem morphismCoefficientAt_diagonalComponent_representative_eq_source
    (C : Word R) (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ C.rightModule hmono) :
    C.morphismCoefficientAt C hmono hmono f
        C.diagonalMorphismCoefficientComponent.representative =
      C.morphismCoefficientAt C hmono hmono f
        (C.diagonalMorphismCoefficientPosition C.sourcePosition) :=
  C.morphismCoefficientAt_eq_of_eqvGen C hmono hmono f
    C.diagonalMorphismCoefficientComponent_representative_eqvGen_source

/-- The identity has coefficient one at the chosen representative of the
diagonal component. -/
theorem morphismCoefficientAt_id_diagonalComponent_representative
    (C : Word R) (hmono : IsMonomial R) :
    C.morphismCoefficientAt C hmono hmono
        (𝟙 (C.rightModule hmono))
        C.diagonalMorphismCoefficientComponent.representative = 1 := by
  calc
    _ = C.morphismCoefficientAt C hmono hmono
        (𝟙 (C.rightModule hmono))
        (C.diagonalMorphismCoefficientPosition C.sourcePosition) :=
      C.morphismCoefficientAt_eq_of_eqvGen C hmono hmono
        (𝟙 (C.rightModule hmono))
        C.diagonalMorphismCoefficientComponent_representative_eqvGen_source
    _ = 1 := C.morphismCoefficientAt_id_diagonal hmono C.sourcePosition

/-- The diagonal component cannot meet an unmatched-step zero boundary. -/
theorem diagonalMorphismCoefficientComponent_isBoundaryFree
    (C : Word R) (hmono : IsMonomial R) :
    C.IsBoundaryFreeMorphismCoefficientComponent C
      C.diagonalMorphismCoefficientComponent.representative := by
  apply C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero C hmono hmono
    (𝟙 (C.rightModule hmono))
  rw [C.morphismCoefficientAt_id_diagonalComponent_representative]
  exact one_ne_zero

/-- The diagonal component as an index in the graph-component basis. -/
def diagonalBoundaryFreeMorphismCoefficientComponent
    (C : Word R) (hmono : IsMonomial R) :
    C.BoundaryFreeMorphismCoefficientComponent C :=
  ⟨C.diagonalMorphismCoefficientComponent,
    C.diagonalMorphismCoefficientComponent_isBoundaryFree hmono⟩

/-- A component different from the diagonal component contains no diagonal
coefficient position. -/
theorem not_representative_eqvGen_diagonal_of_ne
    (C : Word R) (component : C.MorphismCoefficientComponent C)
    (hne : component ≠ C.diagonalMorphismCoefficientComponent)
    {x : Q} (i : C.PositionAt x) :
    ¬ Relation.EqvGen (C.MorphismCoefficientStep C)
        component.representative
        (C.diagonalMorphismCoefficientPosition i) := by
  intro hconn
  apply hne
  calc
    component = C.morphismCoefficientComponentOf C
        component.representative :=
      (C.morphismCoefficientComponentOf_representative C component).symm
    _ = C.morphismCoefficientComponentOf C
        (C.diagonalMorphismCoefficientPosition i) :=
      (C.morphismCoefficientComponentOf_eq_iff C _ _).mpr hconn
    _ = C.diagonalMorphismCoefficientComponent :=
      C.morphismCoefficientComponentOf_diagonal i

/-- Every non-diagonal graph-component basis vector has zero diagonal
coefficient. -/
theorem morphismCoefficientAt_boundaryFreeComponentMap_diagonal_eq_zero
    (C : Word R) (hmono : IsMonomial R)
    (component : C.BoundaryFreeMorphismCoefficientComponent C)
    (hne : component.1 ≠ C.diagonalMorphismCoefficientComponent)
    {x : Q} (i : C.PositionAt x) :
    C.morphismCoefficientAt C hmono hmono
        (C.boundaryFreeMorphismCoefficientComponentMap
          C hmono hmono component)
        (C.diagonalMorphismCoefficientPosition i) = 0 := by
  rw [C.morphismCoefficientAt_boundaryFreeComponentMap,
    C.coefficientComponentIndicator_eq_zero]
  exact C.not_representative_eqvGen_diagonal_of_ne component.1 hne i

/-- The graph-component basis vector indexed by the diagonal component is the
identity endomorphism. -/
theorem boundaryFreeMorphismCoefficientComponentMap_diagonal_eq_id
    (C : Word R) (hmono : IsMonomial R) :
    C.boundaryFreeMorphismCoefficientComponentMap C hmono hmono
        (C.diagonalBoundaryFreeMorphismCoefficientComponent hmono) =
      𝟙 (C.rightModule hmono) := by
  apply C.rightModuleHom_ext_morphismCoefficientAt C hmono hmono
  rintro ⟨x, i, j⟩
  rw [C.morphismCoefficientAt_boundaryFreeComponentMap]
  by_cases hij : i = j
  · subst j
    rw [C.coefficientComponentIndicator_eq_one]
    · exact C.morphismCoefficientAt_id_diagonal hmono i |>.symm
    · change Relation.EqvGen (C.MorphismCoefficientStep C)
        C.diagonalMorphismCoefficientComponent.representative
        (C.diagonalMorphismCoefficientPosition i)
      apply (C.morphismCoefficientComponentOf_eq_iff C _ _).mp
      rw [C.morphismCoefficientComponentOf_representative,
        C.morphismCoefficientComponentOf_diagonal]
  · rw [C.coefficientComponentIndicator_eq_zero,
      C.morphismCoefficientAt_id_eq_zero_of_ne hmono i j hij]
    intro hconn
    have hcoeff := C.morphismCoefficientAt_eq_of_eqvGen C hmono hmono
      (𝟙 (C.rightModule hmono)) hconn
    change C.morphismCoefficientAt C hmono hmono
        (𝟙 (C.rightModule hmono))
          C.diagonalMorphismCoefficientComponent.representative =
      C.morphismCoefficientAt C hmono hmono
        (𝟙 (C.rightModule hmono))
          (⟨x, i, j⟩ : C.MorphismCoefficientPosition C) at hcoeff
    rw [C.morphismCoefficientAt_id_diagonalComponent_representative,
      C.morphismCoefficientAt_id_eq_zero_of_ne hmono i j hij] at hcoeff
    exact one_ne_zero hcoeff

end MagnitudeConjecture.BoundQuiver.StringWord.Word
