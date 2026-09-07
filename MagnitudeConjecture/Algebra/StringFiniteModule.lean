import MagnitudeConjecture.Algebra.StringRepresentation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift

/-!
# String representations as finite-dimensional linear modules

The canonical position-basis representation of a string word was initially
constructed as a raw functor.  This file records that it is additive and
linear, bundles it in the finite-dimensional module category, and exhibits a
canonical nonzero coordinate.  These are the ambient categorical interfaces
needed by finite string reconstruction and the almost-split sequences.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace StringWord.Word

variable {R : RelationFamily k Q}

/-- The right-module realization preserves addition of morphisms. -/
instance rightModule_additive (C : Word R) (hmono : IsMonomial R) :
    (C.rightModule hmono).Additive where
  map_add {X Y} {f g} := by
    apply Quiver.Hom.op_inj
    change
      (C.quotientRightModuleAux hmono).map ((f + g).unop) =
        ((C.quotientRightModuleAux hmono).map f.unop).unop.op +
          ((C.quotientRightModuleAux hmono).map g.unop).unop.op
    simp

/-- The right-module realization preserves coefficient-field scalars. -/
instance rightModule_linear (C : Word R) (hmono : IsMonomial R) :
    (C.rightModule hmono).Linear k where
  map_smul {X Y} f r := by
    apply Quiver.Hom.op_inj
    change
      (C.quotientRightModuleAux hmono).map ((r • f).unop) =
        (r •
          ((C.quotientRightModuleAux hmono).map f.unop).unop).op
    simp

/-- The canonical string representation, bundled as a linear module. -/
def rightLinearModule (C : Word R) (hmono : IsMonomial R) :
    CoveringHom.LinearModuleCategory (C := (Category R)ᵒᵖ) k :=
  ⟨C.rightModule hmono, inferInstance, inferInstance⟩

@[simp]
theorem rightLinearModule_obj (C : Word R) (hmono : IsMonomial R)
    (X : (Category R)ᵒᵖ) :
    (C.rightLinearModule hmono).obj.obj X = (C.rightModule hmono).obj X :=
  rfl

/-- The string representation is nonzero at its source endpoint. -/
theorem rightModule_source_nontrivial
    (C : Word R) (hmono : IsMonomial R) :
    Nontrivial
      ((C.rightModule hmono).obj (Opposite.op (obj R C.source))) := by
  change Nontrivial (C.Space C.source)
  letI : Nonempty (C.PositionAt C.source) := ⟨C.sourcePosition⟩
  infer_instance

variable [Fintype Q]

/-- A string representation over a finite displayed quiver is pointwise
finite-dimensional and has finite support. -/
theorem rightLinearModule_isFiniteDimensional
    (C : Word R) (hmono : IsMonomial R) :
    CoveringHom.IsFiniteDimensionalModule (C := (Category R)ᵒᵖ) k
      (C.rightLinearModule hmono) := by
  constructor
  · rintro ⟨⟨x⟩⟩
    change FiniteDimensional k (C.Space x)
    infer_instance
  · letI : Fintype ((Category R)ᵒᵖ) :=
      Fintype.ofEquiv (Category R) Opposite.equivToOpposite
    exact Set.toFinite _

/-- The canonical string representation, bundled as a finite-dimensional
linear module. -/
def finiteRightModule (C : Word R) (hmono : IsMonomial R) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := (Category R)ᵒᵖ) k :=
  ⟨C.rightLinearModule hmono,
    C.rightLinearModule_isFiniteDimensional hmono⟩

@[simp]
theorem finiteRightModule_obj (C : Word R) (hmono : IsMonomial R)
    (X : (Category R)ᵒᵖ) :
    (C.finiteRightModule hmono).obj.obj.obj X =
      (C.rightModule hmono).obj X :=
  rfl

end StringWord.Word

end MagnitudeConjecture.BoundQuiver
