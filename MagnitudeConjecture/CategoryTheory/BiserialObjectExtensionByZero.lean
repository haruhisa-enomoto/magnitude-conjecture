import MagnitudeConjecture.CategoryTheory.BiserialObject
import MagnitudeConjecture.CategoryTheory.ObjectDeletionAlmostSplit

/-!
# Biserial objects and extension by zero

This file proves the intrinsic transport statement needed by the manuscript's
finite-convex reduction: extension by zero from an object-deletion category
preserves biseriality.  The proof factors through the equivalence with the
vanishing Serre subcategory, so it does not depend on coordinates for
submodules.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable (S : Set C)

/-- Finite-dimensional extension by zero preserves intrinsic biseriality. -/
theorem IsBiserialObject.finiteDimensionalModuleExtensionByZero
    {M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (hM : IsBiserialObject M) :
    IsBiserialObject
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj M) := by
  let P := finiteModuleVanishesOnDeleted (k := k) C S
  letI : P.IsClosedUnderBinaryProducts := {
    limitsOfShape_le := by
      rintro Z ⟨p⟩
      let X := p.diag.obj ⟨WalkingPair.left⟩
      let Y := p.diag.obj ⟨WalkingPair.right⟩
      have hXY : P (X ⊞ Y) :=
        P.prop_biprod
          (p.prop_diag_obj ⟨WalkingPair.left⟩)
          (p.prop_diag_obj ⟨WalkingPair.right⟩)
      exact P.prop_of_iso
        ((biprod.isoProd X Y).trans
          (IsLimit.conePointUniqueUpToIso (prodIsProd X Y)
            ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)))
        hXY }
  letI : P.IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  let E := finiteDimensionalModuleExtensionByZeroVanishingEquivalence
    (k := k) C S
  have hEM : IsBiserialObject (E.functor.obj M) :=
    hM.map_equivalence E
  exact hEM.to_fullSubcategory_ambient
    P

end MagnitudeConjecture.ObjectDeletion
