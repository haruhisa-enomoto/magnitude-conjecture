import MagnitudeConjecture.Algebra.StringBoundarySquare
import MagnitudeConjecture.Algebra.StringFiniteModule
import MagnitudeConjecture.Algebra.StringMixedBoundarySquare
import MagnitudeConjecture.Algebra.StringNegativeBoundarySquare
import MagnitudeConjecture.CategoryTheory.BinaryBiproductExactReflection
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian

/-!
# String boundary squares in the finite module category

The explicit string-module boundary complexes are first proved exact in the
ambient functor category.  This file bundles their maps in the category of
finite-dimensional linear modules and reflects exactness along the faithful
inclusion.  Thus the chosen middle term is a literal binary biproduct in the
finite module category, as required by the almost-split argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q} [Fintype Q]

/-- Bundle a morphism between raw string modules in the finite-dimensional
linear-module category. -/
def finiteRightModuleHom
    {C D : Word R} (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ D.rightModule hmono) :
    C.finiteRightModule hmono ⟶ D.finiteRightModule hmono :=
  ObjectProperty.homMk (ObjectProperty.homMk f)

@[simp]
theorem finiteRightModuleHom_hom_hom
    {C D : Word R} (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ D.rightModule hmono) :
    (finiteRightModuleHom hmono f).hom.hom = f :=
  rfl

/-- Exactness of a binary-biproduct complex of raw string modules lifts to
the corresponding complex in the finite-dimensional module category. -/
theorem finiteRightModule_binaryBiproductShortComplex_exact
    {X A B Y : Word R} (hmono : IsMonomial R)
    (fA : X.rightModule hmono ⟶ A.rightModule hmono)
    (fB : X.rightModule hmono ⟶ B.rightModule hmono)
    (gA : A.rightModule hmono ⟶ Y.rightModule hmono)
    (gB : B.rightModule hmono ⟶ Y.rightModule hmono)
    (hzero : fA ≫ gA + fB ≫ gB = 0)
    (hexact :
      (MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex
        fA fB gA gB hzero).Exact) :
    (MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex
      (finiteRightModuleHom hmono fA)
      (finiteRightModuleHom hmono fB)
      (finiteRightModuleHom hmono gA)
      (finiteRightModuleHom hmono gB) (by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        exact hzero)).Exact := by
  let P := CoveringHom.IsFiniteDimensionalModule
      (C := (Category R)ᵒᵖ) k
  let L := CoveringHom.IsLinearModule (C := (Category R)ᵒᵖ) k
  let J : CoveringHom.FiniteDimensionalModuleCategory
        (C := (Category R)ᵒᵖ) k ⥤
      ((Category R)ᵒᵖ ⥤ ModuleCat k) := P.ι ⋙ L.ι
  letI : PreservesLimitsOfShape (Discrete WalkingPair) P.ι := by
    infer_instance
  letI : PreservesLimitsOfShape (Discrete WalkingPair) L.ι := by
    infer_instance
  letI : PreservesLimitsOfShape (Discrete WalkingPair) J := by
    infer_instance
  letI : PreservesBinaryBiproduct
      (X := A.finiteRightModule hmono) (Y := B.finiteRightModule hmono) J :=
    preservesBinaryBiproduct_of_preservesBinaryProduct J
  apply MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex_exact_of_map J
  change (MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex
    fA fB gA gB _).Exact
  convert hexact using 1

namespace PositiveBoundarySquare

/-- The positive boundary complex bundled in the finite-dimensional module
category. -/
def finiteShortComplex {C : Word R} (square : PositiveBoundarySquare C)
    (hmono : IsMonomial R) := by
  let hzero :
      square.toLeftMap hmono ≫ square.leftToBaseMap hmono +
        (-square.toRightMap hmono) ≫ square.rightToBaseMap hmono = 0 := by
    rw [Preadditive.neg_comp, square.map_commutes hmono]
    exact add_neg_cancel _
  exact MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex
    (finiteRightModuleHom hmono (square.toLeftMap hmono))
    (finiteRightModuleHom hmono (-square.toRightMap hmono))
    (finiteRightModuleHom hmono (square.leftToBaseMap hmono))
    (finiteRightModuleHom hmono (square.rightToBaseMap hmono)) (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact hzero)

/-- The finite-dimensional positive boundary complex is exact. -/
theorem finiteShortComplex_exact {C : Word R}
    (square : PositiveBoundarySquare C) (hmono : IsMonomial R) :
    (square.finiteShortComplex hmono).Exact := by
  let hzero :
      square.toLeftMap hmono ≫ square.leftToBaseMap hmono +
        (-square.toRightMap hmono) ≫ square.rightToBaseMap hmono = 0 := by
    rw [Preadditive.neg_comp, square.map_commutes hmono]
    exact add_neg_cancel _
  have hexact := square.shortComplex_exact hmono
  change (MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex
    (square.toLeftMap hmono) (-square.toRightMap hmono)
    (square.leftToBaseMap hmono) (square.rightToBaseMap hmono) hzero).Exact at hexact
  exact finiteRightModule_binaryBiproductShortComplex_exact hmono
    (square.toLeftMap hmono) (-square.toRightMap hmono)
    (square.leftToBaseMap hmono) (square.rightToBaseMap hmono) hzero hexact

end PositiveBoundarySquare

namespace MixedBoundarySquare

/-- The mixed cohook-hook boundary complex bundled in the
finite-dimensional module category. -/
def finiteShortComplex {D : Word R} (square : MixedBoundarySquare D)
    (hmono : IsMonomial R) := by
  let hzero :
      square.rightToBaseMap hmono ≫ square.baseToLeftMap hmono +
        (-square.rightToCornerMap hmono) ≫ square.cornerToLeftMap hmono = 0 := by
    rw [Preadditive.neg_comp, square.map_commutes]
    exact add_neg_cancel _
  exact MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex
    (finiteRightModuleHom hmono (square.rightToBaseMap hmono))
    (finiteRightModuleHom hmono (-square.rightToCornerMap hmono))
    (finiteRightModuleHom hmono (square.baseToLeftMap hmono))
    (finiteRightModuleHom hmono (square.cornerToLeftMap hmono)) (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact hzero)

/-- The finite-dimensional mixed boundary complex is exact. -/
theorem finiteShortComplex_exact {D : Word R}
    (square : MixedBoundarySquare D) (hmono : IsMonomial R) :
    (square.finiteShortComplex hmono).Exact := by
  let hzero :
      square.rightToBaseMap hmono ≫ square.baseToLeftMap hmono +
        (-square.rightToCornerMap hmono) ≫ square.cornerToLeftMap hmono = 0 := by
    rw [Preadditive.neg_comp, square.map_commutes]
    exact add_neg_cancel _
  have hexact := square.shortComplex_exact hmono
  change (MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex
    (square.rightToBaseMap hmono) (-square.rightToCornerMap hmono)
    (square.baseToLeftMap hmono) (square.cornerToLeftMap hmono) hzero).Exact at hexact
  exact finiteRightModule_binaryBiproductShortComplex_exact hmono
    (square.rightToBaseMap hmono) (-square.rightToCornerMap hmono)
    (square.baseToLeftMap hmono) (square.cornerToLeftMap hmono) hzero hexact

end MixedBoundarySquare

namespace NegativeBoundarySquare

/-- The double-cohook boundary complex bundled in the finite-dimensional
module category. -/
def finiteShortComplex {D : Word R} (square : NegativeBoundarySquare D)
    (hmono : IsMonomial R) := by
  let hzero :
      square.baseToLeftMap hmono ≫ square.leftToCornerMap hmono +
        square.baseToRightMap hmono ≫ (-square.rightToCornerMap hmono) = 0 := by
    rw [Preadditive.comp_neg, square.map_commutes]
    exact add_neg_cancel _
  exact MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex
    (finiteRightModuleHom hmono (square.baseToLeftMap hmono))
    (finiteRightModuleHom hmono (square.baseToRightMap hmono))
    (finiteRightModuleHom hmono (square.leftToCornerMap hmono))
    (finiteRightModuleHom hmono (-square.rightToCornerMap hmono)) (by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact hzero)

/-- The finite-dimensional double-cohook boundary complex is exact. -/
theorem finiteShortComplex_exact {D : Word R}
    (square : NegativeBoundarySquare D) (hmono : IsMonomial R) :
    (square.finiteShortComplex hmono).Exact := by
  let hzero :
      square.baseToLeftMap hmono ≫ square.leftToCornerMap hmono +
        square.baseToRightMap hmono ≫ (-square.rightToCornerMap hmono) = 0 := by
    rw [Preadditive.comp_neg, square.map_commutes]
    exact add_neg_cancel _
  have hexact := square.shortComplex_exact hmono
  change (MagnitudeConjecture.CategoryTheory.binaryBiproductShortComplex
    (square.baseToLeftMap hmono) (square.baseToRightMap hmono)
    (square.leftToCornerMap hmono) (-square.rightToCornerMap hmono) hzero).Exact at hexact
  exact finiteRightModule_binaryBiproductShortComplex_exact hmono
    (square.baseToLeftMap hmono) (square.baseToRightMap hmono)
    (square.leftToCornerMap hmono) (-square.rightToCornerMap hmono) hzero hexact

end NegativeBoundarySquare

end MagnitudeConjecture.BoundQuiver.StringWord.Word
