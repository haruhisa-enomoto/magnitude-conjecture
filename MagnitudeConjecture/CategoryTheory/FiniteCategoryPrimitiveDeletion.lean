import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitivePresentation
import MagnitudeConjecture.CategoryTheory.ObjectDeletionAlmostSplit
import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotient
import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotientCategory
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Primitive category-algebra deletion

For the canonical projector at an object of a finite linear category, the
primitive ideal annihilates a represented module exactly when the original
category module vanishes at that object.  This is the objectwise bridge
between algebraic primitive deletion and the literal object-deletion quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u

variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Fintype C]

namespace finiteCategoryProjectiveGenerator

variable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))

private abbrev representable (X : C) :
    FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k :=
  (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
    (Opposite.op X)

local instance primitiveDeletionAlgebraFiniteDimensional :
    FiniteDimensional k (algebra hP) :=
  algebra_finiteDimensional hP

local instance primitiveDeletionAlgebraOppositeIsNoetherian :
    IsNoetherianRing (algebra hP)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k (algebra hP)ᵐᵒᵖ

/-- Under the projective-generator equivalence, annihilation by the primitive
ideal of the projector at `X` is exactly vanishing at `X`. -/
theorem represented_isAnnihilatedBy_primitiveIdeal_iff_obj_isZero
    (X : C)
    (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k) :
    RightModule.IsAnnihilatedBy
        (RightModule.primitiveIdeal (canonicalProjector hP X))
        ((representedFGFunctor hP).obj M) ↔
      IsZero (M.obj.obj.obj X) := by
  rw [RightModule.isAnnihilatedBy_primitiveIdeal_iff]
  constructor
  · intro hann
    rw [ModuleCat.isZero_iff_subsingleton]
    constructor
    intro x y
    have element_eq_zero (z : M.obj.obj.obj X) : z = 0 := by
      let q : representable hP X ⟶ M :=
        ObjectProperty.homMk (linearCoyonedaHom M.obj X z)
      let f : finiteCategoryProjectiveGenerator hP ⟶ M :=
        biproduct.π (representable hP) X ≫ q
      have hf := hann f
      change canonicalProjector hP X ≫ f = 0 at hf
      have hq := congrArg
        (fun a : finiteCategoryProjectiveGenerator hP ⟶ M ↦
          biproduct.ι (representable hP) X ≫ a) hf
      have hqzero : q = 0 := by
        simpa [f, canonicalProjector, Category.assoc] using hq
      have hqhom : q.hom = 0 := congrArg (fun a ↦ a.hom) hqzero
      have hz := congrArg
        (fun a : linearCoyonedaLinearModule (k := k) X ⟶ M.obj ↦
          a.hom.app X (𝟙 X)) hqhom
      change
        (linearCoyonedaHom M.obj X z).hom.app X (𝟙 X) = 0 at hz
      simpa using hz
    exact (element_eq_zero x).trans (element_eq_zero y).symm
  · intro hzero f
    have hsub : Subsingleton (M.obj.obj.obj X) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero
    let q : representable hP X ⟶ M :=
      biproduct.ι (representable hP) X ≫ f
    have hz : q.hom.hom.app X (𝟙 X) = 0 :=
      Subsingleton.elim _ _
    have hzeroCoyoneda :
        linearCoyonedaHom M.obj X (0 : M.obj.obj.obj X) = 0 := by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext Y
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      simp [linearCoyonedaHom_app_apply]
    have hqhom : q.hom = 0 := by
      calc
        q.hom = linearCoyonedaHom M.obj X
            (q.hom.hom.app X (𝟙 X)) :=
          (linearCoyonedaHom_self M.obj X q.hom).symm
        _ = linearCoyonedaHom M.obj X 0 := by rw [hz]
        _ = 0 := hzeroCoyoneda
    have hqzero : q = 0 := by
      apply ObjectProperty.hom_ext
      exact hqhom
    change canonicalProjector hP X ≫ f = 0
    change
      biproduct.π (representable hP) X ≫ q = 0
    rw [hqzero, comp_zero]

/-- For a singleton deletion, the primitive-ideal annihilation property is
the literal vanishing-on-deleted-objects property. -/
theorem primitiveQuotientProperty_inverseImage_eq_singletonVanishes
    (X : C) :
    (RightModule.PrimitiveQuotientProperty (canonicalProjector hP X)).inverseImage
        (moduleEquivalence hP).functor =
      ObjectDeletion.finiteModuleVanishesOnDeleted
        (k := k) C ({X} : Set C) := by
  ext M
  change
    RightModule.IsAnnihilatedBy
        (RightModule.primitiveIdeal (canonicalProjector hP X))
        ((representedFGFunctor hP).obj M) ↔
      ObjectDeletion.ModuleVanishesOnDeleted
        (k := k) C ({X} : Set C) M.obj.obj
  rw [represented_isAnnihilatedBy_primitiveIdeal_iff_obj_isZero hP X M]
  constructor
  · intro h Y hY
    rw [Set.mem_singleton_iff.mp hY]
    exact h
  · intro h
    exact h X (Set.mem_singleton X)

/-- The finite modules over the literal object-deletion category are
equivalent to the ambient algebra modules annihilated by the corresponding
canonical primitive ideal. -/
def deletionPrimitiveSubcategoryEquivalence (X : C) :
    FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)) k ≌
      RightModule.PrimitiveQuotientSubcategory (canonicalProjector hP X) :=
  (ObjectDeletion.finiteDimensionalModuleExtensionByZeroVanishingEquivalence
      (k := k) C ({X} : Set C)).trans
    ((moduleEquivalence hP).congrFullSubcategory
      (primitiveQuotientProperty_inverseImage_eq_singletonVanishes hP X))

/-- The finite-dimensional module category of literal object deletion is
equivalent to finitely generated modules over the algebraic primitive
quotient by the matching canonical projector. -/
def deletionPrimitiveQuotientEquivalence (X : C) :
    FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)) k ≌
      RightModule.FinitelyGeneratedCategory
        (RightModule.primitiveQuotientAlgebra (canonicalProjector hP X)) :=
  (deletionPrimitiveSubcategoryEquivalence hP X).trans
    (RightModule.primitiveQuotientEquivalence
      (k := k) (canonicalProjector hP X))

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
