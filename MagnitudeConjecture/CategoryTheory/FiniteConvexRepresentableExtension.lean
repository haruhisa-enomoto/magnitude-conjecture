import MagnitudeConjecture.CategoryTheory.BiserialObjectExtensionByZero
import MagnitudeConjecture.CategoryTheory.FiniteConvexModuleThin

/-!
# Extending finite-convex representables

This file identifies the restriction of an ambient covariant representable
with the corresponding representable on a finite convex full subcategory,
through deletion by the complementary objects.  It then combines that
identification with intrinsic biseriality and extension by zero.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- Through the convex-full-subcategory/deletion equivalence, the restriction
of an ambient representable supported in `U` is the literal representable on
the full subcategory on `U`. -/
noncomputable def finiteConvexRestrictionRepresentableIso
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (U : Set C) (hUfinite : U.Finite)
    (hUconvex : IsConvexObjectSet (C := C) U)
    (hPU : ∀ X : FullSubcategoryOn C U,
      IsFiniteDimensionalModule (C := FullSubcategoryOn C U) k
        (linearCoyonedaLinearModule (k := k) X))
    (X : FullSubcategoryOn C U)
    (hsupport : moduleSupport k
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X.obj)).obj.obj ⊆ U) :
    let M := (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
      (Opposite.op X.obj)
    let hvanish := moduleVanishesOnDeleted_compl_of_moduleSupport_subset
      (k := k) C U M hsupport
    let R := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C Uᶜ M hvanish
    let E := finiteConvexFullSubcategoryModuleEquivalence
      (k := k) C hC U hUfinite hUconvex
    E.functor.obj R ≅
      (finiteDimensionalLinearCoyonedaFunctor (k := k) hPU).obj
        (Opposite.op X) := by
  let M := (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
    (Opposite.op X.obj)
  let hvanish := moduleVanishesOnDeleted_compl_of_moduleSupport_subset
    (k := k) C U M hsupport
  let R := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C Uᶜ M hvanish
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun Y ↦ ?_) ?_
  · change ModuleCat.of k (X.obj ⟶ Y.obj) ≅ ModuleCat.of k (X ⟶ Y)
    exact (InducedCategory.homLinearEquiv (R := k)).symm.toModuleIso
  intro Y Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  rfl

/-- Intrinsic biseriality of the representable on a finite convex support
window implies intrinsic biseriality of the ambient representable. -/
theorem finiteCovariantRepresentable_isBiserialObject_of_finiteConvex
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (U : Set C) (hUfinite : U.Finite)
    (hUconvex : IsConvexObjectSet (C := C) U)
    (hPU : ∀ X : FullSubcategoryOn C U,
      IsFiniteDimensionalModule (C := FullSubcategoryOn C U) k
        (linearCoyonedaLinearModule (k := k) X))
    (X : FullSubcategoryOn C U)
    (hsupport : moduleSupport k
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X.obj)).obj.obj ⊆ U)
    (hX : IsBiserialObject
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hPU).obj
        (Opposite.op X))) :
    IsBiserialObject
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X.obj)) := by
  let M := (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
    (Opposite.op X.obj)
  let hvanish := moduleVanishesOnDeleted_compl_of_moduleSupport_subset
    (k := k) C U M hsupport
  let R := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C Uᶜ M hvanish
  let E := finiteConvexFullSubcategoryModuleEquivalence
    (k := k) C hC U hUfinite hUconvex
  let i := finiteConvexRestrictionRepresentableIso
    (k := k) C hC hP U hUfinite hUconvex hPU X hsupport
  have hER : IsBiserialObject (E.functor.obj R) :=
    hX.congr i.symm
  have hR : IsBiserialObject R :=
    IsBiserialObject.of_map_equivalence E hER
  have hext : IsBiserialObject
      ((finiteDimensionalModuleExtensionByZero (k := k) C Uᶜ).obj R) :=
    MagnitudeConjecture.ObjectDeletion.IsBiserialObject.finiteDimensionalModuleExtensionByZero
      C Uᶜ hR
  exact hext.congr
    (finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C Uᶜ M hvanish)

end MagnitudeConjecture.ObjectDeletion
