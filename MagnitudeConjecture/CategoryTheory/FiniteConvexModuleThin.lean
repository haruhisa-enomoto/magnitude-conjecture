import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteConvexModuleControlWindow
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleThin
import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd
import MagnitudeConjecture.CategoryTheory.ObjectDeletionConvexComparison

/-!
# Thin modules on finite convex full subcategories

A finite convex full subcategory of a skeletal linear category is linearly
equivalent to deletion by its complementary object set.  This file lifts that
comparison to finite-dimensional module categories and transports pointwise
thinness of indecomposable modules back to the literal full subcategory used
in the manuscript.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v uM

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- The literal full subcategory on a finite set of objects has finite object
type. -/
theorem fullSubcategoryOn_finite (U : Set C) (hU : U.Finite) :
    Finite (FullSubcategoryOn C U) := by
  letI : Finite U := hU
  let f : FullSubcategoryOn C U → U := fun X ↦ ⟨X.obj, X.property⟩
  exact Finite.of_injective f (by
    intro X Y hXY
    apply ObjectProperty.FullSubcategory.ext
    exact congrArg Subtype.val hXY)

/-- Covariant representables on a finite full subcategory of a locally
bounded category are finite-dimensional modules.  Pointwise finiteness is
inherited from the ambient Hom spaces, while finite support follows from the
finite object type. -/
theorem fullSubcategory_finiteCovariantRepresentables
    (H : IsLocallyBounded (k := k) (C := C))
    (U : Set C) (hU : U.Finite)
    (X : FullSubcategoryOn C U) :
    IsFiniteDimensionalModule (C := FullSubcategoryOn C U) k
      (linearCoyonedaLinearModule (k := k) X) := by
  letI : Finite (FullSubcategoryOn C U) :=
    fullSubcategoryOn_finite C U hU
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    letI : FiniteDimensional k (X.obj ⟶ Y.obj) :=
      (H.finiteCovariantRepresentables X.obj).1 Y.obj
    exact FiniteDimensional.of_injective
      (InducedCategory.homLinearEquiv (R := k)).toLinearMap
      (InducedCategory.homLinearEquiv (R := k)).injective
  · exact Set.toFinite _

/-- Objects of a full subcategory of a locally bounded category retain local
endomorphism rings. -/
theorem fullSubcategory_localEndomorphismRings
    (H : IsLocallyBounded (k := k) (C := C))
    (U : Set C) (X : FullSubcategoryOn C U) :
    IsLocalRing (End X) := by
  letI : IsLocalRing (End X.obj) := H.localEndomorphismRings X.obj
  let q : End X ≃+* End X.obj :=
    { InducedCategory.endEquiv with
      map_add' := fun _ _ ↦ rfl }
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm q.symm

/-- Change of base along the convex-full-subcategory/deletion equivalence.
The direction is from deletion modules to modules on the literal full
subcategory. -/
noncomputable def finiteConvexFullSubcategoryModuleEquivalence
    (hC : Skeletal C) (U : Set C) (hUfinite : U.Finite)
    (hUconvex : IsConvexObjectSet (C := C) U) :
    FiniteDimensionalModuleCategory.{u, v, v, uM}
        (C := DeletionCategory (k := k) C Uᶜ) k ≌
      FiniteDimensionalModuleCategory.{u, v, v, uM}
        (C := FullSubcategoryOn C U) k := by
  letI : Finite (FullSubcategoryOn C U) :=
    fullSubcategoryOn_finite C U hUfinite
  letI : Finite (DeletionCategory (k := k) C Uᶜ) :=
    complementDeletion_finite (k := k) C U hUfinite
  exact finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) (convexFullSubcategoryDeletionEquivalence
      (k := k) C hC U hUconvex)

noncomputable instance
    finiteConvexFullSubcategoryModuleEquivalence_functor_additive
    (hC : Skeletal C) (U : Set C) (hUfinite : U.Finite)
    (hUconvex : IsConvexObjectSet (C := C) U) :
    (finiteConvexFullSubcategoryModuleEquivalence
      (k := k) C hC U hUfinite hUconvex).functor.Additive := by
  letI : Finite (FullSubcategoryOn C U) :=
    fullSubcategoryOn_finite C U hUfinite
  letI : Finite (DeletionCategory (k := k) C Uᶜ) :=
    complementDeletion_finite (k := k) C U hUfinite
  change (finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) (convexFullSubcategoryDeletionEquivalence
      (k := k) C hC U hUconvex)).functor.Additive
  infer_instance

/-- If every indecomposable module on the complementary deletion quotient is
pointwise thin, then every indecomposable module on the literal finite convex
full subcategory is pointwise thin. -/
theorem fullSubcategory_isPointwiseThin_of_deletion
    (hC : Skeletal C) (U : Set C) (hUfinite : U.Finite)
    (hUconvex : IsConvexObjectSet (C := C) U)
    (hthin : ∀ (N : FiniteDimensionalModuleCategory.{u, v, v, uM}
      (C := DeletionCategory (k := k) C Uᶜ) k),
      Indecomposable N → IsPointwiseThin N.obj.obj)
    (M : FiniteDimensionalModuleCategory.{u, v, v, uM}
      (C := FullSubcategoryOn C U) k)
    (hM : Indecomposable M) :
    IsPointwiseThin M.obj.obj := by
  let E := finiteConvexFullSubcategoryModuleEquivalence
    (k := k) C hC U hUfinite hUconvex
  letI : E.functor.Additive := inferInstance
  letI : E.inverse.Additive := inferInstance
  let N := E.inverse.obj M
  have hN : Indecomposable N :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse M).2 hM
  have hthinN : IsPointwiseThin N.obj.obj := hthin N hN
  let eM : E.functor.obj N ≅ M := E.counitIso.app M
  intro X
  let eMX : (E.functor.obj N).obj.obj.obj X ≅ M.obj.obj.obj X :=
    ((IsLinearModule.{u, v, v, uM}
      (C := FullSubcategoryOn C U) k).ι.mapIso
        ((IsFiniteDimensionalModule
          (C := FullSubcategoryOn C U) k).ι.mapIso eM)).app X
  rw [← LinearEquiv.finrank_eq eMX.toLinearEquiv]
  exact hthinN
    ((convexFullSubcategoryDeletionEquivalence
      (k := k) C hC U hUconvex).functor.obj X)

end MagnitudeConjecture.ObjectDeletion
