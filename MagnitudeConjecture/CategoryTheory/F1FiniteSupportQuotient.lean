import MagnitudeConjecture.CategoryTheory.F1FiniteObjectDeletion
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitiveQuotientSurplusReindex
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStructure

/-!
# Finite support quotients for the F1 deletion argument

For a finite object support `K`, the quotient `C/[C \ K]` is represented by the
object-deletion category on `Kᶜ`.  This file packages its finite structural
properties and the literal finite directed deletion inequality.  The
construction is an object quotient, so no convexity of `K` is assumed.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion.Frozen

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- The finite object-support quotient retaining precisely the objects in `K`.
Morphisms factoring through the complement of `K` are killed. -/
abbrev finiteSupportCategory (K : Set C) :=
  ObjectDeletion.DeletionCategory (k := k) C Kᶜ

/-- A finite support quotient has finitely many objects. -/
theorem finiteSupportCategory_finite
    (K : Set C) (hK : K.Finite) :
    Finite (finiteSupportCategory (k := k) (C := C) K) := by
  exact ObjectDeletion.finite_deletion_of_finite_survivors
    (k := k) (C := C) K hK

/-- Covariant representables of a support quotient remain finite-dimensional. -/
theorem finiteSupportCategory_finiteCovariantRepresentables
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (K : Set C) (X : finiteSupportCategory (k := k) (C := C) K) :
    IsFiniteDimensionalModule
      (C := finiteSupportCategory (k := k) (C := C) K) k
      (linearCoyonedaLinearModule (k := k) X) :=
  ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
    (k := k) C hP Kᶜ X

/-- Local representation-finiteness descends to a support quotient. -/
theorem finiteSupportCategory_isLocallyRepresentationFinite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (K : Set C) :
    IsLocallyRepresentationFinite
      (k := k) (C := finiteSupportCategory (k := k) (C := C) K) :=
  ObjectDeletion.isLocallyRepresentationFinite_deletion
    (k := k) C Kᶜ hlocal

/-- Local endomorphism rings descend to a support quotient of a skeletal
category. -/
theorem finiteSupportCategory_localEndomorphismRings
    (hC : Skeletal C)
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (K : Set C) :
    ∀ X : finiteSupportCategory (k := k) (C := C) K,
      IsLocalRing (End X) := by
  intro X
  exact ObjectDeletion.deletion_end_isLocalRing
    (k := k) C hC hlocalRing Kᶜ X

/-- Skeletality descends to a support quotient. -/
theorem finiteSupportCategory_skeletal
    (hC : Skeletal C)
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (K : Set C) :
    Skeletal (finiteSupportCategory (k := k) (C := C) K) :=
  ObjectDeletion.deletion_skeletal (k := k) C hC hlocalRing Kᶜ

/-- Directedness of finite-support modules descends to a support quotient by
extension by zero. -/
theorem finiteSupportCategory_directed
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (K : Set C) :
    HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := finiteSupportCategory (k := k) (C := C) K) :=
  ObjectDeletion.hasAcyclicFiniteModuleNonzeroNonisomorphisms_deletion
    (k := k) (C := C) Kᶜ H

/- The finite support quotient carries canonical complete indecomposable
   families on both sides of a singleton deletion.  Keeping the families
   noncomputable here mirrors the existing finite-category construction and
   leaves the endpoint theorem independent of any residual-cover choice. -/

noncomputable def finiteSupportCategory_skeleton
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (K : Set C) (hK : K.Finite) :
    FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := finiteSupportCategory (k := k) (C := C) K) := by
  letI : Finite (finiteSupportCategory (k := k) (C := C) K) :=
    finiteSupportCategory_finite (k := k) (C := C) K hK
  letI : Fintype (finiteSupportCategory (k := k) (C := C) K) :=
    Fintype.ofFinite _
  exact finiteCategoryModuleIndecomposableSkeleton
    (finiteSupportCategory_isLocallyRepresentationFinite
      (k := k) (C := C) hlocal K)

noncomputable def finiteSupportCategory_singleton_skeleton
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (K : Set C) (hK : K.Finite)
    (x : finiteSupportCategory (k := k) (C := C) K) :
    FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := ObjectDeletion.DeletionCategory (k := k)
        (finiteSupportCategory (k := k) (C := C) K) ({x} : Set _)) := by
  letI : Finite (finiteSupportCategory (k := k) (C := C) K) :=
    finiteSupportCategory_finite (k := k) (C := C) K hK
  letI : Fintype (finiteSupportCategory (k := k) (C := C) K) :=
    Fintype.ofFinite _
  let hlocal' := finiteSupportCategory_isLocallyRepresentationFinite
    (k := k) (C := C) hlocal K
  let hlocalDeleted := ObjectDeletion.isLocallyRepresentationFinite_deletion
    (k := k) (C := finiteSupportCategory (k := k) (C := C) K)
      ({x} : Set _) hlocal'
  letI : Finite (ObjectDeletion.DeletionCategory (k := k)
      (finiteSupportCategory (k := k) (C := C) K) ({x} : Set _)) := by
    infer_instance
  letI : Fintype (ObjectDeletion.DeletionCategory (k := k)
      (finiteSupportCategory (k := k) (C := C) K) ({x} : Set _)) :=
    Fintype.ofFinite _
  exact finiteCategoryModuleIndecomposableSkeleton hlocalDeleted

/-- The finite directed deletion inequality inside a finite support quotient.
The hypotheses and conclusion are entirely literal finite-category data; the
ambient category contributes only the support quotient and its inherited
structural certificates. -/
theorem finiteSupport_singletonDeletion_surplus_le_with_skeletons
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (hC : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (K : Set C) (hK : K.Finite)
    (x : finiteSupportCategory (k := k) (C := C) K)
    (T : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := finiteSupportCategory (k := k) (C := C) K))
    (Tdeleted : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
        (C := ObjectDeletion.DeletionCategory (k := k)
        (finiteSupportCategory (k := k) (C := C) K) ({x} : Set _))) :
    letI : Finite (finiteSupportCategory (k := k) (C := C) K) :=
      finiteSupportCategory_finite (k := k) (C := C) K hK
    let hP' := finiteSupportCategory_finiteCovariantRepresentables
      (k := k) (C := C) hP K
    let hlocal' := finiteSupportCategory_isLocallyRepresentationFinite
      (k := k) (C := C) hlocal K
    let hlocalRing' := finiteSupportCategory_localEndomorphismRings
      (k := k) (C := C) hC hlocalRing K
    let hC' := finiteSupportCategory_skeletal
      (k := k) (C := C) hC hlocalRing K
    let H' := finiteSupportCategory_directed
      (k := k) (C := C) H K
    letI : EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := finiteSupportCategory (k := k) (C := C) K) k) :=
      enoughProjectives_of_finiteRepresentables hP'
    let hPdeleted' := fun Y ↦
      ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
        (k := k) (finiteSupportCategory (k := k) (C := C) K) hP'
          ({x} : Set _) Y
    letI : EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := ObjectDeletion.DeletionCategory (k := k)
            (finiteSupportCategory (k := k) (C := C) K) ({x} : Set _)) k) :=
      enoughProjectives_of_finiteRepresentables hPdeleted'
    @ARCount.surplus (Fin Tdeleted.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity
          Tdeleted.toFiniteRightTauCategoryData)
        Tdeleted.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) ≤
      @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) := by
  let hP' := finiteSupportCategory_finiteCovariantRepresentables
    (k := k) (C := C) hP K
  let hlocal' := finiteSupportCategory_isLocallyRepresentationFinite
    (k := k) (C := C) hlocal K
  let hlocalRing' := finiteSupportCategory_localEndomorphismRings
    (k := k) (C := C) hC hlocalRing K
  let hC' := finiteSupportCategory_skeletal
    (k := k) (C := C) hC hlocalRing K
  let H' := finiteSupportCategory_directed
    (k := k) (C := C) H K
  letI : Finite (finiteSupportCategory (k := k) (C := C) K) :=
    finiteSupportCategory_finite (k := k) (C := C) K hK
  letI : Fintype (finiteSupportCategory (k := k) (C := C) K) :=
    Fintype.ofFinite _
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := finiteSupportCategory (k := k) (C := C) K) k) :=
    enoughProjectives_of_finiteRepresentables hP'
  let hPdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) (finiteSupportCategory (k := k) (C := C) K) hP'
        ({x} : Set _) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := ObjectDeletion.DeletionCategory (k := k)
          (finiteSupportCategory (k := k) (C := C) K) ({x} : Set _)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted
  exact finiteCategoryProjectiveGenerator.singletonDeletion_surplus_le_of_fintype
    hP' hlocalRing' hC' hlocal' H' x T Tdeleted

theorem finiteSupportCategory_singletonDeletion_surplus_le
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (hC : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (K : Set C) (hK : K.Finite)
    (x : finiteSupportCategory (k := k) (C := C) K) :
    letI : Finite (finiteSupportCategory (k := k) (C := C) K) :=
      finiteSupportCategory_finite (k := k) (C := C) K hK
    let hP' := finiteSupportCategory_finiteCovariantRepresentables
      (k := k) (C := C) hP K
    let hlocal' := finiteSupportCategory_isLocallyRepresentationFinite
      (k := k) (C := C) hlocal K
    let hlocalRing' := finiteSupportCategory_localEndomorphismRings
      (k := k) (C := C) hC hlocalRing K
    let hC' := finiteSupportCategory_skeletal
      (k := k) (C := C) hC hlocalRing K
    let H' := finiteSupportCategory_directed
      (k := k) (C := C) H K
    letI : EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := finiteSupportCategory (k := k) (C := C) K) k) :=
      enoughProjectives_of_finiteRepresentables hP'
    let hPdeleted' := fun Y ↦
      ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
        (k := k) (finiteSupportCategory (k := k) (C := C) K) hP'
          ({x} : Set _) Y
    letI : EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := ObjectDeletion.DeletionCategory (k := k)
            (finiteSupportCategory (k := k) (C := C) K) ({x} : Set _)) k) :=
      enoughProjectives_of_finiteRepresentables hPdeleted'
    let T := finiteSupportCategory_skeleton
      (k := k) (C := C) hP hlocal K hK
    let Tdeleted := finiteSupportCategory_singleton_skeleton
      (k := k) (C := C) hP hlocal K hK x
    @ARCount.surplus (Fin Tdeleted.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity
          Tdeleted.toFiniteRightTauCategoryData)
        Tdeleted.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) ≤
      @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) := by
  letI : Finite (finiteSupportCategory (k := k) (C := C) K) :=
    finiteSupportCategory_finite (k := k) (C := C) K hK
  letI : Fintype (finiteSupportCategory (k := k) (C := C) K) :=
    Fintype.ofFinite _
  let hP' := finiteSupportCategory_finiteCovariantRepresentables
    (k := k) (C := C) hP K
  let hlocal' := finiteSupportCategory_isLocallyRepresentationFinite
    (k := k) (C := C) hlocal K
  let hlocalRing' := finiteSupportCategory_localEndomorphismRings
    (k := k) (C := C) hC hlocalRing K
  let hC' := finiteSupportCategory_skeletal
    (k := k) (C := C) hC hlocalRing K
  let H' := finiteSupportCategory_directed
    (k := k) (C := C) H K
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := finiteSupportCategory (k := k) (C := C) K) k) :=
    enoughProjectives_of_finiteRepresentables hP'
  let hPdeleted' := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) (finiteSupportCategory (k := k) (C := C) K) hP'
        ({x} : Set _) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := ObjectDeletion.DeletionCategory (k := k)
          (finiteSupportCategory (k := k) (C := C) K) ({x} : Set _)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted'
  let T := finiteSupportCategory_skeleton
    (k := k) (C := C) hP hlocal K hK
  let Tdeleted := finiteSupportCategory_singleton_skeleton
    (k := k) (C := C) hP hlocal K hK x
  exact finiteSupport_singletonDeletion_surplus_le_with_skeletons
    (k := k) (C := C) hP hlocal hlocalRing hC H K hK x T Tdeleted


end MagnitudeConjecture.ObjectDeletion.Frozen
