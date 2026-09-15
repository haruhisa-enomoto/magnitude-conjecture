import MagnitudeConjecture.Algebra.RightModuleF1EqualityThin
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPointwiseThinBiserial
import MagnitudeConjecture.CategoryTheory.F1FiniteObjectDeletion
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDuality
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownBiserial

/-!
# Biserial representables on the standard-form universal cover

At magnitude equality, every finite-dimensional indecomposable module on the
opposite projective source category is pointwise thin.  Coefficient duality
gives the same statement in the other variance.  Finite object-support
deletion, the direct biserial induction, and extension by zero then prove
intrinsic biseriality of both right and left representables on the universal
cover.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMagnitudeEqualityBiserialCoverQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormMagnitudeEqualityBiserialCoverArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- At equality, every representable on a finite object-deletion quotient of
the opposite projective source category is intrinsically biserial. -/
theorem
    standardFormCoveringDeletion_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (U : Set ((StandardFormProjectiveSourceCategory S x₀)ᵒᵖ))
    (hUfinite : U.Finite)
    (X : ObjectDeletion.DeletionCategory (k := k)
      ((StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) Uᶜ) :
    IsBiserialObject
      ((CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k)
        (ObjectDeletion.isLocallyBounded_deletion
          (k := k) Uᶜ
          (standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀)).finiteCovariantRepresentables).obj
          (Opposite.op X)) := by
  let C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
  let H := standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀
  let hD := ObjectDeletion.isLocallyBounded_deletion (k := k) Uᶜ H
  letI : Finite (ObjectDeletion.DeletionCategory (k := k) C Uᶜ) :=
    ObjectDeletion.finite_deletion_of_finite_survivors (k := k) (C := C) U hUfinite
  letI : Fintype (ObjectDeletion.DeletionCategory (k := k) C Uᶜ) :=
    Fintype.ofFinite _
  exact CoveringHom.finiteCovariantRepresentable_isBiserialObject_of_pointwiseThin
    hD.finiteCovariantRepresentables hD.localEndomorphismRings
    (by
      intro M hM
      exact standardFormCoveringDeletion_isPointwiseThin_of_ambientARSurplus_eq_zero
        S x₀ hconnected hzero Uᶜ M hM)
    X

/-- At equality, every right representable of the universal cover is
intrinsically biserial.  In the opposite projective source category this is
the covariant representable at the corresponding object. -/
theorem
    standardFormCovering_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (X : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    IsBiserialObject
      ((CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k)
        (standardFormOppositeProjectiveSourceCategoryIsLocallyBounded
          S x₀).finiteCovariantRepresentables).obj (Opposite.op X)) := by
  let C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
  let H := standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀
  let hP := H.finiteCovariantRepresentables
  let M := (CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
    (Opposite.op X)
  let T : Set C := {X} ∪ CoveringHom.moduleSupport k M.obj.obj
  have hTfinite : T.Finite :=
    (Set.finite_singleton X).union M.property.2
  have hX : X ∈ T := by simp [T]
  have hXdeleted : X ∉ Tᶜ := by
    simpa only [Set.mem_compl_iff, not_not] using hX
  let XU : ObjectDeletion.DeletionCategory (k := k) C Tᶜ :=
    ObjectDeletion.survivingObj (k := k) C Tᶜ hXdeleted
  let hD := ObjectDeletion.isLocallyBounded_deletion (k := k) Tᶜ H
  letI : Finite (ObjectDeletion.DeletionCategory (k := k) C Tᶜ) :=
    ObjectDeletion.finite_deletion_of_finite_survivors (k := k) (C := C) T hTfinite
  letI : Fintype (ObjectDeletion.DeletionCategory (k := k) C Tᶜ) :=
    Fintype.ofFinite _
  let hPU := hD.finiteCovariantRepresentables
  have hsupport : CoveringHom.moduleSupport k M.obj.obj ⊆ T := by
    intro Y hY
    exact Or.inr hY
  let hvanish : ObjectDeletion.ModuleVanishesOnDeleted
      (k := k) C Tᶜ M.obj.obj := by
    intro Y hY
    rw [ModuleCat.isZero_iff_subsingleton]
    exact not_nontrivial_iff_subsingleton.mp fun hnontrivial ↦
      hY (hsupport hnontrivial)
  let R := ObjectDeletion.finiteDimensionalModuleRestrictionToDeletion
    (k := k) C Tᶜ M hvanish
  have hlocal : IsBiserialObject
      ((CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hPU).obj
        (Opposite.op XU)) :=
    standardFormCoveringDeletion_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero T hTfinite XU
  have hR : IsBiserialObject R := by
    let i := ObjectDeletion.deletionRepresentableRestrictionIso
      (k := k) (C := C) hP T XU hsupport
    exact hlocal.congr i
  have hExt : IsBiserialObject
      ((ObjectDeletion.finiteDimensionalModuleExtensionByZero
        (k := k) C Tᶜ).obj R) :=
    ObjectDeletion.IsBiserialObject.finiteDimensionalModuleExtensionByZero
      C Tᶜ hR
  exact hExt.congr
    (ObjectDeletion.finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C Tᶜ M hvanish)

/-- Coefficient duality transfers the equality-case pointwise-thin theorem
from the opposite projective source category to the projective source
category itself. -/
theorem
    standardFormProjectiveSourceCovering_isPointwiseThin_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := StandardFormProjectiveSourceCategory S x₀) k)
    (hM : Indecomposable M) :
    CoveringHom.IsPointwiseThin M.obj.obj := by
  let D := (CoveringHom.finiteCoefficientDualFunctor
    (k := k) (C := StandardFormProjectiveSourceCategory S x₀)).obj
      (Opposite.op M)
  have hD : Indecomposable D :=
    (CoveringHom.finiteCoefficientDualFunctor_indec_iff M).2 hM
  have hthinD : CoveringHom.IsPointwiseThin D.obj.obj :=
    standardFormCovering_isPointwiseThin_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero D hD
  change CoveringHom.IsPointwiseThin
    (CoveringHom.coefficientDualModule (k := k) M.obj).obj at hthinD
  exact (CoveringHom.coefficientDualModule_isPointwiseThin_iff M).mp hthinD

/-- Pointwise thinness in the left-module variance descends to every
object-deletion stage. -/
theorem
    standardFormProjectiveSourceCoveringDeletion_isPointwiseThin_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (D : Set (StandardFormProjectiveSourceCategory S x₀))
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := ObjectDeletion.DeletionCategory (k := k)
        (StandardFormProjectiveSourceCategory S x₀) D) k)
    (hM : Indecomposable M) :
    CoveringHom.IsPointwiseThin M.obj.obj := by
  let C := StandardFormProjectiveSourceCategory S x₀
  let E := ObjectDeletion.finiteDimensionalModuleExtensionByZero
    (k := k) C D
  have hEM : Indecomposable (E.obj M) :=
    ObjectDeletion.finiteDimensionalModuleExtensionByZero_indec
      (k := k) C D M hM
  have hthin : CoveringHom.IsPointwiseThin (E.obj M).obj.obj :=
    standardFormProjectiveSourceCovering_isPointwiseThin_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero (E.obj M) hEM
  exact ObjectDeletion.isPointwiseThin_of_extensionByZero
    (k := k) C D M.obj hthin

/-- At equality, every representable on a finite object-deletion quotient of
the projective source category is intrinsically biserial. -/
theorem
    standardFormProjectiveSourceDeletion_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (U : Set (StandardFormProjectiveSourceCategory S x₀))
    (hUfinite : U.Finite)
    (X : ObjectDeletion.DeletionCategory (k := k)
      (StandardFormProjectiveSourceCategory S x₀) Uᶜ) :
    IsBiserialObject
      ((CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k)
        (ObjectDeletion.isLocallyBounded_deletion
          (k := k) Uᶜ
          (standardFormProjectiveSourceCategoryIsLocallyBounded S x₀)).finiteCovariantRepresentables).obj
          (Opposite.op X)) := by
  let C := StandardFormProjectiveSourceCategory S x₀
  let H := standardFormProjectiveSourceCategoryIsLocallyBounded S x₀
  let hD := ObjectDeletion.isLocallyBounded_deletion (k := k) Uᶜ H
  letI : Finite (ObjectDeletion.DeletionCategory (k := k) C Uᶜ) :=
    ObjectDeletion.finite_deletion_of_finite_survivors (k := k) (C := C) U hUfinite
  letI : Fintype (ObjectDeletion.DeletionCategory (k := k) C Uᶜ) :=
    Fintype.ofFinite _
  exact CoveringHom.finiteCovariantRepresentable_isBiserialObject_of_pointwiseThin
    hD.finiteCovariantRepresentables hD.localEndomorphismRings
    (by
      intro M hM
      exact standardFormProjectiveSourceCoveringDeletion_isPointwiseThin_of_ambientARSurplus_eq_zero
        S x₀ hconnected hzero Uᶜ M hM)
    X

/-- At equality, every left representable of the universal cover is
intrinsically biserial. -/
theorem
    standardFormProjectiveSource_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (X : StandardFormProjectiveSourceCategory S x₀) :
    IsBiserialObject
      ((CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k)
        (standardFormProjectiveSourceCategoryIsLocallyBounded
          S x₀).finiteCovariantRepresentables).obj (Opposite.op X)) := by
  let C := StandardFormProjectiveSourceCategory S x₀
  let H := standardFormProjectiveSourceCategoryIsLocallyBounded S x₀
  let hP := H.finiteCovariantRepresentables
  let M := (CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
    (Opposite.op X)
  let T : Set C := {X} ∪ CoveringHom.moduleSupport k M.obj.obj
  have hTfinite : T.Finite :=
    (Set.finite_singleton X).union M.property.2
  have hX : X ∈ T := by simp [T]
  have hXdeleted : X ∉ Tᶜ := by
    simpa only [Set.mem_compl_iff, not_not] using hX
  let XU : ObjectDeletion.DeletionCategory (k := k) C Tᶜ :=
    ObjectDeletion.survivingObj (k := k) C Tᶜ hXdeleted
  let hD := ObjectDeletion.isLocallyBounded_deletion (k := k) Tᶜ H
  letI : Finite (ObjectDeletion.DeletionCategory (k := k) C Tᶜ) :=
    ObjectDeletion.finite_deletion_of_finite_survivors (k := k) (C := C) T hTfinite
  letI : Fintype (ObjectDeletion.DeletionCategory (k := k) C Tᶜ) :=
    Fintype.ofFinite _
  let hPU := hD.finiteCovariantRepresentables
  have hsupport : CoveringHom.moduleSupport k M.obj.obj ⊆ T := by
    intro Y hY
    exact Or.inr hY
  let hvanish : ObjectDeletion.ModuleVanishesOnDeleted
      (k := k) C Tᶜ M.obj.obj := by
    intro Y hY
    rw [ModuleCat.isZero_iff_subsingleton]
    exact not_nontrivial_iff_subsingleton.mp fun hnontrivial ↦
      hY (hsupport hnontrivial)
  let R := ObjectDeletion.finiteDimensionalModuleRestrictionToDeletion
    (k := k) C Tᶜ M hvanish
  have hlocal : IsBiserialObject
      ((CoveringHom.finiteDimensionalLinearCoyonedaFunctor (k := k) hPU).obj
        (Opposite.op XU)) :=
    standardFormProjectiveSourceDeletion_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero T hTfinite XU
  have hR : IsBiserialObject R := by
    let i := ObjectDeletion.deletionRepresentableRestrictionIso
      (k := k) (C := C) hP T XU hsupport
    exact hlocal.congr i
  have hExt : IsBiserialObject
      ((ObjectDeletion.finiteDimensionalModuleExtensionByZero
        (k := k) C Tᶜ).obj R) :=
    ObjectDeletion.IsBiserialObject.finiteDimensionalModuleExtensionByZero
      C Tᶜ hR
  exact hExt.congr
    (ObjectDeletion.finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C Tᶜ M hvanish)

/-- At equality, pushing a right representable through the opposite
projective deck covering produces a biserial object. -/
theorem
    standardFormOppositeProjective_pushdown_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (X : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    let H := standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀
    let hP := H.finiteCovariantRepresentables
    let D₀ := standardFormOppositeProjectiveDeckShift S x₀
    let D := D₀.ulift.{0, u, 0, u}
    letI := D₀.hasShift
    letI := D₀.additiveShift
    letI := D₀.linearShift (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    IsBiserialObject
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        (CoveringHom.finiteDimensionalLinearCoyoneda
          (k := k) X (hP X))) := by
  let H := standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀
  let hP := H.finiteCovariantRepresentables
  let hlocal := H.localEndomorphismRings
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI : IsMulTorsionFree
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  change IsBiserialObject
    ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) X (hP X)))
  apply
    D.finiteDimensionalModuleOrbitSkeletonPushdown_biserial_representable
      hP hlocal hfree X
  exact
    standardFormCovering_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero X

/-- The same descent in the opposite variance gives the pushed left
representables. -/
theorem
    standardFormProjectiveSource_pushdown_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (X : StandardFormProjectiveSourceCategory S x₀) :
    let H := standardFormProjectiveSourceCategoryIsLocallyBounded S x₀
    let hP := H.finiteCovariantRepresentables
    let D₀ := standardFormProjectiveDeckShift S x₀
    let D := D₀.ulift.{0, u, 0, u}
    letI := D₀.hasShift
    letI := D₀.additiveShift
    letI := D₀.linearShift (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    IsBiserialObject
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        (CoveringHom.finiteDimensionalLinearCoyoneda
          (k := k) X (hP X))) := by
  let H := standardFormProjectiveSourceCategoryIsLocallyBounded S x₀
  let hP := H.finiteCovariantRepresentables
  let hlocal := H.localEndomorphismRings
  let D₀ := standardFormProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI : IsMulTorsionFree
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  change IsBiserialObject
    ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) X (hP X)))
  apply
    D.finiteDimensionalModuleOrbitSkeletonPushdown_biserial_representable
      hP hlocal hfree X
  exact
    standardFormProjectiveSource_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero X

/-- Hence every right representable on the lifted strict orbit skeleton is
biserial. -/
theorem
    standardFormOppositeProjective_orbitSkeleton_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (q : MulAction.orbitRel.Quotient
      (ULift.{u}
        (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
          S.standardFormRightMeshData x₀))
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    let H := standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀
    let hP := H.finiteCovariantRepresentables
    let D₀ := standardFormOppositeProjectiveDeckShift S x₀
    let D := D₀.ulift.{0, u, 0, u}
    letI := D₀.hasShift
    letI := D₀.additiveShift
    letI := D₀.linearShift (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
    let Q : CoveringHom.DeckOrbitSkeleton
        (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
        (ULift.{u}
          (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
            S.standardFormRightMeshData x₀)) := q
    IsBiserialObject
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) Q (hP' Q)) := by
  let H := standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀
  let hP := H.finiteCovariantRepresentables
  let hlocal := H.localEndomorphismRings
  let D₀ := standardFormOppositeProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI : IsMulTorsionFree
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  apply D.orbitSkeleton_finiteDimensionalLinearCoyoneda_biserial
    hP hlocal hfree
  intro X
  exact
    standardFormCovering_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero X

/-- Every left representable on the lifted strict orbit skeleton is
biserial as well. -/
theorem
    standardFormProjectiveSource_orbitSkeleton_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (q : MulAction.orbitRel.Quotient
      (ULift.{u}
        (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
          S.standardFormRightMeshData x₀))
      (StandardFormProjectiveSourceCategory S x₀)) :
    let H := standardFormProjectiveSourceCategoryIsLocallyBounded S x₀
    let hP := H.finiteCovariantRepresentables
    let D₀ := standardFormProjectiveDeckShift S x₀
    let D := D₀.ulift.{0, u, 0, u}
    letI := D₀.hasShift
    letI := D₀.additiveShift
    letI := D₀.linearShift (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
    let Q : CoveringHom.DeckOrbitSkeleton
        (StandardFormProjectiveSourceCategory S x₀)
        (ULift.{u}
          (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
            S.standardFormRightMeshData x₀)) := q
    IsBiserialObject
      (CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) Q (hP' Q)) := by
  let H := standardFormProjectiveSourceCategoryIsLocallyBounded S x₀
  let hP := H.finiteCovariantRepresentables
  let hlocal := H.localEndomorphismRings
  let D₀ := standardFormProjectiveDeckShift S x₀
  let D := D₀.ulift.{0, u, 0, u}
  letI : IsMulTorsionFree
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) :=
    S.standardForm_fundamentalGroup_isMulTorsionFree x₀ hconnected
  letI := D₀.hasShift
  letI := D₀.additiveShift
  letI := D₀.linearShift (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  apply D.orbitSkeleton_finiteDimensionalLinearCoyoneda_biserial
    hP hlocal hfree
  intro X
  exact
    standardFormProjectiveSource_covariantRepresentable_isBiserialObject_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero X

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
