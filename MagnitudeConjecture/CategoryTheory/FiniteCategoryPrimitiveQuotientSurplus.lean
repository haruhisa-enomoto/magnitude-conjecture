import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotientFiniteSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraSurplus
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraBridge

/-!
# Primitive quotient surplus of literal object deletion

The singleton object-deletion category is equivalent to modules over the
canonical primitive quotient of the finite category algebra.  Pulling back
the label-aligned quotient skeleton through this equivalence identifies its
finite-tau surplus with the intrinsic quotient surplus used by directed
deletion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.CoveringHom

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Fintype C]

namespace finiteCategoryProjectiveGenerator

variable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))

local instance primitiveQuotientSurplusAlgebraFiniteDimensional :
    FiniteDimensional k (algebra hP) :=
  algebra_finiteDimensional hP

local instance primitiveQuotientSurplusAlgebraOppositeIsNoetherian :
    IsNoetherianRing (algebra hP)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k (algebra hP)ᵐᵒᵖ

/-- The surplus of any complete skeleton of the literal singleton-deletion
module category is the actual finite-tau surplus of the corresponding
primitive quotient algebra.  Unlike the intrinsic directed-deletion formula
below, this comparison does not require the ambient module category to be
directed. -/
theorem deletionCategorySkeleton_surplus_eq_primitiveQuotientFinite_ambientARSurplus
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (S : RightModule.FiniteIndecomposableSkeleton k (algebra hP))
    (X : C)
    (T : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C))) :
    letI := enoughProjectives_of_finiteRepresentables
      (fun Y ↦ ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
        (k := k) C hP ({X} : Set C) Y)
    letI : IsNoetherianRing
        (RightModule.primitiveQuotientAlgebra
          (canonicalProjector hP X))ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
      (S.primitiveQuotientFiniteIndecomposableSkeleton
        (canonicalProjector_primitive hP hlocal X)).ambientARSurplus := by
  let D := canonicalProjector_primitive hP hlocal X
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra
        (canonicalProjector hP X))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let hPdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP ({X} : Set C) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted
  let E := deletionPrimitiveQuotientEquivalence hP X
  letI : E.functor.Additive :=
    { map_add := by
        intro M N f g
        apply ObjectProperty.hom_ext
        rfl }
  let Q := S.primitiveQuotientFiniteIndecomposableSkeleton D
  exact categorySkeleton_surplus_eq_ambientARSurplus_of_equivalence E T Q

/-- The surplus of any complete skeleton of the literal singleton-deletion
module category is the intrinsic primitive-quotient surplus of the matching
canonical category-algebra projector. -/
theorem deletionCategorySkeleton_surplus_eq_primitiveQuotientARSurplus
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (S : RightModule.FiniteIndecomposableSkeleton k (algebra hP))
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (X : C)
    (T : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C))) :
    letI := enoughProjectives_of_finiteRepresentables
      (fun Y ↦ ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
        (k := k) C hP ({X} : Set C) Y)
    @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
      S.primitiveQuotientARSurplus
        (canonicalProjector_primitive hP hlocal X) := by
  let D := canonicalProjector_primitive hP hlocal X
  let B := RightModule.primitiveQuotientAlgebra (canonicalProjector hP X)
  letI : FiniteDimensional k B := inferInstance
  letI : IsNoetherianRing Bᵐᵒᵖ := IsNoetherianRing.of_finite k Bᵐᵒᵖ
  let hPdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP ({X} : Set C) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted
  let E := deletionPrimitiveQuotientEquivalence hP X
  letI : E.functor.Additive :=
    { map_add := by
        intro M N f g
        apply ObjectProperty.hom_ext
        rfl }
  let Q := S.primitiveQuotientFiniteIndecomposableSkeleton D
  exact (deletionCategorySkeleton_surplus_eq_primitiveQuotientFinite_ambientARSurplus
    hP hlocal S X T).trans
      (S.primitiveQuotientFinite_ambientARSurplus_eq D H)

/-- Literal singleton object deletion cannot increase finite-tau surplus in a
finite representation-directed category.  All algebra, skeleton, primitive
presentation, coordinate, and boundary data are constructed internally. -/
theorem singletonDeletion_surplus_le
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hskel : Skeletal C)
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C))
    (X : C)
    (T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
    (Tdeleted : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C))) :
    letI := enoughProjectives_of_finiteRepresentables hP
    letI := enoughProjectives_of_finiteRepresentables
      (fun Y ↦ ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
        (k := k) C hP ({X} : Set C) Y)
    @ARCount.surplus (Fin Tdeleted.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity
          Tdeleted.toFiniteRightTauCategoryData)
        Tdeleted.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) ≤
      @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) := by
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  let hPdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP ({X} : Set C) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted
  let hA := algebra_isRepresentationFinite hP hrep
  let S := Classical.choice
    (RightModule.FiniteIndecomposableSkeleton.exists_of_isRepresentationFinite hA)
  let Halg := algebraSkeleton_hasAcyclicNonzeroNonisomorphisms hP H S
  let P := primitiveProjectivePresentation hP hlocal S hskel
  let p := canonicalSourceLabel hP hlocal S X
  have hpObject :
      (canonicalSourceEquiv hP hlocal S hskel).symm p = X :=
    (canonicalSourceEquiv hP hlocal S hskel).symm_apply_apply X
  have hmono :=
    S.primitiveQuotientARSurplus_le_ambientARSurplus P p hA Halg
  change S.primitiveQuotientARSurplus
      (canonicalProjector_primitive hP hlocal
        ((canonicalSourceEquiv hP hlocal S hskel).symm p)) ≤
    S.ambientARSurplus at hmono
  rw [hpObject] at hmono
  calc
    @ARCount.surplus (Fin Tdeleted.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity
            Tdeleted.toFiniteRightTauCategoryData)
          Tdeleted.toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) =
        S.primitiveQuotientARSurplus
          (canonicalProjector_primitive hP hlocal X) :=
      deletionCategorySkeleton_surplus_eq_primitiveQuotientARSurplus
        hP hlocal S Halg X Tdeleted
    _ ≤ S.ambientARSurplus := hmono
    _ = @ARCount.surplus (Fin T.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) :=
      (categorySkeleton_surplus_eq_ambientARSurplus hP T S).symm

/-- If singleton deletion preserves surplus, then every indecomposable module
which is nonzero at the deleted object has one-dimensional fiber there.  This
is the literal category-module form of primitive-deletion equality rigidity.
-/
theorem finrank_obj_eq_one_of_singletonDeletion_surplus_eq
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hskel : Skeletal C)
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C))
    (X : C)
    (T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
    (Tdeleted : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)))
    (hEquality :
      letI := enoughProjectives_of_finiteRepresentables hP
      letI := enoughProjectives_of_finiteRepresentables
        (fun Y ↦ ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
          (k := k) C hP ({X} : Set C) Y)
      @ARCount.surplus (Fin Tdeleted.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity
            Tdeleted.toFiniteRightTauCategoryData)
          Tdeleted.toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) =
        @ARCount.surplus (Fin T.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _))
    (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k)
    (hM : Indecomposable M)
    (hMX : ¬ IsZero (M.obj.obj.obj X)) :
    Module.finrank k (M.obj.obj.obj X) = 1 := by
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  let hPdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP ({X} : Set C) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted
  let hA := algebra_isRepresentationFinite hP hrep
  let S := Classical.choice
    (RightModule.FiniteIndecomposableSkeleton.exists_of_isRepresentationFinite hA)
  let Halg := algebraSkeleton_hasAcyclicNonzeroNonisomorphisms hP H S
  let P := primitiveProjectivePresentation hP hlocal S hskel
  let p := canonicalSourceLabel hP hlocal S X
  have hpObject :
      (canonicalSourceEquiv hP hlocal S hskel).symm p = X :=
    (canonicalSourceEquiv hP hlocal S hskel).symm_apply_apply X
  let E := moduleEquivalence hP
  letI : E.functor.Additive :=
    { map_add := by
        intro U V f g
        change (representedFGFunctor hP).map (f + g) =
          (representedFGFunctor hP).map f +
            (representedFGFunctor hP).map g
        exact (representedFGFunctor hP).map_add }
  have hMap : Indecomposable (E.functor.obj M) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor M).2 hM
  obtain ⟨i, ⟨eM⟩⟩ := S.fgObj_complete (E.functor.obj M) hMap
  have hdim :
      S.primitiveMultiplicity (canonicalProjector_primitive hP hlocal X) i =
        Module.finrank k (M.obj.obj.obj X) :=
    primitiveMultiplicity_eq_finrank_obj hP hlocal S X M i eM
  have hfinrank_ne : Module.finrank k (M.obj.obj.obj X) ≠ 0 := by
    intro hzero
    apply hMX
    rw [ModuleCat.isZero_iff_subsingleton]
    exact Module.finrank_zero_iff.mp hzero
  have hiSurvives :
      i ∉ S.primitiveKilledLabels
        (canonicalProjector_primitive hP hlocal X) := by
    intro hi
    have hzero :=
      (S.mem_primitiveKilledLabels_iff_primitiveMultiplicity_zero
        (canonicalProjector_primitive hP hlocal X) i).1 hi
    apply hfinrank_ne
    rw [← hdim]
    exact hzero
  have hAlgEquality :
      S.ambientARSurplus =
        S.primitiveQuotientARSurplus
          (canonicalProjector_primitive hP hlocal X) := by
    rw [← categorySkeleton_surplus_eq_ambientARSurplus hP T S,
      ← deletionCategorySkeleton_surplus_eq_primitiveQuotientARSurplus
        hP hlocal S Halg X Tdeleted]
    exact hEquality.symm
  have hAlgEqualityP :
      S.ambientARSurplus = S.primitiveQuotientARSurplus (P.primitive p) := by
    change S.ambientARSurplus =
      S.primitiveQuotientARSurplus
        (canonicalProjector_primitive hP hlocal
          ((canonicalSourceEquiv hP hlocal S hskel).symm p))
    rw [hpObject]
    exact hAlgEquality
  have hiSurvivesP :
      i ∉ S.primitiveKilledLabels (P.primitive p) := by
    change i ∉ S.primitiveKilledLabels
      (canonicalProjector_primitive hP hlocal
        ((canonicalSourceEquiv hP hlocal S hskel).symm p))
    rw [hpObject]
    exact hiSurvives
  have hrigid :=
    S.primitiveMultiplicity_eq_one_of_ambientARSurplus_eq_primitiveQuotientARSurplus
      P p hA Halg hAlgEqualityP ⟨i, hiSurvivesP⟩
  change S.primitiveMultiplicity
      (canonicalProjector_primitive hP hlocal
        ((canonicalSourceEquiv hP hlocal S hskel).symm p)) i = 1 at hrigid
  rw [hpObject] at hrigid
  exact hdim.symm.trans hrigid

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
