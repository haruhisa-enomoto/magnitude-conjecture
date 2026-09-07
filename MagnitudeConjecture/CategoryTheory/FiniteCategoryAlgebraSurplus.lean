import MagnitudeConjecture.Algebra.RightModulePrimitiveDirectedDeletion
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitiveDeletion
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleRightTau
import MagnitudeConjecture.CategoryTheory.FiniteSkeletonDensityInvariance
import MagnitudeConjecture.CategoryTheory.FiniteSkeletonShiftAction
import MagnitudeConjecture.CategoryTheory.FiniteTauSurplusEquivalence

/-!
# Finite category and algebra Auslander--Reiten surplus

The projective-generator equivalence pulls a finite algebra-module skeleton
back to a duplicate-free complete skeleton of finite category modules.  The
generic finite-tau equivalence theorem then identifies its surplus with the
literal ambient algebra surplus used by primitive directed deletion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.CoveringHom

universe u

variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable {A : Type u} [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- Pull a duplicate-free complete algebra-module skeleton back along an
additive equivalence from finite category modules. -/
def pullbackRightModuleIndecomposableSkeleton
    (E : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k ≌
      RightModule.FinitelyGeneratedCategory A)
    [E.functor.Additive]
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C) := by
  letI : E.inverse.Additive := inferInstance
  refine
    { n := S.n
      obj := fun i ↦ E.inverse.obj (S.fgObj i)
      indecomposable := ?_
      skeletal := ?_
      complete := ?_ }
  · intro i
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.inverse (S.fgObj i)).2 (S.fgObj_indecomposable i)
  · intro i j hij
    obtain ⟨hij⟩ := hij
    apply S.fgObj_skeletal
    exact ⟨(E.counitIso.app (S.fgObj i)).symm ≪≫
      E.functor.mapIso hij ≪≫ E.counitIso.app (S.fgObj j)⟩
  · intro M hM
    have hMap : Indecomposable (E.functor.obj M) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.functor M).2 hM
    obtain ⟨i, ⟨hi⟩⟩ := S.fgObj_complete (E.functor.obj M) hMap
    exact ⟨i, ⟨E.unitIso.app M ≪≫ E.inverse.mapIso hi⟩⟩

/-- The counit matches the objects of the pulled-back category skeleton with
the original finitely generated algebra-module skeleton. -/
def pullbackRightModuleIndecomposableSkeletonObjIso
    (E : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k ≌
      RightModule.FinitelyGeneratedCategory A)
    [E.functor.Additive]
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (i : Fin S.n) :
    E.functor.obj ((pullbackRightModuleIndecomposableSkeleton E S).obj i) ≅
      S.fgObj i := by
  simpa [pullbackRightModuleIndecomposableSkeleton] using
    E.counitIso.app (S.fgObj i)

/-- Pullback through any additive equivalence preserves the official
finite-tau surplus of a complete algebra-module skeleton. -/
theorem pullbackRightModuleIndecomposableSkeleton_surplus_eq_ambientARSurplus
    (E : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k ≌
      RightModule.FinitelyGeneratedCategory A)
    [E.functor.Additive]
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k)]
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    @ARCount.surplus (Fin S.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity
          (pullbackRightModuleIndecomposableSkeleton E S).toFiniteRightTauCategoryData)
        ((pullbackRightModuleIndecomposableSkeleton E S).toFiniteRightTauCategoryData).IsProjective
        (Classical.decPred _) =
      S.ambientARSurplus := by
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let T :=
    (pullbackRightModuleIndecomposableSkeleton E S).toFiniteRightTauCategoryData
  let U := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  have htransport := FiniteTauMatrix.surplus_eq_of_equivalence
    T U E (Equiv.refl (Fin S.n))
      (pullbackRightModuleIndecomposableSkeletonObjIso E S)
  have hprojective :
      U.IsProjective = fun i ↦ Projective (S.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj U i
  rw [hprojective] at htransport
  exact htransport

/-- Consequently, any complete finite category-module skeleton has the
ambient algebra surplus of a complete algebra-module skeleton across an
additive equivalence. -/
theorem categorySkeleton_surplus_eq_ambientARSurplus_of_equivalence
    (E : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k ≌
      RightModule.FinitelyGeneratedCategory A)
    [E.functor.Additive]
    [EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k)]
    (T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
      S.ambientARSurplus := by
  calc
    @ARCount.surplus (Fin T.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
        @ARCount.surplus
          (Fin (pullbackRightModuleIndecomposableSkeleton E S).n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity
            (pullbackRightModuleIndecomposableSkeleton E S).toFiniteRightTauCategoryData)
          ((pullbackRightModuleIndecomposableSkeleton E S).toFiniteRightTauCategoryData).IsProjective
          (Classical.decPred _) := by
      rw [← T.sum_rightTauLocalDensity_eq_surplus,
        ← (pullbackRightModuleIndecomposableSkeleton E S).sum_rightTauLocalDensity_eq_surplus]
      exact T.sum_rightTauLocalDensity_eq
        (pullbackRightModuleIndecomposableSkeleton E S)
    _ = S.ambientARSurplus :=
      pullbackRightModuleIndecomposableSkeleton_surplus_eq_ambientARSurplus E S

namespace finiteCategoryProjectiveGenerator

variable [Fintype C]
variable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))

local instance finiteCategoryAlgebraSurplusFiniteDimensional :
    FiniteDimensional k (algebra hP) :=
  algebra_finiteDimensional hP

local instance finiteCategoryAlgebraSurplusOppositeIsNoetherian :
    IsNoetherianRing (algebra hP)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k (algebra hP)ᵐᵒᵖ

/-- The algebra skeleton, viewed back inside the finite category module
category through the projective-generator equivalence. -/
def algebraPullbackSkeleton
    (S : RightModule.FiniteIndecomposableSkeleton k (algebra hP)) :
    FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C) := by
  let E := moduleEquivalence hP
  letI : E.functor.Additive :=
    { map_add := by
        intro X Y f g
        change (representedFGFunctor hP).map (f + g) =
          (representedFGFunctor hP).map f +
            (representedFGFunctor hP).map g
        exact (representedFGFunctor hP).map_add }
  exact pullbackRightModuleIndecomposableSkeleton E S

/-- The objectwise counit matching the pulled-back category skeleton with
the original finitely generated algebra-module skeleton. -/
def algebraPullbackSkeletonObjIso
    (S : RightModule.FiniteIndecomposableSkeleton k (algebra hP))
    (i : Fin S.n) :
    (moduleEquivalence hP).functor.obj
        ((algebraPullbackSkeleton hP S).obj i) ≅
      S.fgObj i := by
  let E := moduleEquivalence hP
  change E.functor.obj ((algebraPullbackSkeleton hP S).obj i) ≅ S.fgObj i
  simpa [algebraPullbackSkeleton,
    pullbackRightModuleIndecomposableSkeleton] using
      E.counitIso.app (S.fgObj i)

/-- The pulled-back category skeleton and the original algebra skeleton have
the same Auslander--Reiten surplus. -/
theorem algebraPullbackSkeleton_surplus_eq_ambientARSurplus
    (S : RightModule.FiniteIndecomposableSkeleton k (algebra hP)) :
    letI := enoughProjectives_of_finiteRepresentables hP
    @ARCount.surplus (Fin S.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity
          (algebraPullbackSkeleton hP S).toFiniteRightTauCategoryData)
        (algebraPullbackSkeleton hP S).toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) =
      S.ambientARSurplus := by
  let E := moduleEquivalence hP
  letI : E.functor.Additive :=
    { map_add := by
        intro X Y f g
        change (representedFGFunctor hP).map (f + g) =
          (representedFGFunctor hP).map f +
            (representedFGFunctor hP).map g
        exact (representedFGFunctor hP).map_add }
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory (algebra hP)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives (algebra hP)ᵐᵒᵖ
  let T := (algebraPullbackSkeleton hP S).toFiniteRightTauCategoryData
  let U := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  have htransport := FiniteTauMatrix.surplus_eq_of_equivalence
    T U E (Equiv.refl (Fin S.n))
      (algebraPullbackSkeletonObjIso hP S)
  have hprojective :
      U.IsProjective = fun i ↦ Projective (S.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj U i
  rw [hprojective] at htransport
  exact htransport

/-- The surplus of any complete finite indecomposable category-module
skeleton is the ambient surplus of any complete algebra-module skeleton under
the projective-generator equivalence. -/
theorem categorySkeleton_surplus_eq_ambientARSurplus
    (T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
    (S : RightModule.FiniteIndecomposableSkeleton k (algebra hP)) :
    letI := enoughProjectives_of_finiteRepresentables hP
    @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
      S.ambientARSurplus := by
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  calc
    @ARCount.surplus (Fin T.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
        @ARCount.surplus (Fin (algebraPullbackSkeleton hP S).n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity
            (algebraPullbackSkeleton hP S).toFiniteRightTauCategoryData)
          (algebraPullbackSkeleton hP S).toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) := by
      rw [← T.sum_rightTauLocalDensity_eq_surplus,
        ← (algebraPullbackSkeleton hP S).sum_rightTauLocalDensity_eq_surplus]
      exact T.sum_rightTauLocalDensity_eq (algebraPullbackSkeleton hP S)
    _ = S.ambientARSurplus :=
      algebraPullbackSkeleton_surplus_eq_ambientARSurplus hP S

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
