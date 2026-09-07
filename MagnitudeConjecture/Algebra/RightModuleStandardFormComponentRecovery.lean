import MagnitudeConjecture.Algebra.RightModuleStandardFormComponentExtension
import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleInheritance

/-!
# Recovery of standard-form component representables

Global restricted representables supported on one augmented-walk component
vanish on all projectives outside that component.  Restriction to the
corresponding deletion category identifies them with the intrinsic component
representables.  Consequently, extension by zero of component restricted
Yoneda is naturally isomorphic to global restricted Yoneda after component
inclusion.
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

local instance componentRecoveryQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance componentRecoveryArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- A global restricted representable whose representing vertex lies in one
walk component vanishes on all projectives outside that component. -/
theorem standardFormRestrictedYoneda_component_vanishesOnComplement
    (c : S.StandardFormWalkComponent)
    (X : S.StandardFormComponentMeshCategory (k := k) c) :
    ObjectDeletion.ModuleVanishesOnDeleted
      (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
      (S.standardFormOppositeProjectiveComplement c)
      (((S.standardFormRestrictedYonedaFunctor
        S.standardFormMeshHomFinite).obj
          ((S.standardFormComponentMeshInclusion (k := k) c).obj X)).obj.obj) := by
  intro P hP
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro f g
  apply sub_eq_zero.mp
  have hclass :
      S.standardFormWalkComponentClass P.unop.1 ≠
        S.standardFormWalkComponentClass X.1 := by
    intro h
    exact hP (h.trans X.2)
  exact S.standardForm_meshHom_eq_zero_of_walkComponentClass_ne
    hclass (f - g)

/-- Restriction of the global representable to the deletion model of its
component. -/
def standardFormComponentGlobalYonedaDeletionModule
    (c : S.StandardFormWalkComponent)
    (X : S.StandardFormComponentMeshCategory (k := k) c) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.StandardFormComponentOppositeProjectiveDeletionCategory
        (k := k) c) k :=
  ObjectDeletion.finiteDimensionalModuleRestrictionToDeletion
    (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
    (S.standardFormOppositeProjectiveComplement c)
    ((S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).obj
        ((S.standardFormComponentMeshInclusion (k := k) c).obj X))
    (S.standardFormRestrictedYoneda_component_vanishesOnComplement
      (k := k) c X)

set_option maxHeartbeats 800000 in
/-- The deletion restrictions of global component representables, functorial
in their representing component vertex. -/
def standardFormComponentGlobalYonedaDeletionFunctor
    (c : S.StandardFormWalkComponent) :
    S.StandardFormComponentMeshCategory (k := k) c ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.StandardFormComponentOppositeProjectiveDeletionCategory
          (k := k) c) k where
  obj X := S.standardFormComponentGlobalYonedaDeletionModule
    (k := k) c X
  map {X Y} f := by
    let MX := (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).obj
        ((S.standardFormComponentMeshInclusion (k := k) c).obj X)
    let MY := (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).obj
        ((S.standardFormComponentMeshInclusion (k := k) c).obj Y)
    let hMX :=
      S.standardFormRestrictedYoneda_component_vanishesOnComplement
        (k := k) c X
    let hMY :=
      S.standardFormRestrictedYoneda_component_vanishesOnComplement
        (k := k) c Y
    apply ObjectProperty.homMk
    apply ObjectProperty.homMk
    let alpha := (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).map
        ((S.standardFormComponentMeshInclusion (k := k) c).map f)
    exact
      { app := fun P ↦ alpha.hom.hom.app P.obj.as
        naturality := by
          intro P Q q
          obtain ⟨g, hg⟩ :=
            (ObjectDeletion.rawFunctor (k := k)
              S.StandardFormProjectiveMeshCategoryᵒᵖ
              (S.standardFormOppositeProjectiveComplement c)).map_surjective q.hom
          change
            ((ObjectDeletion.ideal (k := k)
              S.StandardFormProjectiveMeshCategoryᵒᵖ
              (S.standardFormOppositeProjectiveComplement c)).quotientLift
                MX.obj.obj
                (ObjectDeletion.module_isKilledBy_of_vanishesOnDeleted
                  (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
                  (S.standardFormOppositeProjectiveComplement c)
                  MX.obj.obj hMX)).map q.hom ≫
                    alpha.hom.hom.app Q.obj.as =
              alpha.hom.hom.app P.obj.as ≫
                ((ObjectDeletion.ideal (k := k)
                  S.StandardFormProjectiveMeshCategoryᵒᵖ
                  (S.standardFormOppositeProjectiveComplement c)).quotientLift
                    MY.obj.obj
                    (ObjectDeletion.module_isKilledBy_of_vanishesOnDeleted
                      (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
                      (S.standardFormOppositeProjectiveComplement c)
                      MY.obj.obj hMY)).map q.hom
          rw [← hg]
          exact alpha.hom.hom.naturality g }
  map_id X := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext P
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    rw [(S.standardFormComponentMeshInclusion (k := k) c).map_id]
    have h := congrArg
      (fun t ↦ t.hom.hom.app P.obj.as)
      ((S.standardFormRestrictedYonedaFunctor
        S.standardFormMeshHomFinite).map_id
          ((S.standardFormComponentMeshInclusion (k := k) c).obj X))
    exact ConcreteCategory.congr_hom h q
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext P
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    simp only [Functor.map_comp]
    rfl

/-- After transport from the deletion model to the intrinsic component, the
restricted global representable is the component restricted representable. -/
def standardFormComponentGlobalYonedaDeletionIso
    (c : S.StandardFormWalkComponent)
    (X : S.StandardFormComponentMeshCategory (k := k) c) :
    (S.standardFormComponentDeletionModuleEquivalence
      (k := k) c).functor.obj
        (S.standardFormComponentGlobalYonedaDeletionModule
          (k := k) c X) ≅
      (S.standardFormComponentRestrictedYonedaFunctor (k := k) c).obj X := by
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun P ↦ ?_) ?_
  · change ModuleCat.of k
        (MeshCategory.obj (k := k) S.standardFormRightMeshData P.unop.1.1 ⟶
          MeshCategory.obj (k := k) S.standardFormRightMeshData X.1) ≅
      ModuleCat.of k
        ((show S.StandardFormComponentMeshCategory (k := k) c from P.unop.1) ⟶ X)
    exact (InducedCategory.homLinearEquiv (R := k)
      (X := (show S.StandardFormComponentMeshCategory (k := k) c from P.unop.1))
      (Y := X)).symm.toModuleIso
  · intro P Q f
    rfl

/-- The intrinsic/deletion comparison is natural in the represented vertex. -/
def standardFormComponentGlobalYonedaDeletionNatIso
    (c : S.StandardFormWalkComponent) :
    S.standardFormComponentGlobalYonedaDeletionFunctor (k := k) c ⋙
        (S.standardFormComponentDeletionModuleEquivalence
          (k := k) c).functor ≅
      S.standardFormComponentRestrictedYonedaFunctor (k := k) c :=
  NatIso.ofComponents
    (fun X ↦ S.standardFormComponentGlobalYonedaDeletionIso
      (k := k) c X)
    (by
      intro X Y f
      rfl)

/-- Extension by zero naturally recovers the global representable from its
deletion restriction. -/
def standardFormComponentGlobalYonedaRestrictionExtensionNatIso
    (c : S.StandardFormWalkComponent) :
    S.standardFormComponentGlobalYonedaDeletionFunctor (k := k) c ⋙
        ObjectDeletion.finiteDimensionalModuleExtensionByZero
          (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
          (S.standardFormOppositeProjectiveComplement c) ≅
      S.standardFormComponentMeshInclusion (k := k) c ⋙
        S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite :=
  NatIso.ofComponents
    (fun X ↦ ObjectDeletion.finiteDimensionalModuleRestrictionExtensionIso
      (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
      (S.standardFormOppositeProjectiveComplement c)
      ((S.standardFormRestrictedYonedaFunctor
        S.standardFormMeshHomFinite).obj
          ((S.standardFormComponentMeshInclusion (k := k) c).obj X))
      (S.standardFormRestrictedYoneda_component_vanishesOnComplement
        (k := k) c X))
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext P
      by_cases hP : P ∈ S.standardFormOppositeProjectiveComplement c
      · exact
          (ObjectDeletion.moduleExtensionByZero_obj_isZero_of_mem
            (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
            (S.standardFormOppositeProjectiveComplement c)
            (S.standardFormComponentGlobalYonedaDeletionModule
              (k := k) c X).obj.obj hP).eq_of_src _ _
      · let beta :=
          (S.standardFormComponentGlobalYonedaDeletionFunctor
            (k := k) c).map f
        change
          (ObjectDeletion.moduleExtensionByZeroNatTrans
              (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
              (S.standardFormOppositeProjectiveComplement c)
              beta.hom.hom).app P ≫
              (ObjectDeletion.moduleRestrictionExtensionIsoApp
                (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
                (S.standardFormOppositeProjectiveComplement c)
                ((S.standardFormRestrictedYonedaFunctor
                  S.standardFormMeshHomFinite).obj
                    ((S.standardFormComponentMeshInclusion
                      (k := k) c).obj Y)).obj.obj
                  (S.standardFormRestrictedYoneda_component_vanishesOnComplement
                  (k := k) c Y) P).hom =
            (ObjectDeletion.moduleRestrictionExtensionIsoApp
              (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
              (S.standardFormOppositeProjectiveComplement c)
              ((S.standardFormRestrictedYonedaFunctor
                S.standardFormMeshHomFinite).obj
                  ((S.standardFormComponentMeshInclusion
                    (k := k) c).obj X)).obj.obj
              (S.standardFormRestrictedYoneda_component_vanishesOnComplement
                (k := k) c X) P).hom ≫
              beta.hom.hom.app
                (ObjectDeletion.survivingObj
                  (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
                  (S.standardFormOppositeProjectiveComplement c) hP)
        rw [ObjectDeletion.moduleRestrictionExtensionIsoApp_of_not_mem
              (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
              (S.standardFormOppositeProjectiveComplement c) _ _ hP,
            ObjectDeletion.moduleRestrictionExtensionIsoApp_of_not_mem
              (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
              (S.standardFormOppositeProjectiveComplement c) _ _ hP]
        exact ObjectDeletion.moduleExtensionByZeroObjIso_naturality
          (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
          (S.standardFormOppositeProjectiveComplement c)
          beta.hom.hom hP)

/-- Extension by zero of component restricted Yoneda is naturally the global
restricted Yoneda realization of the component inclusion. -/
def standardFormComponentRestrictedYonedaExtensionNatIso
    (c : S.StandardFormWalkComponent) :
    S.standardFormComponentRestrictedYonedaFunctor (k := k) c ⋙
        S.standardFormComponentModuleExtensionByZero (k := k) c ≅
      S.standardFormComponentMeshInclusion (k := k) c ⋙
        S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite := by
  let R := S.standardFormComponentGlobalYonedaDeletionFunctor (k := k) c
  let E := S.standardFormComponentDeletionModuleEquivalence (k := k) c
  let F := ObjectDeletion.finiteDimensionalModuleExtensionByZero
    (k := k) S.StandardFormProjectiveMeshCategoryᵒᵖ
    (S.standardFormOppositeProjectiveComplement c)
  let e : R ⋙ E.functor ≅
      S.standardFormComponentRestrictedYonedaFunctor (k := k) c :=
    S.standardFormComponentGlobalYonedaDeletionNatIso (k := k) c
  let a :
      S.standardFormComponentRestrictedYonedaFunctor (k := k) c ⋙ E.inverse ≅
        R :=
    e.symm.compInverseIso
  change
    S.standardFormComponentRestrictedYonedaFunctor (k := k) c ⋙
        (E.inverse ⋙ F) ≅
      S.standardFormComponentMeshInclusion (k := k) c ⋙
        S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite
  exact
    (Functor.associator
      (S.standardFormComponentRestrictedYonedaFunctor (k := k) c)
      E.inverse F).symm ≪≫
      Functor.isoWhiskerRight a F ≪≫
        S.standardFormComponentGlobalYonedaRestrictionExtensionNatIso
          (k := k) c

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
