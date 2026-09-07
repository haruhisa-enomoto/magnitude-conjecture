import MagnitudeConjecture.Algebra.RightModuleStandardFormComponentRecovery

/-!
# Full recovery on a standard-form walk component

The component inclusion is fully faithful.  The natural comparison with
global restricted Yoneda then transports fullness to component restricted
Yoneda.  Extension by zero also transports global indecomposable density back
to the component: projective detection rules out a representing vertex in any
other walk component.
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

local instance componentPropertiesQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance componentPropertiesArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

instance standardFormComponentMeshInclusion_full
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentMeshInclusion (k := k) c).Full where
  map_surjective f :=
    ⟨InducedCategory.homMk f, rfl⟩

instance standardFormComponentMeshInclusion_faithful
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentMeshInclusion (k := k) c).Faithful where
  map_injective := by
    intro X Y f g h
    apply InducedCategory.hom_ext
    exact h

instance standardFormComponentRestrictedYonedaFunctor_full
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentRestrictedYonedaFunctor (k := k) c).Full := by
  let H := S.standardFormComponentRestrictedYonedaFunctor (k := k) c
  let E := S.standardFormComponentModuleExtensionByZero (k := k) c
  let I := S.standardFormComponentMeshInclusion (k := k) c
  let Y := S.standardFormRestrictedYonedaFunctor S.standardFormMeshHomFinite
  let e : H ⋙ E ≅ I ⋙ Y :=
    S.standardFormComponentRestrictedYonedaExtensionNatIso (k := k) c
  letI : I.Full := S.standardFormComponentMeshInclusion_full (k := k) c
  letI : Y.Full := S.standardFormRestrictedYonedaFunctor_full
  letI : (I ⋙ Y).Full := inferInstance
  letI : E.Faithful :=
    S.standardFormComponentModuleExtensionByZero_faithful (k := k) c
  exact Functor.Full.of_comp_faithful_iso e

theorem standardFormComponentRestrictedYonedaFunctor_indec_dense
    (c : S.StandardFormWalkComponent)
    (M : CoveringHom.FiniteDimensionalModuleCategory
      (C := (S.StandardFormComponentProjectiveMeshCategory
        (k := k) c)ᵒᵖ) k)
    (hM : Indecomposable M) :
    ∃ X : S.StandardFormComponentMeshCategory (k := k) c, Nonempty
      ((S.standardFormComponentRestrictedYonedaFunctor
        (k := k) c).obj X ≅ M) := by
  let E := S.standardFormComponentModuleExtensionByZero (k := k) c
  have hEM : Indecomposable (E.obj M) :=
    S.standardFormComponentModuleExtensionByZero_indec (k := k) c M hM
  obtain ⟨Z, ⟨eZ⟩⟩ :=
    S.standardFormRestrictedYonedaFunctor_indec_dense (E.obj M) hEM
  have hZc : S.standardFormWalkComponentClass Z.as = c := by
    by_contra hne
    obtain ⟨p, hp, g, hg⟩ :=
      S.standardFormRightMeshData.exists_projective_precomposition_ne_zero
        (fun a b ↦ S.standardFormMeshHomFinite
          (MeshCategory.obj (k := k) S.standardFormRightMeshData a)
          (MeshCategory.obj (k := k) S.standardFormRightMeshData b))
        S.standardFormRiedtmannConditionB (𝟙 Z)
        (MeshCategory.id_ne_zero S.standardFormRightMeshData Z.as)
    have hpc : S.standardFormWalkComponentClass p =
        S.standardFormWalkComponentClass Z.as := by
      by_contra hpne
      have hg0 : g = 0 :=
        S.standardForm_meshHom_eq_zero_of_walkComponentClass_ne hpne g
      exact hg (by simp [hg0])
    let P0 : S.StandardFormProjectiveMeshCategory :=
      ⟨p, (S.mem_standardFormProjectiveSet_iff p).mp hp⟩
    let P : S.StandardFormProjectiveMeshCategoryᵒᵖ := Opposite.op P0
    have hPne : S.standardFormWalkComponentClass P.unop.1 ≠ c := by
      change S.standardFormWalkComponentClass p ≠ c
      rw [hpc]
      exact hne
    have hExtZero : IsZero ((E.obj M).obj.obj.obj P) :=
      S.standardFormComponentModuleExtensionByZero_obj_isZero_of_class_ne
        (k := k) c M P hPne
    let Jfin := (CoveringHom.IsFiniteDimensionalModule
      (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k).ι
    let Jlin := (CoveringHom.IsLinearModule
      (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k).ι
    let eP :
        (((S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite).obj Z).obj.obj.obj P) ≅
          ((E.obj M).obj.obj.obj P) :=
      (Jlin.mapIso (Jfin.mapIso eZ)).app P
    have hGlobalZero : IsZero
        (((S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite).obj Z).obj.obj.obj P) :=
      (eP.isZero_iff).2 hExtZero
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hGlobalZero
    have hg' : g ≠ 0 := by
      intro hg0
      exact hg (by simp [hg0])
    apply hg'
    exact @Subsingleton.elim
      (MeshCategory.obj (k := k) S.standardFormRightMeshData p ⟶ Z)
      (by
        change Subsingleton
          (((S.standardFormRestrictedYonedaFunctor
            S.standardFormMeshHomFinite).obj Z).obj.obj.obj P)
        exact hsub) g 0
  let X : S.StandardFormComponentMeshCategory (k := k) c :=
    ⟨Z.as, hZc⟩
  let eGlobal : E.obj
        ((S.standardFormComponentRestrictedYonedaFunctor
          (k := k) c).obj X) ≅ E.obj M :=
    ((S.standardFormComponentRestrictedYonedaExtensionNatIso
      (k := k) c).app X).trans eZ
  letI : E.Full :=
    S.standardFormComponentModuleExtensionByZero_full (k := k) c
  letI : E.Faithful :=
    S.standardFormComponentModuleExtensionByZero_faithful (k := k) c
  exact ⟨X, ⟨E.preimageIso eGlobal⟩⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
