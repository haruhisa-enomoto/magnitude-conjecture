import MagnitudeConjecture.Algebra.RightModuleStandardFormComponentRecoveryProperties
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraBridge
import MagnitudeConjecture.CategoryTheory.LocallyBoundedOpposite

/-!
# Indecomposable skeleton of a standard-form component algebra

The finite vertices of a walk component are enumerated and their restricted
representables form a duplicate-free complete module skeleton.  The finite
category projective-generator equivalence transports it to the component
category algebra.  Indecomposable projectives are precisely the original
projective vertices of the component.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance componentSkeletonQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance componentSkeletonArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance componentSkeletonVertexFintype
    (c : S.StandardFormWalkComponent) :
    Fintype (S.StandardFormWalkComponentVertex c) :=
  Fintype.ofFinite _

/-- A fixed enumeration of the vertices in one standard-form walk component. -/
def standardFormComponentVertexEquivFin
    (c : S.StandardFormWalkComponent) :
    Fin (Fintype.card (S.StandardFormWalkComponentVertex c)) ≃
      S.StandardFormWalkComponentVertex c :=
  (Fintype.equivFin (S.StandardFormWalkComponentVertex c)).symm

/-- Component restricted representables form the complete duplicate-free
indecomposable skeleton of finite modules on the component projectives. -/
def standardFormComponentProjectiveVertexModuleIndecomposableSkeleton
    (c : S.StandardFormWalkComponent) :
    FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := (S.StandardFormComponentProjectiveMeshCategory
        (k := k) c)ᵒᵖ) where
  n := Fintype.card (S.StandardFormWalkComponentVertex c)
  obj i := (S.standardFormComponentRestrictedYonedaFunctor
    (k := k) c).obj (S.standardFormComponentVertexEquivFin c i)
  indecomposable i := by
    let X : S.StandardFormComponentMeshCategory (k := k) c :=
      S.standardFormComponentVertexEquivFin c i
    let F := S.standardFormComponentRestrictedYonedaFunctor (k := k) c
    letI : F.Additive := by
      dsimp only [F, standardFormComponentRestrictedYonedaFunctor]
      infer_instance
    letI : F.Faithful :=
      S.standardFormComponentRestrictedYonedaFunctor_faithful (k := k) c
    letI : F.Full :=
      S.standardFormComponentRestrictedYonedaFunctor_full (k := k) c
    letI : FiniteDimensional k (End X) :=
      S.standardFormComponentMeshHomFinite (k := k) c X X
    letI : FiniteDimensional k
        (End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1)) :=
      S.standardFormMeshHomFinite _ _
    letI : IsLocalRing
        (End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1)) :=
      MeshCategory.end_isLocalRing_of_finiteDimensional
        S.standardFormRightMeshData X.1
    let eEnd : End X ≃+*
        End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1) :=
      { InducedCategory.endEquiv with
        map_add' := fun _ _ ↦ rfl }
    letI : IsLocalRing (End X) :=
      MagnitudeConjecture.RingEquiv.isLocalRing_noncomm eEnd.symm
    letI : IsLocalRing (End (F.obj X)) :=
      MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
        (CategoryTheory.Functor.endRingEquivOfFullyFaithful F X)
    exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _
  skeletal := by
    intro i j hij
    obtain ⟨hij⟩ := hij
    let F := S.standardFormComponentRestrictedYonedaFunctor (k := k) c
    letI : F.Faithful :=
      S.standardFormComponentRestrictedYonedaFunctor_faithful (k := k) c
    letI : F.Full :=
      S.standardFormComponentRestrictedYonedaFunctor_full (k := k) c
    let e := S.standardFormComponentVertexEquivFin c
    apply e.injective
    apply Subtype.ext
    exact MeshCategory.eq_of_obj_iso (k := k)
      S.standardFormRightMeshData
      ((S.standardFormComponentMeshInclusion (k := k) c).mapIso
        (F.preimageIso hij))
  complete := by
    intro M hM
    obtain ⟨X, ⟨eX⟩⟩ :=
      S.standardFormComponentRestrictedYonedaFunctor_indec_dense
        (k := k) c M hM
    let e := S.standardFormComponentVertexEquivFin c
    refine ⟨e.symm X, ?_⟩
    simpa only [e, Equiv.apply_symm_apply] using
      (show Nonempty (M ≅
        (S.standardFormComponentRestrictedYonedaFunctor
          (k := k) c).obj X) from ⟨eX.symm⟩)

/-- The projective-generator equivalence from component modules to modules
over the component category algebra. -/
def standardFormComponentProjectiveVertexModuleAlgebraEquivalence
    (c : S.StandardFormWalkComponent) :
    CoveringHom.FiniteDimensionalModuleCategory
        (C := (S.StandardFormComponentProjectiveMeshCategory
          (k := k) c)ᵒᵖ) k ≌
      RightModule.FinitelyGeneratedCategory
        (S.standardFormComponentAlgebra (k := k) c) :=
  finiteCategoryProjectiveGenerator.moduleEquivalence
    (S.standardFormComponentFiniteRightRepresentables (k := k) c)

instance standardFormComponentProjectiveVertexModuleAlgebraEquivalence_functor_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveVertexModuleAlgebraEquivalence
      (k := k) c).functor.Additive := by
  let hP := S.standardFormComponentFiniteRightRepresentables (k := k) c
  change (finiteCategoryProjectiveGenerator.representedFGFunctor hP).Additive
  exact
    { map_add := by
        intro X Y f g
        exact (finiteCategoryProjectiveGenerator.representedFGFunctor hP).map_add }

/-- The component category algebra has a complete indecomposable skeleton
indexed by the vertices of that component. -/
def standardFormComponentAlgebraIndecomposableSkeleton
    (c : S.StandardFormWalkComponent) :
    RightModule.FiniteIndecomposableSkeleton k
      (S.standardFormComponentAlgebra (k := k) c) := by
  let E := S.standardFormComponentProjectiveVertexModuleAlgebraEquivalence
    (k := k) c
  letI : FiniteDimensional k (S.standardFormComponentAlgebra (k := k) c) :=
    S.standardFormComponentAlgebra_finiteDimensional (k := k) c
  letI : IsNoetherianRing
      (S.standardFormComponentAlgebra (k := k) c)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact pushforwardRightModuleIndecomposableSkeleton E
    (S.standardFormComponentProjectiveVertexModuleIndecomposableSkeleton
      (k := k) c)

/-- Opposite component projective vertices have local endomorphism rings. -/
theorem standardFormComponentOppositeProjectiveEndLocal
    (c : S.StandardFormWalkComponent)
    (P : (S.StandardFormComponentProjectiveMeshCategory
      (k := k) c)ᵒᵖ) :
    IsLocalRing (End P) := by
  let X : S.StandardFormComponentMeshCategory (k := k) c := P.unop.1
  letI : FiniteDimensional k
      (End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1)) :=
    S.standardFormMeshHomFinite _ _
  letI : IsLocalRing
      (End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1)) :=
    MeshCategory.end_isLocalRing_of_finiteDimensional
      S.standardFormRightMeshData X.1
  let eMesh : End X ≃+*
      End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1) :=
    { InducedCategory.endEquiv with
      map_add' := fun _ _ ↦ rfl }
  letI : IsLocalRing (End X) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm eMesh.symm
  let eProjective : End P.unop ≃+* End X :=
    { InducedCategory.endEquiv with
      map_add' := fun _ _ ↦ rfl }
  letI : IsLocalRing (End P.unop) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm eProjective.symm
  letI : IsLocalRing (End P.unop)ᵐᵒᵖ :=
    CoveringHom.isLocalRing_mulOpposite
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (oppositeEndRingEquiv P.unop)

/-- At a component projective vertex, component restricted Yoneda is the
corresponding representable module. -/
def standardFormComponentProjectiveRestrictedYonedaIso
    (c : S.StandardFormWalkComponent)
    (p : S.StandardFormComponentProjectiveVertex c) :
    finiteDimensionalLinearCoyoneda
        (C := (S.StandardFormComponentProjectiveMeshCategory
          (k := k) c)ᵒᵖ) (k := k)
        (Opposite.op
          (show S.StandardFormComponentProjectiveMeshCategory
            (k := k) c from p))
        (S.standardFormComponentFiniteRightRepresentables (k := k) c
          (Opposite.op
            (show S.StandardFormComponentProjectiveMeshCategory
              (k := k) c from p))) ≅
      (S.standardFormComponentRestrictedYonedaFunctor
        (k := k) c).obj p.1 := by
  apply ObjectProperty.isoMk
    (P := IsFiniteDimensionalModule
      (C := (S.StandardFormComponentProjectiveMeshCategory
        (k := k) c)ᵒᵖ) k)
  apply ObjectProperty.isoMk
    (P := IsLinearModule
      (C := (S.StandardFormComponentProjectiveMeshCategory
        (k := k) c)ᵒᵖ) k)
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · change ModuleCat.of k
        ((Opposite.op
          (show S.StandardFormComponentProjectiveMeshCategory
            (k := k) c from p)) ⟶ X) ≅
      ModuleCat.of k
        ((show S.StandardFormComponentMeshCategory (k := k) c from X.unop.1) ⟶
          (show S.StandardFormComponentMeshCategory (k := k) c from p.1))
    exact ((oppositeHomLinearEquiv (k := k)
      (Opposite.op
        (show S.StandardFormComponentProjectiveMeshCategory
          (k := k) c from p)) X).trans
          (InducedCategory.homLinearEquiv (R := k)
            (X := X.unop)
            (Y := (show S.StandardFormComponentProjectiveMeshCategory
              (k := k) c from p)))).toModuleIso
  · intro X Y f
    rfl

/-- A component restricted representable is projective exactly at an original
projective vertex. -/
theorem standardFormComponentRestrictedYoneda_projective_iff_original
    (c : S.StandardFormWalkComponent)
    (x : S.StandardFormWalkComponentVertex c) :
    Projective
        ((S.standardFormComponentRestrictedYonedaFunctor
          (k := k) c).obj x) ↔
      Projective (S.fgObj x.1) := by
  constructor
  · intro hx
    let Y := S.standardFormComponentRestrictedYonedaFunctor (k := k) c
    letI : Y.Full :=
      S.standardFormComponentRestrictedYonedaFunctor_full (k := k) c
    letI : Y.Faithful :=
      S.standardFormComponentRestrictedYonedaFunctor_faithful (k := k) c
    let e := S.standardFormComponentVertexEquivFin c
    let T := S.standardFormComponentProjectiveVertexModuleIndecomposableSkeleton
      (k := k) c
    have hxIndec : Indecomposable (Y.obj x) := by
      have h := T.indecomposable (e.symm x)
      simpa only [T, standardFormComponentProjectiveVertexModuleIndecomposableSkeleton,
        e, Equiv.apply_symm_apply] using h
    letI : Projective (Y.obj x) := hx
    obtain ⟨Q, ⟨eQ⟩⟩ :=
      indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
        (S.standardFormComponentFiniteRightRepresentables (k := k) c)
        (S.standardFormComponentOppositeProjectiveEndLocal (k := k) c)
        (Y.obj x) hxIndec
    let p : S.StandardFormComponentProjectiveMeshCategory (k := k) c := Q.unop
    let eYX : Y.obj p.1 ≅ Y.obj x :=
      (S.standardFormComponentProjectiveRestrictedYonedaIso
        (k := k) c p).symm.trans eQ
    have hpx : p.1.1 = x.1 :=
      MeshCategory.eq_of_obj_iso (k := k) S.standardFormRightMeshData
        ((S.standardFormComponentMeshInclusion (k := k) c).mapIso
          (Y.preimageIso eYX))
    rw [← hpx]
    exact p.2
  · intro hx
    let p : S.StandardFormComponentProjectiveVertex c := ⟨x, hx⟩
    let P := finiteDimensionalLinearCoyoneda
      (C := (S.StandardFormComponentProjectiveMeshCategory
        (k := k) c)ᵒᵖ) (k := k)
      (Opposite.op
        (show S.StandardFormComponentProjectiveMeshCategory
          (k := k) c from p))
      (S.standardFormComponentFiniteRightRepresentables (k := k) c
        (Opposite.op
          (show S.StandardFormComponentProjectiveMeshCategory
            (k := k) c from p)))
    letI : Projective P := finiteDimensionalLinearCoyoneda_projective
      (Opposite.op
        (show S.StandardFormComponentProjectiveMeshCategory
          (k := k) c from p))
      (S.standardFormComponentFiniteRightRepresentables (k := k) c
        (Opposite.op
          (show S.StandardFormComponentProjectiveMeshCategory
            (k := k) c from p)))
    exact Projective.of_iso
      (S.standardFormComponentProjectiveRestrictedYonedaIso
        (k := k) c p) inferInstance

/-- The component-algebra skeleton has exactly the original projective
vertices under the fixed component enumeration. -/
theorem standardFormComponentAlgebraSkeleton_projective_iff_original
    (c : S.StandardFormWalkComponent)
    (i : Fin (Fintype.card (S.StandardFormWalkComponentVertex c))) :
    Projective
        ((S.standardFormComponentAlgebraIndecomposableSkeleton
          (k := k) c).fgObj i) ↔
      Projective
        (S.fgObj (S.standardFormComponentVertexEquivFin c i).1) := by
  let E := S.standardFormComponentProjectiveVertexModuleAlgebraEquivalence
    (k := k) c
  let T := S.standardFormComponentProjectiveVertexModuleIndecomposableSkeleton
    (k := k) c
  letI : FiniteDimensional k (S.standardFormComponentAlgebra (k := k) c) :=
    S.standardFormComponentAlgebra_finiteDimensional (k := k) c
  letI : IsNoetherianRing
      (S.standardFormComponentAlgebra (k := k) c)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let e :
      (S.standardFormComponentAlgebraIndecomposableSkeleton
        (k := k) c).fgObj i ≅ E.functor.obj (T.obj i) :=
    pushforwardRightModuleIndecomposableSkeletonObjIso E T i
  constructor
  · intro hi
    have hmap : Projective (E.functor.obj (T.obj i)) :=
      Projective.of_iso e hi
    have hsource : Projective (T.obj i) :=
      (E.map_projective_iff (T.obj i)).1 hmap
    exact
      (S.standardFormComponentRestrictedYoneda_projective_iff_original
        (k := k) c (S.standardFormComponentVertexEquivFin c i)).1 hsource
  · intro hi
    have hsource : Projective (T.obj i) :=
      (S.standardFormComponentRestrictedYoneda_projective_iff_original
        (k := k) c (S.standardFormComponentVertexEquivFin c i)).2 hi
    have hmap : Projective (E.functor.obj (T.obj i)) :=
      (E.map_projective_iff (T.obj i)).2 hsource
    exact Projective.of_iso e.symm hmap

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
