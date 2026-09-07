import MagnitudeConjecture.Algebra.RightModuleStandardFormRecovery
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraBridge

/-!
# The indecomposable skeleton of the standard-form algebra

The restricted-Yoneda recovery equivalence identifies the original standard
mesh vertices with a duplicate-free complete family of modules on the
projective vertices.  The finite-category algebra equivalence then transports
that literal `Fin S.n` family to the standard-form algebra.
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

local instance standardFormAlgebraSkeletonQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormAlgebraSkeletonArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The restricted-Yoneda images of the standard-mesh vertices form a
duplicate-free complete skeleton of modules on the projective vertices. -/
def standardFormProjectiveVertexModuleIndecomposableSkeleton :
    FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) where
  n := S.n
  obj i := (S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite).obj
      (MeshCategory.obj (k := k) S.standardFormRightMeshData i)
  indecomposable i := by
    let X := MeshCategory.obj (k := k) S.standardFormRightMeshData i
    let F := S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite
    letI : F.Faithful :=
      S.standardFormRestrictedYonedaFunctor_faithful
    letI : FiniteDimensional k (End X) :=
      S.standardFormMeshHomFinite X X
    letI : IsLocalRing (End X) :=
      MeshCategory.end_isLocalRing_of_finiteDimensional
        S.standardFormRightMeshData i
    letI : IsLocalRing (End (F.obj X)) :=
      MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
        (CategoryTheory.Functor.endRingEquivOfFullyFaithful F X)
    exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _
  skeletal := by
    intro i j hij
    obtain ⟨hij⟩ := hij
    let F := S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite
    letI : F.Faithful :=
      S.standardFormRestrictedYonedaFunctor_faithful
    exact MeshCategory.eq_of_obj_iso (k := k)
      S.standardFormRightMeshData (F.preimageIso hij)
  complete := by
    intro M hM
    obtain ⟨X, ⟨e⟩⟩ :=
      S.standardFormRestrictedYonedaFunctor_indec_dense M hM
    exact ⟨X.as, ⟨e.symm⟩⟩

/-- At a projective mesh vertex, restricted Yoneda is the corresponding
representable module on the projective full subcategory. -/
def standardFormProjectiveRestrictedYonedaIso
    (p : S.StandardFormProjectiveVertex) :
    finiteDimensionalLinearCoyoneda
        (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) (k := k)
        (Opposite.op
          (show S.StandardFormProjectiveMeshCategory from p))
        (S.standardFormFiniteRightRepresentables
          S.standardFormMeshHomFinite
            (Opposite.op
              (show S.StandardFormProjectiveMeshCategory from p))) ≅
      (S.standardFormProjectiveVertexModuleIndecomposableSkeleton
        (k := k)).obj p.1 := by
  apply ObjectProperty.isoMk
    (P := IsFiniteDimensionalModule
      (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k)
  apply ObjectProperty.isoMk
    (P := IsLinearModule
      (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k)
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · dsimp only [finiteDimensionalLinearCoyoneda,
      linearCoyonedaLinearModule,
      standardFormProjectiveVertexModuleIndecomposableSkeleton,
      standardFormRestrictedYonedaFunctor,
      finiteRestrictedLinearYonedaFunctor,
      restrictedLinearYonedaFunctor,
      restrictedLinearYonedaLinearModule,
      restrictedLinearYoneda,
      ObjectProperty.lift,
      CategoryTheory.linearCoyoneda,
      CategoryTheory.linearYoneda]
    change ModuleCat.of k
        ((Opposite.op
          (show S.StandardFormProjectiveMeshCategory from p)) ⟶ X) ≅
      ModuleCat.of k
        (MeshCategory.obj (k := k) S.standardFormRightMeshData X.unop.1 ⟶
          MeshCategory.obj (k := k) S.standardFormRightMeshData p.1)
    exact ((oppositeHomLinearEquiv (k := k)
      (Opposite.op
        (show S.StandardFormProjectiveMeshCategory from p)) X).trans
          (InducedCategory.homLinearEquiv (R := k)
            (X := X.unop)
            (Y := (show S.StandardFormProjectiveMeshCategory from p)))).toModuleIso
  intro X Y f
  rfl

/-- Every original projective vertex remains projective in the recovered
module category on the standard-form projective vertices. -/
theorem standardFormProjectiveVertexModule_projective_of_original
    (i : Fin S.n) (hi : Projective (S.fgObj i)) :
    Projective
      ((S.standardFormProjectiveVertexModuleIndecomposableSkeleton
        (k := k)).obj i) := by
  let p : S.StandardFormProjectiveVertex := ⟨i, hi⟩
  let P := finiteDimensionalLinearCoyoneda
    (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) (k := k)
    (Opposite.op
      (show S.StandardFormProjectiveMeshCategory from p))
    (S.standardFormFiniteRightRepresentables
      S.standardFormMeshHomFinite
        (Opposite.op
          (show S.StandardFormProjectiveMeshCategory from p)))
  letI : Projective P := finiteDimensionalLinearCoyoneda_projective
    (Opposite.op
      (show S.StandardFormProjectiveMeshCategory from p))
    (S.standardFormFiniteRightRepresentables
      S.standardFormMeshHomFinite
        (Opposite.op
          (show S.StandardFormProjectiveMeshCategory from p)))
  exact Projective.of_iso
    (S.standardFormProjectiveRestrictedYonedaIso (k := k) p) inferInstance

/-- Restricted Yoneda preserves and reflects the original projective vertex
set.  Reflection uses the nonsplit epic incoming mesh at every
nonprojective vertex. -/
theorem standardFormProjectiveVertexModule_projective_iff_original
    (i : Fin S.n) :
    Projective
        ((S.standardFormProjectiveVertexModuleIndecomposableSkeleton
          (k := k)).obj i) ↔
      Projective (S.fgObj i) := by
  constructor
  · intro hprojective
    by_contra hi
    let z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet} :=
      ⟨i, by simpa [standardFormProjectiveSet] using hi⟩
    let g := S.standardFormRightMeshData.additiveIncomingMap
      (k := k) z.1
    haveI : Epi g :=
      (S.standardFormRiedtmannConditionB_iff_incoming_epi
        (k := k)).1 S.standardFormRiedtmannConditionB z
    let F := S.standardFormAdditiveRestrictedYonedaFunctor (k := k)
    haveI : Epi (F.map g) := by infer_instance
    let e := S.standardFormAdditiveRestrictedYonedaSingletonIso
      (k := k) z.1
    let g' := F.map g ≫ e.hom
    haveI : Epi g' := by
      dsimp only [g']
      infer_instance
    letI : Projective
        ((S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite).obj
            (MeshCategory.obj (k := k)
              S.standardFormRightMeshData z.1)) := by
      change Projective
        ((S.standardFormProjectiveVertexModuleIndecomposableSkeleton
          (k := k)).obj i)
      exact hprojective
    let s := Projective.factorThru (𝟙 _) g'
    have hs : s ≫ g' = 𝟙 _ := Projective.factorThru_comp (𝟙 _) g'
    have hsg : s ≫ F.map g = e.inv := by
      apply (cancel_mono e.hom).1
      simpa only [Category.assoc, e.inv_hom_id] using hs
    let t := F.preimage (e.hom ≫ s)
    apply S.standardFormRightMeshData.additiveIncomingMap_not_splitEpi
      (k := k) z.1
    letI : IsSplitEpi g := IsSplitEpi.mk'
      { section_ := t
        id := by
          apply F.map_injective
          rw [F.map_comp, F.map_preimage, F.map_id]
          simp only [Category.assoc, hsg, e.hom_inv_id]
          rfl }
    infer_instance
  · exact S.standardFormProjectiveVertexModule_projective_of_original
      (k := k) i

/-- The finite-category projective-generator equivalence for the projective
vertex category of the standard mesh. -/
def standardFormProjectiveVertexModuleAlgebraEquivalence :
    S.StandardFormProjectiveVertexModuleCategory (k := k) ≌
      RightModule.FinitelyGeneratedCategory
        (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  finiteCategoryProjectiveGenerator.moduleEquivalence
    (S.standardFormFiniteRightRepresentables
      S.standardFormMeshHomFinite)

instance :
    (S.standardFormProjectiveVertexModuleAlgebraEquivalence
      (k := k)).functor.Additive := by
  let hP := S.standardFormFiniteRightRepresentables
    S.standardFormMeshHomFinite
  change (finiteCategoryProjectiveGenerator.representedFGFunctor hP).Additive
  exact
    { map_add := by
        intro X Y f g
        exact (finiteCategoryProjectiveGenerator.representedFGFunctor hP).map_add }

/-- The standard-form algebra has a duplicate-free complete indecomposable
skeleton indexed by the original Auslander--Reiten vertices. -/
def standardFormAlgebraIndecomposableSkeleton :
    RightModule.FiniteIndecomposableSkeleton k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) := by
  let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
  letI : FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
    S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
  letI : IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact pushforwardRightModuleIndecomposableSkeleton E
    (S.standardFormProjectiveVertexModuleIndecomposableSkeleton (k := k))

/-- The standard-form algebra skeleton has exactly the original projective
labels. -/
theorem standardFormAlgebraSkeleton_projective_iff_original
    (i : Fin S.n) :
    Projective
        ((S.standardFormAlgebraIndecomposableSkeleton (k := k)).fgObj i) ↔
      Projective (S.fgObj i) := by
  let E := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
  let T := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
    (k := k)
  letI : FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
    S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
  letI : IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let e : (S.standardFormAlgebraIndecomposableSkeleton (k := k)).fgObj i ≅
      E.functor.obj (T.obj i) := by
    exact pushforwardRightModuleIndecomposableSkeletonObjIso E T i
  constructor
  · intro hi
    have hmap : Projective (E.functor.obj (T.obj i)) :=
      Projective.of_iso e hi
    have hsource : Projective (T.obj i) :=
      (E.map_projective_iff (T.obj i)).1 hmap
    exact
      (S.standardFormProjectiveVertexModule_projective_iff_original
        (k := k) i).1 hsource
  · intro hi
    have hsource : Projective (T.obj i) :=
      (S.standardFormProjectiveVertexModule_projective_iff_original
        (k := k) i).2 hi
    have hmap : Projective (E.functor.obj (T.obj i)) :=
      (E.map_projective_iff (T.obj i)).2 hsource
    exact Projective.of_iso e.symm hmap

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
