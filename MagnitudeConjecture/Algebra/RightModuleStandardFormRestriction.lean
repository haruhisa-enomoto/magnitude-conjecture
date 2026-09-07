import MagnitudeConjecture.Algebra.RightModuleStandardFormProjectiveInjectives
import MagnitudeConjecture.CategoryTheory.FiniteCoordinateFunctor
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleRestriction

/-!
# Restriction from the standard mesh to its projective vertices

The manuscript's restricted Yoneda functor factors through restriction of
finite contravariant modules on the whole standard mesh.  On
projective-injective modules this restriction is fully faithful: both sides
have finite coordinates indexed by the projective mesh vertices, and
restriction identifies the corresponding dual corepresentables.
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

local instance standardFormRestrictionQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormRestrictionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The full inclusion of projective standard-mesh vertices into the strict
vertex model of the whole standard mesh. -/
def standardFormProjectiveVertexInclusion :
    S.StandardFormProjectiveMeshCategory ⥤
      S.standardFormRightMeshData.VertexCategory (k := k) where
  obj p := p.1
  map f := InducedCategory.homMk f.hom
  map_id p := by
    apply InducedCategory.hom_ext
    rfl
  map_comp f g := by
    apply InducedCategory.hom_ext
    rfl

instance : S.standardFormProjectiveVertexInclusion.Additive where
  map_add := by
    intro X Y f g
    apply InducedCategory.hom_ext
    rfl

instance : S.standardFormProjectiveVertexInclusion.Linear k where
  map_smul := by
    intro X Y f r
    apply InducedCategory.hom_ext
    rfl

instance : S.standardFormProjectiveVertexInclusion.Full where
  map_surjective f :=
    ⟨InducedCategory.homMk f.hom, by
      apply InducedCategory.hom_ext
      rfl⟩

instance : S.standardFormProjectiveVertexInclusion.Faithful where
  map_injective {X Y} f g h := by
    apply InducedCategory.hom_ext
    simpa [standardFormProjectiveVertexInclusion] using
      congrArg InducedCategory.Hom.hom h

instance : S.standardFormProjectiveVertexInclusion.op.Linear k where
  map_smul := by
    intro X Y f r
    apply Quiver.Hom.unop_inj
    exact S.standardFormProjectiveVertexInclusion.map_smul r f.unop

/-- Restriction of finite contravariant modules on the whole standard mesh
to the full subcategory on its projective vertices. -/
def standardFormModuleRestrictionFunctor :
    S.StandardFormFiniteContravariantModuleCategory ⥤
      FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k :=
  finiteLinearModuleRestrictionFunctor
    (k := k) S.standardFormProjectiveVertexInclusion.op
    (C := S.StandardFormProjectiveMeshCategoryᵒᵖ)
    (D := S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ)

instance : (S.standardFormModuleRestrictionFunctor (k := k)).Additive := by
  dsimp only [standardFormModuleRestrictionFunctor]
  infer_instance

instance standardFormModuleRestriction_preservesKernel
    {X Y : S.StandardFormFiniteContravariantModuleCategory} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0)
      (S.standardFormModuleRestrictionFunctor (k := k)) := by
  dsimp only [standardFormModuleRestrictionFunctor]
  infer_instance

/-- Restricting the whole-mesh representable at `x` gives the manuscript's
restricted representable module at `x`. -/
def standardFormRestrictedRepresentableIso (x : Fin S.n) :
    (S.standardFormModuleRestrictionFunctor (k := k)).obj
        (S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) S.standardFormFiniteContravariantRepresentables x) ≅
      (S.standardFormRestrictedYonedaFunctor (k := k)
        (S.standardFormMeshHomFinite (k := k))).obj
          (MeshCategory.obj (k := k) S.standardFormRightMeshData x) := by
  apply ObjectProperty.isoMk
    (P := IsFiniteDimensionalModule
      (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k)
  apply ObjectProperty.isoMk
    (P := IsLinearModule
      (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k)
  refine NatIso.ofComponents (fun Y ↦ ?_) ?_
  · exact (InducedCategory.homLinearEquiv (R := k)).toModuleIso
  · intro Y Z f
    rfl

/-- Dual corepresentables on the projective standard-mesh subcategory are
finite-dimensional modules. -/
theorem standardFormProjectiveMeshFiniteDualCorepresentables :
    ∀ X : S.StandardFormProjectiveMeshCategoryᵒᵖ,
      IsFiniteDimensionalModule
        (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k
        (dualLinearYonedaLinearModule (k := k) X) := by
  intro X
  constructor
  · intro Y
    change FiniteDimensional k (Module.Dual k (Y ⟶ X))
    letI : FiniteDimensional k (X.unop ⟶ Y.unop) := by
      letI : FiniteDimensional k
          (MeshCategory.obj (k := k) S.standardFormRightMeshData X.unop.1 ⟶
            MeshCategory.obj (k := k) S.standardFormRightMeshData Y.unop.1) :=
        S.standardFormMeshHomFinite _ _
      exact FiniteDimensional.of_injective
        InducedCategory.homLinearEquiv.toLinearMap
        InducedCategory.homLinearEquiv.injective
    letI : FiniteDimensional k (Y ⟶ X) :=
      FiniteDimensional.of_injective
        (oppositeHomLinearEquiv Y X).toLinearMap
        (oppositeHomLinearEquiv Y X).injective
    infer_instance
  · exact Set.toFinite _

/-- The projective vertices parameterize the projective-injective coordinate
modules on the whole standard mesh. -/
def standardFormProjectiveDualSourceFunctor :
    S.StandardFormProjectiveMeshCategory ⥤
      S.StandardFormFiniteContravariantModuleCategory :=
  S.standardFormProjectiveVertexInclusion ⋙
    opOp (S.standardFormRightMeshData.VertexCategory (k := k)) ⋙
      finiteDimensionalDualLinearYonedaFunctor
        (k := k) S.standardFormFiniteContravariantDualCorepresentables

instance : S.standardFormProjectiveDualSourceFunctor.Full := by
  dsimp only [standardFormProjectiveDualSourceFunctor]
  infer_instance

instance : S.standardFormProjectiveDualSourceFunctor.Faithful := by
  dsimp only [standardFormProjectiveDualSourceFunctor]
  infer_instance

/-- The projective vertices also parameterize the injective coordinate
modules over the projective full subcategory. -/
def standardFormProjectiveDualTargetFunctor :
    S.StandardFormProjectiveMeshCategory ⥤
      FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k :=
  opOp S.StandardFormProjectiveMeshCategory ⋙
    finiteDimensionalDualLinearYonedaFunctor
      (k := k) S.standardFormProjectiveMeshFiniteDualCorepresentables

instance : S.standardFormProjectiveDualTargetFunctor.Full := by
  dsimp only [standardFormProjectiveDualTargetFunctor]
  infer_instance

instance : S.standardFormProjectiveDualTargetFunctor.Faithful := by
  dsimp only [standardFormProjectiveDualTargetFunctor]
  infer_instance

/-- Restriction identifies a whole-mesh projective-injective coordinate
`D Hom(p,-)` with the corresponding dual corepresentable on the projective
full subcategory. -/
def standardFormRestrictedProjectiveDualIso
    (p : S.StandardFormProjectiveVertex) :
    (S.standardFormModuleRestrictionFunctor (k := k)).obj
        (finiteDimensionalDualLinearYoneda
          (k := k) (S.standardFormOppositeVertex (k := k) p.1)
          (S.standardFormFiniteContravariantDualCorepresentables
            (S.standardFormOppositeVertex (k := k) p.1))) ≅
      finiteDimensionalDualLinearYoneda
        (k := k) (Opposite.op p)
        (S.standardFormProjectiveMeshFiniteDualCorepresentables
          (k := k) (Opposite.op p)) := by
  apply ObjectProperty.isoMk
    (P := IsFiniteDimensionalModule
      (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k)
  apply ObjectProperty.isoMk
    (P := IsLinearModule
      (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k)
  refine NatIso.ofComponents (fun Y ↦ ?_) ?_
  · let eOV :
        ((S.standardFormProjectiveVertexInclusion (k := k)).op.obj Y ⟶
          S.standardFormOppositeVertex (k := k) p.1) ≃ₗ[k]
          ((show S.standardFormRightMeshData.VertexCategory (k := k) from p.1) ⟶
            (show S.standardFormRightMeshData.VertexCategory (k := k) from
              Y.unop.1)) :=
      oppositeHomLinearEquiv _ _
    let eV :
        ((show S.standardFormRightMeshData.VertexCategory (k := k) from p.1) ⟶
          (show S.standardFormRightMeshData.VertexCategory (k := k) from
            Y.unop.1)) ≃ₗ[k]
          (MeshCategory.obj (k := k) S.standardFormRightMeshData p.1 ⟶
            MeshCategory.obj (k := k) S.standardFormRightMeshData Y.unop.1) :=
      InducedCategory.homLinearEquiv
    let eP :
        ((show S.StandardFormProjectiveMeshCategory from p) ⟶
          (show S.StandardFormProjectiveMeshCategory from Y.unop)) ≃ₗ[k]
        (MeshCategory.obj (k := k) S.standardFormRightMeshData p.1 ⟶
          MeshCategory.obj (k := k) S.standardFormRightMeshData Y.unop.1) :=
      InducedCategory.homLinearEquiv
    let eOP : (Y ⟶ Opposite.op p) ≃ₗ[k]
        ((show S.StandardFormProjectiveMeshCategory from p) ⟶
          (show S.StandardFormProjectiveMeshCategory from Y.unop)) :=
      oppositeHomLinearEquiv _ _
    let e := eOV.trans ((eV.trans eP.symm).trans eOP.symm)
    exact e.symm.dualMap.toModuleIso
  · intro Y Z f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro q
    rfl

/-- The coordinatewise restriction isomorphisms are natural in the
projective vertex. -/
def standardFormProjectiveDualRestrictionNatIso :
    S.standardFormProjectiveDualSourceFunctor ⋙
        S.standardFormModuleRestrictionFunctor (k := k) ≅
      S.standardFormProjectiveDualTargetFunctor :=
  NatIso.ofComponents
    (fun p ↦ S.standardFormRestrictedProjectiveDualIso (k := k) p)
    (by
      intro p q f
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext Y
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro phi
      apply LinearMap.ext
      intro g
      rfl)

/-- Restriction carries every projective-injective whole-mesh module to an
injective module on the projective full subcategory. -/
theorem standardFormModuleRestriction_injective
    (I : S.StandardFormFiniteContravariantModuleCategory)
    [Projective I] [Injective I] :
    Injective ((S.standardFormModuleRestrictionFunctor (k := k)).obj I) := by
  let K := S.standardFormModuleRestrictionFunctor (k := k)
  letI : K.Additive := inferInstance
  obtain ⟨Q⟩ := S.standardFormProjectiveInjectiveCoordinates_nonempty I
  let source (i : Fin Q.n) := finiteDimensionalDualLinearYoneda
    (k := k) (S.standardFormOppositeVertex (k := k) (Q.p i).1)
    (S.standardFormFiniteContravariantDualCorepresentables
      (S.standardFormOppositeVertex (k := k) (Q.p i).1))
  let target (i : Fin Q.n) := finiteDimensionalDualLinearYoneda
    (k := k) (Opposite.op
      (show S.StandardFormProjectiveMeshCategory from Q.p i))
    (S.standardFormProjectiveMeshFiniteDualCorepresentables
      (k := k) (Opposite.op
        (show S.StandardFormProjectiveMeshCategory from Q.p i)))
  letI (i : Fin Q.n) : Injective (target i) :=
    finiteDimensionalDualLinearYoneda_injective
      (Opposite.op
        (show S.StandardFormProjectiveMeshCategory from Q.p i))
      (S.standardFormProjectiveMeshFiniteDualCorepresentables
        (k := k) (Opposite.op
          (show S.StandardFormProjectiveMeshCategory from Q.p i)))
  have hsum : Injective (⨁ target) := by infer_instance
  let e : (⨁ target) ≅ K.obj I :=
    (biproduct.mapIso (fun i ↦
      (S.standardFormRestrictedProjectiveDualIso
        (k := k) (Q.p i)).symm) :
        (⨁ target) ≅ ⨁ fun i ↦ K.obj (source i)) ≪≫
      (K.mapBiproduct source).symm ≪≫ K.mapIso Q.isoSource
  exact Injective.of_iso e hsum

/-- Restriction, with its injectivity property recorded in the codomain. -/
def standardFormProjectiveInjectiveRestrictionFunctor :
    ProjectiveInjectiveObject
        S.StandardFormFiniteContravariantModuleCategory ⥤
      InjectiveObject
        (FiniteDimensionalModuleCategory.{0, u, u, u}
          (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k) :=
  (isInjective _).lift
    (ProjectiveInjectiveObject.ι _ ⋙
      S.standardFormModuleRestrictionFunctor (k := k))
    (fun I ↦ S.standardFormModuleRestriction_injective (k := k) I.obj)

instance : (S.standardFormProjectiveInjectiveRestrictionFunctor
    (k := k)).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    rfl

/-- Projective vertices as projective-injective coordinate objects on the
whole standard mesh. -/
def standardFormProjectiveInjectiveCoordinateFunctor :
    S.StandardFormProjectiveMeshCategory ⥤
      ProjectiveInjectiveObject
        S.StandardFormFiniteContravariantModuleCategory :=
  ObjectProperty.lift
      (fun X : S.StandardFormFiniteContravariantModuleCategory ↦
        Projective X ∧ Injective X)
      S.standardFormProjectiveDualSourceFunctor
      (fun p ↦ ⟨
        S.standardFormProjectiveContravariantDualLinearYoneda_projective p,
        finiteDimensionalDualLinearYoneda_injective
          (S.standardFormOppositeVertex (k := k) p.1)
          (S.standardFormFiniteContravariantDualCorepresentables
            (S.standardFormOppositeVertex (k := k) p.1))⟩)

instance : S.standardFormProjectiveInjectiveCoordinateFunctor.Full := by
  dsimp only [standardFormProjectiveInjectiveCoordinateFunctor]
  infer_instance

instance : S.standardFormProjectiveInjectiveCoordinateFunctor.Faithful := by
  dsimp only [standardFormProjectiveInjectiveCoordinateFunctor]
  infer_instance

/-- Projective vertices as injective coordinate objects over the projective
full subcategory. -/
def standardFormInjectiveCoordinateFunctor :
    S.StandardFormProjectiveMeshCategory ⥤
      InjectiveObject
        (FiniteDimensionalModuleCategory.{0, u, u, u}
          (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k) :=
  (isInjective _).lift S.standardFormProjectiveDualTargetFunctor
    (fun p ↦ finiteDimensionalDualLinearYoneda_injective
      (Opposite.op p)
      (S.standardFormProjectiveMeshFiniteDualCorepresentables
        (k := k) (Opposite.op p)))

instance : S.standardFormInjectiveCoordinateFunctor.Full := by
  dsimp only [standardFormInjectiveCoordinateFunctor]
  infer_instance

instance : S.standardFormInjectiveCoordinateFunctor.Faithful := by
  dsimp only [standardFormInjectiveCoordinateFunctor]
  infer_instance

/-- Restriction identifies the projective-injective and injective coordinate
functors. -/
def standardFormProjectiveInjectiveCoordinateRestrictionNatIso :
    S.standardFormProjectiveInjectiveCoordinateFunctor ⋙
        S.standardFormProjectiveInjectiveRestrictionFunctor (k := k) ≅
      S.standardFormInjectiveCoordinateFunctor :=
  NatIso.ofComponents
    (fun p ↦ ObjectProperty.isoMk (P := isInjective _)
      (S.standardFormRestrictedProjectiveDualIso (k := k) p))
    (by
      intro p q f
      apply ObjectProperty.hom_ext
      exact (S.standardFormProjectiveDualRestrictionNatIso
        (k := k)).hom.naturality f)

/-- Every projective-injective whole-mesh module has finite coordinates in
the lifted projective-injective coordinate functor. -/
theorem standardFormProjectiveInjectiveCoordinateFunctor_nonempty
    (I : ProjectiveInjectiveObject
      S.StandardFormFiniteContravariantModuleCategory) :
    ∃ (n : ℕ) (p : Fin n → S.StandardFormProjectiveMeshCategory),
      Nonempty
        ((⨁ fun i ↦
          S.standardFormProjectiveInjectiveCoordinateFunctor.obj (p i)) ≅
            I) := by
  obtain ⟨Q⟩ := S.standardFormProjectiveInjectiveCoordinates_nonempty I.obj
  refine ⟨Q.n, Q.p, ⟨?_⟩⟩
  apply ObjectProperty.isoMk
    (P := fun X : S.StandardFormFiniteContravariantModuleCategory ↦
      Projective X ∧ Injective X)
  exact (ProjectiveInjectiveObject.ι _).mapBiproduct
      (fun i ↦
        S.standardFormProjectiveInjectiveCoordinateFunctor.obj (Q.p i)) ≪≫
    Q.isoSource

/-- Restriction is surjective on morphisms between projective-injective
coordinate objects. -/
theorem standardFormProjectiveInjectiveCoordinate_map_surjective
    (p q : S.StandardFormProjectiveMeshCategory) :
    Function.Surjective
      (fun f : S.standardFormProjectiveInjectiveCoordinateFunctor.obj p ⟶
          S.standardFormProjectiveInjectiveCoordinateFunctor.obj q ↦
        (S.standardFormProjectiveInjectiveRestrictionFunctor
          (k := k)).map f) := by
  let H := S.standardFormProjectiveInjectiveCoordinateFunctor
  let K := S.standardFormProjectiveInjectiveRestrictionFunctor (k := k)
  let J := S.standardFormInjectiveCoordinateFunctor
  let e : H ⋙ K ≅ J :=
    S.standardFormProjectiveInjectiveCoordinateRestrictionNatIso (k := k)
  letI : (H ⋙ K).Full := Functor.Full.of_iso e.symm
  intro f
  obtain ⟨a, ha⟩ := (H ⋙ K).map_surjective f
  exact ⟨H.map a, ha⟩

/-- Restriction is injective on morphisms between projective-injective
coordinate objects. -/
theorem standardFormProjectiveInjectiveCoordinate_map_injective
    (p q : S.StandardFormProjectiveMeshCategory) :
    Function.Injective
      (fun f : S.standardFormProjectiveInjectiveCoordinateFunctor.obj p ⟶
          S.standardFormProjectiveInjectiveCoordinateFunctor.obj q ↦
        (S.standardFormProjectiveInjectiveRestrictionFunctor
          (k := k)).map f) := by
  let H := S.standardFormProjectiveInjectiveCoordinateFunctor
  let K := S.standardFormProjectiveInjectiveRestrictionFunctor (k := k)
  let J := S.standardFormInjectiveCoordinateFunctor
  let e : H ⋙ K ≅ J :=
    S.standardFormProjectiveInjectiveCoordinateRestrictionNatIso (k := k)
  letI : (H ⋙ K).Faithful := Functor.Faithful.of_iso e.symm
  intro f g h
  obtain ⟨a, ha⟩ := H.map_surjective f
  obtain ⟨b, hb⟩ := H.map_surjective g
  have hab : a = b := (H ⋙ K).map_injective (by
    change K.map (H.map a) = K.map (H.map b)
    rw [ha, hb]
    exact h)
  rw [← ha, ← hb, hab]

instance : (S.standardFormProjectiveInjectiveRestrictionFunctor
    (k := k)).Full :=
  MagnitudeConjecture.CategoryTheory.functor_full_of_finite_coordinates
    (P := S.StandardFormProjectiveMeshCategory)
    (fun p ↦ S.standardFormProjectiveInjectiveCoordinateFunctor.obj p)
    (S.standardFormProjectiveInjectiveRestrictionFunctor (k := k))
    S.standardFormProjectiveInjectiveCoordinateFunctor_nonempty
    S.standardFormProjectiveInjectiveCoordinate_map_surjective

instance : (S.standardFormProjectiveInjectiveRestrictionFunctor
    (k := k)).Faithful :=
  MagnitudeConjecture.CategoryTheory.functor_faithful_of_finite_coordinates
    (P := S.StandardFormProjectiveMeshCategory)
    (fun p ↦ S.standardFormProjectiveInjectiveCoordinateFunctor.obj p)
    (S.standardFormProjectiveInjectiveRestrictionFunctor (k := k))
    S.standardFormProjectiveInjectiveCoordinateFunctor_nonempty
    S.standardFormProjectiveInjectiveCoordinate_map_injective

instance : (S.standardFormProjectiveInjectiveRestrictionFunctor
    (k := k)).EssSurj where
  mem_essImage I := by
    obtain ⟨Q⟩ :=
      finiteDualCorepresentableCoordinates_nonempty_of_injective
        S.standardFormProjectiveMeshFiniteDualCorepresentables
        (fun X ↦ opposite_end_isLocalRing
          (fun Y ↦ S.standardFormProjectiveMeshCategoryEndLocal
            (S.standardFormMeshHomFinite (k := k)) Y) X)
        I.obj
    let H := S.standardFormProjectiveInjectiveCoordinateFunctor
    let K := S.standardFormProjectiveInjectiveRestrictionFunctor (k := k)
    let U := InjectiveObject.ι
      (FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k)
    let p : Fin Q.n → S.StandardFormProjectiveMeshCategory :=
      fun i ↦ (Q.X i).unop
    refine ⟨⨁ fun i ↦ H.obj (p i), ⟨?_⟩⟩
    apply ObjectProperty.isoMk (P := isInjective _)
    let e (i : Fin Q.n) :
        U.obj (K.obj (H.obj (p i))) ≅
          (finiteDimensionalDualLinearYonedaFunctor
            (k := k) S.standardFormProjectiveMeshFiniteDualCorepresentables).obj
              (Opposite.op (Q.X i)) := by
      change (S.standardFormModuleRestrictionFunctor (k := k)).obj
          (finiteDimensionalDualLinearYoneda
            (k := k)
            (S.standardFormOppositeVertex (k := k) (Q.X i).unop.1)
            (S.standardFormFiniteContravariantDualCorepresentables
              (S.standardFormOppositeVertex (k := k) (Q.X i).unop.1))) ≅
        finiteDimensionalDualLinearYoneda
          (k := k) (Q.X i)
          (S.standardFormProjectiveMeshFiniteDualCorepresentables
            (k := k) (Q.X i))
      simpa only [p, Opposite.op_unop] using
        S.standardFormRestrictedProjectiveDualIso (k := k) (p i)
    exact U.mapIso (K.mapBiproduct (fun i ↦ H.obj (p i))) ≪≫
      U.mapBiproduct (fun i ↦ K.obj (H.obj (p i))) ≪≫
        biproduct.mapIso e ≪≫ Q.isoSource

instance : (S.standardFormProjectiveInjectiveRestrictionFunctor
    (k := k)).IsEquivalence where

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
