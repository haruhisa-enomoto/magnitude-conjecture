import MagnitudeConjecture.Algebra.RightModuleStandardFormComponentSurplus

/-!
# Category algebras of standard-form walk components

Each augmented-walk component determines full mesh and projective mesh
subcategories.  The projective subcategory has finite-dimensional
representables and hence a finite-dimensional category algebra.  Projective
detection stays inside a component, so component restricted Yoneda is
faithful.  These are the categorical inputs for applying the connected
covering argument one component at a time.
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

local instance componentAlgebraQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance componentAlgebraArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The full subcategory of the standard mesh on one augmented-walk component. -/
abbrev StandardFormComponentMeshCategory
    (c : S.StandardFormWalkComponent) :=
  InducedCategory S.StandardFormMeshCategory
    (fun x : S.StandardFormWalkComponentVertex c ↦
      MeshCategory.obj (k := k) S.standardFormRightMeshData x.1)

/-- Projective vertices in one augmented-walk component. -/
abbrev StandardFormComponentProjectiveVertex
    (c : S.StandardFormWalkComponent) :=
  {x : S.StandardFormWalkComponentVertex c // Projective (S.fgObj x.1)}

/-- The full subcategory on the projective vertices of one component. -/
abbrev StandardFormComponentProjectiveMeshCategory
    (c : S.StandardFormWalkComponent) :=
  InducedCategory (S.StandardFormComponentMeshCategory (k := k) c)
    (fun p : S.StandardFormComponentProjectiveVertex c ↦
      (show S.StandardFormComponentMeshCategory (k := k) c from p.1))

/-- Every standard-form walk component contains a projective vertex. -/
theorem standardFormComponentProjectiveVertex_nonempty
    (c : S.StandardFormWalkComponent) :
    Nonempty (S.StandardFormComponentProjectiveVertex c) := by
  obtain ⟨x⟩ := S.standardFormWalkComponentVertex_nonempty c
  let X := MeshCategory.obj (k := k) S.standardFormRightMeshData x.1
  obtain ⟨p, hp, g, hg⟩ :=
    S.standardFormRightMeshData.exists_projective_precomposition_ne_zero
      (fun a b ↦ S.standardFormMeshHomFinite
        (MeshCategory.obj (k := k) S.standardFormRightMeshData a)
        (MeshCategory.obj (k := k) S.standardFormRightMeshData b))
      S.standardFormRiedtmannConditionB (𝟙 X)
      (MeshCategory.id_ne_zero S.standardFormRightMeshData x.1)
  have hpc : S.standardFormWalkComponentClass p = c := by
    rw [← x.2]
    by_contra hne
    have hg0 : g = 0 :=
      S.standardForm_meshHom_eq_zero_of_walkComponentClass_ne hne g
    exact hg (by simp [hg0])
  exact ⟨⟨⟨p, hpc⟩,
    (S.mem_standardFormProjectiveSet_iff p).mp hp⟩⟩

noncomputable instance standardFormComponentMeshCategoryFintype
    (c : S.StandardFormWalkComponent) :
    Fintype (S.StandardFormComponentMeshCategory (k := k) c) := by
  change Fintype (S.StandardFormWalkComponentVertex c)
  exact Fintype.ofFinite _

noncomputable instance standardFormComponentProjectiveMeshCategoryFintype
    (c : S.StandardFormWalkComponent) :
    Fintype (S.StandardFormComponentProjectiveMeshCategory (k := k) c) := by
  change Fintype (S.StandardFormComponentProjectiveVertex c)
  exact Fintype.ofFinite _

noncomputable instance standardFormComponentProjectiveMeshCategoryOppositeFintype
    (c : S.StandardFormWalkComponent) :
    Fintype (S.StandardFormComponentProjectiveMeshCategory (k := k) c)ᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

/-- Inclusion of a component into the whole standard mesh category. -/
def standardFormComponentMeshInclusion
    (c : S.StandardFormWalkComponent) :
    S.StandardFormComponentMeshCategory (k := k) c ⥤
      S.StandardFormMeshCategory :=
  inducedFunctor (fun x : S.StandardFormWalkComponentVertex c ↦
    MeshCategory.obj (k := k) S.standardFormRightMeshData x.1)

instance standardFormComponentMeshInclusion_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentMeshInclusion (k := k) c).Additive := by
  dsimp only [standardFormComponentMeshInclusion]
  infer_instance

instance standardFormComponentMeshInclusion_linear
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentMeshInclusion (k := k) c).Linear k := by
  dsimp only [standardFormComponentMeshInclusion]
  infer_instance

/-- Inclusion of the projective part of a component into that component. -/
def standardFormComponentProjectiveMeshInclusion
    (c : S.StandardFormWalkComponent) :
    S.StandardFormComponentProjectiveMeshCategory (k := k) c ⥤
      S.StandardFormComponentMeshCategory (k := k) c :=
  inducedFunctor (fun p : S.StandardFormComponentProjectiveVertex c ↦
    (show S.StandardFormComponentMeshCategory (k := k) c from p.1))

/-- Inclusion of a component's projective part into the global projective
mesh category. -/
def standardFormComponentProjectiveToGlobal
    (c : S.StandardFormWalkComponent) :
    S.StandardFormComponentProjectiveMeshCategory (k := k) c ⥤
      S.StandardFormProjectiveMeshCategory where
  obj p := ⟨p.1.1, p.2⟩
  map f := InducedCategory.homMk f.hom.hom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance standardFormComponentProjectiveToGlobal_full
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToGlobal (k := k) c).Full where
  map_surjective f :=
    ⟨InducedCategory.homMk (InducedCategory.homMk f.hom), by ext; rfl⟩

instance standardFormComponentProjectiveToGlobal_faithful
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToGlobal (k := k) c).Faithful where
  map_injective := by
    intro X Y f g h
    apply InducedCategory.hom_ext
    apply InducedCategory.hom_ext
    exact congrArg (fun q ↦ q.hom) h

instance standardFormComponentProjectiveToGlobal_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToGlobal (k := k) c).Additive := by
  exact { map_add := by intros; ext; rfl }

instance standardFormComponentProjectiveToGlobal_linear
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveToGlobal (k := k) c).Linear k := by
  exact { map_smul := by intros; ext; rfl }

instance standardFormComponentProjectiveMeshInclusion_additive
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveMeshInclusion (k := k) c).Additive := by
  dsimp only [standardFormComponentProjectiveMeshInclusion]
  infer_instance

instance standardFormComponentProjectiveMeshInclusion_linear
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentProjectiveMeshInclusion (k := k) c).Linear k := by
  dsimp only [standardFormComponentProjectiveMeshInclusion]
  infer_instance

/-- Ambient finite-dimensionality restricts to every component mesh category. -/
theorem standardFormComponentMeshHomFinite
    (c : S.StandardFormWalkComponent) :
    ∀ X Y : S.StandardFormComponentMeshCategory (k := k) c,
      FiniteDimensional k (X ⟶ Y) := by
  intro X Y
  letI : FiniteDimensional k
      (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1 ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData Y.1) :=
    S.standardFormMeshHomFinite _ _
  exact FiniteDimensional.of_injective
    InducedCategory.homLinearEquiv.toLinearMap
    InducedCategory.homLinearEquiv.injective

/-- Restricted Yoneda from one component mesh to the finite modules on its
projective vertices. -/
def standardFormComponentRestrictedYonedaFunctor
    (c : S.StandardFormWalkComponent) :
    S.StandardFormComponentMeshCategory (k := k) c ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := (S.StandardFormComponentProjectiveMeshCategory
          (k := k) c)ᵒᵖ) k :=
  CoveringHom.finiteRestrictedLinearYonedaFunctor
    (k := k) (S.standardFormComponentProjectiveMeshInclusion (k := k) c)
    (fun X Y ↦ S.standardFormComponentMeshHomFinite
      (k := k) c
      ((S.standardFormComponentProjectiveMeshInclusion (k := k) c).obj Y) X)

/-- Projective vertices in the same component detect all component mesh
morphisms. -/
theorem standardFormComponentRestrictedYonedaFunctor_faithful
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentRestrictedYonedaFunctor (k := k) c).Faithful := by
  apply CoveringHom.finiteRestrictedLinearYonedaFunctor_faithful_of_sourceDetection
  intro X Y f hf
  have hf' : f.hom ≠ 0 := by
    intro hf'
    apply hf
    apply InducedCategory.hom_ext
    exact hf'
  obtain ⟨p, hp, g, hgf⟩ :=
    S.standardFormRightMeshData.exists_projective_precomposition_ne_zero
      (fun a b ↦ S.standardFormMeshHomFinite
        (MeshCategory.obj (k := k) S.standardFormRightMeshData a)
        (MeshCategory.obj (k := k) S.standardFormRightMeshData b))
      S.standardFormRiedtmannConditionB f.hom hf'
  have hpc : S.standardFormWalkComponentClass p = c := by
    rw [← X.2]
    by_contra hne
    have hg0 : g = 0 :=
      S.standardForm_meshHom_eq_zero_of_walkComponentClass_ne hne g
    exact hgf (by simp [hg0])
  let P : S.StandardFormComponentProjectiveMeshCategory (k := k) c :=
    ⟨⟨p, hpc⟩, (S.mem_standardFormProjectiveSet_iff p).mp hp⟩
  refine ⟨P, InducedCategory.homMk g, ?_⟩
  intro hzero
  apply hgf
  exact congrArg (fun q ↦ q.hom) hzero

/-- Finite-dimensional right representables on a component's projective part. -/
theorem standardFormComponentFiniteRightRepresentables
    (c : S.StandardFormWalkComponent) :
    ∀ X : (S.StandardFormComponentProjectiveMeshCategory (k := k) c)ᵒᵖ,
      CoveringHom.IsFiniteDimensionalModule
        (C := (S.StandardFormComponentProjectiveMeshCategory (k := k) c)ᵒᵖ) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  intro X
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    let Y' : S.StandardFormComponentMeshCategory (k := k) c := Y.unop.1
    let X' : S.StandardFormComponentMeshCategory (k := k) c := X.unop.1
    letI : FiniteDimensional k (Y' ⟶ X') :=
      S.standardFormComponentMeshHomFinite (k := k) c Y' X'
    letI : FiniteDimensional k (Y.unop ⟶ X.unop) :=
      FiniteDimensional.of_injective
        InducedCategory.homLinearEquiv.toLinearMap
        InducedCategory.homLinearEquiv.injective
    exact FiniteDimensional.of_injective
      (CoveringHom.oppositeHomLinearEquiv X Y).toLinearMap
      (CoveringHom.oppositeHomLinearEquiv X Y).injective
  · exact Set.toFinite _

/-- The category algebra of the projective vertices in one standard-form component. -/
abbrev standardFormComponentAlgebra
    (c : S.StandardFormWalkComponent) : Type u :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra
    (S.standardFormComponentFiniteRightRepresentables (k := k) c)

/-- A component category algebra is finite dimensional. -/
theorem standardFormComponentAlgebra_finiteDimensional
    (c : S.StandardFormWalkComponent) :
    FiniteDimensional k (S.standardFormComponentAlgebra (k := k) c) :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    (S.standardFormComponentFiniteRightRepresentables (k := k) c)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
