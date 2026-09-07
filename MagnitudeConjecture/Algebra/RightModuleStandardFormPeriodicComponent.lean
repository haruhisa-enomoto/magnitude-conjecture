import MagnitudeConjecture.Algebra.RightModuleStandardFormOrbitGraph
import MagnitudeConjecture.Algebra.RightModuleStandardFormRiedtmann
import MagnitudeConjecture.CategoryTheory.MeshIdealLifting
import MagnitudeConjecture.CategoryTheory.TranslationQuiverPeriodicComponent
import MagnitudeConjecture.CategoryTheory.TranslationQuiverPeriodicComponentMesh
import MagnitudeConjecture.CategoryTheory.TranslationQuiverRiedtmannDegree
import MagnitudeConjecture.CategoryTheory.TranslationQuiverRiedtmannCover
import MagnitudeConjecture.CategoryTheory.TranslationQuiverHomotopyGroupoidCover
import MagnitudeConjecture.CategoryTheory.TranslationQuiverRiedtmannHomotopyLift
import MagnitudeConjecture.CategoryTheory.TranslationQuiverFreeGroupoidAssembly

/-!
# Periodic stable components of the standard-form mesh

This file specializes the generic periodic-component construction to the
finite standard-form Auslander--Reiten translation quiver.  Each component is
an actual finite stable polarized translation quiver, so Riedtmann's canonical
repetition-quiver cover applies without an additional structural hypothesis.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormPeriodicComponentQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormPeriodicComponentArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

open MeshCategory.RightMeshData.IsTauInjective

/-- Vertices lying in one periodic stable component of the standard-form
translation quiver. -/
abbrev StandardFormPeriodicComponentVertex
    (E : S.StandardFormPeriodicComponent) :=
  PeriodicComponentVertex S.standardFormRightMeshData
    S.standardFormRightMeshData_isTauInjective E

/-- The induced stable polarized mesh data on one standard-form periodic
component. -/
abbrev standardFormPeriodicComponentRightMeshData
    (E : S.StandardFormPeriodicComponent) :=
  periodicComponentRightMeshData S.standardFormRightMeshData
    S.standardFormRightMeshData_isTauInjective E

/-- Every standard-form periodic component has a vertex. -/
theorem standardFormPeriodicComponentVertex_nonempty
    (E : S.StandardFormPeriodicComponent) :
    Nonempty (S.StandardFormPeriodicComponentVertex E) :=
  periodicComponentVertex_nonempty S.standardFormRightMeshData
    S.standardFormRightMeshData_isTauInjective E

/-- The induced component mesh has no projective boundary. -/
theorem standardFormPeriodicComponent_stable
    (E : S.StandardFormPeriodicComponent) :
    (S.standardFormPeriodicComponentRightMeshData E).projective = ∅ :=
  periodicComponentRightMeshData_projective S.standardFormRightMeshData
    S.standardFormRightMeshData_isTauInjective E

/-- Translation is a permutation on every finite standard-form periodic
component. -/
theorem standardFormPeriodicComponent_tau_bijective
    (E : S.StandardFormPeriodicComponent) :
    Function.Bijective
      ((S.standardFormPeriodicComponentRightMeshData E).stableTau
        (S.standardFormPeriodicComponent_stable E)) :=
  periodicComponent_stableTau_bijective S.standardFormRightMeshData
    S.standardFormRightMeshData_isTauInjective E

/-- Every Hom space in a standard-form periodic component mesh is
finite-dimensional. -/
theorem standardFormPeriodicComponentMeshHomFinite
    (E : S.StandardFormPeriodicComponent)
    (x y : S.StandardFormPeriodicComponentVertex E) :
    FiniteDimensional k
      (MeshCategory.obj (k := k)
          (S.standardFormPeriodicComponentRightMeshData E) x ⟶
        MeshCategory.obj (k := k)
          (S.standardFormPeriodicComponentRightMeshData E) y) := by
  apply periodicComponentMeshHomFinite
    S.standardFormRightMeshData
    S.standardFormRightMeshData_isTauInjective E
  · intro a b
    exact S.standardFormMeshHomFinite
      (MeshCategory.obj (k := k) S.standardFormRightMeshData a)
      (MeshCategory.obj (k := k) S.standardFormRightMeshData b)

/-- One path-length cutoff works simultaneously for all Hom spaces of a
fixed finite standard-form periodic component. -/
theorem standardFormPeriodicComponent_exists_uniform_lengthComponent_cutoff
    (E : S.StandardFormPeriodicComponent) :
    ∃ N, ∀ x y d, N ≤ d →
      MeshCategory.lengthComponent (k := k)
        (S.standardFormPeriodicComponentRightMeshData E) x y d = ⊥ := by
  classical
  letI : Fintype (S.StandardFormPeriodicComponentVertex E) :=
    Fintype.ofFinite _
  apply MeshCategory.exists_uniform_lengthComponent_cutoff
  intro x y
  exact S.standardFormPeriodicComponentMeshHomFinite E x y

/-- Consequently, every sufficiently long path in the component vanishes
in its mesh category. -/
theorem standardFormPeriodicComponent_exists_uniform_path_nilpotence
    (E : S.StandardFormPeriodicComponent) :
    ∃ N, ∀ {x y : S.StandardFormPeriodicComponentVertex E}
      (p : Quiver.Path x y), N ≤ p.length →
      (MeshCategory.quotientFunctor (k := k)
        (S.standardFormPeriodicComponentRightMeshData E)).map
          (periodicComponentPathHom (k := k)
            S.standardFormRightMeshData
            S.standardFormRightMeshData_isTauInjective p) = 0 := by
  obtain ⟨N, hN⟩ :=
    S.standardFormPeriodicComponent_exists_uniform_lengthComponent_cutoff E
  refine ⟨N, ?_⟩
  intro x y p hp
  have hmem :
      (MeshCategory.quotientFunctor (k := k)
        (S.standardFormPeriodicComponentRightMeshData E)).map
          (periodicComponentPathHom (k := k)
            S.standardFormRightMeshData
            S.standardFormRightMeshData_isTauInjective p) ∈
        MeshCategory.lengthComponent (k := k)
          (S.standardFormPeriodicComponentRightMeshData E) y x p.length := by
    refine ⟨periodicComponentPathHom (k := k)
      S.standardFormRightMeshData
      S.standardFormRightMeshData_isTauInjective p, ?_, rfl⟩
    unfold periodicComponentPathHom
    exact
      (MagnitudeConjecture.LinearPathCategory.pathHom_mem_lengthComponent_iff
        p p.length).2 rfl
  rw [hN y x p.length hp] at hmem
  simpa using hmem

/-- Riedtmann's sectional-path tree for one based standard-form periodic
component. -/
abbrev StandardFormPeriodicComponentTreeBase
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) :=
  MeshCategory.RightMeshData.SectionalPath
    (S.standardFormPeriodicComponentRightMeshData E) x₀

/-- Riedtmann's sectional-path tree for one based standard-form periodic
component, with its prefix orientation. -/
abbrev StandardFormPeriodicComponentTree
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) :=
  MeshCategory.RightMeshData.RiedtmannCover.Tree
    (S.standardFormPeriodicComponentRightMeshData E) x₀

/-- The canonical Riedtmann mesh cover from the repetition quiver of the
sectional-path tree to the chosen standard-form periodic component. -/
def standardFormPeriodicComponentRiedtmannCover
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) :
    MeshCategory.RightMeshData.Cover
      (S.StandardFormPeriodicComponentTree E x₀).rightMeshData
      (S.standardFormPeriodicComponentRightMeshData E) :=
  MeshCategory.RightMeshData.RiedtmannCover.cover
    (S.standardFormPeriodicComponentRightMeshData E)
    (S.standardFormPeriodicComponent_stable E)
    (S.standardFormPeriodicComponent_tau_bijective E) x₀

/-- The Riedtmann cover acts on the mesh-homotopy groupoids of the repetition
and the periodic component. -/
def standardFormPeriodicComponentRiedtmannHomotopyFunctor
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) :
    MeshCategory.RightMeshData.UniversalCover.HomotopyGroupoid
        (S.StandardFormPeriodicComponentTree E x₀).rightMeshData ⥤
      MeshCategory.RightMeshData.UniversalCover.HomotopyGroupoid
        (S.standardFormPeriodicComponentRightMeshData E) :=
  (S.standardFormPeriodicComponentRiedtmannCover E x₀).homotopyFunctor

/-- The augmented-walk map of the Riedtmann cover is itself a quiver
covering, hence arbitrary augmented walks lift uniquely from a chosen
repetition vertex. -/
theorem standardFormPeriodicComponentRiedtmann_augmented_isCovering
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) :
    let C := S.standardFormPeriodicComponentRiedtmannCover E x₀
    C.augmentedPrefunctor.IsCovering := by
  let C := S.standardFormPeriodicComponentRiedtmannCover E x₀
  apply C.augmentedPrefunctor_isCovering
    (S.StandardFormPeriodicComponentTree E x₀).rightMeshData_projective
    (S.standardFormPeriodicComponent_stable E)
    ?_ (S.standardFormPeriodicComponent_tau_bijective E)
  change Function.Bijective
    (S.StandardFormPeriodicComponentTree E x₀).tauVertex
  exact (S.StandardFormPeriodicComponentTree E x₀).tauVertex_bijective

set_option backward.isDefEq.respectTransparency false in
/-- The uniform component bound pulls back through the faithful Riedtmann
mesh covering, so sufficiently long paths in the repetition mesh vanish. -/
theorem standardFormPeriodicComponentRiedtmann_exists_uniform_path_nilpotence
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) :
    letI : (S.StandardFormPeriodicComponentTree E x₀).graph.LocallyFinite :=
      MeshCategory.RightMeshData.SectionalPath.orientedTree_graphLocallyFinite
        (T := S.standardFormPeriodicComponentRightMeshData E) x₀
    ∃ N, ∀
      {x y : (S.StandardFormPeriodicComponentTree E x₀).Vertex}
      (p : Quiver.Path x y), N ≤ p.length →
      (MeshCategory.quotientFunctor (k := k)
        (S.StandardFormPeriodicComponentTree E x₀).rightMeshData).map
          (MagnitudeConjecture.LinearPathCategory.pathHom (k := k) p) = 0 := by
  letI : (S.StandardFormPeriodicComponentTree E x₀).graph.LocallyFinite :=
    MeshCategory.RightMeshData.SectionalPath.orientedTree_graphLocallyFinite
      (T := S.standardFormPeriodicComponentRightMeshData E) x₀
  let C := S.standardFormPeriodicComponentRiedtmannCover E x₀
  obtain ⟨N, hN⟩ :=
    S.standardFormPeriodicComponent_exists_uniform_path_nilpotence E
  refine ⟨N, ?_⟩
  intro x y p hp
  let hC := C.functorUsingSourceFintype_isCovering (k := k)
  apply hC.map_injective
    (MeshCategory.obj (k := k)
      (S.StandardFormPeriodicComponentTree E x₀).rightMeshData y)
    (MeshCategory.obj (k := k)
      (S.StandardFormPeriodicComponentTree E x₀).rightMeshData x)
  rw [C.functorUsingSourceFintype_map_quotient_pathHom,
    C.functorUsingSourceFintype.map_zero]
  have hmapLength : (C.toPrefunctor.mapPath p).length = p.length := by
    clear hp
    induction p with
    | nil => rfl
    | cons p a ih => simp only [Prefunctor.mapPath_cons,
        Quiver.Path.length_cons, ih]
  simpa only [periodicComponentPathHom] using
    hN (C.toPrefunctor.mapPath p) (by rw [hmapLength]; exact hp)

/-- Every periodic standard-form component has finite Riedtmann tree class.
This is the exact tree-finiteness input needed in the component-graph
deformation. -/
theorem standardFormPeriodicComponentTree_finite
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) :
    Finite (S.StandardFormPeriodicComponentTreeBase E x₀) := by
  letI : (S.StandardFormPeriodicComponentTree E x₀).graph.LocallyFinite :=
    MeshCategory.RightMeshData.SectionalPath.orientedTree_graphLocallyFinite
      (T := S.standardFormPeriodicComponentRightMeshData E) x₀
  obtain ⟨N, hN⟩ :=
    S.standardFormPeriodicComponentRiedtmann_exists_uniform_path_nilpotence
      E x₀
  exact
    RepetitionQuiver.OrientedTree.finite_of_uniform_mesh_nilpotence
      (S.StandardFormPeriodicComponentTree E x₀) N hN

/-- Every integer-degree slice of the canonical Riedtmann repetition cover is
finite. -/
theorem standardFormPeriodicComponentRiedtmannDegree_fiber_finite
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) (d : ℤ) :
    Finite {X : (S.StandardFormPeriodicComponentTree E x₀).Vertex //
      MeshCategory.RightMeshData.SectionalPath.repetitionDegree
        (T := S.standardFormPeriodicComponentRightMeshData E) x₀ X = d} := by
  letI : Finite (S.StandardFormPeriodicComponentTreeBase E x₀) :=
    S.standardFormPeriodicComponentTree_finite E x₀
  exact
    MeshCategory.RightMeshData.SectionalPath.repetitionDegree_fiber_finite
      (T := S.standardFormPeriodicComponentRightMeshData E) x₀ d

/-- The based mesh-homotopy fundamental group of every periodic standard-form
component is free.  The finite Riedtmann tree makes its integer deck-degree
map injective. -/
theorem standardFormPeriodicComponent_fundamentalGroup_isFree
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) :
    IsFreeGroup
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        (S.standardFormPeriodicComponentRightMeshData E) x₀) := by
  letI : Finite (S.StandardFormPeriodicComponentTreeBase E x₀) :=
    S.standardFormPeriodicComponentTree_finite E x₀
  exact
    MeshCategory.RightMeshData.RiedtmannCover.fundamentalGroup_isFree_of_finite_sectionalTree
        (S.standardFormPeriodicComponentRightMeshData E)
        (S.standardFormPeriodicComponent_stable E)
        (S.standardFormPeriodicComponent_tau_bijective E) x₀

/-- The entire mesh-homotopy groupoid of every periodic standard-form
component is free. -/
@[reducible] noncomputable def
    standardFormPeriodicComponent_homotopyGroupoidIsFree
    (E : S.StandardFormPeriodicComponent)
    (x₀ : S.StandardFormPeriodicComponentVertex E) :
    IsFreeGroupoid
      (MeshCategory.RightMeshData.UniversalCover.HomotopyGroupoid
        (S.standardFormPeriodicComponentRightMeshData E)) := by
  letI : IsFreeGroup
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        (S.standardFormPeriodicComponentRightMeshData E) x₀) :=
    S.standardFormPeriodicComponent_fundamentalGroup_isFree E x₀
  exact
    MeshCategory.RightMeshData.UniversalCover.HomotopyGroupoid.isFreeGroupoidOfFundamentalGroupIsFree
      (S.standardFormPeriodicComponentRightMeshData E) x₀
      (periodicComponent_isWalkConnectedAt S.standardFormRightMeshData
        S.standardFormRightMeshData_isTauInjective E x₀)

/-- The full standard-form mesh-homotopy groupoid is free.  The generic
assembly joins the free periodic component groupoids to the nonperiodic
tau-chain mesh edges and canonical sigma-boundary arrows. -/
@[reducible] noncomputable def standardForm_homotopyGroupoidIsFree :
    IsFreeGroupoid
      (MeshCategory.RightMeshData.UniversalCover.HomotopyGroupoid
        S.standardFormRightMeshData) := by
  letI periodicFree : ∀ E : S.StandardFormPeriodicComponent,
      IsFreeGroupoid
        (MeshCategory.RightMeshData.UniversalCover.HomotopyGroupoid
          (S.standardFormPeriodicComponentRightMeshData E)) :=
    fun E ↦ S.standardFormPeriodicComponent_homotopyGroupoidIsFree E
      (Classical.choice (S.standardFormPeriodicComponentVertex_nonempty E))
  exact
    MeshCategory.RightMeshData.IsTauInjective.isFreeGroupoidOfPeriodicComponents
      S.standardFormRightMeshData S.standardFormRightMeshData_isTauInjective

/-- The fundamental group of the connected standard-form translation quiver
is free. -/
theorem standardForm_fundamentalGroup_isFree
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    IsFreeGroup
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) := by
  letI : IsFreeGroupoid
      (MeshCategory.RightMeshData.UniversalCover.HomotopyGroupoid
        S.standardFormRightMeshData) :=
    S.standardForm_homotopyGroupoidIsFree
  exact
    MeshCategory.RightMeshData.UniversalCover.HomotopyGroupoid.fundamentalGroup_isFree_of_isFreeGroupoid
      S.standardFormRightMeshData x₀ hconnected

/-- The standard-form deck group is torsion-free. -/
theorem standardForm_fundamentalGroup_isMulTorsionFree
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    IsMulTorsionFree
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) := by
  letI : IsFreeGroup
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) :=
    S.standardForm_fundamentalGroup_isFree x₀ hconnected
  exact MagnitudeConjecture.isMulTorsionFreeOfIsFreeGroup _

/-- The standard-form deck group is residually finite. -/
theorem standardForm_fundamentalGroup_residuallyFinite
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    Group.ResiduallyFinite
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) := by
  letI : IsFreeGroup
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) :=
    S.standardForm_fundamentalGroup_isFree x₀ hconnected
  exact MagnitudeConjecture.residuallyFiniteOfIsFreeGroup _

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
