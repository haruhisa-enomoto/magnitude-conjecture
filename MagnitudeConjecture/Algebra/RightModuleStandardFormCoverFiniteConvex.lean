import MagnitudeConjecture.Algebra.RightModuleStandardFormCoverLocallyBounded
import MagnitudeConjecture.CategoryTheory.FiniteConvexRanked
import MagnitudeConjecture.CategoryTheory.TranslationQuiverUniversalMeshRank

/-!
# Finite convex neighborhoods in the concrete standard-form cover

The canonical augmented-walk degree strictly decreases along nonzero
nonisomorphisms of the raw universal mesh category, and therefore strictly
increases after restricting to projective vertices and taking the opposite.
Local boundedness supplies finite branching, so bounded rank reachability
gives the finite convex neighborhoods required by admissibility.
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

local instance standardFormCoverFiniteConvexQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormCoverFiniteConvexArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormCoverFiniteConvexBaseStarFintype
    (x : Fin S.n) : Fintype (Quiver.Star x) := by
  infer_instance

namespace UniversalCover

/-- Canonical augmented-walk degree of an object of the raw universal mesh
category. -/
def standardFormUniversalObjectDegree
    (p : Fin S.n) (X : SourceCategory S p) : ℤ :=
  MeshCategory.RightMeshData.UniversalCover.vertexDegree
    S.standardFormRightMeshData p
      (MagnitudeConjecture.LinearPathCategory.vertex X.as)

/-- A nonzero nonisomorphism in the raw universal mesh category strictly
decreases augmented-walk degree. -/
theorem standardFormUniversalObjectDegree_strict
    (p : Fin S.n) {X Y : SourceCategory S p}
    (hXY : CoveringHom.BaseNonzeroNonisomorphism X Y) :
    standardFormUniversalObjectDegree S p Y <
      standardFormUniversalObjectDegree S p X := by
  rcases hXY with ⟨f, hf, hnotIso⟩
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  let W := MagnitudeConjecture.LinearPathCategory.vertex X
  let Z := MagnitudeConjecture.LinearPathCategory.vertex Y
  change
    MeshCategory.obj (k := k)
        (MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData p) W ⟶
      MeshCategory.obj (k := k)
        (MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData p) Z at f
  letI : Nontrivial
      (MeshCategory.obj (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData p) W ⟶
        MeshCategory.obj (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData p) Z) :=
    ⟨⟨f, 0, hf⟩⟩
  obtain ⟨n, hdegree, hncomponent⟩ :=
    MeshCategory.RightMeshData.UniversalCover.exists_meshLength_of_nontrivial_hom
      (k := k) S.standardFormRightMeshData p W Z
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hWZ : W = Z := by
      by_contra hWZ
      apply hncomponent
      exact MeshCategory.lengthComponent_zero_eq_bot_of_ne
        (k := k)
        (MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData p) (Ne.symm hWZ)
    change X = Y at hWZ
    subst Y
    change
      MeshCategory.obj (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData p) W ⟶
        MeshCategory.obj (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData p) W at f
    apply hnotIso
    exact
      MeshCategory.RightMeshData.UniversalCover.meshEndomorphism_isIso_of_ne_zero
        (k := k) S.standardFormRightMeshData p W f hf
  change
    MeshCategory.RightMeshData.UniversalCover.vertexDegree
        S.standardFormRightMeshData p Z <
      MeshCategory.RightMeshData.UniversalCover.vertexDegree
        S.standardFormRightMeshData p W
  omega

/-- The rank used on the opposite projective source category. -/
def standardFormOppositeProjectiveObjectDegree
    (p : Fin S.n)
    (X : (StandardFormProjectiveSourceCategory S p)ᵒᵖ) : ℤ :=
  standardFormUniversalObjectDegree S p X.unop.obj

/-- Nonzero nonisomorphisms in the opposite projective source category
strictly increase augmented-walk degree. -/
theorem standardFormOppositeProjectiveObjectDegree_strict
    (p : Fin S.n)
    {X Y : (StandardFormProjectiveSourceCategory S p)ᵒᵖ}
    (hXY : CoveringHom.BaseNonzeroNonisomorphism X Y) :
    standardFormOppositeProjectiveObjectDegree S p X <
      standardFormOppositeProjectiveObjectDegree S p Y := by
  rcases hXY with ⟨f, hf, hnotIso⟩
  let F := (standardFormProjectiveProperty S p).ι
  let g := F.map f.unop
  have hfunop : f.unop ≠ 0 := by
    intro hzero
    apply hf
    apply Quiver.Hom.unop_inj
    simpa using hzero
  have hg : g ≠ 0 := by
    intro hg
    apply hfunop
    apply F.map_injective
    simpa [g] using hg
  have hgnotIso : ¬ IsIso g := by
    intro hgIso
    apply hnotIso
    letI : IsIso g := hgIso
    letI : IsIso f.unop := isIso_of_reflects_iso f.unop F
    exact (isIso_unop_iff f).mp inferInstance
  exact standardFormUniversalObjectDegree_strict S p ⟨g, hg, hgnotIso⟩

/-- Every object has only finitely many outgoing nonzero nonisomorphism
neighbors in the opposite projective source category. -/
theorem standardFormOppositeProjectiveBaseSuccessorsFinite
    (p : Fin S.n)
    (X : (StandardFormProjectiveSourceCategory S p)ᵒᵖ) :
    {Y | CoveringHom.BaseNonzeroNonisomorphism X Y}.Finite := by
  let H := standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S p
  exact (H.finiteCovariantRepresentables X).2.subset fun Y hY ↦ by
    rcases hY with ⟨f, hf, _⟩
    exact ⟨⟨f, 0, hf⟩⟩

/-- The opposite projective source category has the finite convex object
neighborhoods required by the manuscript's admissibility package. -/
theorem standardFormOppositeProjectiveSourceCategoryHasFiniteConvexObjectNeighborhoods
    (p : Fin S.n) :
    CoveringHom.HasFiniteConvexObjectNeighborhoods
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) :=
  CoveringHom.hasFiniteConvexObjectNeighborhoods_of_rank
    (CoveringHom.BaseNonzeroNonisomorphism
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ))
    (standardFormOppositeProjectiveObjectDegree S p)
    (standardFormOppositeProjectiveBaseSuccessorsFinite S p)
    (standardFormOppositeProjectiveObjectDegree_strict S p)

/-- The sign-reversed augmented-walk degree on the projective source
category. -/
def standardFormProjectiveObjectDegree
    (p : Fin S.n)
    (X : StandardFormProjectiveSourceCategory S p) : ℤ :=
  -standardFormUniversalObjectDegree S p X.obj

/-- Nonzero nonisomorphisms in the projective source category strictly
increase the sign-reversed augmented-walk degree. -/
theorem standardFormProjectiveObjectDegree_strict
    (p : Fin S.n)
    {X Y : StandardFormProjectiveSourceCategory S p}
    (hXY : CoveringHom.BaseNonzeroNonisomorphism X Y) :
    standardFormProjectiveObjectDegree S p X <
      standardFormProjectiveObjectDegree S p Y := by
  rcases hXY with ⟨f, hf, hnotIso⟩
  let F := (standardFormProjectiveProperty S p).ι
  let g := F.map f
  have hg : g ≠ 0 := by
    intro hg
    apply hf
    apply F.map_injective
    simpa [g] using hg
  have hgnotIso : ¬ IsIso g := by
    intro hgIso
    apply hnotIso
    letI : IsIso g := hgIso
    exact isIso_of_reflects_iso f F
  have hdegree := standardFormUniversalObjectDegree_strict S p
    (X := X.obj) (Y := Y.obj) ⟨g, hg, hgnotIso⟩
  change -standardFormUniversalObjectDegree S p X.obj <
    -standardFormUniversalObjectDegree S p Y.obj
  omega

/-- Every projective-source object has finitely many outgoing nonzero
nonisomorphism neighbors. -/
theorem standardFormProjectiveBaseSuccessorsFinite
    (p : Fin S.n)
    (X : StandardFormProjectiveSourceCategory S p) :
    {Y | CoveringHom.BaseNonzeroNonisomorphism X Y}.Finite := by
  let H := standardFormProjectiveSourceCategoryIsLocallyBounded S p
  exact (H.finiteCovariantRepresentables X).2.subset fun Y hY ↦ by
    rcases hY with ⟨f, hf, _⟩
    exact ⟨⟨f, 0, hf⟩⟩

/-- The projective source category also has finite convex object
neighborhoods; this is the variance-reversed window used for left
representables. -/
theorem standardFormProjectiveSourceCategoryHasFiniteConvexObjectNeighborhoods
    (p : Fin S.n) :
    CoveringHom.HasFiniteConvexObjectNeighborhoods
      (C := StandardFormProjectiveSourceCategory S p) :=
  CoveringHom.hasFiniteConvexObjectNeighborhoods_of_rank
    (CoveringHom.BaseNonzeroNonisomorphism
      (C := StandardFormProjectiveSourceCategory S p))
    (standardFormProjectiveObjectDegree S p)
    (standardFormProjectiveBaseSuccessorsFinite S p)
    (standardFormProjectiveObjectDegree_strict S p)

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
