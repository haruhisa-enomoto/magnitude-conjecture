import MagnitudeConjecture.Algebra.RightModuleStandardFormOppositeProjectiveCover
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence

/-!
# The standard-form algebra as the opposite projective deck-orbit algebra

The strict deck-orbit skeleton of the opposite lifted projective category has
already been identified with the exact opposite projective mesh category used
to define the standard-form algebra.  Here the literal object bijection is
used to identify the corresponding finite category algebras.
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

local instance standardFormOrbitAlgebraQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormOrbitAlgebraArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

/-- Connectedness and the strict orbit identification make the opposite
projective orbit set finite. -/
theorem standardFormOppositeProjectiveDeckOrbitFinite
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only
  exact Finite.of_injective
    (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
      S x₀ hconnected).functor.obj
    (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_obj_injective
      S x₀ hconnected)

/-- The opposite projective deck-orbit category has finite-dimensional
covariant representables, transported from the finite standard-form mesh
category along the strict orbit equivalence. -/
theorem standardFormOppositeProjectiveDeckOrbitFiniteRightRepresentables
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hfinite : S.StandardFormMeshHomFinite) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI : Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
      standardFormOppositeProjectiveDeckOrbitFinite S x₀ hconnected
    ∀ X : CoveringHom.DeckOrbitSkeleton
        (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
        (ProjectiveGroup S x₀),
      CoveringHom.IsFiniteDimensionalModule
        (C := CoveringHom.DeckOrbitSkeleton
          (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
          (ProjectiveGroup S x₀)) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveDeckOrbitFinite S x₀ hconnected
  letI : Finite (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (ProjectiveGroup S x₀)) := by
    change Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    infer_instance
  letI : Fintype (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (ProjectiveGroup S x₀)) := Fintype.ofFinite _
  let e := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
    S x₀ hconnected
  letI : e.functor.Additive := inferInstance
  letI : e.functor.Linear k := inferInstance
  exact CoveringHom.linearCoyonedaFiniteOfFullyFaithful
    (k := k) e.functor (S.standardFormFiniteRightRepresentables hfinite)

/-- The finite category algebra of the strict opposite projective deck orbit.
Its finite representables are transported from the standard-form category,
so this definition does not impose an artificial universe equality between
the deck group and the coefficient field. -/
noncomputable abbrev standardFormOppositeProjectiveDeckOrbitAlgebra
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hfinite : S.StandardFormMeshHomFinite) : Type u := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveDeckOrbitFinite S x₀ hconnected
  letI : Finite (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (ProjectiveGroup S x₀)) := by
    change Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    infer_instance
  letI : Fintype (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (ProjectiveGroup S x₀)) := Fintype.ofFinite _
  exact CoveringHom.finiteCategoryProjectiveGenerator.algebra
    (standardFormOppositeProjectiveDeckOrbitFiniteRightRepresentables
      S x₀ hconnected hfinite)

/-- The finite category algebra of the strict opposite projective deck orbit
is the manuscript's literal standard-form algebra. -/
noncomputable def standardFormOppositeProjectiveOrbitCategoryAlgebraEquiv
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hfinite : S.StandardFormMeshHomFinite) :
    standardFormOppositeProjectiveDeckOrbitAlgebra
        S x₀ hconnected hfinite ≃ₐ[k]
      S.standardFormAlgebra hfinite := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :=
    standardFormOppositeProjectiveDeckOrbitFinite S x₀ hconnected
  letI : Finite (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (ProjectiveGroup S x₀)) := by
    change Finite (MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    infer_instance
  letI : Fintype (CoveringHom.DeckOrbitSkeleton
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (ProjectiveGroup S x₀)) := Fintype.ofFinite _
  let e := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
    S x₀ hconnected
  letI : e.functor.Additive := inferInstance
  letI : e.functor.Linear k := inferInstance
  exact CoveringHom.finiteCategoryAlgebraEquiv
    (standardFormOppositeProjectiveDeckOrbitFiniteRightRepresentables
      S x₀ hconnected hfinite)
    (S.standardFormFiniteRightRepresentables hfinite)
    e
    (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_obj_bijective
      S x₀ hconnected)

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
