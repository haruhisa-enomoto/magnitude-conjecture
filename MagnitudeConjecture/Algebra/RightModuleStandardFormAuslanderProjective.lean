import MagnitudeConjecture.Algebra.RightModuleStandardFormAuslanderRepresentable
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates

/-!
# Projective-injective copresentations of projective standard-mesh modules
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormAuslanderProjectiveQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormAuslanderProjectiveArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- Every projective finite module on the standard mesh has a two-term
projective-injective copresentation. -/
theorem standardFormProjective_projectiveInjectiveCopresentation_nonempty
    (P : CategoryTheory.ProjectiveObject
      S.StandardFormFiniteContravariantModuleCategory) :
    Nonempty (LeftFreyd.ProjectiveInjectiveCopresentation P.obj) := by
  classical
  let T := S.standardFormRightMeshData
  let hP := S.standardFormFiniteContravariantRepresentables
  obtain ⟨Q⟩ := finiteRepresentableCoordinates_nonempty_of_projective
    hP (fun X ↦ S.standardFormOppositeVertexCategoryEndLocal X) P.obj
  let R (j : Fin Q.n) :=
    T.contravariantRepresentableFiniteModule (k := k) hP (Q.X j).unop
  let Irep (j : Fin Q.n) :
      LeftFreyd.ProjectiveInjectiveCopresentation (R j) :=
    S.standardFormContravariantRepresentableProjectiveInjectiveCopresentation
      (Q.X j).unop
  let ecoord (j : Fin Q.n) : R j ≅
      (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op (Q.X j)) :=
    (T.contravariantRepresentableFiniteIso (k := k) hP (Q.X j).unop).symm
  let Icoord (j : Fin Q.n) :
      LeftFreyd.ProjectiveInjectiveCopresentation
        ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
          (Opposite.op (Q.X j))) :=
    (Irep j).ofIso (ecoord j)
  let Isum := LeftFreyd.ProjectiveInjectiveCopresentation.biproduct
    (fun j ↦ (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
      (Opposite.op (Q.X j))) Icoord
  exact ⟨Isum.ofIso Q.isoSource⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
