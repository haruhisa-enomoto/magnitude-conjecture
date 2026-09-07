import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectExtTwo
import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectEvaluation
import MagnitudeConjecture.Algebra.RightModuleRestrictedCoyonedaHom
import MagnitudeConjecture.CategoryTheory.LinearEquivQuotient

/-!
# Restricted covariant Yoneda and the reverse presentation quotient

Restricted covariant Yoneda carries the ordinary module coboundaries in a
covariant-defect presentation onto the corresponding natural-transformation
coboundaries.  It therefore descends to the quotient computing reverse
coherent duality.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable [HasExt.{u} (S.FiniteCovariantFunctor)]

/-- Restricted covariant Yoneda identifies the two presentation ranges. -/
theorem finiteCovariantDefectPresentationRange_map_coyoneda
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    (S.finiteContravariantPresentationRange K X).map
        (S.ambientFiniteRestrictedCovariantRepresentableHomLinearEquiv
          K.X₃ X).toLinearMap =
      ProjectivePresentationExt.presentationRange (k := k)
        (S.finiteCovariantDefectLeftShortComplex K)
        (S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X)) := by
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    change ∃ b : (S.fgObj X).obj ⟶ K.X₂.obj,
      b ≫ K.g.hom = a at ha
    obtain ⟨b, rfl⟩ := ha
    change ∃ q, (S.finiteCovariantDefectLeftShortComplex K).f ≫ q = _
    refine ⟨S.finiteRestrictedCovariantRepresentableMap
      (ObjectProperty.homMk b), ?_⟩
    change
      S.finiteRestrictedCovariantRepresentableMap K.g ≫
          S.finiteRestrictedCovariantRepresentableMap
            (ObjectProperty.homMk b) =
        S.finiteRestrictedCovariantRepresentableMap
          (ObjectProperty.homMk (b ≫ K.g.hom))
    exact S.finiteRestrictedCovariantRepresentableMap_comp
      (ObjectProperty.homMk b) K.g
  · intro hp
    change ∃ q,
      (S.finiteCovariantDefectLeftShortComplex K).f ≫ q = p at hp
    obtain ⟨q, hq⟩ := hp
    obtain ⟨b, rfl⟩ :=
      (S.ambientFiniteRestrictedCovariantRepresentableHomLinearEquiv
        K.X₂ X).surjective q
    refine ⟨b ≫ K.g.hom, ?_, ?_⟩
    · exact ⟨b, rfl⟩
    · change
        S.finiteRestrictedCovariantRepresentableMap
          (ObjectProperty.homMk (b ≫ K.g.hom)) = p
      rw [show ObjectProperty.homMk (b ≫ K.g.hom) =
          ObjectProperty.homMk b ≫ K.g from rfl,
        S.finiteRestrictedCovariantRepresentableMap_comp]
      exact hq

/-- The module presentation quotient and the corresponding quotient of
natural-transformation spaces are canonically linearly equivalent. -/
def finiteCovariantDefectPresentationCoyonedaLinearEquiv
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    (((S.fgObj X).obj ⟶ K.X₃.obj) ⧸
        S.finiteContravariantPresentationRange K X) ≃ₗ[k]
      (((S.finiteCovariantDefectLeftShortComplex K).X₁ ⟶
            S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X)) ⧸
        ProjectivePresentationExt.presentationRange (k := k)
          (S.finiteCovariantDefectLeftShortComplex K)
          (S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X))) :=
  LinearEquiv.quotientOfMapEq
    (S.ambientFiniteRestrictedCovariantRepresentableHomLinearEquiv K.X₃ X)
    (S.finiteContravariantPresentationRange K X)
    (ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteCovariantDefectLeftShortComplex K)
      (S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X)))
    (S.finiteCovariantDefectPresentationRange_map_coyoneda K X)

@[simp]
theorem finiteCovariantDefectPresentationCoyonedaLinearEquiv_mk
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory)
    (f : (S.fgObj X).obj ⟶ K.X₃.obj) :
    S.finiteCovariantDefectPresentationCoyonedaLinearEquiv K X
        (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk
        (S.finiteRestrictedCovariantRepresentableMap
          (ObjectProperty.homMk f)) :=
  LinearEquiv.quotientOfMapEq_mk
    (S.ambientFiniteRestrictedCovariantRepresentableHomLinearEquiv K.X₃ X)
    (S.finiteContravariantPresentationRange K X)
    (ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteCovariantDefectLeftShortComplex K)
      (S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X)))
    (S.finiteCovariantDefectPresentationRange_map_coyoneda K X) f

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
