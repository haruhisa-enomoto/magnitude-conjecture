import MagnitudeConjecture.Algebra.RightModuleCoherentDuality
import MagnitudeConjecture.Algebra.RightModuleCoherentDefectEvaluation
import MagnitudeConjecture.Algebra.RightModuleRestrictedYonedaHom
import MagnitudeConjecture.CategoryTheory.LinearEquivQuotient

/-!
# Restricted Yoneda and the presentation quotient of a coherent defect

Restricted Yoneda identifies maps between the representables in Auslander's
four-term resolution with ordinary module maps.  This file proves that the
identification carries the presentation coboundaries onto one another and
therefore descends to the corresponding quotients.
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
variable [HasExt.{u} (FG (A := A))]
variable [HasExt.{u} (S.FiniteContravariantFunctor)]

/-- Restricted Yoneda carries the ordinary module-presentation
coboundaries exactly onto the functor-presentation coboundaries. -/
theorem finiteContravariantDefectPresentationRange_map_yoneda
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    (S.finiteCovariantPresentationRange K X).map
        (S.ambientFiniteRestrictedContravariantRepresentableHomLinearEquiv
          K.X₁ X).toLinearMap =
      ProjectivePresentationExt.presentationRange (k := k)
        (S.finiteContravariantDefectLeftShortComplex K)
        (S.finiteContravariantRepresentableOnSkeleton.obj X) := by
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    change ∃ b : K.X₂.obj ⟶ (S.fgObj X).obj,
      K.f.hom ≫ b = a at ha
    obtain ⟨b, rfl⟩ := ha
    change ∃ q, (S.finiteContravariantDefectLeftShortComplex K).f ≫ q = _
    refine ⟨S.finiteRestrictedContravariantRepresentableMap
      (ObjectProperty.homMk b), ?_⟩
    change
      S.finiteRestrictedContravariantRepresentableMap K.f ≫
          S.finiteRestrictedContravariantRepresentableMap
            (ObjectProperty.homMk b) =
        S.finiteRestrictedContravariantRepresentableMap
          (ObjectProperty.homMk (K.f.hom ≫ b))
    exact (S.finiteRestrictedContravariantRepresentableMap_comp
      K.f (ObjectProperty.homMk b)).symm
  · intro hp
    change ∃ q,
      (S.finiteContravariantDefectLeftShortComplex K).f ≫ q = p at hp
    obtain ⟨q, hq⟩ := hp
    obtain ⟨b, rfl⟩ :=
      (S.ambientFiniteRestrictedContravariantRepresentableHomLinearEquiv
        K.X₂ X).surjective q
    refine ⟨K.f.hom ≫ b, ?_, ?_⟩
    · exact ⟨b, rfl⟩
    · change
        S.finiteRestrictedContravariantRepresentableMap
          (ObjectProperty.homMk (K.f.hom ≫ b)) = p
      rw [show ObjectProperty.homMk (K.f.hom ≫ b) =
          K.f ≫ ObjectProperty.homMk b from rfl,
        S.finiteRestrictedContravariantRepresentableMap_comp]
      exact hq

/-- The ordinary module-presentation quotient and the corresponding quotient
of natural-transformation spaces are canonically linearly equivalent. -/
def finiteContravariantDefectPresentationYonedaLinearEquiv
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    ((K.X₁.obj ⟶ (S.fgObj X).obj) ⧸
        S.finiteCovariantPresentationRange K X) ≃ₗ[k]
      (((S.finiteContravariantDefectLeftShortComplex K).X₁ ⟶
            S.finiteContravariantRepresentableOnSkeleton.obj X) ⧸
        ProjectivePresentationExt.presentationRange (k := k)
          (S.finiteContravariantDefectLeftShortComplex K)
          (S.finiteContravariantRepresentableOnSkeleton.obj X)) :=
  LinearEquiv.quotientOfMapEq
    (S.ambientFiniteRestrictedContravariantRepresentableHomLinearEquiv K.X₁ X)
    (S.finiteCovariantPresentationRange K X)
    (ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteContravariantDefectLeftShortComplex K)
      (S.finiteContravariantRepresentableOnSkeleton.obj X))
    (S.finiteContravariantDefectPresentationRange_map_yoneda K X)

@[simp]
theorem finiteContravariantDefectPresentationYonedaLinearEquiv_mk
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory)
    (f : K.X₁.obj ⟶ (S.fgObj X).obj) :
    S.finiteContravariantDefectPresentationYonedaLinearEquiv K X
        (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk
        (S.finiteRestrictedContravariantRepresentableMap
          (ObjectProperty.homMk f)) :=
  LinearEquiv.quotientOfMapEq_mk
    (S.ambientFiniteRestrictedContravariantRepresentableHomLinearEquiv K.X₁ X)
    (S.finiteCovariantPresentationRange K X)
    (ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteContravariantDefectLeftShortComplex K)
      (S.finiteContravariantRepresentableOnSkeleton.obj X))
    (S.finiteContravariantDefectPresentationRange_map_yoneda K X) f

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
