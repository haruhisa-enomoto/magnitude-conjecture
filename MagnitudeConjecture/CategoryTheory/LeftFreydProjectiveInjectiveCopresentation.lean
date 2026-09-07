import MagnitudeConjecture.CategoryTheory.LeftFreydKernel
import MagnitudeConjecture.CategoryTheory.InjectiveEnvelope

/-!
# Constructors for projective-injective copresentations
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Preadditive.LeftFreyd.ProjectiveInjectiveCopresentation

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Regard a two-step minimal injective presentation whose two injective terms
are also projective as a projective-injective copresentation. -/
def ofTwoStepMinimalInjectivePresentation
    {P : C} (I : MagnitudeConjecture.TwoStepMinimalInjectivePresentation P)
    (hI₀Projective : Projective I.augmentation.J)
    (hI₁Projective : Projective I.cosyzygyPresentation.J) :
    ProjectiveInjectiveCopresentation P :=
  { I₀ := ⟨I.augmentation.J, hI₀Projective, inferInstance⟩
    I₁ := ⟨I.cosyzygyPresentation.J, hI₁Projective, inferInstance⟩
    augmentation := I.augmentation.f
    differential := ObjectProperty.homMk I.differential
    zero := I.augmentation_comp_differential
    exact := I.presentationComplex_exact }

end CategoryTheory.Preadditive.LeftFreyd.ProjectiveInjectiveCopresentation
