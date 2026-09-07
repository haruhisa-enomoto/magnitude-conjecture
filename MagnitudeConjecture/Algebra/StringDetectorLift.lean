import MagnitudeConjecture.Algebra.StringDetectorFunctor
import Mathlib.Algebra.Module.Projective

/-!
# Linear representatives of finite-string detector classes

The detector is a quotient of its numerator.  Over a field its quotient map
has a linear section, providing a chosen numerator representative of every
detector class.  Coherent lifting of that representative along the word is
constructed separately in `StringDetectorTrajectory`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]

namespace EndpointWord

variable {A : Type u} [Ring A] [Algebra k A]
variable [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u₀ : Q} {t : Bool}

/-- The quotient map from the detector numerator to the detector space. -/
def detectorQuotientMap
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    detectorNumerator N C →ₗ[k] DetectorSpace N C :=
  Submodule.mkQ (detectorDenominatorInNumerator N C)

/-- The detector quotient map is surjective. -/
theorem detectorQuotientMap_surjective
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    Function.Surjective (detectorQuotientMap N C) :=
  Submodule.mkQ_surjective _

/-- A chosen linear representative in the numerator for each detector
quotient class. -/
def detectorRepresentative
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    DetectorSpace N C →ₗ[k] detectorNumerator N C :=
  Classical.choose
    ((detectorQuotientMap N C).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 (detectorQuotientMap_surjective N C)))

/-- Taking the class of the chosen representative recovers the original
detector class. -/
theorem detectorQuotientMap_comp_detectorRepresentative
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    detectorQuotientMap N C ∘ₗ detectorRepresentative N C =
      LinearMap.id :=
  Classical.choose_spec
    ((detectorQuotientMap N C).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 (detectorQuotientMap_surjective N C)))

/-- The chosen numerator representative, regarded as a member of the upper
word subspace along `C`. -/
def detectorUpperRepresentative
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    DetectorSpace N C →ₗ[k] upperSubspace N C :=
  LinearMap.codRestrict (upperSubspace N C)
    ((detectorNumerator N C).subtype.comp
      (detectorRepresentative N C))
        (fun z ↦ (detectorRepresentative N C z).property.2)

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
