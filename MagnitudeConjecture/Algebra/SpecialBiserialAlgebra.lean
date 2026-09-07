import MagnitudeConjecture.Algebra.BoundQuiverPresentation
import Mathlib.RingTheory.Morita.Basic

/-!
# Special-biserial algebras up to Morita equivalence

The frozen manuscript calls an algebra special biserial when its basic
algebra admits a special-biserial bound-quiver presentation.  This file
records that convention literally: a witness consists of a Morita-equivalent
algebra and the exact bound-quiver presentation from
`BoundQuiverPresentation`.  Such a bound-quiver algebra is itself the chosen
basic representative, so basicness is not stored as a redundant field.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture

universe u

namespace BoundQuiver

variable {k A B : Type u}
variable [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [Ring B] [Algebra k B] [FiniteDimensional k B]

/-- A special-biserial bound-quiver representative of the Morita class of
`A`. -/
structure SpecialBiserialMoritaModel (k A : Type u)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] where
  Carrier : Type u
  [ring : Ring Carrier]
  [algebra : Algebra k Carrier]
  [finiteDimensional : FiniteDimensional k Carrier]
  morita : MoritaEquivalence k A Carrier
  presentation : AdmitsSpecialBiserialPresentation k Carrier

namespace SpecialBiserialMoritaModel

attribute [instance] ring algebra finiteDimensional

/-- Change the source algebra of a special-biserial Morita model. -/
def precompMorita
    (M : SpecialBiserialMoritaModel k A)
    (e : MoritaEquivalence k B A) :
    SpecialBiserialMoritaModel k B where
  Carrier := M.Carrier
  morita := MoritaEquivalence.trans k e M.morita
  presentation := M.presentation

end SpecialBiserialMoritaModel

/-- The manuscript's convention for an arbitrary finite-dimensional algebra:
some basic representative of its Morita class has a special-biserial
bound-quiver presentation. -/
def IsSpecialBiserial (k A : Type u)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] : Prop :=
  Nonempty (SpecialBiserialMoritaModel k A)

/-- An algebra carrying the literal presentation is special biserial in the
manuscript's Morita-invariant sense. -/
theorem isSpecialBiserial_of_presentation
    (hpresentation : AdmitsSpecialBiserialPresentation k A) :
    IsSpecialBiserial k A :=
  ⟨{
    Carrier := A
    morita := MoritaEquivalence.refl k A
    presentation := hpresentation
  }⟩

/-- Special biseriality depends only on the Morita class of the algebra. -/
theorem isSpecialBiserial_iff_of_moritaEquivalence
    (e : MoritaEquivalence k A B) :
    IsSpecialBiserial k A ↔ IsSpecialBiserial k B := by
  constructor
  · rintro ⟨M⟩
    exact ⟨M.precompMorita (MoritaEquivalence.symm k e)⟩
  · rintro ⟨M⟩
    exact ⟨M.precompMorita e⟩

/-- In particular, special biseriality is invariant under algebra
equivalence. -/
theorem isSpecialBiserial_iff_of_algEquiv (e : A ≃ₐ[k] B) :
    IsSpecialBiserial k A ↔ IsSpecialBiserial k B :=
  isSpecialBiserial_iff_of_moritaEquivalence
    (MoritaEquivalence.ofAlgEquiv e)

end BoundQuiver

end MagnitudeConjecture
