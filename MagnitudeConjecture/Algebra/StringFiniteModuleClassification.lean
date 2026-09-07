import MagnitudeConjecture.Algebra.StringDetectorFiniteIndex
import MagnitudeConjecture.Algebra.StringReverse

/-!
# Isomorphism classification of literal finite string modules

The finite detector family separates inversion classes.  Applying one
detector to an isomorphism between two literal string modules therefore shows
that the underlying words agree up to formal reversal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}

namespace Word

/-- Reversal of words, bundled in the finite-dimensional linear-module
category. -/
def finiteReverseRightModuleIso
    (C : Word P.toPresentation.relations) :
    C.finiteRightModule P.monomial ≅
      C.reverse.finiteRightModule P.monomial := by
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  exact reverseRightModuleIso C P.monomial

end Word

namespace DetectorIndex

private theorem nonempty_endpointWordFiniteRightModuleIso
    (C : Word P.toPresentation.relations)
    (i : DetectorIndex S) (hi : i = ofWord S C) :
    Nonempty (i.endpointWord.word.finiteRightModule P.monomial ≅
      C.finiteRightModule P.monomial) := by
  have hindex : ofWord S i.endpointWord.word = ofWord S C := by
    rw [← hi]
    exact ofWord_endpointWord i
  rcases (ofWord_eq_iff S i.endpointWord.word C).mp hindex with h | h
  · exact ⟨eqToIso (congrArg (fun W : Word P.toPresentation.relations ↦
      W.finiteRightModule P.monomial) h)⟩
  · exact ⟨eqToIso (congrArg (fun W : Word P.toPresentation.relations ↦
      W.finiteRightModule P.monomial) h) ≪≫
        (C.finiteReverseRightModuleIso).symm⟩

private noncomputable def endpointWordFiniteRightModuleIso
    (C : Word P.toPresentation.relations)
    (i : DetectorIndex S) (hi : i = ofWord S C) :
    i.endpointWord.word.finiteRightModule P.monomial ≅
      C.finiteRightModule P.monomial :=
  Classical.choice (nonempty_endpointWordFiniteRightModuleIso C i hi)

/-- Two literal finite string modules are isomorphic only when their words
agree up to formal reversal. -/
theorem eq_or_eq_reverse_of_finiteRightModule_iso
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (C D : Word P.toPresentation.relations)
    (e : C.finiteRightModule P.monomial ≅
      D.finiteRightModule P.monomial) :
    C = D ∨ C = D.reverse := by
  classical
  let i := ofWord S C
  let j := ofWord S D
  let eC : i.endpointWord.word.finiteRightModule P.monomial ≅
      C.finiteRightModule P.monomial :=
    endpointWordFiniteRightModuleIso C i rfl
  let eD : j.endpointWord.word.finiteRightModule P.monomial ≅
      D.finiteRightModule P.monomial :=
    endpointWordFiniteRightModuleIso D j rfl
  let eij : i.endpointWord.word.finiteRightModule P.monomial ≅
      j.endpointWord.word.finiteRightModule P.monomial :=
    eC ≪≫ e ≪≫ eD.symm
  have hfinrank :=
    (FGModuleCat.isoToLinearEquiv
      (i.finiteDetectorFunctor.mapIso eij)).finrank_eq
  change Module.finrank k
      (EndpointWord.DetectorSpace
        (i.endpointWord.word.rightModule P.monomial) i.endpointWord) =
    Module.finrank k
      (EndpointWord.DetectorSpace
        (j.endpointWord.word.rightModule P.monomial) i.endpointWord) at hfinrank
  rw [finrank_detectorSpace_rightModule_endpointWord i i,
    finrank_detectorSpace_rightModule_endpointWord i j] at hfinrank
  have hij : i = j := by
    by_contra hne
    simp [hne] at hfinrank
  exact (ofWord_eq_iff S C D).mp hij

end DetectorIndex

end MagnitudeConjecture.BoundQuiver.StringWord
