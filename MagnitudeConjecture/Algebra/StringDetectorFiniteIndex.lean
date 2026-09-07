import MagnitudeConjecture.Algebra.StringIndecomposable
import MagnitudeConjecture.Algebra.StringFiniteDetectorFunctor
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteType

/-!
# Finiteness of the detector index in finite representation type

The literal string module attached to a detector index is indecomposable.  A
finite complete indecomposable skeleton therefore assigns it a skeleton
label.  The diagonal/off-diagonal detector calculation shows that two indices
with the same label must coincide.  Thus the full family of finite-string
detectors is finite in the representation-finite setting.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.DetectorIndex

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

section StringPresentation

variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}

abbrev FiniteIndecomposableSkeleton :=
  MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton
    (k := k) (C := (Category P.toPresentation.relations)ᵒᵖ)

/-- A chosen skeleton label for the literal string module represented by a
detector index. -/
def finiteSkeletonLabel (T : FiniteIndecomposableSkeleton (P := P))
    (i : DetectorIndex S) : Fin T.n :=
  Classical.choose
    (T.complete
      (i.endpointWord.word.finiteRightModule P.monomial)
      (i.endpointWord.word.finiteRightModule_indecomposable P.monomial))

/-- The chosen isomorphism from a literal string module to its finite-skeleton
representative. -/
def finiteSkeletonIso (T : FiniteIndecomposableSkeleton (P := P))
    (i : DetectorIndex S) :
    i.endpointWord.word.finiteRightModule P.monomial ≅
      T.obj (finiteSkeletonLabel T i) :=
  Classical.choice
    (Classical.choose_spec
      (T.complete
        (i.endpointWord.word.finiteRightModule P.monomial)
        (i.endpointWord.word.finiteRightModule_indecomposable P.monomial)))

/-- Distinct detector indices have distinct labels in any complete
indecomposable skeleton. -/
theorem finiteSkeletonLabel_injective
    (T : FiniteIndecomposableSkeleton (P := P)) :
    Function.Injective (finiteSkeletonLabel (S := S) T) := by
  classical
  intro i j hij
  by_contra hne
  let e : i.endpointWord.word.finiteRightModule P.monomial ≅
      j.endpointWord.word.finiteRightModule P.monomial :=
    finiteSkeletonIso T i ≪≫
      eqToIso (congrArg T.obj hij) ≪≫
        (finiteSkeletonIso T j).symm
  have hfinrank :=
    (FGModuleCat.isoToLinearEquiv
      (i.finiteDetectorFunctor.mapIso e)).finrank_eq
  change Module.finrank k
      (EndpointWord.DetectorSpace
        (i.endpointWord.word.rightModule P.monomial) i.endpointWord) =
    Module.finrank k
      (EndpointWord.DetectorSpace
        (j.endpointWord.word.rightModule P.monomial) i.endpointWord) at hfinrank
  rw [finrank_detectorSpace_rightModule_endpointWord i i,
    finrank_detectorSpace_rightModule_endpointWord i j] at hfinrank
  simp [hne] at hfinrank

/-- In finite representation type, the entire inversion-class index of
finite-string detectors is finite. -/
theorem finite_of_finiteIndecomposableSkeleton
    (T : FiniteIndecomposableSkeleton (P := P)) :
    Finite (DetectorIndex S) :=
  Finite.of_injective (finiteSkeletonLabel (S := S) T)
    (finiteSkeletonLabel_injective T)

end StringPresentation

section SpecialBiserialPresentation

variable {P : BoundQuiver.SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization}

/-- If the inversion classes of finite string words are finite, then the
literal string words themselves are finite.  Each inversion class contains
at most the chosen representative and its formal inverse. -/
theorem finite_word_of_finite_detectorIndex
    [Finite (DetectorIndex S)] :
    Finite (Word P.toPresentation.relations) := by
  let decode : DetectorIndex S × Bool →
      Word P.toPresentation.relations :=
    fun ib ↦ if ib.2 then ib.1.endpointWord.word.reverse
      else ib.1.endpointWord.word
  apply Finite.of_surjective decode
  intro C
  let i := ofWord S C
  have hi : ofWord S i.endpointWord.word = ofWord S C :=
    ofWord_endpointWord i
  rcases (ofWord_eq_iff S i.endpointWord.word C).mp hi with h | h
  · refine ⟨(i, false), ?_⟩
    simpa [decode] using h
  · refine ⟨(i, true), ?_⟩
    simp [decode, h]

/-- Finiteness of literal words also gives finiteness of every fixed
endpoint-polarized word family. -/
theorem finite_endpointWord_of_finite_detectorIndex
    [Finite (DetectorIndex S)] (u : Q) (t : Bool) :
    Finite (EndpointWord S u t) := by
  letI : Finite (Word P.toPresentation.relations) :=
    finite_word_of_finite_detectorIndex (P := P) (S := S)
  exact Finite.of_injective EndpointWord.word
    (EndpointWord.word_injective S)

/-- A finite detector index supplies a uniform bound on the length of every
literal string word. -/
theorem exists_word_length_bound_of_finite_detectorIndex
    [Finite (DetectorIndex S)] :
    ∃ L : ℕ, ∀ C : Word P.toPresentation.relations, C.length ≤ L := by
  letI : Finite (Word P.toPresentation.relations) :=
    finite_word_of_finite_detectorIndex (P := P) (S := S)
  letI : Fintype (Word P.toPresentation.relations) := Fintype.ofFinite _
  refine ⟨Finset.univ.sup (fun C : Word P.toPresentation.relations ↦
    C.length), ?_⟩
  intro C
  exact Finset.le_sup
    (f := fun C : Word P.toPresentation.relations ↦ C.length)
    (Finset.mem_univ C)

end SpecialBiserialPresentation

section StringPresentation

variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}

/-- The number of finite-string detector indices is bounded by the number of
indecomposable representatives in a complete finite skeleton. -/
theorem natCard_le_skeleton
    (T : FiniteIndecomposableSkeleton (P := P)) :
    Nat.card (DetectorIndex S) ≤ T.n := by
  letI : Finite (DetectorIndex S) :=
    finite_of_finiteIndecomposableSkeleton T
  letI : Fintype (DetectorIndex S) := Fintype.ofFinite _
  simpa using Fintype.card_le_of_injective
    (finiteSkeletonLabel (S := S) T)
    (finiteSkeletonLabel_injective T)

end StringPresentation

end MagnitudeConjecture.BoundQuiver.StringWord.DetectorIndex
