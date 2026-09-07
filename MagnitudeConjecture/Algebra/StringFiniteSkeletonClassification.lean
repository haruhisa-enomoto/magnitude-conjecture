import MagnitudeConjecture.Algebra.StringReconstructionCoverage
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecompositionUniqueness

/-!
# Classification of a finite indecomposable skeleton by strings

Detector reconstruction writes every finite-dimensional module as a finite
biproduct of literal string modules.  If the module is indecomposable, its
local endomorphism ring forces one coordinate projection of this biproduct to
be an isomorphism.  Consequently the already injective map from detector
indices to any complete finite indecomposable skeleton is also surjective.

This is the duplicate-free object-classification interface needed by the
Butler--Ringel almost-split argument.  It introduces no periodic-string or
band-module compatibility layer.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.BoundQuiver.StringWord.DetectorIndex

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}

/-- Every label of a complete finite indecomposable skeleton is represented
by the literal string belonging to a detector index. -/
theorem finiteSkeletonLabel_surjective
    (T : FiniteIndecomposableSkeleton (P := P)) :
    Function.Surjective (finiteSkeletonLabel (S := S) T) := by
  classical
  letI : Finite (DetectorIndex S) :=
    finite_of_finiteIndecomposableSkeleton T
  letI : Fintype (DetectorIndex S) := Fintype.ofFinite _
  intro j
  let N := T.obj j
  let n := Fintype.card (ReconstructionCopyIndex (S := S) N)
  let M : Fin n → Word P.toPresentation.relations :=
    reconstructionWord (S := S) N
  let e : N ≅ ⨁ fun t : Fin n ↦ (M t).finiteRightModule P.monomial :=
    reconstructionIsoFiniteStringBiproduct S N
  obtain ⟨t, ht⟩ :=
    MagnitudeConjecture.CategoryTheory.exists_isIso_component_of_retraction_finBiproduct
      (T.indecomposable j) (T.obj_end_local j) n
      (fun q ↦ (M q).finiteRightModule P.monomial)
      (fun q ↦ (M q).finiteRightModule_indecomposable P.monomial)
      e.hom e.inv e.hom_inv_id
  letI : IsIso
      (e.hom ≫ biproduct.π
        (fun q : Fin n ↦ (M q).finiteRightModule P.monomial) t) := ht
  let eString : N ≅ (M t).finiteRightModule P.monomial :=
    asIso (e.hom ≫ biproduct.π
      (fun q : Fin n ↦ (M q).finiteRightModule P.monomial) t)
  let p : ReconstructionCopyIndex (S := S) N :=
    reconstructionCopyEquiv (S := S) N t
  let i : DetectorIndex S := p.1
  let eLiteral : i.endpointWord.word.finiteRightModule P.monomial ≅ N := by
    simpa [i, p, M, reconstructionWord] using eString.symm
  refine ⟨i, ?_⟩
  apply T.skeletal
  exact ⟨(finiteSkeletonIso T i).symm ≪≫ eLiteral⟩

/-- Detector indices and the labels of any complete duplicate-free finite
indecomposable skeleton are canonically equivalent after making the existing
classical choices. -/
def finiteSkeletonEquiv
    (T : FiniteIndecomposableSkeleton (P := P)) :
    DetectorIndex S ≃ Fin T.n :=
  Equiv.ofBijective (finiteSkeletonLabel (S := S) T)
    ⟨finiteSkeletonLabel_injective T,
      finiteSkeletonLabel_surjective T⟩

/-- The detector index chosen to represent one finite-skeleton label. -/
def detectorIndexOfFiniteSkeletonLabel
    (T : FiniteIndecomposableSkeleton (P := P)) (j : Fin T.n) :
    DetectorIndex S :=
  (finiteSkeletonEquiv (S := S) T).symm j

@[simp]
theorem finiteSkeletonLabel_detectorIndexOfFiniteSkeletonLabel
    (T : FiniteIndecomposableSkeleton (P := P)) (j : Fin T.n) :
    finiteSkeletonLabel T (detectorIndexOfFiniteSkeletonLabel (S := S) T j) = j :=
  (finiteSkeletonEquiv (S := S) T).apply_symm_apply j

/-- The literal string canonically selected for a finite-skeleton label is
isomorphic to that skeleton object. -/
def finiteSkeletonStringIso
    (T : FiniteIndecomposableSkeleton (P := P)) (j : Fin T.n) :
    (detectorIndexOfFiniteSkeletonLabel (S := S) T j).endpointWord.word.finiteRightModule
        P.monomial ≅
      T.obj j :=
  finiteSkeletonIso T
      (detectorIndexOfFiniteSkeletonLabel (S := S) T j) ≪≫
    eqToIso (congrArg T.obj
      (finiteSkeletonLabel_detectorIndexOfFiniteSkeletonLabel
        (S := S) T j))

end MagnitudeConjecture.BoundQuiver.StringWord.DetectorIndex
