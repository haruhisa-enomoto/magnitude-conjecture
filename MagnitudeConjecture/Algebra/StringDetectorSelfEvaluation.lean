import MagnitudeConjecture.Algebra.StringDetectorCoordinateTrace

/-!
# The distinguished coordinate on a matching string detector

Target-coordinate evaluation annihilates the matching detector denominator,
so it descends to a linear map from the detector quotient to the coefficient
field.  The endpoint basis class gives an explicit linear section.  Proving
that this descended coordinate is injective is exactly the remaining
one-dimensionality problem for diagonal detector evaluation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

variable {P : BoundQuiver.StringPresentation k A Q}
variable {S : P.toSpecialBiserialPresentation.ArrowPolarization}
variable {u₀ : Q} {t : Bool}

/-- Target-coordinate evaluation restricted to the matching detector
numerator. -/
def numeratorTargetCoordinate (C : EndpointWord S u₀ t) :
    detectorNumerator (C.word.rightModule P.monomial) C →ₗ[k] k where
  toFun x := (show C.word.Space u₀ from x.1) C.word.targetPosition
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem numeratorTargetCoordinate_apply (C : EndpointWord S u₀ t)
    (x : detectorNumerator (C.word.rightModule P.monomial) C) :
    C.numeratorTargetCoordinate x =
      (show C.word.Space u₀ from x.1) C.word.targetPosition :=
  rfl

/-- The numerator coordinate kills the denominator submodule. -/
theorem denominatorInNumerator_le_ker_numeratorTargetCoordinate
    (C : EndpointWord S u₀ t) :
    detectorDenominatorInNumerator (C.word.rightModule P.monomial) C ≤
      LinearMap.ker C.numeratorTargetCoordinate := by
  intro x hx
  change (show C.word.Space u₀ from x.1) C.word.targetPosition = 0
  exact C.detectorDenominator_apply_targetPosition_eq_zero_rightModule x.1 hx

/-- Target-coordinate evaluation descended to the matching detector
quotient. -/
def detectorTargetCoordinate (C : EndpointWord S u₀ t) :
    DetectorSpace (C.word.rightModule P.monomial) C →ₗ[k] k :=
  (detectorDenominatorInNumerator (C.word.rightModule P.monomial) C).liftQ
    C.numeratorTargetCoordinate
    C.denominatorInNumerator_le_ker_numeratorTargetCoordinate

@[simp]
theorem detectorTargetCoordinate_mk (C : EndpointWord S u₀ t)
    (x : detectorNumerator (C.word.rightModule P.monomial) C) :
    C.detectorTargetCoordinate (Submodule.Quotient.mk x) =
      C.numeratorTargetCoordinate x :=
  rfl

@[simp]
theorem detectorTargetCoordinate_targetDetectorClass
    (C : EndpointWord S u₀ t) :
    C.detectorTargetCoordinate C.targetDetectorClass = 1 := by
  rw [show C.targetDetectorClass =
    Submodule.Quotient.mk C.targetNumeratorElement from rfl]
  rw [C.detectorTargetCoordinate_mk]
  exact Finsupp.single_eq_same

/-- Scalar multiples of the distinguished endpoint class give a linear
section of the descended target coordinate. -/
def detectorTargetSection (C : EndpointWord S u₀ t) :
    k →ₗ[k] DetectorSpace (C.word.rightModule P.monomial) C where
  toFun c := c • C.targetDetectorClass
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := mul_smul _ _ _

@[simp]
theorem detectorTargetSection_apply (C : EndpointWord S u₀ t) (c : k) :
    C.detectorTargetSection c = c • C.targetDetectorClass :=
  rfl

/-- The descended target coordinate is a split epimorphism. -/
theorem detectorTargetCoordinate_comp_detectorTargetSection
    (C : EndpointWord S u₀ t) :
    C.detectorTargetCoordinate.comp C.detectorTargetSection = LinearMap.id := by
  apply LinearMap.ext
  intro c
  change C.detectorTargetCoordinate (c • C.targetDetectorClass) = c
  rw [map_smul, C.detectorTargetCoordinate_targetDetectorClass]
  simpa only [smul_eq_mul] using mul_one c

theorem detectorTargetCoordinate_surjective (C : EndpointWord S u₀ t) :
    Function.Surjective C.detectorTargetCoordinate := by
  intro c
  exact ⟨C.detectorTargetSection c, by simp⟩

/-- Exact residual form of diagonal one-dimensionality: the descended
coordinate is injective precisely when every numerator vector with zero
target coordinate already lies in the detector denominator. -/
theorem detectorTargetCoordinate_injective_iff
    (C : EndpointWord S u₀ t) :
    Function.Injective C.detectorTargetCoordinate ↔
      LinearMap.ker C.numeratorTargetCoordinate ≤
        detectorDenominatorInNumerator (C.word.rightModule P.monomial) C := by
  constructor
  · intro hinjective x hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply hinjective
    rw [map_zero]
    exact C.detectorTargetCoordinate_mk x |>.trans hx
  · intro hkernel
    apply LinearMap.ker_eq_bot.mp
    unfold detectorTargetCoordinate
    exact Submodule.ker_liftQ_eq_bot _ _ _ hkernel

/-- The reverse kernel inclusion is equivalent to a basis-position
statement: every non-target position basis vector which lies in the numerator
already lies in the denominator. -/
theorem ker_numeratorTargetCoordinate_le_denominator_iff_single
    (C : EndpointWord S u₀ t) :
    LinearMap.ker C.numeratorTargetCoordinate ≤
        detectorDenominatorInNumerator
          (C.word.rightModule P.monomial) C ↔
      ∀ i : C.word.PositionAt u₀,
        i ≠ C.word.targetPosition →
          Finsupp.single i (1 : k) ∈
              detectorNumerator (C.word.rightModule P.monomial) C →
            Finsupp.single i (1 : k) ∈
              detectorDenominator (C.word.rightModule P.monomial) C := by
  constructor
  · intro hkernel i hne hnum
    let x : detectorNumerator (C.word.rightModule P.monomial) C :=
      ⟨Finsupp.single i (1 : k), hnum⟩
    have hx : x ∈ LinearMap.ker C.numeratorTargetCoordinate := by
      change Finsupp.single i (1 : k) C.word.targetPosition = 0
      simp [hne]
    exact hkernel hx
  · intro hsingle x hx
    let v : C.word.Space u₀ := x.1
    let V : Submodule k (C.word.Space u₀) :=
      detectorNumerator (C.word.rightModule P.monomial) C
    let W : Submodule k (C.word.Space u₀) :=
      detectorDenominator (C.word.rightModule P.monomial) C
    change v ∈ W
    have hparts : ∀ i : C.word.PositionAt u₀,
        Finsupp.single i (v i) ∈ W := by
      intro i
      by_cases hitarget : i = C.word.targetPosition
      · subst i
        change v C.word.targetPosition = 0 at hx
        rw [hx]
        simpa only [Finsupp.single_zero] using W.zero_mem
      · by_cases hcoefficient : v i = 0
        · rw [hcoefficient]
          simpa only [Finsupp.single_zero] using W.zero_mem
        · have hpartNumerator : Finsupp.single i (v i) ∈ V :=
            C.detectorNumerator_isCoordinate_rightModule C.word x.1 x.2 i
          have honeNumerator : Finsupp.single i (1 : k) ∈ V := by
            have hscaled := V.smul_mem (v i)⁻¹ hpartNumerator
            have heq : (v i)⁻¹ • Finsupp.single i (v i) =
                Finsupp.single i (1 : k) := by
              rw [Finsupp.smul_single', inv_mul_cancel₀ hcoefficient]
            rw [← heq]
            exact hscaled
          have honeDenominator : Finsupp.single i (1 : k) ∈ W :=
            hsingle i hitarget honeNumerator
          have hscaled := W.smul_mem (v i) honeDenominator
          rw [← Finsupp.smul_single_one i (v i)]
          exact hscaled
    exact C.word.mem_of_all_coordinateParts_mem W v hparts

/-- Diagonal one-dimensionality is therefore exactly the absence of any
surviving non-target position basis vector in the matching detector. -/
theorem detectorTargetCoordinate_injective_iff_single
    (C : EndpointWord S u₀ t) :
    Function.Injective C.detectorTargetCoordinate ↔
      ∀ i : C.word.PositionAt u₀,
        i ≠ C.word.targetPosition →
          Finsupp.single i (1 : k) ∈
              detectorNumerator (C.word.rightModule P.monomial) C →
            Finsupp.single i (1 : k) ∈
              detectorDenominator (C.word.rightModule P.monomial) C := by
  rw [C.detectorTargetCoordinate_injective_iff,
    C.ker_numeratorTargetCoordinate_le_denominator_iff_single]

/-- Target-coordinate evaluation is injective on the matching detector.
Every hypothetical surviving non-target coordinate traces a complete copy of
the word through itself, whose endpoint rigidity forces that coordinate to be
the target after all. -/
theorem detectorTargetCoordinate_injective (C : EndpointWord S u₀ t) :
    Function.Injective C.detectorTargetCoordinate := by
  rw [C.detectorTargetCoordinate_injective_iff_single]
  intro i hne hnum
  change Finsupp.single i (1 : k) ∈
      upperSubspace (C.word.rightModule P.monomial) C.oppositeVertex ⊓
        upperSubspace (C.word.rightModule P.monomial) C at hnum
  have hoppositeUpper := hnum.1
  have hupper := hnum.2
  by_contra hnotDenominator
  have hnotLower : Finsupp.single i (1 : k) ∉
      lowerSubspace (C.word.rightModule P.monomial) C := by
    intro hlower
    apply hnotDenominator
    change Finsupp.single i (1 : k) ∈
      (upperSubspace (C.word.rightModule P.monomial) C.oppositeVertex ⊓
          lowerSubspace (C.word.rightModule P.monomial) C) ⊔
        (lowerSubspace (C.word.rightModule P.monomial) C.oppositeVertex ⊓
          upperSubspace (C.word.rightModule P.monomial) C)
    exact (le_sup_left :
      upperSubspace (C.word.rightModule P.monomial) C.oppositeVertex ⊓
          lowerSubspace (C.word.rightModule P.monomial) C ≤
        (upperSubspace (C.word.rightModule P.monomial) C.oppositeVertex ⊓
            lowerSubspace (C.word.rightModule P.monomial) C) ⊔
          (lowerSubspace (C.word.rightModule P.monomial) C.oppositeVertex ⊓
            upperSubspace (C.word.rightModule P.monomial) C))
      ⟨hoppositeUpper, hlower⟩
  rcases C.word.exists_positionReach_of_single_mem_signedPathSubspace_not_mem
      P.monomial C.path
      (C.upperBoundarySubspace_isCoordinate_rightModule C.word)
      i hupper hnotLower with ⟨j, hreach, _, _⟩
  exact hne (C.word.positionReach_self_eq_targetPosition hreach)

/-- The matching finite-string detector is canonically one-dimensional by
target-coordinate evaluation. -/
def detectorTargetEquiv (C : EndpointWord S u₀ t) :
    DetectorSpace (C.word.rightModule P.monomial) C ≃ₗ[k] k :=
  LinearEquiv.ofBijective C.detectorTargetCoordinate
    ⟨C.detectorTargetCoordinate_injective,
      C.detectorTargetCoordinate_surjective⟩

/-- Literal dimension statement for matching detector evaluation. -/
theorem finrank_detectorSpace_rightModule_self
    (C : EndpointWord S u₀ t) :
    Module.finrank k (DetectorSpace (C.word.rightModule P.monomial) C) = 1 := by
  rw [C.detectorTargetEquiv.finrank_eq, Module.finrank_self]

end MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord
