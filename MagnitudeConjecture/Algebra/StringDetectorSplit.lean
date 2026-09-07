import MagnitudeConjecture.Algebra.StringDetectorPairWord
import MagnitudeConjecture.Algebra.StringReverse
import MagnitudeConjecture.LinearAlgebra.PairSubquotient

/-!
# Contextual detectors at every position of a string

The boundary conditions of a string detector belong to the two outer ends of
the complete string.  At an internal split, they are transported along the
prefix and the reversed suffix.  Keeping those outer boundary conditions
fixed makes passage across one displayed letter a pure image/preimage
calculation, even when the monomial relations have length greater than two.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization}

namespace Word

/-- A displayed cut of a word into a prefix and suffix. -/
structure Split (E : Word P.toPresentation.relations) where
  vertex : Q
  prefixPath : SignedPath E.source vertex
  suffixPath : SignedPath vertex E.target
  factor : E.path = prefixPath.comp suffixPath

namespace Split

/-- The cut at the target endpoint. -/
def target (E : Word P.toPresentation.relations) : E.Split where
  vertex := E.target
  prefixPath := E.path
  suffixPath := Quiver.Path.nil
  factor := by simp

/-- The cut represented by a word position. -/
def ofPosition (E : Word P.toPresentation.relations) (i : E.Position) :
    E.Split where
  vertex := i.1
  prefixPath := i.2.1
  suffixPath := i.2.suffix
  factor := i.2.prefix_comp_suffix

@[simp]
theorem target_vertex (E : Word P.toPresentation.relations) :
    (target E).vertex = E.target :=
  rfl

@[simp]
theorem target_prefix (E : Word P.toPresentation.relations) :
    (target E).prefixPath = E.path :=
  rfl

@[simp]
theorem target_suffix (E : Word P.toPresentation.relations) :
    (target E).suffixPath = Quiver.Path.nil :=
  rfl

/-- Two consecutive cuts separated by a positively traversed quiver arrow. -/
structure PositiveStep {E : Word P.toPresentation.relations}
    (c d : E.Split) where
  arrow : c.vertex ⟶ d.vertex
  prefix_eq : d.prefixPath =
    c.prefixPath.comp (positiveArrow arrow).toPath
  suffix_eq : c.suffixPath =
    (positiveArrow arrow).toPath.comp d.suffixPath

/-- Two consecutive cuts separated by a formally inverse quiver arrow. -/
structure NegativeStep {E : Word P.toPresentation.relations}
    (c d : E.Split) where
  arrow : d.vertex ⟶ c.vertex
  prefix_eq : d.prefixPath =
    c.prefixPath.comp (negativeArrow arrow).toPath
  suffix_eq : c.suffixPath =
    (negativeArrow arrow).toPath.comp d.suffixPath

end Split

end Word

namespace EndpointWord

variable {E : Word P.toPresentation.relations}

/-- The endpoint detector word belonging to a literal word. -/
abbrev detectorEndpoint (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) :=
  EndpointWord.ofWord S E

/-- Lower filtration subspace arriving from the source end of `E`. -/
def splitRightLower
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations c.vertex))) :=
  signedPathSubspace N c.prefixPath
    (lowerBoundarySubspace N (detectorEndpoint S E).sourceVertex)

/-- Upper filtration subspace arriving from the source end of `E`. -/
def splitRightUpper
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations c.vertex))) :=
  signedPathSubspace N c.prefixPath
    (upperBoundarySubspace N (detectorEndpoint S E).sourceVertex)

/-- Lower filtration subspace arriving backwards from the target end of
`E`. -/
def splitLeftLower
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations c.vertex))) :=
  signedPathSubspace N c.suffixPath.reverse
    (lowerBoundarySubspace N (detectorEndpoint S E).oppositeVertex)

/-- Upper filtration subspace arriving backwards from the target end of
`E`. -/
def splitLeftUpper
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations c.vertex))) :=
  signedPathSubspace N c.suffixPath.reverse
    (upperBoundarySubspace N (detectorEndpoint S E).oppositeVertex)

/-- Numerator of the contextual detector at `c`. -/
def splitDetectorNumerator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations c.vertex))) :=
  splitLeftUpper N S E c ⊓ splitRightUpper N S E c

/-- Denominator of the contextual detector at `c`. -/
def splitDetectorDenominator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations c.vertex))) :=
  (splitLeftUpper N S E c ⊓ splitRightLower N S E c) ⊔
    (splitLeftLower N S E c ⊓ splitRightUpper N S E c)

theorem splitRightLower_le_splitRightUpper
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    splitRightLower N S E c ≤ splitRightUpper N S E c := by
  exact signedPathSubspace_mono N c.prefixPath
    (lowerBoundarySubspace_le_upperBoundarySubspace N
      (detectorEndpoint S E).sourceVertex)

theorem splitLeftLower_le_splitLeftUpper
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    splitLeftLower N S E c ≤ splitLeftUpper N S E c := by
  exact signedPathSubspace_mono N c.suffixPath.reverse
    (lowerBoundarySubspace_le_upperBoundarySubspace N
      (detectorEndpoint S E).oppositeVertex)

theorem splitRightLower_positiveStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.PositiveStep d) :
    splitRightLower N S E d =
      (splitRightLower N S E c).map
        (moduleArrowMap N step.arrow).hom := by
  rw [splitRightLower, splitRightLower, step.prefix_eq,
    signedPathSubspace_comp]
  simp

theorem splitRightUpper_positiveStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.PositiveStep d) :
    splitRightUpper N S E d =
      (splitRightUpper N S E c).map
        (moduleArrowMap N step.arrow).hom := by
  rw [splitRightUpper, splitRightUpper, step.prefix_eq,
    signedPathSubspace_comp]
  simp

theorem splitLeftLower_positiveStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.PositiveStep d) :
    splitLeftLower N S E c =
      (splitLeftLower N S E d).comap
        (moduleArrowMap N step.arrow).hom := by
  rw [splitLeftLower, splitLeftLower, step.suffix_eq,
    Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    signedPathSubspace_comp]
  change signedPathSubspace N (negativeArrow step.arrow).toPath _ = _
  rw [signedPathSubspace_toPath]
  rfl

theorem splitLeftUpper_positiveStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.PositiveStep d) :
    splitLeftUpper N S E c =
      (splitLeftUpper N S E d).comap
        (moduleArrowMap N step.arrow).hom := by
  rw [splitLeftUpper, splitLeftUpper, step.suffix_eq,
    Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    signedPathSubspace_comp]
  change signedPathSubspace N (negativeArrow step.arrow).toPath _ = _
  rw [signedPathSubspace_toPath]
  rfl

theorem splitRightLower_negativeStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.NegativeStep d) :
    splitRightLower N S E d =
      (splitRightLower N S E c).comap
        (moduleArrowMap N step.arrow).hom := by
  rw [splitRightLower, splitRightLower, step.prefix_eq,
    signedPathSubspace_comp]
  simp

theorem splitRightUpper_negativeStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.NegativeStep d) :
    splitRightUpper N S E d =
      (splitRightUpper N S E c).comap
        (moduleArrowMap N step.arrow).hom := by
  rw [splitRightUpper, splitRightUpper, step.prefix_eq,
    signedPathSubspace_comp]
  simp

theorem splitLeftLower_negativeStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.NegativeStep d) :
    splitLeftLower N S E c =
      (splitLeftLower N S E d).map
        (moduleArrowMap N step.arrow).hom := by
  rw [splitLeftLower, splitLeftLower, step.suffix_eq,
    Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    signedPathSubspace_comp]
  change signedPathSubspace N (positiveArrow step.arrow).toPath _ = _
  rw [signedPathSubspace_toPath]
  rfl

theorem splitLeftUpper_negativeStep
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.NegativeStep d) :
    splitLeftUpper N S E c =
      (splitLeftUpper N S E d).map
        (moduleArrowMap N step.arrow).hom := by
  rw [splitLeftUpper, splitLeftUpper, step.suffix_eq,
    Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
    signedPathSubspace_comp]
  change signedPathSubspace N (positiveArrow step.arrow).toPath _ = _
  rw [signedPathSubspace_toPath]
  rfl

theorem splitDetectorDenominator_le_splitDetectorNumerator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    splitDetectorDenominator N S E c ≤
      splitDetectorNumerator N S E c := by
  apply sup_le
  · exact inf_le_inf le_rfl
      (splitRightLower_le_splitRightUpper N S E c)
  · exact inf_le_inf (splitLeftLower_le_splitLeftUpper N S E c) le_rfl

/-- Contextual denominator inside its numerator. -/
def splitDetectorDenominatorInNumerator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :
    Submodule k (splitDetectorNumerator N S E c) :=
  (splitDetectorDenominator N S E c).comap
    (splitDetectorNumerator N S E c).subtype

/-- Contextual detector space at a displayed split. -/
abbrev SplitDetectorSpace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (c : E.Split) :=
  splitDetectorNumerator N S E c ⧸
    splitDetectorDenominatorInNumerator N S E c

/-- Contextual detector spaces at consecutive positive positions are
canonically linearly equivalent. -/
def splitDetectorSpacePositiveStepEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.PositiveStep d) :
    SplitDetectorSpace N S E c ≃ₗ[k] SplitDetectorSpace N S E d := by
  let f := (moduleArrowMap N step.arrow).hom
  let sourceNum :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedSourceNumerator
      f (splitRightUpper N S E c) (splitLeftUpper N S E d)
  let sourceDen :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedSourceDenominator
      f (splitRightLower N S E c) (splitRightUpper N S E c)
        (splitLeftLower N S E d) (splitLeftUpper N S E d)
  let targetNum :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedTargetNumerator
      f (splitRightUpper N S E c) (splitLeftUpper N S E d)
  let targetDen :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedTargetDenominator
      f (splitRightLower N S E c) (splitRightUpper N S E c)
        (splitLeftLower N S E d) (splitLeftUpper N S E d)
  have hSourceNum : splitDetectorNumerator N S E c = sourceNum := by
    simp [splitDetectorNumerator, sourceNum,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedSourceNumerator,
      f, splitLeftUpper_positiveStep N S E step]
  have hSourceDen : splitDetectorDenominator N S E c = sourceDen := by
    simp [splitDetectorDenominator, sourceDen,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedSourceDenominator,
      f, splitLeftUpper_positiveStep N S E step,
      splitLeftLower_positiveStep N S E step]
  have hTargetNum : targetNum = splitDetectorNumerator N S E d := by
    simp [splitDetectorNumerator, targetNum,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedTargetNumerator,
      f, splitRightUpper_positiveStep N S E step]
  have hTargetDen : targetDen = splitDetectorDenominator N S E d := by
    simp [splitDetectorDenominator, targetDen,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedTargetDenominator,
      f, splitRightUpper_positiveStep N S E step,
      splitRightLower_positiveStep N S E step]
  change
    (splitDetectorNumerator N S E c ⧸
        (splitDetectorDenominator N S E c).comap
          (splitDetectorNumerator N S E c).subtype) ≃ₗ[k]
      (splitDetectorNumerator N S E d ⧸
        (splitDetectorDenominator N S E d).comap
          (splitDetectorNumerator N S E d).subtype)
  exact
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivSwappedIdentified
      f (splitRightLower N S E c) (splitRightUpper N S E c)
      (splitLeftLower N S E d) (splitLeftUpper N S E d)
      (splitDetectorNumerator N S E c) (splitDetectorDenominator N S E c)
      (splitDetectorNumerator N S E d) (splitDetectorDenominator N S E d)
      hSourceNum hSourceDen hTargetNum hTargetDen
      (splitRightLower_le_splitRightUpper N S E c)
      (splitLeftLower_le_splitLeftUpper N S E d)

/-- Contextual detector spaces at consecutive negative positions are
canonically linearly equivalent. -/
def splitDetectorSpaceNegativeStepEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.NegativeStep d) :
    SplitDetectorSpace N S E c ≃ₗ[k] SplitDetectorSpace N S E d := by
  let f := (moduleArrowMap N step.arrow).hom
  let sourceNum :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.sourceNumerator
      f (splitLeftUpper N S E d) (splitRightUpper N S E c)
  let sourceDen :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.sourceDenominator
      f (splitLeftLower N S E d) (splitLeftUpper N S E d)
        (splitRightLower N S E c) (splitRightUpper N S E c)
  let targetNum :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.targetNumerator
      f (splitLeftUpper N S E d) (splitRightUpper N S E c)
  let targetDen :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.targetDenominator
      f (splitLeftLower N S E d) (splitLeftUpper N S E d)
        (splitRightLower N S E c) (splitRightUpper N S E c)
  have hSourceNum : splitDetectorNumerator N S E c = targetNum := by
    simp [splitDetectorNumerator, targetNum,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.targetNumerator,
      f, splitLeftUpper_negativeStep N S E step]
  have hSourceDen : splitDetectorDenominator N S E c = targetDen := by
    simp [splitDetectorDenominator, targetDen,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.targetDenominator,
      f, splitLeftUpper_negativeStep N S E step,
      splitLeftLower_negativeStep N S E step]
  have hTargetNum : sourceNum = splitDetectorNumerator N S E d := by
    simp [splitDetectorNumerator, sourceNum,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.sourceNumerator,
      f, splitRightUpper_negativeStep N S E step]
  have hTargetDen : sourceDen = splitDetectorDenominator N S E d := by
    simp [splitDetectorDenominator, sourceDen,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.sourceDenominator,
      f, splitRightUpper_negativeStep N S E step,
      splitRightLower_negativeStep N S E step]
  change
    (splitDetectorNumerator N S E c ⧸
        (splitDetectorDenominator N S E c).comap
          (splitDetectorNumerator N S E c).subtype) ≃ₗ[k]
      (splitDetectorNumerator N S E d ⧸
        (splitDetectorDenominator N S E d).comap
          (splitDetectorNumerator N S E d).subtype)
  exact
    (MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivIdentified
      f (splitLeftLower N S E d) (splitLeftUpper N S E d)
      (splitRightLower N S E c) (splitRightUpper N S E c)
      (splitDetectorNumerator N S E d) (splitDetectorDenominator N S E d)
      (splitDetectorNumerator N S E c) (splitDetectorDenominator N S E c)
      hTargetNum.symm hTargetDen.symm hSourceNum.symm hSourceDen.symm
      (splitLeftLower_le_splitLeftUpper N S E d)
      (splitRightLower_le_splitRightUpper N S E c)).symm

@[simp]
theorem splitDetectorSpacePositiveStepEquiv_mk
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.PositiveStep d)
    (x : splitDetectorNumerator N S E c) :
    splitDetectorSpacePositiveStepEquiv N S E step
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨moduleArrowMap N step.arrow x.1, by
          constructor
          · have hx := x.2.1
            rw [splitLeftUpper_positiveStep N S E step] at hx
            exact hx
          · rw [splitRightUpper_positiveStep N S E step]
            exact ⟨x, x.2.2, rfl⟩⟩ :
          splitDetectorNumerator N S E d) := by
  let f := (moduleArrowMap N step.arrow).hom
  let sourceNum :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedSourceNumerator
      f (splitRightUpper N S E c) (splitLeftUpper N S E d)
  let sourceDen :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedSourceDenominator
      f (splitRightLower N S E c) (splitRightUpper N S E c)
        (splitLeftLower N S E d) (splitLeftUpper N S E d)
  let targetNum :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedTargetNumerator
      f (splitRightUpper N S E c) (splitLeftUpper N S E d)
  let targetDen :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedTargetDenominator
      f (splitRightLower N S E c) (splitRightUpper N S E c)
        (splitLeftLower N S E d) (splitLeftUpper N S E d)
  have hSourceNum : splitDetectorNumerator N S E c = sourceNum := by
    simp [splitDetectorNumerator, sourceNum,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedSourceNumerator,
      f, splitLeftUpper_positiveStep N S E step]
  have hSourceDen : splitDetectorDenominator N S E c = sourceDen := by
    simp [splitDetectorDenominator, sourceDen,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedSourceDenominator,
      f, splitLeftUpper_positiveStep N S E step,
      splitLeftLower_positiveStep N S E step]
  have hTargetNum : targetNum = splitDetectorNumerator N S E d := by
    simp [splitDetectorNumerator, targetNum,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedTargetNumerator,
      f, splitRightUpper_positiveStep N S E step]
  have hTargetDen : targetDen = splitDetectorDenominator N S E d := by
    simp [splitDetectorDenominator, targetDen,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.swappedTargetDenominator,
      f, splitRightUpper_positiveStep N S E step,
      splitRightLower_positiveStep N S E step]
  change
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivSwappedIdentified
        f (splitRightLower N S E c) (splitRightUpper N S E c)
        (splitLeftLower N S E d) (splitLeftUpper N S E d)
        (splitDetectorNumerator N S E c) (splitDetectorDenominator N S E c)
        (splitDetectorNumerator N S E d) (splitDetectorDenominator N S E d)
        hSourceNum hSourceDen hTargetNum hTargetDen
        (splitRightLower_le_splitRightUpper N S E c)
        (splitLeftLower_le_splitLeftUpper N S E d)
        (Submodule.Quotient.mk x) = _
  rw [MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivSwappedIdentified_apply_mk]
  rfl

@[simp]
theorem splitDetectorSpaceNegativeStepEquiv_symm_mk
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.NegativeStep d)
    (x : splitDetectorNumerator N S E d) :
    (splitDetectorSpaceNegativeStepEquiv N S E step).symm
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨moduleArrowMap N step.arrow x.1, by
          constructor
          · rw [splitLeftUpper_negativeStep N S E step]
            exact ⟨x, x.2.1, rfl⟩
          · have hx := x.2.2
            rw [splitRightUpper_negativeStep N S E step] at hx
            exact hx⟩ : splitDetectorNumerator N S E c) := by
  let f := (moduleArrowMap N step.arrow).hom
  let sourceNum :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.sourceNumerator
      f (splitLeftUpper N S E d) (splitRightUpper N S E c)
  let sourceDen :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.sourceDenominator
      f (splitLeftLower N S E d) (splitLeftUpper N S E d)
        (splitRightLower N S E c) (splitRightUpper N S E c)
  let targetNum :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.targetNumerator
      f (splitLeftUpper N S E d) (splitRightUpper N S E c)
  let targetDen :=
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.targetDenominator
      f (splitLeftLower N S E d) (splitLeftUpper N S E d)
        (splitRightLower N S E c) (splitRightUpper N S E c)
  have hSourceNum : splitDetectorNumerator N S E c = targetNum := by
    simp [splitDetectorNumerator, targetNum,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.targetNumerator,
      f, splitLeftUpper_negativeStep N S E step]
  have hSourceDen : splitDetectorDenominator N S E c = targetDen := by
    simp [splitDetectorDenominator, targetDen,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.targetDenominator,
      f, splitLeftUpper_negativeStep N S E step,
      splitLeftLower_negativeStep N S E step]
  have hTargetNum : sourceNum = splitDetectorNumerator N S E d := by
    simp [splitDetectorNumerator, sourceNum,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.sourceNumerator,
      f, splitRightUpper_negativeStep N S E step]
  have hTargetDen : sourceDen = splitDetectorDenominator N S E d := by
    simp [splitDetectorDenominator, sourceDen,
      MagnitudeConjecture.LinearAlgebra.PairSubquotient.sourceDenominator,
      f, splitRightUpper_negativeStep N S E step,
      splitRightLower_negativeStep N S E step]
  change
    MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivIdentified
        f (splitLeftLower N S E d) (splitLeftUpper N S E d)
        (splitRightLower N S E c) (splitRightUpper N S E c)
        (splitDetectorNumerator N S E d) (splitDetectorDenominator N S E d)
        (splitDetectorNumerator N S E c) (splitDetectorDenominator N S E c)
        hTargetNum.symm hTargetDen.symm hSourceNum.symm hSourceDen.symm
        (splitLeftLower_le_splitLeftUpper N S E d)
        (splitRightLower_le_splitRightUpper N S E c)
        (Submodule.Quotient.mk x) = _
  rw [MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivIdentified_apply_mk]
  rfl

@[simp]
theorem splitRightLower_target
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations) :
    splitRightLower N S E (.target E) =
      lowerSubspace N (detectorEndpoint S E) := by
  exact (lowerSubspace_eq_sourceVertexBoundaryTransport
    N (detectorEndpoint S E)).symm

@[simp]
theorem splitRightUpper_target
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations) :
    splitRightUpper N S E (.target E) =
      upperSubspace N (detectorEndpoint S E) := by
  exact (upperSubspace_eq_sourceVertexBoundaryTransport
    N (detectorEndpoint S E)).symm

@[simp]
theorem splitLeftLower_target
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations) :
    splitLeftLower N S E (.target E) =
      lowerSubspace N (detectorEndpoint S E).oppositeVertex := by
  change signedPathSubspace N Quiver.Path.nil.reverse _ =
    signedPathSubspace N Quiver.Path.nil _
  simp

@[simp]
theorem splitLeftUpper_target
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations) :
    splitLeftUpper N S E (.target E) =
      upperSubspace N (detectorEndpoint S E).oppositeVertex := by
  change signedPathSubspace N Quiver.Path.nil.reverse _ =
    signedPathSubspace N Quiver.Path.nil _
  simp

@[simp]
theorem splitDetectorNumerator_target
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations) :
    splitDetectorNumerator N S E (.target E) =
      detectorNumerator N (detectorEndpoint S E) := by
  simp only [splitDetectorNumerator, detectorNumerator,
    splitLeftUpper_target, splitRightUpper_target]
  rfl

@[simp]
theorem splitDetectorDenominator_target
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations) :
    splitDetectorDenominator N S E (.target E) =
      detectorDenominator N (detectorEndpoint S E) := by
  simp only [splitDetectorDenominator, detectorDenominator,
    splitLeftUpper_target, splitRightLower_target,
    splitLeftLower_target, splitRightUpper_target]
  rfl

/-- At the target cut, the contextual detector is the campaign's canonical
endpoint detector. -/
def splitDetectorSpaceTargetEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations) :
    SplitDetectorSpace N S E (.target E) ≃ₗ[k]
      DetectorSpace N (detectorEndpoint S E) := by
  exact MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivOfEq
    (splitDetectorNumerator N S E (.target E))
    (detectorNumerator N (detectorEndpoint S E))
    (splitDetectorDenominator N S E (.target E))
    (detectorDenominator N (detectorEndpoint S E))
    (splitDetectorNumerator_target N S E)
    (splitDetectorDenominator_target N S E)

@[simp]
theorem splitDetectorSpaceTargetEquiv_mk
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    (x : splitDetectorNumerator N S E (.target E)) :
    splitDetectorSpaceTargetEquiv N S E (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨x.1, by
          rw [← splitDetectorNumerator_target N S E]
          exact x.2⟩ : detectorNumerator N (detectorEndpoint S E)) := by
  exact MagnitudeConjecture.LinearAlgebra.PairSubquotient.quotientEquivOfEq_apply_mk
    _ _ _ _ _ _ x

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
