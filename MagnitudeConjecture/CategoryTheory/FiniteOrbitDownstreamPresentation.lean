import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownMinimalPresentation

/-!
# Literal finite-representable presentations on the deck-orbit skeleton

The orbit-skeleton representables and dual corepresentables are finite at
every downstairs object.  The recoordinated pushed minimal presentation can
therefore be packaged in the generic finite-representable interface used by
the presentation-dependent Auslander--Reiten formula.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Finiteness of every covariant representable on the deck-orbit skeleton,
obtained from any upstairs representative of its strict orbit. -/
theorem orbitSkeletonLinearCoyonedaFinite
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ∀ X : DeckOrbitSkeleton C G,
      IsFiniteDimensionalModule (C := DeckOrbitSkeleton C G) k
        (linearCoyonedaLinearModule (k := k) X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  intro q
  induction q using Quotient.inductionOn with
  | _ X =>
      exact (D.orbitSkeletonFiniteDimensionalLinearCoyoneda
        (k := k) X (hP X)).property

/-- Finiteness of every dual corepresentable on the deck-orbit skeleton,
obtained from any upstairs representative of its strict orbit. -/
theorem orbitSkeletonDualLinearYonedaFinite
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ∀ X : DeckOrbitSkeleton C G,
      IsFiniteDimensionalModule (C := DeckOrbitSkeleton C G) k
        (dualLinearYonedaLinearModule (k := k) X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  intro q
  induction q using Quotient.inductionOn with
  | _ X =>
      exact (D.orbitSkeletonFiniteDimensionalDualLinearYoneda
        (k := k) X (hI X)).property

set_option backward.isDefEq.respectTransparency false in
/-- The literal downstream minimal projective presentation, packaged with
finite-representable coordinates indexed by the mapped upstairs vertices. -/
noncomputable def orbitSkeletonTwoStepMinimalFiniteRepresentablePresentation
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    TwoStepMinimalFiniteRepresentablePresentation
      (D.orbitSkeletonLinearCoyonedaFinite (k := k) hP)
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let S := D.orbitSkeletonTwoStepMinimalProjectivePresentation
    (k := k) hP hlocal hfree Q
  let P₀ : MinimalFiniteRepresentablePresentation hP'
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) :=
    { n := Q.augmentation.n
      X := fun i ↦ D.orbitSkeletonFunctor.obj (Q.augmentation.X i)
      f := S.augmentation.f
      rightMinimal := S.augmentation.rightMinimal }
  let P₁ : MinimalFiniteRepresentablePresentation hP' (kernel P₀.f) :=
    { n := Q.syzygyPresentation.n
      X := fun i ↦ D.orbitSkeletonFunctor.obj (Q.syzygyPresentation.X i)
      f := S.syzygyPresentation.f
      rightMinimal := S.syzygyPresentation.rightMinimal }
  exact { augmentation := P₀, syzygyPresentation := P₁ }

set_option backward.isDefEq.respectTransparency false in
/-- The representing differential of the downstream finite-representable
presentation is the upstairs representing matrix mapped to the orbit
skeleton. -/
theorem orbitSkeletonTwoStepMinimalFiniteRepresentablePresentation_representingDifferential
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.orbitSkeletonTwoStepMinimalFiniteRepresentablePresentation
        (k := k) hP hlocal hfree Q).toTwoStepFiniteRepresentablePresentation.matrixDifferential =
      (D.orbitSkeletonFunctor.op.mapMat_).map
        Q.toTwoStepFiniteRepresentablePresentation.matrixDifferential := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let R := D.orbitSkeletonTwoStepMinimalFiniteRepresentablePresentation
    (k := k) hP hlocal hfree Q
  apply (finiteProjectiveRepresentableSumFunctor (k := k) hP').map_injective
  rw [R.toTwoStepFiniteRepresentablePresentation.map_matrixDifferential]
  change
    (D.orbitSkeletonTwoStepMinimalProjectivePresentation
      (k := k) hP hlocal hfree Q).differential =
        (D.orbitSkeletonFiniteProjectiveRepresentableSumFunctor
          (k := k) hP).map
            Q.toTwoStepFiniteRepresentablePresentation.matrixDifferential
  exact D.orbitSkeletonTwoStepMinimalProjectivePresentation_differential
    (k := k) hP hlocal hfree Q

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
