import MagnitudeConjecture.CategoryTheory.FiniteCategoryProjectiveGenerator
import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamPresentation

/-!
# Basic category algebra of a finite standard covering quotient
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.StandardCovering

open MagnitudeConjecture.CoveringHom

universe u

variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable {G : Type u} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- Finite-dimensional covariant representables on the strict deck-orbit
category, obtained by push-down from the locally bounded cover. -/
noncomputable abbrev orbitFiniteCovariantRepresentables
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ∀ Q : DeckOrbitSkeleton C G,
      IsFiniteDimensionalModule (C := DeckOrbitSkeleton C G) k
        (linearCoyonedaLinearModule (k := k) Q) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact D.orbitSkeletonLinearCoyonedaFinite (k := k) hP

/-- The finite category algebra of the strict deck-orbit category, in the
paper's right-module convention. -/
noncomputable abbrev orbitCategoryAlgebra
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) : Type u := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Finite (DeckOrbitSkeleton C G) := by
    change Finite (MulAction.orbitRel.Quotient G C)
    infer_instance
  letI : Fintype (DeckOrbitSkeleton C G) := Fintype.ofFinite _
  exact finiteCategoryProjectiveGenerator.algebra
    (orbitFiniteCovariantRepresentables (k := k) D hP)

end MagnitudeConjecture.StandardCovering
