import MagnitudeConjecture.CategoryTheory.F1FiniteSupportLocalChange
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleOrbit
import MagnitudeConjecture.CategoryTheory.FiniteModuleLocalDensityEquivalence

/-!
# Shift equivariance for the F1 finite-support route

The frozen positive deletion-order argument reindexes finite support families
along deck translates.  This file records the elementary local-density part
of that reindexing: shifting an indecomposable module preserves its intrinsic
local density because the finite-dimensional module shift is an additive
equivalence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Intrinsic local density is invariant under a deck shift. -/
theorem finiteModuleLocalDensity_shift_eq
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (g : G) (M : FiniteDimensionalModuleCategory (C := C) k)
    (hM : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    finiteModuleLocalDensity hlocal
      ((shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
        (Additive.ofMul g)).obj M)
      ((MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
          (Additive.ofMul g)) M).2 hM) =
      finiteModuleLocalDensity hlocal M hM := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  let E := CategoryTheory.shiftEquiv
    (FiniteDimensionalModuleCategory (C := C) k) (Additive.ofMul g)
  letI : E.functor.Additive := by
    dsimp [E]
    exact D.finiteDimensionalModuleCategoryAdditiveShift
      (k := k) (Additive.ofMul g)
  exact finiteModuleLocalDensity_map_equivalence hlocal hlocal E M hM

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
