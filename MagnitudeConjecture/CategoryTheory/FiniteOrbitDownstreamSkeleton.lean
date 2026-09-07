import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteType
import MagnitudeConjecture.CategoryTheory.FiniteOrbitARComponentExhaustion

/-!
# A finite indecomposable skeleton downstairs

Gabriel density and the finite pushed family give finitely many, possibly
repeated, representatives of all indecomposable modules over the finite
deck-orbit skeleton.  Deduplicating that family produces the literal finite
Krull--Schmidt skeleton needed to assemble downstream finite tau-category
data.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The finite deck-orbit module category has a duplicate-free complete
indecomposable skeleton under the manuscript's covering hypotheses. -/
noncomputable def finiteOrbitModuleIndecomposableSkeleton
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := DeckOrbitSkeleton C G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  letI : P.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful (k := k)
  let S := D.finitePushedIndecomposableFamily (k := k) hrep
  let hDensity :=
    D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
      (k := k) hP hI hlocal hfree hrep
  apply FiniteDimensionalModuleIndecomposableSkeleton.ofFamily
    (FinitePushedIndecomposableFamily.obj D S)
    S.downstairsIndecomposable
  intro Y hY
  obtain ⟨X, ⟨eY⟩⟩ := hDensity.essSurj.mem_essImage Y
  have hPX : Indecomposable (P.obj X) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eY).2 hY
  have hX : Indecomposable X :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P X hPX
  obtain ⟨i, ⟨eX⟩⟩ := S.covers X hX
  exact ⟨i, ⟨eY.symm ≪≫ eX.symm⟩⟩

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
