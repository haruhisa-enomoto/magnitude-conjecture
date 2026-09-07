import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraBiserial
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraThinReindex

/-!
# Biserial representables from pointwise thinness

This file packages the variance-neutral finite-category step in the frozen
manuscript.  Pointwise thinness of every indecomposable finite module is
transported to canonical idempotent-coordinate thinness for a small category
algebra; the direct biserial induction then applies to each representable.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u

variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Fintype C]

/-- On a finite linear category with local endomorphism rings, pointwise
thinness of all indecomposable finite modules makes every covariant
representable intrinsically biserial. -/
theorem finiteCovariantRepresentable_isBiserialObject_of_pointwiseThin
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hthin : ∀
      (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k),
      Indecomposable M → IsPointwiseThin M.obj.obj)
    (X : C) :
    IsBiserialObject
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op X)) := by
  let C₀ := FiniteObjectModel (C := C)
  let e := finiteObjectModelEquivalence (C := C)
  let hP₀ := finiteObjectModel_finiteCovariantRepresentables hP
  letI : FiniteDimensional k
      (finiteCategoryProjectiveGenerator.algebra hP₀) :=
    finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP₀
  letI : IsNoetherianRing
      (finiteCategoryProjectiveGenerator.algebra hP₀)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : HasBinaryBiproducts
      (RightModule.FinitelyGeneratedCategory
        (finiteCategoryProjectiveGenerator.algebra hP₀)) := by
    infer_instance
  have hcoordinate : RightModule.AllIndecomposablesCoordinateThin (k := k)
      (finiteCategoryProjectiveGenerator.canonicalProjector hP₀) := by
    intro N hN
    exact
      finiteCategoryProjectiveGenerator.finiteObjectModelAlgebra_coordinateThin_of_pointwiseThin
        hP hthin N hN
  let hlocal₀ : ∀ Y : C₀, IsLocalRing (End Y) :=
    finiteObjectModel_localEndomorphismRings hlocal
  let X₀ : C₀ := (finiteObjectEquiv (C := C)).symm X
  have hsmall : IsBiserialObject
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP₀).obj
        (Opposite.op X₀)) :=
    finiteCategoryProjectiveGenerator.covariantRepresentable_isBiserialObject_of_allIndecomposablesCoordinateThin
      hP₀ hlocal₀ hcoordinate X₀
  have hobj : Function.Bijective e.functor.obj := by
    change Function.Bijective (finiteObjectEquiv (C := C))
    exact (finiteObjectEquiv (C := C)).bijective
  have horiginal : IsBiserialObject
      ((finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
        (Opposite.op (e.functor.obj X₀))) :=
    (finiteDimensionalLinearCoyoneda_isBiserialObject_iff_of_equivalence
      hP₀ hP e hobj X₀).mpr hsmall
  have hX : e.functor.obj X₀ = X := by
    change finiteObjectEquiv (C := C)
      ((finiteObjectEquiv (C := C)).symm X) = X
    exact (finiteObjectEquiv (C := C)).apply_symm_apply X
  simpa only [hX] using horiginal

end MagnitudeConjecture.CoveringHom
