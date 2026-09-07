import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraThin
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitiveQuotientSurplusReindex

/-!
# Coordinate thinness after finite-object reindexing

An arbitrary finite object type is replaced by its small `Fin` model before
forming the category algebra.  This file transports pointwise thinness to the
small model and then applies the canonical-projector coordinate theorem.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Fintype C]

namespace finiteCategoryProjectiveGenerator

noncomputable local instance finiteObjectModelThinFGHasFiniteBiproducts
    {R : Type v} [Ring R] [IsNoetherianRing R] :
    HasFiniteBiproducts (FGModuleCat.{v} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))

local instance finiteObjectModelThinAlgebraFiniteDimensional :
    FiniteDimensional k
      (algebra (finiteObjectModel_finiteCovariantRepresentables
        (k := k) (C := C) hP)) :=
  algebra_finiteDimensional
    (finiteObjectModel_finiteCovariantRepresentables
      (k := k) (C := C) hP)

local instance finiteObjectModelThinAlgebraOppositeIsNoetherian :
    IsNoetherianRing
      (algebra (finiteObjectModel_finiteCovariantRepresentables
        (k := k) (C := C) hP))ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

noncomputable local instance
    finiteObjectModelThinRightModuleHasFiniteBiproducts :
    HasFiniteBiproducts
      (RightModule.FinitelyGeneratedCategory
        (algebra (finiteObjectModel_finiteCovariantRepresentables
          (k := k) (C := C) hP))) := by
  letI : IsNoetherianRing
      (algebra (finiteObjectModel_finiteCovariantRepresentables
        (k := k) (C := C) hP))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Pointwise thinness of all indecomposable modules on a finite linear
category makes every indecomposable right module over the category algebra of
its small object model thin in every canonical primitive coordinate. -/
theorem finiteObjectModelAlgebra_coordinateThin_of_pointwiseThin
    (hthin : ∀
      (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
      Indecomposable M → IsPointwiseThin M.obj.obj)
    (N : RightModule.FinitelyGeneratedCategory
      (algebra (finiteObjectModel_finiteCovariantRepresentables
        (k := k) (C := C) hP)))
    [HasBinaryBiproducts
      (RightModule.FinitelyGeneratedCategory
        (algebra (finiteObjectModel_finiteCovariantRepresentables
          (k := k) (C := C) hP)))]
    (hN : Indecomposable N) :
    RightModule.IsCoordinateThin (k := k)
      (canonicalProjector
        (finiteObjectModel_finiteCovariantRepresentables
          (k := k) (C := C) hP)) N := by
  let C₀ := FiniteObjectModel (C := C)
  let E₀ := finiteObjectModelEquivalence (C := C)
  let E := finiteObjectModelModuleEquivalence (k := k) (C := C)
  let hP₀ := finiteObjectModel_finiteCovariantRepresentables
    (k := k) (C := C) hP
  have hthin₀ : ∀
      (M : FiniteDimensionalModuleCategory.{0, v, v, v} (C := C₀) k),
      Indecomposable M → IsPointwiseThin M.obj.obj := by
    intro M hM
    letI : E.functor.Additive := inferInstance
    letI : E.inverse.Additive := inferInstance
    let L := E.inverse.obj M
    have hL : Indecomposable L :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.inverse M).2 hM
    have hthinL : IsPointwiseThin L.obj.obj := hthin L hL
    let eM : E.functor.obj L ≅ M := E.counitIso.app M
    intro X
    let eMX : (E.functor.obj L).obj.obj.obj X ≅ M.obj.obj.obj X :=
      ((IsLinearModule.{0, v, v, v} (C := C₀) k).ι.mapIso
        ((IsFiniteDimensionalModule (C := C₀) k).ι.mapIso eM)).app X
    rw [← LinearEquiv.finrank_eq eMX.toLinearEquiv]
    exact hthinL (E₀.functor.obj X)
  exact algebra_coordinateThin_of_pointwiseThin hP₀ hthin₀ N hN

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
