import MagnitudeConjecture.Algebra.CoordinateThinModule
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitivePresentation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleThin

/-!
# Pointwise thin category modules and primitive algebra coordinates

The projective-generator equivalence for a finite linear category identifies
the value of a category module at an object with the coordinate of the
corresponding right module at the canonical summand projector.  Consequently,
pointwise thinness of all indecomposable category modules is exactly the
coordinate-thin premise needed on the finite category algebra.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.CoveringHom

universe u

variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Fintype C]

namespace finiteCategoryProjectiveGenerator

variable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))

local instance thinAlgebraFiniteDimensional :
    FiniteDimensional k (algebra hP) :=
  algebra_finiteDimensional hP

local instance thinAlgebraOppositeIsNoetherian :
    IsNoetherianRing (algebra hP)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k (algebra hP)ᵐᵒᵖ

/-- If every indecomposable finite-dimensional category module is pointwise
thin, then every indecomposable finitely generated right module over the
finite category algebra is thin in all canonical primitive coordinates. -/
theorem algebra_coordinateThin_of_pointwiseThin
    (hthin : ∀
      (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k),
      Indecomposable M → CoveringHom.IsPointwiseThin M.obj.obj)
    (N : RightModule.FinitelyGeneratedCategory (algebra hP))
    (hN : Indecomposable N) :
    RightModule.IsCoordinateThin (k := k)
      (canonicalProjector hP) N := by
  let E := moduleEquivalence hP
  letI : E.functor.Additive := representedFGFunctor_additive hP
  letI : E.inverse.Additive := inferInstance
  let M := E.inverse.obj N
  have hM : Indecomposable M :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse N).2 hN
  have hMthin : CoveringHom.IsPointwiseThin M.obj.obj := hthin M hM
  intro X
  let eN : E.functor.obj M ≅ N := E.counitIso.app N
  calc
    Module.finrank k
          (RightModule.idempotentCoordinate
            (k := k) (canonicalProjector hP X) N) =
        Module.finrank k
          (RightModule.idempotentCoordinate
            (k := k) (canonicalProjector hP X) (E.functor.obj M)) :=
      (RightModule.idempotentCoordinateLinearEquivOfIso
        (k := k) ((canonicalProjector_complete hP).idem X) eN).finrank_eq.symm
    _ = Module.finrank k (M.obj.obj.obj X) :=
      (canonicalProjectorCoordinateLinearEquiv
        (k := k) hP X M).finrank_eq
    _ ≤ 1 := hMthin X

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
