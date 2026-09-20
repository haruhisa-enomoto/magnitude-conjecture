import MagnitudeConjecture.Algebra.RightModuleCoordinateQuotient
import MagnitudeConjecture.Algebra.RightModuleGeneratedRelationsExt
import MagnitudeConjecture.Algebra.RightModuleDirectedScalarCorner
import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # The quotient used in generated-relations realization -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The canonical submodule-quotient sequence of finite right modules. -/
def quotientFGShortComplex (V : FinitelyGeneratedCategory A) (K : Submodule Aᵐᵒᵖ V) :
    ShortComplex (FinitelyGeneratedCategory A) :=
  ShortComplex.mk (FGModuleCat.ofHom K.subtype) (quotientFGMap V K) (by
    apply FGModuleCat.hom_ext
    ext x
    exact (Submodule.Quotient.mk_eq_zero K).2 x.property)

/-- The finite submodule-quotient sequence is short exact. -/
theorem quotientFGShortComplex_shortExact
    (V : FinitelyGeneratedCategory A) (K : Submodule Aᵐᵒᵖ V) :
    (quotientFGShortComplex V K).ShortExact := by
  apply ShortExact.reflects_shortExact_of_faithful
    (forget₂ (FGModuleCat.{u} Aᵐᵒᵖ) (ModuleCat.{u} Aᵐᵒᵖ))
  apply ModuleCat.shortComplex_shortExact
  · exact LinearMap.exact_subtype_mkQ K
  · exact K.subtype_injective
  · exact K.mkQ_surjective

namespace FiniteIndecomposableSkeleton
variable (S : FiniteIndecomposableSkeleton k A)

/-- Every map from a factor tau-projective to the generated-relations
quotient lifts to its presentation module. -/
theorem generatedRelationsQuotient_hom_lift
    [HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ)]
    {e : A} (D : PrimitiveIdempotentData e)
    (p : S.FactorProjectiveLabel (S.primitiveKilledLabels D))
    (V : FinitelyGeneratedCategory A)
    (R : Submodule k (idempotentCoordinate (k := k) e V))
    (f : S.fgObj p.1.1 ⟶ quotientFGObj V (generatedCoordinateRelations e V R)) :
    ∃ g : S.fgObj p.1.1 ⟶ V,
      g ≫ quotientFGMap V (generatedCoordinateRelations e V R) = f :=
  S.factorProjective_hom_lift_of_generated_kernel D p
    (quotientFGShortComplex_shortExact V _)
    (generatedCoordinateRelations_isGenerated D.idempotent V R) f

/-- The generated-relations quotient realizes a prescribed coordinate
surjection in the directed primitive setup. -/
def directedGeneratedRelations_coordinateEquivTarget [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (D : PrimitiveIdempotentData e)
    (V : FinitelyGeneratedCategory A)
    {W : Type u} [AddCommGroup W] [Module k W]
    (π : idempotentCoordinate (k := k) e V →ₗ[k] W) (hπ : Function.Surjective π) :=
  generatedRelations_coordinateEquivTarget D.idempotent
    (S.primitive_opposite_corner_scalar H D) V π hπ

end FiniteIndecomposableSkeleton
end MagnitudeConjecture.RightModule
