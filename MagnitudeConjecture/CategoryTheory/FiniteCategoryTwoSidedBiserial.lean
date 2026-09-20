import MagnitudeConjecture.CategoryTheory.FiniteCategoryPointwiseThinBiserial
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDuality
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraOpposite
import MagnitudeConjecture.Algebra.BiserialLeftIdealOpposite
import MagnitudeConjecture.Algebra.RightModulePrimitiveSpecialBiserial

/-! # Both sides of a finite category algebra from thin indecomposables -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CoveringHom
universe u
variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Fintype C]
local instance twoSidedBiserialOpFintype : Fintype Cᵒᵖ := Fintype.ofEquiv _ Opposite.equivToOpposite
variable (hC : ∀ X : C, IsFiniteDimensionalModule (C := C) k
  (linearCoyonedaLinearModule (k := k) X))
variable (hOp : ∀ X : Cᵒᵖ, IsFiniteDimensionalModule (C := Cᵒᵖ) k
  (linearCoyonedaLinearModule (k := k) X))

omit [Fintype C] in
/-- Coefficient duality gives thinness in the other variance. -/
theorem pointwiseThin_of_opposite_indecomposables_pointwiseThin
    (hthin : ∀ (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := Cᵒᵖ) k),
      Indecomposable M → IsPointwiseThin M.obj.obj)
    (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k)
    (hM : Indecomposable M) : IsPointwiseThin M.obj.obj := by
  apply (coefficientDualModule_isPointwiseThin_iff M).mp
  exact hthin ((finiteCoefficientDualFunctor (k := k) (C := C)).obj (Opposite.op M))
    ((finiteCoefficientDualFunctor_indec_iff M).mpr hM)

namespace finiteCategoryProjectiveGenerator
local instance twoSidedBiserialFinite : FiniteDimensional k (algebra hC) := algebra_finiteDimensional hC
local instance twoSidedBiserialOpFinite : FiniteDimensional k (algebra hOp) := algebra_finiteDimensional hOp
local instance twoSidedBiserialNoetherian : IsNoetherianRing (algebra hC)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
local instance twoSidedBiserialOpLeftNoetherian : IsNoetherianRing (algebra hOp) := IsNoetherianRing.of_finite k _
local instance twoSidedBiserialOpNoetherian : IsNoetherianRing (algebra hOp)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
local instance twoSidedBiserialOpOpNoetherian : IsNoetherianRing ((algebra hOp)ᵐᵒᵖ)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

include hC in
/-- Thinness in the opposite functor category makes canonical left ideals
biserial by coefficient duality and the opposite-algebra identification. -/
theorem canonicalLeftIdeal_isBiserialObject_of_opposite_pointwiseThin
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hthin : ∀ (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := Cᵒᵖ) k),
      Indecomposable M → IsPointwiseThin M.obj.obj)
    (X : Cᵒᵖ) :
    IsBiserialObject (RightModule.leftIdealFGObj (k := k) (canonicalProjector hOp X)) := by
  have hRep := finiteCovariantRepresentable_isBiserialObject_of_pointwiseThin hC hlocal
    (pointwiseThin_of_opposite_indecomposables_pointwiseThin hthin) X.unop
  have hRight := canonicalRightIdeal_isBiserialObject_of_covariantRepresentable hC X.unop hRep
  let f : algebra hC ≃ₐ[k] (algebra hOp)ᵐᵒᵖ := categoryAlgebraOppositeEquiv hC hOp
  have hMapped := (RightModule.rightIdealFGObj_isBiserialObject_mapAlgEquiv_iff
    f (canonicalProjector hC X.unop)).mpr hRight
  rw [categoryAlgebraOppositeEquiv_canonicalProjector] at hMapped
  apply (RightModule.leftIdealFGObj_isBiserialObject_iff_oppositeRightIdeal
    (k := k) (canonicalProjector hOp X)).mpr
  simpa using hMapped

include hC in
/-- The complete primitive-projective presentation is biserial on both sides
when all indecomposable opposite-category modules are thin. -/
theorem primitiveProjectivePresentation_isBiserial_of_opposite_pointwiseThin
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hlocalOp : ∀ X : Cᵒᵖ, IsLocalRing (End X))
    (hskel : Skeletal Cᵒᵖ)
    (hthin : ∀ (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := Cᵒᵖ) k),
      Indecomposable M → IsPointwiseThin M.obj.obj)
    (S : RightModule.FiniteIndecomposableSkeleton k (algebra hOp)) :
    (primitiveProjectivePresentation hOp hlocalOp S hskel).IsBiserial := by
  constructor
  · intro p
    exact canonicalRightIdeal_isBiserialObject_of_covariantRepresentable hOp _
      (finiteCovariantRepresentable_isBiserialObject_of_pointwiseThin hOp hlocalOp hthin _)
  · intro p
    exact canonicalLeftIdeal_isBiserialObject_of_opposite_pointwiseThin hC hOp hlocal hthin _

include hC in
/-- The resulting category algebra has a literal special-biserial presentation. -/
theorem admitsSpecialBiserialPresentation_of_opposite_pointwiseThin
    [IsAlgClosed k]
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hlocalOp : ∀ X : Cᵒᵖ, IsLocalRing (End X))
    (hskel : Skeletal Cᵒᵖ)
    (hthin : ∀ (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := Cᵒᵖ) k),
      Indecomposable M → IsPointwiseThin M.obj.obj)
    (S : RightModule.FiniteIndecomposableSkeleton k (algebra hOp)) :
    BoundQuiver.AdmitsSpecialBiserialPresentation k (algebra hOp) :=
  (primitiveProjectivePresentation hOp hlocalOp S hskel).ambient_admitsSpecialBiserialPresentation_of_isBiserial
      (primitiveProjectivePresentation_isBiserial_of_opposite_pointwiseThin
        hC hOp hlocal hlocalOp hskel hthin S)

end finiteCategoryProjectiveGenerator
end MagnitudeConjecture.CoveringHom
