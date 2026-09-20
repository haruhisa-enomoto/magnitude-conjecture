import MagnitudeConjecture.Algebra.RightModuleStandardSeparatedIntervals
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSkeletonDirected
import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalModuleEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraInvariants

/-! # Intrinsic category surplus for the actual standard-form intervals -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance intervalCategoryBaseFinite :
    FiniteDimensional k (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
local instance intervalCategoryAlgebraFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) := S.standardFormIntervalAlgebra_finiteDimensional m
local instance intervalCategoryAlgebraNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
local instance intervalCategoryFintype (m : ℕ) :
    Fintype (S.standardFormIntervalPrincipalCategory m) :=
  inferInstanceAs (Fintype (S.StandardFormProjectiveMeshCategory × Fin (m + 1)))
local instance intervalCategoryOpFintype (m : ℕ) :
    Fintype (S.standardFormIntervalPrincipalCategory m)ᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

/-- Finite representables for the actual standard-form interval category. -/
theorem standardFormIntervalCategory_finiteRepresentables (m : ℕ) :
    ∀ X : (S.standardFormIntervalPrincipalCategory m)ᵒᵖ,
      CoveringHom.IsFiniteDimensionalModule (C := (S.standardFormIntervalPrincipalCategory m)ᵒᵖ) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) :=
  Graded.FiniteGradedModule.principalIntervalFiniteRepresentables
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent m

/-- Actual interval category modules and the named interval algebra have the same module category. -/
def standardFormIntervalCategoryAlgebraEquivalence (m : ℕ) :
    CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (S.standardFormIntervalPrincipalCategory m)ᵒᵖ) k ≌
      RightModule.FinitelyGeneratedCategory (S.standardFormIntervalAlgebra m) :=
  Graded.FiniteGradedModule.principalIntervalCategoryAlgebraEquivalence
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent m

instance standardFormIntervalCategoryAlgebraEquivalence_additive (m : ℕ) :
    (S.standardFormIntervalCategoryAlgebraEquivalence m).functor.Additive :=
  inferInstanceAs ((Graded.FiniteGradedModule.principalIntervalCategoryAlgebraEquivalence
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent m).functor.Additive)

attribute [local irreducible] standardFormIntervalCategoryAlgebraEquivalence
  standardFormIntervalAlgebraEquivalence standardFormIntervalFamily standardFormIntervalSkeleton

/-- The classified interval algebra skeleton gives local representation finiteness. -/
theorem standardFormIntervalCategory_repFinite (m : ℕ) :
    CoveringHom.IsLocallyRepresentationFinite (k := k)
      (C := (S.standardFormIntervalPrincipalCategory m)ᵒᵖ) :=
  CoveringHom.isLocallyRepresentationFinite_of_finiteSkeleton
    (CoveringHom.pullbackRightModuleIndecomposableSkeleton
      (S.standardFormIntervalCategoryAlgebraEquivalence m) (S.standardFormIntervalSkeleton m))

/-- The shift rank proves directedness of the actual interval functor-module category. -/
theorem standardFormIntervalCategory_directed (m : ℕ) :
    CoveringHom.HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k)
      (C := (S.standardFormIntervalPrincipalCategory m)ᵒᵖ) :=
  CoveringHom.hasAcyclicFiniteModuleNonzeroNonisomorphisms_of_ranked_algebra_family
    (S.standardFormIntervalCategoryAlgebraEquivalence m)
    (S.standardFormIntervalFamily m) (fun a ↦ a.2.val)
    (fun a b f hf hi ↦ S.standardFormIntervalFamily_noniso_descent a b f hf hi)
    (S.standardFormIntervalFamily_complete m)

/-- The category surplus in the packing theorem is the existing interval algebra surplus. -/
theorem standardFormIntervalCategory_surplus_eq (m : ℕ) :
    CoveringHom.finiteCategorySurplus (S.standardFormIntervalCategory_finiteRepresentables m)
      (S.standardFormIntervalCategory_repFinite m) =
      (S.standardFormIntervalSkeleton m).ambientARSurplus :=
  CoveringHom.finiteCategorySurplus_eq_algebra_surplus
    (S.standardFormIntervalCategoryAlgebraEquivalence m)
    (S.standardFormIntervalCategory_finiteRepresentables m)
    (S.standardFormIntervalCategory_repFinite m) (S.standardFormIntervalSkeleton m)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
