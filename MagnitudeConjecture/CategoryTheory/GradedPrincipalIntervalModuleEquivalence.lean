import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalAlgebra
import MagnitudeConjecture.CategoryTheory.FiniteCategorySurplusInvariant

/-! # Interval category modules and the actual interval algebra -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

/-- The finite functor modules are precisely right modules over the interval matrix algebra. -/
def principalIntervalCategoryAlgebraEquivalence (m : ℕ) :
    CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ) k ≌
      FGModuleCat.{u} (principalIntervalAlgebra R hmul e he0 he m)ᵐᵒᵖ := by
  letI : Fintype (PrincipalIntervalCategory R hmul e he0 m) :=
    inferInstanceAs (Fintype (ι × Fin (m + 1)))
  letI : Fintype (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ :=
    Fintype.ofEquiv _ Opposite.equivToOpposite
  let hP := principalIntervalFiniteRepresentables R hmul e he0 he m
  letI := principalIntervalAlgebra_finiteDimensional R hmul e he0 he m
  letI := CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  exact (CoveringHom.finiteCategoryProjectiveGenerator.moduleEquivalence hP).trans
    (LeftModule.fgModuleEquivalenceOfAlgEquiv
      (AlgEquiv.op (principalIntervalAlgebraRepresentableEquiv R hmul e he0 he m))).symm

instance principalIntervalCategoryAlgebraEquivalence_additive (m : ℕ) :
    (principalIntervalCategoryAlgebraEquivalence R hmul e he0 he m).functor.Additive := by
  letI := principalIntervalAlgebra_finiteDimensional R hmul e he0 he m
  letI : IsNoetherianRing (principalIntervalAlgebra R hmul e he0 he m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
  exact Functor.additive_of_preserves_binary_products _

end MagnitudeConjecture.Graded.FiniteGradedModule
