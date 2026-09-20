import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalRepresentations
import MagnitudeConjecture.CategoryTheory.CategoryAlgebraMatrixModel
import MagnitudeConjecture.Algebra.RepresentationFiniteQuotient

/-! # A finite interval algebra realizing supported graded modules -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)

local instance principalIntervalFintype (m : ℕ) :
    Fintype (PrincipalIntervalCategory R hmul e he0 m) :=
  inferInstanceAs (Fintype (ι × Fin (m + 1)))
local instance principalIntervalOpFintype (m : ℕ) :
    Fintype (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

include he in
/-- Every representable on the finite interval has finite dimension and finite support. -/
theorem principalIntervalFiniteRepresentables (m : ℕ)
    (X : (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ) :
    CoveringHom.IsFiniteDimensionalModule (C := (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ) k
      (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    let E : (Y.unop ⟶ X.unop) ≃ₗ[k]
        cornerComponent R (e Y.unop.1) (e X.unop.1)
          ((Y.unop.2.val : ℤ) - X.unop.2.val) :=
      InducedCategory.homLinearEquiv.trans
        (principalDegreeHomEquiv R hmul e he0 he _ _)
    letI : FiniteDimensional k (Y.unop ⟶ X.unop) := Module.Finite.equiv E.symm
    exact Module.Finite.equiv (CoveringHom.oppositeHomLinearEquiv (k := k) X Y).symm
  · exact Set.toFinite _

/-- The finite matrix algebra of the interval of actual shifted principal projectives. -/
abbrev principalIntervalAlgebra (_he : ∀ i, e i * e i = e i) (m : ℕ) :=
  End (CoveringHom.categoryAlgebraTuple (C := (PrincipalIntervalCategory R hmul e he0 m)ᵒᵖ))

/-- The matrix model is algebra-isomorphic to the existing representable generator model. -/
def principalIntervalAlgebraRepresentableEquiv (m : ℕ) :
    principalIntervalAlgebra R hmul e he0 he m ≃ₐ[k]
      CoveringHom.finiteCategoryProjectiveGenerator.algebra
        (principalIntervalFiniteRepresentables R hmul e he0 he m) :=
  CoveringHom.categoryAlgebraTupleEquiv
    (principalIntervalFiniteRepresentables R hmul e he0 he m)

/-- The interval algebra is finite dimensional over the original field. -/
theorem principalIntervalAlgebra_finiteDimensional (m : ℕ) :
    FiniteDimensional k (principalIntervalAlgebra R hmul e he0 he m) := by
  letI := CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    (principalIntervalFiniteRepresentables R hmul e he0 he m)
  exact Module.Finite.equiv (principalIntervalAlgebraRepresentableEquiv R hmul e he0 he m).toLinearEquiv.symm

/-- Right modules over the finite interval algebra are actual graded modules supported on that interval. -/
def principalIntervalAlgebraGradedModuleEquivalence
    (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
    (horth : Pairwise fun i j ↦ e i * e j = 0) (m : ℕ) :
    FGModuleCat.{u} (principalIntervalAlgebra R hmul e he0 he m)ᵐᵒᵖ ≌
      SupportedCategory (R := R) m := by
  letI := principalIntervalAlgebra_finiteDimensional R hmul e he0 he m
  letI := CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    (principalIntervalFiniteRepresentables R hmul e he0 he m)
  exact (LeftModule.fgModuleEquivalenceOfAlgEquiv
    (AlgEquiv.op (principalIntervalAlgebraRepresentableEquiv R hmul e he0 he m))).trans
      ((CoveringHom.finiteCategoryProjectiveGenerator.moduleEquivalence
        (principalIntervalFiniteRepresentables R hmul e he0 he m)).symm.trans
          (principalIntervalGradedModuleEquivalence R hmul e he0 he hneg h1 hsum horth m))

end MagnitudeConjecture.Graded.FiniteGradedModule
