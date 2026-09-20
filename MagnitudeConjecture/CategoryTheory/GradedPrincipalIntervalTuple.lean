import MagnitudeConjecture.CategoryTheory.CategoryAlgebraOppositeTuple
import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalAlgebra
import MagnitudeConjecture.CategoryTheory.GradedPrincipalBlockProduct

/-! # Identifying interval algebras with principal-projective tuples -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

/-- The interval algebra used for module classification equals the direct
principal-projective tuple algebra used for separated blocks. -/
def principalIntervalAlgebraTupleEquiv (r : ℕ) :
    principalIntervalAlgebra R hmul e he0 he r ≃ₐ[k]
      End (principalIntervalTuple R hmul e he0 r) := by
  letI : Fintype (PrincipalIntervalCategory R hmul e he0 r) :=
    inferInstanceAs (Fintype (ι × Fin (r + 1)))
  let F := inducedFunctor (intervalProjectiveLabel R hmul e he0 r)
  exact CoveringHom.categoryAlgebraOppositeTupleEquiv (k := k) F

/-- The algebra of separated translated blocks is the product of the actual
small interval algebras. -/
def principalSeparatedBlockAlgebraEquiv
    (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (h : ℕ) (hupper : ∀ d : ℤ, (h : ℤ) < d → R.component d = ⊥) (r q : ℕ) :
    End (principalSeparatedBlockTuple R hmul e he0 r h q) ≃ₐ[k]
      (Fin q → principalIntervalAlgebra R hmul e he0 he r) :=
  (principalSeparatedBlockEndAlgEquiv R hmul e he0 he hneg h hupper r q).trans
    (AlgEquiv.piCongrRight (fun _ ↦ (principalIntervalAlgebraTupleEquiv R hmul e he0 he r).symm))

end MagnitudeConjecture.Graded.FiniteGradedModule
