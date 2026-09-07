import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation

/-!
# Nonzero representable generators of finite functors

Every nonzero finite-dimensional functor receives a nonzero morphism from one
finite-dimensional representable. This is the componentwise form of the
finite-representable generation theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- A nonzero finite-dimensional functor receives a nonzero map from a
finite-dimensional representable. -/
theorem finiteDimensionalModule_exists_nonzero_representableMap
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (hM : ¬ IsZero M) :
    ∃ (X : C) (f : finiteDimensionalLinearCoyoneda (k := k) X (hP X) ⟶ M),
      f ≠ 0 := by
  classical
  obtain ⟨P⟩ := finiteRepresentablePresentation_nonempty hP M
  by_contra h
  push Not at h
  have hcomponent (i : Fin P.n) :
      biproduct.ι (fun i ↦
        (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
          (Opposite.op (P.X i))) i ≫ P.f = 0 := by
    exact h (P.X i) _
  have hf : P.f = 0 := by
    apply biproduct.hom_ext'
    intro i
    exact hcomponent i
  exact hM (IsZero.of_epi_eq_zero P.f hf)

end MagnitudeConjecture.CoveringHom
