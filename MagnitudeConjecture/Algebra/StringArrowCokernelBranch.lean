import MagnitudeConjecture.Algebra.StringArrowCokernelBranchIdentification

/-!
# The surviving branch of a string-arrow cokernel

For a displayed arrow `a : x ⟶ y`, the radical of the Butler--Ringel
module `V(a)` is obtained from the radical of the represented projective
`P(y)` by deleting the coordinate indexed by `a`.  Since a special-biserial
vertex has at most two incoming arrows, at most one uniserial branch remains.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- A dependent family of uniserial modules indexed by a subsingleton type
is uniserial. -/
theorem isUniserialModule_pi_of_subsingleton
    {R : Type u} [Ring R] {I : Type u} [Subsingleton I]
    (M : I → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (hM : ∀ i, IsUniserialModule R (M i)) :
    IsUniserialModule R (∀ i, M i) := by
  classical
  by_cases hI : Nonempty I
  · letI : Unique I :=
      { default := Classical.choice hI
        uniq := fun _ ↦ Subsingleton.elim _ _ }
    exact IsUniserialModule.congr
      (LinearEquiv.piUnique R M).symm (hM default)
  · haveI : IsEmpty I := not_nonempty_iff.mp hI
    exact IsUniserialModule.of_subsingleton

/-- Every Butler--Ringel arrow cokernel `V(a)` is uniserial: its radical has
at most the one incoming branch different from `a`, and its top is simple. -/
theorem arrowCokernelFGObj_isUniserial
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
      (P.arrowCokernelFGObj a) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Subsingleton (OtherIncomingArrow (Sigma.mk x a)) :=
    P.otherIncomingArrow_subsingleton (Sigma.mk x a)
  have hfamily : IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
      (∀ b : OtherIncomingArrow (Sigma.mk x a),
        LinearMap.range (P.representedArrowLinearMap b.1.2)) := by
    apply isUniserialModule_pi_of_subsingleton
    intro b
    exact P.representedArrowLinearRange_isUniserial b.1.2
  have hradical : IsUniserialModule P.quotientCategoryAlgebraᵐᵒᵖ
      (Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.arrowCokernelFGObj a)) :=
    IsUniserialModule.congr
      (P.otherIncomingFamilyCokernelRadicalLinearEquiv a) hfamily
  exact IsUniserialModule.of_simpleTop_of_jacobson
    (P.arrowCokernelFGObj_top_isSimple a) hradical
