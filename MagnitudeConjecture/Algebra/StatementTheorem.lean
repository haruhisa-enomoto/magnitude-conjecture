import MagnitudeConjecture.Algebra.StatementFiniteModules
import MagnitudeConjecture.Algebra.StatementPresentation

/-!
# The full theorem in the independent Mathlib vocabulary

Both directions of special biseriality preserve the displayed quiver and
Morita equivalence. Together with the numerical connections, this derives
the independent statement from the production theorem.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory

namespace MagnitudeConjecture.Statement
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A]

attribute [local instance] SpecialBiserialModel.ring SpecialBiserialModel.algebra
  SpecialBiserialModel.finiteDimensional SpecialBiserialModel.vertices
  SpecialBiserialModel.quiver SpecialBiserialModel.arrows

/-- The independent special-biserial predicate has exactly the production
meaning, including the Morita-class convention for nonbasic algebras. -/
theorem isSpecialBiserial_iff :
    IsSpecialBiserial k A ↔ BoundQuiver.IsSpecialBiserial k A := by
  constructor
  · rintro ⟨M⟩
    exact ⟨{
      Carrier := M.Carrier
      morita := M.morita
      presentation := ⟨{
        Vertex := M.Vertex
        vertexFintype := M.vertices
        quiver := M.quiver
        arrowFintype := M.arrows
        presentation := M.presentation.toProduction }⟩ }⟩
  · rintro ⟨M⟩
    obtain ⟨P⟩ := M.presentation
    let : Fintype P.Vertex := P.vertexFintype
    let : Quiver.{u} P.Vertex := P.quiver
    let (x y : P.Vertex) : Fintype (x ⟶ y) := P.arrowFintype x y
    exact ⟨{
      Carrier := M.Carrier
      morita := M.morita
      Vertex := P.Vertex
      presentation := QuiverPresentation.ofProduction P.presentation }⟩

/-- The magnitude theorem with independent definitions: nonsingularity of
the Hom matrix, the lower bound by simple classes, and the full equality case. -/
theorem mainClaim [IsAlgClosed k] : MainClaim k A := by
  intro S
  let : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k _
  obtain ⟨hle, heq⟩ := S.magnitude_inequality_and_equality
  exact ⟨S.homMatrix_det_ne_zero, hle, heq.trans isSpecialBiserial_iff.symm⟩

end MagnitudeConjecture.Statement
