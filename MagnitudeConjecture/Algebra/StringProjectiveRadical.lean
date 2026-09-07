import MagnitudeConjecture.Algebra.StringProjectiveIncomingSum
import MagnitudeConjecture.Algebra.StringQuotientEndLocal
import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates

/-!
# Projective radicals of a string category algebra

Dimension and maximal-submodule arguments identify the incoming-arrow sum
inside a represented canonical projective with its Jacobson radical.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- The total continuation-basis index over all arrows ending at a vertex is
finite. -/
instance incomingContinuationFinite
    (P : StringPresentation k A Q) (y : Q) :
    Finite
      (Σ a : DisplayedIncomingArrow y,
        P.toSpecialBiserialPresentation.LeftContinuationPath a.2) := by
  letI (a : DisplayedIncomingArrow y) : Finite
      (P.toSpecialBiserialPresentation.LeftContinuationPath a.2) :=
    P.toSpecialBiserialPresentation.leftContinuationPath_finite a.2
  infer_instance

/-- The zero-length surviving path ending at `y` is the trivial path at
`y`. -/
def nilVertexPath (P : StringPresentation k A Q) (y : Q) :
    P.VertexPath y :=
  ⟨y, ⟨Quiver.Path.nil,
    pathMap_ne_zero_of_length_lt_two P.toPresentation.admissible
      Quiver.Path.nil (by simp)⟩⟩

/-- There is exactly one zero-length surviving path ending at a fixed
vertex. -/
theorem zeroLengthVertexPath_unique
    (P : StringPresentation k A Q) (y : Q)
    (p : {p : P.VertexPath y // p.2.1.length = 0}) :
    p.1 = P.nilVertexPath y := by
  rcases p with ⟨⟨z, ⟨q, hq⟩⟩, hlen⟩
  have hzy : z = y := q.eq_of_length_zero hlen
  subst z
  have hqnil : q = Quiver.Path.nil := q.eq_nil_of_length_zero hlen
  subst q
  rfl

/-- The zero-length part of the global represented-projective path basis has
cardinality one. -/
theorem natCard_zeroLengthVertexPath_eq_one
    (P : StringPresentation k A Q) (y : Q) :
    Nat.card {p : P.VertexPath y // p.2.1.length = 0} = 1 := by
  letI : Fintype {p : P.VertexPath y // p.2.1.length = 0} :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
  refine ⟨⟨P.nilVertexPath y, by simp [nilVertexPath]⟩, ?_⟩
  intro p
  apply Subtype.ext
  exact P.zeroLengthVertexPath_unique y p

/-- The complete path basis is the disjoint union of the nontrivial path
basis and the unique trivial path. -/
theorem natCard_vertexPath_eq_positive_add_one
    (P : StringPresentation k A Q) (y : Q) :
    Nat.card (P.VertexPath y) =
      Nat.card (P.PositiveVertexPath y) + 1 := by
  let pred : P.VertexPath y → Prop := fun p ↦ p.2.1.length ≠ 0
  let e := Equiv.sumCompl pred
  calc
    Nat.card (P.VertexPath y) =
        Nat.card ({p : P.VertexPath y // pred p} ⊕
          {p : P.VertexPath y // ¬ pred p}) :=
      (Nat.card_congr e).symm
    _ = Nat.card {p : P.VertexPath y // pred p} +
        Nat.card {p : P.VertexPath y // ¬ pred p} := Nat.card_sum
    _ = Nat.card (P.PositiveVertexPath y) + 1 := by
      congr 1
      simpa only [pred, not_not] using
        P.natCard_zeroLengthVertexPath_eq_one y

/-- The represented canonical projective has dimension equal to the number
of its surviving-path basis vectors. -/
theorem finrank_representedVertexModule_eq_natCard
    (P : StringPresentation k A Q) (y : Q) :
    Module.finrank k (P.representedVertexModule y) =
      Nat.card (P.VertexPath y) := by
  letI : Fintype (P.VertexPath y) := Fintype.ofFinite _
  simpa only [Fintype.card_eq_nat_card] using
    Module.finrank_eq_card_basis (P.representedVertexPathBasis y)

/-- The product of incoming arrow ranges has dimension equal to its literal
continuation-basis cardinality. -/
theorem finrank_incomingArrowRangeFamily_eq_natCard
    (P : StringPresentation k A Q) (y : Q) :
    Module.finrank k
        (∀ a : DisplayedIncomingArrow y,
          LinearMap.range (P.representedArrowLinearMap a.2)) =
      Nat.card
        (Σ a : DisplayedIncomingArrow y,
          P.toSpecialBiserialPresentation.LeftContinuationPath a.2) := by
  letI : Fintype
      (Σ a : DisplayedIncomingArrow y,
        P.toSpecialBiserialPresentation.LeftContinuationPath a.2) :=
    Fintype.ofFinite _
  simpa only [Fintype.card_eq_nat_card] using
    Module.finrank_eq_card_basis (P.incomingArrowRangeBasis y)

/-- The sum of all represented arrow ranges ending at a vertex has
codimension one in the corresponding canonical projective. -/
theorem finrank_incomingArrowRangeSum_quotient_eq_one
    (P : StringPresentation k A Q) (y : Q) :
    Module.finrank k
        (P.representedVertexModule y ⧸
          LinearMap.range (P.incomingArrowRangeSumLinearMap y)) = 1 := by
  letI : Module.Finite k (P.representedVertexModule y) :=
    Module.Finite.of_basis (P.representedVertexPathBasis y)
  let N := LinearMap.range (P.incomingArrowRangeSumLinearMap y)
  have hRange : Module.finrank k N =
      Module.finrank k
        (∀ a : DisplayedIncomingArrow y,
          LinearMap.range (P.representedArrowLinearMap a.2)) := by
    let e := LinearEquiv.ofInjective
      (P.incomingArrowRangeSumLinearMap y)
      (P.incomingArrowRangeSumLinearMap_injective y)
    exact (e.restrictScalars k).finrank_eq.symm
  have hPositive :
      Nat.card
          (Σ a : DisplayedIncomingArrow y,
            P.toSpecialBiserialPresentation.LeftContinuationPath a.2) =
        Nat.card (P.PositiveVertexPath y) :=
    Nat.card_congr (P.incomingContinuationEquivPositiveVertexPath y)
  have hTarget : Module.finrank k (P.representedVertexModule y) =
      Module.finrank k N + 1 := by
    rw [P.finrank_representedVertexModule_eq_natCard y,
      P.natCard_vertexPath_eq_positive_add_one y, hRange,
      P.finrank_incomingArrowRangeFamily_eq_natCard y, hPositive]
  rw [N.finrank_quotient, hTarget]
  omega

/-- The internal sum of all represented arrow ranges ending at a vertex is
a maximal submodule of the corresponding canonical projective. -/
theorem incomingArrowRangeSum_isCoatom
    (P : StringPresentation k A Q) (y : Q) :
    IsCoatom (LinearMap.range (P.incomingArrowRangeSumLinearMap y)) := by
  apply isSimpleModule_iff_isCoatom.mp
  exact
    { __ := is_simple_module_of_finrank_eq_one
        (P.finrank_incomingArrowRangeSum_quotient_eq_one y) }

/-- The internal sum of the represented incoming-arrow ranges is exactly
the module Jacobson radical of the represented canonical projective. -/
theorem incomingArrowRangeSum_eq_jacobson
    (P : StringPresentation k A Q) (y : Q) :
    LinearMap.range (P.incomingArrowRangeSumLinearMap y) =
      Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let hlocal : ∀ X : Category P.toPresentation.relations,
      IsLocalRing (End X) := fun X ↦ P.quotientEnd_isLocalRing X
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let e := P.vertexRightIdealRepresentedLinearEquiv y
  have hProjector : IsIdempotentElem (P.vertexProjector y) := by
    rw [IsIdempotentElem, End.mul_def]
    simp [vertexProjector, Category.assoc]
  letI : Module.Projective P.quotientCategoryAlgebraᵐᵒᵖ
      (RightModule.rightIdeal (P.vertexProjector y)) :=
    RightModule.rightIdeal_moduleProjective hProjector
  letI : Module.Projective P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) :=
    Module.Projective.of_equiv' e
  let b := P.representedVertexPathBasis y
  let p₀ := P.nilVertexPath y
  letI : Nontrivial (P.representedVertexModule y) :=
    ⟨b p₀, 0, b.ne_zero p₀⟩
  letI : Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) := inferInstance
  let X := P.quotientRepresentable (obj P.toPresentation.relations y)
  let F := CoveringHom.finiteCategoryProjectiveGenerator.representedFGFunctor hP
  letI : IsLocalRing (End X) :=
    CoveringHom.finiteDimensionalLinearCoyoneda_end_isLocalRing
      hP hlocal (obj P.toPresentation.relations y)
  letI : IsLocalRing (End (F.obj X)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (CategoryTheory.Functor.endRingEquivOfFullyFaithful F X)
  letI : IsLocalRing
      (Module.End P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y)) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (RightModule.FiniteIndecomposableSkeleton.fgEndModuleEndRingEquiv
        (P.representedVertexModule y))
  have hJacobson : IsCoatom
      (Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y)) :=
    jacobson_isCoatom_of_projective_local_end
  have hIncoming := P.incomingArrowRangeSum_isCoatom y
  have hle : Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) ≤
      LinearMap.range (P.incomingArrowRangeSumLinearMap y) :=
    sInf_le hIncoming
  exact (hJacobson.le_iff_eq hIncoming.ne_top).mp hle

end StringPresentation

end MagnitudeConjecture.BoundQuiver
