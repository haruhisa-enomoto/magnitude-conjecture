import MagnitudeConjecture.Algebra.StringGraphComponentSpanning

/-!
# Boundary continuation for string graph components

A boundary-free coefficient component cannot stop against a displayed arrow
which continues on the other word in the forbidden direction.  These lemmas
turn that condition into explicit matched-arrow and continued-support
witnesses.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- An outgoing target-word arrow at a supported pair has a matching outgoing
source-word arrow. -/
theorem BoundaryFreeMorphismCoefficientComponent.exists_inputArrowStep_of_outputArrowStep
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (i' : D.PositionAt x) (j' : D.PositionAt y)
    (hsupport : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨x, i, i'⟩)
    (hstep : D.ArrowStep a i' j') :
    ∃ j : C.PositionAt y, C.ArrowStep a i j := by
  by_contra h
  exact component.2 ⟨x, i, i'⟩ hsupport
    (IsMorphismCoefficientBoundary.target a i i' j' h hstep)

/-- An incoming source-word arrow at a supported pair has a matching incoming
target-word arrow. -/
theorem BoundaryFreeMorphismCoefficientComponent.exists_outputArrowStep_of_inputArrowStep
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y) (j' : D.PositionAt y)
    (hsupport : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨y, j, j'⟩)
    (hstep : C.ArrowStep a i j) :
    ∃ i' : D.PositionAt x, D.ArrowStep a i' j' := by
  by_contra h
  exact component.2 ⟨y, j, j'⟩ hsupport
    (IsMorphismCoefficientBoundary.source a i j j' hstep h)

/-- A supported pair continues across any outgoing target-word arrow. -/
theorem BoundaryFreeMorphismCoefficientComponent.exists_support_of_outputArrowStep
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (i' : D.PositionAt x) (j' : D.PositionAt y)
    (hsupport : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨x, i, i'⟩)
    (hstep : D.ArrowStep a i' j') :
    ∃ j : C.PositionAt y,
      C.ArrowStep a i j ∧
        Relation.EqvGen (C.MorphismCoefficientStep D)
          component.1.representative ⟨y, j, j'⟩ := by
  obtain ⟨j, hsource⟩ :=
    component.exists_inputArrowStep_of_outputArrowStep a i i' j'
      hsupport hstep
  refine ⟨j, hsource, Relation.EqvGen.trans _ _ _ hsupport ?_⟩
  exact Relation.EqvGen.rel _ _
    (MorphismCoefficientStep.ofArrow a i j i' j' hsource hstep)

/-- A supported pair continues backwards across any incoming source-word
arrow. -/
theorem BoundaryFreeMorphismCoefficientComponent.exists_support_of_inputArrowStep
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y) (j' : D.PositionAt y)
    (hsupport : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨y, j, j'⟩)
    (hstep : C.ArrowStep a i j) :
    ∃ i' : D.PositionAt x,
      D.ArrowStep a i' j' ∧
        Relation.EqvGen (C.MorphismCoefficientStep D)
          component.1.representative ⟨x, i, i'⟩ := by
  obtain ⟨i', htarget⟩ :=
    component.exists_outputArrowStep_of_inputArrowStep a i j j'
      hsupport hstep
  refine ⟨i', htarget, Relation.EqvGen.trans _ _ _ hsupport ?_⟩
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
    (MorphismCoefficientStep.ofArrow a i j i' j' hstep htarget))

end MagnitudeConjecture.BoundQuiver.StringWord.Word
