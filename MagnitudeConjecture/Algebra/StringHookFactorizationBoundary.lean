import MagnitudeConjecture.Algebra.StringGraphComponentFactorizationAlignment
import MagnitudeConjecture.Algebra.StringGraphComponentProperInterval
import MagnitudeConjecture.Algebra.StringHookCohookFactorizationLength

/-!
# The first arm edge in right hook and cohook factorizations

For a strict-growth factorization of a right hook through a literal string,
the outward edge of the selected full-target interval forces the first factor
component to continue across the hook's actual first new position.  Both
orientation-preserving and orientation-reversing overlaps are retained.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Pointwise factorization alignment identifies the first component above
the position selected by the full-output-support second component. -/
theorem HookExtension.firstComponent_support_inputPosition
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (first : D.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent C)
    (houtput : second.HasFullOutputSupport)
    (hne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0)
    {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (D.MorphismCoefficientStep M)
      first.1.representative
      ⟨x, hook.toPositiveBoundaryExtension.toRightExtension.position i,
        second.inputPosition houtput i⟩ := by
  obtain ⟨j, hfirst, hsecond⟩ :=
    hook.exists_intermediate_of_component_pair hmono first second hne i
  have hj := second.inputPosition_eq_of_support houtput i j hsecond
  rw [hj]
  exact hfirst

/-- In the strict-growth branch, the first factor component continues across
the actual first new position of the right hook. -/
theorem HookExtension.exists_firstNewPosition_support_of_component_pair_of_length_lt
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (first : D.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent C)
    (houtput : second.HasFullOutputSupport)
    (hne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0)
    (hlength : C.length < M.length) :
    ∃ j : M.PositionAt hook.vertex,
      (j.index = (second.inputPosition houtput C.targetPosition).index + 1 ∨
        j.index + 1 =
          (second.inputPosition houtput C.targetPosition).index) ∧
      Relation.EqvGen (D.MorphismCoefficientStep M)
        first.1.representative
        ⟨hook.vertex,
          hook.toPositiveBoundaryExtension.firstNewPosition, j⟩ := by
  have hfirstSource := hook.firstComponent_support_inputPosition
    hmono first second houtput hne C.sourcePosition
  have hfirstTarget := hook.firstComponent_support_inputPosition
    hmono first second houtput hne C.targetPosition
  rcases houtput.exists_outgoingBoundary_of_length_lt second hlength with
    ⟨hforward, hleft | hright⟩ | ⟨hreverse, hleft | hright⟩
  · obtain ⟨x, j, a, hj, hstep⟩ := hleft
    obtain ⟨d, hdstep, hcontinued⟩ :=
      first.exists_support_of_outputArrowStep a
        (hook.toPositiveBoundaryExtension.toRightExtension.position
          C.sourcePosition)
        (second.inputPosition houtput C.sourcePosition) j
        hfirstSource hstep
    have hdindexStep := hdstep.index
    rw [hook.toPositiveBoundaryExtension.toRightExtension.position_index,
      C.sourcePosition_index] at hdindexStep
    have hdindex : d.index = 1 := by omega
    by_cases hzero : C.length = 0
    · have hposition : (⟨x, d⟩ : D.Position) =
          ⟨hook.vertex,
            hook.toPositiveBoundaryExtension.firstNewPosition⟩ :=
        Position.ext_index (C := D) (by
          change d.index =
            hook.toPositiveBoundaryExtension.firstNewPosition.index
          simp [hdindex, hzero])
      cases hposition
      exact ⟨j, Or.inr (by omega), hcontinued⟩
    · have hpos : 0 < C.length := Nat.pos_of_ne_zero hzero
      have hcomponent : Relation.EqvGen (D.MorphismCoefficientStep M)
          (⟨x, d, j⟩ : D.MorphismCoefficientPosition M)
          ⟨C.target,
            hook.toPositiveBoundaryExtension.toRightExtension.position
              C.targetPosition,
            second.inputPosition houtput C.targetPosition⟩ :=
        Relation.EqvGen.trans _ first.1.representative _
          hcontinued.symm hfirstTarget
      have hinputLe : d.index ≤
          (hook.toPositiveBoundaryExtension.toRightExtension.position
            C.targetPosition).index := by
        rw [RightExtension.position_index, targetPosition_index]
        omega
      have hslope := D.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
        M hcomponent hinputLe
      simp only [MorphismCoefficientPosition.inputIndex,
        MorphismCoefficientPosition.outputIndex,
        RightExtension.position_index, targetPosition_index] at hslope
      omega
  · obtain ⟨y, j, a, hj, hstep⟩ := hright
    obtain ⟨d, _, hcontinued⟩ :=
      first.exists_support_of_outputArrowStep a
        (hook.toPositiveBoundaryExtension.toRightExtension.position
          C.targetPosition)
        (second.inputPosition houtput C.targetPosition) j
        hfirstTarget hstep
    have hcomponent : Relation.EqvGen (D.MorphismCoefficientStep M)
        (⟨C.source,
          hook.toPositiveBoundaryExtension.toRightExtension.position
            C.sourcePosition,
          second.inputPosition houtput C.sourcePosition⟩ :
          D.MorphismCoefficientPosition M)
        ⟨y, d, j⟩ :=
      Relation.EqvGen.trans _ first.1.representative _
        hfirstSource.symm hcontinued
    have hinputLe :
        (hook.toPositiveBoundaryExtension.toRightExtension.position
          C.sourcePosition).index ≤ d.index := by simp
    have hslope := D.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      M hcomponent hinputLe
    simp only [MorphismCoefficientPosition.inputIndex,
      MorphismCoefficientPosition.outputIndex,
      RightExtension.position_index, sourcePosition_index,
      Nat.sub_zero] at hslope
    have hdindex : d.index = C.length + 1 := by omega
    have hposition : (⟨y, d⟩ : D.Position) =
        ⟨hook.vertex,
          hook.toPositiveBoundaryExtension.firstNewPosition⟩ :=
      Position.ext_index (C := D) (by
        change d.index =
          hook.toPositiveBoundaryExtension.firstNewPosition.index
        simp [hdindex])
    cases hposition
    exact ⟨j, Or.inl hj, hcontinued⟩
  · obtain ⟨x, j, a, hj, hstep⟩ := hleft
    obtain ⟨d, _, hcontinued⟩ :=
      first.exists_support_of_outputArrowStep a
        (hook.toPositiveBoundaryExtension.toRightExtension.position
          C.targetPosition)
        (second.inputPosition houtput C.targetPosition) j
        hfirstTarget hstep
    have hcomponent : Relation.EqvGen (D.MorphismCoefficientStep M)
        (⟨C.source,
          hook.toPositiveBoundaryExtension.toRightExtension.position
            C.sourcePosition,
          second.inputPosition houtput C.sourcePosition⟩ :
          D.MorphismCoefficientPosition M)
        ⟨x, d, j⟩ :=
      Relation.EqvGen.trans _ first.1.representative _
        hfirstSource.symm hcontinued
    have hinputLe :
        (hook.toPositiveBoundaryExtension.toRightExtension.position
          C.sourcePosition).index ≤ d.index := by simp
    have hslope := D.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      M hcomponent hinputLe
    simp only [MorphismCoefficientPosition.inputIndex,
      MorphismCoefficientPosition.outputIndex,
      RightExtension.position_index, sourcePosition_index,
      Nat.sub_zero] at hslope
    have hdindex : d.index = C.length + 1 := by omega
    have hposition : (⟨x, d⟩ : D.Position) =
        ⟨hook.vertex,
          hook.toPositiveBoundaryExtension.firstNewPosition⟩ :=
      Position.ext_index (C := D) (by
        change d.index =
          hook.toPositiveBoundaryExtension.firstNewPosition.index
        simp [hdindex])
    cases hposition
    exact ⟨j, Or.inr hj, hcontinued⟩
  · obtain ⟨y, j, a, hj, hstep⟩ := hright
    obtain ⟨d, hdstep, hcontinued⟩ :=
      first.exists_support_of_outputArrowStep a
        (hook.toPositiveBoundaryExtension.toRightExtension.position
          C.sourcePosition)
        (second.inputPosition houtput C.sourcePosition) j
        hfirstSource hstep
    have hdindexStep := hdstep.index
    rw [hook.toPositiveBoundaryExtension.toRightExtension.position_index,
      C.sourcePosition_index] at hdindexStep
    have hdindex : d.index = 1 := by omega
    by_cases hzero : C.length = 0
    · have hposition : (⟨y, d⟩ : D.Position) =
          ⟨hook.vertex,
            hook.toPositiveBoundaryExtension.firstNewPosition⟩ :=
        Position.ext_index (C := D) (by
          change d.index =
            hook.toPositiveBoundaryExtension.firstNewPosition.index
          simp [hdindex, hzero])
      cases hposition
      exact ⟨j, Or.inl (by omega), hcontinued⟩
    · have hpos : 0 < C.length := Nat.pos_of_ne_zero hzero
      have hcomponent : Relation.EqvGen (D.MorphismCoefficientStep M)
          (⟨y, d, j⟩ : D.MorphismCoefficientPosition M)
          ⟨C.target,
            hook.toPositiveBoundaryExtension.toRightExtension.position
              C.targetPosition,
            second.inputPosition houtput C.targetPosition⟩ :=
        Relation.EqvGen.trans _ first.1.representative _
          hcontinued.symm hfirstTarget
      have hinputLe : d.index ≤
          (hook.toPositiveBoundaryExtension.toRightExtension.position
            C.targetPosition).index := by
        rw [RightExtension.position_index, targetPosition_index]
        omega
      have hslope := D.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
        M hcomponent hinputLe
      simp only [MorphismCoefficientPosition.inputIndex,
        MorphismCoefficientPosition.outputIndex,
        RightExtension.position_index, targetPosition_index] at hslope
      omega

/-- Pointwise factorization alignment identifies the second component below
the position selected by the full-input-support first component. -/
theorem CohookExtension.secondComponent_support_outputPosition
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : first.HasFullInputSupport)
    (hne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0)
    {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (M.MorphismCoefficientStep D)
      second.1.representative
      ⟨x, first.outputPosition hinput i,
        cohook.toNegativeBoundaryExtension.toRightExtension.position i⟩ := by
  obtain ⟨j, hfirst, hsecond⟩ :=
    cohook.exists_intermediate_of_component_pair hmono first second hne i
  have hj := first.outputPosition_eq_of_support hinput i j hfirst
  rw [hj]
  exact hsecond

/-- In the strict-growth branch, the second factor component continues across
the actual first new position of the right cohook. -/
theorem CohookExtension.exists_firstNewPosition_support_of_component_pair_of_length_lt
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : first.HasFullInputSupport)
    (hne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0)
    (hlength : C.length < M.length) :
    ∃ i : M.PositionAt cohook.vertex,
      (i.index = (first.outputPosition hinput C.targetPosition).index + 1 ∨
        i.index + 1 =
          (first.outputPosition hinput C.targetPosition).index) ∧
      Relation.EqvGen (M.MorphismCoefficientStep D)
        second.1.representative
        ⟨cohook.vertex, i,
          cohook.toNegativeBoundaryExtension.firstNewPosition⟩ := by
  have hsecondSource := cohook.secondComponent_support_outputPosition
    hmono first second hinput hne C.sourcePosition
  have hsecondTarget := cohook.secondComponent_support_outputPosition
    hmono first second hinput hne C.targetPosition
  rcases hinput.exists_incomingBoundary_of_length_lt first hlength with
    ⟨hforward, hleft | hright⟩ | ⟨hreverse, hleft | hright⟩
  · obtain ⟨x, i, a, hi, hstep⟩ := hleft
    obtain ⟨d, hdstep, hcontinued⟩ :=
      second.exists_support_of_inputArrowStep a i
        (first.outputPosition hinput C.sourcePosition)
        (cohook.toNegativeBoundaryExtension.toRightExtension.position
          C.sourcePosition)
        hsecondSource hstep
    have hdindexStep := hdstep.index
    rw [cohook.toNegativeBoundaryExtension.toRightExtension.position_index,
      C.sourcePosition_index] at hdindexStep
    have hdindex : d.index = 1 := by omega
    by_cases hzero : C.length = 0
    · have hposition : (⟨x, d⟩ : D.Position) =
          ⟨cohook.vertex,
            cohook.toNegativeBoundaryExtension.firstNewPosition⟩ :=
        Position.ext_index (C := D) (by
          change d.index =
            cohook.toNegativeBoundaryExtension.firstNewPosition.index
          simp [hdindex, hzero])
      cases hposition
      exact ⟨i, Or.inr (by omega), hcontinued⟩
    · have hpos : 0 < C.length := Nat.pos_of_ne_zero hzero
      have hcomponent : Relation.EqvGen (M.MorphismCoefficientStep D)
          (⟨x, i, d⟩ : M.MorphismCoefficientPosition D)
          ⟨C.target,
            first.outputPosition hinput C.targetPosition,
            cohook.toNegativeBoundaryExtension.toRightExtension.position
              C.targetPosition⟩ :=
        Relation.EqvGen.trans _ second.1.representative _
          hcontinued.symm hsecondTarget
      have hinputLe : i.index ≤
          (first.outputPosition hinput C.targetPosition).index := by
        omega
      have hslope := M.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
        D hcomponent hinputLe
      simp only [MorphismCoefficientPosition.inputIndex,
        MorphismCoefficientPosition.outputIndex,
        RightExtension.position_index, targetPosition_index] at hslope
      omega
  · obtain ⟨y, i, a, hi, hstep⟩ := hright
    obtain ⟨d, _, hcontinued⟩ :=
      second.exists_support_of_inputArrowStep a i
        (first.outputPosition hinput C.targetPosition)
        (cohook.toNegativeBoundaryExtension.toRightExtension.position
          C.targetPosition)
        hsecondTarget hstep
    have hcomponent : Relation.EqvGen (M.MorphismCoefficientStep D)
        (⟨C.source, first.outputPosition hinput C.sourcePosition,
          cohook.toNegativeBoundaryExtension.toRightExtension.position
            C.sourcePosition⟩ : M.MorphismCoefficientPosition D)
        ⟨y, i, d⟩ :=
      Relation.EqvGen.trans _ second.1.representative _
        hsecondSource.symm hcontinued
    have hinputLe :
        (first.outputPosition hinput C.sourcePosition).index ≤ i.index := by
      omega
    have hslope := M.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hinputLe
    simp only [MorphismCoefficientPosition.inputIndex,
      MorphismCoefficientPosition.outputIndex,
      RightExtension.position_index, sourcePosition_index,
      Nat.zero_add] at hslope
    have hdindex : d.index = C.length + 1 := by omega
    have hposition : (⟨y, d⟩ : D.Position) =
        ⟨cohook.vertex,
          cohook.toNegativeBoundaryExtension.firstNewPosition⟩ :=
      Position.ext_index (C := D) (by
        change d.index =
          cohook.toNegativeBoundaryExtension.firstNewPosition.index
        simp [hdindex])
    cases hposition
    exact ⟨i, Or.inl hi, hcontinued⟩
  · obtain ⟨x, i, a, hi, hstep⟩ := hleft
    obtain ⟨d, _, hcontinued⟩ :=
      second.exists_support_of_inputArrowStep a i
        (first.outputPosition hinput C.targetPosition)
        (cohook.toNegativeBoundaryExtension.toRightExtension.position
          C.targetPosition)
        hsecondTarget hstep
    have hcomponent : Relation.EqvGen (M.MorphismCoefficientStep D)
        (⟨x, i, d⟩ : M.MorphismCoefficientPosition D)
        ⟨C.source, first.outputPosition hinput C.sourcePosition,
          cohook.toNegativeBoundaryExtension.toRightExtension.position
            C.sourcePosition⟩ :=
      Relation.EqvGen.trans _ second.1.representative _
        hcontinued.symm hsecondSource
    have hinputLe : i.index ≤
        (first.outputPosition hinput C.sourcePosition).index := by
      omega
    have hslope := M.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hinputLe
    simp only [MorphismCoefficientPosition.inputIndex,
      MorphismCoefficientPosition.outputIndex,
      RightExtension.position_index, sourcePosition_index,
      Nat.zero_add] at hslope
    have hdindex : d.index = C.length + 1 := by omega
    have hposition : (⟨x, d⟩ : D.Position) =
        ⟨cohook.vertex,
          cohook.toNegativeBoundaryExtension.firstNewPosition⟩ :=
      Position.ext_index (C := D) (by
        change d.index =
          cohook.toNegativeBoundaryExtension.firstNewPosition.index
        simp [hdindex])
    cases hposition
    exact ⟨i, Or.inr hi, hcontinued⟩
  · obtain ⟨y, i, a, hi, hstep⟩ := hright
    obtain ⟨d, hdstep, hcontinued⟩ :=
      second.exists_support_of_inputArrowStep a i
        (first.outputPosition hinput C.sourcePosition)
        (cohook.toNegativeBoundaryExtension.toRightExtension.position
          C.sourcePosition)
        hsecondSource hstep
    have hdindexStep := hdstep.index
    rw [cohook.toNegativeBoundaryExtension.toRightExtension.position_index,
      C.sourcePosition_index] at hdindexStep
    have hdindex : d.index = 1 := by omega
    by_cases hzero : C.length = 0
    · have hposition : (⟨y, d⟩ : D.Position) =
          ⟨cohook.vertex,
            cohook.toNegativeBoundaryExtension.firstNewPosition⟩ :=
        Position.ext_index (C := D) (by
          change d.index =
            cohook.toNegativeBoundaryExtension.firstNewPosition.index
          simp [hdindex, hzero])
      cases hposition
      exact ⟨i, Or.inl (by omega), hcontinued⟩
    · have hpos : 0 < C.length := Nat.pos_of_ne_zero hzero
      have hcomponent : Relation.EqvGen (M.MorphismCoefficientStep D)
          ⟨C.target, first.outputPosition hinput C.targetPosition,
            cohook.toNegativeBoundaryExtension.toRightExtension.position
              C.targetPosition⟩
          (⟨y, i, d⟩ : M.MorphismCoefficientPosition D) :=
        Relation.EqvGen.trans _ second.1.representative _
          hsecondTarget.symm hcontinued
      have hinputLe :
          (first.outputPosition hinput C.targetPosition).index ≤ i.index := by
        omega
      have hslope := M.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
        D hcomponent hinputLe
      simp only [MorphismCoefficientPosition.inputIndex,
        MorphismCoefficientPosition.outputIndex,
        RightExtension.position_index, targetPosition_index] at hslope
      omega

end MagnitudeConjecture.BoundQuiver.StringWord.Word
