import MagnitudeConjecture.Algebra.StringGraphComponentBoundaryContinuation
import MagnitudeConjecture.Algebra.StringGraphComponentFullSupport

/-!
# Proper intervals of full-support string graph components

The position selected by a one-sided full-support component traverses the
entire shorter word with constant slope.  When the other word is strictly
longer, the selected interval has an explicit unused position on at least one
of its two sides.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The source positions selected over the two target endpoints differ by
the target word's length. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.inputPosition_endpointSlope
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport) :
    (component.inputPosition hfull D.targetPosition).index =
        (component.inputPosition hfull D.sourcePosition).index + D.length ∨
      (component.inputPosition hfull D.sourcePosition).index =
        (component.inputPosition hfull D.targetPosition).index + D.length := by
  obtain ⟨i₀, iₙ, hi₀, hiₙ, hslope⟩ :=
    hfull.exists_endpointPositions component
  have hi₀eq := component.inputPosition_eq_of_support
    hfull D.sourcePosition i₀ hi₀
  have hiₙeq := component.inputPosition_eq_of_support
    hfull D.targetPosition iₙ hiₙ
  rw [hi₀eq, hiₙeq]
  exact hslope

/-- If the source word is strictly longer, a full-target-support component
occupies a proper source interval, with the unused side recorded together
with its orientation. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.inputPosition_properInterval
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hlength : D.length < C.length) :
    ((component.inputPosition hfull D.targetPosition).index =
          (component.inputPosition hfull D.sourcePosition).index + D.length ∧
        (0 < (component.inputPosition hfull D.sourcePosition).index ∨
          (component.inputPosition hfull D.targetPosition).index < C.length)) ∨
      ((component.inputPosition hfull D.sourcePosition).index =
          (component.inputPosition hfull D.targetPosition).index + D.length ∧
        (0 < (component.inputPosition hfull D.targetPosition).index ∨
          (component.inputPosition hfull D.sourcePosition).index < C.length)) := by
  have hsource := (component.inputPosition hfull D.sourcePosition).index_le
  have htarget := (component.inputPosition hfull D.targetPosition).index_le
  rcases hfull.inputPosition_endpointSlope component with hslope | hslope
  · left
    refine ⟨hslope, ?_⟩
    omega
  · right
    refine ⟨hslope, ?_⟩
    omega

/-- The target positions selected over the two source endpoints differ by
the source word's length. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.outputPosition_endpointSlope
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport) :
    (component.outputPosition hfull C.targetPosition).index =
        (component.outputPosition hfull C.sourcePosition).index + C.length ∨
      (component.outputPosition hfull C.sourcePosition).index =
        (component.outputPosition hfull C.targetPosition).index + C.length := by
  obtain ⟨j₀, jₙ, hj₀, hjₙ, hslope⟩ :=
    hfull.exists_endpointPositions component
  have hj₀eq := component.outputPosition_eq_of_support
    hfull C.sourcePosition j₀ hj₀
  have hjₙeq := component.outputPosition_eq_of_support
    hfull C.targetPosition jₙ hjₙ
  rw [hj₀eq, hjₙeq]
  exact hslope

/-- If the target word is strictly longer, a full-source-support component
occupies a proper target interval, with the unused side recorded together
with its orientation. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.outputPosition_properInterval
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hlength : C.length < D.length) :
    ((component.outputPosition hfull C.targetPosition).index =
          (component.outputPosition hfull C.sourcePosition).index + C.length ∧
        (0 < (component.outputPosition hfull C.sourcePosition).index ∨
          (component.outputPosition hfull C.targetPosition).index < D.length)) ∨
      ((component.outputPosition hfull C.sourcePosition).index =
          (component.outputPosition hfull C.targetPosition).index + C.length ∧
        (0 < (component.outputPosition hfull C.targetPosition).index ∨
          (component.outputPosition hfull C.sourcePosition).index < D.length)) := by
  have hsource := (component.outputPosition hfull C.sourcePosition).index_le
  have htarget := (component.outputPosition hfull C.targetPosition).index_le
  rcases hfull.outputPosition_endpointSlope component with hslope | hslope
  · left
    refine ⟨hslope, ?_⟩
    omega
  · right
    refine ⟨hslope, ?_⟩
    omega

/-- At the right end of an increasing full-target-support interval, an extra
source-word edge must point out of the interval. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.exists_outgoingAtTarget_of_forward_of_lt
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hforward : (component.inputPosition hfull D.targetPosition).index =
      (component.inputPosition hfull D.sourcePosition).index + D.length)
    (hlt : (component.inputPosition hfull D.targetPosition).index < C.length) :
    ∃ (y : Q) (j : C.PositionAt y) (a : D.target ⟶ y),
      j.index = (component.inputPosition hfull D.targetPosition).index + 1 ∧
        C.ArrowStep a (component.inputPosition hfull D.targetPosition) j := by
  let endpoint : C.Position :=
    ⟨D.target, component.inputPosition hfull D.targetPosition⟩
  rcases C.exists_arrowStep_of_index_lt_length endpoint hlt with
    houtgoing | hincoming
  · obtain ⟨y, j, a, hj, hstep⟩ := houtgoing
    exact ⟨y, j, a, hj, hstep⟩
  · obtain ⟨y, j, a, hj, hstep⟩ := hincoming
    change j.index =
      (component.inputPosition hfull D.targetPosition).index + 1 at hj
    have htargetSupport := component.inputPosition_support
      hfull D.targetPosition
    obtain ⟨i', _, hcontinued⟩ :=
      component.exists_support_of_inputArrowStep a j
        (component.inputPosition hfull D.targetPosition)
        D.targetPosition htargetSupport hstep
    have hsourceSupport := component.inputPosition_support
      hfull D.sourcePosition
    have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D)
        (⟨D.source, component.inputPosition hfull D.sourcePosition,
          D.sourcePosition⟩ : C.MorphismCoefficientPosition D)
        ⟨y, j, i'⟩ :=
      Relation.EqvGen.trans _ component.1.representative _
        hsourceSupport.symm hcontinued
    have hsourceLe :
        (component.inputPosition hfull D.sourcePosition).index ≤ j.index := by
      omega
    have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hsourceLe
    have hi' := i'.index_le
    change i'.index = 0 +
        (j.index - (component.inputPosition hfull D.sourcePosition).index) ∨
      0 = i'.index +
        (j.index - (component.inputPosition hfull D.sourcePosition).index)
      at hslope
    omega

/-- At the left end of an increasing full-target-support interval, an extra
source-word edge must point out of the interval. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.exists_outgoingAtSource_of_forward_of_pos
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hforward : (component.inputPosition hfull D.targetPosition).index =
      (component.inputPosition hfull D.sourcePosition).index + D.length)
    (hpos : 0 < (component.inputPosition hfull D.sourcePosition).index) :
    ∃ (x : Q) (j : C.PositionAt x) (a : D.source ⟶ x),
      j.index + 1 = (component.inputPosition hfull D.sourcePosition).index ∧
        C.ArrowStep a (component.inputPosition hfull D.sourcePosition) j := by
  let endpoint : C.Position :=
    ⟨D.source, component.inputPosition hfull D.sourcePosition⟩
  rcases C.exists_arrowStep_of_index_pos endpoint hpos with
    hincoming | houtgoing
  · obtain ⟨x, j, a, hj, hstep⟩ := hincoming
    change j.index + 1 =
      (component.inputPosition hfull D.sourcePosition).index at hj
    have hsourceSupport := component.inputPosition_support
      hfull D.sourcePosition
    obtain ⟨i', _, hcontinued⟩ :=
      component.exists_support_of_inputArrowStep a j
        (component.inputPosition hfull D.sourcePosition)
        D.sourcePosition hsourceSupport hstep
    have htargetSupport := component.inputPosition_support
      hfull D.targetPosition
    have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D)
        (⟨x, j, i'⟩ : C.MorphismCoefficientPosition D)
        ⟨D.target, component.inputPosition hfull D.targetPosition,
          D.targetPosition⟩ :=
      Relation.EqvGen.trans _ component.1.representative _
        hcontinued.symm htargetSupport
    have hjLe : j.index ≤
        (component.inputPosition hfull D.targetPosition).index := by
      omega
    have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hjLe
    have hi' := i'.index_le
    change D.length = i'.index +
        ((component.inputPosition hfull D.targetPosition).index - j.index) ∨
      i'.index = D.length +
        ((component.inputPosition hfull D.targetPosition).index - j.index)
      at hslope
    omega
  · obtain ⟨x, j, a, hj, hstep⟩ := houtgoing
    exact ⟨x, j, a, hj, hstep⟩

/-- At the left end of a decreasing full-target-support interval, an extra
source-word edge must point out of the interval. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.exists_outgoingAtTarget_of_reverse_of_pos
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hreverse : (component.inputPosition hfull D.sourcePosition).index =
      (component.inputPosition hfull D.targetPosition).index + D.length)
    (hpos : 0 < (component.inputPosition hfull D.targetPosition).index) :
    ∃ (x : Q) (j : C.PositionAt x) (a : D.target ⟶ x),
      j.index + 1 = (component.inputPosition hfull D.targetPosition).index ∧
        C.ArrowStep a (component.inputPosition hfull D.targetPosition) j := by
  let endpoint : C.Position :=
    ⟨D.target, component.inputPosition hfull D.targetPosition⟩
  rcases C.exists_arrowStep_of_index_pos endpoint hpos with
    hincoming | houtgoing
  · obtain ⟨x, j, a, hj, hstep⟩ := hincoming
    change j.index + 1 =
      (component.inputPosition hfull D.targetPosition).index at hj
    have htargetSupport := component.inputPosition_support
      hfull D.targetPosition
    obtain ⟨i', _, hcontinued⟩ :=
      component.exists_support_of_inputArrowStep a j
        (component.inputPosition hfull D.targetPosition)
        D.targetPosition htargetSupport hstep
    have hsourceSupport := component.inputPosition_support
      hfull D.sourcePosition
    have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D)
        (⟨x, j, i'⟩ : C.MorphismCoefficientPosition D)
        ⟨D.source, component.inputPosition hfull D.sourcePosition,
          D.sourcePosition⟩ :=
      Relation.EqvGen.trans _ component.1.representative _
        hcontinued.symm hsourceSupport
    have hjLe : j.index ≤
        (component.inputPosition hfull D.sourcePosition).index := by
      omega
    have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hjLe
    have hi' := i'.index_le
    change 0 = i'.index +
        ((component.inputPosition hfull D.sourcePosition).index - j.index) ∨
      i'.index = 0 +
        ((component.inputPosition hfull D.sourcePosition).index - j.index)
      at hslope
    omega
  · obtain ⟨x, j, a, hj, hstep⟩ := houtgoing
    exact ⟨x, j, a, hj, hstep⟩

/-- At the right end of a decreasing full-target-support interval, an extra
source-word edge must point out of the interval. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.exists_outgoingAtSource_of_reverse_of_lt
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hreverse : (component.inputPosition hfull D.sourcePosition).index =
      (component.inputPosition hfull D.targetPosition).index + D.length)
    (hlt : (component.inputPosition hfull D.sourcePosition).index < C.length) :
    ∃ (y : Q) (j : C.PositionAt y) (a : D.source ⟶ y),
      j.index = (component.inputPosition hfull D.sourcePosition).index + 1 ∧
        C.ArrowStep a (component.inputPosition hfull D.sourcePosition) j := by
  let endpoint : C.Position :=
    ⟨D.source, component.inputPosition hfull D.sourcePosition⟩
  rcases C.exists_arrowStep_of_index_lt_length endpoint hlt with
    houtgoing | hincoming
  · obtain ⟨y, j, a, hj, hstep⟩ := houtgoing
    exact ⟨y, j, a, hj, hstep⟩
  · obtain ⟨y, j, a, hj, hstep⟩ := hincoming
    change j.index =
      (component.inputPosition hfull D.sourcePosition).index + 1 at hj
    have hsourceSupport := component.inputPosition_support
      hfull D.sourcePosition
    obtain ⟨i', _, hcontinued⟩ :=
      component.exists_support_of_inputArrowStep a j
        (component.inputPosition hfull D.sourcePosition)
        D.sourcePosition hsourceSupport hstep
    have htargetSupport := component.inputPosition_support
      hfull D.targetPosition
    have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D)
        (⟨D.target, component.inputPosition hfull D.targetPosition,
          D.targetPosition⟩ : C.MorphismCoefficientPosition D)
        ⟨y, j, i'⟩ :=
      Relation.EqvGen.trans _ component.1.representative _
        htargetSupport.symm hcontinued
    have htargetLe :
        (component.inputPosition hfull D.targetPosition).index ≤ j.index := by
      omega
    have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent htargetLe
    have hi' := i'.index_le
    change i'.index = D.length +
        (j.index - (component.inputPosition hfull D.targetPosition).index) ∨
      D.length = i'.index +
        (j.index - (component.inputPosition hfull D.targetPosition).index)
      at hslope
    omega

/-- A proper full-target-support interval has an outward source-word arrow at
one of its four oriented boundaries. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.exists_outgoingBoundary_of_length_lt
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hlength : D.length < C.length) :
    ((component.inputPosition hfull D.targetPosition).index =
        (component.inputPosition hfull D.sourcePosition).index + D.length ∧
      ((∃ (x : Q) (j : C.PositionAt x) (a : D.source ⟶ x),
          j.index + 1 =
            (component.inputPosition hfull D.sourcePosition).index ∧
          C.ArrowStep a (component.inputPosition hfull D.sourcePosition) j) ∨
        (∃ (y : Q) (j : C.PositionAt y) (a : D.target ⟶ y),
          j.index =
            (component.inputPosition hfull D.targetPosition).index + 1 ∧
          C.ArrowStep a (component.inputPosition hfull D.targetPosition) j))) ∨
    ((component.inputPosition hfull D.sourcePosition).index =
        (component.inputPosition hfull D.targetPosition).index + D.length ∧
      ((∃ (x : Q) (j : C.PositionAt x) (a : D.target ⟶ x),
          j.index + 1 =
            (component.inputPosition hfull D.targetPosition).index ∧
          C.ArrowStep a (component.inputPosition hfull D.targetPosition) j) ∨
        (∃ (y : Q) (j : C.PositionAt y) (a : D.source ⟶ y),
          j.index =
            (component.inputPosition hfull D.sourcePosition).index + 1 ∧
          C.ArrowStep a (component.inputPosition hfull D.sourcePosition) j))) := by
  rcases hfull.inputPosition_properInterval component hlength with
    ⟨hforward, hleft | hright⟩ | ⟨hreverse, hleft | hright⟩
  · exact Or.inl ⟨hforward, Or.inl
      (hfull.exists_outgoingAtSource_of_forward_of_pos
        component hforward hleft)⟩
  · exact Or.inl ⟨hforward, Or.inr
      (hfull.exists_outgoingAtTarget_of_forward_of_lt
        component hforward hright)⟩
  · exact Or.inr ⟨hreverse, Or.inl
      (hfull.exists_outgoingAtTarget_of_reverse_of_pos
        component hreverse hleft)⟩
  · exact Or.inr ⟨hreverse, Or.inr
      (hfull.exists_outgoingAtSource_of_reverse_of_lt
        component hreverse hright)⟩

/-- At the right end of an increasing full-source-support interval, an extra
target-word edge must point into the interval. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.exists_incomingAtTarget_of_forward_of_lt
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hforward : (component.outputPosition hfull C.targetPosition).index =
      (component.outputPosition hfull C.sourcePosition).index + C.length)
    (hlt : (component.outputPosition hfull C.targetPosition).index < D.length) :
    ∃ (y : Q) (j : D.PositionAt y) (a : y ⟶ C.target),
      j.index = (component.outputPosition hfull C.targetPosition).index + 1 ∧
        D.ArrowStep a j (component.outputPosition hfull C.targetPosition) := by
  let endpoint : D.Position :=
    ⟨C.target, component.outputPosition hfull C.targetPosition⟩
  rcases D.exists_arrowStep_of_index_lt_length endpoint hlt with
    houtgoing | hincoming
  · obtain ⟨y, j, a, hj, hstep⟩ := houtgoing
    change j.index =
      (component.outputPosition hfull C.targetPosition).index + 1 at hj
    have htargetSupport := component.outputPosition_support
      hfull C.targetPosition
    obtain ⟨i, _, hcontinued⟩ :=
      component.exists_support_of_outputArrowStep a C.targetPosition
        (component.outputPosition hfull C.targetPosition) j
        htargetSupport hstep
    have hsourceSupport := component.outputPosition_support
      hfull C.sourcePosition
    have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D)
        (⟨C.source, C.sourcePosition,
          component.outputPosition hfull C.sourcePosition⟩ :
          C.MorphismCoefficientPosition D)
        ⟨y, i, j⟩ :=
      Relation.EqvGen.trans _ component.1.representative _
        hsourceSupport.symm hcontinued
    have hinputLe : C.sourcePosition.index ≤ i.index := by simp
    have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hinputLe
    have hi := i.index_le
    change j.index =
        (component.outputPosition hfull C.sourcePosition).index + i.index ∨
      (component.outputPosition hfull C.sourcePosition).index =
        j.index + i.index at hslope
    omega
  · obtain ⟨y, j, a, hj, hstep⟩ := hincoming
    exact ⟨y, j, a, hj, hstep⟩

/-- At the left end of an increasing full-source-support interval, an extra
target-word edge must point into the interval. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.exists_incomingAtSource_of_forward_of_pos
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hforward : (component.outputPosition hfull C.targetPosition).index =
      (component.outputPosition hfull C.sourcePosition).index + C.length)
    (hpos : 0 < (component.outputPosition hfull C.sourcePosition).index) :
    ∃ (x : Q) (j : D.PositionAt x) (a : x ⟶ C.source),
      j.index + 1 = (component.outputPosition hfull C.sourcePosition).index ∧
        D.ArrowStep a j (component.outputPosition hfull C.sourcePosition) := by
  let endpoint : D.Position :=
    ⟨C.source, component.outputPosition hfull C.sourcePosition⟩
  rcases D.exists_arrowStep_of_index_pos endpoint hpos with
    hincoming | houtgoing
  · obtain ⟨x, j, a, hj, hstep⟩ := hincoming
    exact ⟨x, j, a, hj, hstep⟩
  · obtain ⟨x, j, a, hj, hstep⟩ := houtgoing
    change j.index + 1 =
      (component.outputPosition hfull C.sourcePosition).index at hj
    have hsourceSupport := component.outputPosition_support
      hfull C.sourcePosition
    obtain ⟨i, _, hcontinued⟩ :=
      component.exists_support_of_outputArrowStep a C.sourcePosition
        (component.outputPosition hfull C.sourcePosition) j
        hsourceSupport hstep
    have htargetSupport := component.outputPosition_support
      hfull C.targetPosition
    have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D)
        (⟨x, i, j⟩ : C.MorphismCoefficientPosition D)
        ⟨C.target, C.targetPosition,
          component.outputPosition hfull C.targetPosition⟩ :=
      Relation.EqvGen.trans _ component.1.representative _
        hcontinued.symm htargetSupport
    have hinputLe : i.index ≤ C.targetPosition.index := i.index_le
    have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hinputLe
    change (component.outputPosition hfull C.targetPosition).index =
        j.index + (C.length - i.index) ∨
      j.index = (component.outputPosition hfull C.targetPosition).index +
        (C.length - i.index) at hslope
    omega

/-- At the left end of a decreasing full-source-support interval, an extra
target-word edge must point into the interval. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.exists_incomingAtTarget_of_reverse_of_pos
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hreverse : (component.outputPosition hfull C.sourcePosition).index =
      (component.outputPosition hfull C.targetPosition).index + C.length)
    (hpos : 0 < (component.outputPosition hfull C.targetPosition).index) :
    ∃ (x : Q) (j : D.PositionAt x) (a : x ⟶ C.target),
      j.index + 1 = (component.outputPosition hfull C.targetPosition).index ∧
        D.ArrowStep a j (component.outputPosition hfull C.targetPosition) := by
  let endpoint : D.Position :=
    ⟨C.target, component.outputPosition hfull C.targetPosition⟩
  rcases D.exists_arrowStep_of_index_pos endpoint hpos with
    hincoming | houtgoing
  · obtain ⟨x, j, a, hj, hstep⟩ := hincoming
    exact ⟨x, j, a, hj, hstep⟩
  · obtain ⟨x, j, a, hj, hstep⟩ := houtgoing
    change j.index + 1 =
      (component.outputPosition hfull C.targetPosition).index at hj
    have htargetSupport := component.outputPosition_support
      hfull C.targetPosition
    obtain ⟨i, _, hcontinued⟩ :=
      component.exists_support_of_outputArrowStep a C.targetPosition
        (component.outputPosition hfull C.targetPosition) j
        htargetSupport hstep
    have hsourceSupport := component.outputPosition_support
      hfull C.sourcePosition
    have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D)
        (⟨C.source, C.sourcePosition,
          component.outputPosition hfull C.sourcePosition⟩ :
          C.MorphismCoefficientPosition D)
        ⟨x, i, j⟩ :=
      Relation.EqvGen.trans _ component.1.representative _
        hsourceSupport.symm hcontinued
    have hinputLe : C.sourcePosition.index ≤ i.index := by simp
    have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hinputLe
    have hi := i.index_le
    change j.index =
        (component.outputPosition hfull C.sourcePosition).index + i.index ∨
      (component.outputPosition hfull C.sourcePosition).index =
        j.index + i.index at hslope
    omega

/-- At the right end of a decreasing full-source-support interval, an extra
target-word edge must point into the interval. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.exists_incomingAtSource_of_reverse_of_lt
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hreverse : (component.outputPosition hfull C.sourcePosition).index =
      (component.outputPosition hfull C.targetPosition).index + C.length)
    (hlt : (component.outputPosition hfull C.sourcePosition).index < D.length) :
    ∃ (y : Q) (j : D.PositionAt y) (a : y ⟶ C.source),
      j.index = (component.outputPosition hfull C.sourcePosition).index + 1 ∧
        D.ArrowStep a j (component.outputPosition hfull C.sourcePosition) := by
  let endpoint : D.Position :=
    ⟨C.source, component.outputPosition hfull C.sourcePosition⟩
  rcases D.exists_arrowStep_of_index_lt_length endpoint hlt with
    houtgoing | hincoming
  · obtain ⟨y, j, a, hj, hstep⟩ := houtgoing
    change j.index =
      (component.outputPosition hfull C.sourcePosition).index + 1 at hj
    have hsourceSupport := component.outputPosition_support
      hfull C.sourcePosition
    obtain ⟨i, _, hcontinued⟩ :=
      component.exists_support_of_outputArrowStep a C.sourcePosition
        (component.outputPosition hfull C.sourcePosition) j
        hsourceSupport hstep
    have htargetSupport := component.outputPosition_support
      hfull C.targetPosition
    have hcomponent : Relation.EqvGen (C.MorphismCoefficientStep D)
        (⟨y, i, j⟩ : C.MorphismCoefficientPosition D)
        ⟨C.target, C.targetPosition,
          component.outputPosition hfull C.targetPosition⟩ :=
      Relation.EqvGen.trans _ component.1.representative _
        hcontinued.symm htargetSupport
    have hinputLe : i.index ≤ C.targetPosition.index := i.index_le
    have hslope := C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hcomponent hinputLe
    change (component.outputPosition hfull C.targetPosition).index =
        j.index + (C.length - i.index) ∨
      j.index = (component.outputPosition hfull C.targetPosition).index +
        (C.length - i.index) at hslope
    omega
  · obtain ⟨y, j, a, hj, hstep⟩ := hincoming
    exact ⟨y, j, a, hj, hstep⟩

/-- A proper full-source-support interval has an inward target-word arrow at
one of its four oriented boundaries. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.exists_incomingBoundary_of_length_lt
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hlength : C.length < D.length) :
    ((component.outputPosition hfull C.targetPosition).index =
        (component.outputPosition hfull C.sourcePosition).index + C.length ∧
      ((∃ (x : Q) (j : D.PositionAt x) (a : x ⟶ C.source),
          j.index + 1 =
            (component.outputPosition hfull C.sourcePosition).index ∧
          D.ArrowStep a j (component.outputPosition hfull C.sourcePosition)) ∨
        (∃ (y : Q) (j : D.PositionAt y) (a : y ⟶ C.target),
          j.index =
            (component.outputPosition hfull C.targetPosition).index + 1 ∧
          D.ArrowStep a j (component.outputPosition hfull C.targetPosition)))) ∨
    ((component.outputPosition hfull C.sourcePosition).index =
        (component.outputPosition hfull C.targetPosition).index + C.length ∧
      ((∃ (x : Q) (j : D.PositionAt x) (a : x ⟶ C.target),
          j.index + 1 =
            (component.outputPosition hfull C.targetPosition).index ∧
          D.ArrowStep a j (component.outputPosition hfull C.targetPosition)) ∨
        (∃ (y : Q) (j : D.PositionAt y) (a : y ⟶ C.source),
          j.index =
            (component.outputPosition hfull C.sourcePosition).index + 1 ∧
          D.ArrowStep a j (component.outputPosition hfull C.sourcePosition)))) := by
  rcases hfull.outputPosition_properInterval component hlength with
    ⟨hforward, hleft | hright⟩ | ⟨hreverse, hleft | hright⟩
  · exact Or.inl ⟨hforward, Or.inl
      (hfull.exists_incomingAtSource_of_forward_of_pos
        component hforward hleft)⟩
  · exact Or.inl ⟨hforward, Or.inr
      (hfull.exists_incomingAtTarget_of_forward_of_lt
        component hforward hright)⟩
  · exact Or.inr ⟨hreverse, Or.inl
      (hfull.exists_incomingAtTarget_of_reverse_of_pos
        component hreverse hleft)⟩
  · exact Or.inr ⟨hreverse, Or.inr
      (hfull.exists_incomingAtSource_of_reverse_of_lt
        component hreverse hright)⟩

end MagnitudeConjecture.BoundQuiver.StringWord.Word
