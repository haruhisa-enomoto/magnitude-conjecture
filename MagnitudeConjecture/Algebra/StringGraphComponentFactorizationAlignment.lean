import MagnitudeConjecture.Algebra.StringGraphComponentFullSupport

/-!
# Aligned positions in string graph-component factorizations

When a graph-component product is nonzero on an output component, a full
support hypothesis identifies the outside position before the intermediate
position is extracted.  This strengthens mere support transfer to a
pointwise alignment of the two selected factor components along the entire
output interval.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Full target support of the output component aligns both selected factor
components above every target position. -/
theorem BoundaryFreeMorphismCoefficientComponent.exists_intermediate_of_comp_of_fullOutputSupport
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (output : C.BoundaryFreeMorphismCoefficientComponent E)
    (houtput : output.HasFullOutputSupport)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E)
    (hne : C.morphismCoefficientAt E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      output.1.representative ≠ 0)
    {x : Q} (l : E.PositionAt x) :
    ∃ j : D.PositionAt x,
      Relation.EqvGen (C.MorphismCoefficientStep D)
          first.1.representative
          ⟨x, output.inputPosition houtput l, j⟩ ∧
        Relation.EqvGen (D.MorphismCoefficientStep E)
          second.1.representative ⟨x, j, l⟩ := by
  have hsupport := output.inputPosition_support houtput l
  have hpne : C.morphismCoefficientAt E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      ⟨x, output.inputPosition houtput l, l⟩ ≠ 0 := by
    have heq := C.morphismCoefficientAt_eq_of_eqvGen E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      hsupport
    rw [heq] at hne
    exact hne
  exact C.exists_intermediate_of_componentMaps_comp_coefficient_ne_zero
    D E hC hD hE first second
      ⟨x, output.inputPosition houtput l, l⟩ hpne

/-- Full source support of the output component aligns both selected factor
components below every source position. -/
theorem BoundaryFreeMorphismCoefficientComponent.exists_intermediate_of_comp_of_fullInputSupport
    (C D E : Word R)
    (hC : IsMonomial R) (hD : IsMonomial R) (hE : IsMonomial R)
    (output : C.BoundaryFreeMorphismCoefficientComponent E)
    (hinput : output.HasFullInputSupport)
    (first : C.BoundaryFreeMorphismCoefficientComponent D)
    (second : D.BoundaryFreeMorphismCoefficientComponent E)
    (hne : C.morphismCoefficientAt E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      output.1.representative ≠ 0)
    {x : Q} (i : C.PositionAt x) :
    ∃ j : D.PositionAt x,
      Relation.EqvGen (C.MorphismCoefficientStep D)
          first.1.representative ⟨x, i, j⟩ ∧
        Relation.EqvGen (D.MorphismCoefficientStep E)
          second.1.representative
          ⟨x, j, output.outputPosition hinput i⟩ := by
  have hsupport := output.outputPosition_support hinput i
  have hpne : C.morphismCoefficientAt E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      ⟨x, i, output.outputPosition hinput i⟩ ≠ 0 := by
    have heq := C.morphismCoefficientAt_eq_of_eqvGen E hC hE
      (C.boundaryFreeMorphismCoefficientComponentMap D hC hD first ≫
        D.boundaryFreeMorphismCoefficientComponentMap E hD hE second)
      hsupport
    rw [heq] at hne
    exact hne
  exact C.exists_intermediate_of_componentMaps_comp_coefficient_ne_zero
    D E hC hD hE first second
      ⟨x, i, output.outputPosition hinput i⟩ hpne

/-- The input selected by the right-boundary projection component is the
inherited position in the extended word. -/
theorem PositiveBoundaryExtension.rightModuleProjectionComponent_inputPosition_eq_position
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) :
    (extension.rightModuleProjectionComponent hmono).inputPosition
        (extension.rightModuleProjectionComponent_hasFullOutputSupport hmono)
        i =
      extension.toRightExtension.position i := by
  exact (extension.rightModuleProjectionComponent hmono).inputPosition_eq_of_support
    (extension.rightModuleProjectionComponent_hasFullOutputSupport hmono) i
    (extension.toRightExtension.position i)
    (extension.rightModuleProjectionComponent_position_support hmono i)

/-- The output selected by the right-boundary inclusion component is the
inherited position in the extended word. -/
theorem NegativeBoundaryExtension.rightModuleInclusionComponent_outputPosition_eq_position
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) :
    (extension.rightModuleInclusionComponent hmono).outputPosition
        (extension.rightModuleInclusionComponent_hasFullInputSupport hmono)
        i =
      extension.toRightExtension.position i := by
  exact (extension.rightModuleInclusionComponent hmono).outputPosition_eq_of_support
    (extension.rightModuleInclusionComponent_hasFullInputSupport hmono) i
    (extension.toRightExtension.position i)
    (extension.rightModuleInclusionComponent_position_support hmono i)

/-- The input selected by the positive left-boundary projection component is
the inherited position in the extended word. -/
theorem LeftPositiveBoundaryExtension.moduleMapComponent_inputPosition_eq_position
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) :
    (extension.moduleMapComponent hmono).inputPosition
        (extension.moduleMapComponent_hasFullOutputSupport hmono) i =
      extension.position i := by
  exact (extension.moduleMapComponent hmono).inputPosition_eq_of_support
    (extension.moduleMapComponent_hasFullOutputSupport hmono) i
    (extension.position i)
    (extension.moduleMapComponent_position_support hmono i)

/-- The output selected by the negative left-boundary inclusion component is
the inherited position in the extended word. -/
theorem LeftNegativeBoundaryExtension.moduleMapComponent_outputPosition_eq_position
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) :
    (extension.moduleMapComponent hmono).outputPosition
        (extension.moduleMapComponent_hasFullInputSupport hmono) i =
      extension.position i := by
  exact (extension.moduleMapComponent hmono).outputPosition_eq_of_support
    (extension.moduleMapComponent_hasFullInputSupport hmono) i
    (extension.position i)
    (extension.moduleMapComponent_position_support hmono i)

/-- A nonzero component product over a right hook aligns both factor
components at every inherited position of the old word. -/
theorem HookExtension.exists_intermediate_of_component_pair
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (first : D.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent C)
    (hne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0)
    {x : Q} (i : C.PositionAt x) :
    ∃ j : M.PositionAt x,
      Relation.EqvGen (D.MorphismCoefficientStep M)
          first.1.representative
          ⟨x, hook.toPositiveBoundaryExtension.toRightExtension.position i, j⟩ ∧
        Relation.EqvGen (M.MorphismCoefficientStep C)
          second.1.representative ⟨x, j, i⟩ := by
  obtain ⟨j, hfirst, hsecond⟩ :=
    (hook.moduleMapComponent hmono).exists_intermediate_of_comp_of_fullOutputSupport
      D M C hmono hmono hmono
      (hook.moduleMapComponent_hasFullOutputSupport hmono)
      first second hne i
  refine ⟨j, ?_, hsecond⟩
  simpa only [HookExtension.moduleMapComponent,
    PositiveBoundaryExtension.rightModuleProjectionComponent_inputPosition_eq_position]
    using hfirst

/-- A nonzero component product over a right cohook aligns both factor
components at every inherited position of the old word. -/
theorem CohookExtension.exists_intermediate_of_component_pair
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent D)
    (hne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0)
    {x : Q} (i : C.PositionAt x) :
    ∃ j : M.PositionAt x,
      Relation.EqvGen (C.MorphismCoefficientStep M)
          first.1.representative ⟨x, i, j⟩ ∧
        Relation.EqvGen (M.MorphismCoefficientStep D)
          second.1.representative
          ⟨x, j, cohook.toNegativeBoundaryExtension.toRightExtension.position i⟩ := by
  obtain ⟨j, hfirst, hsecond⟩ :=
    (cohook.moduleMapComponent hmono).exists_intermediate_of_comp_of_fullInputSupport
      C M D hmono hmono hmono
      (cohook.moduleMapComponent_hasFullInputSupport hmono)
      first second hne i
  refine ⟨j, hfirst, ?_⟩
  simpa only [CohookExtension.moduleMapComponent,
    NegativeBoundaryExtension.rightModuleInclusionComponent_outputPosition_eq_position]
    using hsecond

/-- A nonzero component product over a left hook aligns both factor
components at every inherited position of the old word. -/
theorem LeftHookExtension.exists_intermediate_of_component_pair
    {C M : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R)
    (first : hook.result.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent C)
    (hne : hook.result.morphismCoefficientAt C hmono hmono
      (hook.result.boundaryFreeMorphismCoefficientComponentMap M
          hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0)
    {x : Q} (i : C.PositionAt x) :
    ∃ j : M.PositionAt x,
      Relation.EqvGen (hook.result.MorphismCoefficientStep M)
          first.1.representative
          ⟨x, hook.toLeftPositiveBoundaryExtension.position i, j⟩ ∧
        Relation.EqvGen (M.MorphismCoefficientStep C)
          second.1.representative ⟨x, j, i⟩ := by
  obtain ⟨j, hfirst, hsecond⟩ :=
    (hook.moduleMapComponent hmono).exists_intermediate_of_comp_of_fullOutputSupport
      hook.result M C hmono hmono hmono
      (hook.moduleMapComponent_hasFullOutputSupport hmono)
      first second hne i
  refine ⟨j, ?_, hsecond⟩
  have hinherited : Relation.EqvGen
      (hook.result.MorphismCoefficientStep C)
      (hook.moduleMapComponent hmono).1.representative
      ⟨x, hook.toLeftPositiveBoundaryExtension.position i, i⟩ := by
    simpa only [LeftHookExtension.moduleMapComponent,
      LeftHookExtension.result,
      LeftHookExtension.toLeftPositiveBoundaryExtension,
      LeftPositiveBoundaryExtension.result] using
      hook.toLeftPositiveBoundaryExtension.moduleMapComponent_position_support
        hmono i
  have hposition := (hook.moduleMapComponent hmono).inputPosition_eq_of_support
    (hook.moduleMapComponent_hasFullOutputSupport hmono) i
    (hook.toLeftPositiveBoundaryExtension.position i) hinherited
  rw [hposition] at hfirst
  exact hfirst

/-- A nonzero component product over a left cohook aligns both factor
components at every inherited position of the old word. -/
theorem LeftCohookExtension.exists_intermediate_of_component_pair
    {C M : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent cohook.result)
    (hne : C.morphismCoefficientAt cohook.result hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap cohook.result
          hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0)
    {x : Q} (i : C.PositionAt x) :
    ∃ j : M.PositionAt x,
      Relation.EqvGen (C.MorphismCoefficientStep M)
          first.1.representative ⟨x, i, j⟩ ∧
        Relation.EqvGen (M.MorphismCoefficientStep cohook.result)
          second.1.representative
          ⟨x, j, cohook.toLeftNegativeBoundaryExtension.position i⟩ := by
  obtain ⟨j, hfirst, hsecond⟩ :=
    (cohook.moduleMapComponent hmono).exists_intermediate_of_comp_of_fullInputSupport
      C M cohook.result hmono hmono hmono
      (cohook.moduleMapComponent_hasFullInputSupport hmono)
      first second hne i
  refine ⟨j, hfirst, ?_⟩
  have hinherited : Relation.EqvGen
      (C.MorphismCoefficientStep cohook.result)
      (cohook.moduleMapComponent hmono).1.representative
      ⟨x, i, cohook.toLeftNegativeBoundaryExtension.position i⟩ := by
    simpa only [LeftCohookExtension.moduleMapComponent,
      LeftCohookExtension.result,
      LeftCohookExtension.toLeftNegativeBoundaryExtension,
      LeftNegativeBoundaryExtension.result] using
      cohook.toLeftNegativeBoundaryExtension.moduleMapComponent_position_support
        hmono i
  have hposition := (cohook.moduleMapComponent hmono).outputPosition_eq_of_support
    (cohook.moduleMapComponent_hasFullInputSupport hmono) i
    (cohook.toLeftNegativeBoundaryExtension.position i) hinherited
  rw [hposition] at hsecond
  exact hsecond

end MagnitudeConjecture.BoundQuiver.StringWord.Word
