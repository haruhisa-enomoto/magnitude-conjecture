import MagnitudeConjecture.Algebra.StringGraphComponentPathTransfer

/-!
# Maximality obstructions for right-hook and right-cohook factorizations

A selected full-source-support component through a word longer than the
complete hook must have an incoming boundary edge.  At the hook endpoint,
path transfer contradicts maximality directly.  At the inherited source
endpoint, factorization alignment transfers that edge through the second
component and forces the first component to occupy two incompatible adjacent
positions.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Transport an arrow step when its target is identified as a total word
position.  Packaging the endpoint equality this way keeps dependent endpoint
casts out of the factorization argument. -/
private theorem exists_arrowStep_of_targetPosition_eq
    {C : Word R} {x y z : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hstep : C.ArrowStep a i j) (j' : C.PositionAt z)
    (hposition : (⟨y, j⟩ : C.Position) = ⟨z, j'⟩) :
    ∃ a' : x ⟶ z, C.ArrowStep a' i j' := by
  cases hposition
  exact ⟨a, hstep⟩

/-- Transport an arrow step when its source is identified as a total word
position. -/
private theorem exists_arrowStep_of_sourcePosition_eq
    {C : Word R} {x y z : Q} (a : y ⟶ x)
    (i : C.PositionAt y) (j : C.PositionAt x)
    (hstep : C.ArrowStep a i j) (i' : C.PositionAt z)
    (hposition : (⟨y, i⟩ : C.Position) = ⟨z, i'⟩) :
    ∃ a' : z ⟶ x, C.ArrowStep a' i' j := by
  cases hposition
  exact ⟨a, hstep⟩

/-- In the forward orientation, an unused edge immediately before the
inherited source endpoint is incompatible with the aligned second factor. -/
private theorem HookExtension.false_of_forward_source_boundary
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (first : D.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent C)
    (houtput : second.HasFullOutputSupport)
    (hinput : first.HasFullInputSupport)
    (hne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0)
    (hforward : (first.outputPosition hinput D.targetPosition).index =
      (first.outputPosition hinput D.sourcePosition).index + D.length)
    {x : Q} (j : M.PositionAt x) (a : x ⟶ D.source)
    (hj : j.index + 1 =
      (first.outputPosition hinput D.sourcePosition).index)
    (hstep : M.ArrowStep a j
      (first.outputPosition hinput D.sourcePosition)) : False := by
  have hsource := first.outputPosition_support hinput D.sourcePosition
  have haligned := hook.firstComponent_support_inputPosition
    hmono first second houtput hne C.sourcePosition
  have hcomponent : Relation.EqvGen (D.MorphismCoefficientStep M)
      (⟨D.source, D.sourcePosition,
        first.outputPosition hinput D.sourcePosition⟩ :
        D.MorphismCoefficientPosition M)
      ⟨C.source,
        hook.toPositiveBoundaryExtension.toRightExtension.position
          C.sourcePosition,
        second.inputPosition houtput C.sourcePosition⟩ :=
    Relation.EqvGen.trans _ first.1.representative _
      hsource.symm haligned
  have hpairs := D.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq
    M hcomponent (by
      change D.sourcePosition.index =
        (hook.toPositiveBoundaryExtension.toRightExtension.position
          C.sourcePosition).index
      simp)
  have houtputPair := congrArg MorphismCoefficientPosition.outputPosition hpairs
  obtain ⟨aC, hstepC⟩ := exists_arrowStep_of_targetPosition_eq
    a j (first.outputPosition hinput D.sourcePosition) hstep
      (second.inputPosition houtput C.sourcePosition) houtputPair
  obtain ⟨cpos, hcstep, hcontinued⟩ :=
    second.exists_support_of_inputArrowStep aC j
      (second.inputPosition houtput C.sourcePosition) C.sourcePosition
      (second.inputPosition_support houtput C.sourcePosition) hstepC
  have hcstepIndex := hcstep.index
  simp only [sourcePosition_index] at hcstepIndex
  have hcindex : cpos.index = 1 := by omega
  have hselectedSecond := second.inputPosition_eq_of_support
    houtput cpos j hcontinued
  have hfirstC := hook.firstComponent_support_inputPosition
    hmono first second houtput hne cpos
  rw [hselectedSecond] at hfirstC
  have hselectedFirst := first.outputPosition_eq_of_support hinput
    (hook.toPositiveBoundaryExtension.toRightExtension.position cpos)
    j hfirstC
  have hselectedFirstIndex := congrArg PositionAt.index hselectedFirst
  have hformula :=
    hinput.outputPosition_index_eq_source_add_of_forward
      first hforward
        (hook.toPositiveBoundaryExtension.toRightExtension.position cpos)
  simp only [RightExtension.position_index] at hformula
  omega

/-- In the reverse orientation, an unused edge immediately after the
inherited source endpoint is incompatible with the aligned second factor. -/
private theorem HookExtension.false_of_reverse_source_boundary
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (first : D.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent C)
    (houtput : second.HasFullOutputSupport)
    (hinput : first.HasFullInputSupport)
    (hne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0)
    (hreverse : (first.outputPosition hinput D.sourcePosition).index =
      (first.outputPosition hinput D.targetPosition).index + D.length)
    {x : Q} (j : M.PositionAt x) (a : x ⟶ D.source)
    (hj : j.index =
      (first.outputPosition hinput D.sourcePosition).index + 1)
    (hstep : M.ArrowStep a j
      (first.outputPosition hinput D.sourcePosition)) : False := by
  have hsource := first.outputPosition_support hinput D.sourcePosition
  have haligned := hook.firstComponent_support_inputPosition
    hmono first second houtput hne C.sourcePosition
  have hcomponent : Relation.EqvGen (D.MorphismCoefficientStep M)
      (⟨D.source, D.sourcePosition,
        first.outputPosition hinput D.sourcePosition⟩ :
        D.MorphismCoefficientPosition M)
      ⟨C.source,
        hook.toPositiveBoundaryExtension.toRightExtension.position
          C.sourcePosition,
        second.inputPosition houtput C.sourcePosition⟩ :=
    Relation.EqvGen.trans _ first.1.representative _
      hsource.symm haligned
  have hpairs := D.eq_of_morphismCoefficientStep_eqvGen_of_inputIndex_eq
    M hcomponent (by
      change D.sourcePosition.index =
        (hook.toPositiveBoundaryExtension.toRightExtension.position
          C.sourcePosition).index
      simp)
  have houtputPair := congrArg MorphismCoefficientPosition.outputPosition hpairs
  obtain ⟨aC, hstepC⟩ := exists_arrowStep_of_targetPosition_eq
    a j (first.outputPosition hinput D.sourcePosition) hstep
      (second.inputPosition houtput C.sourcePosition) houtputPair
  obtain ⟨cpos, hcstep, hcontinued⟩ :=
    second.exists_support_of_inputArrowStep aC j
      (second.inputPosition houtput C.sourcePosition) C.sourcePosition
      (second.inputPosition_support houtput C.sourcePosition) hstepC
  have hcstepIndex := hcstep.index
  simp only [sourcePosition_index] at hcstepIndex
  have hcindex : cpos.index = 1 := by omega
  have hselectedSecond := second.inputPosition_eq_of_support
    houtput cpos j hcontinued
  have hfirstC := hook.firstComponent_support_inputPosition
    hmono first second houtput hne cpos
  rw [hselectedSecond] at hfirstC
  have hselectedFirst := first.outputPosition_eq_of_support hinput
    (hook.toPositiveBoundaryExtension.toRightExtension.position cpos)
    j hfirstC
  have hselectedFirstIndex := congrArg PositionAt.index hselectedFirst
  have hformula :=
    hinput.outputPosition_index_add_eq_source_of_reverse
      first hreverse
        (hook.toPositiveBoundaryExtension.toRightExtension.position cpos)
  simp only [RightExtension.position_index] at hformula
  omega

/-- A component pair selected from a right-hook factorization cannot make the
first component cover the complete hook inside a strictly longer word. -/
theorem HookExtension.not_length_lt_intermediate_of_component_pair
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (first : D.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent C)
    (houtput : second.HasFullOutputSupport)
    (hinput : first.HasFullInputSupport)
    (hne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0)
    (hlength : D.length < M.length) : False := by
  rcases hinput.exists_incomingBoundary_of_length_lt first hlength with
    ⟨hforward, hleft | hright⟩ | ⟨hreverse, hleft | hright⟩
  · obtain ⟨x, j, a, hj, hstep⟩ := hleft
    exact hook.false_of_forward_source_boundary hmono first second
      houtput hinput hne hforward j a hj hstep
  · obtain ⟨y, j, a, hj, hstep⟩ := hright
    exact hook.maximal a
      (hinput.isString_comp_negative_of_forward_of_target_step
        first hforward a j hj hstep)
  · obtain ⟨x, j, a, hj, hstep⟩ := hleft
    exact hook.maximal a
      (hinput.isString_comp_negative_of_reverse_of_target_step
        first hreverse a j hj hstep)
  · obtain ⟨y, j, a, hj, hstep⟩ := hright
    exact hook.false_of_reverse_source_boundary hmono first second
      houtput hinput hne hreverse j a hj hstep

/-- A single component pair contributing nontrivially to the canonical
right-hook component already forces one of the two ambient factor maps to
split.  In particular, the composite of the ambient maps need not equal the
hook map; this is the form used after expanding a factorization through a
finite direct sum of string modules. -/
theorem HookExtension.isSplitMono_or_isSplitEpi_of_component_pair
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (f : D.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (first : D.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent C)
    (hfirstCoefficient : D.morphismCoefficientAt M hmono hmono f
      first.1.representative ≠ 0)
    (hsecondCoefficient : M.morphismCoefficientAt C hmono hmono g
      second.1.representative ≠ 0)
    (hne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsSplitMono f ∨ IsSplitEpi g := by
  by_cases hf : IsSplitMono f
  · exact Or.inl hf
  by_cases hg : IsSplitEpi g
  · exact Or.inr hg
  exfalso
  have houtput : second.HasFullOutputSupport :=
    BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.second_of_comp
      D M C hmono hmono hmono (hook.moduleMapComponent hmono)
        (hook.moduleMapComponent_hasFullOutputSupport hmono)
        first second hne
  have hC_le_M := houtput.target_length_le_source_length second
  have hC_lt_M : C.length < M.length := by
    apply lt_of_le_of_ne hC_le_M
    intro hlength
    have hinput : second.HasFullInputSupport :=
      houtput.hasFullInputSupport_of_length_eq second hlength.symm
    letI : IsIso g :=
      second.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
        hmono hmono hinput houtput g hsecondCoefficient
    exact hg inferInstance
  have hinput : first.HasFullInputSupport :=
    hook.firstComponent_hasFullInputSupport_of_length_lt
      hmono first second houtput hne hC_lt_M
  have hD_le_M := hinput.source_length_le_target_length first
  have hD_lt_M : D.length < M.length := by
    apply lt_of_le_of_ne hD_le_M
    intro hlength
    have hfullOutput : first.HasFullOutputSupport :=
      hinput.hasFullOutputSupport_of_length_eq first hlength
    letI : IsIso f :=
      first.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
        hmono hmono hinput hfullOutput f hfirstCoefficient
    exact hf inferInstance
  exact hook.not_length_lt_intermediate_of_component_pair
    hmono first second houtput hinput hne hD_lt_M

/-- Every factorization of the canonical right-hook projection through a
literal string module has a split first factor or a split second factor. -/
theorem HookExtension.isSplitMono_or_isSplitEpi_of_moduleMap_factorization
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (f : D.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  obtain ⟨first, second, hfirstCoefficient, hsecondCoefficient,
      hproduct, _⟩ :=
    hook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hproduct_ne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [hproduct]
    exact one_ne_zero
  exact hook.isSplitMono_or_isSplitEpi_of_component_pair
    hmono f g first second hfirstCoefficient hsecondCoefficient hproduct_ne

/-- In the forward orientation, an unused edge immediately before the
inherited source endpoint is incompatible with the aligned first factor. -/
private theorem CohookExtension.false_of_forward_source_boundary
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : first.HasFullInputSupport)
    (houtput : second.HasFullOutputSupport)
    (hne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0)
    (hforward : (second.inputPosition houtput D.targetPosition).index =
      (second.inputPosition houtput D.sourcePosition).index + D.length)
    {x : Q} (j : M.PositionAt x) (a : D.source ⟶ x)
    (hj : j.index + 1 =
      (second.inputPosition houtput D.sourcePosition).index)
    (hstep : M.ArrowStep a
      (second.inputPosition houtput D.sourcePosition) j) : False := by
  have hsource := second.inputPosition_support houtput D.sourcePosition
  have haligned := cohook.secondComponent_support_outputPosition
    hmono first second hinput hne C.sourcePosition
  have hcomponent : Relation.EqvGen (M.MorphismCoefficientStep D)
      (⟨D.source, second.inputPosition houtput D.sourcePosition,
        D.sourcePosition⟩ : M.MorphismCoefficientPosition D)
      ⟨C.source, first.outputPosition hinput C.sourcePosition,
        cohook.toNegativeBoundaryExtension.toRightExtension.position
          C.sourcePosition⟩ :=
    Relation.EqvGen.trans _ second.1.representative _
      hsource.symm haligned
  have hpairs := M.eq_of_morphismCoefficientStep_eqvGen_of_outputIndex_eq
    D hcomponent (by
      change D.sourcePosition.index =
        (cohook.toNegativeBoundaryExtension.toRightExtension.position
          C.sourcePosition).index
      simp)
  have hinputPair := congrArg MorphismCoefficientPosition.inputPosition hpairs
  obtain ⟨aC, hstepC⟩ := exists_arrowStep_of_sourcePosition_eq
    a (second.inputPosition houtput D.sourcePosition) j hstep
      (first.outputPosition hinput C.sourcePosition) hinputPair
  obtain ⟨cpos, hcstep, hcontinued⟩ :=
    first.exists_support_of_outputArrowStep aC C.sourcePosition
      (first.outputPosition hinput C.sourcePosition) j
      (first.outputPosition_support hinput C.sourcePosition) hstepC
  have hcstepIndex := hcstep.index
  simp only [sourcePosition_index] at hcstepIndex
  have hcindex : cpos.index = 1 := by omega
  have hselectedFirst := first.outputPosition_eq_of_support
    hinput cpos j hcontinued
  have hsecondC := cohook.secondComponent_support_outputPosition
    hmono first second hinput hne cpos
  rw [hselectedFirst] at hsecondC
  have hselectedSecond := second.inputPosition_eq_of_support houtput
    (cohook.toNegativeBoundaryExtension.toRightExtension.position cpos)
    j hsecondC
  have hselectedSecondIndex := congrArg PositionAt.index hselectedSecond
  have hformula :=
    houtput.inputPosition_index_eq_source_add_of_forward
      second hforward
        (cohook.toNegativeBoundaryExtension.toRightExtension.position cpos)
  simp only [RightExtension.position_index] at hformula
  omega

/-- In the reverse orientation, an unused edge immediately after the
inherited source endpoint is incompatible with the aligned first factor. -/
private theorem CohookExtension.false_of_reverse_source_boundary
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : first.HasFullInputSupport)
    (houtput : second.HasFullOutputSupport)
    (hne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0)
    (hreverse : (second.inputPosition houtput D.sourcePosition).index =
      (second.inputPosition houtput D.targetPosition).index + D.length)
    {x : Q} (j : M.PositionAt x) (a : D.source ⟶ x)
    (hj : j.index =
      (second.inputPosition houtput D.sourcePosition).index + 1)
    (hstep : M.ArrowStep a
      (second.inputPosition houtput D.sourcePosition) j) : False := by
  have hsource := second.inputPosition_support houtput D.sourcePosition
  have haligned := cohook.secondComponent_support_outputPosition
    hmono first second hinput hne C.sourcePosition
  have hcomponent : Relation.EqvGen (M.MorphismCoefficientStep D)
      (⟨D.source, second.inputPosition houtput D.sourcePosition,
        D.sourcePosition⟩ : M.MorphismCoefficientPosition D)
      ⟨C.source, first.outputPosition hinput C.sourcePosition,
        cohook.toNegativeBoundaryExtension.toRightExtension.position
          C.sourcePosition⟩ :=
    Relation.EqvGen.trans _ second.1.representative _
      hsource.symm haligned
  have hpairs := M.eq_of_morphismCoefficientStep_eqvGen_of_outputIndex_eq
    D hcomponent (by
      change D.sourcePosition.index =
        (cohook.toNegativeBoundaryExtension.toRightExtension.position
          C.sourcePosition).index
      simp)
  have hinputPair := congrArg MorphismCoefficientPosition.inputPosition hpairs
  obtain ⟨aC, hstepC⟩ := exists_arrowStep_of_sourcePosition_eq
    a (second.inputPosition houtput D.sourcePosition) j hstep
      (first.outputPosition hinput C.sourcePosition) hinputPair
  obtain ⟨cpos, hcstep, hcontinued⟩ :=
    first.exists_support_of_outputArrowStep aC C.sourcePosition
      (first.outputPosition hinput C.sourcePosition) j
      (first.outputPosition_support hinput C.sourcePosition) hstepC
  have hcstepIndex := hcstep.index
  simp only [sourcePosition_index] at hcstepIndex
  have hcindex : cpos.index = 1 := by omega
  have hselectedFirst := first.outputPosition_eq_of_support
    hinput cpos j hcontinued
  have hsecondC := cohook.secondComponent_support_outputPosition
    hmono first second hinput hne cpos
  rw [hselectedFirst] at hsecondC
  have hselectedSecond := second.inputPosition_eq_of_support houtput
    (cohook.toNegativeBoundaryExtension.toRightExtension.position cpos)
    j hsecondC
  have hselectedSecondIndex := congrArg PositionAt.index hselectedSecond
  have hformula :=
    houtput.inputPosition_index_add_eq_source_of_reverse
      second hreverse
        (cohook.toNegativeBoundaryExtension.toRightExtension.position cpos)
  simp only [RightExtension.position_index] at hformula
  omega

/-- A component pair selected from a right-cohook factorization cannot make
the second component cover the complete cohook inside a strictly longer
word. -/
theorem CohookExtension.not_length_lt_intermediate_of_component_pair
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (first : C.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent D)
    (hinput : first.HasFullInputSupport)
    (houtput : second.HasFullOutputSupport)
    (hne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0)
    (hlength : D.length < M.length) : False := by
  rcases houtput.exists_outgoingBoundary_of_length_lt second hlength with
    ⟨hforward, hleft | hright⟩ | ⟨hreverse, hleft | hright⟩
  · obtain ⟨x, j, a, hj, hstep⟩ := hleft
    exact cohook.false_of_forward_source_boundary hmono first second
      hinput houtput hne hforward j a hj hstep
  · obtain ⟨y, j, a, hj, hstep⟩ := hright
    exact cohook.maximal a
      (houtput.isString_comp_positive_of_forward_of_target_step
        second hforward a j hj hstep)
  · obtain ⟨x, j, a, hj, hstep⟩ := hleft
    exact cohook.maximal a
      (houtput.isString_comp_positive_of_reverse_of_target_step
        second hreverse a j hj hstep)
  · obtain ⟨y, j, a, hj, hstep⟩ := hright
    exact cohook.false_of_reverse_source_boundary hmono first second
      hinput houtput hne hreverse j a hj hstep

/-- A single component pair contributing nontrivially to the canonical
right-cohook component already forces one of the two ambient factor maps to
split.  This is the direct-sum-ready form of cohook maximality. -/
theorem CohookExtension.isSplitMono_or_isSplitEpi_of_component_pair
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ D.rightModule hmono)
    (first : C.BoundaryFreeMorphismCoefficientComponent M)
    (second : M.BoundaryFreeMorphismCoefficientComponent D)
    (hfirstCoefficient : C.morphismCoefficientAt M hmono hmono f
      first.1.representative ≠ 0)
    (hsecondCoefficient : M.morphismCoefficientAt D hmono hmono g
      second.1.representative ≠ 0)
    (hne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0) :
    IsSplitMono f ∨ IsSplitEpi g := by
  by_cases hf : IsSplitMono f
  · exact Or.inl hf
  by_cases hg : IsSplitEpi g
  · exact Or.inr hg
  exfalso
  have hinput : first.HasFullInputSupport :=
    BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.first_of_comp
      C M D hmono hmono hmono (cohook.moduleMapComponent hmono)
        (cohook.moduleMapComponent_hasFullInputSupport hmono)
        first second hne
  have hC_le_M := hinput.source_length_le_target_length first
  have hC_lt_M : C.length < M.length := by
    apply lt_of_le_of_ne hC_le_M
    intro hlength
    have houtput : first.HasFullOutputSupport :=
      hinput.hasFullOutputSupport_of_length_eq first hlength
    letI : IsIso f :=
      first.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
        hmono hmono hinput houtput f hfirstCoefficient
    exact hf inferInstance
  have houtput : second.HasFullOutputSupport :=
    cohook.secondComponent_hasFullOutputSupport_of_length_lt
      hmono first second hinput hne hC_lt_M
  have hD_le_M := houtput.target_length_le_source_length second
  have hD_lt_M : D.length < M.length := by
    apply lt_of_le_of_ne hD_le_M
    intro hlength
    have hfullInput : second.HasFullInputSupport :=
      houtput.hasFullInputSupport_of_length_eq second hlength.symm
    letI : IsIso g :=
      second.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
        hmono hmono hfullInput houtput g hsecondCoefficient
    exact hg inferInstance
  exact cohook.not_length_lt_intermediate_of_component_pair
    hmono first second hinput houtput hne hD_lt_M

/-- Every factorization of the canonical right-cohook inclusion through a
literal string module has a split first factor or a split second factor. -/
theorem CohookExtension.isSplitMono_or_isSplitEpi_of_moduleMap_factorization
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ D.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono) :
    IsSplitMono f ∨ IsSplitEpi g := by
  obtain ⟨first, second, hfirstCoefficient, hsecondCoefficient,
      hproduct, _⟩ :=
    cohook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hproduct_ne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [hproduct]
    exact one_ne_zero
  exact cohook.isSplitMono_or_isSplitEpi_of_component_pair
    hmono f g first second hfirstCoefficient hsecondCoefficient hproduct_ne

end MagnitudeConjecture.BoundQuiver.StringWord.Word
