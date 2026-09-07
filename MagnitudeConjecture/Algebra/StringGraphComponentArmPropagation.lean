import MagnitudeConjecture.Algebra.StringHookFactorizationBoundary

/-!
# Propagating string graph components along one-sign arms

Support at the two endpoint indices fills the complete intervening word by
component convexity.  Boundary-freeness propagates endpoint support through a
negative source arm or, dually, through a positive target arm.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- Support above the two source-word endpoints fills every source position
of a coefficient component. -/
theorem BoundaryFreeMorphismCoefficientComponent.hasFullInputSupport_of_endpoint_support
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (j₀ : D.PositionAt C.source) (jₙ : D.PositionAt C.target)
    (h₀ : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨C.source, C.sourcePosition, j₀⟩)
    (hₙ : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨C.target, C.targetPosition, jₙ⟩) :
    component.HasFullInputSupport := by
  intro x i
  let p₀ : C.MorphismCoefficientPosition D :=
    ⟨C.source, C.sourcePosition, j₀⟩
  let pₙ : C.MorphismCoefficientPosition D :=
    ⟨C.target, C.targetPosition, jₙ⟩
  let s₀ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨p₀, h₀⟩
  let sₙ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨pₙ, hₙ⟩
  obtain ⟨r, hrIndex⟩ :=
    C.exists_morphismCoefficientComponentSupport_inputIndex_eq_of_between
      D component.1.representative s₀ sₙ i.index (by
        change C.sourcePosition.index ≤ i.index
        simp) (by
        change i.index ≤ C.targetPosition.index
        exact i.index_le)
  rcases r with ⟨⟨y, i', j⟩, hr⟩
  have hposition : (⟨y, i'⟩ : C.Position) = ⟨x, i⟩ :=
    Position.ext_index (C := C) hrIndex
  cases hposition
  exact ⟨j, hr⟩

/-- Support below the two target-word endpoints fills every target position
of a coefficient component. -/
theorem BoundaryFreeMorphismCoefficientComponent.hasFullOutputSupport_of_endpoint_support
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (i₀ : C.PositionAt D.source) (iₙ : C.PositionAt D.target)
    (h₀ : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨D.source, i₀, D.sourcePosition⟩)
    (hₙ : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨D.target, iₙ, D.targetPosition⟩) :
    component.HasFullOutputSupport := by
  intro x j
  let p₀ : C.MorphismCoefficientPosition D :=
    ⟨D.source, i₀, D.sourcePosition⟩
  let pₙ : C.MorphismCoefficientPosition D :=
    ⟨D.target, iₙ, D.targetPosition⟩
  let s₀ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨p₀, h₀⟩
  let sₙ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨pₙ, hₙ⟩
  obtain ⟨r, hrIndex⟩ :=
    C.exists_morphismCoefficientComponentSupport_outputIndex_eq_of_between
      D component.1.representative s₀ sₙ j.index (by
        change D.sourcePosition.index ≤ j.index
        simp) (by
        change j.index ≤ D.targetPosition.index
        exact j.index_le)
  rcases r with ⟨⟨y, i, j'⟩, hr⟩
  have hposition : (⟨y, j'⟩ : D.Position) = ⟨x, j⟩ :=
    Position.ext_index (C := D) hrIndex
  cases hposition
  exact ⟨i, hr⟩

/-- Support at source-index zero and source-index `C.length` fills every
source position, without requiring the two witnesses to be presented using
the named endpoint positions. -/
theorem BoundaryFreeMorphismCoefficientComponent.hasFullInputSupport_of_support_at_endpoint_indices
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    {p₀ pₙ : C.MorphismCoefficientPosition D}
    (h₀ : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative p₀)
    (hₙ : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative pₙ)
    (hp₀ : p₀.inputIndex = 0) (hpₙ : pₙ.inputIndex = C.length) :
    component.HasFullInputSupport := by
  intro x i
  let s₀ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨p₀, h₀⟩
  let sₙ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨pₙ, hₙ⟩
  obtain ⟨r, hrIndex⟩ :=
    C.exists_morphismCoefficientComponentSupport_inputIndex_eq_of_between
      D component.1.representative s₀ sₙ i.index (by
        change p₀.inputIndex ≤ i.index
        omega) (by
        change i.index ≤ pₙ.inputIndex
        have hi := i.index_le
        omega)
  rcases r with ⟨⟨y, i', j⟩, hr⟩
  have hposition : (⟨y, i'⟩ : C.Position) = ⟨x, i⟩ :=
    Position.ext_index (C := C) hrIndex
  cases hposition
  exact ⟨j, hr⟩

/-- Support at target-index zero and target-index `D.length` fills every
target position, without requiring the two witnesses to be presented using
the named endpoint positions. -/
theorem BoundaryFreeMorphismCoefficientComponent.hasFullOutputSupport_of_support_at_endpoint_indices
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    {p₀ pₙ : C.MorphismCoefficientPosition D}
    (h₀ : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative p₀)
    (hₙ : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative pₙ)
    (hp₀ : p₀.outputIndex = 0) (hpₙ : pₙ.outputIndex = D.length) :
    component.HasFullOutputSupport := by
  intro x j
  let s₀ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨p₀, h₀⟩
  let sₙ : C.MorphismCoefficientComponentSupport D
      component.1.representative := ⟨pₙ, hₙ⟩
  obtain ⟨r, hrIndex⟩ :=
    C.exists_morphismCoefficientComponentSupport_outputIndex_eq_of_between
      D component.1.representative s₀ sₙ j.index (by
        change p₀.outputIndex ≤ j.index
        omega) (by
        change j.index ≤ pₙ.outputIndex
        have hj := j.index_le
        omega)
  rcases r with ⟨⟨y, i, j'⟩, hr⟩
  have hposition : (⟨y, j'⟩ : D.Position) = ⟨x, j⟩ :=
    Position.ext_index (C := D) hrIndex
  cases hposition
  exact ⟨i, hr⟩

/-- If a component from the final word supports the embedded base endpoint,
then it supports the embedded final endpoint of every negative arm. -/
theorem NegativeExtension.exists_target_support_of_base_target_support
    {B E D M : Word R} (arm : NegativeExtension B E)
    (suffix : RightExtension E D)
    (component : D.BoundaryFreeMorphismCoefficientComponent M)
    (j₀ : M.PositionAt B.target)
    (h₀ : Relation.EqvGen (D.MorphismCoefficientStep M)
      component.1.representative
      ⟨B.target, (arm.toRightExtension.trans suffix).position
        B.targetPosition, j₀⟩) :
    ∃ jₙ : M.PositionAt E.target,
      Relation.EqvGen (D.MorphismCoefficientStep M)
        component.1.representative
        ⟨E.target, suffix.position E.targetPosition, jₙ⟩ := by
  induction arm generalizing D with
  | base =>
      exact ⟨j₀, by
        simpa only [NegativeExtension.toRightExtension,
          RightExtension.base_trans] using h₀⟩
  | @step E₀ arm z a h ih =>
      let one : RightExtension E₀ (append R E₀ (negativeArrow a) h) :=
        .step .base (negativeArrow a) h
      let priorSuffix : RightExtension E₀ D := one.trans suffix
      have hbase : Relation.EqvGen (D.MorphismCoefficientStep M)
          component.1.representative
          ⟨B.target, (arm.toRightExtension.trans priorSuffix).position
            B.targetPosition, j₀⟩ := by
        have hextension : arm.toRightExtension.trans priorSuffix =
            (NegativeExtension.step arm a h).toRightExtension.trans suffix := by
          simpa only [priorSuffix, one,
            NegativeExtension.toRightExtension, RightExtension.trans] using
              (RightExtension.trans_assoc arm.toRightExtension one suffix).symm
        rw [hextension]
        exact h₀
      obtain ⟨j, hj⟩ := ih priorSuffix component hbase
      have hj' : Relation.EqvGen (D.MorphismCoefficientStep M)
          component.1.representative
          ⟨E₀.target,
            suffix.position
              (appendPosition E₀ (negativeArrow a) h E₀.targetPosition),
            j⟩ := by
        rw [show priorSuffix = one.trans suffix by rfl,
          RightExtension.position_trans one suffix E₀.targetPosition] at hj
        change Relation.EqvGen (D.MorphismCoefficientStep M)
          component.1.representative
          ⟨E₀.target,
            suffix.position
              (appendPosition E₀ (negativeArrow a) h E₀.targetPosition),
            j⟩ at hj
        exact hj
      have hstepAppend :
          (append R E₀ (negativeArrow a) h).ArrowStep a
            (appendEndPosition E₀ (negativeArrow a) h)
            (appendPosition E₀ (negativeArrow a) h E₀.targetPosition) :=
        Or.inr rfl
      have hstep := suffix.arrowStep_position a _ _ hstepAppend
      obtain ⟨j', _, hj'⟩ :=
        component.exists_support_of_inputArrowStep a
          (suffix.position (appendEndPosition E₀ (negativeArrow a) h))
          (suffix.position
            (appendPosition E₀ (negativeArrow a) h E₀.targetPosition))
          j hj' hstep
      have hend :
          (⟨z, appendEndPosition E₀ (negativeArrow a) h⟩ :
            (append R E₀ (negativeArrow a) h).Position) =
          ⟨(append R E₀ (negativeArrow a) h).target,
            (append R E₀ (negativeArrow a) h).targetPosition⟩ :=
        Position.ext_index (C := append R E₀ (negativeArrow a) h) (by
          change (appendEndPosition E₀ (negativeArrow a) h).index =
            (append R E₀ (negativeArrow a) h).targetPosition.index
          calc
            _ = E₀.length + 1 :=
              appendEndPosition_index E₀ (negativeArrow a) h
            _ = (append R E₀ (negativeArrow a) h).length := by
              rw [append_length]
            _ = _ := (targetPosition_index
              (append R E₀ (negativeArrow a) h)).symm)
      cases hend
      exact ⟨j', hj'⟩

/-- If a component into the final word supports the embedded base endpoint,
then it supports the embedded final endpoint of every positive arm. -/
theorem PositiveExtension.exists_target_support_of_base_target_support
    {B E D M : Word R} (arm : PositiveExtension B E)
    (suffix : RightExtension E D)
    (component : M.BoundaryFreeMorphismCoefficientComponent D)
    (i₀ : M.PositionAt B.target)
    (h₀ : Relation.EqvGen (M.MorphismCoefficientStep D)
      component.1.representative
      ⟨B.target, i₀, (arm.toRightExtension.trans suffix).position
        B.targetPosition⟩) :
    ∃ iₙ : M.PositionAt E.target,
      Relation.EqvGen (M.MorphismCoefficientStep D)
        component.1.representative
        ⟨E.target, iₙ, suffix.position E.targetPosition⟩ := by
  induction arm generalizing D with
  | base =>
      exact ⟨i₀, by
        simpa only [PositiveExtension.toRightExtension,
          RightExtension.base_trans] using h₀⟩
  | @step E₀ arm z a h ih =>
      let one : RightExtension E₀ (append R E₀ (positiveArrow a) h) :=
        .step .base (positiveArrow a) h
      let priorSuffix : RightExtension E₀ D := one.trans suffix
      have hbase : Relation.EqvGen (M.MorphismCoefficientStep D)
          component.1.representative
          ⟨B.target, i₀, (arm.toRightExtension.trans priorSuffix).position
            B.targetPosition⟩ := by
        have hextension : arm.toRightExtension.trans priorSuffix =
            (PositiveExtension.step arm a h).toRightExtension.trans suffix := by
          simpa only [priorSuffix, one,
            PositiveExtension.toRightExtension, RightExtension.trans] using
              (RightExtension.trans_assoc arm.toRightExtension one suffix).symm
        rw [hextension]
        exact h₀
      obtain ⟨i, hi⟩ := ih priorSuffix component hbase
      have hi' : Relation.EqvGen (M.MorphismCoefficientStep D)
          component.1.representative
          ⟨E₀.target, i,
            suffix.position
              (appendPosition E₀ (positiveArrow a) h E₀.targetPosition)⟩ := by
        rw [show priorSuffix = one.trans suffix by rfl,
          RightExtension.position_trans one suffix E₀.targetPosition] at hi
        change Relation.EqvGen (M.MorphismCoefficientStep D)
          component.1.representative
          ⟨E₀.target, i,
            suffix.position
              (appendPosition E₀ (positiveArrow a) h E₀.targetPosition)⟩ at hi
        exact hi
      have hstepAppend :
          (append R E₀ (positiveArrow a) h).ArrowStep a
            (appendPosition E₀ (positiveArrow a) h E₀.targetPosition)
            (appendEndPosition E₀ (positiveArrow a) h) :=
        Or.inl rfl
      have hstep := suffix.arrowStep_position a _ _ hstepAppend
      obtain ⟨i', _, hi'⟩ :=
        component.exists_support_of_outputArrowStep a i
          (suffix.position
            (appendPosition E₀ (positiveArrow a) h E₀.targetPosition))
          (suffix.position (appendEndPosition E₀ (positiveArrow a) h))
          hi' hstep
      have hend :
          (⟨z, appendEndPosition E₀ (positiveArrow a) h⟩ :
            (append R E₀ (positiveArrow a) h).Position) =
          ⟨(append R E₀ (positiveArrow a) h).target,
            (append R E₀ (positiveArrow a) h).targetPosition⟩ :=
        Position.ext_index (C := append R E₀ (positiveArrow a) h) (by
          change (appendEndPosition E₀ (positiveArrow a) h).index =
            (append R E₀ (positiveArrow a) h).targetPosition.index
          calc
            _ = E₀.length + 1 :=
              appendEndPosition_index E₀ (positiveArrow a) h
            _ = (append R E₀ (positiveArrow a) h).length := by
              rw [append_length]
            _ = _ := (targetPosition_index
              (append R E₀ (positiveArrow a) h)).symm)
      cases hend
      exact ⟨i', hi'⟩

/-- In a strict-growth right-hook factorization, propagation through the
negative tail makes the selected first component cover the complete hook
word. -/
theorem HookExtension.firstComponent_hasFullInputSupport_of_length_lt
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
    first.HasFullInputSupport := by
  obtain ⟨jBoundary, _, hboundary⟩ :=
    hook.exists_firstNewPosition_support_of_component_pair_of_length_lt
      hmono first second houtput hne hlength
  let B := append R C (positiveArrow hook.arrow) hook.valid
  have hBend :
      appendEndPosition C (positiveArrow hook.arrow) hook.valid =
        B.targetPosition :=
    PositionAt.ext_index (by
      change C.length + 1 = B.length
      simp [B])
  have hbase : Relation.EqvGen (D.MorphismCoefficientStep M)
      first.1.representative
      ⟨B.target, hook.tail.toRightExtension.position B.targetPosition,
        jBoundary⟩ := by
    change Relation.EqvGen (D.MorphismCoefficientStep M)
      first.1.representative
      ⟨B.target,
        hook.tail.toRightExtension.position
          (appendEndPosition C (positiveArrow hook.arrow) hook.valid),
        jBoundary⟩ at hboundary
    rw [hBend] at hboundary
    exact hboundary
  obtain ⟨jTarget, htarget⟩ :=
    hook.tail.exists_target_support_of_base_target_support
      (RightExtension.base : RightExtension D D) first jBoundary (by
        simpa only [RightExtension.trans_base] using hbase)
  have hsource := hook.firstComponent_support_inputPosition
    hmono first second houtput hne C.sourcePosition
  intro x i
  exact (first.hasFullInputSupport_of_support_at_endpoint_indices
      (p₀ := ⟨C.source,
        hook.toPositiveBoundaryExtension.toRightExtension.position
          C.sourcePosition,
        second.inputPosition houtput C.sourcePosition⟩)
      (pₙ := ⟨D.target, D.targetPosition, jTarget⟩)
      hsource htarget (by
        change
          (hook.toPositiveBoundaryExtension.toRightExtension.position
            C.sourcePosition).index = 0
        simp) (by
        change D.targetPosition.index = D.length
        simp)) i

/-- In a strict-growth right-cohook factorization, propagation through the
positive tail makes the selected second component cover the complete cohook
word. -/
theorem CohookExtension.secondComponent_hasFullOutputSupport_of_length_lt
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
    second.HasFullOutputSupport := by
  obtain ⟨iBoundary, _, hboundary⟩ :=
    cohook.exists_firstNewPosition_support_of_component_pair_of_length_lt
      hmono first second hinput hne hlength
  let B := append R C (negativeArrow cohook.arrow) cohook.valid
  have hBend :
      appendEndPosition C (negativeArrow cohook.arrow) cohook.valid =
        B.targetPosition :=
    PositionAt.ext_index (by
      change C.length + 1 = B.length
      simp [B])
  have hbase : Relation.EqvGen (M.MorphismCoefficientStep D)
      second.1.representative
      ⟨B.target, iBoundary,
        cohook.tail.toRightExtension.position B.targetPosition⟩ := by
    change Relation.EqvGen (M.MorphismCoefficientStep D)
      second.1.representative
      ⟨B.target, iBoundary,
        cohook.tail.toRightExtension.position
          (appendEndPosition C (negativeArrow cohook.arrow) cohook.valid)⟩
      at hboundary
    rw [hBend] at hboundary
    exact hboundary
  obtain ⟨iTarget, htarget⟩ :=
    cohook.tail.exists_target_support_of_base_target_support
      (RightExtension.base : RightExtension D D) second iBoundary (by
        simpa only [RightExtension.trans_base] using hbase)
  have hsource := cohook.secondComponent_support_outputPosition
    hmono first second hinput hne C.sourcePosition
  intro x j
  exact (second.hasFullOutputSupport_of_support_at_endpoint_indices
      (p₀ := ⟨C.source,
        first.outputPosition hinput C.sourcePosition,
        cohook.toNegativeBoundaryExtension.toRightExtension.position
          C.sourcePosition⟩)
      (pₙ := ⟨D.target, iTarget, D.targetPosition⟩)
      hsource htarget (by
        change
          (cohook.toNegativeBoundaryExtension.toRightExtension.position
            C.sourcePosition).index = 0
        simp) (by
      change D.targetPosition.index = D.length
      simp)) j

/-- If the intermediate string has the hook result's length, the first factor
of a right-hook factorization is an isomorphism. -/
theorem HookExtension.firstFactor_isIso_of_intermediate_length_eq_result
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (f : D.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono)
    (hlength : M.length = D.length) :
    IsIso f := by
  obtain ⟨first, second, hfirstCoefficient, _, hproduct, houtput⟩ :=
    hook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hC_lt_D : C.length < D.length := by
    rw [hook.result_length]
    simp only [HookExtension.steps]
    omega
  have hC_lt_M : C.length < M.length := by omega
  have hproduct_ne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [hproduct]
    exact one_ne_zero
  have hinput : first.HasFullInputSupport := by
    intro x i
    exact hook.firstComponent_hasFullInputSupport_of_length_lt
      hmono first second houtput hproduct_ne hC_lt_M i
  have hfullOutput : first.HasFullOutputSupport :=
    hinput.hasFullOutputSupport_of_length_eq first hlength.symm
  exact first.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
    hmono hmono hinput hfullOutput f hfirstCoefficient

/-- If the intermediate string has the cohook result's length, the second
factor of a right-cohook factorization is an isomorphism. -/
theorem CohookExtension.secondFactor_isIso_of_intermediate_length_eq_result
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ D.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono)
    (hlength : M.length = D.length) :
    IsIso g := by
  obtain ⟨first, second, _, hsecondCoefficient, hproduct, hinput⟩ :=
    cohook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hC_lt_D : C.length < D.length := by
    rw [cohook.result_length]
    simp only [CohookExtension.steps]
    omega
  have hC_lt_M : C.length < M.length := by omega
  have hproduct_ne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [hproduct]
    exact one_ne_zero
  have houtput : second.HasFullOutputSupport := by
    intro x j
    exact cohook.secondComponent_hasFullOutputSupport_of_length_lt
      hmono first second hinput hproduct_ne hC_lt_M j
  have hfullInput : second.HasFullInputSupport :=
    houtput.hasFullInputSupport_of_length_eq second hlength
  exact second.isIso_of_morphismCoefficientAt_ne_zero_of_fullSupport
    hmono hmono hfullInput houtput g hsecondCoefficient

/-- A literal-string factorization of a right hook with neither factor split
must pass through a word strictly longer than the complete hook word. -/
theorem HookExtension.result_length_lt_intermediate_of_not_split
    {C D M : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R)
    (f : D.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ C.rightModule hmono)
    (hfactor : f ≫ g = hook.moduleMap hmono)
    (hf : ¬ IsSplitMono f) (hg : ¬ IsSplitEpi g) :
    D.length < M.length := by
  obtain ⟨first, second, _, _, hproduct, houtput⟩ :=
    hook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hC_lt_M := hook.base_length_lt_intermediate_of_not_isSplitEpi
    hmono f g hfactor hg
  have hproduct_ne : D.morphismCoefficientAt C hmono hmono
      (D.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap C hmono hmono second)
      (hook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [hproduct]
    exact one_ne_zero
  have hinput : first.HasFullInputSupport := by
    intro x i
    exact hook.firstComponent_hasFullInputSupport_of_length_lt
      hmono first second houtput hproduct_ne hC_lt_M i
  have hle := hinput.source_length_le_target_length first
  apply lt_of_le_of_ne hle
  intro hlength
  letI : IsIso f := hook.firstFactor_isIso_of_intermediate_length_eq_result
    hmono f g hfactor hlength.symm
  exact hf inferInstance

/-- A literal-string factorization of a right cohook with neither factor split
must pass through a word strictly longer than the complete cohook word. -/
theorem CohookExtension.result_length_lt_intermediate_of_not_split
    {C D M : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R)
    (f : C.rightModule hmono ⟶ M.rightModule hmono)
    (g : M.rightModule hmono ⟶ D.rightModule hmono)
    (hfactor : f ≫ g = cohook.moduleMap hmono)
    (hf : ¬ IsSplitMono f) (hg : ¬ IsSplitEpi g) :
    D.length < M.length := by
  obtain ⟨first, second, _, _, hproduct, hinput⟩ :=
    cohook.exists_component_pair_of_moduleMap_factorization
      hmono f g hfactor
  have hC_lt_M := cohook.base_length_lt_intermediate_of_not_isSplitMono
    hmono f g hfactor hf
  have hproduct_ne : C.morphismCoefficientAt D hmono hmono
      (C.boundaryFreeMorphismCoefficientComponentMap M hmono hmono first ≫
        M.boundaryFreeMorphismCoefficientComponentMap D hmono hmono second)
      (cohook.moduleMapComponent hmono).1.representative ≠ 0 := by
    rw [hproduct]
    exact one_ne_zero
  have houtput : second.HasFullOutputSupport := by
    intro x j
    exact cohook.secondComponent_hasFullOutputSupport_of_length_lt
      hmono first second hinput hproduct_ne hC_lt_M j
  have hle := houtput.target_length_le_source_length second
  apply lt_of_le_of_ne hle
  intro hlength
  letI : IsIso g := cohook.secondFactor_isIso_of_intermediate_length_eq_result
    hmono f g hfactor hlength.symm
  exact hg inferInstance

end MagnitudeConjecture.BoundQuiver.StringWord.Word
