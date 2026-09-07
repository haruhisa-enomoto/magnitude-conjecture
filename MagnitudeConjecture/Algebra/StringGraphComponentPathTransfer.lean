import MagnitudeConjecture.Algebra.StringGraphComponentArmPropagation

/-!
# Path transfer along full-support string graph components

A full-source-support coefficient component matches every displayed arrow
step of its source word.  Once the endpoint slope is fixed, the selected
target positions therefore contain either the source word itself or its
reverse as a literal contiguous signed subpath.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- The positions selected by a full-input-support component preserve every
displayed-arrow step of the source word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.outputPosition_arrowStep
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hstep : C.ArrowStep a i j) :
    D.ArrowStep a (component.outputPosition hfull i)
      (component.outputPosition hfull j) := by
  obtain ⟨i', htargetStep, hi'⟩ :=
    component.exists_support_of_inputArrowStep a i j
      (component.outputPosition hfull j)
      (component.outputPosition_support hfull j) hstep
  have hi := component.outputPosition_eq_of_support hfull i i' hi'
  rw [hi]
  exact htargetStep

/-- In the forward endpoint orientation, every selected target index is the
selected source index plus the corresponding source-word index. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.outputPosition_index_eq_source_add_of_forward
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hforward : (component.outputPosition hfull C.targetPosition).index =
      (component.outputPosition hfull C.sourcePosition).index + C.length)
    {x : Q} (i : C.PositionAt x) :
    (component.outputPosition hfull i).index =
      (component.outputPosition hfull C.sourcePosition).index + i.index := by
  have hsource := component.outputPosition_support hfull C.sourcePosition
  have hi := component.outputPosition_support hfull i
  have htarget := component.outputPosition_support hfull C.targetPosition
  have hsource_i : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨C.source, C.sourcePosition,
        component.outputPosition hfull C.sourcePosition⟩ :
        C.MorphismCoefficientPosition D)
      ⟨x, i, component.outputPosition hfull i⟩ :=
    Relation.EqvGen.trans _ component.1.representative _ hsource.symm hi
  have hi_target : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨x, i, component.outputPosition hfull i⟩ :
        C.MorphismCoefficientPosition D)
      ⟨C.target, C.targetPosition,
        component.outputPosition hfull C.targetPosition⟩ :=
    Relation.EqvGen.trans _ component.1.representative _ hi.symm htarget
  have hslopeLeft :=
    C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hsource_i (by
        change C.sourcePosition.index ≤ i.index
        simp)
  have hslopeRight :=
    C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hi_target (by
        change i.index ≤ C.targetPosition.index
        exact i.index_le)
  simp only [MorphismCoefficientPosition.inputIndex,
    MorphismCoefficientPosition.outputIndex, sourcePosition_index,
    targetPosition_index, Nat.sub_zero] at hslopeLeft hslopeRight
  have hiLe := i.index_le
  omega

/-- In the reverse endpoint orientation, every selected target index is the
selected source index minus the corresponding source-word index. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.outputPosition_index_add_eq_source_of_reverse
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hreverse : (component.outputPosition hfull C.sourcePosition).index =
      (component.outputPosition hfull C.targetPosition).index + C.length)
    {x : Q} (i : C.PositionAt x) :
    (component.outputPosition hfull i).index + i.index =
      (component.outputPosition hfull C.sourcePosition).index := by
  have hsource := component.outputPosition_support hfull C.sourcePosition
  have hi := component.outputPosition_support hfull i
  have htarget := component.outputPosition_support hfull C.targetPosition
  have hsource_i : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨C.source, C.sourcePosition,
        component.outputPosition hfull C.sourcePosition⟩ :
        C.MorphismCoefficientPosition D)
      ⟨x, i, component.outputPosition hfull i⟩ :=
    Relation.EqvGen.trans _ component.1.representative _ hsource.symm hi
  have hi_target : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨x, i, component.outputPosition hfull i⟩ :
        C.MorphismCoefficientPosition D)
      ⟨C.target, C.targetPosition,
        component.outputPosition hfull C.targetPosition⟩ :=
    Relation.EqvGen.trans _ component.1.representative _ hi.symm htarget
  have hslopeLeft :=
    C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hsource_i (by
        change C.sourcePosition.index ≤ i.index
        simp)
  have hslopeRight :=
    C.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le
      D hi_target (by
        change i.index ≤ C.targetPosition.index
        exact i.index_le)
  simp only [MorphismCoefficientPosition.inputIndex,
    MorphismCoefficientPosition.outputIndex, sourcePosition_index,
    targetPosition_index, Nat.sub_zero] at hslopeLeft hslopeRight
  have hiLe := i.index_le
  omega

/-- In the forward orientation, the prefix of every selected target position
is the selected source prefix followed by the corresponding source prefix. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.outputPosition_prefix_eq_of_forward_decomposition
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hforward : (component.outputPosition hfull C.targetPosition).index =
      (component.outputPosition hfull C.sourcePosition).index + C.length) :
    ∀ {x : Quiver.Symmetrify Q}
      (p : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) C.source x)
      (q : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) x C.target)
      (hpq : C.path = p.comp q),
      (component.outputPosition hfull
        (⟨p, ⟨q, hpq⟩⟩ : C.PositionAt x)).1 =
        (component.outputPosition hfull C.sourcePosition).1.comp p := by
  intro x p
  induction p with
  | nil =>
      intro q hpq
      have hi :
          (⟨Quiver.Path.nil, ⟨q, hpq⟩⟩ : C.PositionAt C.source) =
            C.sourcePosition :=
        PositionAt.ext_index rfl
      rw [hi]
      simp
  | @cons y z p e ih =>
      intro q hpq
      have hprefix : C.path = p.comp (e.toPath.comp q) := by
        calc
          C.path = (p.cons e).comp q := hpq
          _ = (p.comp e.toPath).comp q := by
            rw [Quiver.Path.comp_toPath_eq_cons]
          _ = p.comp (e.toPath.comp q) :=
            Quiver.Path.comp_assoc _ _ _
      let iprev : C.PositionAt y := ⟨p, ⟨e.toPath.comp q, hprefix⟩⟩
      let icurr : C.PositionAt z := ⟨p.cons e, ⟨q, hpq⟩⟩
      have ihprev := ih (e.toPath.comp q) hprefix
      have hprevIndex :=
        hfull.outputPosition_index_eq_source_add_of_forward
          component hforward iprev
      have hcurrIndex :=
        hfull.outputPosition_index_eq_source_add_of_forward
          component hforward icurr
      have hindex : (component.outputPosition hfull icurr).index =
          (component.outputPosition hfull iprev).index + 1 := by
        change (component.outputPosition hfull icurr).index =
          (component.outputPosition hfull iprev).index + 1
        change (component.outputPosition hfull icurr).index =
            (component.outputPosition hfull C.sourcePosition).index +
              (p.length + 1) at hcurrIndex
        change (component.outputPosition hfull iprev).index =
            (component.outputPosition hfull C.sourcePosition).index +
              p.length at hprevIndex
        omega
      rcases e with a | a
      · have hstep := hfull.outputPosition_arrowStep component a iprev icurr
          (Or.inl rfl)
        rcases hstep with hstep | hstep
        · calc
            (component.outputPosition hfull icurr).1 =
                (component.outputPosition hfull iprev).1.comp
                  (positiveArrow a).toPath := hstep
            _ = (component.outputPosition hfull C.sourcePosition).1.comp
                (p.comp (positiveArrow a).toPath) := by
              rw [ihprev, Quiver.Path.comp_assoc]
            _ = (component.outputPosition hfull C.sourcePosition).1.comp
                (p.cons (Sum.inl a)) := by
              simp only [positiveArrow, Quiver.Path.comp_toPath_eq_cons]
        · have hlength := congrArg Quiver.Path.length hstep
          simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
            at hlength
          change (component.outputPosition hfull iprev).index =
            (component.outputPosition hfull icurr).index + 1 at hlength
          omega
      · have hstep := hfull.outputPosition_arrowStep component a icurr iprev
          (Or.inr rfl)
        rcases hstep with hstep | hstep
        · have hlength := congrArg Quiver.Path.length hstep
          simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
            at hlength
          change (component.outputPosition hfull iprev).index =
            (component.outputPosition hfull icurr).index + 1 at hlength
          omega
        · calc
            (component.outputPosition hfull icurr).1 =
                (component.outputPosition hfull iprev).1.comp
                  (negativeArrow a).toPath := hstep
            _ = (component.outputPosition hfull C.sourcePosition).1.comp
                (p.comp (negativeArrow a).toPath) := by
              rw [ihprev, Quiver.Path.comp_assoc]
            _ = (component.outputPosition hfull C.sourcePosition).1.comp
                (p.cons (Sum.inr a)) := by
              simp only [negativeArrow, Quiver.Path.comp_toPath_eq_cons]

/-- In the forward orientation, selected prefixes literally contain the
corresponding source prefixes. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.outputPosition_prefix_eq_of_forward
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hforward : (component.outputPosition hfull C.targetPosition).index =
      (component.outputPosition hfull C.sourcePosition).index + C.length)
    {x : Q} (i : C.PositionAt x) :
    (component.outputPosition hfull i).1 =
      (component.outputPosition hfull C.sourcePosition).1.comp i.1 := by
  rcases i with ⟨p, q, hpq⟩
  exact hfull.outputPosition_prefix_eq_of_forward_decomposition
    component hforward p q hpq

/-- In the reverse orientation, the selected source prefix is the selected
prefix at `p` followed by the reverse of `p`. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.outputPosition_source_prefix_eq_comp_reverse_decomposition
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hreverse : (component.outputPosition hfull C.sourcePosition).index =
      (component.outputPosition hfull C.targetPosition).index + C.length) :
    ∀ {x : Quiver.Symmetrify Q}
      (p : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) C.source x)
      (q : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) x C.target)
      (hpq : C.path = p.comp q),
      (component.outputPosition hfull C.sourcePosition).1 =
        (component.outputPosition hfull
          (⟨p, ⟨q, hpq⟩⟩ : C.PositionAt x)).1.comp p.reverse := by
  intro x p
  induction p with
  | nil =>
      intro q hpq
      have hi :
          (⟨Quiver.Path.nil, ⟨q, hpq⟩⟩ : C.PositionAt C.source) =
            C.sourcePosition :=
        PositionAt.ext_index rfl
      rw [hi]
      simp
  | @cons y z p e ih =>
      intro q hpq
      have hprefix : C.path = p.comp (e.toPath.comp q) := by
        calc
          C.path = (p.cons e).comp q := hpq
          _ = (p.comp e.toPath).comp q := by
            rw [Quiver.Path.comp_toPath_eq_cons]
          _ = p.comp (e.toPath.comp q) :=
            Quiver.Path.comp_assoc _ _ _
      let iprev : C.PositionAt y := ⟨p, ⟨e.toPath.comp q, hprefix⟩⟩
      let icurr : C.PositionAt z := ⟨p.cons e, ⟨q, hpq⟩⟩
      have ihprev := ih (e.toPath.comp q) hprefix
      have hprevIndex :=
        hfull.outputPosition_index_add_eq_source_of_reverse
          component hreverse iprev
      have hcurrIndex :=
        hfull.outputPosition_index_add_eq_source_of_reverse
          component hreverse icurr
      have hindex : (component.outputPosition hfull iprev).index =
          (component.outputPosition hfull icurr).index + 1 := by
        change (component.outputPosition hfull iprev).index =
          (component.outputPosition hfull icurr).index + 1
        change (component.outputPosition hfull iprev).index + p.length =
            (component.outputPosition hfull C.sourcePosition).index
          at hprevIndex
        change (component.outputPosition hfull icurr).index +
            (p.length + 1) =
            (component.outputPosition hfull C.sourcePosition).index
          at hcurrIndex
        omega
      rcases e with a | a
      · have hstep := hfull.outputPosition_arrowStep component a iprev icurr
          (Or.inl rfl)
        rcases hstep with hstep | hstep
        · have hlength := congrArg Quiver.Path.length hstep
          simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
            at hlength
          change (component.outputPosition hfull icurr).index =
            (component.outputPosition hfull iprev).index + 1 at hlength
          omega
        · calc
            (component.outputPosition hfull C.sourcePosition).1 =
                (component.outputPosition hfull iprev).1.comp p.reverse :=
              ihprev
            _ = ((component.outputPosition hfull icurr).1.comp
                  (negativeArrow a).toPath).comp p.reverse := by rw [hstep]
            _ = (component.outputPosition hfull icurr).1.comp
                ((negativeArrow a).toPath.comp p.reverse) :=
              Quiver.Path.comp_assoc _ _ _
            _ = (component.outputPosition hfull icurr).1.comp
                (p.cons (Sum.inl a)).reverse := by
              simp only [negativeArrow,
                ← Quiver.Path.comp_toPath_eq_cons,
                Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
                Quiver.symmetrify_reverse, Sum.swap_inl]
      · have hstep := hfull.outputPosition_arrowStep component a icurr iprev
          (Or.inr rfl)
        rcases hstep with hstep | hstep
        · calc
            (component.outputPosition hfull C.sourcePosition).1 =
                (component.outputPosition hfull iprev).1.comp p.reverse :=
              ihprev
            _ = ((component.outputPosition hfull icurr).1.comp
                  (positiveArrow a).toPath).comp p.reverse := by rw [hstep]
            _ = (component.outputPosition hfull icurr).1.comp
                ((positiveArrow a).toPath.comp p.reverse) :=
              Quiver.Path.comp_assoc _ _ _
            _ = (component.outputPosition hfull icurr).1.comp
                (p.cons (Sum.inr a)).reverse := by
              simp only [positiveArrow,
                ← Quiver.Path.comp_toPath_eq_cons,
                Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
                Quiver.symmetrify_reverse, Sum.swap_inr]
        · have hlength := congrArg Quiver.Path.length hstep
          simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
            at hlength
          change (component.outputPosition hfull icurr).index =
            (component.outputPosition hfull iprev).index + 1 at hlength
          omega

/-- In the reverse orientation, selected prefixes literally contain reversed
source prefixes. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.outputPosition_source_prefix_eq_comp_reverse
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hreverse : (component.outputPosition hfull C.sourcePosition).index =
      (component.outputPosition hfull C.targetPosition).index + C.length)
    {x : Q} (i : C.PositionAt x) :
    (component.outputPosition hfull C.sourcePosition).1 =
      (component.outputPosition hfull i).1.comp i.1.reverse := by
  rcases i with ⟨p, q, hpq⟩
  exact hfull.outputPosition_source_prefix_eq_comp_reverse_decomposition
    component hreverse p q hpq

/-- In the forward orientation, one further incoming arrow after the selected
target endpoint gives a valid negative extension of the source word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.isString_comp_negative_of_forward_of_target_step
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hforward : (component.outputPosition hfull C.targetPosition).index =
      (component.outputPosition hfull C.sourcePosition).index + C.length)
    {z : Q} (a : z ⟶ C.target) (j : D.PositionAt z)
    (hindex : j.index =
      (component.outputPosition hfull C.targetPosition).index + 1)
    (hstep : D.ArrowStep a j
      (component.outputPosition hfull C.targetPosition)) :
    IsString R (C.path.comp (negativeArrow a).toPath) := by
  have hprefix := hfull.outputPosition_prefix_eq_of_forward
    component hforward C.targetPosition
  change (component.outputPosition hfull C.targetPosition).1 =
    (component.outputPosition hfull C.sourcePosition).1.comp C.path at hprefix
  rcases hstep with hstep | hstep
  · have hlength := congrArg Quiver.Path.length hstep
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
    change (component.outputPosition hfull C.targetPosition).index =
      j.index + 1 at hlength
    omega
  · rcases j.2 with ⟨suffix, hj⟩
    apply IsString.of_contiguousSubpath R D.isString
    refine ⟨(component.outputPosition hfull C.sourcePosition).1,
      suffix, ?_⟩
    calc
      D.path = j.1.comp suffix := hj
      _ = ((component.outputPosition hfull C.targetPosition).1.comp
          (negativeArrow a).toPath).comp suffix := by rw [hstep]
      _ = (((component.outputPosition hfull C.sourcePosition).1.comp
          C.path).comp (negativeArrow a).toPath).comp suffix := by
        rw [hprefix]
      _ = (component.outputPosition hfull C.sourcePosition).1.comp
          ((C.path.comp (negativeArrow a).toPath).comp suffix) := by
        simp only [Quiver.Path.comp_assoc]

/-- In the reverse orientation, one further incoming arrow before the
selected target endpoint gives the same valid negative extension after
reversing the ambient contiguous subpath. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport.isString_comp_negative_of_reverse_of_target_step
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullInputSupport)
    (hreverse : (component.outputPosition hfull C.sourcePosition).index =
      (component.outputPosition hfull C.targetPosition).index + C.length)
    {z : Q} (a : z ⟶ C.target) (j : D.PositionAt z)
    (hindex : j.index + 1 =
      (component.outputPosition hfull C.targetPosition).index)
    (hstep : D.ArrowStep a j
      (component.outputPosition hfull C.targetPosition)) :
    IsString R (C.path.comp (negativeArrow a).toPath) := by
  have hprefix := hfull.outputPosition_source_prefix_eq_comp_reverse
    component hreverse C.targetPosition
  change (component.outputPosition hfull C.sourcePosition).1 =
    (component.outputPosition hfull C.targetPosition).1.comp C.path.reverse
    at hprefix
  rcases hstep with hstep | hstep
  · rcases (component.outputPosition hfull C.sourcePosition).2 with
      ⟨suffix, hsource⟩
    apply (isString_reverse_iff R
      (C.path.comp (negativeArrow a).toPath)).mp
    apply IsString.of_contiguousSubpath R D.isString
    refine ⟨j.1, suffix, ?_⟩
    calc
      D.path = (component.outputPosition hfull C.sourcePosition).1.comp
          suffix := hsource
      _ = ((component.outputPosition hfull C.targetPosition).1.comp
          C.path.reverse).comp suffix := by rw [hprefix]
      _ = ((j.1.comp (positiveArrow a).toPath).comp
          C.path.reverse).comp suffix := by rw [hstep]
      _ = j.1.comp
          ((C.path.comp (negativeArrow a).toPath).reverse.comp suffix) := by
        simp only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
          reverse_negativeArrow, Quiver.Path.comp_assoc]
  · have hlength := congrArg Quiver.Path.length hstep
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
    change j.index =
      (component.outputPosition hfull C.targetPosition).index + 1 at hlength
    omega

/-- The positions selected by a full-output-support component preserve every
displayed-arrow step of the target word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.inputPosition_arrowStep
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    {x y : Q} (a : x ⟶ y)
    (i : D.PositionAt x) (j : D.PositionAt y)
    (hstep : D.ArrowStep a i j) :
    C.ArrowStep a (component.inputPosition hfull i)
      (component.inputPosition hfull j) := by
  obtain ⟨j', hsourceStep, hj'⟩ :=
    component.exists_support_of_outputArrowStep a
      (component.inputPosition hfull i) i j
      (component.inputPosition_support hfull i) hstep
  have hj := component.inputPosition_eq_of_support hfull j j' hj'
  rw [hj]
  exact hsourceStep

/-- In the forward endpoint orientation, every selected source index is the
selected target-source index plus the corresponding target-word index. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.inputPosition_index_eq_source_add_of_forward
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hforward : (component.inputPosition hfull D.targetPosition).index =
      (component.inputPosition hfull D.sourcePosition).index + D.length)
    {x : Q} (i : D.PositionAt x) :
    (component.inputPosition hfull i).index =
      (component.inputPosition hfull D.sourcePosition).index + i.index := by
  have hsource := component.inputPosition_support hfull D.sourcePosition
  have hi := component.inputPosition_support hfull i
  have htarget := component.inputPosition_support hfull D.targetPosition
  have hsource_i : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨D.source, component.inputPosition hfull D.sourcePosition,
        D.sourcePosition⟩ : C.MorphismCoefficientPosition D)
      ⟨x, component.inputPosition hfull i, i⟩ :=
    Relation.EqvGen.trans _ component.1.representative _
      hsource.symm hi
  have hi_target : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨x, component.inputPosition hfull i, i⟩ :
        C.MorphismCoefficientPosition D)
      ⟨D.target, component.inputPosition hfull D.targetPosition,
        D.targetPosition⟩ :=
    Relation.EqvGen.trans _ component.1.representative _
      hi.symm htarget
  have hslopeLeft :=
    D.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le C
      (C.morphismCoefficientStep_eqvGen_transpose D hsource_i) (by
        change D.sourcePosition.index ≤ i.index
        simp)
  have hslopeRight :=
    D.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le C
      (C.morphismCoefficientStep_eqvGen_transpose D hi_target) (by
        change i.index ≤ D.targetPosition.index
        exact i.index_le)
  change (component.inputPosition hfull i).index =
        (component.inputPosition hfull D.sourcePosition).index + i.index ∨
      (component.inputPosition hfull D.sourcePosition).index =
        (component.inputPosition hfull i).index + i.index at hslopeLeft
  change (component.inputPosition hfull D.targetPosition).index =
        (component.inputPosition hfull i).index + (D.length - i.index) ∨
      (component.inputPosition hfull i).index =
        (component.inputPosition hfull D.targetPosition).index +
          (D.length - i.index) at hslopeRight
  have hiLe := i.index_le
  omega

/-- In the reverse endpoint orientation, every selected source index plus the
corresponding target-word index is the selected target-source index. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.inputPosition_index_add_eq_source_of_reverse
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hreverse : (component.inputPosition hfull D.sourcePosition).index =
      (component.inputPosition hfull D.targetPosition).index + D.length)
    {x : Q} (i : D.PositionAt x) :
    (component.inputPosition hfull i).index + i.index =
      (component.inputPosition hfull D.sourcePosition).index := by
  have hsource := component.inputPosition_support hfull D.sourcePosition
  have hi := component.inputPosition_support hfull i
  have htarget := component.inputPosition_support hfull D.targetPosition
  have hsource_i : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨D.source, component.inputPosition hfull D.sourcePosition,
        D.sourcePosition⟩ : C.MorphismCoefficientPosition D)
      ⟨x, component.inputPosition hfull i, i⟩ :=
    Relation.EqvGen.trans _ component.1.representative _
      hsource.symm hi
  have hi_target : Relation.EqvGen (C.MorphismCoefficientStep D)
      (⟨x, component.inputPosition hfull i, i⟩ :
        C.MorphismCoefficientPosition D)
      ⟨D.target, component.inputPosition hfull D.targetPosition,
        D.targetPosition⟩ :=
    Relation.EqvGen.trans _ component.1.representative _
      hi.symm htarget
  have hslopeLeft :=
    D.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le C
      (C.morphismCoefficientStep_eqvGen_transpose D hsource_i) (by
        change D.sourcePosition.index ≤ i.index
        simp)
  have hslopeRight :=
    D.morphismCoefficientStep_eqvGen_outputSlope_of_inputIndex_le C
      (C.morphismCoefficientStep_eqvGen_transpose D hi_target) (by
        change i.index ≤ D.targetPosition.index
        exact i.index_le)
  change (component.inputPosition hfull i).index =
        (component.inputPosition hfull D.sourcePosition).index + i.index ∨
      (component.inputPosition hfull D.sourcePosition).index =
        (component.inputPosition hfull i).index + i.index at hslopeLeft
  change (component.inputPosition hfull D.targetPosition).index =
        (component.inputPosition hfull i).index + (D.length - i.index) ∨
      (component.inputPosition hfull i).index =
        (component.inputPosition hfull D.targetPosition).index +
          (D.length - i.index) at hslopeRight
  have hiLe := i.index_le
  omega

/-- In the forward orientation, the prefix of every selected source position
is the selected target-source prefix followed by the corresponding target
prefix. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.inputPosition_prefix_eq_of_forward_decomposition
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hforward : (component.inputPosition hfull D.targetPosition).index =
      (component.inputPosition hfull D.sourcePosition).index + D.length) :
    ∀ {x : Quiver.Symmetrify Q}
      (p : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) D.source x)
      (q : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) x D.target)
      (hpq : D.path = p.comp q),
      (component.inputPosition hfull
        (⟨p, ⟨q, hpq⟩⟩ : D.PositionAt x)).1 =
        (component.inputPosition hfull D.sourcePosition).1.comp p := by
  intro x p
  induction p with
  | nil =>
      intro q hpq
      have hi :
          (⟨Quiver.Path.nil, ⟨q, hpq⟩⟩ : D.PositionAt D.source) =
            D.sourcePosition :=
        PositionAt.ext_index rfl
      rw [hi]
      simp
  | @cons y z p e ih =>
      intro q hpq
      have hprefix : D.path = p.comp (e.toPath.comp q) := by
        calc
          D.path = (p.cons e).comp q := hpq
          _ = (p.comp e.toPath).comp q := by
            rw [Quiver.Path.comp_toPath_eq_cons]
          _ = p.comp (e.toPath.comp q) :=
            Quiver.Path.comp_assoc _ _ _
      let iprev : D.PositionAt y := ⟨p, ⟨e.toPath.comp q, hprefix⟩⟩
      let icurr : D.PositionAt z := ⟨p.cons e, ⟨q, hpq⟩⟩
      have ihprev := ih (e.toPath.comp q) hprefix
      have hprevIndex :=
        hfull.inputPosition_index_eq_source_add_of_forward
          component hforward iprev
      have hcurrIndex :=
        hfull.inputPosition_index_eq_source_add_of_forward
          component hforward icurr
      have hindex : (component.inputPosition hfull icurr).index =
          (component.inputPosition hfull iprev).index + 1 := by
        change (component.inputPosition hfull icurr).index =
          (component.inputPosition hfull iprev).index + 1
        change (component.inputPosition hfull icurr).index =
            (component.inputPosition hfull D.sourcePosition).index +
              (p.length + 1) at hcurrIndex
        change (component.inputPosition hfull iprev).index =
            (component.inputPosition hfull D.sourcePosition).index +
              p.length at hprevIndex
        omega
      rcases e with a | a
      · have hstep := hfull.inputPosition_arrowStep component a iprev icurr
          (Or.inl rfl)
        rcases hstep with hstep | hstep
        · calc
            (component.inputPosition hfull icurr).1 =
                (component.inputPosition hfull iprev).1.comp
                  (positiveArrow a).toPath := hstep
            _ = (component.inputPosition hfull D.sourcePosition).1.comp
                (p.comp (positiveArrow a).toPath) := by
              rw [ihprev, Quiver.Path.comp_assoc]
            _ = (component.inputPosition hfull D.sourcePosition).1.comp
                (p.cons (Sum.inl a)) := by
              simp only [positiveArrow, Quiver.Path.comp_toPath_eq_cons]
        · have hlength := congrArg Quiver.Path.length hstep
          simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
            at hlength
          change (component.inputPosition hfull iprev).index =
            (component.inputPosition hfull icurr).index + 1 at hlength
          omega
      · have hstep := hfull.inputPosition_arrowStep component a icurr iprev
          (Or.inr rfl)
        rcases hstep with hstep | hstep
        · have hlength := congrArg Quiver.Path.length hstep
          simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
            at hlength
          change (component.inputPosition hfull iprev).index =
            (component.inputPosition hfull icurr).index + 1 at hlength
          omega
        · calc
            (component.inputPosition hfull icurr).1 =
                (component.inputPosition hfull iprev).1.comp
                  (negativeArrow a).toPath := hstep
            _ = (component.inputPosition hfull D.sourcePosition).1.comp
                (p.comp (negativeArrow a).toPath) := by
              rw [ihprev, Quiver.Path.comp_assoc]
            _ = (component.inputPosition hfull D.sourcePosition).1.comp
                (p.cons (Sum.inr a)) := by
              simp only [negativeArrow, Quiver.Path.comp_toPath_eq_cons]

/-- In the forward orientation, selected source prefixes literally contain
the corresponding target prefixes. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.inputPosition_prefix_eq_of_forward
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hforward : (component.inputPosition hfull D.targetPosition).index =
      (component.inputPosition hfull D.sourcePosition).index + D.length)
    {x : Q} (i : D.PositionAt x) :
    (component.inputPosition hfull i).1 =
      (component.inputPosition hfull D.sourcePosition).1.comp i.1 := by
  rcases i with ⟨p, q, hpq⟩
  exact hfull.inputPosition_prefix_eq_of_forward_decomposition
    component hforward p q hpq

/-- In the reverse orientation, the selected target-source prefix is the
selected prefix at `p` followed by the reverse of `p`. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.inputPosition_source_prefix_eq_comp_reverse_decomposition
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hreverse : (component.inputPosition hfull D.sourcePosition).index =
      (component.inputPosition hfull D.targetPosition).index + D.length) :
    ∀ {x : Quiver.Symmetrify Q}
      (p : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) D.source x)
      (q : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) x D.target)
      (hpq : D.path = p.comp q),
      (component.inputPosition hfull D.sourcePosition).1 =
        (component.inputPosition hfull
          (⟨p, ⟨q, hpq⟩⟩ : D.PositionAt x)).1.comp p.reverse := by
  intro x p
  induction p with
  | nil =>
      intro q hpq
      have hi :
          (⟨Quiver.Path.nil, ⟨q, hpq⟩⟩ : D.PositionAt D.source) =
            D.sourcePosition :=
        PositionAt.ext_index rfl
      rw [hi]
      simp
  | @cons y z p e ih =>
      intro q hpq
      have hprefix : D.path = p.comp (e.toPath.comp q) := by
        calc
          D.path = (p.cons e).comp q := hpq
          _ = (p.comp e.toPath).comp q := by
            rw [Quiver.Path.comp_toPath_eq_cons]
          _ = p.comp (e.toPath.comp q) :=
            Quiver.Path.comp_assoc _ _ _
      let iprev : D.PositionAt y := ⟨p, ⟨e.toPath.comp q, hprefix⟩⟩
      let icurr : D.PositionAt z := ⟨p.cons e, ⟨q, hpq⟩⟩
      have ihprev := ih (e.toPath.comp q) hprefix
      have hprevIndex :=
        hfull.inputPosition_index_add_eq_source_of_reverse
          component hreverse iprev
      have hcurrIndex :=
        hfull.inputPosition_index_add_eq_source_of_reverse
          component hreverse icurr
      have hindex : (component.inputPosition hfull iprev).index =
          (component.inputPosition hfull icurr).index + 1 := by
        change (component.inputPosition hfull iprev).index =
          (component.inputPosition hfull icurr).index + 1
        change (component.inputPosition hfull iprev).index + p.length =
            (component.inputPosition hfull D.sourcePosition).index
          at hprevIndex
        change (component.inputPosition hfull icurr).index +
            (p.length + 1) =
            (component.inputPosition hfull D.sourcePosition).index
          at hcurrIndex
        omega
      rcases e with a | a
      · have hstep := hfull.inputPosition_arrowStep component a iprev icurr
          (Or.inl rfl)
        rcases hstep with hstep | hstep
        · have hlength := congrArg Quiver.Path.length hstep
          simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
            at hlength
          change (component.inputPosition hfull icurr).index =
            (component.inputPosition hfull iprev).index + 1 at hlength
          omega
        · calc
            (component.inputPosition hfull D.sourcePosition).1 =
                (component.inputPosition hfull iprev).1.comp p.reverse :=
              ihprev
            _ = ((component.inputPosition hfull icurr).1.comp
                  (negativeArrow a).toPath).comp p.reverse := by rw [hstep]
            _ = (component.inputPosition hfull icurr).1.comp
                ((negativeArrow a).toPath.comp p.reverse) :=
              Quiver.Path.comp_assoc _ _ _
            _ = (component.inputPosition hfull icurr).1.comp
                (p.cons (Sum.inl a)).reverse := by
              simp only [negativeArrow,
                ← Quiver.Path.comp_toPath_eq_cons,
                Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
                Quiver.symmetrify_reverse, Sum.swap_inl]
      · have hstep := hfull.inputPosition_arrowStep component a icurr iprev
          (Or.inr rfl)
        rcases hstep with hstep | hstep
        · calc
            (component.inputPosition hfull D.sourcePosition).1 =
                (component.inputPosition hfull iprev).1.comp p.reverse :=
              ihprev
            _ = ((component.inputPosition hfull icurr).1.comp
                  (positiveArrow a).toPath).comp p.reverse := by rw [hstep]
            _ = (component.inputPosition hfull icurr).1.comp
                ((positiveArrow a).toPath.comp p.reverse) :=
              Quiver.Path.comp_assoc _ _ _
            _ = (component.inputPosition hfull icurr).1.comp
                (p.cons (Sum.inr a)).reverse := by
              simp only [positiveArrow,
                ← Quiver.Path.comp_toPath_eq_cons,
                Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
                Quiver.symmetrify_reverse, Sum.swap_inr]
        · have hlength := congrArg Quiver.Path.length hstep
          simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
            at hlength
          change (component.inputPosition hfull icurr).index =
            (component.inputPosition hfull iprev).index + 1 at hlength
          omega

/-- In the reverse orientation, selected source prefixes literally contain
reversed target prefixes. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.inputPosition_source_prefix_eq_comp_reverse
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hreverse : (component.inputPosition hfull D.sourcePosition).index =
      (component.inputPosition hfull D.targetPosition).index + D.length)
    {x : Q} (i : D.PositionAt x) :
    (component.inputPosition hfull D.sourcePosition).1 =
      (component.inputPosition hfull i).1.comp i.1.reverse := by
  rcases i with ⟨p, q, hpq⟩
  exact hfull.inputPosition_source_prefix_eq_comp_reverse_decomposition
    component hreverse p q hpq

/-- In the forward orientation, one further outgoing arrow after the selected
target endpoint gives a valid positive extension of the target word. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.isString_comp_positive_of_forward_of_target_step
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hforward : (component.inputPosition hfull D.targetPosition).index =
      (component.inputPosition hfull D.sourcePosition).index + D.length)
    {z : Q} (a : D.target ⟶ z) (j : C.PositionAt z)
    (hindex : j.index =
      (component.inputPosition hfull D.targetPosition).index + 1)
    (hstep : C.ArrowStep a
      (component.inputPosition hfull D.targetPosition) j) :
    IsString R (D.path.comp (positiveArrow a).toPath) := by
  have hprefix := hfull.inputPosition_prefix_eq_of_forward
    component hforward D.targetPosition
  change (component.inputPosition hfull D.targetPosition).1 =
    (component.inputPosition hfull D.sourcePosition).1.comp D.path at hprefix
  rcases hstep with hstep | hstep
  · rcases j.2 with ⟨suffix, hj⟩
    apply IsString.of_contiguousSubpath R C.isString
    refine ⟨(component.inputPosition hfull D.sourcePosition).1,
      suffix, ?_⟩
    calc
      C.path = j.1.comp suffix := hj
      _ = ((component.inputPosition hfull D.targetPosition).1.comp
          (positiveArrow a).toPath).comp suffix := by rw [hstep]
      _ = (((component.inputPosition hfull D.sourcePosition).1.comp
          D.path).comp (positiveArrow a).toPath).comp suffix := by
        rw [hprefix]
      _ = (component.inputPosition hfull D.sourcePosition).1.comp
          ((D.path.comp (positiveArrow a).toPath).comp suffix) := by
        simp only [Quiver.Path.comp_assoc]
  · have hlength := congrArg Quiver.Path.length hstep
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
    change (component.inputPosition hfull D.targetPosition).index =
      j.index + 1 at hlength
    omega

/-- In the reverse orientation, one further outgoing arrow before the
selected target endpoint gives the same valid positive extension after
reversing the ambient contiguous subpath. -/
theorem BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport.isString_comp_positive_of_reverse_of_target_step
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D)
    (hfull : component.HasFullOutputSupport)
    (hreverse : (component.inputPosition hfull D.sourcePosition).index =
      (component.inputPosition hfull D.targetPosition).index + D.length)
    {z : Q} (a : D.target ⟶ z) (j : C.PositionAt z)
    (hindex : j.index + 1 =
      (component.inputPosition hfull D.targetPosition).index)
    (hstep : C.ArrowStep a
      (component.inputPosition hfull D.targetPosition) j) :
    IsString R (D.path.comp (positiveArrow a).toPath) := by
  have hprefix := hfull.inputPosition_source_prefix_eq_comp_reverse
    component hreverse D.targetPosition
  change (component.inputPosition hfull D.sourcePosition).1 =
    (component.inputPosition hfull D.targetPosition).1.comp D.path.reverse
    at hprefix
  rcases hstep with hstep | hstep
  · have hlength := congrArg Quiver.Path.length hstep
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hlength
    change j.index =
      (component.inputPosition hfull D.targetPosition).index + 1 at hlength
    omega
  · rcases (component.inputPosition hfull D.sourcePosition).2 with
      ⟨suffix, hsource⟩
    apply (isString_reverse_iff R
      (D.path.comp (positiveArrow a).toPath)).mp
    apply IsString.of_contiguousSubpath R C.isString
    refine ⟨j.1, suffix, ?_⟩
    calc
      C.path = (component.inputPosition hfull D.sourcePosition).1.comp
          suffix := hsource
      _ = ((component.inputPosition hfull D.targetPosition).1.comp
          D.path.reverse).comp suffix := by rw [hprefix]
      _ = ((j.1.comp (negativeArrow a).toPath).comp
          D.path.reverse).comp suffix := by rw [hstep]
      _ = j.1.comp
          ((D.path.comp (positiveArrow a).toPath).reverse.comp suffix) := by
        simp only [Quiver.Path.reverse_comp, Quiver.Path.reverse_toPath,
          reverse_positiveArrow, Quiver.Path.comp_assoc]

end MagnitudeConjecture.BoundQuiver.StringWord.Word
