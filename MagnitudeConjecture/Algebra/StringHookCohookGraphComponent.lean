import MagnitudeConjecture.Algebra.StringGraphComponentSpanning
import MagnitudeConjecture.Algebra.StringLeftHookCohook

/-!
# Hook and cohook maps as graph components

The canonical hook and cohook maps are carried by the single coefficient
component pairing every old word position with its inherited position in the
extended word.  This file identifies those maps with literal vectors in the
compiled graph-component basis.  It is the coefficient-level input for the
remaining irreducible-factorization argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k Q : Type u} [Field k] [Quiver.{u} Q]
variable {R : RelationFamily k Q}

/-- A coefficient position obtained by mapping the same position of an
indexing word into a source word and a target word. -/
def pairedMorphismCoefficientPosition
    (W C D : Word R)
    (inputPosition : ∀ {x : Q}, W.PositionAt x → C.PositionAt x)
    (outputPosition : ∀ {x : Q}, W.PositionAt x → D.PositionAt x)
    {x : Q} (i : W.PositionAt x) :
    C.MorphismCoefficientPosition D :=
  ⟨x, inputPosition i, outputPosition i⟩

private theorem pairedMorphismCoefficientPosition_eqvGen_source_of_prefix
    (W C D : Word R)
    (inputPosition : ∀ {x : Q}, W.PositionAt x → C.PositionAt x)
    (outputPosition : ∀ {x : Q}, W.PositionAt x → D.PositionAt x)
    (hinput : ∀ {x y : Q} (a : x ⟶ y)
      (i : W.PositionAt x) (j : W.PositionAt y),
      W.ArrowStep a i j →
        C.ArrowStep a (inputPosition i) (inputPosition j))
    (houtput : ∀ {x y : Q} (a : x ⟶ y)
      (i : W.PositionAt x) (j : W.PositionAt y),
      W.ArrowStep a i j →
        D.ArrowStep a (outputPosition i) (outputPosition j)) :
    ∀ {x : Quiver.Symmetrify Q}
      (p : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) W.source x)
      (q : @Quiver.Path (Quiver.Symmetrify Q)
        (Quiver.symmetrifyQuiver Q) x W.target)
      (hpq : W.path = p.comp q),
      Relation.EqvGen (C.MorphismCoefficientStep D)
        (pairedMorphismCoefficientPosition W C D inputPosition outputPosition
          (⟨p, ⟨q, hpq⟩⟩ : W.PositionAt x))
        (pairedMorphismCoefficientPosition W C D inputPosition outputPosition
          W.sourcePosition) := by
  intro x p
  induction p with
  | nil =>
      intro q hpq
      have hi :
          (⟨Quiver.Path.nil, ⟨q, hpq⟩⟩ :
              W.PositionAt W.source) = W.sourcePosition := by
        apply PositionAt.ext_index
        rfl
      rw [hi]
      exact Relation.EqvGen.refl _
  | @cons y z p e ih =>
      intro q hpq
      have hprefix : W.path = p.comp (e.toPath.comp q) := by
        calc
          W.path = (p.cons e).comp q := hpq
          _ = (p.comp e.toPath).comp q := by
            rw [Quiver.Path.comp_toPath_eq_cons]
          _ = p.comp (e.toPath.comp q) :=
            Quiver.Path.comp_assoc _ _ _
      let iprev : W.PositionAt y :=
        ⟨p, ⟨e.toPath.comp q, hprefix⟩⟩
      have hprev := ih (e.toPath.comp q) hprefix
      rcases e with a | a
      · let icurr : W.PositionAt z :=
          ⟨p.cons (Sum.inl a), ⟨q, hpq⟩⟩
        have hstep : W.ArrowStep a iprev icurr := Or.inl rfl
        have hedge : C.MorphismCoefficientStep D
            (pairedMorphismCoefficientPosition W C D inputPosition
              outputPosition iprev)
            (pairedMorphismCoefficientPosition W C D inputPosition
              outputPosition icurr) :=
          MorphismCoefficientStep.ofArrow a
            (inputPosition iprev) (inputPosition icurr)
            (outputPosition iprev) (outputPosition icurr)
            (hinput a iprev icurr hstep)
            (houtput a iprev icurr hstep)
        change Relation.EqvGen (C.MorphismCoefficientStep D)
          (pairedMorphismCoefficientPosition W C D inputPosition
            outputPosition icurr) _
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hedge)) hprev
      · let icurr : W.PositionAt z :=
          ⟨p.cons (Sum.inr a), ⟨q, hpq⟩⟩
        have hstep : W.ArrowStep a icurr iprev := Or.inr rfl
        have hedge : C.MorphismCoefficientStep D
            (pairedMorphismCoefficientPosition W C D inputPosition
              outputPosition icurr)
            (pairedMorphismCoefficientPosition W C D inputPosition
              outputPosition iprev) :=
          MorphismCoefficientStep.ofArrow a
            (inputPosition icurr) (inputPosition iprev)
            (outputPosition icurr) (outputPosition iprev)
            (hinput a icurr iprev hstep)
            (houtput a icurr iprev hstep)
        change Relation.EqvGen (C.MorphismCoefficientStep D)
          (pairedMorphismCoefficientPosition W C D inputPosition
            outputPosition icurr) _
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ hedge) hprev

/-- Position maps preserving displayed-arrow steps carry the whole indexing
word into one coefficient component. -/
theorem pairedMorphismCoefficientPosition_eqvGen_source
    (W C D : Word R)
    (inputPosition : ∀ {x : Q}, W.PositionAt x → C.PositionAt x)
    (outputPosition : ∀ {x : Q}, W.PositionAt x → D.PositionAt x)
    (hinput : ∀ {x y : Q} (a : x ⟶ y)
      (i : W.PositionAt x) (j : W.PositionAt y),
      W.ArrowStep a i j →
        C.ArrowStep a (inputPosition i) (inputPosition j))
    (houtput : ∀ {x y : Q} (a : x ⟶ y)
      (i : W.PositionAt x) (j : W.PositionAt y),
      W.ArrowStep a i j →
        D.ArrowStep a (outputPosition i) (outputPosition j))
    {x : Q} (i : W.PositionAt x) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
      (pairedMorphismCoefficientPosition W C D inputPosition outputPosition i)
      (pairedMorphismCoefficientPosition W C D inputPosition outputPosition
        W.sourcePosition) := by
  rcases i with ⟨p, q, hpq⟩
  exact pairedMorphismCoefficientPosition_eqvGen_source_of_prefix
    W C D inputPosition outputPosition hinput houtput p q hpq

/-- Boundary-freeness is independent of the chosen root inside one
coefficient component. -/
theorem isBoundaryFreeMorphismCoefficientComponent_of_eqvGen
    (C D : Word R) {root root' : C.MorphismCoefficientPosition D}
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root)
    (hroot : Relation.EqvGen (C.MorphismCoefficientStep D) root root') :
    C.IsBoundaryFreeMorphismCoefficientComponent D root' := by
  intro q hq
  exact hfree q (Relation.EqvGen.trans _ _ _ hroot hq)

/-- The boundary-free component class containing a specified root. -/
def boundaryFreeMorphismCoefficientComponentOf
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root) :
    C.BoundaryFreeMorphismCoefficientComponent D := by
  let component := C.morphismCoefficientComponentOf D root
  refine ⟨component, ?_⟩
  have hrepresentative : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.representative root := by
    apply (C.morphismCoefficientComponentOf_eq_iff D
      component.representative root).mp
    simp only [C.morphismCoefficientComponentOf_representative, component]
  exact C.isBoundaryFreeMorphismCoefficientComponent_of_eqvGen D hfree
    hrepresentative.symm

/-- The chosen representative of the component class of `root` lies in the
same generated coefficient component as `root`. -/
theorem boundaryFreeMorphismCoefficientComponentOf_representative_eqvGen
    (C D : Word R) (root : C.MorphismCoefficientPosition D)
    (hfree : C.IsBoundaryFreeMorphismCoefficientComponent D root) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
      (C.boundaryFreeMorphismCoefficientComponentOf D root hfree).1.representative
      root := by
  apply (C.morphismCoefficientComponentOf_eq_iff D _ root).mp
  simp [boundaryFreeMorphismCoefficientComponentOf]

/-- A coefficient component meets every position of its source word. -/
def BoundaryFreeMorphismCoefficientComponent.HasFullInputSupport
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D) : Prop :=
  ∀ {x : Q} (i : C.PositionAt x), ∃ j : D.PositionAt x,
    Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨x, i, j⟩

/-- A coefficient component meets every position of its target word. -/
def BoundaryFreeMorphismCoefficientComponent.HasFullOutputSupport
    {C D : Word R}
    (component : C.BoundaryFreeMorphismCoefficientComponent D) : Prop :=
  ∀ {x : Q} (j : D.PositionAt x), ∃ i : C.PositionAt x,
    Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative ⟨x, i, j⟩

/-- A morphism with root coefficient one and no support outside the root
component is exactly the corresponding graph-component basis map. -/
theorem eq_boundaryFreeMorphismCoefficientComponentMap_of_root
    (C D : Word R) (hC : IsMonomial R) (hD : IsMonomial R)
    (f : C.rightModule hC ⟶ D.rightModule hD)
    (root : C.MorphismCoefficientPosition D)
    (hroot : C.morphismCoefficientAt D hC hD f root = 1)
    (hsupport : ∀ p : C.MorphismCoefficientPosition D,
      C.morphismCoefficientAt D hC hD f p ≠ 0 →
        Relation.EqvGen (C.MorphismCoefficientStep D) root p) :
    f = C.boundaryFreeMorphismCoefficientComponentMap D hC hD
      (C.boundaryFreeMorphismCoefficientComponentOf D root
        (C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
          D hC hD f root (hroot.trans_ne one_ne_zero))) := by
  let hfree := C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
    D hC hD f root (hroot.trans_ne one_ne_zero)
  let component := C.boundaryFreeMorphismCoefficientComponentOf D root hfree
  change f = C.boundaryFreeMorphismCoefficientComponentMap D hC hD component
  apply C.rightModuleHom_ext_morphismCoefficientAt D hC hD
  intro p
  rw [C.morphismCoefficientAt_boundaryFreeComponentMap]
  have hrepresentative : Relation.EqvGen (C.MorphismCoefficientStep D)
      component.1.representative root := by
    exact C.boundaryFreeMorphismCoefficientComponentOf_representative_eqvGen
      D root hfree
  by_cases hp : Relation.EqvGen (C.MorphismCoefficientStep D) root p
  · rw [C.coefficientComponentIndicator_eq_one D _ p
      (Relation.EqvGen.trans _ _ _ hrepresentative hp)]
    exact (C.morphismCoefficientAt_eq_of_eqvGen D hC hD f hp).symm.trans hroot
  · rw [C.coefficientComponentIndicator_eq_zero D _ p]
    · by_contra hne
      exact hp (hsupport p hne)
    · intro hcomponent
      exact hp (Relation.EqvGen.trans _ _ _ hrepresentative.symm hcomponent)

/-- The coefficient position pairing an old position with its image in a
right extension, in the inclusion direction. -/
def RightExtension.inclusionMorphismCoefficientPosition
    {C D : Word R} (extension : RightExtension C D)
    {x : Q} (i : C.PositionAt x) :
    C.MorphismCoefficientPosition D :=
  pairedMorphismCoefficientPosition C C D (fun i ↦ i)
    (fun i ↦ extension.position i) i

/-- The same inherited-position pair in the projection direction. -/
def RightExtension.projectionMorphismCoefficientPosition
    {C D : Word R} (extension : RightExtension C D)
    {x : Q} (i : C.PositionAt x) :
    D.MorphismCoefficientPosition C :=
  pairedMorphismCoefficientPosition C D C
    (fun i ↦ extension.position i) (fun i ↦ i) i

/-- All inherited pairs in the inclusion direction lie in the component of
the inherited source position. -/
theorem RightExtension.inclusionMorphismCoefficientPosition_eqvGen_source
    {C D : Word R} (extension : RightExtension C D)
    {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
      (extension.inclusionMorphismCoefficientPosition i)
      (extension.inclusionMorphismCoefficientPosition C.sourcePosition) := by
  exact pairedMorphismCoefficientPosition_eqvGen_source C C D
    (fun i ↦ i) (fun i ↦ extension.position i)
    (fun _ _ _ hij ↦ hij)
    (fun a i j hij ↦ extension.arrowStep_position a i j hij) i

/-- All inherited pairs in the projection direction lie in the component of
the inherited source position. -/
theorem RightExtension.projectionMorphismCoefficientPosition_eqvGen_source
    {C D : Word R} (extension : RightExtension C D)
    {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (D.MorphismCoefficientStep C)
      (extension.projectionMorphismCoefficientPosition i)
      (extension.projectionMorphismCoefficientPosition C.sourcePosition) := by
  exact pairedMorphismCoefficientPosition_eqvGen_source C D C
    (fun i ↦ extension.position i) (fun i ↦ i)
    (fun a i j hij ↦ extension.arrowStep_position a i j hij)
    (fun _ _ _ hij ↦ hij) i

/-- The right-boundary inclusion has coefficient one at the inherited source
position. -/
@[simp]
theorem NegativeBoundaryExtension.rightModuleInclusion_morphismCoefficientAt_source
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) :
    C.morphismCoefficientAt D hmono hmono
        (extension.rightModuleInclusion hmono)
        (extension.toRightExtension.inclusionMorphismCoefficientPosition
          C.sourcePosition) = 1 := by
  change
    (extension.toRightExtension.spaceInclusion C.source
      (Finsupp.single C.sourcePosition 1))
        (extension.toRightExtension.position C.sourcePosition) = 1
  rw [extension.toRightExtension.spaceInclusion_single]
  simp

/-- Every nonzero coefficient of a right-boundary inclusion belongs to its
inherited-position component. -/
theorem NegativeBoundaryExtension.rightModuleInclusion_coefficient_eqvGen_source
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) (p : C.MorphismCoefficientPosition D)
    (hp : C.morphismCoefficientAt D hmono hmono
      (extension.rightModuleInclusion hmono) p ≠ 0) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
      (extension.toRightExtension.inclusionMorphismCoefficientPosition
        C.sourcePosition) p := by
  rcases p with ⟨x, i, j⟩
  change
    (extension.toRightExtension.spaceInclusion x
      (Finsupp.single i 1)) j ≠ 0 at hp
  rw [extension.toRightExtension.spaceInclusion_single] at hp
  change (Finsupp.single (extension.toRightExtension.position i) 1) j ≠ 0 at hp
  have hj : extension.toRightExtension.position i = j :=
    (Finsupp.single_apply_ne_zero.mp hp).1.symm
  subst j
  exact (RightExtension.inclusionMorphismCoefficientPosition_eqvGen_source
    extension.toRightExtension i).symm

/-- The graph-basis component carrying a right-boundary inclusion. -/
def NegativeBoundaryExtension.rightModuleInclusionComponent
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) :
    C.BoundaryFreeMorphismCoefficientComponent D :=
  C.boundaryFreeMorphismCoefficientComponentOf D
    (extension.toRightExtension.inclusionMorphismCoefficientPosition
      C.sourcePosition)
    (C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero D hmono hmono
      (extension.rightModuleInclusion hmono) _
      (by simp))

/-- A right-boundary inclusion is exactly its inherited-position graph-basis
map. -/
theorem NegativeBoundaryExtension.rightModuleInclusion_eq_componentMap
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) :
    extension.rightModuleInclusion hmono =
      C.boundaryFreeMorphismCoefficientComponentMap D hmono hmono
        (extension.rightModuleInclusionComponent hmono) := by
  simpa only [rightModuleInclusionComponent] using
    C.eq_boundaryFreeMorphismCoefficientComponentMap_of_root D hmono hmono
      (extension.rightModuleInclusion hmono)
      (extension.toRightExtension.inclusionMorphismCoefficientPosition
        C.sourcePosition)
      (extension.rightModuleInclusion_morphismCoefficientAt_source hmono)
      (extension.rightModuleInclusion_coefficient_eqvGen_source hmono)

/-- The right-boundary projection has coefficient one at the inherited source
position. -/
@[simp]
theorem PositiveBoundaryExtension.rightModuleProjection_morphismCoefficientAt_source
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) :
    D.morphismCoefficientAt C hmono hmono
        (extension.rightModuleProjection hmono)
        (extension.toRightExtension.projectionMorphismCoefficientPosition
          C.sourcePosition) = 1 := by
  change
    (extension.toRightExtension.spaceProjection C.source
      (Finsupp.single
        (extension.toRightExtension.position C.sourcePosition) 1))
        C.sourcePosition = 1
  rw [extension.toRightExtension.spaceProjection_single_position]
  simp

/-- Every nonzero coefficient of a right-boundary projection belongs to its
inherited-position component. -/
theorem PositiveBoundaryExtension.rightModuleProjection_coefficient_eqvGen_source
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) (p : D.MorphismCoefficientPosition C)
    (hp : D.morphismCoefficientAt C hmono hmono
      (extension.rightModuleProjection hmono) p ≠ 0) :
    Relation.EqvGen (D.MorphismCoefficientStep C)
      (extension.toRightExtension.projectionMorphismCoefficientPosition
        C.sourcePosition) p := by
  rcases p with ⟨x, i, j⟩
  change
    (extension.toRightExtension.spaceProjection x
      (Finsupp.single i 1)) j ≠ 0 at hp
  rw [extension.toRightExtension.spaceProjection_apply_position] at hp
  change (Finsupp.single i 1)
    (extension.toRightExtension.position j) ≠ 0 at hp
  have hi : i = extension.toRightExtension.position j :=
    (Finsupp.single_apply_ne_zero.mp hp).1.symm
  subst i
  exact (RightExtension.projectionMorphismCoefficientPosition_eqvGen_source
    extension.toRightExtension j).symm

/-- The graph-basis component carrying a right-boundary projection. -/
def PositiveBoundaryExtension.rightModuleProjectionComponent
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) :
    D.BoundaryFreeMorphismCoefficientComponent C :=
  D.boundaryFreeMorphismCoefficientComponentOf C
    (extension.toRightExtension.projectionMorphismCoefficientPosition
      C.sourcePosition)
    (D.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero C hmono hmono
      (extension.rightModuleProjection hmono) _
      (by simp))

/-- A right-boundary projection is exactly its inherited-position graph-basis
map. -/
theorem PositiveBoundaryExtension.rightModuleProjection_eq_componentMap
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) :
    extension.rightModuleProjection hmono =
      D.boundaryFreeMorphismCoefficientComponentMap C hmono hmono
        (extension.rightModuleProjectionComponent hmono) := by
  simpa only [rightModuleProjectionComponent] using
    D.eq_boundaryFreeMorphismCoefficientComponentMap_of_root C hmono hmono
      (extension.rightModuleProjection hmono)
      (extension.toRightExtension.projectionMorphismCoefficientPosition
        C.sourcePosition)
      (extension.rightModuleProjection_morphismCoefficientAt_source hmono)
      (extension.rightModuleProjection_coefficient_eqvGen_source hmono)

/-- Every inherited pair belongs to the component of a right-boundary
inclusion. -/
theorem NegativeBoundaryExtension.rightModuleInclusionComponent_position_support
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (C.MorphismCoefficientStep D)
      (extension.rightModuleInclusionComponent hmono).1.representative
      ⟨x, i, extension.toRightExtension.position i⟩ := by
  let root := RightExtension.inclusionMorphismCoefficientPosition
    extension.toRightExtension C.sourcePosition
  let hfree := C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
    D hmono hmono (extension.rightModuleInclusion hmono) root (by simp [root])
  have hrepresentative :=
    C.boundaryFreeMorphismCoefficientComponentOf_representative_eqvGen
      D root hfree
  have hi := RightExtension.inclusionMorphismCoefficientPosition_eqvGen_source
    extension.toRightExtension i
  simpa only [rightModuleInclusionComponent,
    boundaryFreeMorphismCoefficientComponentOf, root,
    RightExtension.inclusionMorphismCoefficientPosition,
    pairedMorphismCoefficientPosition] using
    Relation.EqvGen.trans _ _ _ hrepresentative hi.symm

/-- The component of a right-boundary inclusion has full support on its
source word. -/
theorem NegativeBoundaryExtension.rightModuleInclusionComponent_hasFullInputSupport
    {C D : Word R} (extension : NegativeBoundaryExtension C D)
    (hmono : IsMonomial R) :
    (extension.rightModuleInclusionComponent hmono).HasFullInputSupport := by
  intro x i
  exact ⟨extension.toRightExtension.position i,
    extension.rightModuleInclusionComponent_position_support hmono i⟩

/-- Every inherited pair belongs to the component of a right-boundary
projection. -/
theorem PositiveBoundaryExtension.rightModuleProjectionComponent_position_support
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (D.MorphismCoefficientStep C)
      (extension.rightModuleProjectionComponent hmono).1.representative
      ⟨x, extension.toRightExtension.position i, i⟩ := by
  let root := RightExtension.projectionMorphismCoefficientPosition
    extension.toRightExtension C.sourcePosition
  let hfree := D.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
    C hmono hmono (extension.rightModuleProjection hmono) root (by simp [root])
  have hrepresentative :=
    D.boundaryFreeMorphismCoefficientComponentOf_representative_eqvGen
      C root hfree
  have hi := RightExtension.projectionMorphismCoefficientPosition_eqvGen_source
    extension.toRightExtension i
  simpa only [rightModuleProjectionComponent,
    boundaryFreeMorphismCoefficientComponentOf, root,
    RightExtension.projectionMorphismCoefficientPosition,
    pairedMorphismCoefficientPosition] using
    Relation.EqvGen.trans _ _ _ hrepresentative hi.symm

/-- The component of a right-boundary projection has full support on its
target word. -/
theorem PositiveBoundaryExtension.rightModuleProjectionComponent_hasFullOutputSupport
    {C D : Word R} (extension : PositiveBoundaryExtension C D)
    (hmono : IsMonomial R) :
    (extension.rightModuleProjectionComponent hmono).HasFullOutputSupport := by
  intro x i
  exact ⟨extension.toRightExtension.position i,
    extension.rightModuleProjectionComponent_position_support hmono i⟩

/-- The graph-basis component carrying a right hook projection. -/
def HookExtension.moduleMapComponent
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) :
    D.BoundaryFreeMorphismCoefficientComponent C :=
  hook.toPositiveBoundaryExtension.rightModuleProjectionComponent hmono

/-- A right hook projection is one graph-basis vector. -/
theorem HookExtension.moduleMap_eq_componentMap
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) :
    hook.moduleMap hmono =
      D.boundaryFreeMorphismCoefficientComponentMap C hmono hmono
        (hook.moduleMapComponent hmono) :=
  hook.toPositiveBoundaryExtension.rightModuleProjection_eq_componentMap hmono

/-- A right hook component covers every position of its target word. -/
theorem HookExtension.moduleMapComponent_hasFullOutputSupport
    {C D : Word R} (hook : HookExtension C D)
    (hmono : IsMonomial R) :
    (hook.moduleMapComponent hmono).HasFullOutputSupport :=
  PositiveBoundaryExtension.rightModuleProjectionComponent_hasFullOutputSupport
    hook.toPositiveBoundaryExtension hmono

/-- The graph-basis component carrying a right cohook inclusion. -/
def CohookExtension.moduleMapComponent
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) :
    C.BoundaryFreeMorphismCoefficientComponent D :=
  cohook.toNegativeBoundaryExtension.rightModuleInclusionComponent hmono

/-- A right cohook inclusion is one graph-basis vector. -/
theorem CohookExtension.moduleMap_eq_componentMap
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) :
    cohook.moduleMap hmono =
      C.boundaryFreeMorphismCoefficientComponentMap D hmono hmono
        (cohook.moduleMapComponent hmono) :=
  cohook.toNegativeBoundaryExtension.rightModuleInclusion_eq_componentMap hmono

/-- A right cohook component covers every position of its source word. -/
theorem CohookExtension.moduleMapComponent_hasFullInputSupport
    {C D : Word R} (cohook : CohookExtension C D)
    (hmono : IsMonomial R) :
    (cohook.moduleMapComponent hmono).HasFullInputSupport :=
  NegativeBoundaryExtension.rightModuleInclusionComponent_hasFullInputSupport
    cohook.toNegativeBoundaryExtension hmono

/-- A positive left-boundary extension preserves every displayed-arrow step
between inherited positions. -/
theorem LeftPositiveBoundaryExtension.arrowStep_position
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    extension.result.ArrowStep a (extension.position i)
      (extension.position j) := by
  exact arrowStep_reversePosition extension.reverseResult a _ _
    (extension.extension.toRightExtension.arrowStep_position a _ _
      (arrowStep_reversePosition C a i j hij))

/-- A negative left-boundary extension preserves every displayed-arrow step
between inherited positions. -/
theorem LeftNegativeBoundaryExtension.arrowStep_position
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    {x y : Q} (a : x ⟶ y)
    (i : C.PositionAt x) (j : C.PositionAt y)
    (hij : C.ArrowStep a i j) :
    extension.result.ArrowStep a (extension.position i)
      (extension.position j) := by
  exact arrowStep_reversePosition extension.reverseResult a _ _
    (extension.extension.toRightExtension.arrowStep_position a _ _
      (arrowStep_reversePosition C a i j hij))

/-- An inherited-position coefficient pair for a positive left-boundary
projection. -/
def LeftPositiveBoundaryExtension.projectionMorphismCoefficientPosition
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) :
    extension.result.MorphismCoefficientPosition C :=
  pairedMorphismCoefficientPosition C extension.result C
    (fun i ↦ extension.position i) (fun i ↦ i) i

/-- An inherited-position coefficient pair for a negative left-boundary
inclusion. -/
def LeftNegativeBoundaryExtension.inclusionMorphismCoefficientPosition
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) :
    C.MorphismCoefficientPosition extension.result :=
  pairedMorphismCoefficientPosition C C extension.result (fun i ↦ i)
    (fun i ↦ extension.position i) i

/-- All inherited pairs of a positive left-boundary projection lie in the
component of the original source position. -/
theorem LeftPositiveBoundaryExtension.projectionMorphismCoefficientPosition_eqvGen_source
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (extension.result.MorphismCoefficientStep C)
      (extension.projectionMorphismCoefficientPosition i)
      (extension.projectionMorphismCoefficientPosition C.sourcePosition) := by
  exact pairedMorphismCoefficientPosition_eqvGen_source
    C extension.result C (fun i ↦ extension.position i) (fun i ↦ i)
    (fun a i j hij ↦ extension.arrowStep_position a i j hij)
    (fun _ _ _ hij ↦ hij) i

/-- All inherited pairs of a negative left-boundary inclusion lie in the
component of the original source position. -/
theorem LeftNegativeBoundaryExtension.inclusionMorphismCoefficientPosition_eqvGen_source
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (C.MorphismCoefficientStep extension.result)
      (extension.inclusionMorphismCoefficientPosition i)
      (extension.inclusionMorphismCoefficientPosition C.sourcePosition) := by
  exact pairedMorphismCoefficientPosition_eqvGen_source
    C C extension.result (fun i ↦ i) (fun i ↦ extension.position i)
    (fun _ _ _ hij ↦ hij)
    (fun a i j hij ↦ extension.arrowStep_position a i j hij) i

/-- The positive left-boundary projection has coefficient one at the
inherited source position. -/
@[simp]
theorem LeftPositiveBoundaryExtension.moduleMap_morphismCoefficientAt_source
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) :
    extension.result.morphismCoefficientAt C hmono hmono
        (extension.moduleMap hmono)
        (extension.projectionMorphismCoefficientPosition C.sourcePosition) =
      1 := by
  change
    (show C.Space C.source from
      (extension.moduleMap hmono).app (Opposite.op (obj R C.source))
        (Finsupp.single (extension.position C.sourcePosition) 1))
        C.sourcePosition = 1
  rw [extension.moduleMap_app_single_position]
  simp

/-- Every nonzero coefficient of a positive left-boundary projection belongs
to its inherited-position component. -/
theorem LeftPositiveBoundaryExtension.moduleMap_coefficient_eqvGen_source
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R)
    (p : extension.result.MorphismCoefficientPosition C)
    (hp : extension.result.morphismCoefficientAt C hmono hmono
      (extension.moduleMap hmono) p ≠ 0) :
    Relation.EqvGen (extension.result.MorphismCoefficientStep C)
      (extension.projectionMorphismCoefficientPosition C.sourcePosition) p := by
  rcases p with ⟨x, i, j⟩
  by_cases hi : ∃ q : C.PositionAt x, extension.position q = i
  · rcases hi with ⟨q, rfl⟩
    change
      (show C.Space x from
        (extension.moduleMap hmono).app (Opposite.op (obj R x))
          (Finsupp.single (extension.position q) 1)) j ≠ 0 at hp
    rw [extension.moduleMap_app_single_position] at hp
    change (Finsupp.single q 1) j ≠ 0 at hp
    have hj : q = j := (Finsupp.single_apply_ne_zero.mp hp).1.symm
    subst j
    exact (LeftPositiveBoundaryExtension.projectionMorphismCoefficientPosition_eqvGen_source
      extension q).symm
  · change (extension.spaceProjection x (Finsupp.single i 1)) j ≠ 0 at hp
    rw [extension.spaceProjection_single_of_not_exists i 1 hi] at hp
    simp at hp

/-- The graph-basis component carrying a positive left-boundary projection. -/
def LeftPositiveBoundaryExtension.moduleMapComponent
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) :
    extension.result.BoundaryFreeMorphismCoefficientComponent C :=
  extension.result.boundaryFreeMorphismCoefficientComponentOf C
    (extension.projectionMorphismCoefficientPosition C.sourcePosition)
    (extension.result.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
      C hmono hmono
      (extension.moduleMap hmono) _ (by simp))

/-- A positive left-boundary projection is exactly its inherited-position
graph-basis map. -/
theorem LeftPositiveBoundaryExtension.moduleMap_eq_componentMap
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) :
    extension.moduleMap hmono =
      extension.result.boundaryFreeMorphismCoefficientComponentMap
        C hmono hmono (extension.moduleMapComponent hmono) := by
  simpa only [moduleMapComponent] using
    extension.result.eq_boundaryFreeMorphismCoefficientComponentMap_of_root
        C hmono hmono (extension.moduleMap hmono)
        (extension.projectionMorphismCoefficientPosition C.sourcePosition)
        (extension.moduleMap_morphismCoefficientAt_source hmono)
        (extension.moduleMap_coefficient_eqvGen_source hmono)

/-- Every inherited pair belongs to the component of a positive
left-boundary projection. -/
theorem LeftPositiveBoundaryExtension.moduleMapComponent_position_support
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (extension.result.MorphismCoefficientStep C)
      (extension.moduleMapComponent hmono).1.representative
      ⟨x, extension.position i, i⟩ := by
  let root := extension.projectionMorphismCoefficientPosition C.sourcePosition
  let hfree := isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
    extension.result C hmono hmono (extension.moduleMap hmono) root
      (by simp [root])
  have hrepresentative :=
    boundaryFreeMorphismCoefficientComponentOf_representative_eqvGen
      extension.result C root hfree
  have hi := extension.projectionMorphismCoefficientPosition_eqvGen_source i
  simpa only [moduleMapComponent,
    boundaryFreeMorphismCoefficientComponentOf, root,
    LeftPositiveBoundaryExtension.projectionMorphismCoefficientPosition,
    pairedMorphismCoefficientPosition] using
    Relation.EqvGen.trans _ _ _ hrepresentative hi.symm

/-- A positive left-boundary projection component has full support on its
target word. -/
theorem LeftPositiveBoundaryExtension.moduleMapComponent_hasFullOutputSupport
    {C : Word R} (extension : LeftPositiveBoundaryExtension C)
    (hmono : IsMonomial R) :
    (extension.moduleMapComponent hmono).HasFullOutputSupport := by
  intro x i
  exact ⟨extension.position i,
    extension.moduleMapComponent_position_support hmono i⟩

/-- The negative left-boundary inclusion has coefficient one at the inherited
source position. -/
@[simp]
theorem LeftNegativeBoundaryExtension.moduleMap_morphismCoefficientAt_source
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) :
    C.morphismCoefficientAt extension.result hmono hmono
        (extension.moduleMap hmono)
        (extension.inclusionMorphismCoefficientPosition C.sourcePosition) =
      1 := by
  change
    (show extension.result.Space C.source from
      (extension.moduleMap hmono).app (Opposite.op (obj R C.source))
        (Finsupp.single C.sourcePosition 1))
        (extension.position C.sourcePosition) = 1
  rw [extension.moduleMap_app_single]
  simp

/-- Every nonzero coefficient of a negative left-boundary inclusion belongs
to its inherited-position component. -/
theorem LeftNegativeBoundaryExtension.moduleMap_coefficient_eqvGen_source
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R)
    (p : C.MorphismCoefficientPosition extension.result)
    (hp : C.morphismCoefficientAt extension.result hmono hmono
      (extension.moduleMap hmono) p ≠ 0) :
    Relation.EqvGen (C.MorphismCoefficientStep extension.result)
      (extension.inclusionMorphismCoefficientPosition C.sourcePosition) p := by
  rcases p with ⟨x, i, j⟩
  change
    (show extension.result.Space x from
      (extension.moduleMap hmono).app (Opposite.op (obj R x))
        (Finsupp.single i 1)) j ≠ 0 at hp
  rw [extension.moduleMap_app_single] at hp
  change (Finsupp.single (extension.position i) 1) j ≠ 0 at hp
  have hj : extension.position i = j :=
    (Finsupp.single_apply_ne_zero.mp hp).1.symm
  subst j
  exact (extension.inclusionMorphismCoefficientPosition_eqvGen_source i).symm

/-- The graph-basis component carrying a negative left-boundary inclusion. -/
def LeftNegativeBoundaryExtension.moduleMapComponent
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) :
    C.BoundaryFreeMorphismCoefficientComponent extension.result :=
  C.boundaryFreeMorphismCoefficientComponentOf extension.result
    (extension.inclusionMorphismCoefficientPosition C.sourcePosition)
    (C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
      extension.result hmono hmono (extension.moduleMap hmono) _ (by simp))

/-- A negative left-boundary inclusion is exactly its inherited-position
graph-basis map. -/
theorem LeftNegativeBoundaryExtension.moduleMap_eq_componentMap
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) :
    extension.moduleMap hmono =
      C.boundaryFreeMorphismCoefficientComponentMap extension.result
        hmono hmono (extension.moduleMapComponent hmono) := by
  simpa only [moduleMapComponent] using
    C.eq_boundaryFreeMorphismCoefficientComponentMap_of_root
      extension.result hmono hmono (extension.moduleMap hmono)
      (extension.inclusionMorphismCoefficientPosition C.sourcePosition)
      (extension.moduleMap_morphismCoefficientAt_source hmono)
      (extension.moduleMap_coefficient_eqvGen_source hmono)

/-- Every inherited pair belongs to the component of a negative
left-boundary inclusion. -/
theorem LeftNegativeBoundaryExtension.moduleMapComponent_position_support
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) {x : Q} (i : C.PositionAt x) :
    Relation.EqvGen (C.MorphismCoefficientStep extension.result)
      (extension.moduleMapComponent hmono).1.representative
      ⟨x, i, extension.position i⟩ := by
  let root := extension.inclusionMorphismCoefficientPosition C.sourcePosition
  let hfree := C.isBoundaryFreeMorphismCoefficientComponent_of_ne_zero
    extension.result hmono hmono (extension.moduleMap hmono) root
      (by simp [root])
  have hrepresentative :=
    C.boundaryFreeMorphismCoefficientComponentOf_representative_eqvGen
      extension.result root hfree
  have hi := extension.inclusionMorphismCoefficientPosition_eqvGen_source i
  simpa only [moduleMapComponent,
    boundaryFreeMorphismCoefficientComponentOf, root,
    LeftNegativeBoundaryExtension.inclusionMorphismCoefficientPosition,
    pairedMorphismCoefficientPosition] using
    Relation.EqvGen.trans _ _ _ hrepresentative hi.symm

/-- A negative left-boundary inclusion component has full support on its
source word. -/
theorem LeftNegativeBoundaryExtension.moduleMapComponent_hasFullInputSupport
    {C : Word R} (extension : LeftNegativeBoundaryExtension C)
    (hmono : IsMonomial R) :
    (extension.moduleMapComponent hmono).HasFullInputSupport := by
  intro x i
  exact ⟨extension.position i,
    extension.moduleMapComponent_position_support hmono i⟩

/-- The graph-basis component carrying a left hook projection. -/
def LeftHookExtension.moduleMapComponent
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) :
    hook.result.BoundaryFreeMorphismCoefficientComponent C :=
  hook.toLeftPositiveBoundaryExtension.moduleMapComponent hmono

/-- A left hook projection is one graph-basis vector. -/
theorem LeftHookExtension.moduleMap_eq_componentMap
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) :
    hook.moduleMap hmono =
      hook.result.boundaryFreeMorphismCoefficientComponentMap C hmono hmono
        (hook.moduleMapComponent hmono) :=
  hook.toLeftPositiveBoundaryExtension.moduleMap_eq_componentMap hmono

/-- A left hook component covers every position of its target word. -/
theorem LeftHookExtension.moduleMapComponent_hasFullOutputSupport
    {C : Word R} (hook : LeftHookExtension C)
    (hmono : IsMonomial R) :
    (hook.moduleMapComponent hmono).HasFullOutputSupport :=
  hook.toLeftPositiveBoundaryExtension.moduleMapComponent_hasFullOutputSupport
    hmono

/-- A left hook and a right hook from the same extended word to the same base
word give different module maps.  At the initial position of the common
extended word, the right projection is the identity while the left projection
kills the basis vector. -/
theorem LeftHookExtension.moduleMap_ne_rightHook_moduleMap
    {C : Word R} (left : LeftHookExtension C)
    (right : HookExtension C left.result)
    (hmono : IsMonomial R) :
    left.moduleMap hmono ≠ right.moduleMap hmono := by
  intro hmaps
  let rightExtension := right.toPositiveBoundaryExtension.toRightExtension
  let j : left.result.PositionAt C.source :=
    rightExtension.position C.sourcePosition
  have hjnot : ¬ ∃ i : C.PositionAt C.source,
      left.toLeftPositiveBoundaryExtension.position i = j := by
    rintro ⟨i, hi⟩
    have hindex : left.steps + i.index = C.sourcePosition.index :=
      calc
        left.steps + i.index =
            (left.toLeftPositiveBoundaryExtension.position i).index := by
          rw [LeftPositiveBoundaryExtension.position_index]
          simp only [LeftHookExtension.steps,
            LeftHookExtension.toLeftPositiveBoundaryExtension,
            LeftPositiveBoundaryExtension.steps,
            HookExtension.toPositiveBoundaryExtension,
            PositiveBoundaryExtension.toRightExtension_steps,
            NegativeExtension.toRightExtension_steps,
            HookExtension.steps]
        _ = j.index := congrArg PositionAt.index hi
        _ = C.sourcePosition.index := by
          exact rightExtension.position_index C.sourcePosition
    rw [C.sourcePosition_index] at hindex
    have hsteps : 0 < left.steps := by
      simp only [LeftHookExtension.steps, HookExtension.steps]
      omega
    omega
  have happ := congrArg
    (fun f : left.result.rightModule hmono ⟶ C.rightModule hmono ↦
      (f.app (Opposite.op (obj R C.source))).hom
        (Finsupp.single j (1 : k))) hmaps
  change left.toLeftPositiveBoundaryExtension.spaceProjection C.source
      (Finsupp.single j (1 : k)) =
    rightExtension.spaceProjection C.source
      (Finsupp.single j (1 : k)) at happ
  rw [left.toLeftPositiveBoundaryExtension.spaceProjection_single_of_not_exists
      j 1 hjnot,
    rightExtension.spaceProjection_single_position C.sourcePosition 1] at happ
  have hcoordinate := congrArg (fun v ↦ v C.sourcePosition) happ
  simp at hcoordinate

/-- The graph components of a left hook and a right hook with the same
literal source word are distinct. -/
theorem LeftHookExtension.moduleMapComponent_ne_rightHook_moduleMapComponent
    {C : Word R} (left : LeftHookExtension C)
    (right : HookExtension C left.result)
    (hmono : IsMonomial R) :
    left.moduleMapComponent hmono ≠ right.moduleMapComponent hmono := by
  intro hcomponents
  apply left.moduleMap_ne_rightHook_moduleMap right hmono
  rw [left.moduleMap_eq_componentMap hmono,
    right.moduleMap_eq_componentMap hmono, hcomponents]

/-- A left-hook projection has coefficient zero on the different component
carrying the right-hook projection from the same extended word. -/
theorem LeftHookExtension.morphismCoefficientAt_moduleMap_rightHookComponent_eq_zero
    {C : Word R} (left : LeftHookExtension C)
    (right : HookExtension C left.result)
    (hmono : IsMonomial R) :
    left.result.morphismCoefficientAt C hmono hmono
      (left.moduleMap hmono)
      (right.moduleMapComponent hmono).1.representative = 0 := by
  rw [left.moduleMap_eq_componentMap hmono,
    left.result.morphismCoefficientAt_boundaryFreeComponentMap,
    left.result.coefficientComponentIndicator_eq_zero]
  intro heqv
  apply left.moduleMapComponent_ne_rightHook_moduleMapComponent right hmono
  apply Subtype.ext
  exact (left.result.representative_eqv_iff C _ _).1 heqv

/-- The graph-basis component carrying a left cohook inclusion. -/
def LeftCohookExtension.moduleMapComponent
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) :
    C.BoundaryFreeMorphismCoefficientComponent cohook.result :=
  cohook.toLeftNegativeBoundaryExtension.moduleMapComponent hmono

/-- A left cohook inclusion is one graph-basis vector. -/
theorem LeftCohookExtension.moduleMap_eq_componentMap
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) :
    cohook.moduleMap hmono =
      C.boundaryFreeMorphismCoefficientComponentMap cohook.result hmono hmono
        (cohook.moduleMapComponent hmono) :=
  cohook.toLeftNegativeBoundaryExtension.moduleMap_eq_componentMap hmono

/-- A left cohook component covers every position of its source word. -/
theorem LeftCohookExtension.moduleMapComponent_hasFullInputSupport
    {C : Word R} (cohook : LeftCohookExtension C)
    (hmono : IsMonomial R) :
    (cohook.moduleMapComponent hmono).HasFullInputSupport :=
  cohook.toLeftNegativeBoundaryExtension.moduleMapComponent_hasFullInputSupport
    hmono

/-- A left cohook and a right cohook from the same base word to the same
literal extended word give different module maps.  Their images of the
initial basis vector occupy different positions. -/
theorem LeftCohookExtension.moduleMap_ne_rightCohook_moduleMap
    {C : Word R} (left : LeftCohookExtension C)
    (right : CohookExtension C left.result)
    (hmono : IsMonomial R) :
    left.moduleMap hmono ≠ right.moduleMap hmono := by
  intro hmaps
  let rightExtension := right.toNegativeBoundaryExtension.toRightExtension
  let leftPosition : left.result.PositionAt C.source :=
    left.position C.sourcePosition
  let rightPosition : left.result.PositionAt C.source :=
    rightExtension.position C.sourcePosition
  have hpositions : leftPosition ≠ rightPosition := by
    intro hposition
    have hindex := congrArg PositionAt.index hposition
    have hleftIndex : leftPosition.index = left.steps := by
      calc
        leftPosition.index =
            (left.toLeftNegativeBoundaryExtension.position
              C.sourcePosition).index := rfl
        _ = left.toLeftNegativeBoundaryExtension.steps +
            C.sourcePosition.index :=
          LeftNegativeBoundaryExtension.position_index _ _
        _ = left.steps := by
          simp only [C.sourcePosition_index, Nat.add_zero,
            LeftCohookExtension.steps,
            LeftCohookExtension.toLeftNegativeBoundaryExtension,
            LeftNegativeBoundaryExtension.steps,
            CohookExtension.toNegativeBoundaryExtension,
            NegativeBoundaryExtension.toRightExtension_steps,
            PositiveExtension.toRightExtension_steps,
            CohookExtension.steps]
    have hrightIndex : rightPosition.index = 0 := by
      simp only [rightPosition, rightExtension,
        RightExtension.position_index, C.sourcePosition_index]
    rw [hleftIndex, hrightIndex] at hindex
    have hsteps : 0 < left.steps := by
      simp only [LeftCohookExtension.steps, CohookExtension.steps]
      omega
    omega
  have happ := congrArg
    (fun f : C.rightModule hmono ⟶ left.result.rightModule hmono ↦
      (f.app (Opposite.op (obj R C.source))).hom
        (Finsupp.single C.sourcePosition (1 : k))) hmaps
  have himages : Finsupp.single leftPosition (1 : k) =
      Finsupp.single rightPosition (1 : k) := by
    change left.toLeftNegativeBoundaryExtension.spaceInclusion C.source
        (Finsupp.single C.sourcePosition 1) =
      rightExtension.spaceInclusion C.source
        (Finsupp.single C.sourcePosition 1) at happ
    rw [LeftNegativeBoundaryExtension.spaceInclusion_single,
      RightExtension.spaceInclusion_single] at happ
    exact happ
  have hcoordinate := congrArg (fun v ↦ v rightPosition) himages
  simp [hpositions] at hcoordinate

/-- The graph components of literal left and right cohook inclusions are
distinct. -/
theorem LeftCohookExtension.moduleMapComponent_ne_rightCohook_moduleMapComponent
    {C : Word R} (left : LeftCohookExtension C)
    (right : CohookExtension C left.result)
    (hmono : IsMonomial R) :
    left.moduleMapComponent hmono ≠ right.moduleMapComponent hmono := by
  intro hcomponents
  apply left.moduleMap_ne_rightCohook_moduleMap right hmono
  rw [left.moduleMap_eq_componentMap hmono,
    right.moduleMap_eq_componentMap hmono, hcomponents]

/-- A left-cohook inclusion has coefficient zero on the different component
carrying the right-cohook inclusion into the same literal result word. -/
theorem LeftCohookExtension.morphismCoefficientAt_moduleMap_rightCohookComponent_eq_zero
    {C : Word R} (left : LeftCohookExtension C)
    (right : CohookExtension C left.result)
    (hmono : IsMonomial R) :
    C.morphismCoefficientAt left.result hmono hmono
      (left.moduleMap hmono)
      (right.moduleMapComponent hmono).1.representative = 0 := by
  rw [left.moduleMap_eq_componentMap hmono,
    C.morphismCoefficientAt_boundaryFreeComponentMap,
    C.coefficientComponentIndicator_eq_zero]
  intro heqv
  apply left.moduleMapComponent_ne_rightCohook_moduleMapComponent right hmono
  apply Subtype.ext
  exact (C.representative_eqv_iff left.result _ _).1 heqv

end MagnitudeConjecture.BoundQuiver.StringWord.Word
