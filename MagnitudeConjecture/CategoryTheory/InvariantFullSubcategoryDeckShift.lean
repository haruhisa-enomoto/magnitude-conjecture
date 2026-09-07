import MagnitudeConjecture.CategoryTheory.DeckShiftAction
import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive

/-!
# Coherent deck shifts on invariant full subcategories

A full subcategory preserved both by the object action and by the chosen
coherent shift functors inherits the whole deck-shift package.  The shift
coherence is Mathlib's canonical full-subcategory coherence, so the inclusion
automatically commutes with shifts.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C]

/-- Invariance data for restricting a coherent deck shift to a full
subcategory.  The two clauses are kept explicit because the chosen shift
functor need only be isomorphic, rather than definitionally equal, to the
corresponding object action. -/
structure InvariantFullSubcategoryData
    (D : CoherentDeckShift C G) (P : ObjectProperty C) where
  smul_mem : ∀ (g : G) (X : C), P X → P (g • X)
  shift_mem : ∀ (a : Additive G) (X : C), P X → P ((D.core.F a).obj X)

/-- The restricted object action on an invariant full subcategory. -/
@[implicit_reducible]
def InvariantFullSubcategoryData.mulAction
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P) :
    MulAction G P.FullSubcategory where
  smul g X := ⟨g • X.obj, H.smul_mem g X.obj X.property⟩
  one_smul X := by
    apply ObjectProperty.FullSubcategory.ext
    exact one_smul G X.obj
  mul_smul g h X := by
    apply ObjectProperty.FullSubcategory.ext
    exact mul_smul g h X.obj

/-- Freeness/cancellation of the ambient object action descends to the
invariant full subcategory. -/
theorem InvariantFullSubcategoryData.isCancelSMul
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P) [IsCancelSMul G C] :
    letI := H.mulAction
    IsCancelSMul G P.FullSubcategory := by
  letI := H.mulAction
  exact
    { left_cancel' := by
        intro g X Y h
        apply ObjectProperty.FullSubcategory.ext
        exact IsLeftCancelSMul.left_cancel g X.obj Y.obj
          (congrArg ObjectProperty.FullSubcategory.obj h)
      right_cancel' := by
        intro g h X hgh
        exact IsCancelSMul.right_cancel g h X.obj
          (congrArg ObjectProperty.FullSubcategory.obj hgh) }

private noncomputable def shiftMkCoreOfHasShift
    {B : Type u} [Category.{v} B]
    {A : Type w} [AddMonoid A] [HasShift B A] :
    ShiftMkCore B A where
  F := shiftFunctor B
  zero := shiftFunctorZero B A
  add := shiftFunctorAdd B
  assoc_hom_app := by
    intro a b c X
    simpa [shiftFunctorAdd'] using
      shiftFunctorAdd_assoc_hom_app a b c X
  zero_add_hom_app := shiftFunctorAdd_zero_add_hom_app
  add_zero_hom_app := shiftFunctorAdd_add_zero_hom_app

/-- Explicit shift invariance supplies Mathlib's stable-object-property
interface for the ambient coherent deck shift. -/
theorem InvariantFullSubcategoryData.isStableUnderShift
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P) :
    letI := D.hasShift
    P.IsStableUnderShift (Additive G) := by
  letI := D.hasShift
  exact
    { isStableUnderShiftBy := fun a ↦
        { le_shift := fun X hX ↦ H.shift_mem a X hX } }

/-- A coherent deck shift restricts to every invariant full subcategory.  Its
shift core is rebuilt from Mathlib's canonical full-subcategory shift. -/
def InvariantFullSubcategoryData.coherentDeckShift
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P) :
    letI := H.mulAction
    CoherentDeckShift P.FullSubcategory G := by
  letI := D.hasShift
  letI := H.isStableUnderShift
  letI := H.mulAction
  exact
    { core := shiftMkCoreOfHasShift
      objIso := fun g X ↦
        P.isoMk ((P.ι.commShiftIso (Additive.ofMul g)).app X ≪≫
          D.objIso g X.obj) }

/-- The shift instance exported by the restricted coherent package is the
canonical full-subcategory shift from which its core was built. -/
theorem InvariantFullSubcategoryData.hasShift_eq
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P) :
    letI := D.hasShift
    letI := H.isStableUnderShift
    letI := H.mulAction
    (H.coherentDeckShift).hasShift = ObjectProperty.hasShift P := by
  letI := D.hasShift
  letI := H.isStableUnderShift
  letI := H.mulAction
  unfold InvariantFullSubcategoryData.coherentDeckShift
    CoherentDeckShift.hasShift shiftMkCoreOfHasShift
    ObjectProperty.hasShift
  rfl

/-- The inclusion of an invariant full subcategory commutes with its
restricted coherent deck shift and the ambient deck shift. -/
@[implicit_reducible]
noncomputable def InvariantFullSubcategoryData.inclusionCommShift
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P) :
    letI := H.mulAction
    let R := H.coherentDeckShift
    letI := R.hasShift
    letI := D.hasShift
    P.ι.CommShift (Additive G) := by
  letI := D.hasShift
  letI := H.isStableUnderShift
  letI := H.mulAction
  dsimp only
  change @Functor.CommShift _ _ _ _ P.ι (Additive G) _
    (H.coherentDeckShift.hasShift) D.hasShift
  rw [H.hasShift_eq]
  infer_instance

omit [MulAction G C] in
set_option backward.isDefEq.respectTransparency false in
/-- For Mathlib's canonical shift on a stable full subcategory, the
shift-commutation isomorphism of the inclusion is the identity after
forgetting the object wrapper. -/
theorem fullSubcategoryInclusionCommShift_hom_app_heq
    [HasShift C (Additive G)]
    {P : ObjectProperty C} [P.IsStableUnderShift (Additive G)]
    (a : Additive G) (X : P.FullSubcategory) :
    letI : HasShift P.FullSubcategory (Additive G) :=
      ObjectProperty.hasShift P
    letI : P.ι.CommShift (Additive G) := ObjectProperty.commShiftι P
    HEq ((P.ι.commShiftIso a).hom.app X)
      (𝟙 ((shiftFunctor C a).obj X.obj)) := by
  letI : HasShift P.FullSubcategory (Additive G) :=
    ObjectProperty.hasShift P
  letI : P.ι.CommShift (Additive G) := ObjectProperty.commShiftι P
  unfold Functor.commShiftIso ObjectProperty.commShiftι ObjectProperty.hasShift
  change HEq
    ((P.liftCompιIso (P.ι ⋙ shiftFunctor C a) _).hom.app X)
    (𝟙 ((shiftFunctor C a).obj X.obj))
  rfl

omit [MulAction G C] in
set_option backward.isDefEq.respectTransparency false in
/-- Equality-transport form of the canonical full-subcategory inclusion
shift comparison. -/
theorem fullSubcategoryInclusionCommShift_hom_app
    [HasShift C (Additive G)]
    {P : ObjectProperty C} [P.IsStableUnderShift (Additive G)]
    (a : Additive G) (X : P.FullSubcategory) :
    letI : HasShift P.FullSubcategory (Additive G) :=
      ObjectProperty.hasShift P
    letI : P.ι.CommShift (Additive G) := ObjectProperty.commShiftι P
    (P.ι.commShiftIso a).hom.app X = eqToHom (by
      change
        ((@shiftFunctor P.FullSubcategory (Additive G) _ _
          (ObjectProperty.hasShift P) a).obj X).obj =
          (shiftFunctor C a).obj X.obj
      unfold ObjectProperty.hasShift
      rfl) := by
  letI : HasShift P.FullSubcategory (Additive G) :=
    ObjectProperty.hasShift P
  letI : P.ι.CommShift (Additive G) := ObjectProperty.commShiftι P
  unfold Functor.commShiftIso ObjectProperty.commShiftι ObjectProperty.hasShift
  change
    (P.liftCompιIso (P.ι ⋙ shiftFunctor C a) _).hom.app X = eqToHom _
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical identity formula transported to a coherent deck shift on
an invariant full subcategory. -/
theorem InvariantFullSubcategoryData.inclusionCommShift_hom_app_heq
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P)
    (a : Additive G) (X : P.FullSubcategory) :
    letI := H.mulAction
    let R := H.coherentDeckShift
    letI := R.hasShift
    letI := D.hasShift
    letI : P.ι.CommShift (Additive G) := H.inclusionCommShift
    HEq ((P.ι.commShiftIso a).hom.app X)
      (𝟙 ((shiftFunctor C a).obj X.obj)) := by
  letI := D.hasShift
  letI := H.isStableUnderShift
  letI := H.mulAction
  let R := H.coherentDeckShift
  letI := R.hasShift
  letI : P.ι.CommShift (Additive G) := H.inclusionCommShift
  dsimp only
  unfold Functor.commShiftIso InvariantFullSubcategoryData.inclusionCommShift
  unfold InvariantFullSubcategoryData.coherentDeckShift
    CoherentDeckShift.hasShift shiftMkCoreOfHasShift
    ObjectProperty.commShiftι ObjectProperty.hasShift
  change HEq
    ((P.liftCompιIso (P.ι ⋙ shiftFunctor C a) _).hom.app X)
    (𝟙 ((shiftFunctor C a).obj X.obj))
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Equality-transport form of the inclusion shift comparison inherited by
an invariant full subcategory. -/
theorem InvariantFullSubcategoryData.inclusionCommShift_hom_app
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P)
    (a : Additive G) (X : P.FullSubcategory) :
    letI := H.mulAction
    let R := H.coherentDeckShift
    letI := R.hasShift
    letI := D.hasShift
    letI : P.ι.CommShift (Additive G) := H.inclusionCommShift
    (P.ι.commShiftIso a).hom.app X = eqToHom (by
      change
        ((@shiftFunctor P.FullSubcategory (Additive G) _ _
          R.hasShift a).obj X).obj =
          (@shiftFunctor C (Additive G) _ _ D.hasShift a).obj X.obj
      unfold R InvariantFullSubcategoryData.coherentDeckShift
        CoherentDeckShift.hasShift shiftMkCoreOfHasShift
      unfold ObjectProperty.hasShift
      rfl) := by
  letI := D.hasShift
  letI := H.isStableUnderShift
  letI := H.mulAction
  let R := H.coherentDeckShift
  letI := R.hasShift
  letI : P.ι.CommShift (Additive G) := H.inclusionCommShift
  dsimp only
  unfold Functor.commShiftIso InvariantFullSubcategoryData.inclusionCommShift
  unfold InvariantFullSubcategoryData.coherentDeckShift
    CoherentDeckShift.hasShift shiftMkCoreOfHasShift
    ObjectProperty.commShiftι ObjectProperty.hasShift
  change
    (P.liftCompιIso (P.ι ⋙ shiftFunctor C a) _).hom.app X = eqToHom _
  rfl

section Linear

variable {k : Type*} [Semiring k] [Preadditive C]
  [CategoryTheory.Linear k C]

noncomputable instance InvariantFullSubcategoryData.functor_additive
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P)
    [∀ a : Additive G, (D.core.F a).Additive]
    (a : Additive G) :
    letI := H.mulAction
    (((H.coherentDeckShift).core.F a).Additive) := by
  letI := D.hasShift
  letI := H.isStableUnderShift
  letI := H.mulAction
  letI : (shiftFunctor C a).Additive := by
    change (D.core.F a).Additive
    infer_instance
  dsimp only [InvariantFullSubcategoryData.coherentDeckShift]
  change (shiftFunctor P.FullSubcategory a).Additive
  infer_instance

noncomputable instance InvariantFullSubcategoryData.functor_linear
    {D : CoherentDeckShift C G} {P : ObjectProperty C}
    (H : InvariantFullSubcategoryData D P)
    [∀ a : Additive G, (D.core.F a).Linear k]
    (a : Additive G) :
    letI := H.mulAction
    (((H.coherentDeckShift).core.F a).Linear k) := by
  letI := D.hasShift
  letI := H.isStableUnderShift
  letI := H.mulAction
  letI : (shiftFunctor C a).Linear k := by
    change (D.core.F a).Linear k
    infer_instance
  dsimp only [InvariantFullSubcategoryData.coherentDeckShift]
  let F := shiftFunctor P.FullSubcategory a
  have hcomp : (F ⋙ P.ι).Linear k :=
    Functor.linear_of_iso k (P.ι.commShiftIso a).symm
  refine { map_smul := fun {X Y} f r ↦ ?_ }
  apply P.ι.map_injective
  change P.ι.map (F.map (r • f)) = P.ι.map (r • F.map f)
  rw [P.ι.map_smul]
  exact hcomp.map_smul f r

end Linear

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
