import MagnitudeConjecture.Algebra.StringDetectorBoundary
import MagnitudeConjecture.CategoryTheory.LinearModuleDeckShift
import MagnitudeConjecture.CategoryTheory.OppositeLinear
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The finite-string detecting functors

For `C` in Butler--Ringel's `W(u,t)`, this file constructs the detecting
quotient

`(1^+ ∩ C^+) / ((1^+ ∩ C^-) + (1^- ∩ C^+))`

as a functor from linear modules over the bound path category to
`ModuleCat k`.  Here `1` is the oppositely polarized trivial word
`1_(u,not t)`.  The subspace naturality proved in the preceding files gives
the induced quotient maps and the functor laws.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization} {u₀ : Q} {t : Bool}

namespace EndpointWord

/-- The oppositely polarized trivial word `1_(u,not t)` used in the detector
indexed by `C ∈ W(u,t)`. -/
def oppositeVertex (_C : EndpointWord S u₀ t) :
    EndpointWord S u₀ (Bool.not t) :=
  EndpointWord.vertex P S u₀ (Bool.not t)

@[simp]
theorem oppositeVertex_path (C : EndpointWord S u₀ t) :
    C.oppositeVertex.path = Quiver.Path.nil :=
  rfl

@[simp]
theorem upperSubspace_oppositeVertex
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
  upperSubspace N C.oppositeVertex =
      upperBoundarySubspace N C.oppositeVertex := by
  unfold upperSubspace
  change signedPathSubspace N (Quiver.Path.nil : SignedPath u₀ u₀)
      (upperBoundarySubspace N C.oppositeVertex) = _
  exact signedPathSubspace_nil N _

@[simp]
theorem lowerSubspace_oppositeVertex
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
  lowerSubspace N C.oppositeVertex =
      lowerBoundarySubspace N C.oppositeVertex := by
  unfold lowerSubspace
  change signedPathSubspace N (Quiver.Path.nil : SignedPath u₀ u₀)
      (lowerBoundarySubspace N C.oppositeVertex) = _
  exact signedPathSubspace_nil N _

/-- The numerator `1^+ ∩ C^+` of the detecting quotient. -/
def detectorNumerator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u₀))) :=
  upperSubspace N C.oppositeVertex ⊓ upperSubspace N C

/-- The denominator `(1^+ ∩ C^-) + (1^- ∩ C^+)` of the detecting quotient. -/
def detectorDenominator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u₀))) :=
  (upperSubspace N C.oppositeVertex ⊓ lowerSubspace N C) ⊔
    (lowerSubspace N C.oppositeVertex ⊓ upperSubspace N C)

/-- The detector denominator lies in its numerator. -/
theorem detectorDenominator_le_detectorNumerator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive] (C : EndpointWord S u₀ t) :
    detectorDenominator N C ≤ detectorNumerator N C := by
  apply sup_le
  · exact inf_le_inf le_rfl (lowerSubspace_le_upperSubspace N C)
  · exact inf_le_inf
      (lowerSubspace_le_upperSubspace N C.oppositeVertex) le_rfl

/-- The denominator regarded as a submodule of the numerator. -/
def detectorDenominatorInNumerator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    Submodule k (detectorNumerator N C) :=
  (detectorDenominator N C).comap (detectorNumerator N C).subtype

/-- The underlying vector space of the Butler--Ringel detector. -/
abbrev DetectorSpace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :=
  (detectorNumerator N C) ⧸ detectorDenominatorInNumerator N C

/-- The detector numerator is preserved by a module morphism. -/
theorem detectorNumerator_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t) :
    (detectorNumerator M C).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations u₀))).hom ≤
      detectorNumerator N C := by
  rintro z ⟨v, hv, rfl⟩
  constructor
  · apply upperSubspace_map_le f C.oppositeVertex
    exact ⟨v, hv.1, rfl⟩
  · apply upperSubspace_map_le f C
    exact ⟨v, hv.2, rfl⟩

/-- The detector denominator is preserved by a module morphism. -/
theorem detectorDenominator_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t) :
    (detectorDenominator M C).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations u₀))).hom ≤
      detectorDenominator N C := by
  rw [detectorDenominator, Submodule.map_sup]
  apply sup_le
  · apply (Submodule.map_inf_le _).trans
    exact (inf_le_inf
      (upperSubspace_map_le f C.oppositeVertex)
      (lowerSubspace_map_le f C)).trans le_sup_left
  · apply (Submodule.map_inf_le _).trans
    exact (inf_le_inf
      (lowerSubspace_map_le f C.oppositeVertex)
      (upperSubspace_map_le f C)).trans le_sup_right

/-- Restriction of a module morphism to the detector numerators. -/
def detectorNumeratorMap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t) :
    detectorNumerator M C →ₗ[k] detectorNumerator N C :=
  LinearMap.codRestrict (detectorNumerator N C)
    ((f.app (Opposite.op
      (obj P.toPresentation.relations u₀))).hom.domRestrict
        (detectorNumerator M C)) (by
      rintro ⟨v, hv⟩
      apply detectorNumerator_map_le f C
      exact ⟨v, hv, rfl⟩)

@[simp]
theorem detectorNumeratorMap_coe
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t)
    (x : detectorNumerator M C) :
    (detectorNumeratorMap f C x :
      N.obj (Opposite.op (obj P.toPresentation.relations u₀))) =
        f.app (Opposite.op
          (obj P.toPresentation.relations u₀)) x :=
  rfl

/-- The restricted numerator map preserves the denominator submodules. -/
theorem detectorDenominatorInNumerator_le_comap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t) :
    detectorDenominatorInNumerator M C ≤
      (detectorDenominatorInNumerator N C).comap
        (detectorNumeratorMap f C) := by
  rintro ⟨v, hvnum⟩ hvden
  change f.app (Opposite.op
      (obj P.toPresentation.relations u₀)) v ∈ detectorDenominator N C
  apply detectorDenominator_map_le f C
  exact ⟨v, hvden, rfl⟩

/-- The linear map induced on detector quotients. -/
def detectorLinearMap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t) :
    DetectorSpace M C →ₗ[k] DetectorSpace N C :=
  Submodule.mapQ
    (detectorDenominatorInNumerator M C)
    (detectorDenominatorInNumerator N C)
    (detectorNumeratorMap f C)
    (detectorDenominatorInNumerator_le_comap f C)

@[simp]
theorem detectorLinearMap_mk
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t)
    (x : detectorNumerator M C) :
    detectorLinearMap f C (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (detectorNumeratorMap f C x) := by
  exact Submodule.mapQ_apply _ _ _ x

open MagnitudeConjecture.CoveringHom

/-- The Butler--Ringel detector associated to an endpoint word. -/
def detectorFunctor (C : EndpointWord S u₀ t) :
    LinearModuleCategory
        (C := (Category P.toPresentation.relations)ᵒᵖ) k ⥤
      ModuleCat.{u} k where
  obj N := ModuleCat.of k (DetectorSpace N.obj C)
  map {M N} f := ModuleCat.ofHom (detectorLinearMap f.hom C)
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

instance detectorFunctor_additive (C : EndpointWord S u₀ t) :
    C.detectorFunctor.Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

instance detectorFunctor_linear (C : EndpointWord S u₀ t) :
    C.detectorFunctor.Linear k where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

end EndpointWord

end MagnitudeConjecture.BoundQuiver.StringWord
