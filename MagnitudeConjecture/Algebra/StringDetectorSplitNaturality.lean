import MagnitudeConjecture.Algebra.StringDetectorSplit

/-!
# Naturality of contextual split detectors

A module morphism preserves the four contextual filtration subspaces at a
fixed cut of a complete string.  It therefore induces a map on the contextual
detector quotient.  This is the vertical map used in the change-of-split
naturality square.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable {P : SpecialBiserialPresentation k A Q}
variable {S : P.ArrowPolarization}

variable {E : Word P.toPresentation.relations} {c : E.Split}

theorem splitRightLower_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split) :
    (splitRightLower M S E c).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations c.vertex))).hom ≤
      splitRightLower N S E c := by
  exact (signedPathSubspace_map_le f c.prefixPath
    (lowerBoundarySubspace M (detectorEndpoint S E).sourceVertex)).trans
      (signedPathSubspace_mono N c.prefixPath
        (lowerBoundarySubspace_map_le f
          (detectorEndpoint S E).sourceVertex))

theorem splitRightUpper_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split) :
    (splitRightUpper M S E c).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations c.vertex))).hom ≤
      splitRightUpper N S E c := by
  exact (signedPathSubspace_map_le f c.prefixPath
    (upperBoundarySubspace M (detectorEndpoint S E).sourceVertex)).trans
      (signedPathSubspace_mono N c.prefixPath
        (upperBoundarySubspace_map_le f
          (detectorEndpoint S E).sourceVertex))

theorem splitLeftLower_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split) :
    (splitLeftLower M S E c).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations c.vertex))).hom ≤
      splitLeftLower N S E c := by
  exact (signedPathSubspace_map_le f c.suffixPath.reverse
    (lowerBoundarySubspace M (detectorEndpoint S E).oppositeVertex)).trans
      (signedPathSubspace_mono N c.suffixPath.reverse
        (lowerBoundarySubspace_map_le f
          (detectorEndpoint S E).oppositeVertex))

theorem splitLeftUpper_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split) :
    (splitLeftUpper M S E c).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations c.vertex))).hom ≤
      splitLeftUpper N S E c := by
  exact (signedPathSubspace_map_le f c.suffixPath.reverse
    (upperBoundarySubspace M (detectorEndpoint S E).oppositeVertex)).trans
      (signedPathSubspace_mono N c.suffixPath.reverse
        (upperBoundarySubspace_map_le f
          (detectorEndpoint S E).oppositeVertex))

theorem splitDetectorNumerator_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split) :
    (splitDetectorNumerator M S E c).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations c.vertex))).hom ≤
      splitDetectorNumerator N S E c := by
  rintro z ⟨v, hv, rfl⟩
  constructor
  · apply splitLeftUpper_map_le f S E c
    exact ⟨v, hv.1, rfl⟩
  · apply splitRightUpper_map_le f S E c
    exact ⟨v, hv.2, rfl⟩

theorem splitDetectorDenominator_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split) :
    (splitDetectorDenominator M S E c).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations c.vertex))).hom ≤
      splitDetectorDenominator N S E c := by
  rw [splitDetectorDenominator, Submodule.map_sup]
  apply sup_le
  · apply (Submodule.map_inf_le _).trans
    exact (inf_le_inf (splitLeftUpper_map_le f S E c)
      (splitRightLower_map_le f S E c)).trans le_sup_left
  · apply (Submodule.map_inf_le _).trans
    exact (inf_le_inf (splitLeftLower_map_le f S E c)
      (splitRightUpper_map_le f S E c)).trans le_sup_right

/-- Restriction of a module morphism to contextual split numerators. -/
def splitDetectorNumeratorMap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split) :
    splitDetectorNumerator M S E c →ₗ[k]
      splitDetectorNumerator N S E c :=
  LinearMap.codRestrict (splitDetectorNumerator N S E c)
    ((f.app (Opposite.op
      (obj P.toPresentation.relations c.vertex))).hom.domRestrict
        (splitDetectorNumerator M S E c)) (by
      intro x
      apply splitDetectorNumerator_map_le f S E c
      exact ⟨x, x.2, rfl⟩)

@[simp]
theorem splitDetectorNumeratorMap_coe
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split)
    (x : splitDetectorNumerator M S E c) :
    (splitDetectorNumeratorMap f S E c x :
      N.obj (Opposite.op (obj P.toPresentation.relations c.vertex))) =
        f.app (Opposite.op
          (obj P.toPresentation.relations c.vertex)) x :=
  rfl

theorem splitDetectorDenominatorInNumerator_le_comap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split) :
    splitDetectorDenominatorInNumerator M S E c ≤
      (splitDetectorDenominatorInNumerator N S E c).comap
        (splitDetectorNumeratorMap f S E c) := by
  rintro ⟨v, hvnum⟩ hvden
  change f.app (Opposite.op
      (obj P.toPresentation.relations c.vertex)) v ∈
    splitDetectorDenominator N S E c
  apply splitDetectorDenominator_map_le f S E c
  exact ⟨v, hvden, rfl⟩

/-- Linear map induced on a contextual split detector. -/
def splitDetectorLinearMap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split) :
    SplitDetectorSpace M S E c →ₗ[k] SplitDetectorSpace N S E c :=
  Submodule.mapQ
    (splitDetectorDenominatorInNumerator M S E c)
    (splitDetectorDenominatorInNumerator N S E c)
    (splitDetectorNumeratorMap f S E c)
    (splitDetectorDenominatorInNumerator_le_comap f S E c)

@[simp]
theorem splitDetectorLinearMap_mk
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations) (c : E.Split)
    (x : splitDetectorNumerator M S E c) :
    splitDetectorLinearMap f S E c (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (splitDetectorNumeratorMap f S E c x) := by
  exact Submodule.mapQ_apply _ _ _ x

/-- At the target cut, the contextual detector map is the canonical endpoint
detector map, under the target-cut identifications. -/
theorem splitDetectorLinearMap_target
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive]
    (f : M ⟶ N) (S : P.ArrowPolarization)
    (E : Word P.toPresentation.relations)
    (q : SplitDetectorSpace M S E (.target E)) :
    splitDetectorSpaceTargetEquiv N S E
        (splitDetectorLinearMap f S E (.target E) q) =
      detectorLinearMap f (detectorEndpoint S E)
        (splitDetectorSpaceTargetEquiv M S E q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [splitDetectorLinearMap_mk,
        splitDetectorSpaceTargetEquiv_mk,
        splitDetectorSpaceTargetEquiv_mk,
        detectorLinearMap_mk]
      rfl

/-- Change of split across a positive letter commutes with module
morphisms. -/
theorem splitDetectorLinearMap_positiveStep
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.PositiveStep d)
    (q : SplitDetectorSpace M S E c) :
    splitDetectorSpacePositiveStepEquiv N S E step
        (splitDetectorLinearMap f S E c q) =
      splitDetectorLinearMap f S E d
        (splitDetectorSpacePositiveStepEquiv M S E step q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [splitDetectorLinearMap_mk,
        splitDetectorSpacePositiveStepEquiv_mk,
        splitDetectorSpacePositiveStepEquiv_mk,
        splitDetectorLinearMap_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      have hnat := f.naturality
        (BoundQuiver.arrowMap P.toPresentation.relations step.arrow).op
      have happly := congrArg (fun g ↦ g.hom x.1) hnat
      simpa only [moduleArrowMap, ModuleCat.comp_apply,
        splitDetectorNumeratorMap_coe] using happly.symm

/-- The natural arrow-direction map across a negative letter, namely the
inverse of change of split, commutes with module morphisms. -/
theorem splitDetectorLinearMap_negativeStep_symm
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.NegativeStep d)
    (q : SplitDetectorSpace M S E d) :
    (splitDetectorSpaceNegativeStepEquiv N S E step).symm
        (splitDetectorLinearMap f S E d q) =
      splitDetectorLinearMap f S E c
        ((splitDetectorSpaceNegativeStepEquiv M S E step).symm q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [splitDetectorLinearMap_mk,
        splitDetectorSpaceNegativeStepEquiv_symm_mk,
        splitDetectorSpaceNegativeStepEquiv_symm_mk,
        splitDetectorLinearMap_mk]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      have hnat := f.naturality
        (BoundQuiver.arrowMap P.toPresentation.relations step.arrow).op
      have happly := congrArg (fun g ↦ g.hom x.1) hnat
      simpa only [moduleArrowMap, ModuleCat.comp_apply,
        splitDetectorNumeratorMap_coe] using happly.symm

/-- Change of split across a negative letter commutes with module
morphisms. -/
theorem splitDetectorLinearMap_negativeStep
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    [M.Additive] [N.Additive] (f : M ⟶ N)
    (S : P.ArrowPolarization) (E : Word P.toPresentation.relations)
    {c d : E.Split} (step : c.NegativeStep d)
    (q : SplitDetectorSpace M S E c) :
    splitDetectorSpaceNegativeStepEquiv N S E step
        (splitDetectorLinearMap f S E c q) =
      splitDetectorLinearMap f S E d
        (splitDetectorSpaceNegativeStepEquiv M S E step q) := by
  apply (splitDetectorSpaceNegativeStepEquiv N S E step).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  rw [splitDetectorLinearMap_negativeStep_symm]
  rw [LinearEquiv.symm_apply_apply]

end MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord
