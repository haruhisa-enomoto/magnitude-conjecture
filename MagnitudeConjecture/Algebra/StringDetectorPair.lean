import MagnitudeConjecture.Algebra.StringDetectorFunctor

/-!
# Pair-position string detectors

Ringel's filtration uses a detector at every split position of a string.  At
a vertex `u`, such a split is represented by endpoint words with opposite
polarizations.  This file packages the corresponding subquotient

`(L⁺ ∩ R⁺) / ((L⁺ ∩ R⁻) + (L⁻ ∩ R⁺))`

and its functorial action.  The detector already used in the campaign is the
special case in which `L` is the oppositely polarized trivial word.
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
variable {S : P.ArrowPolarization} {u₀ : Q} {t : Bool}

/-- Numerator of the detector at a split position. -/
def pairDetectorNumerator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u₀))) :=
  upperSubspace N L ⊓ upperSubspace N R

/-- Denominator of the detector at a split position. -/
def pairDetectorDenominator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Submodule k (N.obj (Opposite.op
      (obj P.toPresentation.relations u₀))) :=
  (upperSubspace N L ⊓ lowerSubspace N R) ⊔
    (lowerSubspace N L ⊓ upperSubspace N R)

/-- The pair denominator lies in the pair numerator. -/
theorem pairDetectorDenominator_le_pairDetectorNumerator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    [N.Additive]
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    pairDetectorDenominator N L R ≤ pairDetectorNumerator N L R := by
  apply sup_le
  · exact inf_le_inf le_rfl (lowerSubspace_le_upperSubspace N R)
  · exact inf_le_inf (lowerSubspace_le_upperSubspace N L) le_rfl

/-- The pair denominator as a submodule of the pair numerator. -/
def pairDetectorDenominatorInNumerator
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    Submodule k (pairDetectorNumerator N L R) :=
  (pairDetectorDenominator N L R).comap
    (pairDetectorNumerator N L R).subtype

/-- Underlying vector space of the detector at a split position. -/
abbrev PairDetectorSpace
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :=
  (pairDetectorNumerator N L R) ⧸
    pairDetectorDenominatorInNumerator N L R

/-- A module morphism preserves pair numerators. -/
theorem pairDetectorNumerator_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    (pairDetectorNumerator M L R).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations u₀))).hom ≤
      pairDetectorNumerator N L R := by
  rintro z ⟨v, hv, rfl⟩
  constructor
  · apply upperSubspace_map_le f L
    exact ⟨v, hv.1, rfl⟩
  · apply upperSubspace_map_le f R
    exact ⟨v, hv.2, rfl⟩

/-- A module morphism preserves pair denominators. -/
theorem pairDetectorDenominator_map_le
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    (pairDetectorDenominator M L R).map
        (f.app (Opposite.op
          (obj P.toPresentation.relations u₀))).hom ≤
      pairDetectorDenominator N L R := by
  rw [pairDetectorDenominator, Submodule.map_sup]
  apply sup_le
  · apply (Submodule.map_inf_le _).trans
    exact (inf_le_inf (upperSubspace_map_le f L)
      (lowerSubspace_map_le f R)).trans le_sup_left
  · apply (Submodule.map_inf_le _).trans
    exact (inf_le_inf (lowerSubspace_map_le f L)
      (upperSubspace_map_le f R)).trans le_sup_right

/-- Restriction of a module morphism to pair numerators. -/
def pairDetectorNumeratorMap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    pairDetectorNumerator M L R →ₗ[k] pairDetectorNumerator N L R :=
  LinearMap.codRestrict (pairDetectorNumerator N L R)
    ((f.app (Opposite.op
      (obj P.toPresentation.relations u₀))).hom.domRestrict
        (pairDetectorNumerator M L R)) (by
      rintro ⟨v, hv⟩
      apply pairDetectorNumerator_map_le f L R
      exact ⟨v, hv, rfl⟩)

@[simp]
theorem pairDetectorNumeratorMap_coe
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (x : pairDetectorNumerator M L R) :
    (pairDetectorNumeratorMap f L R x :
      N.obj (Opposite.op (obj P.toPresentation.relations u₀))) =
        f.app (Opposite.op
          (obj P.toPresentation.relations u₀)) x :=
  rfl

/-- The restricted pair-numerator map preserves the pair denominator. -/
theorem pairDetectorDenominatorInNumerator_le_comap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    pairDetectorDenominatorInNumerator M L R ≤
      (pairDetectorDenominatorInNumerator N L R).comap
        (pairDetectorNumeratorMap f L R) := by
  rintro ⟨v, hvnum⟩ hvden
  change f.app (Opposite.op
      (obj P.toPresentation.relations u₀)) v ∈
    pairDetectorDenominator N L R
  apply pairDetectorDenominator_map_le f L R
  exact ⟨v, hvden, rfl⟩

/-- Linear map induced on a pair detector. -/
def pairDetectorLinearMap
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    PairDetectorSpace M L R →ₗ[k] PairDetectorSpace N L R :=
  Submodule.mapQ
    (pairDetectorDenominatorInNumerator M L R)
    (pairDetectorDenominatorInNumerator N L R)
    (pairDetectorNumeratorMap f L R)
    (pairDetectorDenominatorInNumerator_le_comap f L R)

@[simp]
theorem pairDetectorLinearMap_mk
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N)
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t)
    (x : pairDetectorNumerator M L R) :
    pairDetectorLinearMap f L R (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (pairDetectorNumeratorMap f L R x) := by
  exact Submodule.mapQ_apply _ _ _ x

open MagnitudeConjecture.CoveringHom

/-- The detector functor attached to a split pair. -/
def pairDetectorFunctor
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    LinearModuleCategory
        (C := (Category P.toPresentation.relations)ᵒᵖ) k ⥤
      ModuleCat.{u} k where
  obj N := ModuleCat.of k (PairDetectorSpace N.obj L R)
  map {M N} f := ModuleCat.ofHom (pairDetectorLinearMap f.hom L R)
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

instance pairDetectorFunctor_additive
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    (pairDetectorFunctor L R).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

instance pairDetectorFunctor_linear
    (L : EndpointWord S u₀ (Bool.not t)) (R : EndpointWord S u₀ t) :
    (pairDetectorFunctor L R).Linear k where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

/-- The existing endpoint detector is literally the pair detector with a
trivial left half. -/
def pairDetectorSpaceOppositeVertexEquiv
    (N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k)
    (C : EndpointWord S u₀ t) :
    PairDetectorSpace N C.oppositeVertex C ≃ₗ[k] DetectorSpace N C :=
  LinearEquiv.refl k _

@[simp]
theorem pairDetectorLinearMap_oppositeVertex
    {M N : (Category P.toPresentation.relations)ᵒᵖ ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (C : EndpointWord S u₀ t) :
    pairDetectorLinearMap f C.oppositeVertex C = detectorLinearMap f C :=
  rfl

end MagnitudeConjecture.BoundQuiver.StringWord.EndpointWord
