import MagnitudeConjecture.Algebra.StringPeakWedge
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation

/-!
# Peak-wedge string modules are representable

For a two-sided maximal peak wedge, evaluation at the common peak position
identifies the covariant representable on the opposite bound-quiver category
with the literal right-string module.  The variance is explicit: a displayed
path from the peak becomes a morphism out of the opposite peak object.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word.PeakWedge

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]
variable (P : StringPresentation k A Q)
variable {C : Word P.toPresentation.relations}
variable (W : C.PeakWedge)

/-- The finite representable at the common peak, in the literal category of
right modules on the opposite bound quiver. -/
noncomputable def peakRepresentable :=
  finiteDimensionalLinearCoyoneda
    (C := (Category P.toPresentation.relations)ᵒᵖ) (k := k)
    (Opposite.op (obj P.toPresentation.relations W.peak))
    (finiteOppositeRepresentablesOfAdmissible
      P.toPresentation.admissible
      (Opposite.op (obj P.toPresentation.relations W.peak)))

/-- Evaluation at the peak position gives the canonical map from the peak
representable to the string module. -/
noncomputable def peakRepresentableHom :
    peakRepresentable P W ⟶ C.finiteRightModule P.monomial :=
  ObjectProperty.homMk
    (linearCoyonedaHom (C.rightLinearModule P.monomial)
      (Opposite.op (obj P.toPresentation.relations W.peak))
      (Finsupp.single W.peakPosition 1))

/-- The surviving-path basis of one component of the peak representable. -/
noncomputable def peakRepresentableBasis (y : Q) :
    Module.Basis
      (SurvivingPath P.toPresentation.relations W.peak y) k
      ((peakRepresentable P W).obj.obj.obj
        (Opposite.op (obj P.toPresentation.relations y))) :=
  (survivingPathBasis P.toPresentation.relations P.monomial W.peak y).map
    (oppositeHomLinearEquiv (k := k)
      (Opposite.op (obj P.toPresentation.relations W.peak))
      (Opposite.op (obj P.toPresentation.relations y))).symm

@[simp]
theorem peakRepresentableBasis_apply (y : Q)
    (p : SurvivingPath P.toPresentation.relations W.peak y) :
    peakRepresentableBasis P W y p =
      (pathMap P.toPresentation.relations p.1).op := by
  rw [peakRepresentableBasis, Module.Basis.map_apply,
    survivingPathBasis_apply]
  rfl

/-- On surviving-path basis vectors, peak evaluation is the corresponding
position-basis vector. -/
theorem peakRepresentableHom_app_basis
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    (y : Q)
    (p : SurvivingPath P.toPresentation.relations W.peak y) :
    ((peakRepresentableHom P W).hom.hom.app
      (Opposite.op (obj P.toPresentation.relations y))).hom
        (peakRepresentableBasis P W y p) =
      Finsupp.single
        (W.survivingPathTargetPosition P.toSpecialBiserialPresentation
          hleft hright y p) 1 := by
  rw [peakRepresentableBasis_apply]
  change
    (linearCoyonedaHom (C.rightLinearModule P.monomial)
      (Opposite.op (obj P.toPresentation.relations W.peak))
      (Finsupp.single W.peakPosition 1)).hom.app
        (Opposite.op (obj P.toPresentation.relations y))
        (pathMap P.toPresentation.relations p.1).op = _
  rw [linearCoyonedaHom_app_apply]
  change (C.rightModule P.monomial).map
      (pathMap P.toPresentation.relations p.1).op
        (Finsupp.single W.peakPosition 1) = _
  rw [C.rightModule_map_pathMap]
  change C.quiverRepresentation.map p.1
      (Finsupp.single W.peakPosition 1) = _
  rw [C.quiverRepresentation_map_single, one_smul,
    C.pathOnBasis_eq_single_of_reach p.1 W.peakPosition
      (W.survivingPathTargetPosition P.toSpecialBiserialPresentation
        hleft hright y p)
      (W.pathReach_survivingPathTargetPosition
        P.toSpecialBiserialPresentation hleft hright y p)]

/-- The componentwise linear equivalence induced by the surviving-path and
word-position bases. -/
noncomputable def peakRepresentableComponentLinearEquiv
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    (y : Q) :
    ((peakRepresentable P W).obj.obj.obj
        (Opposite.op (obj P.toPresentation.relations y))) ≃ₗ[k]
      C.Space y :=
  (peakRepresentableBasis P W y).equiv
    Finsupp.basisSingleOne
    (W.survivingPathEquivPositionAt P.toSpecialBiserialPresentation
      hleft hright y)

/-- Each component of peak evaluation is the basis equivalence above. -/
theorem peakRepresentableHom_app_eq
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length)
    (y : Q) :
    ((peakRepresentableHom P W).hom.hom.app
      (Opposite.op (obj P.toPresentation.relations y))).hom =
      (peakRepresentableComponentLinearEquiv P W
        hleft hright y).toLinearMap := by
  apply (peakRepresentableBasis P W y).ext
  intro p
  rw [peakRepresentableHom_app_basis P W hleft hright y p]
  change Finsupp.single
      (W.survivingPathTargetPosition P.toSpecialBiserialPresentation
        hleft hright y p) 1 =
    (peakRepresentableComponentLinearEquiv P W hleft hright y)
      (peakRepresentableBasis P W y p)
  rw [peakRepresentableComponentLinearEquiv,
    Module.Basis.equiv_apply]
  rfl

/-- Peak evaluation is an isomorphism of finite-dimensional modules on the
opposite bound-quiver category. -/
theorem peakRepresentableHom_isIso
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length) :
    IsIso (peakRepresentableHom P W) := by
  let f := peakRepresentableHom P W
  let J := (IsFiniteDimensionalModule
    (C := (Category P.toPresentation.relations)ᵒᵖ) k).ι
  let I := (IsLinearModule
    (C := (Category P.toPresentation.relations)ᵒᵖ) k).ι
  letI appIso (X : (Category P.toPresentation.relations)ᵒᵖ) :
      IsIso (f.hom.hom.app X) := by
    apply (ConcreteCategory.isIso_iff_bijective (f.hom.hom.app X)).mpr
    change Function.Bijective
      ((f.hom.hom.app (Opposite.op
        (obj P.toPresentation.relations X.unop.as))).hom)
    rw [show (f.hom.hom.app (Opposite.op
        (obj P.toPresentation.relations X.unop.as))).hom =
      (peakRepresentableComponentLinearEquiv P W
        hleft hright X.unop.as).toLinearMap from
      peakRepresentableHom_app_eq P W
        hleft hright X.unop.as]
    exact (peakRepresentableComponentLinearEquiv P W
      hleft hright X.unop.as).bijective
  haveI : IsIso f.hom.hom := NatIso.isIso_of_isIso_app f.hom.hom
  haveI : IsIso (I.map f.hom) := by
    change IsIso f.hom.hom
    infer_instance
  haveI : IsIso f.hom := isIso_of_reflects_iso f.hom I
  haveI : IsIso (J.map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f J

/-- The literal right-string module of a two-sided maximal peak wedge is the
finite representable at its common peak. -/
noncomputable def peakRepresentableIso
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length) :
    peakRepresentable P W ≅ C.finiteRightModule P.monomial := by
  letI : IsIso (peakRepresentableHom P W) :=
    peakRepresentableHom_isIso P W hleft hright
  exact asIso (peakRepresentableHom P W)

/-- A two-sided maximal peak-wedge right-string module is projective. -/
theorem finiteRightModule_projective
    (hleft : 0 < W.leftArm.length)
    (hright : 0 < W.rightArm.length) :
    Projective (C.finiteRightModule P.monomial) := by
  letI : Projective (peakRepresentable P W) :=
    finiteDimensionalLinearCoyoneda_projective
      (Opposite.op (obj P.toPresentation.relations W.peak))
      (finiteOppositeRepresentablesOfAdmissible
        P.toPresentation.admissible
        (Opposite.op (obj P.toPresentation.relations W.peak)))
  exact CategoryTheory.Projective.of_iso
    (peakRepresentableIso P W hleft hright) inferInstance

end MagnitudeConjecture.BoundQuiver.StringWord.Word.PeakWedge

namespace MagnitudeConjecture.BoundQuiver.StringWord.Word

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- The literal right-string module at the exceptional overlapping-cohook
boundary is projective. -/
theorem finiteRightModule_projective_of_overlappingCohookDeletions
    (P : StringPresentation k A Q)
    {C L D : Word P.toPresentation.relations}
    (leftDeletion : LeftCohookDeletion C D)
    (rightDeletion : CohookDeletion C L)
    (hoverlap : C.length < leftDeletion.steps + rightDeletion.steps) :
    Projective (C.finiteRightModule P.monomial) := by
  obtain ⟨W, _, _, hleft, hright⟩ :=
    exists_peakWedge_of_overlappingCohookDeletions
      P.toSpecialBiserialPresentation leftDeletion rightDeletion hoverlap
  exact W.finiteRightModule_projective P hleft hright

end MagnitudeConjecture.BoundQuiver.StringWord.Word
