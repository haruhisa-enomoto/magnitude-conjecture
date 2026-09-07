import MagnitudeConjecture.Algebra.RightModulePrimitiveMarkerComplement
import MagnitudeConjecture.Algebra.RightModulePrimitiveContragredient
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# The sign of a primitive new mesh under contragredient duality

The deleted simple for the opposite primitive idempotent is the
contragredient dual of the original deleted simple.  Together with reversal
of the two ambient markers, this identifies positivity of the dual new mesh
with vanishing of maps from the original left marker to the deleted simple.
The manuscript's marker-complement theorem then turns every negative mesh
into a positive dual mesh.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : PrimitiveIdempotentData e)

/-- Under the label-aligned contragredient skeleton, the original primitive
injective label is the primitive projective label for `op e`. -/
theorem contragredient_primitiveSinkLabel_eq_primitiveSourceLabel
    [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ] :
    S.primitiveSinkLabel D =
      S.contragredientSkeleton.primitiveSourceLabel D.opposite := by
  let Sop := S.contragredientSkeleton
  let i : Sop.fgObj (S.primitiveSinkLabel D) ≅
      Sop.fgObj (Sop.primitiveSourceLabel D.opposite) :=
    (S.contragredientSkeleton_fgObjIso
        (S.primitiveSinkLabel D)).trans
      (((Contragredient.dualFunctor k Aᵐᵒᵖ).mapIso
          (S.primitiveSinkIso D).op).trans
        ((RightModule.oppositeRightIdealDualPrimitiveInjectiveIso
          (k := k) e).symm.trans
            (Sop.primitiveSourceIso D.opposite)))
  exact Sop.fgObj_skeletal ⟨i⟩

/-- The deleted simple is a simple object of the finitely generated module
category. -/
theorem primitiveDeletedSimple_simple :
    Simple (S.primitiveDeletedSimple D) := by
  letI : IsSimpleModule Aᵐᵒᵖ (S.primitiveDeletedSimple D) :=
    S.projectiveSimpleTop_isSimpleModule
      (S.primitiveSourceProjectiveLabel D)
  exact RightModule.fgModule_simple_of_isSimpleModule _

/-- The opposite of the deleted simple is simple in the opposite category.
-/
theorem primitiveDeletedSimple_op_simple :
    Simple (Opposite.op (S.primitiveDeletedSimple D)) := by
  letI : Simple (S.primitiveDeletedSimple D) :=
    S.primitiveDeletedSimple_simple D
  apply simple_of_cosimple
  intro Z f _
  haveI : Mono f.unop := inferInstance
  constructor
  · intro hf
    haveI : IsIso f.unop := (isIso_unop_iff f).2 hf
    have hne : f.unop ≠ 0 :=
      Simple.mono_isIso_iff_nonzero f.unop |>.mp inferInstance
    intro hzero
    apply hne
    simpa using congrArg Quiver.Hom.unop hzero
  · intro hne
    have hneUnop : f.unop ≠ 0 := by
      intro hzero
      apply hne
      apply Quiver.Hom.unop_inj
      simpa using hzero
    haveI : IsIso f.unop :=
      Simple.mono_isIso_iff_nonzero f.unop |>.mpr hneUnop
    exact (isIso_unop_iff f).1 inferInstance

/-- The contragredient dual of the deleted simple is a simple object. -/
theorem contragredientPrimitiveDeletedSimple_simple :
    Simple ((Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.obj
      (Opposite.op (S.primitiveDeletedSimple D))) := by
  letI : Simple (Opposite.op (S.primitiveDeletedSimple D)) :=
    S.primitiveDeletedSimple_op_simple D
  exact CategoryTheory.simple_obj
    (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor _

/-- The simple top for `op e` is canonically isomorphic to the
contragredient dual of the original deleted simple. -/
def contragredientPrimitiveDeletedSimpleIso
    [IsAlgClosed k] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    S.contragredientSkeleton.primitiveDeletedSimple D.opposite ≅
      (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.obj
        (Opposite.op (S.primitiveDeletedSimple D)) := by
  let Sop := S.contragredientSkeleton
  let sourceOp := Sop.primitiveSourceLabel D.opposite
  let sink := S.primitiveSinkLabel D
  have hlabel : sink = sourceOp :=
    S.contragredient_primitiveSinkLabel_eq_primitiveSourceLabel D
  let iSource : Sop.fgObj sourceOp ≅ Sop.fgObj sink :=
    eqToIso (congrArg Sop.fgObj hlabel.symm)
  let j := S.primitiveDeletedSimpleToSink (D := D) H
  let h : Sop.fgObj sourceOp ⟶
      (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.obj
        (Opposite.op (S.primitiveDeletedSimple D)) :=
    iSource.hom ≫
      (S.contragredientSkeleton_fgObjIso sink).hom ≫
        (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.map j.op
  have hjop : j.op ≠ 0 := by
    intro hzero
    apply S.primitiveDeletedSimpleToSink_ne_zero (D := D) H
    apply Quiver.Hom.op_inj
    simpa using hzero
  have hmap :
      (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.map j.op ≠ 0 := by
    intro hzero
    apply hjop
    apply (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.map_injective
    simpa using hzero
  have hh : h ≠ 0 := by
    intro hzero
    apply hmap
    have hzero' :
        (S.contragredientSkeleton_fgObjIso sink).hom ≫
          (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.map j.op =
            0 := by
      apply (cancel_epi iSource.hom).1
      simpa [Category.assoc, h] using hzero
    apply (cancel_epi
      (S.contragredientSkeleton_fgObjIso sink).hom).1
    exact hzero'
  let DE := (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor.obj
    (Opposite.op (S.primitiveDeletedSimple D))
  letI : Simple DE := S.contragredientPrimitiveDeletedSimple_simple D
  letI : IsSimpleModule (Aᵐᵒᵖ)ᵐᵒᵖ DE :=
    RightModule.fgModule_isSimpleModule_of_simple DE
  have hrad : Module.jacobson (Aᵐᵒᵖ)ᵐᵒᵖ (Sop.fgObj sourceOp) ≤
      h.hom.hom.ker :=
    IsSemisimpleModule.jacobson_le_ker
      (Aᵐᵒᵖ)ᵐᵒᵖ (Aᵐᵒᵖ)ᵐᵒᵖ (Sop.fgObj sourceOp) DE h.hom.hom
  let gLinear :=
    (Module.jacobson (Aᵐᵒᵖ)ᵐᵒᵖ
      (Sop.fgObj sourceOp)).liftQ h.hom.hom fun x hx => hrad hx
  let g : Sop.primitiveDeletedSimple D.opposite ⟶ DE :=
    ConcreteCategory.ofHom gLinear
  have hfac : Sop.primitiveDeletedSimpleProjection D.opposite ≫ g = h := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hg : g ≠ 0 := by
    intro hzero
    apply hh
    rw [← hfac, hzero, comp_zero]
  letI : Simple (Sop.primitiveDeletedSimple D.opposite) :=
    Sop.primitiveDeletedSimple_simple D.opposite
  letI : IsIso g := CategoryTheory.isIso_of_hom_simple hg
  exact asIso g

/-- The right marker of the dual new mesh is the dual of the original left
marker, at the same label in the aligned skeleton. -/
theorem contragredientNewMeshEndpoint_rightMarker_eq_leftMarker
    [IsAlgClosed k] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (N.contragredientNewMeshEndpoint H he).rightMarker.1 =
      (N.leftMarker H he).1 := by
  change S.contragredientRightTranslationLabel
      (S.contragredientNonprojectiveLabel
        (N.sourceNoninjectiveLabel H he)) =
    ((S.rightTranslationEquiv).symm
      (N.sourceNoninjectiveLabel H he)).1
  exact S.contragredient_rightTranslationLabel_eq_inverse
    (N.sourceNoninjectiveLabel H he)

/-- Positivity of the dual new mesh is exactly vanishing of all maps from
the original left marker to the original deleted simple. -/
theorem contragredientNewMeshEndpoint_isPositive_iff
    [IsAlgClosed k] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (N.contragredientNewMeshEndpoint H he).IsPositive ↔
      ∀ f : S.fgObj (N.leftMarker H he).1 ⟶
        S.primitiveDeletedSimple D, f = 0 := by
  let F := (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor
  let Sop := S.contragredientSkeleton
  let Nop := N.contragredientNewMeshEndpoint H he
  let E := S.primitiveDeletedSimple D
  let P := S.fgObj (N.leftMarker H he).1
  let eE : Sop.primitiveDeletedSimple D.opposite ≅
      F.obj (Opposite.op E) :=
    S.contragredientPrimitiveDeletedSimpleIso D H
  let eP : Sop.fgObj Nop.rightMarker.1 ≅ F.obj (Opposite.op P) :=
    (eqToIso (congrArg Sop.fgObj
      (S.contragredientNewMeshEndpoint_rightMarker_eq_leftMarker
        D H he N))).trans
      (S.contragredientSkeleton_fgObjIso (N.leftMarker H he).1)
  constructor
  · intro hpositive f
    let g : Sop.primitiveDeletedSimple D.opposite ⟶
        Sop.fgObj Nop.rightMarker.1 :=
      eE.hom ≫ F.map f.op ≫ eP.inv
    have hg : g = 0 := hpositive g
    have hmap : F.map f.op = 0 := by
      apply (cancel_epi eE.hom).1
      apply (cancel_mono eP.inv).1
      simpa [Category.assoc, g] using hg
    have hfop : f.op = 0 := by
      apply F.map_injective
      simpa using hmap
    apply Quiver.Hom.op_inj
    simpa using hfop
  · intro hzero g
    let d : F.obj (Opposite.op E) ⟶ F.obj (Opposite.op P) :=
      eE.inv ≫ g ≫ eP.hom
    let fop : Opposite.op E ⟶ Opposite.op P := F.preimage d
    have hf : fop.unop = 0 := hzero fop.unop
    have hfop : fop = 0 := by
      apply Quiver.Hom.unop_inj
      simpa using hf
    have hd : d = 0 := by
      calc
        d = F.map (F.preimage d) := (F.map_preimage d).symm
        _ = F.map fop := by rfl
        _ = 0 := by rw [hfop, F.map_zero]
    apply (cancel_epi eE.inv).1
    apply (cancel_mono eP.hom).1
    simpa [Category.assoc, d] using hd

/-- The marker-complement theorem converts a negative original mesh into a
positive contragredient mesh. -/
theorem contragredientNewMeshEndpoint_isPositive_of_not_isPositive
    [IsAlgClosed k] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (N : S.PrimitiveNewRightMeshEndpoint D)
    (hnegative : ¬ N.IsPositive) :
    (N.contragredientNewMeshEndpoint H he).IsPositive := by
  apply (S.contragredientNewMeshEndpoint_isPositive_iff D H he N).2
  intro f
  by_contra hf
  apply hnegative
  exact (N.hasComplementaryMarkers B H he).1 ⟨f, hf⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
