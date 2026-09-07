import MagnitudeConjecture.Algebra.RightModuleSupportQuotient

/-!
# Directedness of literal support quotients

The module category of a support quotient is equivalent to the full ambient
subcategory on the selected vertices.  This file uses that equivalence to
send each indecomposable of a support-algebra skeleton back to its unique
ambient skeleton label.  Nonzero nonisomorphisms remain nonzero
nonisomorphisms, so ambient representation-directedness descends to the
literal support quotient.

No support corner or compatibility presentation is introduced.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- Inflate right modules over a literal support algebra to ambient right
modules, through the support-subcategory equivalence. -/
def supportInflationFunctor
    (X : RightModule.FinitelyGeneratedCategory A) :
    RightModule.FinitelyGeneratedCategory (P.SupportAlgebra X) ⥤
      RightModule.FinitelyGeneratedCategory A :=
  (P.supportEquivalence X).inverse ⋙
    (SupportedOn (S := S) X).ι

noncomputable instance supportInflationFunctorFaithful
    (X : RightModule.FinitelyGeneratedCategory A) :
    (P.supportInflationFunctor X).Faithful := by
  dsimp [supportInflationFunctor]
  infer_instance

noncomputable instance supportInflationFunctorAdditive
    (X : RightModule.FinitelyGeneratedCategory A) :
    (P.supportInflationFunctor X).Additive where
  map_add := by
    intro M N f g
    apply FGModuleCat.hom_ext
    rfl

noncomputable instance supportInflationFunctorReflectsIsomorphisms
    (X : RightModule.FinitelyGeneratedCategory A) :
    (P.supportInflationFunctor X).ReflectsIsomorphisms := by
  dsimp [supportInflationFunctor]
  infer_instance

/-- The ambient module represented by one label of the chosen support-algebra
skeleton. -/
abbrev supportSkeletonAmbientFGObj
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A)
    (i : Fin (P.supportAlgebraSkeleton hA X).n) :
    RightModule.FinitelyGeneratedCategory A :=
  (P.supportInflationFunctor X).obj
    ((P.supportAlgebraSkeleton hA X).fgObj i)

/-- Inflation of a chosen support-algebra indecomposable remains
indecomposable in the ambient finitely generated module category. -/
theorem supportSkeletonAmbientFGObj_indecomposable
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A)
    (i : Fin (P.supportAlgebraSkeleton hA X).n) :
    Indecomposable (P.supportSkeletonAmbientFGObj hA X i) := by
  have hright : Indecomposable
      ((P.supportAlgebraSkeleton hA X).fgObj i) :=
    (P.supportAlgebraSkeleton hA X).fgObj_indecomposable i
  letI : (P.leftToRightSupportFGEquivalence X).symm.functor.Additive := by
    change (P.leftToRightSupportFGEquivalence X).inverse.Additive
    infer_instance
  letI : (P.leftToRightSupportFGEquivalence X).symm.inverse.Additive := by
    change (P.leftToRightSupportFGEquivalence X).functor.Additive
    infer_instance
  have hleft : Indecomposable
      ((P.leftToRightSupportFGEquivalence X).inverse.obj
        ((P.supportAlgebraSkeleton hA X).fgObj i)) :=
    (LeftModule.indecomposable_functor_obj_iff
      (P.leftToRightSupportFGEquivalence X).symm
      ((P.supportAlgebraSkeleton hA X).fgObj i)).2 hright
  have hleftObj : Indecomposable
      ((P.leftToRightSupportFGEquivalence X).inverse.obj
        ((P.supportAlgebraSkeleton hA X).fgObj i)).obj :=
    (LeftModule.fgModule_indecomposable_iff_obj
      ((P.leftToRightSupportFGEquivalence X).inverse.obj
        ((P.supportAlgebraSkeleton hA X).fgObj i))).1 hleft
  have hinflatedObj : Indecomposable
      ((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (P.supportIdeal X).asIdeal)).obj
          ((P.leftToRightSupportFGEquivalence X).inverse.obj
            ((P.supportAlgebraSkeleton hA X).fgObj i)).obj) :=
    LeftModule.quotientRestrict_indecomposable
      (P.supportIdeal X)
      ((P.leftToRightSupportFGEquivalence X).inverse.obj
        ((P.supportAlgebraSkeleton hA X).fgObj i)).obj hleftObj
  apply (LeftModule.fgModule_indecomposable_iff_obj
    (P.supportSkeletonAmbientFGObj hA X i)).2
  simpa only [supportSkeletonAmbientFGObj, supportInflationFunctor,
    supportEquivalence, leftSupportEquivalence,
    leftToRightSupportFGEquivalence, Functor.comp_obj,
    ObjectProperty.ι_obj, Equivalence.symm_inverse,
    Equivalence.trans_inverse, leftSupportInflateFunctor,
    leftSupportInflateFGObj] using hinflatedObj

/-- The unique ambient skeleton label represented by a support-algebra
skeleton object after inflation. -/
def supportSkeletonAmbientLabel
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A)
    (i : Fin (P.supportAlgebraSkeleton hA X).n) : Fin S.n :=
  Classical.choose (S.fgObj_complete
    (P.supportSkeletonAmbientFGObj hA X i)
    (P.supportSkeletonAmbientFGObj_indecomposable hA X i))

/-- The selected ambient label represents the inflated support-algebra
object. -/
def supportSkeletonAmbientIso
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A)
    (i : Fin (P.supportAlgebraSkeleton hA X).n) :
    P.supportSkeletonAmbientFGObj hA X i ≅
      S.fgObj (P.supportSkeletonAmbientLabel hA X i) :=
  Classical.choice (Classical.choose_spec (S.fgObj_complete
    (P.supportSkeletonAmbientFGObj hA X i)
    (P.supportSkeletonAmbientFGObj_indecomposable hA X i)))

/-- A morphism between support-skeleton representatives, inflated and
conjugated to the corresponding ambient skeleton representatives. -/
def supportSkeletonAmbientMap
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A)
    {i j : Fin (P.supportAlgebraSkeleton hA X).n}
    (f : (P.supportAlgebraSkeleton hA X).fgObj i ⟶
      (P.supportAlgebraSkeleton hA X).fgObj j) :
    S.fgObj (P.supportSkeletonAmbientLabel hA X i) ⟶
      S.fgObj (P.supportSkeletonAmbientLabel hA X j) :=
  (P.supportSkeletonAmbientIso hA X i).inv ≫
    (P.supportInflationFunctor X).map f ≫
      (P.supportSkeletonAmbientIso hA X j).hom

/-- Inflation and conjugation preserve nonzero morphisms. -/
theorem supportSkeletonAmbientMap_ne_zero
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A)
    {i j : Fin (P.supportAlgebraSkeleton hA X).n}
    {f : (P.supportAlgebraSkeleton hA X).fgObj i ⟶
      (P.supportAlgebraSkeleton hA X).fgObj j} (hf : f ≠ 0) :
    P.supportSkeletonAmbientMap hA X f ≠ 0 := by
  intro hzero
  apply hf
  apply (P.supportInflationFunctor X).map_injective
  rw [Functor.map_zero]
  rw [← cancel_epi (P.supportSkeletonAmbientIso hA X i).inv]
  rw [← cancel_mono (P.supportSkeletonAmbientIso hA X j).hom]
  simpa [supportSkeletonAmbientMap, Category.assoc] using hzero

/-- Inflation and conjugation reflect isomorphisms. -/
theorem supportSkeletonAmbientMap_not_isIso
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A)
    {i j : Fin (P.supportAlgebraSkeleton hA X).n}
    {f : (P.supportAlgebraSkeleton hA X).fgObj i ⟶
      (P.supportAlgebraSkeleton hA X).fgObj j} (hf : ¬ IsIso f) :
    ¬ IsIso (P.supportSkeletonAmbientMap hA X f) := by
  intro hmap
  letI : IsIso (P.supportSkeletonAmbientMap hA X f) := hmap
  haveI : IsIso ((P.supportSkeletonAmbientIso hA X i).inv ≫
      (P.supportInflationFunctor X).map f ≫
        (P.supportSkeletonAmbientIso hA X j).hom) := by
    change IsIso (P.supportSkeletonAmbientMap hA X f)
    infer_instance
  haveI : IsIso ((P.supportInflationFunctor X).map f ≫
      (P.supportSkeletonAmbientIso hA X j).hom) :=
    IsIso.of_isIso_comp_left
      (P.supportSkeletonAmbientIso hA X i).inv _
  haveI : IsIso ((P.supportInflationFunctor X).map f) :=
    IsIso.of_isIso_comp_right _
      (P.supportSkeletonAmbientIso hA X j).hom
  exact hf (isIso_of_reflects_iso f (P.supportInflationFunctor X))

/-- Each nonzero nonisomorphism in the support skeleton gives one in the
ambient skeleton. -/
theorem supportNonzeroNonisomorphism_to_ambient
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A)
    {i j : Fin (P.supportAlgebraSkeleton hA X).n}
    (h : (P.supportAlgebraSkeleton hA X).NonzeroNonisomorphism i j) :
    S.NonzeroNonisomorphism
      (P.supportSkeletonAmbientLabel hA X i)
      (P.supportSkeletonAmbientLabel hA X j) := by
  obtain ⟨f, hf, hnotIso⟩ := h
  exact ⟨P.supportSkeletonAmbientMap hA X f,
    P.supportSkeletonAmbientMap_ne_zero hA X hf,
    P.supportSkeletonAmbientMap_not_isIso hA X hnotIso⟩

/-- A path of nonzero nonisomorphisms in the support skeleton inflates to
such a path in the ambient skeleton. -/
theorem supportNonzeroNonisomorphism_transGen_to_ambient
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A)
    {i j : Fin (P.supportAlgebraSkeleton hA X).n}
    (h : Relation.TransGen
      (P.supportAlgebraSkeleton hA X).NonzeroNonisomorphism i j) :
    Relation.TransGen S.NonzeroNonisomorphism
      (P.supportSkeletonAmbientLabel hA X i)
      (P.supportSkeletonAmbientLabel hA X j) := by
  induction h with
  | single hxy =>
      exact Relation.TransGen.single
        (P.supportNonzeroNonisomorphism_to_ambient hA X hxy)
  | tail hxy hyz ih =>
      exact ih.tail
        (P.supportNonzeroNonisomorphism_to_ambient hA X hyz)

/-- Representation-directedness descends to every literal support quotient. -/
theorem supportAlgebraSkeleton_hasAcyclicNonzeroNonisomorphisms
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (hA : RightModule.IsRepresentationFinite k A)
    (X : RightModule.FinitelyGeneratedCategory A) :
    (P.supportAlgebraSkeleton hA X).HasAcyclicNonzeroNonisomorphisms := by
  intro i hcycle
  exact H (P.supportSkeletonAmbientLabel hA X i)
    (P.supportNonzeroNonisomorphism_transGen_to_ambient hA X hcycle)

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
