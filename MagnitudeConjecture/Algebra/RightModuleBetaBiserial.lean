import MagnitudeConjecture.Algebra.RightModuleBetaSocleReduction
import MagnitudeConjecture.Algebra.RightModuleAllMoritaBasic
import MagnitudeConjecture.Algebra.RightModuleBasicMorita
import MagnitudeConjecture.Algebra.RightModuleOppositeProjectivePresentation
import MagnitudeConjecture.Algebra.RightModulePrimitiveSpecialBiserial
import MagnitudeConjecture.Algebra.RightModuleProjectiveRadicalRecursion
import MagnitudeConjecture.Algebra.SpecialBiserialAlgebra
import MagnitudeConjecture.CategoryTheory.BiserialObject

/-!
# Biserial projectives in the beta-two socle quotient

The canonical quotient by all non-simple projective-injective socles has
right-middle arity at most two at every vertex.  The finite radical recursion
therefore makes every indecomposable projective of that quotient biserial,
with separated uniserial radical branches.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- For an ideal-annihilated module with simple top on both sides of the
quotient equivalence, biseriality over the quotient algebra is equivalent to
biseriality over the ambient algebra. -/
theorem idealQuotientFGObj_isBiserial_iff_ambient_of_simpleTop
    (I : TwoSidedIdeal A) (M : IdealQuotientSubcategory I)
    (hQuotientTop : IsSimpleModule (idealQuotientAlgebra I)ᵐᵒᵖ
      (((idealQuotientEquivalence (k := k) I).functor.obj M) ⧸
        Module.jacobson (idealQuotientAlgebra I)ᵐᵒᵖ
          ((idealQuotientEquivalence (k := k) I).functor.obj M)))
    (hAmbientTop : IsSimpleModule Aᵐᵒᵖ
      (M.obj ⧸ Module.jacobson Aᵐᵒᵖ M.obj)) :
    IsBiserialModule (idealQuotientAlgebra I)ᵐᵒᵖ
        ((idealQuotientEquivalence (k := k) I).functor.obj M) ↔
      IsBiserialModule Aᵐᵒᵖ M.obj := by
  letI : IsNoetherianRing (idealQuotientAlgebra I)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let E := idealQuotientEquivalence (k := k) I
  let Q := IdealQuotientProperty I
  letI : Q.Nonempty := ObjectProperty.nonempty_of_prop M.property
  letI : Q.ContainsZero := inferInstance
  letI : HasFiniteProducts (IdealQuotientSubcategory I) :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      E.functor⟩
  letI : Abelian (IdealQuotientSubcategory I) :=
    CategoryTheory.abelianOfEquivalence E.functor
  constructor
  · intro hQuotient
    have hQuotientObject : IsBiserialObject (E.functor.obj M) :=
      IsBiserialModule.toFGModuleCatIsBiserialObject
        _ hQuotient hQuotientTop
    have hSubcategory : IsBiserialObject M :=
      IsBiserialObject.of_map_equivalence E hQuotientObject
    have hAmbientObject : IsBiserialObject M.obj :=
      IsBiserialObject.congrOrderIso hSubcategory
        (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
          Q M)
    exact IsBiserialObject.toIsBiserialModule_of_fg M.obj hAmbientObject
  · intro hAmbient
    have hAmbientObject : IsBiserialObject M.obj :=
      IsBiserialModule.toFGModuleCatIsBiserialObject
        M.obj hAmbient hAmbientTop
    have hSubcategory : IsBiserialObject M :=
      IsBiserialObject.congrOrderIso hAmbientObject
        (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
          Q M).symm
    have hQuotientObject : IsBiserialObject (E.functor.obj M) :=
      IsBiserialObject.map_equivalence hSubcategory E
    exact IsBiserialObject.toIsBiserialModule_of_fg
      (E.functor.obj M) hQuotientObject

/-- Under the same simple-top hypotheses, the stronger decomposition into
two uniserial branches with zero intersection is also invariant under the
ideal-quotient equivalence. -/
theorem idealQuotientFGObj_hasSeparatedBranches_iff_ambient_of_simpleTop
    (I : TwoSidedIdeal A) (M : IdealQuotientSubcategory I)
    (hQuotientTop : IsSimpleModule (idealQuotientAlgebra I)ᵐᵒᵖ
      (((idealQuotientEquivalence (k := k) I).functor.obj M) ⧸
        Module.jacobson (idealQuotientAlgebra I)ᵐᵒᵖ
          ((idealQuotientEquivalence (k := k) I).functor.obj M)))
    (hAmbientTop : IsSimpleModule Aᵐᵒᵖ
      (M.obj ⧸ Module.jacobson Aᵐᵒᵖ M.obj)) :
    IsBiserialModule.HasSeparatedUniserialJacobsonBranches
        (idealQuotientAlgebra I)ᵐᵒᵖ
        ((idealQuotientEquivalence (k := k) I).functor.obj M) ↔
      IsBiserialModule.HasSeparatedUniserialJacobsonBranches Aᵐᵒᵖ M.obj := by
  letI : IsNoetherianRing (idealQuotientAlgebra I)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let E := idealQuotientEquivalence (k := k) I
  let Q := IdealQuotientProperty I
  letI : Q.Nonempty := ObjectProperty.nonempty_of_prop M.property
  letI : Q.ContainsZero := inferInstance
  letI : HasFiniteProducts (IdealQuotientSubcategory I) :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      E.functor⟩
  letI : Abelian (IdealQuotientSubcategory I) :=
    CategoryTheory.abelianOfEquivalence E.functor
  constructor
  · intro hQuotient
    have hQuotientObject : HasSeparatedUniserialRadicalObject
        (E.functor.obj M) :=
      hQuotient.toFGModuleCatObject _ hQuotientTop
    have hSubcategory : HasSeparatedUniserialRadicalObject M :=
      HasSeparatedUniserialRadicalObject.of_map_equivalence
        E hQuotientObject
    have hAmbientObject : HasSeparatedUniserialRadicalObject M.obj :=
      HasSeparatedUniserialRadicalObject.congrOrderIso hSubcategory
        (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
          Q M)
    exact IsBiserialModule.hasSeparatedUniserialJacobsonBranches_of_fgModuleCatObject
      M.obj hAmbientObject
  · intro hAmbient
    have hAmbientObject : HasSeparatedUniserialRadicalObject M.obj :=
      hAmbient.toFGModuleCatObject M.obj hAmbientTop
    have hSubcategory : HasSeparatedUniserialRadicalObject M :=
      HasSeparatedUniserialRadicalObject.congrOrderIso hAmbientObject
        (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
          Q M).symm
    have hQuotientObject : HasSeparatedUniserialRadicalObject
        (E.functor.obj M) :=
      HasSeparatedUniserialRadicalObject.map_equivalence hSubcategory E
    exact IsBiserialModule.hasSeparatedUniserialJacobsonBranches_of_fgModuleCatObject
      (E.functor.obj M) hQuotientObject

end MagnitudeConjecture.RightModule

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

set_option synthInstance.maxHeartbeats 100000

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

noncomputable local instance betaBiserialHasExt :
    HasExt.{u} (RightModule.FinitelyGeneratedCategory A) := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  exact CategoryTheory.hasExt_of_enoughProjectives _

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- Every indecomposable projective of the canonical simultaneous socle
quotient has radical equal to the internal direct sum of at most two
uniserial branches. -/
theorem nonsimpleProjectiveInjectiveSocleFamily_projective_hasSeparatedBranches
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2)
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective))ᵐᵒᵖ]
    (j : Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleFamilyIdeal
        S.nonsimpleProjectiveInjectiveLabels
        S.nonsimpleProjectiveInjectiveLabels_injective)).n)
    (hj : Projective
      ((S.idealQuotientFiniteIndecomposableSkeleton
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective)).fgObj j)) :
    IsBiserialModule.HasSeparatedUniserialJacobsonBranches
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective))ᵐᵒᵖ
      ((S.idealQuotientFiniteIndecomposableSkeleton
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective)).fgObj j) := by
  let J := P.primitiveProjectiveSocleFamilyIdeal
    S.nonsimpleProjectiveInjectiveLabels
    S.nonsimpleProjectiveInjectiveLabels_injective
  let Q := S.idealQuotientFiniteIndecomposableSkeleton J
  exact Q.projective_hasSeparatedUniserialJacobsonBranches_of_total_bound
    (fun i ↦
      P.nonsimpleProjectiveInjectiveSocleFamily_rightMiddleArity_le_two
        hbeta i) j hj

/-- Every indecomposable projective of the canonical simultaneous socle
quotient is biserial. -/
theorem nonsimpleProjectiveInjectiveSocleFamily_projective_isBiserialModule
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2)
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective))ᵐᵒᵖ]
    (j : Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleFamilyIdeal
        S.nonsimpleProjectiveInjectiveLabels
        S.nonsimpleProjectiveInjectiveLabels_injective)).n)
    (hj : Projective
      ((S.idealQuotientFiniteIndecomposableSkeleton
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective)).fgObj j)) :
    IsBiserialModule
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective))ᵐᵒᵖ
      ((S.idealQuotientFiniteIndecomposableSkeleton
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective)).fgObj j) := by
  let J := P.primitiveProjectiveSocleFamilyIdeal
    S.nonsimpleProjectiveInjectiveLabels
    S.nonsimpleProjectiveInjectiveLabels_injective
  let Q := S.idealQuotientFiniteIndecomposableSkeleton J
  exact Q.projective_isBiserialModule_of_total_bound
    (fun i ↦
      P.nonsimpleProjectiveInjectiveSocleFamily_rightMiddleArity_le_two
        hbeta i) j hj

include P in
/-- Every ambient indecomposable projective not belonging to the deleted
non-simple projective-injective family is biserial.  Such a projective is an
ordinary surviving quotient projective, so its quotient-algebra biseriality
transports back through the annihilated full subcategory. -/
theorem projective_isBiserialModule_of_beta_le_two_of_not_mem_nonsimpleProjectiveInjective
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2)
    (p : S.ProjectiveLabel)
    (hpNotMem : p ∉ S.nonsimpleProjectiveInjectiveLabels) :
    IsBiserialModule Aᵐᵒᵖ (S.fgObj p.label) := by
  let T := S.nonsimpleProjectiveInjectiveLabels
  let hInjective := S.nonsimpleProjectiveInjectiveLabels_injective
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  letI : IsNoetherianRing (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Q := S.idealQuotientFiniteIndecomposableSkeleton J
  let q := S.idealQuotientFiniteLabelEquiv J
  have hpAnn : RightModule.IsAnnihilatedBy J (S.fgObj p.label) := by
    apply (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
      T hInjective p.label).2
    intro r hr heq
    apply hpNotMem
    have hrp : r = p := by
      cases r with
      | mk r hrProjective =>
          cases p with
          | mk p hpProjective =>
              dsimp at heq
              subst r
              rfl
    subst r
    exact hr
  let x : S.IdealQuotientLabel J := ⟨p.label, hpAnn⟩
  let j : Fin Q.n := q.symm x
  let E := RightModule.idealQuotientEquivalence (k := k) J
  let M : RightModule.IdealQuotientSubcategory J :=
    S.idealQuotientLabelObj J x
  let e : Q.fgObj j ≅ E.functor.obj M :=
    (S.idealQuotientFiniteFGObjIso J j).trans
      (E.functor.mapIso (eqToIso (congrArg
        (S.idealQuotientLabelObj J) (q.apply_symm_apply x))))
  have hIntrinsicProjective : Projective (E.functor.obj M) :=
    RightModule.idealQuotientFGObj_projective_of_ambient
      J (S.fgObj p.label) hpAnn p.projective
  have hjProjective : Projective (Q.fgObj j) :=
    Projective.of_iso e.symm hIntrinsicProjective
  have hjBiserial : IsBiserialModule
      (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ (Q.fgObj j) :=
    P.nonsimpleProjectiveInjectiveSocleFamily_projective_isBiserialModule
      hbeta j hjProjective
  let eLin := FGModuleCat.isoToLinearEquiv e
  have hIntrinsicBiserial : IsBiserialModule
      (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ (E.functor.obj M) :=
    IsBiserialModule.congr eLin hjBiserial
  let pj : Q.ProjectiveLabel := ⟨j, hjProjective⟩
  have hjTop : IsSimpleModule (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ
      (Q.fgObj j ⧸ Module.jacobson
        (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ (Q.fgObj j)) :=
    Q.projectiveSimpleTop_isSimpleModule pj
  have hIntrinsicTop :
      IsSimpleModule (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ
        ((E.functor.obj M) ⧸ Module.jacobson
          (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ (E.functor.obj M)) :=
    isSimpleModule_top_congr eLin hjTop
  have hAmbientTop : IsSimpleModule Aᵐᵒᵖ
      (S.fgObj p.label ⧸
        Module.jacobson Aᵐᵒᵖ (S.fgObj p.label)) :=
    S.projectiveSimpleTop_isSimpleModule p
  exact (RightModule.idealQuotientFGObj_isBiserial_iff_ambient_of_simpleTop
    J M hIntrinsicTop hAmbientTop).1 hIntrinsicBiserial

include P in
/-- A selected non-simple projective-injective right ideal is biserial.  Its
socle quotient is one of the replacement projectives in the simultaneous
quotient.  The separated radical branches of that replacement transport back
to the literal socle quotient and then lift across its simple essential
socle. -/
theorem selectedProjective_rightIdeal_isBiserialModule_of_beta_le_two
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2)
    (p : S.ProjectiveLabel)
    (hp : p ∈ S.nonsimpleProjectiveInjectiveLabels) :
    IsBiserialModule Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p)) := by
  let T := S.nonsimpleProjectiveInjectiveLabels
  let hInjective := S.nonsimpleProjectiveInjectiveLabels_injective
  let hNotSimple := S.nonsimpleProjectiveInjectiveLabels_notSimple
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  letI : IsNoetherianRing (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Q := S.idealQuotientFiniteIndecomposableSkeleton J
  let j : Fin Q.n :=
    P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
      T hInjective hNotSimple p hp
  let x : S.IdealQuotientLabel J :=
    P.primitiveProjectiveSocleFamilyReplacementLabel
      T hInjective hNotSimple p hp
  let M : RightModule.IdealQuotientSubcategory J :=
    S.idealQuotientLabelObj J x
  let E := RightModule.idealQuotientEquivalence (k := k) J
  let e : Q.fgObj j ≅ E.functor.obj M :=
    P.primitiveProjectiveSocleFamilyFiniteReplacementIso
      T hInjective hNotSimple p hp
  have hjProjective : Projective (Q.fgObj j) :=
    P.primitiveProjectiveSocleFamilyFiniteReplacement_projective
      T hInjective hNotSimple p hp
  have hjBranches :
      IsBiserialModule.HasSeparatedUniserialJacobsonBranches
        (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ (Q.fgObj j) :=
    P.nonsimpleProjectiveInjectiveSocleFamily_projective_hasSeparatedBranches
      hbeta j hjProjective
  let eLin := FGModuleCat.isoToLinearEquiv e
  have hIntrinsicBranches :
      IsBiserialModule.HasSeparatedUniserialJacobsonBranches
        (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ (E.functor.obj M) :=
    IsBiserialModule.HasSeparatedUniserialJacobsonBranches.congr
      eLin hjBranches
  let pj : Q.ProjectiveLabel := ⟨j, hjProjective⟩
  have hjTop : IsSimpleModule (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ
      (Q.fgObj j ⧸ Module.jacobson
        (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ (Q.fgObj j)) :=
    Q.projectiveSimpleTop_isSimpleModule pj
  have hIntrinsicTop :
      IsSimpleModule (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ
        ((E.functor.obj M) ⧸ Module.jacobson
          (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ (E.functor.obj M)) :=
    isSimpleModule_top_congr eLin hjTop
  let hpInjective := hInjective p hp
  let hpNotSimple := hNotSimple p hp
  let eAmbient : P.primitiveProjectiveSocleQuotientFGObj p ≅ M.obj :=
    P.primitiveProjectiveSocleQuotientAmbientIso
      p hpInjective hpNotSimple
  let eAmbientLin := FGModuleCat.isoToLinearEquiv eAmbient
  have hLiteralTop : IsSimpleModule Aᵐᵒᵖ
      (P.primitiveProjectiveSocleQuotientFGObj p ⧸
        Module.jacobson Aᵐᵒᵖ
          (P.primitiveProjectiveSocleQuotientFGObj p)) :=
    P.primitiveProjectiveSocleQuotient_top_isSimpleModule p hpNotSimple
  have hAmbientTop : IsSimpleModule Aᵐᵒᵖ
      (M.obj ⧸ Module.jacobson Aᵐᵒᵖ M.obj) :=
    isSimpleModule_top_congr eAmbientLin hLiteralTop
  have hAmbientBranches :
      IsBiserialModule.HasSeparatedUniserialJacobsonBranches Aᵐᵒᵖ M.obj :=
    (RightModule.idealQuotientFGObj_hasSeparatedBranches_iff_ambient_of_simpleTop
      J M hIntrinsicTop hAmbientTop).1 hIntrinsicBranches
  have hLiteralBranches :
      IsBiserialModule.HasSeparatedUniserialJacobsonBranches Aᵐᵒᵖ
        (P.primitiveProjectiveSocleQuotientFGObj p) :=
    IsBiserialModule.HasSeparatedUniserialJacobsonBranches.congr
      eAmbientLin.symm hAmbientBranches
  let R := RightModule.rightIdealFGObj (P.idempotent p)
  let pIso := P.primitiveProjectiveIso p
  letI : Injective R := Injective.of_iso pIso.symm hpInjective
  have hRind : Indecomposable R :=
    RightModule.rightIdealFGObj_indecomposable (P.primitive p)
  have hsocle : IsSimpleModule Aᵐᵒᵖ (moduleSocle Aᵐᵒᵖ R) :=
    MagnitudeConjecture.moduleSocle_isSimple_of_injective_indecomposable
      (k := k) R hRind
  have hlength :=
    RightModule.FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := A) R
  letI : IsArtinian Aᵐᵒᵖ R :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).2
  exact
    IsBiserialModule.of_quotient_moduleSocle_hasSeparatedUniserialJacobsonBranches
      hsocle (P.primitiveProjective_moduleSocle_le_jacobson p hpNotSimple)
        hLiteralBranches

include P in
/-- If the right AR middle-term bound is at most two, every primitive right
ideal in the chosen presentation is a biserial module. -/
theorem rightIdeal_isBiserialModule_of_beta_le_two
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2)
    (p : S.ProjectiveLabel) :
    IsBiserialModule Aᵐᵒᵖ
      (RightModule.rightIdealFGObj (P.idempotent p)) := by
  by_cases hp : p ∈ S.nonsimpleProjectiveInjectiveLabels
  · exact P.selectedProjective_rightIdeal_isBiserialModule_of_beta_le_two
      hbeta p hp
  · have hRepresentative : IsBiserialModule Aᵐᵒᵖ
        (S.fgObj p.label) :=
      P.projective_isBiserialModule_of_beta_le_two_of_not_mem_nonsimpleProjectiveInjective
        hbeta p hp
    exact IsBiserialModule.congr
      (FGModuleCat.isoToLinearEquiv (P.primitiveProjectiveIso p)).symm
        hRepresentative

include P in
/-- The right beta bound at most two makes the chosen primitive-projective
presentation biserial on both sides.  The left ideals are the right ideals of
the opposite presentation, whose beta bound is Gabriel's left/right
comparison. -/
theorem isBiserial_of_beta_le_two
    [IsNoetherianRing A] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    P.IsBiserial := by
  constructor
  · intro p
    exact IsBiserialModule.toFGModuleCatIsBiserialObject _
      (P.rightIdeal_isBiserialModule_of_beta_le_two hbeta p)
      (P.primitiveProjective_top_isSimpleModule p)
  · intro p
    let Sop := S.contragredientSkeleton
    let Pop := P.oppositePresentation
    have hbetaOp : FiniteTauMatrix.beta
        Sop.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
      rw [S.contragredient_beta_eq_leftBeta]
      exact S.leftBeta_le_two_of_beta_le_two hbeta
    let q : Sop.ProjectiveLabel := P.oppositeProjectiveEquiv p
    have hOppModule : IsBiserialModule (Aᵐᵒᵖ)ᵐᵒᵖ
        (RightModule.rightIdealFGObj (Pop.idempotent q)) :=
      Pop.rightIdeal_isBiserialModule_of_beta_le_two hbetaOp q
    have hOppObject : IsBiserialObject
        (RightModule.rightIdealFGObj (Pop.idempotent q)) :=
      IsBiserialModule.toFGModuleCatIsBiserialObject _ hOppModule
        (Pop.primitiveProjective_top_isSimpleModule q)
    apply (RightModule.leftIdealFGObj_isBiserialObject_iff_oppositeRightIdeal
      (k := k) (P.idempotent p)).2
    simpa [Pop, q, PrimitiveProjectivePresentation.oppositePresentation,
      PrimitiveProjectivePresentation.oppositeIdempotent] using hOppObject

include P in
/-- For an algebra carrying a complete duplicate-free primitive-projective
presentation, the beta-two bound produces a literal special-biserial
bound-quiver presentation. -/
theorem admitsSpecialBiserialPresentation_of_beta_le_two
    [IsNoetherianRing A] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    BoundQuiver.AdmitsSpecialBiserialPresentation k A :=
  P.ambient_admitsSpecialBiserialPresentation_of_isBiserial
    (P.isBiserial_of_beta_le_two hbeta)

include P in
/-- The beta-two bound implies special-biseriality whenever the ambient
algebra itself is supplied with the complete primitive presentation. -/
theorem isSpecialBiserial_of_beta_le_two
    [IsNoetherianRing A] [IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ]
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    BoundQuiver.IsSpecialBiserial k A :=
  BoundQuiver.isSpecialBiserial_of_presentation
    (P.admitsSpecialBiserialPresentation_of_beta_le_two hbeta)

end PrimitiveProjectivePresentation

/-- For an arbitrary representation-finite algebra, the canonical basic
endomorphism algebra carries a literal special-biserial presentation under
the beta-two bound. -/
theorem moritaBasicAlgebra_admitsSpecialBiserialPresentation_of_beta_le_two
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    BoundQuiver.AdmitsSpecialBiserialPresentation k S.moritaBasicAlgebra := by
  let U := S.moritaBasicSkeleton
  let P := S.moritaBasicPrimitiveProjectivePresentation
  letI : IsNoetherianRing S.moritaBasicAlgebra :=
    IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing (S.moritaBasicAlgebraᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact P.admitsSpecialBiserialPresentation_of_beta_le_two
    (S.moritaBasicSkeleton_beta_le hbeta)

/-- The final Morita transport, isolated from the representation-theoretic
argument.  Once the canonical basic endomorphism algebra is connected to the
ambient algebra by Mathlib's all-module Morita witness, its literal
special-biserial presentation gives the manuscript's Morita-invariant
predicate for the ambient algebra. -/
theorem isSpecialBiserial_of_beta_le_two_of_moritaBasicEquivalence
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (e : MoritaEquivalence k A S.moritaBasicAlgebra)
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    BoundQuiver.IsSpecialBiserial k A := by
  apply (BoundQuiver.isSpecialBiserial_iff_of_moritaEquivalence e).2
  exact BoundQuiver.isSpecialBiserial_of_presentation
    (S.moritaBasicAlgebra_admitsSpecialBiserialPresentation_of_beta_le_two
      hbeta)

/-- For an arbitrary representation-finite algebra, the beta-two bound
implies the Morita-invariant special-biserial predicate. The all-module Morita
witness comes from the basic projective generator of the contragredient
skeleton; its target is the opposite algebra whose literal special-biserial
presentation is supplied by the opposite primitive-projective presentation. -/
theorem isSpecialBiserial_of_beta_le_two
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2) :
    BoundQuiver.IsSpecialBiserial k A := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Sop := S.contragredientSkeleton
  let Uop := Sop.moritaBasicSkeleton
  let Pop := Sop.moritaBasicPrimitiveProjectivePresentation
  letI : IsNoetherianRing Sop.moritaBasicAlgebra :=
    IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing (Sop.moritaBasicAlgebraᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  have hbetaOp : FiniteTauMatrix.beta
      Sop.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
    rw [S.contragredient_beta_eq_leftBeta]
    exact S.leftBeta_le_two_of_beta_le_two hbeta
  have hPop : Pop.IsBiserial :=
    Pop.isBiserial_of_beta_le_two
      (Sop.moritaBasicSkeleton_beta_le hbetaOp)
  have hPresentation : BoundQuiver.AdmitsSpecialBiserialPresentation k
      (Sop.moritaBasicAlgebra)ᵐᵒᵖ :=
    Pop.oppositePresentation.ambient_admitsSpecialBiserialPresentation_of_isBiserial
      (Pop.oppositePresentation_isBiserial hPop)
  let e : MoritaEquivalence k A (Sop.moritaBasicAlgebra)ᵐᵒᵖ :=
    S.allModuleMoritaEquivalenceToContragredientBasicOpposite
  apply (BoundQuiver.isSpecialBiserial_iff_of_moritaEquivalence e).2
  exact BoundQuiver.isSpecialBiserial_of_presentation hPresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
