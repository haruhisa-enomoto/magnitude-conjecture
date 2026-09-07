import MagnitudeConjecture.Algebra.RightModuleIdealQuotientTorsion
import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveARMesh
import MagnitudeConjecture.Algebra.RightModuleTauAssembly
import MagnitudeConjecture.CategoryTheory.AlmostSplitInjectiveKernel
import MagnitudeConjecture.CategoryTheory.FiniteTauAlmostSplitMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteTauRejection

/-!
# Socle rejection at a projective-injective module

Besides making `P / soc(P)` projective, rejection of the embedded socle of a
non-simple indecomposable projective-injective `P` makes `rad(P)` injective.
This file proves that assertion first in the full ambient subcategory
annihilated by the socle ideal and then transports it to the literal quotient
algebra.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

/-- The finite tau-category of the literal quotient by an arbitrary ideal,
with Noetherianity discharged from finite dimensionality. -/
def idealQuotientFiniteTauCategoryData
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (I : TwoSidedIdeal A)
    [IsNoetherianRing (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ] :
    QuotientSubmoduleEquidistribution.Iyama.FiniteTauCategoryData
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra I))
      (Fin (S.idealQuotientFiniteIndecomposableSkeleton I).n) :=
  (S.idealQuotientFiniteIndecomposableSkeleton I).finiteTauCategoryData

/-- The chosen ambient minimal right almost-split decomposition, reindexed
by a finite ordinal. -/
def minimalRightAlmostSplitAtDecomposition
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (x : Fin S.n) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (S.minimalRightAlmostSplitAt x).middle := by
  classical
  let B := S.minimalRightAlmostSplitAt x
  let n := Fintype.card B.index
  let epsilon : B.index ≃ Fin n := Fintype.equivFin B.index
  let summand : Fin n → RightModule.FinitelyGeneratedCategory A :=
    fun i ↦ S.fgObj (B.label (epsilon.symm i))
  let eReindex :
      S.almostSplitSkeleton.sumOver B.index B.label ≅ ⨁ summand :=
    biproduct.whiskerEquiv epsilon
      (fun i ↦ eqToIso (by
        simp only [summand, Equiv.symm_apply_apply]
        rfl))
  exact {
    n := n
    summand := summand
    indecomposable := fun i ↦ S.fgObj_indecomposable _
    isoBiproduct := B.decomposition.trans eReindex }

/-- A non-simple projective-injective vertex has exactly one incoming
right-middle occurrence. -/
theorem projectiveInjective_rightMiddleArity_eq_one
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p.label = 1 := by
  let B := S.minimalRightAlmostSplitAt p.label
  let d := S.minimalRightAlmostSplitAtDecomposition p.label
  have harity : MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p.label = d.n :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p.label d
        B.rightAlmostSplit B.rightMinimal
  change MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData p.label =
    Fintype.card B.index at harity
  exact harity.trans
    (PrimitiveProjectivePresentation.projectiveInjectiveRightMiddle_card_eq_one
      (S := S) p hpInjective hnotSimple)

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

include P in
/-- Away from `P / soc(P)`, the ambient minimal right almost-split middle
term contains no copy of the rejected projective-injective `P`. -/
theorem minimalRightAlmostSplitAt_label_ne_projectiveInjective_of_endpoint_ne
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : Fin S.n)
    (hx : x ≠
      (P.socleQuotientReplacementLabel
        p hpInjective hnotSimple).1)
    (t : (S.minimalRightAlmostSplitAt x).index) :
    (S.minimalRightAlmostSplitAt x).label t ≠ p.label := by
  intro ht
  let B := S.minimalRightAlmostSplitAt x
  have hirr : HasIrreducibleMorphism
      (S.fgObj p.label) (S.fgObj x) :=
    (B.summandIrreducibleCorrespondence p.label).1 ⟨t, ht⟩
  exact hx <| (P.hasIrreducibleMorphism_from_projectiveInjective_iff
    p hpInjective hnotSimple x).1 hirr

include P in
/-- Away from the exceptional endpoint `P / soc(P)`, the entire ambient
minimal right almost-split middle term is already a module over the socle
quotient. -/
theorem minimalRightAlmostSplitAt_middle_isAnnihilatedBy_of_endpoint_ne
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : Fin S.n)
    (hx : x ≠
      (P.socleQuotientReplacementLabel
        p hpInjective hnotSimple).1) :
    RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleIdeal p hpInjective)
      (S.minimalRightAlmostSplitAt x).middle := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let B := S.minimalRightAlmostSplitAt x
  have hsummand (t : B.index) :
      RightModule.IsAnnihilatedBy I (S.fgObj (B.label t)) :=
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
      p hpInjective (B.label t)).2
        (P.minimalRightAlmostSplitAt_label_ne_projectiveInjective_of_endpoint_ne
          p hpInjective hnotSimple x hx t)
  have hsum : RightModule.IsAnnihilatedBy I
      (⨁ fun t : B.index ↦ S.fgObj (B.label t)) :=
    RightModule.isAnnihilatedBy_biproduct I
      (fun t : B.index ↦ S.fgObj (B.label t)) hsummand
  exact (RightModule.IdealQuotientProperty I).prop_of_iso
    B.decomposition.symm hsum

include P in
/-- At every surviving endpoint other than `P / soc(P)`, projectivity in
the annihilated full subcategory is equivalent to ambient projectivity. -/
theorem socleQuotientLabelObj_projective_iff_ambient_of_endpoint_ne
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : S.IdealQuotientLabel
      (P.primitiveProjectiveSocleIdeal p hpInjective))
    (hx : x.1 ≠
      (P.socleQuotientReplacementLabel
        p hpInjective hnotSimple).1) :
    Projective
        (S.idealQuotientLabelObj
          (P.primitiveProjectiveSocleIdeal p hpInjective) x) ↔
      Projective (S.fgObj x.1) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let B := S.minimalRightAlmostSplitAt x.1
  exact RightModule.idealQuotient_projective_iff_of_minimal_sink_source_isAnnihilatedBy
    (k := k) (A := A) I
    (P.minimalRightAlmostSplitAt_middle_isAnnihilatedBy_of_endpoint_ne
      p hpInjective hnotSimple x.1 hx)
    x.2 B.map B.rightAlmostSplit B.rightMinimal

include P in
/-- The same ordinary-vertex projectivity comparison over the literal
socle quotient algebra. -/
theorem socleQuotientFGObj_projective_iff_ambient_of_endpoint_ne
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : S.IdealQuotientLabel
      (P.primitiveProjectiveSocleIdeal p hpInjective))
    (hx : x.1 ≠
      (P.socleQuotientReplacementLabel
        p hpInjective hnotSimple).1) :
    Projective
        (S.idealQuotientFGObj
          (P.primitiveProjectiveSocleIdeal p hpInjective) x) ↔
      Projective (S.fgObj x.1) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let Eq := RightModule.idealQuotientEquivalence (k := k) I
  exact (Eq.map_projective_iff
    (S.idealQuotientLabelObj I x)).trans
      (P.socleQuotientLabelObj_projective_iff_ambient_of_endpoint_ne
        p hpInjective hnotSimple x hx)

/-- Intrinsic socle-quotient labels are exactly the ambient labels other
than the rejected projective-injective label. -/
def socleQuotientSurvivingEquiv
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    S.IdealQuotientLabel
        (P.primitiveProjectiveSocleIdeal p hpInjective) ≃
      {i : Fin S.n // i ≠ p.label} where
  toFun x := ⟨x.1,
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
      p hpInjective x.1).1 x.2⟩
  invFun x := ⟨x.1,
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
      p hpInjective x.1).2 x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

/-- The finite-ordinal quotient labels are equivalent to the ambient labels
surviving rejection. -/
def socleQuotientFiniteSurvivingEquiv
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ] :
    Fin (S.idealQuotientFiniteIndecomposableSkeleton
        (P.primitiveProjectiveSocleIdeal p hpInjective)).n ≃
      {i : Fin S.n // i ≠ p.label} :=
  (S.idealQuotientFiniteLabelEquiv
      (P.primitiveProjectiveSocleIdeal p hpInjective)).trans
    (P.socleQuotientSurvivingEquiv p hpInjective)

/-- The finite quotient-skeleton label corresponding to an ambient label
other than the rejected projective-injective. -/
def socleQuotientFiniteSurvivorLabel
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (i : Fin S.n) (hi : i ≠ p.label) :
    Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleIdeal p hpInjective)).n :=
  (P.socleQuotientFiniteSurvivingEquiv p hpInjective).symm ⟨i, hi⟩

@[simp]
theorem socleQuotientFiniteSurvivingEquiv_survivorLabel
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (i : Fin S.n) (hi : i ≠ p.label) :
    P.socleQuotientFiniteSurvivingEquiv p hpInjective
        (P.socleQuotientFiniteSurvivorLabel
          p hpInjective i hi) = ⟨i, hi⟩ :=
  Equiv.apply_symm_apply _ _

/-- The finite quotient representative of a surviving ambient label is the
literal quotient module obtained from that ambient object. -/
def socleQuotientFiniteSurvivorIso
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (i : Fin S.n) (hi : i ≠ p.label) :
    (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleIdeal p hpInjective)).fgObj
        (P.socleQuotientFiniteSurvivorLabel
          p hpInjective i hi) ≅
      (RightModule.idealQuotientEquivalence
        (k := k) (P.primitiveProjectiveSocleIdeal p hpInjective)).functor.obj
        (S.idealQuotientLabelObj
          (P.primitiveProjectiveSocleIdeal p hpInjective)
          ⟨i,
            (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
              p hpInjective i).2 hi⟩) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let j := P.socleQuotientFiniteSurvivorLabel p hpInjective i hi
  let x : S.IdealQuotientLabel I :=
    ⟨i, (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
      p hpInjective i).2 hi⟩
  have hj : S.idealQuotientFiniteLabelEquiv I j = x := by
    apply (P.socleQuotientSurvivingEquiv p hpInjective).injective
    exact P.socleQuotientFiniteSurvivingEquiv_survivorLabel
      p hpInjective i hi
  exact (S.idealQuotientFiniteFGObjIso I j).trans
    ((RightModule.idealQuotientEquivalence (k := k) I).functor.mapIso
      (eqToIso (congrArg (S.idealQuotientLabelObj I) hj)))

include P in
/-- Every other projective-injective vertex remains projective-injective
after rejecting the socle of `p`. -/
theorem socleQuotient_other_projectiveInjective
    (p q : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hq : q.label ≠ p.label)
    (hqInjective : Injective (S.fgObj q.label)) :
    Projective
        ((S.idealQuotientFiniteIndecomposableSkeleton
          (P.primitiveProjectiveSocleIdeal p hpInjective)).fgObj
            (P.socleQuotientFiniteSurvivorLabel p hpInjective q.label
              hq)) ∧
      Injective
        ((S.idealQuotientFiniteIndecomposableSkeleton
          (P.primitiveProjectiveSocleIdeal p hpInjective)).fgObj
            (P.socleQuotientFiniteSurvivorLabel p hpInjective q.label
              hq)) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let hlabel : q.label ≠ p.label := hq
  let hAnn : RightModule.IsAnnihilatedBy I (S.fgObj q.label) :=
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
      p hpInjective q.label).2 hlabel
  let e := P.socleQuotientFiniteSurvivorIso
    p hpInjective q.label hlabel
  have hProjective : Projective
      ((RightModule.idealQuotientEquivalence (k := k) I).functor.obj
        (⟨S.fgObj q.label, hAnn⟩ : RightModule.IdealQuotientSubcategory I)) :=
    RightModule.idealQuotientFGObj_projective_of_ambient
      (k := k) I (S.fgObj q.label) hAnn q.projective
  have hInjective : Injective
      ((RightModule.idealQuotientEquivalence (k := k) I).functor.obj
        (⟨S.fgObj q.label, hAnn⟩ : RightModule.IdealQuotientSubcategory I)) :=
    RightModule.idealQuotientFGObj_injective_of_ambient
      (k := k) I (S.fgObj q.label) hAnn hqInjective
  exact ⟨Projective.of_iso e.symm hProjective,
    Injective.of_iso e.symm hInjective⟩

include P in
/-- A distinct ambient nonsimple projective-injective remains nonsimple as
a module over the one-step socle quotient. -/
theorem socleQuotient_other_not_isSimpleModule
    (p q : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hq : q.label ≠ p.label)
    (hqNotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj q.label)) :
    ¬ IsSimpleModule
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ
      ((S.idealQuotientFiniteIndecomposableSkeleton
        (P.primitiveProjectiveSocleIdeal p hpInjective)).fgObj
          (P.socleQuotientFiniteSurvivorLabel
            p hpInjective q.label hq)) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let hAnn : RightModule.IsAnnihilatedBy I (S.fgObj q.label) :=
    (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
      p hpInjective q.label).2 hq
  let e := P.socleQuotientFiniteSurvivorIso
    p hpInjective q.label hq
  intro hSimple
  have hFiniteSimple : Simple
      ((S.idealQuotientFiniteIndecomposableSkeleton I).fgObj
        (P.socleQuotientFiniteSurvivorLabel p hpInjective q.label hq)) :=
    (RightModule.fgModule_simple_iff_isSimpleModule _).2 hSimple
  letI : Simple
      ((S.idealQuotientFiniteIndecomposableSkeleton I).fgObj
        (P.socleQuotientFiniteSurvivorLabel p hpInjective q.label hq)) :=
    hFiniteSimple
  have hMappedSimple : Simple
      ((RightModule.idealQuotientEquivalence (k := k) I).functor.obj
        (⟨S.fgObj q.label, hAnn⟩ : RightModule.IdealQuotientSubcategory I)) :=
    Simple.of_iso e.symm
  have hAmbientSimple : Simple (S.fgObj q.label) :=
    (idealQuotientFGObj_simple_iff_ambient
      (I := I)
      (⟨S.fgObj q.label, hAnn⟩ : RightModule.IdealQuotientSubcategory I)).1
        hMappedSimple
  exact hqNotSimple
    ((RightModule.fgModule_simple_iff_isSimpleModule _).1 hAmbientSimple)

/-- The replacement vertex in the finite-ordinal quotient skeleton. -/
def socleQuotientFiniteReplacementLabel
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleIdeal p hpInjective)).n :=
  (S.idealQuotientFiniteLabelEquiv
    (P.primitiveProjectiveSocleIdeal p hpInjective)).symm
      (P.socleQuotientReplacementLabel p hpInjective hnotSimple)

@[simp]
theorem idealQuotientFiniteLabelEquiv_socleQuotientFiniteReplacementLabel
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleIdeal p hpInjective)
        (P.socleQuotientFiniteReplacementLabel
          p hpInjective hnotSimple) =
      P.socleQuotientReplacementLabel p hpInjective hnotSimple :=
  Equiv.apply_symm_apply _ _

include P in
/-- The replacement vertex is nonprojective in the ambient finite-tau
presentation. -/
theorem socleQuotientFiniteReplacement_ambient_not_isProjective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    ¬ S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
      (S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleIdeal p hpInjective)
        (P.socleQuotientFiniteReplacementLabel
          p hpInjective hnotSimple)).1 := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
  change ¬ Projective
    (S.fgObj
      (S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleIdeal p hpInjective)
        (P.socleQuotientFiniteReplacementLabel
          p hpInjective hnotSimple)).1)
  rw [P.idealQuotientFiniteLabelEquiv_socleQuotientFiniteReplacementLabel
    p hpInjective hnotSimple]
  exact P.socleQuotientReplacementLabel_not_projective
    p hpInjective hnotSimple

include P in
/-- The replacement vertex is projective in the rejected finite-tau
presentation. -/
theorem socleQuotientFiniteReplacement_isProjective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    (idealQuotientFiniteTauCategoryData S
      (P.primitiveProjectiveSocleIdeal p hpInjective)
        ).toFiniteRightTauCategoryData.IsProjective
      (P.socleQuotientFiniteReplacementLabel
        p hpInjective hnotSimple) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra I)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ
  rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
  change Projective
    (S.idealQuotientFGObj
      (P.primitiveProjectiveSocleIdeal p hpInjective)
      (S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleIdeal p hpInjective)
        (P.socleQuotientFiniteReplacementLabel
          p hpInjective hnotSimple)))
  rw [P.idealQuotientFiniteLabelEquiv_socleQuotientFiniteReplacementLabel
    p hpInjective hnotSimple]
  exact P.socleQuotientReplacementLabel_projective
    p hpInjective hnotSimple

include P in
/-- In the finite-tau presentations, projectivity is unchanged at every
ordinary surviving endpoint. -/
theorem socleQuotient_isProjective_iff_ambient_of_endpoint_ne
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (j : Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleIdeal p hpInjective)).n)
    (hj : (S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleIdeal p hpInjective) j).1 ≠
      (P.socleQuotientReplacementLabel
        p hpInjective hnotSimple).1) :
    S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
        (S.idealQuotientFiniteLabelEquiv
          (P.primitiveProjectiveSocleIdeal p hpInjective) j).1 ↔
      (idealQuotientFiniteTauCategoryData S
        (P.primitiveProjectiveSocleIdeal p hpInjective)
          ).toFiniteRightTauCategoryData.IsProjective j := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let q := S.idealQuotientFiniteLabelEquiv I
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let TQ := (idealQuotientFiniteTauCategoryData S I).toFiniteRightTauCategoryData
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra I)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ
  rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj,
    MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
  change Projective (S.fgObj (q j).1) ↔
    Projective (S.idealQuotientFGObj I (q j))
  exact (P.socleQuotientFGObj_projective_iff_ambient_of_endpoint_ne
    p hpInjective hnotSimple (q j) hj).symm

include P in
/-- Every ordinary surviving endpoint has the same incoming right-mesh
arity before and after rejection of the projective-injective socle. -/
theorem socleQuotient_rightMiddleArity_eq_ambient_of_endpoint_ne
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (j : Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleIdeal p hpInjective)).n)
    (hj : (S.idealQuotientFiniteLabelEquiv
        (P.primitiveProjectiveSocleIdeal p hpInjective) j).1 ≠
      (P.socleQuotientReplacementLabel
        p hpInjective hnotSimple).1) :
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (S.idealQuotientFiniteLabelEquiv
          (P.primitiveProjectiveSocleIdeal p hpInjective) j).1 =
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleIdeal p hpInjective)
            ).toFiniteRightTauCategoryData j := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let q := S.idealQuotientFiniteLabelEquiv I
  let x := q j
  let B := S.minimalRightAlmostSplitAt x.1
  let dA := S.minimalRightAlmostSplitAtDecomposition x.1
  have hE : RightModule.IsAnnihilatedBy I B.middle :=
    P.minimalRightAlmostSplitAt_middle_isAnnihilatedBy_of_endpoint_ne
      p hpInjective hnotSimple x.1 hj
  have hsummand (i : Fin dA.n) :
      RightModule.IsAnnihilatedBy I (dA.summand i) := by
    change RightModule.IsAnnihilatedBy I
      (S.fgObj (B.label ((Fintype.equivFin B.index).symm i)))
    exact (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
      p hpInjective _).2
        (P.minimalRightAlmostSplitAt_label_ne_projectiveInjective_of_endpoint_ne
          p hpInjective hnotSimple x.1 hj
            ((Fintype.equivFin B.index).symm i))
  let dQ := RightModule.idealTorsionTargetSourceDecomposition
    (k := k) I B.middle hE dA hsummand
  let Eq := RightModule.idealQuotientEquivalence (k := k) I
  let restricted := RightModule.idealTorsionTargetMap I x.2 B.map
  let mapped := Eq.functor.map restricted
  have hmappedAS : IsRightAlmostSplit mapped :=
    (RightModule.idealTorsionTargetMap_isRightAlmostSplit
      I x.2 B.map B.rightAlmostSplit).map_equivalence Eq
  have hmappedMin : IsRightMinimal mapped :=
    (RightModule.idealTorsionTargetMap_isRightMinimal_of_source_isAnnihilatedBy
      I hE x.2 B.map B.rightMinimal).map_equivalence Eq
  let TQ := (idealQuotientFiniteTauCategoryData S I).toFiniteRightTauCategoryData
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  have hQ : MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TQ j = dQ.n :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TQ j dQ hmappedAS hmappedMin
  have hA : MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TA x.1 = dA.n :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TA x.1 dA B.rightAlmostSplit B.rightMinimal
  exact hA.trans (hQ.trans (by rfl)).symm

include P in
/-- The radical boundary object is not injective in the ambient module
category. -/
theorem projectiveInjectiveBoundaryRadical_not_injective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    ¬ Injective (S.projectiveBoundaryRadical p.label) := by
  intro hradInjective
  let z := P.socleQuotientReplacementNonprojectiveLabel
    p hpInjective hnotSimple
  apply (S.chosenRight_kernel_ar_sequence z).2.2.2
  exact Injective.of_iso
    (P.socleQuotientReplacementKernelIso
      p hpInjective hnotSimple).symm hradInjective

include P in
/-- The embedded socle ideal annihilates the radical boundary object. -/
theorem projectiveInjectiveBoundaryRadical_isAnnihilatedBy
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    RightModule.IsAnnihilatedBy
      (P.primitiveProjectiveSocleIdeal p hpInjective)
      (S.projectiveBoundaryRadical p.label) := by
  apply P.isAnnihilatedBy_primitiveProjectiveSocleIdeal_of_not_iso
    p hpInjective
      (S.projectiveBoundaryRadical p.label)
      (projectiveInjectiveBoundaryRadical_indecomposable
        p hpInjective hnotSimple)
  rintro ⟨e⟩
  apply P.projectiveInjectiveBoundaryRadical_not_injective
    p hpInjective hnotSimple
  exact Injective.of_iso e.symm hpInjective

include P in
/-- The maximal submodule of the rejected projective-injective annihilated
by its embedded socle ideal is its Jacobson radical. -/
def idealTorsionFGObj_projectiveInjectiveIsoRadical
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    RightModule.idealTorsionFGObj
        (P.primitiveProjectiveSocleIdeal p hpInjective)
        (S.fgObj p.label) ≅
      S.projectiveBoundaryRadical p.label := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let T := RightModule.idealTorsionFGObj I (S.fgObj p.label)
  let ti := RightModule.idealTorsionInclusion I (S.fgObj p.label)
  let R := S.projectiveBoundaryRadical p.label
  let j := S.projectiveBoundaryRadicalInclusion p.label
  have hR : RightModule.IsAnnihilatedBy I R :=
    P.projectiveInjectiveBoundaryRadical_isAnnihilatedBy
      p hpInjective hnotSimple
  have htiNotSplit : ¬ IsSplitEpi ti := by
    intro hs
    obtain ⟨s⟩ := hs.exists_splitEpi
    let r : Retract (S.fgObj p.label) T :=
      { i := s.section_
        r := ti
        retract := s.id }
    have hP : RightModule.IsAnnihilatedBy I (S.fgObj p.label) :=
      (RightModule.IdealQuotientProperty I).prop_of_retract r
        (RightModule.idealTorsionFGObj_isAnnihilatedBy
          I (S.fgObj p.label))
    exact (P.fgObj_not_isAnnihilatedBy_primitiveProjectiveSocleIdeal
      p hpInjective) hP
  let hex :=
    (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit
      p.label p.projective).factors ti htiNotSplit
  let h := Classical.choose hex
  have hh : h ≫ j = ti := Classical.choose_spec hex
  let l : R ⟶ T := RightModule.idealTorsionLift I hR j
  have hl : l ≫ ti = j :=
    RightModule.idealTorsionLift_comp_inclusion I hR j
  letI : Mono ti := by
    dsimp only [ti]
    infer_instance
  letI : Mono j := by
    apply (IndecomposableSkeleton.fg_mono_iff_injective j).2
    exact (Module.jacobson Aᵐᵒᵖ (S.fgObj p.label)).subtype_injective
  exact {
    hom := h
    inv := l
    hom_inv_id := by
      apply (cancel_mono ti).1
      rw [Category.assoc, hl, hh, Category.id_comp]
    inv_hom_id := by
      apply (cancel_mono j).1
      rw [Category.assoc, hh, hl, Category.id_comp] }

include P in
/-- The restricted source at the exceptional endpoint has a displayed
indecomposable decomposition with the same number of terms as the ambient
right almost-split middle term.  The rejected summand becomes `rad(P)`;
every other summand is already annihilated by the socle ideal. -/
def socleQuotientExceptionalSourceDecomposition
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      ((RightModule.idealQuotientEquivalence
          (k := k) (P.primitiveProjectiveSocleIdeal p hpInjective)).functor.obj
        (RightModule.idealTorsionSubcategoryObj
          (P.primitiveProjectiveSocleIdeal p hpInjective)
          (S.minimalRightAlmostSplitAt
            (P.socleQuotientReplacementNonprojectiveLabel
              p hpInjective hnotSimple).1).middle)) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let z := P.socleQuotientReplacementNonprojectiveLabel
    p hpInjective hnotSimple
  let B := S.minimalRightAlmostSplitAt z.1
  let dA := S.minimalRightAlmostSplitAtDecomposition z.1
  have hIndec (i : Fin dA.n) : Indecomposable
      ((RightModule.idealTorsionFunctor I).obj (dA.summand i)) := by
    let t := (Fintype.equivFin B.index).symm i
    change Indecomposable
      (RightModule.idealTorsionFGObj I (S.fgObj (B.label t)))
    by_cases hi : B.label t = p.label
    · rw [hi]
      exact
        (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso
          (P.idealTorsionFGObj_projectiveInjectiveIsoRadical
            p hpInjective hnotSimple)).2
          (projectiveInjectiveBoundaryRadical_indecomposable
            p hpInjective hnotSimple)
    · let hAnn : RightModule.IsAnnihilatedBy I
          (S.fgObj (B.label t)) :=
        (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleIdeal_iff
          p hpInjective (B.label t)).2 hi
      exact
        (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso
          (RightModule.idealTorsionIsoOfIsAnnihilated
            I (S.fgObj (B.label t)) hAnn)).2
          (S.fgObj_indecomposable (B.label t))
  let dT := dA.mapOfIndecomposable
    (RightModule.idealTorsionFunctor I) hIndec
  exact RightModule.idealTorsionSourceDecomposition
    (k := k) I B.middle dT
      (fun i ↦ RightModule.idealTorsionFGObj_isAnnihilatedBy
        I (dA.summand i))

/-- The radical boundary object bundled in the full annihilated
subcategory. -/
def projectiveInjectiveBoundaryRadicalObj
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    RightModule.IdealQuotientSubcategory
      (P.primitiveProjectiveSocleIdeal p hpInjective) :=
  ⟨S.projectiveBoundaryRadical p.label,
    P.projectiveInjectiveBoundaryRadical_isAnnihilatedBy
      p hpInjective hnotSimple⟩

include P in
/-- After socle rejection, `rad(P)` is injective in the annihilated ambient
full subcategory. -/
theorem projectiveInjectiveBoundaryRadicalObj_injective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Injective
      (P.projectiveInjectiveBoundaryRadicalObj
        p hpInjective hnotSimple) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let U := (RightModule.IdealQuotientProperty I).ι
  let R := P.projectiveInjectiveBoundaryRadicalObj
    p hpInjective hnotSimple
  let j := S.projectiveBoundaryRadicalInclusion p.label
  letI : Injective (S.fgObj p.label) := hpInjective
  refine { factors := ?_ }
  intro X Y g f _
  letI : (RightModule.IdealQuotientProperty I).Nonempty :=
    ObjectProperty.nonempty_of_prop R.property
  letI : U.PreservesMonomorphisms :=
    (RightModule.IdealQuotientProperty I)
      |>.preservesMonomorphisms_ι_of_isNormalEpiCategory
  haveI : Mono f.hom := by
    change Mono (U.map f)
    infer_instance
  obtain ⟨h, hh⟩ := Injective.factors (g.hom ≫ j) f.hom
  have hnotSplit : ¬ IsSplitEpi h := by
    intro hs
    obtain ⟨s⟩ := hs.exists_splitEpi
    let r : Retract (S.fgObj p.label) Y.obj :=
      { i := s.section_
        r := h
        retract := s.id }
    have hPannihilated : RightModule.IsAnnihilatedBy I
        (S.fgObj p.label) :=
      (RightModule.IdealQuotientProperty I).prop_of_retract r Y.property
    exact (P.fgObj_not_isAnnihilatedBy_primitiveProjectiveSocleIdeal
      p hpInjective) hPannihilated
  obtain ⟨l, hl⟩ :=
    (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit
      p.label p.projective).factors h hnotSplit
  refine ⟨ObjectProperty.homMk l, ?_⟩
  apply ObjectProperty.hom_ext
  letI : Mono j := by
    apply (IndecomposableSkeleton.fg_mono_iff_injective j).2
    exact (Module.jacobson Aᵐᵒᵖ (S.fgObj p.label)).subtype_injective
  apply (cancel_mono j).1
  change (f.hom ≫ l) ≫ j = g.hom ≫ j
  rw [Category.assoc, hl]
  exact hh

/-- The literal quotient-algebra module corresponding to `rad(P)`. -/
def projectiveInjectiveBoundaryRadicalAlgebraFGObj
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    RightModule.FinitelyGeneratedCategory
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective)) :=
  (RightModule.idealQuotientEquivalence
    (k := k) (P.primitiveProjectiveSocleIdeal p hpInjective)).functor.obj
      (P.projectiveInjectiveBoundaryRadicalObj
        p hpInjective hnotSimple)

/-- The transported radical boundary module is injective over the literal
socle quotient algebra. -/
theorem projectiveInjectiveBoundaryRadicalAlgebraFGObj_injective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Injective
      (P.projectiveInjectiveBoundaryRadicalAlgebraFGObj
        p hpInjective hnotSimple) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let E := RightModule.idealQuotientEquivalence (k := k) I
  exact (E.map_injective_iff
    (P.projectiveInjectiveBoundaryRadicalObj
      p hpInjective hnotSimple)).2
        (P.projectiveInjectiveBoundaryRadicalObj_injective
          p hpInjective hnotSimple)

/-- The intrinsic quotient-skeleton label represented by `rad(P)`. -/
def socleQuotientRadicalLabel
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    S.IdealQuotientLabel
      (P.primitiveProjectiveSocleIdeal p hpInjective) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let e := projectiveInjectiveBoundaryRadicalIso
    p hpInjective hnotSimple
  exact ⟨projectiveInjectiveBoundaryRadicalLabel
      p hpInjective hnotSimple,
    (RightModule.IdealQuotientProperty I).prop_of_iso e
      (P.projectiveInjectiveBoundaryRadical_isAnnihilatedBy
        p hpInjective hnotSimple)⟩

/-- The literal transported radical is isomorphic to its intrinsic
quotient-skeleton representative. -/
def projectiveInjectiveBoundaryRadicalReplacementIso
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    P.projectiveInjectiveBoundaryRadicalAlgebraFGObj
        p hpInjective hnotSimple ≅
      S.idealQuotientFGObj
        (P.primitiveProjectiveSocleIdeal p hpInjective)
        (P.socleQuotientRadicalLabel p hpInjective hnotSimple) := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let E := RightModule.idealQuotientEquivalence (k := k) I
  apply E.functor.mapIso
  exact ObjectProperty.isoMk _
    (projectiveInjectiveBoundaryRadicalIso
      p hpInjective hnotSimple)

/-- The intrinsic radical label is injective over the socle quotient
algebra. -/
theorem socleQuotientRadicalLabel_injective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Injective
      (S.idealQuotientFGObj
        (P.primitiveProjectiveSocleIdeal p hpInjective)
        (P.socleQuotientRadicalLabel p hpInjective hnotSimple)) :=
  Injective.of_iso
    (P.projectiveInjectiveBoundaryRadicalReplacementIso
      p hpInjective hnotSimple)
    (P.projectiveInjectiveBoundaryRadicalAlgebraFGObj_injective
      p hpInjective hnotSimple)

include P in
/-- At the exceptional endpoint `P / soc(P)`, socle rejection removes
exactly one indecomposable occurrence from the incoming right mesh. -/
theorem socleQuotient_replacement_rightMiddleArity_add_one_eq_ambient
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleIdeal p hpInjective)
            ).toFiniteRightTauCategoryData
        (P.socleQuotientFiniteReplacementLabel
          p hpInjective hnotSimple) + 1 =
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (S.idealQuotientFiniteLabelEquiv
          (P.primitiveProjectiveSocleIdeal p hpInjective)
          (P.socleQuotientFiniteReplacementLabel
            p hpInjective hnotSimple)).1 := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let r := P.socleQuotientReplacementLabel p hpInjective hnotSimple
  let j := P.socleQuotientFiniteReplacementLabel
    p hpInjective hnotSimple
  let z := P.socleQuotientReplacementNonprojectiveLabel
    p hpInjective hnotSimple
  let B := S.minimalRightAlmostSplitAt z.1
  let dA := S.minimalRightAlmostSplitAtDecomposition z.1
  let Eq := RightModule.idealQuotientEquivalence (k := k) I
  let C := RightModule.IdealQuotientSubcategory I
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      Eq.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence Eq.functor
  let restricted := RightModule.idealTorsionTargetMap I r.2 B.map
  let mapped := Eq.functor.map restricted
  let dSource := P.socleQuotientExceptionalSourceDecomposition
    p hpInjective hnotSimple
  let R := P.projectiveInjectiveBoundaryRadicalObj
    p hpInjective hnotSimple
  have hKernelAnnihilated : RightModule.IsAnnihilatedBy I (kernel B.map) :=
    (RightModule.IdealQuotientProperty I).prop_of_iso
      (P.socleQuotientReplacementKernelIso
        p hpInjective hnotSimple).symm
      (P.projectiveInjectiveBoundaryRadical_isAnnihilatedBy
        p hpInjective hnotSimple)
  let eRestrictedKernel : kernel restricted ≅ R :=
    (RightModule.idealTorsionTargetKernelIso
      I r.2 B.map hKernelAnnihilated).trans
        (ObjectProperty.isoMk _
          (P.socleQuotientReplacementKernelIso
            p hpInjective hnotSimple))
  let eMappedKernel : kernel mapped ≅ Eq.functor.obj R :=
    (PreservesKernel.iso Eq.functor restricted).symm.trans
      (Eq.functor.mapIso eRestrictedKernel)
  have hRIndec : Indecomposable R :=
    (idealQuotientSubcategory_indecomposable_iff_ambient
      (I := I) R).2
      (projectiveInjectiveBoundaryRadical_indecomposable
        p hpInjective hnotSimple)
  have hEqRIndec : Indecomposable (Eq.functor.obj R) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      Eq.functor R).2 hRIndec
  have hKernelIndec : Indecomposable (kernel mapped) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso
      eMappedKernel).2 hEqRIndec
  have hEqRInjective : Injective (Eq.functor.obj R) :=
    (Eq.map_injective_iff R).2
      (P.projectiveInjectiveBoundaryRadicalObj_injective
        p hpInjective hnotSimple)
  have hKernelInjective : Injective (kernel mapped) :=
    Injective.of_iso eMappedKernel.symm hEqRInjective
  letI : Injective (kernel mapped) := hKernelInjective
  have hmappedAS : IsRightAlmostSplit mapped :=
    (RightModule.idealTorsionTargetMap_isRightAlmostSplit
      I r.2 B.map B.rightAlmostSplit).map_equivalence Eq
  obtain ⟨E', g, hgMono, hgAS, hgMin, hSplit⟩ :=
    MagnitudeConjecture.CategoryTheory.exists_mono_rightAlmostSplit_complement_of_injective_kernel
      mapped hmappedAS
  letI : Mono g := hgMono
  letI : Module k E' := Module.restrictScalars k
    (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ E'
  letI : IsScalarTower k
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ E' :=
    IsScalarTower.restrictScalars k
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ E'
  letI : Module.Finite k E' :=
    RightModule.finite_over_field_of_finitelyGenerated k
      (RightModule.idealQuotientAlgebra I) E'
  obtain ⟨dE⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) E'
  let dK :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
      (kernel mapped) hKernelIndec
  let dSum := dK.biprod dE
  have hlocal (i : Fin dSource.n) :
      IsLocalRing (End (dSource.summand i)) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := RightModule.idealQuotientAlgebra I)
        (dSource.summand i) (dSource.indecomposable i)
  have hcount := dSource.n_eq_of_iso dSum hlocal (Classical.choice hSplit)
  change dA.n = 1 + dE.n at hcount
  let q := S.idealQuotientFiniteLabelEquiv I
  have hj : q j = r := by
    exact P.idealQuotientFiniteLabelEquiv_socleQuotientFiniteReplacementLabel
      p hpInjective hnotSimple
  let TQ :=
    (idealQuotientFiniteTauCategoryData S I).toFiniteRightTauCategoryData
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let eTarget : Eq.functor.obj (S.idealQuotientLabelObj I r) ≅ TQ.obj j :=
    Eq.functor.mapIso
      (eqToIso (congrArg (S.idealQuotientLabelObj I) hj.symm))
  let g' : E' ⟶ TQ.obj j := g ≫ eTarget.hom
  have hg'AS : IsRightAlmostSplit g' :=
    IsRightAlmostSplit.postcomp_iso eTarget hgAS
  have hg'Min : IsRightMinimal g' :=
    IsRightMinimal.postcomp_iso eTarget hgMin
  have hQ : MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      TQ j = dE.n :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TQ j dE hg'AS hg'Min
  have hA : MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      TA z.1 = dA.n :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TA z.1 dA B.rightAlmostSplit B.rightMinimal
  change MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TQ j + 1 =
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TA (q j).1
  have hz : (q j).1 = z.1 := congrArg Subtype.val hj
  rw [hQ, hz, hA]
  omega

/-- The complete finite-tau rejection profile produced by removing the
socle of one non-simple indecomposable projective-injective module. -/
def socleQuotientRejectionProfile
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    MagnitudeConjecture.FiniteTauMatrix.RejectionProfile
      S.finiteTauCategoryData.toFiniteRightTauCategoryData
      (idealQuotientFiniteTauCategoryData S
        (P.primitiveProjectiveSocleIdeal p hpInjective)
          ).toFiniteRightTauCategoryData := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let q := S.idealQuotientFiniteLabelEquiv I
  let replacement := P.socleQuotientFiniteReplacementLabel
    p hpInjective hnotSimple
  have hreplacement : q replacement =
      P.socleQuotientReplacementLabel p hpInjective hnotSimple :=
    P.idealQuotientFiniteLabelEquiv_socleQuotientFiniteReplacementLabel
      p hpInjective hnotSimple
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra I)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ
  refine {
    deleted := p.label
    replacement := replacement
    surviving := P.socleQuotientFiniteSurvivingEquiv p hpInjective
    deleted_projective := ?_
    deleted_arity := S.projectiveInjective_rightMiddleArity_eq_one
      p hpInjective hnotSimple
    replacement_ambient_nonprojective := ?_
    replacement_rejected_projective :=
      P.socleQuotientFiniteReplacement_isProjective
        p hpInjective hnotSimple
    projective_iff_of_ne := ?_
    replacement_arity :=
      P.socleQuotient_replacement_rightMiddleArity_add_one_eq_ambient
        p hpInjective hnotSimple
    arity_eq_of_ne := ?_ }
  · rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
    exact p.projective
  · change ¬ (S.finiteTauCategoryData.toFiniteRightTauCategoryData
        ).IsProjective (q replacement).1
    exact P.socleQuotientFiniteReplacement_ambient_not_isProjective
      p hpInjective hnotSimple
  · intro j hj
    have hj' : (q j).1 ≠
        (P.socleQuotientReplacementLabel
          p hpInjective hnotSimple).1 := by
      intro heq
      apply hj
      apply q.injective
      apply Subtype.ext
      exact heq.trans (congrArg Subtype.val hreplacement).symm
    change
      ((S.finiteTauCategoryData.toFiniteRightTauCategoryData
          ).IsProjective (q j).1 ↔
        ((idealQuotientFiniteTauCategoryData S I
          ).toFiniteRightTauCategoryData).IsProjective j)
    exact P.socleQuotient_isProjective_iff_ambient_of_endpoint_ne
      p hpInjective hnotSimple j hj'
  · intro j hj
    have hj' : (q j).1 ≠
        (P.socleQuotientReplacementLabel
          p hpInjective hnotSimple).1 := by
      intro heq
      apply hj
      apply q.injective
      apply Subtype.ext
      exact heq.trans (congrArg Subtype.val hreplacement).symm
    change
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData (q j).1 =
        MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
          (idealQuotientFiniteTauCategoryData S I
            ).toFiniteRightTauCategoryData j
    exact P.socleQuotient_rightMiddleArity_eq_ambient_of_endpoint_ne
      p hpInjective hnotSimple j hj'

include P in
/-- Removing the socle of one non-simple indecomposable
projective-injective preserves the finite Auslander--Reiten Euler
magnitude. -/
theorem socleQuotient_eulerMagnitude_eq
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleIdeal p hpInjective))ᵐᵒᵖ]
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    @MagnitudeConjecture.ARCount.eulerMagnitude _ _
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData)
        S.finiteTauCategoryData.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) =
      @MagnitudeConjecture.ARCount.eulerMagnitude _ _
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          (idealQuotientFiniteTauCategoryData S
            (P.primitiveProjectiveSocleIdeal p hpInjective)
              ).toFiniteRightTauCategoryData)
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleIdeal p hpInjective)
            ).toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) :=
  (P.socleQuotientRejectionProfile
    p hpInjective hnotSimple).eulerMagnitude_eq

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
