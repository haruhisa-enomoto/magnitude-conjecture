import MagnitudeConjecture.Algebra.RightModuleBetaBoundary
import MagnitudeConjecture.Algebra.RightModuleBetaProjectiveRadical
import MagnitudeConjecture.Algebra.RightModuleGabrielBetaComparison
import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveSocleFamily
import MagnitudeConjecture.CategoryTheory.IrreducibleShortExactAlmostSplit

/-!
# Beta bounds after rejecting all projective-injective socles

For the family of all non-simple indecomposable projective-injective right
modules, every nonprojective mesh of the simultaneous socle quotient is an
unchanged ambient mesh with no projective-injective middle summand.  Thus the
left/right beta boundary estimate bounds its total middle arity.

This is the occurrence-level content of Auslander--Reiten, *Uniserial
functors*, Lemma 4.2, separated from the later uniserial-functor argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

set_option synthInstance.maxHeartbeats 100000

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The basic family of all non-simple indecomposable projective-injective
right modules.  Simple projective-injectives cannot occur in a nontrivial
almost-split middle term, so this is the full family relevant to socle
reduction. -/
def nonsimpleProjectiveInjectiveLabels : Finset S.ProjectiveLabel := by
  classical
  exact Finset.univ.filter fun p ↦
    Injective (S.fgObj p.label) ∧
      ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)

@[simp]
theorem mem_nonsimpleProjectiveInjectiveLabels_iff
    (p : S.ProjectiveLabel) :
    p ∈ S.nonsimpleProjectiveInjectiveLabels ↔
      Injective (S.fgObj p.label) ∧
        ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label) := by
  classical
  simp [nonsimpleProjectiveInjectiveLabels]

/-- Every selected label in the all-projective-injective family is
injective. -/
theorem nonsimpleProjectiveInjectiveLabels_injective
    (p : S.ProjectiveLabel)
    (hp : p ∈ S.nonsimpleProjectiveInjectiveLabels) :
    Injective (S.fgObj p.label) :=
  (S.mem_nonsimpleProjectiveInjectiveLabels_iff p).1 hp |>.1

/-- Every selected label in the all-projective-injective family is
non-simple. -/
theorem nonsimpleProjectiveInjectiveLabels_notSimple
    (p : S.ProjectiveLabel)
    (hp : p ∈ S.nonsimpleProjectiveInjectiveLabels) :
    ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label) :=
  (S.mem_nonsimpleProjectiveInjectiveLabels_iff p).1 hp |>.2

/-- An injective occurrence in a minimal right almost-split middle term
cannot be simple.  Indeed, a nonzero map from a simple object is monic, and
injectivity would split that irreducible component. -/
theorem rightMiddleLabel_not_simple_of_injective
    (z : Fin S.n)
    (i : (S.minimalRightAlmostSplitAt z).index)
    (hi : Injective
      (S.fgObj ((S.minimalRightAlmostSplitAt z).label i))) :
    ¬ IsSimpleModule Aᵐᵒᵖ
      (S.fgObj ((S.minimalRightAlmostSplitAt z).label i)) := by
  intro hsimple
  let B := S.minimalRightAlmostSplitAt z
  let f := B.component S.almostSplitSkeleton i
  have hf : IsIrreducibleMorphism f :=
    B.component_irreducible S.almostSplitSkeleton i
  letI : Simple (S.almostSplitSkeleton.obj (B.label i)) := by
    change Simple (S.fgObj (B.label i))
    exact (RightModule.fgModule_simple_iff_isSimpleModule _).2 hsimple
  letI : Mono f := CategoryTheory.mono_of_nonzero_from_simple
    (MagnitudeConjecture.CategoryTheory.isIrreducibleMorphism_ne_zero hf)
  letI : Injective (S.almostSplitSkeleton.obj (B.label i)) := by
    change Injective (S.fgObj (B.label i))
    exact hi
  apply hf.not_isSplitMono
  exact IsSplitMono.mk'
    { retraction := Injective.factorThru (𝟙 _) f
      id := Injective.comp_factorThru (𝟙 _) f }

/-- A simple projective has zero radical, hence its projective-boundary
right middle term has arity zero. -/
theorem rightMiddleArity_eq_zero_of_projective_simple
    (p : Fin S.n) (hp : Projective (S.fgObj p))
    (hsimple : IsSimpleModule Aᵐᵒᵖ (S.fgObj p)) :
    FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData p = 0 := by
  letI : IsSimpleModule Aᵐᵒᵖ (S.fgObj p) := hsimple
  have hJ : Module.jacobson Aᵐᵒᵖ (S.fgObj p) = ⊥ :=
    IsSimpleModule.jacobson_eq_bot Aᵐᵒᵖ (S.fgObj p)
  have hzero : IsZero (S.projectiveBoundaryRadical p) := by
    apply IsZero.of_full_of_faithful_of_isZero
      (forget₂ (RightModule.FinitelyGeneratedCategory A) (ModuleCat Aᵐᵒᵖ))
    rw [ModuleCat.isZero_iff_subsingleton]
    change Subsingleton (Module.jacobson Aᵐᵒᵖ (S.fgObj p))
    rw [hJ]
    infer_instance
  let d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (S.projectiveBoundaryRadical p) :=
    { n := 0
      summand := fun i ↦ Fin.elim0 i
      indecomposable := fun i ↦ Fin.elim0 i
      isoBiproduct :=
        MagnitudeConjecture.CategoryTheory.zeroIsoEmptyBiproduct _ hzero }
  exact FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
    S.finiteTauCategoryData.toFiniteRightTauCategoryData p d
      (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit p hp)
      (S.projectiveBoundaryRadicalInclusion_isRightMinimal p)

namespace PrimitiveProjectivePresentation

variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable (P : S.PrimitiveProjectivePresentation)

/-- After simultaneously rejecting the socles of all non-simple
projective-injective indecomposables, every nonprojective quotient mesh has
total middle arity bounded by any common bound on the ambient right and left
beta invariants. -/
theorem nonsimpleProjectiveInjectiveSocleFamily_rightMiddleArity_le
    {bound : ℕ}
    (hbeta : FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ bound)
    (hleft : S.leftBeta ≤ bound)
    [IsNoetherianRing
      (RightModule.idealQuotientAlgebra
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective))ᵐᵒᵖ]
    (j : Fin (S.idealQuotientFiniteIndecomposableSkeleton
      (P.primitiveProjectiveSocleFamilyIdeal
        S.nonsimpleProjectiveInjectiveLabels
        S.nonsimpleProjectiveInjectiveLabels_injective)).n)
    (hjNonprojective : ¬
      (idealQuotientFiniteTauCategoryData S
        (P.primitiveProjectiveSocleFamilyIdeal
          S.nonsimpleProjectiveInjectiveLabels
          S.nonsimpleProjectiveInjectiveLabels_injective)
        ).toFiniteRightTauCategoryData.IsProjective j) :
    FiniteTauMatrix.rightMiddleArity
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleFamilyIdeal
            S.nonsimpleProjectiveInjectiveLabels
            S.nonsimpleProjectiveInjectiveLabels_injective)
          ).toFiniteRightTauCategoryData j ≤ bound := by
  classical
  let T := S.nonsimpleProjectiveInjectiveLabels
  let hInjective := S.nonsimpleProjectiveInjectiveLabels_injective
  let hNotSimple := S.nonsimpleProjectiveInjectiveLabels_notSimple
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let q := S.idealQuotientFiniteLabelEquiv J
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let TQ := (idealQuotientFiniteTauCategoryData S J
    ).toFiniteRightTauCategoryData
  let x := q j
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra J)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ
  have hjOrdinary : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T),
      x.1 ≠ (P.socleQuotientReplacementLabel
        p (hInjective p hp) (hNotSimple p hp)).1 := by
    intro p hp heq
    let jr := P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
      T hInjective hNotSimple p hp
    have hqjr : q jr =
        P.primitiveProjectiveSocleFamilyReplacementLabel
          T hInjective hNotSimple p hp :=
      P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
        T hInjective hNotSimple p hp
    have hjr : j = jr := by
      apply q.injective
      apply Subtype.ext
      exact heq.trans (congrArg Subtype.val hqjr).symm
    apply hjNonprojective
    rw [hjr]
    rw [FiniteTauMatrix.isProjective_iff_projective_obj]
    exact P.primitiveProjectiveSocleFamilyFiniteReplacement_projective
      T hInjective hNotSimple p hp
  have hxNonprojective : ¬ TA.IsProjective x.1 := by
    intro hx
    apply hjNonprojective
    exact (P.primitiveProjectiveSocleFamily_isProjective_iff_ambient
      T hInjective hNotSimple j hjOrdinary).1 hx
  let z : {i : Fin S.n // ¬ Projective (S.fgObj i)} := ⟨x.1, by
    intro hxProjective
    apply hxNonprojective
    rw [FiniteTauMatrix.isProjective_iff_projective_obj]
    exact hxProjective⟩
  let B := S.minimalRightAlmostSplitAt z.1
  have hnoPI : ∀ i : B.index,
      Projective (S.fgObj (B.label i)) →
        ¬ Injective (S.fgObj (B.label i)) := by
    intro i hiProjective hiInjective
    let p : S.ProjectiveLabel := ⟨B.label i, hiProjective⟩
    have hpNotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label) :=
      S.rightMiddleLabel_not_simple_of_injective z.1 i hiInjective
    have hp : p ∈ T := by
      exact (S.mem_nonsimpleProjectiveInjectiveLabels_iff p).2
        ⟨hiInjective, hpNotSimple⟩
    exact P.minimalRightAlmostSplitAt_label_ne_familySelected_of_endpoint_ne
      T hInjective hNotSimple z.1 hjOrdinary i p hp rfl
  have hAmbientCard : Nat.card B.index ≤ bound :=
    S.rightMiddle_natCard_le_of_no_projectiveInjective
      hbeta hleft z hnoPI
  let dA := S.minimalRightAlmostSplitAtDecomposition z.1
  have hAmbientArity : FiniteTauMatrix.rightMiddleArity TA z.1 ≤ bound := by
    have hA :=
      FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
        TA z.1 dA B.rightAlmostSplit B.rightMinimal
    change FiniteTauMatrix.rightMiddleArity TA z.1 ≤ bound
    rw [hA]
    rw [Nat.card_eq_fintype_card] at hAmbientCard
    exact hAmbientCard
  have hArity := P.primitiveProjectiveSocleFamily_rightMiddleArity_eq_ambient
    T hInjective hNotSimple j hjOrdinary
  change FiniteTauMatrix.rightMiddleArity TQ j ≤ bound
  exact hArity.symm.le.trans hAmbientArity

/-- If the ambient beta invariant is at most two, then every right mesh of
the simultaneous quotient by all non-simple projective-injective socles has
total middle arity at most two, including the new projective replacement
vertices. -/
theorem nonsimpleProjectiveInjectiveSocleFamily_rightMiddleArity_le_two
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
        S.nonsimpleProjectiveInjectiveLabels_injective)).n) :
    FiniteTauMatrix.rightMiddleArity
        (idealQuotientFiniteTauCategoryData S
          (P.primitiveProjectiveSocleFamilyIdeal
            S.nonsimpleProjectiveInjectiveLabels
            S.nonsimpleProjectiveInjectiveLabels_injective)
          ).toFiniteRightTauCategoryData j ≤ 2 := by
  classical
  let T := S.nonsimpleProjectiveInjectiveLabels
  let hInjective := S.nonsimpleProjectiveInjectiveLabels_injective
  let hNotSimple := S.nonsimpleProjectiveInjectiveLabels_notSimple
  let J := P.primitiveProjectiveSocleFamilyIdeal T hInjective
  let q := S.idealQuotientFiniteLabelEquiv J
  let TA := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let TQ := (idealQuotientFiniteTauCategoryData S J
    ).toFiniteRightTauCategoryData
  let x := q j
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra J)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (RightModule.idealQuotientAlgebra J)ᵐᵒᵖ
  by_cases hjProjective : TQ.IsProjective j
  · by_cases hjReplacement : ∃ (p : S.ProjectiveLabel) (hp : p ∈ T),
        P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
          T hInjective hNotSimple p hp = j
    · obtain ⟨p, hp, rfl⟩ := hjReplacement
      let hpI := hInjective p hp
      let hpNS := hNotSimple p hp
      let z := P.socleQuotientReplacementNonprojectiveLabel p hpI hpNS
      let y := S.rightTranslationEquiv z
      let B := S.minimalRightAlmostSplitAt z.1
      obtain ⟨i, hiLabel⟩ : ∃ i : B.index,
          B.label i = p.label := by
        simpa only [B] using
          P.exists_projectiveInjectiveMiddleOccurrence_at_socleQuotient
            p hpI hpNS
      have hiProjective : Projective (S.fgObj (B.label i)) := by
        rw [hiLabel]
        exact p.projective
      have hcard : Nat.card B.index ≤ S.leftBetaAt y.1 + 1 := by
        have hy : (S.rightTranslationEquiv).symm y = z :=
          Equiv.symm_apply_apply S.rightTranslationEquiv z
        have hbound : ∀ i : (S.minimalRightAlmostSplitAt
              ((S.rightTranslationEquiv).symm y).1).index,
            Projective (S.fgObj ((S.minimalRightAlmostSplitAt
              ((S.rightTranslationEquiv).symm y).1).label i)) →
            Nat.card (S.minimalRightAlmostSplitAt
              ((S.rightTranslationEquiv).symm y).1).index ≤
                S.leftBetaAt y.1 + 1 := by
          intro t ht
          exact S.rightMiddle_natCard_le_leftBetaAt_add_one_of_projective
            y t ht
        rw [hy] at hbound
        exact hbound i hiProjective
      have hleft : S.leftBeta ≤ 2 :=
        S.leftBeta_le_two_of_beta_le_two hbeta
      have hleftAt : S.leftBetaAt y.1 ≤ 2 :=
        (S.leftBeta_le_iff 2).1 hleft y.1 y.2
      have hcardThree : Nat.card B.index ≤ 3 := by omega
      let dA := S.minimalRightAlmostSplitAtDecomposition z.1
      have hAmbientArity :
          FiniteTauMatrix.rightMiddleArity TA z.1 ≤ 3 := by
        have hA :=
          FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
            TA z.1 dA B.rightAlmostSplit B.rightMinimal
        rw [hA]
        rw [Nat.card_eq_fintype_card] at hcardThree
        exact hcardThree
      have hReplacement :=
        P.primitiveProjectiveSocleFamily_replacement_rightMiddleArity_add_one_eq_ambient
          T hInjective hNotSimple p hp
      have hq :
          (q (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
            T hInjective hNotSimple p hp)).1 = z.1 := by
        exact congrArg Subtype.val
          (P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
            T hInjective hNotSimple p hp)
      change FiniteTauMatrix.rightMiddleArity TQ
          (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
            T hInjective hNotSimple p hp) ≤ 2
      change FiniteTauMatrix.rightMiddleArity TQ
            (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
              T hInjective hNotSimple p hp) + 1 =
          FiniteTauMatrix.rightMiddleArity TA
            (q (P.primitiveProjectiveSocleFamilyFiniteReplacementLabel
              T hInjective hNotSimple p hp)).1 at hReplacement
      rw [hq] at hReplacement
      omega
    · have hjOrdinary : ∀ (p : S.ProjectiveLabel) (hp : p ∈ T),
          x.1 ≠ (P.socleQuotientReplacementLabel
            p (hInjective p hp) (hNotSimple p hp)).1 := by
        intro p hp heq
        apply hjReplacement
        refine ⟨p, hp, ?_⟩
        apply q.injective
        apply Subtype.ext
        rw [P.idealQuotientFiniteLabelEquiv_familyFiniteReplacementLabel
          T hInjective hNotSimple p hp]
        exact heq.symm
      have hxProjectiveTA : TA.IsProjective x.1 :=
        (P.primitiveProjectiveSocleFamily_isProjective_iff_ambient
          T hInjective hNotSimple j hjOrdinary).2 hjProjective
      have hxProjective : Projective (S.fgObj x.1) := by
        rw [FiniteTauMatrix.isProjective_iff_projective_obj] at hxProjectiveTA
        exact hxProjectiveTA
      have hAmbientArity :
          FiniteTauMatrix.rightMiddleArity TA x.1 ≤ 2 := by
        by_cases hxInjective : Injective (S.fgObj x.1)
        · have hxSimple : IsSimpleModule Aᵐᵒᵖ (S.fgObj x.1) := by
            by_contra hxNotSimple
            let p : S.ProjectiveLabel := ⟨x.1, hxProjective⟩
            have hp : p ∈ T :=
              (S.mem_nonsimpleProjectiveInjectiveLabels_iff p).2
                ⟨hxInjective, hxNotSimple⟩
            exact
              (P.fgObj_isAnnihilatedBy_primitiveProjectiveSocleFamilyIdeal_iff
                T hInjective x.1).1 x.2 p hp rfl
          have hxZero := S.rightMiddleArity_eq_zero_of_projective_simple
            x.1 hxProjective hxSimple
          change FiniteTauMatrix.rightMiddleArity TA x.1 = 0 at hxZero
          omega
        · exact (S.projective_rightMiddleArity_le_beta
            x.1 hxProjective hxInjective).trans hbeta
      have hArity :=
        P.primitiveProjectiveSocleFamily_rightMiddleArity_eq_ambient
          T hInjective hNotSimple j hjOrdinary
      change FiniteTauMatrix.rightMiddleArity TQ j ≤ 2
      exact hArity.symm.le.trans hAmbientArity
  · exact P.nonsimpleProjectiveInjectiveSocleFamily_rightMiddleArity_le
      hbeta (S.leftBeta_le_two_of_beta_le_two hbeta) j hjProjective

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
