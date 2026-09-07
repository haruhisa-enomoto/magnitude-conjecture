import MagnitudeConjecture.Algebra.RightModuleProjectiveBoundary
import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveSocleQuotient
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecompositionUniqueness

/-!
# The Auslander--Reiten boundary at a projective-injective module

Let `P` be a non-simple indecomposable projective-injective right module.
The two canonical boundary maps

* `rad(P) ⟶ P`, and
* `P ⟶ P / soc(P)`

are respectively minimal right and minimal left almost split.  Their middle
objects are indecomposable.  Consequently each chosen almost-split
decomposition incident with `P` has exactly one summand.  This is the
categorical form of the two-arrow boundary used in projective-injective
socle rejection.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

/-- The radical of a non-simple indecomposable projective-injective has a
simple socle, hence is indecomposable. -/
theorem projectiveInjectiveBoundaryRadical_isIndecomposableModule
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Foundation.IsIndecomposableModule Aᵐᵒᵖ
      (S.projectiveBoundaryRadical p.label) := by
  letI : Injective (S.fgObj p.label) := hpInjective
  change Foundation.IsIndecomposableModule Aᵐᵒᵖ
    (Module.jacobson Aᵐᵒᵖ (S.fgObj p.label))
  exact jacobson_isIndecomposableModule_of_injective
    (k := k) (S.fgObj p.label) (S.fgObj_indecomposable p.label)
      (S.projectiveSimpleTop_isSimpleModule p) hnotSimple

/-- The radical boundary object is categorically indecomposable. -/
theorem projectiveInjectiveBoundaryRadical_indecomposable
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Indecomposable (S.projectiveBoundaryRadical p.label) :=
  (fgModule_isIndecomposableModule_iff_indecomposable
    (k := k) (A := A) (S.projectiveBoundaryRadical p.label)).1
      (projectiveInjectiveBoundaryRadical_isIndecomposableModule
        p hpInjective hnotSimple)

/-- A skeletal label for the indecomposable radical of the selected
projective-injective. -/
def projectiveInjectiveBoundaryRadicalLabel
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Fin S.n :=
  Classical.choose <| S.fgObj_complete
    (S.projectiveBoundaryRadical p.label)
    (projectiveInjectiveBoundaryRadical_indecomposable
      p hpInjective hnotSimple)

/-- The radical boundary object is isomorphic to its chosen skeletal
representative. -/
def projectiveInjectiveBoundaryRadicalIso
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    S.projectiveBoundaryRadical p.label ≅
      S.fgObj (projectiveInjectiveBoundaryRadicalLabel
        p hpInjective hnotSimple) :=
  Classical.choice <| Classical.choose_spec <| S.fgObj_complete
    (S.projectiveBoundaryRadical p.label)
    (projectiveInjectiveBoundaryRadical_indecomposable
      p hpInjective hnotSimple)

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- Viewed again as an ambient `A`-module, the literal socle quotient is
isomorphic to the ambient representative underlying its intrinsic quotient
label. -/
def primitiveProjectiveSocleQuotientAmbientIso
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    P.primitiveProjectiveSocleQuotientFGObj p ≅
      S.fgObj
        (P.socleQuotientReplacementLabel p hpInjective hnotSimple).1 := by
  let I := P.primitiveProjectiveSocleIdeal p hpInjective
  let E := RightModule.idealQuotientEquivalence (k := k) I
  let U := (RightModule.IdealQuotientProperty I).ι
  exact U.mapIso <| E.functor.preimageIso <|
    P.primitiveProjectiveSocleQuotientReplacementIso
      p hpInjective hnotSimple

/-- The chosen minimal left almost-split middle term out of `P` is the
literal quotient `P / soc(P)`. -/
def projectiveInjectiveLeftMiddleIso
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label)) :
    (S.minimalLeftAlmostSplitAt p.label).middle ≅
      P.primitiveProjectiveSocleQuotientFGObj p := by
  let B := S.minimalLeftAlmostSplitAt p.label
  let q := P.primitiveProjectiveSocleQuotientProjection p
  let qSkeletal : S.fgObj p.label ⟶
      P.primitiveProjectiveSocleQuotientFGObj p :=
    (P.primitiveProjectiveIso p).inv ≫ q
  have hqAS : IsLeftAlmostSplit qSkeletal :=
    (P.primitiveProjectiveSocleQuotientProjection_isLeftAlmostSplit
      p hpInjective).precomp_iso (P.primitiveProjectiveIso p).symm
  have hqMin : IsLeftMinimal qSkeletal :=
    (P.primitiveProjectiveSocleQuotientProjection_isLeftMinimal p).precomp_iso
      (P.primitiveProjectiveIso p).symm
  exact Classical.choose <| exists_leftAlmostSplit_middleIso
    B.leftAlmostSplit B.leftMinimal hqAS hqMin

/-- The chosen minimal right almost-split middle term ending at `P` is
`rad(P)`. -/
def projectiveInjectiveRightMiddleIso
    (p : S.ProjectiveLabel) :
    (S.minimalRightAlmostSplitAt p.label).middle ≅
      S.projectiveBoundaryRadical p.label := by
  let B := S.minimalRightAlmostSplitAt p.label
  exact Classical.choose <| exists_rightAlmostSplit_middleIso
    B.rightAlmostSplit B.rightMinimal
      (S.projectiveBoundaryRadicalInclusion_isRightAlmostSplit
        p.label p.projective)
      (S.projectiveBoundaryRadicalInclusion_isRightMinimal p.label)

/-- The displayed decomposition of the chosen left almost-split middle
term, reindexed by a finite ordinal. -/
def projectiveInjectiveLeftMiddleDecomposition
    (p : S.ProjectiveLabel) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (S.minimalLeftAlmostSplitAt p.label).middle := by
  classical
  let B := S.minimalLeftAlmostSplitAt p.label
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

/-- The displayed decomposition of the chosen right almost-split middle
term, reindexed by a finite ordinal. -/
def projectiveInjectiveRightMiddleDecomposition
    (p : S.ProjectiveLabel) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (S.minimalRightAlmostSplitAt p.label).middle := by
  classical
  let B := S.minimalRightAlmostSplitAt p.label
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

include P in
/-- Exactly one indecomposable summand occurs in the chosen minimal left
almost-split middle term out of `P`. -/
theorem projectiveInjectiveLeftMiddle_card_eq_one
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Fintype.card (S.minimalLeftAlmostSplitAt p.label).index = 1 := by
  let dB := projectiveInjectiveLeftMiddleDecomposition (S := S) p
  let Q := P.primitiveProjectiveSocleQuotientFGObj p
  have hQ : Indecomposable Q :=
    (fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) Q).1
        (P.primitiveProjectiveSocleQuotient_isIndecomposableModule
          p hnotSimple)
  let dQ := MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
    Q hQ
  have hn :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.n_eq_of_iso
      dB dQ (fun i ↦ S.fgObj_end_isLocalRing _) <|
        P.projectiveInjectiveLeftMiddleIso p hpInjective
  exact hn

/-- Exactly one indecomposable summand occurs in the chosen minimal right
almost-split middle term ending at `P`. -/
theorem projectiveInjectiveRightMiddle_card_eq_one
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Fintype.card (S.minimalRightAlmostSplitAt p.label).index = 1 := by
  let dB := projectiveInjectiveRightMiddleDecomposition (S := S) p
  let R := S.projectiveBoundaryRadical p.label
  have hR : Indecomposable R :=
    projectiveInjectiveBoundaryRadical_indecomposable
      p hpInjective hnotSimple
  let dR := MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
    R hR
  have hn :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.n_eq_of_iso
      dB dR (fun i ↦ S.fgObj_end_isLocalRing _) <|
        projectiveInjectiveRightMiddleIso (S := S) p
  exact hn

include P in
/-- Every summand of the chosen left almost-split middle term out of `P`
has the ambient label of `P / soc(P)`. -/
theorem projectiveInjectiveLeftMiddle_label_eq_replacement
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (t : (S.minimalLeftAlmostSplitAt p.label).index) :
    (S.minimalLeftAlmostSplitAt p.label).label t =
      (P.socleQuotientReplacementLabel
        p hpInjective hnotSimple).1 := by
  let B := S.minimalLeftAlmostSplitAt p.label
  have hcard := P.projectiveInjectiveLeftMiddle_card_eq_one
    p hpInjective hnotSimple
  obtain ⟨t₀, ht₀⟩ := Fintype.card_eq_one_iff.mp hcard
  letI : Unique B.index := { default := t₀, uniq := ht₀ }
  have ht : t = (default : B.index) := Subsingleton.elim _ _
  subst t
  let eB : B.middle ≅ S.fgObj (B.label (default : B.index)) :=
    B.decomposition.trans <|
      biproductUniqueIso (fun i : B.index ↦ S.fgObj (B.label i))
  let eQ : B.middle ≅
      S.fgObj
        (P.socleQuotientReplacementLabel
          p hpInjective hnotSimple).1 :=
    (P.projectiveInjectiveLeftMiddleIso p hpInjective).trans
      (P.primitiveProjectiveSocleQuotientAmbientIso
        p hpInjective hnotSimple)
  exact S.fgObj_skeletal ⟨eB.symm.trans eQ⟩

/-- Every summand of the chosen right almost-split middle term ending at
`P` has the ambient label of `rad(P)`. -/
theorem projectiveInjectiveRightMiddle_label_eq_radical
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (t : (S.minimalRightAlmostSplitAt p.label).index) :
    (S.minimalRightAlmostSplitAt p.label).label t =
      projectiveInjectiveBoundaryRadicalLabel
        p hpInjective hnotSimple := by
  let B := S.minimalRightAlmostSplitAt p.label
  have hcard := projectiveInjectiveRightMiddle_card_eq_one
    (S := S) p hpInjective hnotSimple
  obtain ⟨t₀, ht₀⟩ := Fintype.card_eq_one_iff.mp hcard
  letI : Unique B.index := { default := t₀, uniq := ht₀ }
  have ht : t = (default : B.index) := Subsingleton.elim _ _
  subst t
  let eB : B.middle ≅ S.fgObj (B.label (default : B.index)) :=
    B.decomposition.trans <|
      biproductUniqueIso (fun i : B.index ↦ S.fgObj (B.label i))
  let eR : B.middle ≅
      S.fgObj (projectiveInjectiveBoundaryRadicalLabel
        p hpInjective hnotSimple) :=
    (projectiveInjectiveRightMiddleIso (S := S) p).trans
      (projectiveInjectiveBoundaryRadicalIso
        p hpInjective hnotSimple)
  exact S.fgObj_skeletal ⟨eB.symm.trans eR⟩

include P in
/-- The only ambient indecomposable target of an irreducible map out of
the selected projective-injective is its socle-quotient replacement. -/
theorem hasIrreducibleMorphism_from_projectiveInjective_iff
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : Fin S.n) :
    HasIrreducibleMorphism (S.fgObj p.label) (S.fgObj x) ↔
      x = (P.socleQuotientReplacementLabel
        p hpInjective hnotSimple).1 := by
  let B := S.minimalLeftAlmostSplitAt p.label
  constructor
  · intro hx
    obtain ⟨t, ht⟩ :=
      (B.summandIrreducibleCorrespondence x).2 hx
    exact ht.symm.trans <|
      P.projectiveInjectiveLeftMiddle_label_eq_replacement
        p hpInjective hnotSimple t
  · intro hx
    subst x
    have hcard := P.projectiveInjectiveLeftMiddle_card_eq_one
      p hpInjective hnotSimple
    obtain ⟨t₀, ht₀⟩ := Fintype.card_eq_one_iff.mp hcard
    letI : Unique B.index := { default := t₀, uniq := ht₀ }
    apply (B.summandIrreducibleCorrespondence _).1
    exact ⟨default,
      P.projectiveInjectiveLeftMiddle_label_eq_replacement
        p hpInjective hnotSimple default⟩

/-- The only ambient indecomposable source of an irreducible map into the
selected projective-injective is its radical. -/
theorem hasIrreducibleMorphism_to_projectiveInjective_iff
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label))
    (x : Fin S.n) :
    HasIrreducibleMorphism (S.fgObj x) (S.fgObj p.label) ↔
      x = projectiveInjectiveBoundaryRadicalLabel
        p hpInjective hnotSimple := by
  let B := S.minimalRightAlmostSplitAt p.label
  constructor
  · intro hx
    obtain ⟨t, ht⟩ :=
      (B.summandIrreducibleCorrespondence x).2 hx
    exact ht.symm.trans <|
      projectiveInjectiveRightMiddle_label_eq_radical
        (S := S) p hpInjective hnotSimple t
  · intro hx
    subst x
    have hcard := projectiveInjectiveRightMiddle_card_eq_one
      (S := S) p hpInjective hnotSimple
    obtain ⟨t₀, ht₀⟩ := Fintype.card_eq_one_iff.mp hcard
    letI : Unique B.index := { default := t₀, uniq := ht₀ }
    apply (B.summandIrreducibleCorrespondence _).1
    exact ⟨default,
      projectiveInjectiveRightMiddle_label_eq_radical
        (S := S) p hpInjective hnotSimple default⟩

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
