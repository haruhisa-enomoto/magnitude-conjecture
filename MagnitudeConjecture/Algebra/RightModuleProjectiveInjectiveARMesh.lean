import MagnitudeConjecture.Algebra.RightModuleDirectedCartan
import MagnitudeConjecture.Algebra.RightModuleProjectiveInjectiveARBoundary
import MagnitudeConjecture.CategoryTheory.AlgebraicallyClosedOccurrenceBasis

/-!
# The exceptional Auslander--Reiten mesh under socle rejection

Let `P` be a non-simple indecomposable projective-injective right module and
let `Q = P / soc(P)`.  This file identifies the ambient Auslander--Reiten
sequence ending at `Q`: the endpoint `Q` is nonprojective and its
Auslander--Reiten translate is `rad(P)`.  Thus the canonical kernel of the
chosen right almost-split map ending at `Q` is isomorphic to the literal
radical boundary object.
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

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

include P in
/-- Although `P / soc(P)` becomes projective after socle rejection, it is
not projective as an ambient `A`-module. -/
theorem socleQuotientReplacementLabel_not_projective
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    ¬ Projective
      (S.fgObj
        (P.socleQuotientReplacementLabel
          p hpInjective hnotSimple).1) := by
  intro hprojective
  let Q := P.primitiveProjectiveSocleQuotientFGObj p
  let q := P.primitiveProjectiveSocleQuotientProjection p
  let eQ := P.primitiveProjectiveSocleQuotientAmbientIso
    p hpInjective hnotSimple
  have hQindecomposable : Indecomposable Q :=
    (fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) Q).1
        (P.primitiveProjectiveSocleQuotient_isIndecomposableModule
          p hnotSimple)
  letI : Projective Q := Projective.of_iso eQ.symm hprojective
  letI : Epi q :=
    P.primitiveProjectiveSocleQuotientProjection_epi p
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 Q) q
  letI : IsSplitEpi q := IsSplitEpi.mk'
    { section_ := s
      id := hs }
  letI : IsIso q :=
    MagnitudeConjecture.CategoryTheory.isIso_of_isSplitEpi_from_indecomposable
      (RightModule.rightIdealFGObj_indecomposable (P.primitive p))
      q hQindecomposable.1
  exact (P.primitiveProjectiveSocleQuotientProjection_isLeftAlmostSplit
    p hpInjective).not_isSplitMono inferInstance

/-- The replacement label bundled with its ambient nonprojectivity. -/
def socleQuotientReplacementNonprojectiveLabel
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    {x : Fin S.n // ¬ Projective (S.fgObj x)} :=
  ⟨(P.socleQuotientReplacementLabel p hpInjective hnotSimple).1,
    P.socleQuotientReplacementLabel_not_projective
      p hpInjective hnotSimple⟩

include P in
/-- The selected projective-injective occurs in the middle term of the
ambient right almost-split sequence ending at `P / soc(P)`. -/
theorem exists_projectiveInjectiveMiddleOccurrence_at_socleQuotient
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    ∃ t : (S.minimalRightAlmostSplitAt
        (P.socleQuotientReplacementNonprojectiveLabel
          p hpInjective hnotSimple).1).index,
      (S.minimalRightAlmostSplitAt
        (P.socleQuotientReplacementNonprojectiveLabel
          p hpInjective hnotSimple).1).label t = p.label := by
  let z := P.socleQuotientReplacementNonprojectiveLabel
    p hpInjective hnotSimple
  let B := S.minimalRightAlmostSplitAt z.1
  have hPQ : HasIrreducibleMorphism
      (S.fgObj p.label) (S.fgObj z.1) :=
    (P.hasIrreducibleMorphism_from_projectiveInjective_iff
      p hpInjective hnotSimple z.1).2 rfl
  exact (B.summandIrreducibleCorrespondence p.label).2 hPQ

include P in
/-- Over an algebraically closed field, the selected projective-injective
occurs exactly once in the ambient right almost-split middle term ending at
`P / soc(P)`.  This is the single incoming boundary arrow removed from that
mesh by socle rejection. -/
theorem card_projectiveInjectiveMiddleOccurrence_at_socleQuotient_eq_one
    [IsAlgClosed k]
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    Nat.card
        (S.almostSplitSkeleton.RightAROccurrence
          (S.minimalRightAlmostSplitAt
            (P.socleQuotientReplacementNonprojectiveLabel
              p hpInjective hnotSimple).1)
          p.label) = 1 := by
  classical
  let z := P.socleQuotientReplacementNonprojectiveLabel
    p hpInjective hnotSimple
  let B := S.minimalRightAlmostSplitAt z.1
  let L := S.minimalLeftAlmostSplitAt p.label
  let q := (P.socleQuotientReplacementLabel
    p hpInjective hnotSimple).1
  have hright :=
    S.almostSplitSkeleton
      |>.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
        (K := k) B p.label
  have hleft :=
    S.almostSplitSkeleton
      |>.finrank_irreducibleHomSpace_eq_card_leftAROccurrence_of_isAlgClosed
        (K := k) L q
  have hlabels : ∀ t : L.index, L.label t = q :=
    fun t ↦ P.projectiveInjectiveLeftMiddle_label_eq_replacement
      p hpInjective hnotSimple t
  let e : L.index ≃ S.almostSplitSkeleton.LeftAROccurrence L q :=
    { toFun := fun t ↦ ⟨t, hlabels t⟩
      invFun := fun t ↦ t.1
      left_inv := fun _ ↦ rfl
      right_inv := fun t ↦ Subtype.ext rfl }
  calc
    Nat.card (S.almostSplitSkeleton.RightAROccurrence B p.label) =
        Module.finrank k
          (S.almostSplitSkeleton.irreducibleHomSpace
            (K := k) p.label q) := hright.symm
    _ = Nat.card
        (S.almostSplitSkeleton.LeftAROccurrence L q) := hleft
    _ = Nat.card L.index := Nat.card_congr e.symm
    _ = Fintype.card L.index := Nat.card_eq_fintype_card
    _ = 1 := P.projectiveInjectiveLeftMiddle_card_eq_one
      p hpInjective hnotSimple

include P in
/-- The ambient Auslander--Reiten translate of `P / soc(P)` is the chosen
skeletal representative of `rad(P)`. -/
theorem rightTranslationLabel_socleQuotientReplacement
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    S.rightTranslationLabel
        (P.socleQuotientReplacementNonprojectiveLabel
          p hpInjective hnotSimple) =
      projectiveInjectiveBoundaryRadicalLabel
        p hpInjective hnotSimple := by
  let z := P.socleQuotientReplacementNonprojectiveLabel
    p hpInjective hnotSimple
  let B := S.minimalRightAlmostSplitAt z.1
  let L := S.rightSequenceLeftDecomposition z
  obtain ⟨t, ht⟩ :=
    P.exists_projectiveInjectiveMiddleOccurrence_at_socleQuotient
      p hpInjective hnotSimple
  have hTauP : HasIrreducibleMorphism
      (S.fgObj (S.rightTranslationLabel z)) (S.fgObj p.label) :=
    (L.summandIrreducibleCorrespondence p.label).1 ⟨t, ht⟩
  exact (hasIrreducibleMorphism_to_projectiveInjective_iff
    (S := S) p hpInjective hnotSimple
      (S.rightTranslationLabel z)).1 hTauP

/-- The kernel of the chosen ambient right almost-split map ending at
`P / soc(P)` is the literal radical `rad(P)`. -/
def socleQuotientReplacementKernelIso
    (p : S.ProjectiveLabel)
    (hpInjective : Injective (S.fgObj p.label))
    (hnotSimple : ¬ IsSimpleModule Aᵐᵒᵖ (S.fgObj p.label)) :
    kernel
        (S.minimalRightAlmostSplitAt
          (P.socleQuotientReplacementNonprojectiveLabel
            p hpInjective hnotSimple).1).map ≅
      S.projectiveBoundaryRadical p.label :=
  (S.rightTranslationKernelIso
      (P.socleQuotientReplacementNonprojectiveLabel
        p hpInjective hnotSimple)).trans <|
    (eqToIso (congrArg S.fgObj
      (P.rightTranslationLabel_socleQuotientReplacement
        p hpInjective hnotSimple))).trans <|
      (projectiveInjectiveBoundaryRadicalIso
        p hpInjective hnotSimple).symm

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
