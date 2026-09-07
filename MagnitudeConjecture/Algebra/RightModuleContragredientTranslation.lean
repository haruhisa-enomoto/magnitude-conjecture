import MagnitudeConjecture.Algebra.RightModuleContragredientSkeleton
import MagnitudeConjecture.Algebra.RightModuleLeftTau
import MagnitudeConjecture.CategoryTheory.AlmostSplitDuality

/-!
# Auslander--Reiten translation under contragredient duality

The label-aligned contragredient skeleton turns a noninjective right
`A`-module into a nonprojective right `Aᵐᵒᵖ`-module at the same label.
Uniqueness of minimal left almost-split maps then identifies target
Auslander--Reiten translation with inverse source translation, which is the
translation identity used by the manuscript's negative new-mesh construction.
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

/-- A noninjective original label, dualized at the same finite coordinate, is
nonprojective in the contragredient skeleton. -/
def contragredientNonprojectiveLabel
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)}) :
    {i : Fin S.contragredientSkeleton.n //
      ¬ Projective (S.contragredientSkeleton.fgObj i)} := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  refine ⟨x.1, ?_⟩
  intro hp
  apply x.2
  exact
    (S.contragredientAlignedBiduality.forward
      |>.injective_iff_projective_image
        S.almostSplitSkeleton S.contragredientAlmostSplitSkeleton x.1).2 hp

/-- Target Auslander--Reiten translation with the automatically derived
Noetherian instance for the opposite-opposite algebra kept internal. -/
def contragredientRightTranslationLabel
    (q : {i : Fin S.contragredientSkeleton.n //
      ¬ Projective (S.contragredientSkeleton.fgObj i)}) :
    Fin S.contragredientSkeleton.n := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact S.contragredientSkeleton.rightTranslationLabel q

/-- Under the label-aligned contragredient skeleton, target
Auslander--Reiten translation is inverse source translation:
`τ_(Aᵐᵒᵖ)(D X) = D(τ_A⁻¹ X)` at the level of selected labels. -/
theorem contragredient_rightTranslationLabel_eq_inverse
    (x : {i : Fin S.n // ¬ Injective (S.fgObj i)}) :
    S.contragredientRightTranslationLabel
        (S.contragredientNonprojectiveLabel x) =
      ((S.rightTranslationEquiv).symm x).1 := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Sop := S.contragredientSkeleton
  let B := S.contragredientAlignedBiduality
  let q := S.contragredientNonprojectiveLabel x
  let AopAR := Sop.minimalRightAlmostSplitAt q.1
  let g : S.fgObj x.1 ⟶
      B.backward.categoryEquiv.functor.obj
        (Opposite.op AopAR.middle) :=
    (B.backward.objIso q.1).inv ≫
      B.backward.categoryEquiv.functor.map AopAR.map.op
  have hgAS : IsLeftAlmostSplit g :=
    (AopAR.rightAlmostSplit.map_op_equivalence
      B.backward.categoryEquiv).precomp_iso
        (B.backward.objIso q.1).symm
  have hgMin : IsLeftMinimal g :=
    (AopAR.rightMinimal.map_op_equivalence
      B.backward.categoryEquiv).precomp_iso
        (B.backward.objIso q.1).symm
  let z := (S.rightTranslationEquiv).symm x
  let AAR := S.minimalRightAlmostSplitAt z.1
  let f : S.fgObj x.1 ⟶ AAR.middle :=
    (S.noninjectiveLeftSourceIso x).hom ≫ S.rightKernelMap z
  have hfAS : IsLeftAlmostSplit f :=
    (S.rightKernelMap_leftAlmostSplit z).precomp_iso
      (S.noninjectiveLeftSourceIso x)
  have hfMin : IsLeftMinimal f :=
    (S.rightKernelMap_leftMinimal z).precomp_iso
      (S.noninjectiveLeftSourceIso x)
  let ec : cokernel g ≅ cokernel f :=
    Classical.choice
      (nonempty_cokernelIso_of_leftAlmostSplit
        hgAS hgMin hfAS hfMin)
  let eg : cokernel g ≅
      S.fgObj (Sop.rightTranslationLabel q) :=
    (cokernelPrecompMapOpIsoKernel
      B.backward.categoryEquiv AopAR.map
        (B.backward.objIso q.1).symm).trans
      ((B.backward.categoryEquiv.functor.mapIso
        (Sop.rightTranslationKernelIso q).symm.op).trans
          (B.backward.objIso (Sop.rightTranslationLabel q)))
  haveI : Epi AAR.map :=
    IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      S.almostSplitSkeleton AAR.map AAR.rightAlmostSplit z.2
  let eSource : S.fgObj x.1 ≅ kernel AAR.map :=
    (S.noninjectiveLeftSourceIso x).trans
      (S.rightTranslationKernelIso z).symm
  let ef : cokernel f ≅ S.fgObj z.1 :=
    (cokernel.mapIso f (kernel.ι AAR.map) eSource (Iso.refl _)
      (by simp [f, eSource, rightKernelMap, AAR])).trans
        (cokernelKernelIsoTarget AAR.map)
  exact S.fgObj_skeletal ⟨eg.symm.trans (ec.trans ef)⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
