import MagnitudeConjecture.Algebra.RightModuleContragredientTranslation
import MagnitudeConjecture.Algebra.RightModulePrimitiveRelativeMesh
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Primitive quotient and new meshes under contragredient duality

Contragredient duality restricts to an anti-equivalence between the literal
primitive-quotient subcategories on `A` and `Aᵐᵒᵖ`.  It therefore converts
the noninjective source of a primitive new mesh into a nonprojective opposite
endpoint.  Together with translation reversal, this constructs the dual new
mesh used in the manuscript's negative case.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The inverse image of opposite primitive annihilation under
contragredient duality is original primitive annihilation. -/
theorem primitiveQuotientProperty_inverseImage_contragredient
    (e : A) :
    (PrimitiveQuotientProperty (MulOpposite.op e)).inverseImage
        (Contragredient.dualityEquivalence k Aᵐᵒᵖ).functor =
      (PrimitiveQuotientProperty e).op := by
  ext M
  exact
    MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.isAnnihilatedBy_primitiveIdeal_contragredient_iff
      (k := k) e M.unop

/-- Contragredient duality restricted to the literal primitive-quotient
subcategories. -/
def primitiveQuotientContragredientEquivalence (e : A) :
    (PrimitiveQuotientSubcategory e)ᵒᵖ ≌
      PrimitiveQuotientSubcategory (MulOpposite.op e) :=
  (ObjectProperty.opEquivalence (PrimitiveQuotientProperty e)).symm |>.trans
    ((Contragredient.dualityEquivalence k Aᵐᵒᵖ).congrFullSubcategory
      (primitiveQuotientProperty_inverseImage_contragredient
        (k := k) e))

namespace FiniteIndecomposableSkeleton

variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : PrimitiveIdempotentData e)

/-- Primitive-quotient labels are literally preserved by the label-aligned
contragredient skeleton.  The equivalence changes only the proof that the
common finite coordinate survives primitive deletion. -/
def contragredientPrimitiveQuotientLabelEquiv :
    S.PrimitiveQuotientLabel D ≃
      S.contragredientSkeleton.PrimitiveQuotientLabel D.opposite where
  toFun x :=
    ⟨x.1, (S.mem_contragredient_primitiveKilledLabels_iff D x.1).2 x.2⟩
  invFun x :=
    ⟨x.1, (S.mem_contragredient_primitiveKilledLabels_iff D x.1).1 x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- A quotient label in the original skeleton, dualized at the same finite
coordinate and bundled in the opposite primitive-quotient subcategory. -/
def contragredientPrimitiveQuotientLabelObj
    (x : S.PrimitiveQuotientLabel D) :
    PrimitiveQuotientSubcategory (MulOpposite.op e) := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact S.contragredientSkeleton.primitiveQuotientLabelObj D.opposite
    ⟨x.1, (S.mem_contragredient_primitiveKilledLabels_iff D x.1).2 x.2⟩

/-- The restricted contragredient equivalence sends a quotient label object
to the same label in the opposite quotient skeleton. -/
def contragredientPrimitiveQuotientLabelObjIso
    (x : S.PrimitiveQuotientLabel D) :
    (primitiveQuotientContragredientEquivalence (k := k) e).functor.obj
        (Opposite.op (S.primitiveQuotientLabelObj D x)) ≅
      S.contragredientPrimitiveQuotientLabelObj D x :=
  ObjectProperty.isoMk _ (S.contragredientSkeleton_fgObjIso x.1).symm

namespace PrimitiveNewRightMeshEndpoint

variable {S D}

/-- The source of a primitive new mesh is noninjective in the literal
primitive-quotient subcategory, not only in the ambient category. -/
theorem sourceLabel_not_injective_primitiveQuotient [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ¬ Injective
      (S.primitiveQuotientLabelObj D (N.sourceLabel H he)) := by
  let T := N.quotientShortComplex
  have hT : T.ShortExact := N.quotientShortComplex_shortExact
  letI : Mono T.f := hT.mono_f
  have hnot : ¬ Injective T.X₁ :=
    (N.quotientShortComplex_f_minimalLeftAlmostSplit H he).1
      |>.not_injective_source T.f
  let eSource : T.X₁ ≅
      S.primitiveQuotientLabelObj D (N.sourceLabel H he) :=
    ObjectProperty.isoMk _ (N.sourceIso H he)
  intro hInjective
  apply hnot
  exact Injective.of_iso eSource.symm hInjective

/-- The dual of a new-mesh source is nonprojective in the literal opposite
primitive quotient. -/
theorem contragredient_sourceLabel_quotient_nonprojective
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ¬ Projective
      (S.contragredientPrimitiveQuotientLabelObj D
        (N.sourceLabel H he)) := by
  let E := primitiveQuotientContragredientEquivalence (k := k) e
  let X := S.primitiveQuotientLabelObj D (N.sourceLabel H he)
  let Y := S.contragredientPrimitiveQuotientLabelObj D
    (N.sourceLabel H he)
  let i : E.functor.obj (Opposite.op X) ≅ Y :=
    S.contragredientPrimitiveQuotientLabelObjIso D
      (N.sourceLabel H he)
  intro hY
  have hmap : Projective (E.functor.obj (Opposite.op X)) :=
    Projective.of_iso i.symm hY
  have hop : Projective (Opposite.op X) :=
    (E.map_projective_iff (Opposite.op X)).1 hmap
  have hX : Injective X :=
    Injective.injective_iff_projective_op.mpr hop
  exact N.sourceLabel_not_injective_primitiveQuotient H he hX

/-- Dualizing a primitive new mesh produces the opposite primitive new-mesh
endpoint labelled by the original source. -/
def contragredientNewMeshEndpoint [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    @PrimitiveNewRightMeshEndpoint k Aᵐᵒᵖ
      inferInstance inferInstance inferInstance inferInstance
      (IsNoetherianRing.of_finite k _)
      S.contragredientSkeleton (MulOpposite.op e) D.opposite := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let x := N.sourceNoninjectiveLabel H he
  let q := S.contragredientNonprojectiveLabel x
  let label : S.contragredientSkeleton.PrimitiveQuotientLabel D.opposite :=
    ⟨x.1, (S.mem_contragredient_primitiveKilledLabels_iff D x.1).2
      (N.sourceAmbientLabel_mem H he)⟩
  refine
    { label := label
      ambient_nonprojective := q.2
      quotient_nonprojective := ?_
      translation_not_mem := ?_ }
  · change ¬ Projective
      (S.contragredientPrimitiveQuotientLabelObj D
        (N.sourceLabel H he))
    exact N.contragredient_sourceLabel_quotient_nonprojective H he
  · let qTarget : {i : Fin S.contragredientSkeleton.n //
        ¬ Projective (S.contragredientSkeleton.fgObj i)} :=
      ⟨label.1, q.2⟩
    change S.contragredientSkeleton.rightTranslationLabel qTarget ∉
      S.contragredientSkeleton.primitiveKilledLabels D.opposite
    have hq : qTarget = q := Subtype.ext (by rfl)
    have htranslation :
        S.contragredientSkeleton.rightTranslationLabel q =
          ((S.rightTranslationEquiv).symm x).1 := by
      change S.contragredientRightTranslationLabel q = _
      exact S.contragredient_rightTranslationLabel_eq_inverse x
    intro hmem
    rw [hq, htranslation] at hmem
    exact N.leftMarkerAmbientLabel_not_mem H he
      ((S.mem_contragredient_primitiveKilledLabels_iff D _).1 hmem)

end PrimitiveNewRightMeshEndpoint

end FiniteIndecomposableSkeleton

end MagnitudeConjecture.RightModule
