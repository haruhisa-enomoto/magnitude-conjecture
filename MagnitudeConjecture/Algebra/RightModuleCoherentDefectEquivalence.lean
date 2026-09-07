import MagnitudeConjecture.Algebra.RightModuleCoherentDefectFreyd

/-!
# The exact-defect anti-equivalence on a fixed short exact presentation

This file identifies the abstract Freyd-category anti-equivalence with the
two defects attached to the same short exact module sequence.  It is the
object-level bridge needed to transport uniseriality in
Auslander--Reiten Proposition 1.3.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

private abbrev ModuleEpiFreyd :=
  CategoryTheory.Preadditive.RightFreyd.EpiCategory
    (RightModule.FinitelyGeneratedCategory A)

private abbrev OppositeModuleEpiFreyd :=
  CategoryTheory.Preadditive.RightFreyd.EpiCategory
    (RightModule.FinitelyGeneratedCategory A)ᵒᵖ

/-- The contravariant defect as an object of the exact-defect
subcategory. -/
def contravariantDefectObject
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) : S.FiniteContravariantDefectCategory :=
  ⟨S.finiteContravariantDefect K, ⟨K, hK, ⟨Iso.refl _⟩⟩⟩

/-- The covariant defect as an object of the exact-defect subcategory. -/
def covariantDefectObject
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) : S.FiniteCovariantDefectCategory :=
  ⟨S.finiteCovariantDefect K, ⟨K, hK, ⟨Iso.refl _⟩⟩⟩

/-- The epimorphic Freyd presentation `B ⟶ C` of a short exact
sequence. -/
def contravariantEpiPresentation
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) : ModuleEpiFreyd (A := A) :=
  ⟨(CategoryTheory.Preadditive.RightFreyd.quotient _).obj
      (Arrow.mk K.g), hK.epi_g⟩

/-- The epimorphic opposite-Freyd presentation `Bᵒᵖ ⟶ Aᵒᵖ`. -/
def covariantEpiPresentation
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) : OppositeModuleEpiFreyd (A := A) := by
  letI : Mono K.f := hK.mono_f
  exact ⟨(CategoryTheory.Preadditive.RightFreyd.quotient _).obj
    (Arrow.mk K.f.op), (inferInstance : Epi K.f.op)⟩

/-- The contravariant Freyd realization of the displayed epimorphism is
the displayed contravariant defect. -/
def contravariantEpiPresentationRealizationIso
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) :
    S.contravariantEpiFreydRealization.obj
        (contravariantEpiPresentation K hK) ≅
      S.contravariantDefectObject K hK :=
  Iso.refl _

/-- The opposite-Freyd realization of the displayed monomorphism is the
displayed covariant defect. -/
def covariantEpiPresentationRealizationIso
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) :
    S.covariantEpiFreydRealization.obj
        (covariantEpiPresentation K hK) ≅
      S.covariantDefectObject K hK :=
  Iso.refl _

/-- Kernel reversal sends the epimorphic presentation `B ⟶ C` to the
opposite presentation `Bᵒᵖ ⟶ Aᵒᵖ`, up to the canonical kernel
isomorphism supplied by exactness. -/
def kernelOpContravariantPresentationIso
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) :
    CategoryTheory.Preadditive.RightFreyd.kernelOp.obj
        (Opposite.op (contravariantEpiPresentation K hK)) ≅
      covariantEpiPresentation K hK := by
  letI : Mono K.f := hK.mono_f
  let qop := CategoryTheory.Preadditive.RightFreyd.quotient
    (RightModule.FinitelyGeneratedCategory A)ᵒᵖ
  let eK : kernel K.g ≅ K.X₁ :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel K.g) hK.exact.fIsKernel
  have heK : eK.inv ≫ kernel.ι K.g = K.f := by
    have h := IsLimit.conePointUniqueUpToIso_inv_comp
      (kernelIsKernel K.g) hK.exact.fIsKernel WalkingParallelPair.zero
    change eK.inv ≫ kernel.ι K.g = K.f at h
    exact h
  let eArrow : Arrow.mk (kernel.ι K.g).op ≅ Arrow.mk K.f.op :=
    Arrow.isoMk (Iso.refl _) eK.symm.op (by
      apply Quiver.Hom.unop_inj
      change K.f = eK.inv ≫ kernel.ι K.g
      exact heK.symm)
  exact ObjectProperty.isoMk _ (qop.mapIso eArrow)

/-- The chosen inverse of contravariant Freyd realization is canonically
isomorphic to the displayed presentation. -/
def contravariantRealizationInverseIsoPresentation
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) :
    S.contravariantEpiFreydEquivalence.inverse.obj
        (S.contravariantDefectObject K hK) ≅
      contravariantEpiPresentation K hK :=
  S.contravariantEpiFreydRealization.preimageIso
    (S.contravariantEpiFreydRealization.objObjPreimageIso
        (S.contravariantDefectObject K hK) ≪≫
      (S.contravariantEpiPresentationRealizationIso K hK).symm)

/-- The exact-defect anti-equivalence sends the contravariant defect of a
short exact sequence to its covariant defect. -/
def coherentDefectEquivalenceObjIso
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) :
    S.coherentDefectEquivalence.functor.obj
        (Opposite.op (S.contravariantDefectObject K hK)) ≅
      S.covariantDefectObject K hK := by
  let ePresentation :=
    S.contravariantRealizationInverseIsoPresentation K hK
  exact
    S.covariantEpiFreydRealization.mapIso
        (CategoryTheory.Preadditive.RightFreyd.kernelOp.mapIso
          ePresentation.symm.op) ≪≫
      S.covariantEpiFreydRealization.mapIso
        (kernelOpContravariantPresentationIso K hK) ≪≫
      S.covariantEpiPresentationRealizationIso K hK

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
