import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownMinimalPresentation
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownSimple
import MagnitudeConjecture.CategoryTheory.RadicalSubobject
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# Uniserial modules under finite orbit push-down

For a nonzero uniserial finite module, a minimal projective cover has
indecomposable source and hence, under the localness hypotheses, is a single
finite representable.  Its radical is the monic right almost-split boundary
of that representable.  The projective-radical square identifies this
boundary after push-down.  Strong induction on total dimension then proves
that finite skeletal Gabriel push-down preserves uniseriality.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G]
variable [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Finite skeletal Gabriel push-down sends uniserial finite modules to
uniserial finite modules. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_uniserial
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : IsUniserialObject M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    IsUniserialObject
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  have main : ∀ n : ℕ,
      ∀ N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
        moduleTotalDimension N = n → IsUniserialObject N →
          IsUniserialObject (F.obj N) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro N hdim hN
        by_cases hNzero : IsZero N
        · exact IsUniserialObject.of_isZero (F.map_isZero hNzero)
        obtain ⟨P⟩ :=
          finiteDimensionalModule_minimalProjectivePresentation_nonempty hP N
        have hPind : Indecomposable P.p :=
          P.source_indecomposable_of_uniserial hN hNzero
        obtain ⟨X, ⟨eP⟩⟩ :=
          indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
            hP hlocal P.p hPind
        let Rep := finiteDimensionalLinearCoyoneda (k := k) X (hP X)
        let b : (⨁ fun _ : Fin 1 ↦ Rep) ≅ Rep :=
          biproductUniqueIso (fun _ : Fin 1 ↦ Rep)
        let coordinates : FiniteRepresentableCoordinates hP P.p :=
          { n := 1
            X := fun _ ↦ X
            isoSource := b ≪≫ eP }
        let Q : MinimalFiniteRepresentablePresentation hP N :=
          MinimalFiniteRepresentablePresentation.ofMinimalProjectivePresentation
            P coordinates
        let r := finiteDimensionalLinearCoyonedaRadicalInclusion
          (k := k) X (hP X)
        let rQ : finiteDimensionalLinearCoyonedaRadical (k := k) X (hP X) ⟶
            Q.source := r ≫ b.inv
        have hr : IsRightAlmostSplit r :=
          finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
            hP hlocal X
        have hrQ : IsRightAlmostSplit rQ := by
          exact hr.postcomp_iso b.symm
        have hRQradical :
            IsUniserialObject.IsRadicalSubobject (Subobject.mk rQ) :=
          isRadicalSubobject_mk_of_mono_rightAlmostSplit rQ hrQ
        have hRQproper : Subobject.mk rQ ≠ ⊤ :=
          mk_ne_top_of_mono_rightAlmostSplit rQ hrQ
        let fU := rQ ≫ Q.f
        let RU := imageSubobject fU
        have hRUradical :
            IsUniserialObject.IsRadicalSubobject RU := by
          exact isRadicalSubobject_imageSubobject_comp_of_epi
            rQ Q.f hRQradical
        have hQessential : IsEssentialEpi Q.f :=
          isEssentialEpi_of_isRightMinimal Q.f Q.rightMinimal
        have hRUproper : RU ≠ ⊤ := by
          exact imageSubobject_comp_ne_top_of_isEssentialEpi
            rQ Q.f hQessential hRQproper
        have hRU : IsUniserialObject (RU :
            FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
          hN.subobject RU
        have hRUarrowNotIso : ¬ IsIso RU.arrow := by
          intro hiso
          letI : IsIso RU.arrow := hiso
          apply hRUproper
          simpa using
            (Subobject.isIso_iff_mk_eq_top RU.arrow).mp
              (inferInstance : IsIso RU.arrow)
        have hRUdim : moduleTotalDimension (RU :
              FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) < n := by
          rw [← hdim]
          exact moduleTotalDimension_lt_of_mono_not_isIso
            (RU : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
            N RU.arrow hRUarrowNotIso
        have hFRU : IsUniserialObject (F.obj (RU :
            FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)) :=
          ih (moduleTotalDimension (RU :
              FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
            hRUdim (RU :
              FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
            rfl hRU
        let eb := F.mapIso b.symm
        have hFr : IsRightAlmostSplit (F.map r) :=
          D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalInclusion_isRightAlmostSplit
            (k' := k) hP hlocal hfree X
        have hFrQ : IsRightAlmostSplit (F.map rQ) := by
          have hcomp := hFr.postcomp_iso eb
          change IsRightAlmostSplit (F.map r ≫ F.map b.inv) at hcomp
          change IsRightAlmostSplit (F.map (r ≫ b.inv))
          simpa only [F.map_comp] using hcomp
        letI : Projective (F.obj Q.source) := by
          change Projective
            (F.obj
              ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj
                Q.toFiniteRepresentablePresentation.matrixObject))
          exact
            D.finiteProjectiveRepresentableSumOrbitSkeletonPushdown_projective
              (k := k) hP Q.toFiniteRepresentablePresentation.matrixObject
        have hQDminimal : IsRightMinimal (F.map Q.f) :=
          D.finiteDimensionalModuleOrbitSkeletonPushdown_minimalFiniteRepresentablePresentation_rightMinimal
            (k := k) hP hlocal hfree Q
        have hQDessential : IsEssentialEpi (F.map Q.f) :=
          isEssentialEpi_of_isRightMinimal (F.map Q.f) hQDminimal
        let RD := imageSubobject (F.map fU)
        have hRDradical :
            IsUniserialObject.IsRadicalSubobject RD := by
          simpa only [RD, fU, F.map_comp] using
            (isRadicalSubobject_imageSubobject_comp_of_epi
              (F.map rQ) (F.map Q.f)
              (isRadicalSubobject_mk_of_mono_rightAlmostSplit
                (F.map rQ) hFrQ))
        have eImage : F.obj (RU :
              FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) ≅
            (RD : FiniteDimensionalModuleCategory.{u, v, v, v}
              (C := DeckOrbitSkeleton C G) k) :=
          F.mapIso (imageSubobjectIso fU) ≪≫
            F.mapIso (Abelian.imageIsoImage fU).symm ≪≫
            Abelian.PreservesImage.iso F fU ≪≫
              Abelian.imageIsoImage (F.map fU) ≪≫
              (imageSubobjectIso (F.map fU)).symm
        have hRD : IsUniserialObject (RD :
            FiniteDimensionalModuleCategory.{u, v, v, v}
              (C := DeckOrbitSkeleton C G) k) :=
          hFRU.congr eImage
        exact IsUniserialObject.of_radicalSubobject RD hRDradical hRD
  exact main (moduleTotalDimension M) M rfl hM

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
