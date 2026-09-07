import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownExact
import MagnitudeConjecture.CategoryTheory.FiniteOrbitRadicalComponents

/-!
# Simple modules under finite orbit push-down

Every simple finite module is the simple top of an indecomposable
representable.  The already established projective-radical square and
exactness of skeletal orbit push-down therefore identify its push-down with
the simple top of the corresponding orbit representable.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Every simple finite-dimensional module over a locally bounded linear
category is the cokernel of the radical inclusion of some finite
representable. -/
theorem exists_iso_cokernel_finiteDimensionalLinearCoyonedaRadicalInclusion_of_simple
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    [Simple M] :
    ∃ X : C, Nonempty
      (M ≅ cokernel
        (finiteDimensionalLinearCoyonedaRadicalInclusion
          (k := k) X (hP X))) := by
  classical
  have hex : ∃ (X : C) (x : M.obj.obj.obj X), x ≠ 0 := by
    by_contra h
    push Not at h
    apply CategoryTheory.id_nonzero M
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = 0
    exact h X x
  obtain ⟨X, x, hx⟩ := hex
  let P := finiteDimensionalLinearCoyoneda (k := k) X (hP X)
  let r := finiteDimensionalLinearCoyonedaRadicalInclusion
    (k := k) X (hP X)
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let pLinear : J.obj P ⟶ J.obj M :=
    linearCoyonedaHom M.obj X x
  let p : P ⟶ M := J.preimage pLinear
  have hp : p ≠ 0 := by
    intro hzero
    apply hx
    have hmap : J.map p = pLinear := by
      dsimp only [p]
      exact J.map_preimage pLinear
    have hz := congrArg
      (fun f : P ⟶ M ↦ (J.map f).hom.app X (𝟙 X)) hzero
    rw [hmap, J.map_zero] at hz
    change (linearCoyonedaHom M.obj X x).hom.app X (𝟙 X) = 0 at hz
    rw [linearCoyonedaHom_app_id] at hz
    exact hz
  letI : Projective P :=
    finiteDimensionalLinearCoyoneda_projective X (hP X)
  letI : IsLocalRing (End P) :=
    finiteDimensionalLinearCoyoneda_end_isLocalRing hP hlocal X
  have hr : IsRightAlmostSplit r :=
    finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hP hlocal X
  exact ⟨X, ⟨
    (MagnitudeConjecture.CategoryTheory.cokernelIsoSimpleTarget_of_mono_rightAlmostSplit_projective
      r hr p hp).symm⟩⟩

namespace CoherentDeckShift

variable {G : Type v} [Group G]
variable [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Finite skeletal Gabriel push-down sends simple finite modules to simple
finite modules. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_simple
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Simple M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Simple
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Simple M := hM
  obtain ⟨X, ⟨eM⟩⟩ :=
    exists_iso_cokernel_finiteDimensionalLinearCoyonedaRadicalInclusion_of_simple
      hP hlocal M
  let F := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let r := finiteDimensionalLinearCoyonedaRadicalInclusion
    (k := k) X (hP X)
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hlocal' := D.orbitSkeleton_end_isLocalRing
    (k := k) hP hlocal hfree
  let Q : DeckOrbitSkeleton C G :=
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
  let r' := finiteDimensionalLinearCoyonedaRadicalInclusion
    (k := k) Q (hP' Q)
  let eR :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k) hP hlocal hfree X
  let eP :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) X (hP X)
  have hsquare : F.map r ≫ eP.hom = eR.hom ≫ r' := by
    exact (D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalInclusion
      (k' := k) hP hlocal hfree X).symm
  let ecoker : F.obj (cokernel r) ≅ cokernel r' :=
    PreservesCokernel.iso F r ≪≫
      cokernel.mapIso (F.map r) r' eR eP hsquare
  let e : F.obj M ≅ cokernel r' := F.mapIso eM ≪≫ ecoker
  let P' := finiteDimensionalLinearCoyoneda (k := k) Q (hP' Q)
  letI : Projective P' :=
    finiteDimensionalLinearCoyoneda_projective Q (hP' Q)
  have hr' : IsRightAlmostSplit r' :=
    finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hP' hlocal' Q
  letI : Simple (cokernel r') :=
    MagnitudeConjecture.CategoryTheory.simple_cokernel_of_mono_rightAlmostSplit_projective
      r' hr'
  exact Simple.of_iso e

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
