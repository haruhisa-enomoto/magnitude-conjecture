import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleInjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamPresentation
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownIndecomposable
import MagnitudeConjecture.CategoryTheory.RepresentableDeckShift

/-!
# Projective and injective boundaries of finite orbit push-down

Gabriel's component argument also uses the boundary vertices of the
Auslander--Reiten quiver.  This file begins the boundary comparison by showing
that the chosen deck-orbit skeleton again has local vertex endomorphism rings
and that every indecomposable projective downstairs is the push-down of an
indecomposable projective upstairs.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v u₀ v₀ uD vD

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

private def endRingEquivOfFullyFaithful
    {C₀ : Type u₀} {D₀ : Type uD}
    [Category.{v₀} C₀] [Preadditive C₀]
    [Category.{vD} D₀] [Preadditive D₀]
    (F : Functor C₀ᵒᵖ D₀) [F.Additive] [F.Full] [F.Faithful]
    (X : C₀ᵒᵖ) :
    End X ≃+* End (F.obj X) where
  toFun := F.map
  invFun := F.preimage
  left_inv := F.preimage_map
  right_inv := F.map_preimage
  map_add' _ _ := F.map_add
  map_mul' f g := F.map_comp g f

private def oppositeEndRingEquiv
    {C₀ : Type u₀} [Category.{v₀} C₀] [Preadditive C₀]
    (X : C₀) :
    (End X)ᵐᵒᵖ ≃+* End (Opposite.op X) where
  toFun f := f.unop.op
  invFun f := MulOpposite.op f.unop
  left_inv := by intro f; cases f; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; apply Quiver.Hom.unop_inj; rfl
  map_mul' := by intro f g; apply Quiver.Hom.unop_inj; rfl

private def endRingEquivOfIso
    {D₀ : Type uD} [Category.{vD} D₀] [Preadditive D₀]
    {X Y : D₀} (e : X ≅ Y) : End X ≃+* End Y :=
  { e.conj with
    map_add' := by
      intro f g
      apply End.ext
      change e.inv ≫ (End.asHom f + End.asHom g) ≫ e.hom =
        e.inv ≫ End.asHom f ≫ e.hom +
          e.inv ≫ End.asHom g ≫ e.hom
      simp only [Preadditive.comp_add, Preadditive.add_comp] }

private theorem isLocalRing_mulOpposite
    {R : Type v} [Ring R] [IsLocalRing R] :
    IsLocalRing Rᵐᵒᵖ := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := R) (a := a.unop) (b := 1 - a.unop)
      (add_sub_cancel a.unop 1) with h | h
  · exact Or.inl (by simpa using h.op)
  · exact Or.inr (by simpa using h.op)

private theorem isLocalRing_of_mulOpposite
    {R : Type v} [Ring R] [IsLocalRing Rᵐᵒᵖ] :
    IsLocalRing R := by
  letI : IsLocalRing (Rᵐᵒᵖ)ᵐᵒᵖ := isLocalRing_mulOpposite
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (RingEquiv.opOp R).symm

/-- The endomorphism ring of every object of the chosen deck-orbit skeleton
is local.  This is inherited from an upstairs representative by passing to
its finite representable, using Gabriel 3.5 for the pushed module, and then
reflecting through fully faithful linear co-Yoneda. -/
theorem orbitSkeleton_end_isLocalRing
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ q : DeckOrbitSkeleton C G, IsLocalRing (End q) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro q
  induction q using Quotient.inductionOn with
  | _ X =>
      let M := finiteDimensionalLinearCoyoneda (k := k) X (hP X)
      have hM : Indecomposable M :=
        finiteDimensionalLinearCoyoneda_indecomposable hP hlocal X
      have hPM : Indecomposable
          ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) :=
        D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
          (k := k) M hM
            (D.finiteDimensionalLinearCoyoneda_trivialStabilizer
              (k := k) hP hfree X)
      let R := D.orbitSkeletonFiniteDimensionalLinearCoyoneda
        (k := k) X (hP X)
      let e := D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
        (k := k) X (hP X)
      have hR : Indecomposable R :=
        (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).mp hPM
      let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
      let F := finiteDimensionalLinearCoyonedaFunctor (k := k) hP'
      let Q : DeckOrbitSkeleton C G :=
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
      let eR : R ≅ F.obj (Opposite.op Q) :=
        Iso.refl _
      letI : IsLocalRing (End R) :=
        finiteDimensionalModule_end_isLocalRing k R hR
      letI : IsLocalRing (End (F.obj (Opposite.op Q))) :=
        MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
          (endRingEquivOfIso eR)
      letI : F.Full := by
        dsimp [F, finiteDimensionalLinearCoyonedaFunctor,
          linearCoyonedaLinearModuleFunctor]
        infer_instance
      letI : F.Faithful := by
        dsimp [F, finiteDimensionalLinearCoyonedaFunctor,
          linearCoyonedaLinearModuleFunctor]
        infer_instance
      letI : IsLocalRing (End (Opposite.op Q)) :=
        MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
          (endRingEquivOfFullyFaithful
            (C₀ := DeckOrbitSkeleton C G)
            (D₀ := FiniteDimensionalModuleCategory
              (C := DeckOrbitSkeleton C G) k)
            F (Opposite.op Q)).symm
      letI : IsLocalRing (End Q)ᵐᵒᵖ :=
        MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
          (oppositeEndRingEquiv Q).symm
      exact isLocalRing_of_mulOpposite

/-- Gabriel 3.6(b), projective boundary: every indecomposable projective on
the deck-orbit skeleton is the push-down of an indecomposable projective
finite module upstairs. -/
theorem exists_projectiveIndecomposable_preimage
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ {Y : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k} [Projective Y],
      Indecomposable Y →
        ∃ M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
          Projective M ∧ Indecomposable M ∧
            Nonempty
              ((D.finiteDimensionalModuleOrbitSkeletonPushdown
                (k := k)).obj M ≅ Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro Y hYProjective hY
  letI : Projective Y := hYProjective
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  have hlocal' : ∀ q : DeckOrbitSkeleton C G, IsLocalRing (End q) :=
    D.orbitSkeleton_end_isLocalRing (k := k) hP hlocal hfree
  obtain ⟨q, ⟨eY⟩⟩ :=
    indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
      hP' hlocal' Y hY
  revert eY
  induction q using Quotient.inductionOn with
  | _ X =>
      intro eY
      let M := finiteDimensionalLinearCoyoneda (k := k) X (hP X)
      have hM : Indecomposable M :=
        finiteDimensionalLinearCoyoneda_indecomposable hP hlocal X
      let ePush :=
        D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
          (k := k) X (hP X)
      let eCoordinate :
          D.orbitSkeletonFiniteDimensionalLinearCoyoneda (k := k) X (hP X)
            ≅
          (finiteDimensionalLinearCoyonedaFunctor (k := k) hP').obj
            (Opposite.op
              (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)) :=
        Iso.refl _
      exact ⟨M, inferInstance, hM, ⟨ePush ≪≫ eCoordinate ≪≫ eY⟩⟩

/-- Gabriel 3.6(b), injective boundary: every indecomposable injective on
the deck-orbit skeleton is the push-down of an indecomposable injective
finite module upstairs. -/
theorem exists_injectiveIndecomposable_preimage
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ {Y : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k} [Injective Y],
      Indecomposable Y →
        ∃ M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
          Injective M ∧ Indecomposable M ∧
            Nonempty
              ((D.finiteDimensionalModuleOrbitSkeletonPushdown
                (k := k)).obj M ≅ Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro Y hYInjective hY
  letI : Injective Y := hYInjective
  let hI' := D.orbitSkeletonDualLinearYonedaFinite (k := k) hI
  have hlocal' : ∀ q : DeckOrbitSkeleton C G, IsLocalRing (End q) :=
    D.orbitSkeleton_end_isLocalRing (k := k) hP hlocal hfree
  obtain ⟨q, ⟨eY⟩⟩ :=
    indecomposable_injective_iso_finiteDimensionalDualLinearYoneda
      hI' hlocal' Y hY
  revert eY
  induction q using Quotient.inductionOn with
  | _ X =>
      intro eY
      let M := finiteDimensionalDualLinearYoneda (k := k) X (hI X)
      have hM : Indecomposable M :=
        finiteDimensionalDualLinearYoneda_indecomposable hI hlocal X
      let ePush :=
        D.finiteDimensionalModuleOrbitSkeletonPushdownDualLinearYonedaIso
          (k := k) X (hI X)
      let eCoordinate :
          D.orbitSkeletonFiniteDimensionalDualLinearYoneda (k := k) X (hI X)
            ≅
          (finiteDimensionalDualLinearYonedaFunctor (k := k) hI').obj
            (Opposite.op
              (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)) :=
        Iso.refl _
      exact ⟨M, finiteDimensionalDualLinearYoneda_injective X (hI X),
        hM, ⟨ePush ≪≫ eCoordinate ≪≫ eY⟩⟩

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
