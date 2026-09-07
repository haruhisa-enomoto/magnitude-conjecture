import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdown
import MagnitudeConjecture.CategoryTheory.OrbitPushdownIndecomposable

/-!
# Indecomposability under finite skeletal orbit push-down

This file packages the generic orbit push-down indecomposability theorem for
the literal finite-dimensional module categories and chosen deck-orbit
skeleton used by the covering argument.  The finite-dimensional module's
local endomorphism ring is transported to its underlying raw functor, while
its categorical trivial stabilizer is converted to the corresponding raw
precomposition statement.  Indecomposability then passes through restriction
to the orbit skeleton and the two full-subcategory wrappers.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The two fully faithful full-subcategory inclusions identify the
endomorphism ring of a finite-dimensional module with that of its underlying
raw functor. -/
noncomputable def finiteDimensionalModuleEndUnderlyingRingEquiv
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    End M ≃+* End M.obj.obj := by
  let J : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      (C ⥤ ModuleCat.{uM} k) :=
    (IsFiniteDimensionalModule (C := C) k).ι ⋙
      (IsLinearModule (C := C) k).ι
  exact
    { toFun := J.map
      invFun := J.preimage
      left_inv := J.preimage_map
      right_inv := J.map_preimage
      map_add' := by
        intro f g
        exact J.map_add
      map_mul' := fun f g ↦ J.map_comp g f }

/-- Localness of the finite-dimensional categorical endomorphism ring passes
to the underlying raw functor. -/
theorem finiteDimensionalModule_underlying_end_isLocalRing
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hM : Indecomposable M) : IsLocalRing (End M.obj.obj) := by
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hM
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (finiteDimensionalModuleEndUnderlyingRingEquiv (k := k) M)

set_option backward.isDefEq.respectTransparency false in
/-- A trivial stabilizer in the finite-dimensional module category gives the
raw precomposition form required by generic orbit push-down.  Module shift
degree `-a` has underlying functor `shiftFunctor C a ⋙ M`. -/
theorem finiteDimensionalModule_trivial_raw_translate_stabilizer
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    (∀ a : Additive G, Nonempty (M ≅ M⟦a⟧) → a = 0) →
      ∀ a : Additive G,
        Nonempty (M.obj.obj ≅ shiftFunctor C a ⋙ M.obj.obj) →
          a = 0 := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro htrivial a
  rintro ⟨e⟩
  change M.obj.obj ≅ D.core.F a ⋙ M.obj.obj at e
  let J : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      (C ⥤ ModuleCat.{uM} k) :=
    (IsFiniteDimensionalModule (C := C) k).ι ⋙
      (IsLinearModule (C := C) k).ι
  let eshift : J.obj (M⟦-a⟧) ≅
      D.core.F a ⋙ M.obj.obj := by
    let efd := D.finiteDimensionalModuleShiftUnderlyingIso
      (k := k) M (-a)
    let efdRaw := (IsLinearModule (C := C) k).ι.mapIso efd
    let epre := linearModuleShiftUnderlyingIso
      (k := k) D.core M.obj (-a)
    let epre' :
        (IsLinearModule (C := C) k).ι.obj (M.obj⟦-a⟧) ≅
          D.core.F a ⋙ M.obj.obj := by
      convert epre using 1
      all_goals simp
    exact efdRaw ≪≫ epre'
  have hneg : -a = 0 := htrivial (-a)
    ⟨J.preimageIso (e ≪≫ eshift.symm)⟩
  exact neg_eq_zero.mp hneg

variable [IsCancelSMul G C]

/-- Manuscript-facing Gabriel 3.5: an indecomposable finite-dimensional
module with trivial deck stabilizer has indecomposable literal skeletal
push-down. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
    (M : FiniteDimensionalModuleCategory.{u, v, uK, w} (C := C) k)
    (hM : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    (∀ a : Additive G, Nonempty (M ≅ M⟦a⟧) → a = 0) →
      Indecomposable
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro htrivial
  have hraw : Indecomposable
      (orbitPushdown (A := Additive G) M.obj.obj) :=
    orbitPushdown_indecomposable_of_local_end_of_trivial_stabilizer
      (A := Additive G) M.obj.obj
      (finiteDimensionalModule_underlying_end_isLocalRing (k := k) M hM)
      (D.finiteDimensionalModule_trivial_raw_translate_stabilizer
        (k := k) M htrivial)
  let R := deckOrbitRepresentativeFunctor (C := C) (G := G)
  letI : R.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := D.deckOrbitRepresentativeFunctor_essSurj }
  let W := (Functor.whiskeringLeft
    (DeckOrbitSkeleton C G)
    (ShiftOrbitCategory C (Additive G))
    (ModuleCat.{w} k)).obj R
  have hskeletonRaw : Indecomposable
      (orbitSkeletonPushdown (G := G) M.obj.obj) := by
    change Indecomposable
      (W.obj (orbitPushdown (A := Additive G) M.obj.obj))
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        W (orbitPushdown (A := Additive G) M.obj.obj)).mpr hraw
  have hskeletonLinear : Indecomposable
      ((linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G)).obj M.obj) := by
    apply
      MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
        (IsLinearModule (C := DeckOrbitSkeleton C G) k).ι
    exact hskeletonRaw
  apply
    MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
      (IsFiniteDimensionalModule (C := DeckOrbitSkeleton C G) k).ι
  exact hskeletonLinear

/-- Indecomposability preservation transported across an explicit equality of
shift instances. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_indecomposable_of_trivial_stabilizer
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (M : FiniteDimensionalModuleCategory.{u, v, uK, w} (C := C) k)
    (hM : Indecomposable M)
    (htrivial :
      letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := isLinearModule_stableUnderShift (k := k) D.core
      letI := linearModuleCategoryHasShift (k := k) D.core
      letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
      letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
      ∀ a : Additive G, Nonempty (M ≅ M⟦a⟧) → a = 0) :
    letI := H
    letI := hadd
    letI := hlinear
    Indecomposable
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
        (k := k) H hadd hlinear hH).obj M) := by
  cases hH
  letI := D.hasShift
  letI := hadd
  letI := hlinear
  change Indecomposable
    ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M)
  exact
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) M hM htrivial

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
