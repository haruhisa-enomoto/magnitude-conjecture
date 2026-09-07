import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownHomEquiv
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecompositionUniqueness
import MagnitudeConjecture.CategoryTheory.ShiftOrbitIsoComponent
import MagnitudeConjecture.CategoryTheory.ShiftOrbitSplitComponent

/-!
# Finite orbit push-down reflects deck orbits

Gabriel's Hom equivalence identifies the shift-orbit endomorphism ring of an
upstairs finite module with the endomorphism ring of its skeletal push-down.
For an indecomposable with trivial stabilizer, the latter is local.  Hence an
isomorphism between two push-downs has an invertible homogeneous lift, so the
upstairs modules differ by a deck translate.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Gabriel's Hom equivalence is an equivalence of endomorphism rings. -/
noncomputable def finiteDimensionalModuleOrbitEndRingEquiv
    (M : FiniteDimensionalModuleCategory.{u, v, uK, w} (C := C) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, w}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    End (show ShiftOrbitCategory
      (LinearModuleCategory.{u, v, uK, w} (C := C) k)
        (Additive G) from M.obj) ≃+*
      End ((D.finiteDimensionalModuleOrbitSkeletonPushdown
        (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, w}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let E := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M M
  exact
    { toFun := E
      invFun := E.symm
      left_inv := E.symm_apply_apply
      right_inv := E.apply_symm_apply
      map_add' := E.map_add
      map_mul' := by
        intro f g
        change E (shiftOrbitCompHom g f) = E g ≫ E f
        exact (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_comp
          (k := k) M M M g f).symm }

/-- A shift autoequivalence transports the local-endomorphism property. -/
theorem shift_obj_end_isLocalRing
    {C₀ : Type u} [Category.{v} C₀] [Preadditive C₀]
    {A₀ : Type w} [AddGroup A₀] [HasShift C₀ A₀]
    [∀ a : A₀, (shiftFunctor C₀ a).Additive]
    (X : C₀) (hlocal : IsLocalRing (End X)) (a : A₀) :
    IsLocalRing (End ((shiftFunctor C₀ a).obj X)) := by
  let F := shiftFunctor C₀ a
  letI : F.IsEquivalence := inferInstance
  letI : IsLocalRing (End X) := hlocal
  let E : End X ≃+* End (F.obj X) :=
    { toFun := F.map
      invFun := F.preimage
      left_inv := F.preimage_map
      right_inv := F.map_preimage
      map_add' := by
        intro f g
        exact F.map_add
      map_mul' := fun f g ↦ F.map_comp g f }
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm E

/-- The shift-orbit endomorphism ring of an indecomposable finite module
with trivial stabilizer is local, via its indecomposable push-down. -/
theorem finiteDimensionalModuleOrbit_end_isLocalRing
    (M : FiniteDimensionalModuleCategory.{u, v, uK, w} (C := C) k)
    (hM : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, w}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    (∀ a : Additive G, Nonempty (M ≅ M⟦a⟧) → a = 0) →
      IsLocalRing
        (End (show ShiftOrbitCategory
          (LinearModuleCategory.{u, v, uK, w} (C := C) k)
            (Additive G) from M.obj)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, w}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro htrivial
  have hPM : Indecomposable
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) M hM htrivial
  letI : IsLocalRing
      (End ((D.finiteDimensionalModuleOrbitSkeletonPushdown
        (k := k)).obj M)) :=
    finiteDimensionalModule_end_isLocalRing k _ hPM
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (D.finiteDimensionalModuleOrbitEndRingEquiv (k := k) M).symm

/-- An isomorphism of finite skeletal push-downs makes an indecomposable
upstairs source a retract of one translate of the arbitrary upstairs target. -/
theorem exists_splitMono_shiftHom_of_pushdown_iso
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hM : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    Nonempty
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M ≅
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj N) →
      ∃ a : Additive G, ∃ f : ShiftHom M.obj N.obj a, IsSplitMono f := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  rintro ⟨e⟩
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let E_MN := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M N
  let E_NM := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) N M
  let E_MM := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M M
  let q : ShiftOrbitHom (Additive G) M.obj N.obj := E_MN.symm e.hom
  let r : ShiftOrbitHom (Additive G) N.obj M.obj := E_NM.symm e.inv
  have hEidM : E_MM (shiftOrbitId M.obj) = 𝟙 (P.obj M) := by
    rw [shiftOrbitId, ← shiftHomZero_id (A := Additive G)]
    exact (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero
      (k := k) M M (𝟙 M)).trans (P.map_id M)
  have hqr : shiftOrbitCompHom q r = shiftOrbitId M.obj := by
    apply E_MM.injective
    rw [← D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_comp
      (k := k) M N M]
    rw [E_MN.apply_symm_apply, E_NM.apply_symm_apply, hEidM]
    exact e.hom_inv_id
  have hlocal : IsLocalRing (End M.obj) :=
    finiteDimensionalModule_linearModule_end_isLocalRing k M hM
  obtain ⟨a, ha⟩ :=
    exists_isSplitMono_shiftOrbitHom_component_of_retraction
      (k := k) hlocal q r hqr
  exact ⟨a, q a, ha⟩

/-- If an indecomposable upstairs module has push-down isomorphic to the
push-down of a finite biproduct of indecomposables, it is a translate of one
of those summands. -/
theorem exists_shift_iso_finBiproduct_component_of_pushdown_iso
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hM : Indecomposable M) (n : ℕ)
    (N : Fin n → FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hN : ∀ i, Indecomposable (N i)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    Nonempty
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M ≅
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
            (⨁ N)) →
      ∃ a : Additive G, ∃ i : Fin n, Nonempty (M ≅ (N i)⟦a⟧) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro hpush
  obtain ⟨a, f, hf⟩ := D.exists_splitMono_shiftHom_of_pushdown_iso
    (k := k) M (⨁ N) hM hpush
  letI : IsSplitMono f := hf
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  let S := shiftFunctor
    (LinearModuleCategory.{u, v, uK, uM} (C := C) k) a
  let eTarget : (⨁ N).obj⟦a⟧ ≅
      ⨁ fun i ↦ (N i).obj⟦a⟧ :=
    S.mapIso (J.mapBiproduct N) ≪≫
      S.mapBiproduct (fun i ↦ (N i).obj)
  let f' : M.obj ⟶ ⨁ fun i ↦ (N i).obj⟦a⟧ := f ≫ eTarget.hom
  let g' : (⨁ fun i ↦ (N i).obj⟦a⟧) ⟶ M.obj :=
    eTarget.inv ≫ retraction f
  have hfg : f' ≫ g' = 𝟙 M.obj := by
    simp [f', g', Category.assoc, IsSplitMono.id]
  have hlocalM : IsLocalRing (End M.obj) :=
    finiteDimensionalModule_linearModule_end_isLocalRing k M hM
  have hMobj : Indecomposable M.obj := by
    letI : IsLocalRing (End M.obj) := hlocalM
    exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _
  have hNshift : ∀ i, Indecomposable ((N i).obj⟦a⟧) := by
    intro i
    have hlocalNi : IsLocalRing (End (N i).obj) :=
      finiteDimensionalModule_linearModule_end_isLocalRing k (N i) (hN i)
    have hlocalShift : IsLocalRing (End ((N i).obj⟦a⟧)) :=
      shift_obj_end_isLocalRing (N i).obj hlocalNi a
    letI : IsLocalRing (End ((N i).obj⟦a⟧)) := hlocalShift
    exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _
  obtain ⟨i, hi⟩ :=
    MagnitudeConjecture.CategoryTheory.exists_isIso_component_of_retraction_finBiproduct
      hMobj hlocalM n (fun i ↦ (N i).obj⟦a⟧) hNshift f' g' hfg
  letI : IsIso
      (f' ≫ Limits.biproduct.π (fun i ↦ (N i).obj⟦a⟧) i) := hi
  let eLinear : M.obj ≅ (N i).obj⟦a⟧ :=
    asIso (f' ≫ Limits.biproduct.π (fun i ↦ (N i).obj⟦a⟧) i)
  let eFiniteUnderlying : M.obj ≅ ((N i)⟦a⟧).obj :=
    eLinear ≪≫
      (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) (N i) a).symm
  exact ⟨a, i, ⟨J.preimageIso eFiniteUnderlying⟩⟩

/-- The finite skeletal orbit push-down reflects isomorphism classes up to a
deck translate. -/
theorem exists_shift_iso_of_pushdown_iso
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, w} (C := C) k)
    (hM : Indecomposable M) (hN : Indecomposable N) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, w}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    (∀ a : Additive G, Nonempty (M ≅ M⟦a⟧) → a = 0) →
      Nonempty
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M ≅
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj N) →
      ∃ a : Additive G, Nonempty (M ≅ N⟦a⟧) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, w}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro htrivial
  rintro ⟨e⟩
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let E_MN := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M N
  let E_NM := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) N M
  let E_MM := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) M M
  let E_NN := D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv
    (k := k) N N
  let q : ShiftOrbitHom (Additive G) M.obj N.obj := E_MN.symm e.hom
  let r : ShiftOrbitHom (Additive G) N.obj M.obj := E_NM.symm e.inv
  have hEidM : E_MM (shiftOrbitId M.obj) = 𝟙 (P.obj M) := by
    rw [shiftOrbitId, ← shiftHomZero_id (A := Additive G)]
    exact (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero
      (k := k) M M (𝟙 M)).trans (P.map_id M)
  have hEidN : E_NN (shiftOrbitId N.obj) = 𝟙 (P.obj N) := by
    rw [shiftOrbitId, ← shiftHomZero_id (A := Additive G)]
    exact (D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_zero
      (k := k) N N (𝟙 N)).trans (P.map_id N)
  have hqr : shiftOrbitCompHom q r = shiftOrbitId M.obj := by
    apply E_MM.injective
    rw [← D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_comp
      (k := k) M N M]
    rw [E_MN.apply_symm_apply, E_NM.apply_symm_apply, hEidM]
    exact e.hom_inv_id
  have hrq : shiftOrbitCompHom r q = shiftOrbitId N.obj := by
    apply E_NN.injective
    rw [← D.finiteDimensionalModuleOrbitSkeletonPushdownHomLinearEquiv_comp
      (k := k) N M N]
    rw [E_NM.apply_symm_apply, E_MN.apply_symm_apply, hEidN]
    exact e.inv_hom_id
  have hqIso : IsIso
      (show (show ShiftOrbitCategory
          (LinearModuleCategory.{u, v, uK, w} (C := C) k)
            (Additive G) from M.obj) ⟶
        (show ShiftOrbitCategory
          (LinearModuleCategory.{u, v, uK, w} (C := C) k)
            (Additive G) from N.obj) from q) := by
    apply IsIso.mk
    exact ⟨r, hqr, hrq⟩
  letI : IsIso
      (show (show ShiftOrbitCategory
          (LinearModuleCategory.{u, v, uK, w} (C := C) k)
            (Additive G) from M.obj) ⟶
        (show ShiftOrbitCategory
          (LinearModuleCategory.{u, v, uK, w} (C := C) k)
            (Additive G) from N.obj) from q) := hqIso
  letI : IsLocalRing (End M.obj) :=
    finiteDimensionalModule_linearModule_end_isLocalRing k M hM
  letI : IsLocalRing
      (End (show ShiftOrbitCategory
        (LinearModuleCategory.{u, v, uK, w} (C := C) k)
          (Additive G) from M.obj)) :=
    D.finiteDimensionalModuleOrbit_end_isLocalRing
      (k := k) M hM htrivial
  have hlocalN : IsLocalRing (End N.obj) :=
    finiteDimensionalModule_linearModule_end_isLocalRing k N hN
  have hlocalShiftN : ∀ a : Additive G,
      IsLocalRing
        (End ((shiftFunctor
          (LinearModuleCategory.{u, v, uK, w} (C := C) k) a).obj
            N.obj)) := fun a ↦ shift_obj_end_isLocalRing N.obj hlocalN a
  obtain ⟨a, ha⟩ := exists_isIso_shiftOrbitHom_component
    (k := k) hlocalShiftN q
  letI : IsIso (q a) := ha
  let eLinear : M.obj ≅ N.obj⟦a⟧ := asIso (q a)
  let eFiniteUnderlying : M.obj ≅ (N⟦a⟧).obj :=
    eLinear ≪≫ (D.finiteDimensionalModuleShiftUnderlyingIso
      (k := k) N a).symm
  exact ⟨a, ⟨(IsFiniteDimensionalModule (C := C) k).ι.preimageIso
    eFiniteUnderlying⟩⟩

/-- Orbit reflection transported across an explicit equality of shift
instances. -/
theorem exists_shift_iso_of_pushdown_iso_of_hasShift_eq
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (M N : FiniteDimensionalModuleCategory.{u, v, uK, w} (C := C) k)
    (hM : Indecomposable M) (hN : Indecomposable N)
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
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    Nonempty
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
          (k := k) H hadd hlinear hH).obj M ≅
        (D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
          (k := k) H hadd hlinear hH).obj N) →
      ∃ a : Additive G, Nonempty (M ≅ N⟦a⟧) := by
  cases hH
  letI := D.hasShift
  letI := hadd
  letI := hlinear
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  intro hMN
  apply D.exists_shift_iso_of_pushdown_iso (k := k) M N hM hN htrivial
  exact hMN

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
