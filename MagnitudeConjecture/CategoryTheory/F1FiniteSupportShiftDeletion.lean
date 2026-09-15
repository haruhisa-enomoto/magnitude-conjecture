import MagnitudeConjecture.CategoryTheory.F1FiniteSupportLocality
import MagnitudeConjecture.CategoryTheory.F1DeletionEquivariance
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence

/-!
# Shift transport for finite-support deletion density

This is the transport seam in the frozen F1 average.  A deck translate of an
indecomposable module, restricted after deleting the translated support, is
equivalent to the original restriction.  The statement is entirely
finite-dimensional and does not use residual finiteness.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped Pointwise
open MagnitudeConjecture.CoveringHom
open MagnitudeConjecture.ObjectDeletion

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Vanishing on an action-invariant deleted set is preserved by every deck
shift.  This is the support transport used when source-orbit labels are
reindexed by their unique translate at the selected object. -/
theorem moduleVanishesOnDeleted_shift_of_actionInvariant
    (S : Set C) (hS : ActionInvariant (G := G) S) (g : G)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift
      (k := k) (Additive.ofMul g)
    let Mshift :=
      (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
        (Additive.ofMul g)).obj M
    ModuleVanishesOnDeleted (k := k) C S Mshift.obj.obj := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift
    (k := k) (Additive.ofMul g)
  dsimp
  intro Y hY
  have hY' : g • Y ∈ S := (hS g Y).2 hY
  exact (hvanish (g • Y) hY').of_iso
    (D.finiteDimensionalModuleShiftEvaluationIso k M g Y)

set_option backward.isDefEq.respectTransparency false in
theorem finiteDimensionalModuleRestrictionToDeletion_shift_iso
    (hC : Skeletal C) (S : Set C) (hS : ActionInvariant (G := G) S)
    (g : Additive G)
    (M : FiniteDimensionalModuleCategory (C:=C) k)
    (hM : ModuleVanishesOnDeleted (k:=k) C S M.obj.obj) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k:=k)
    letI : ObjectProperty.IsClosedUnderIsomorphisms S := isClosedUnderIsomorphisms_of_skeletal hC S
    letI := D.isFiniteDimensionalModule_stableUnderShift (k:=k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k:=k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k:=k) g
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k:=k) S hShift
    letI := deletionMulAction (k:=k) S hS
    letI := deletionHasShift (k:=k) S hShift
    letI : ∀ a : Additive G, (shiftFunctor (DeletionCategory (k:=k) C S) a).Additive := fun a => deletionShift_additive (k:=k) S hShift a
    letI : ∀ a : Additive G, (shiftFunctor (DeletionCategory (k:=k) C S) a).Linear k := fun a => deletionShift_linear (k:=k) S hShift a
    letI : ∀ a : Additive G, (D.core.F a).Linear k := D.linearShift (k:=k)
    let Dstage := CoherentDeckShift.deletionCoherentDeckShift (k:=k) D S hS
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k:=k)
    letI := Dstage.isFiniteDimensionalModule_stableUnderShift (k:=k)
    letI := Dstage.finiteDimensionalModuleCategoryHasShift (k:=k)
    letI := Dstage.finiteDimensionalModuleCategoryAdditiveShift (k:=k) g
    let hshift := CoherentDeckShift.moduleVanishesOnDeleted_shift_of_actionInvariant (k:=k) D S hS g.toMul M hM
    Nonempty (finiteDimensionalModuleRestrictionToDeletion (k:=k) C S
      ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M) hshift ≅
      (shiftFunctor (FiniteDimensionalModuleCategory (C:=DeletionCategory (k:=k) C S) k) g).obj
        (finiteDimensionalModuleRestrictionToDeletion (k:=k) C S M hM)) := by
  letI : ObjectProperty.IsClosedUnderIsomorphisms S := isClosedUnderIsomorphisms_of_skeletal hC S
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k:=k)
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k:=k) S hShift
  letI := rawFunctorCommShift (k:=k) S hShift
  letI := isSurvivingRaw_stableUnderShift (k:=k) S hShift
  letI : (IsSurvivingRaw (k:=k) C S).ι.CommShift (Additive G) :=
    deletionInclusionCommShift (k:=k) S hShift
  letI := deletionMulAction (k:=k) S hS
  letI := deletionHasShift (k:=k) S hShift
  letI : ∀ a : Additive G, (shiftFunctor (DeletionCategory (k:=k) C S) a).Additive := fun a => deletionShift_additive (k:=k) S hShift a
  letI : ∀ a : Additive G, (shiftFunctor (DeletionCategory (k:=k) C S) a).Linear k := fun a => deletionShift_linear (k:=k) S hShift a
  let Dstage := CoherentDeckShift.deletionCoherentDeckShift (k:=k) D S hS
  letI := D.finiteDimensionalModuleCategoryHasShift (k:=k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k:=k) g
  have hshift : ModuleVanishesOnDeleted (k:=k) C S
      (((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj) := by
    exact CoherentDeckShift.moduleVanishesOnDeleted_shift_of_actionInvariant (k:=k) D S hS g.toMul M hM
  let A := finiteDimensionalModuleRestrictionToDeletion (k:=k) C S
      ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M) hshift
  let R := finiteDimensionalModuleRestrictionToDeletion (k:=k) C S M hM
  letI := isLinearModule_stableUnderShift (k:=k) D.core
  letI := linearModuleCategoryHasShift (k:=k) D.core
  letI := linearModuleCategoryAdditiveShift (R:=k) D.core
  letI := linearModuleCategoryLinearShift (R:=k) D.core
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R:=k) D.core
  letI := linearModuleCategoryLinearShift (R:=k) D.core
  let eunder := D.finiteDimensionalModuleShiftUnderlyingIso (k:=k) M g
  let eunderNat :
      ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj ≅
        ((shiftFunctor (LinearModuleCategory (C:=C) k) g).obj M.obj).obj := by
    exact { hom := eunder.hom.hom,
             inv := eunder.inv.hom,
             hom_inv_id := by
               change eunder.hom.hom ≫ eunder.inv.hom = 𝟙 _
               exact congrArg (fun t => t.hom) eunder.hom_inv_id,
             inv_hom_id := by
               change eunder.inv.hom ≫ eunder.hom.hom = 𝟙 _
               exact congrArg (fun t => t.hom) eunder.inv_hom_id }
  let elin := linearModuleShiftUnderlyingIso (k:=k) D.core M.obj g
  let elinNat :
      ((shiftFunctor (LinearModuleCategory (C:=C) k) g).obj M.obj).obj ≅
        (D.core.F (-g) ⋙ M.obj.obj) := by
    exact { hom := elin.hom,
             inv := elin.inv,
             hom_inv_id := elin.hom_inv_id,
             inv_hom_id := elin.inv_hom_id }
  let eA : A.obj.obj ≅ Dstage.core.F (-g) ⋙ R.obj.obj := by
    refine NatIso.ofComponents (fun X => ?_) ?_
    · dsimp [A, R, finiteDimensionalModuleRestrictionToDeletion,
        linearModuleRestrictionToDeletion, moduleRestrictionToDeletion]
      have hsurv : (D.core.F (-g)).obj X.obj.as ∉ S := by
        intro h
        apply X.property
        apply (hShift (-g) X.obj.as).1
        simpa [D.core.shiftFunctor_eq] using h
      let Y : DeletionCategory (k:=k) C S :=
        ⟨⟨(D.core.F (-g)).obj X.obj.as⟩, hsurv⟩
      have hxraw : X.obj = (rawFunctor (k:=k) C S).obj X.obj.as := by
        apply CategoryTheory.Quotient.ext
        rfl
      have eRaw :
          (rawFunctor (k:=k) C S).obj ((D.core.F (-g)).obj X.obj.as) ≅
            (rawShiftFunctor (k:=k) S hShift (-g)).obj X.obj := by
        rw [hxraw]
        have hxas : ((rawFunctor (k:=k) C S).obj X.obj.as).as = X.obj.as := rfl
        rw [hxas]
        convert ((rawFunctorShiftIso (k:=k) S hShift (-g)).app X.obj.as).symm using 1 <;>
          simp [D.core.shiftFunctor_eq]
      have eShift :
          (IsSurvivingRaw (k:=k) C S).ι.obj
              ((shiftFunctor (DeletionCategory (k:=k) C S) (-g)).obj X) ≅
            (rawShiftFunctor (k:=k) S hShift (-g)).obj X.obj := by
        exact ((IsSurvivingRaw (k:=k) C S).ι.commShiftIso (-g)).app X
      have eDel : Y ≅ (Dstage.core.F (-g)).obj X := by
        change Y ≅
          (shiftFunctor (DeletionCategory (k:=k) C S) (-g)).obj X
        apply ObjectProperty.isoMk
        exact eRaw ≪≫ eShift.symm
      let eR := R.obj.obj.mapIso eDel
      dsimp [Y, R, finiteDimensionalModuleRestrictionToDeletion,
        linearModuleRestrictionToDeletion, moduleRestrictionToDeletion] at eR ⊢
      exact (eunderNat.app X.obj.as).trans ((elinNat.app X.obj.as).trans eR)
    · intro X Y f
      rcases X with ⟨⟨X⟩, hX⟩
      rcases Y with ⟨⟨Y⟩, hY⟩
      obtain ⟨q, hq⟩ := (rawFunctor (k:=k) C S).map_surjective f.hom
      have hsurvX : (D.core.F (-g)).obj X ∉ S := by
        intro h
        apply hX
        apply (hShift (-g) X).1
        simpa [D.core.shiftFunctor_eq] using h
      have hsurvY : (D.core.F (-g)).obj Y ∉ S := by
        intro h
        apply hY
        apply (hShift (-g) Y).1
        simpa [D.core.shiftFunctor_eq] using h
      let eRawX :
          (rawFunctor (k:=k) C S).obj ((D.core.F (-g)).obj X) ≅
            (rawShiftFunctor (k:=k) S hShift (-g)).obj
              ((rawFunctor (k:=k) C S).obj X) := by
        simpa [D.core.shiftFunctor_eq] using
          ((rawFunctorShiftIso (k:=k) S hShift (-g)).app X).symm
      let eRawY :
          (rawFunctor (k:=k) C S).obj ((D.core.F (-g)).obj Y) ≅
            (rawShiftFunctor (k:=k) S hShift (-g)).obj
              ((rawFunctor (k:=k) C S).obj Y) := by
        simpa [D.core.shiftFunctor_eq] using
          ((rawFunctorShiftIso (k:=k) S hShift (-g)).app Y).symm
      let eShiftX :
          (IsSurvivingRaw (k:=k) C S).ι.obj
              ((shiftFunctor (DeletionCategory (k:=k) C S) (-g)).obj
                ⟨⟨X⟩, hX⟩) ≅
            (rawShiftFunctor (k:=k) S hShift (-g)).obj
              ((rawFunctor (k:=k) C S).obj X) := by
        exact ((IsSurvivingRaw (k:=k) C S).ι.commShiftIso (-g)).app
          ⟨⟨X⟩, hX⟩
      let eShiftY :
          (IsSurvivingRaw (k:=k) C S).ι.obj
              ((shiftFunctor (DeletionCategory (k:=k) C S) (-g)).obj
                ⟨⟨Y⟩, hY⟩) ≅
            (rawShiftFunctor (k:=k) S hShift (-g)).obj
              ((rawFunctor (k:=k) C S).obj Y) := by
        exact ((IsSurvivingRaw (k:=k) C S).ι.commShiftIso (-g)).app
          ⟨⟨Y⟩, hY⟩
      have hdel :
          (rawFunctor (k:=k) C S).map ((D.core.F (-g)).map q) ≫
              (eRawY ≪≫ eShiftY.symm).hom =
            (eRawX ≪≫ eShiftX.symm).hom ≫
              (IsSurvivingRaw (k:=k) C S).ι.map
                ((shiftFunctor (DeletionCategory (k:=k) C S) (-g)).map f) := by
        have hraw :=
          Functor.commShiftIso_inv_naturality
            (rawFunctor (k:=k) C S) q (-g)
        have hsurv :=
          Functor.commShiftIso_inv_naturality
            ((IsSurvivingRaw (k:=k) C S).ι) f (-g)
        have hmap :
            (rawShiftFunctor (k:=k) S hShift (-g)).map
                ((rawFunctor (k:=k) C S).map q) =
              (shiftFunctor (RawCategory (k:=k) C S) (-g)).map f.hom := by
          rw [hq]
          rfl
        have hraw' :
            (rawFunctor (k:=k) C S).map ((D.core.F (-g)).map q) ≫ eRawY.hom =
              eRawX.hom ≫
                (rawShiftFunctor (k:=k) S hShift (-g)).map
                  ((rawFunctor (k:=k) C S).map q) := by
          convert hraw using 1 <;>
            first | rfl | simp [eRawX, eRawY, rawShiftFunctor, shiftedRawFunctor,
              rawHasShift, D.core.shiftFunctor_eq]
        have hsurv' :
            (rawShiftFunctor (k:=k) S hShift (-g)).map
                ((rawFunctor (k:=k) C S).map q) ≫ eShiftY.inv =
              eShiftX.inv ≫
                (IsSurvivingRaw (k:=k) C S).ι.map
                  ((shiftFunctor (DeletionCategory (k:=k) C S) (-g)).map f) := by
          rw [hmap]
          exact hsurv
        rw [show (eRawY ≪≫ eShiftY.symm).hom = eRawY.hom ≫ eShiftY.inv by rfl,
          show (eRawX ≪≫ eShiftX.symm).hom = eRawX.hom ≫ eShiftX.inv by rfl,
          ← Category.assoc, hraw', Category.assoc, hsurv', ← Category.assoc]
      change
        ((ideal (k:=k) C S).quotientLift
            ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj
            (module_isKilledBy_of_vanishesOnDeleted (k:=k) C S
              (((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj)
              hshift)).map f.hom ≫ _ = _
      rw [← hq]
      have houter :=
        CategoricalIdeal.HomIdeal.quotientLift_map_functor_map
          (ideal (k:=k) C S)
          ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj
          (module_isKilledBy_of_vanishesOnDeleted (k:=k) C S
            (((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj)
            hshift) q
      rw [houter]
      change
        ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj.map q ≫
            eunderNat.hom.app Y ≫ elinNat.hom.app Y ≫ _ =
          (eunderNat.hom.app X ≫ elinNat.hom.app X ≫ _) ≫
            R.obj.obj.map ((Dstage.core.F (-g)).map f)
      have hcombined :
          (((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj.map q ≫
              eunderNat.hom.app Y) ≫ elinNat.hom.app Y =
            (eunderNat.hom.app X ≫ elinNat.hom.app X) ≫
              (D.core.F (-g) ⋙ M.obj.obj).map q := by
        calc
          _ = (((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj.map q ≫
              eunderNat.hom.app Y) ≫ elinNat.hom.app Y := by simp only [Category.assoc]
          _ = (eunderNat.hom.app X ≫
              ((shiftFunctor (LinearModuleCategory (C:=C) k) g).obj M.obj).obj.map q) ≫
              elinNat.hom.app Y := by rw [eunderNat.hom.naturality q]
          _ = eunderNat.hom.app X ≫
              (((shiftFunctor (LinearModuleCategory (C:=C) k) g).obj M.obj).obj.map q ≫
                elinNat.hom.app Y) := by simp only [Category.assoc]
          _ = eunderNat.hom.app X ≫
              (elinNat.hom.app X ≫ (D.core.F (-g) ⋙ M.obj.obj).map q) := by
            rw [elinNat.hom.naturality q]
          _ = (eunderNat.hom.app X ≫ elinNat.hom.app X) ≫
              (D.core.F (-g) ⋙ M.obj.obj).map q := by simp only [Category.assoc]
      change
        (((((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) g).obj M).obj.obj.map q ≫
            eunderNat.hom.app Y) ≫ elinNat.hom.app Y) ≫ _) = _
      rw [hcombined]
      have hmapcalc := congrArg
        (fun z ↦
          (eunderNat.hom.app X ≫ elinNat.hom.app X) ≫
            ((ideal (k:=k) C S).quotientLift M.obj.obj
            (module_isKilledBy_of_vanishesOnDeleted (k:=k) C S M.obj.obj hM)).map z) hdel
      have hF : Dstage.core.F (-g) =
          shiftFunctor (DeletionCategory (k:=k) C S) (-g) := by
        rfl
      have hmapF : (Dstage.core.F (-g)).map f =
          (shiftFunctor (DeletionCategory (k:=k) C S) (-g)).map f :=
        by
          change (shiftFunctor (DeletionCategory (k:=k) C S) (-g)).map f = _
          rfl
      simp only [CoherentDeckShift.deletionCoherentDeckShift_core_F_eq_shiftFunctor
        (k:=k) D S hS (-g)]
      convert hmapcalc using 1 <;>
        simp [hF, R, finiteDimensionalModuleRestrictionToDeletion,
          linearModuleRestrictionToDeletion, moduleRestrictionToDeletion,
          eRawX, eRawY, eShiftX, eShiftY,
          ObjectProperty.isoMk_hom, ObjectProperty.homMk, Functor.mapIso_hom,
          Iso.trans_hom, Iso.symm_hom,
          eqToHom_refl, eqToHom_trans, Category.assoc]
      all_goals rw [hmapF]
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k:=k)
  letI := isLinearModule_stableUnderShift (k:=k) Dstage.core
  letI := linearModuleCategoryHasShift (k:=k) Dstage.core
  letI := linearModuleCategoryAdditiveShift (R:=k) Dstage.core
  letI := linearModuleCategoryLinearShift (R:=k) Dstage.core
  letI := Dstage.finiteDimensionalModuleCategoryHasShift (k:=k)
  letI := Dstage.finiteDimensionalModuleCategoryAdditiveShift (k:=k) g
  let B := (shiftFunctor (FiniteDimensionalModuleCategory (C:=DeletionCategory (k:=k) C S) k) g).obj R
  let eBfd := Dstage.finiteDimensionalModuleShiftUnderlyingIso (k:=k) R g
  let eBfd' := (IsLinearModule (C := DeletionCategory (k:=k) C S) k).ι.mapIso eBfd
  letI := functorCategoryHasShift (E := ModuleCat.{v} k) Dstage.core
  let ecomm := ((IsLinearModule (C := DeletionCategory (k:=k) C S) k).ι.commShiftIso g).app R.obj
  let eB : ((shiftFunctor (LinearModuleCategory (C := DeletionCategory (k:=k) C S) k) g).obj R.obj).obj ≅ Dstage.core.F (-g) ⋙ R.obj.obj := linearModuleShiftUnderlyingIso (k:=k) Dstage.core R.obj g
  have eBfull :
      ((shiftFunctor (LinearModuleCategory (C := DeletionCategory (k:=k) C S) k) g).obj R.obj).obj ≅
        B.obj.obj := by
    dsimp [B]
    change (IsLinearModule (C := DeletionCategory (k:=k) C S) k).ι.obj
      ((shiftFunctor (LinearModuleCategory (C := DeletionCategory (k:=k) C S) k) g).obj R.obj) ≅
      (IsLinearModule (C := DeletionCategory (k:=k) C S) k).ι.obj
        ((IsFiniteDimensionalModule (C := DeletionCategory (k:=k) C S) k).ι.obj
          ((shiftFunctor (FiniteDimensionalModuleCategory (C := DeletionCategory (k:=k) C S) k) g).obj R))
    exact eBfd'.symm
  have eABlin : A.obj.obj ≅ B.obj.obj := by
    exact eA.trans (eB.symm.trans eBfull)
  have eAB : A ≅ B := by
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact eABlin
  exact ⟨eAB⟩

private noncomputable def finiteDeletionObjectEquivOfSkeletal
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (e : C ≌ D) (hC : Skeletal C) (hD : Skeletal D) : C ≃ D := by
  apply Equiv.ofBijective e.functor.obj
  constructor
  · intro X Y hXY
    apply hC
    exact ⟨e.unitIso.app X ≪≫ e.inverse.mapIso (eqToIso hXY) ≪≫
      (e.unitIso.app Y).symm⟩
  · intro Y
    obtain ⟨X, ⟨hXY⟩⟩ :=
      (Functor.IsEquivalence.essSurj (F := e.functor)).mem_essImage Y
    apply Exists.intro X
    apply hD
    exact ⟨hXY⟩

/- The ambient density is invariant under translating both the module and the
deleted support.  The long local construction is kept here so the averaging
bridge can use one checked theorem rather than duplicate quotient-category
transport. -/
theorem finiteDeletionExtendedLocalDensity_shift_eq
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hC : Skeletal C)
    (hlocalEnd : ∀ X : C, IsLocalRing (End X))
    (S : Set C) (g : G)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift
      (k := k) (Additive.ofMul g)
    let Ebase := shiftEquiv C (Additive.ofMul g)
    let hMshift :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
          (Additive.ofMul g)) M).2 hM
    let Mshift :=
      (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
        (Additive.ofMul g)).obj M
    finiteDeletionExtendedLocalDensity (k := k) C hlocal
      (equivalenceDeletedSet Ebase S) Mshift hMshift =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let Ebase := shiftEquiv C (Additive.ofMul g)
  letI : Ebase.functor.Additive := D.additiveShift (Additive.ofMul g)
  letI : Ebase.functor.Linear k := D.linearShift (k := k) (Additive.ofMul g)
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC S
  let eDel := deletionEquivalence (k := k) Ebase S
  letI : eDel.functor.Additive := by
    change (deletionMapFunctor (k := k) Ebase S).Additive
    infer_instance
  letI : eDel.functor.Linear k := by
    change (deletionMapFunctor (k := k) Ebase S).Linear k
    infer_instance
  let hDelSrc := deletion_skeletal (k := k) C hC hlocalEnd S
  let hDelTgt := deletion_skeletal (k := k) C hC hlocalEnd
    (equivalenceDeletedSet Ebase S)
  let eObj := finiteDeletionObjectEquivOfSkeletal eDel hDelSrc hDelTgt
  let hobj : ∀ X, eDel.functor.obj X = eObj X := by
    intro X
    rfl
  let E := finiteDimensionalModuleCongrEquivalence.{u,v,u,v,v,v}
    (k := k) eDel eObj hobj
  letI : E.functor.Additive :=
    finiteDimensionalModuleCongrEquivalence_functor_additive
      (k := k) eDel eObj hobj
  letI : E.functor.Linear k :=
    finiteDimensionalModuleCongrEquivalence_functor_linear
      (k := k) eDel eObj hobj
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI : (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
      (Additive.ofMul g)).Additive :=
    D.finiteDimensionalModuleCategoryAdditiveShift (k := k) (Additive.ofMul g)
  let Mshift :=
    (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
      (Additive.ofMul g)).obj M
  let hMshift :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
        (Additive.ofMul g)) M).2 hM
  let Rsrc := finiteDimensionalModuleRestrictionToDeletion C S M hvanish
  have hMshiftvanish : ModuleVanishesOnDeleted (k := k) C
      (equivalenceDeletedSet Ebase S) Mshift.obj.obj := by
    intro Y hY
    have hIso : Ebase.inverse.obj Y ≅ g • Y := by
      have hEq : Ebase.inverse = D.core.F (Additive.ofMul g⁻¹) := by
        simp [Ebase, shiftEquiv, shiftEquiv', D.core.shiftFunctor_eq]
      simpa [hEq] using (D.objIso g⁻¹ Y)
    have hY' : g • Y ∈ S := ObjectProperty.prop_of_iso S hIso hY
    exact (hvanish (g • Y) hY').of_iso
      (D.finiteDimensionalModuleShiftEvaluationIso k M g Y)
  let Rtar := finiteDimensionalModuleRestrictionToDeletion C
    (equivalenceDeletedSet Ebase S) Mshift hMshiftvanish
  letI := linearModuleCategoryHasShift (k := k) D.core
  let eunder := D.finiteDimensionalModuleShiftUnderlyingIso
    (k := k) M (Additive.ofMul g)
  let eunderNat : Mshift.obj.obj ≅
      ((shiftFunctor (LinearModuleCategory (C := C) k)
        (Additive.ofMul g)).obj M.obj).obj := by
    exact
      { hom := eunder.hom.hom
        inv := eunder.inv.hom
        hom_inv_id := by
          change eunder.hom.hom ≫ eunder.inv.hom = 𝟙 _
          exact congrArg (fun t => t.hom) eunder.hom_inv_id
        inv_hom_id := by
          change eunder.inv.hom ≫ eunder.hom.hom = 𝟙 _
          exact congrArg (fun t => t.hom) eunder.inv_hom_id }
  let elin := linearModuleShiftUnderlyingIso (k := k) D.core M.obj
    (Additive.ofMul g)
  let elinNat :
      ((shiftFunctor (LinearModuleCategory (C := C) k)
        (Additive.ofMul g)).obj M.obj).obj ≅
        (D.core.F (-Additive.ofMul g) ⋙ M.obj.obj) := by
    exact
      { hom := elin.hom
        inv := elin.inv
        hom_inv_id := by
          change elin.hom ≫ elin.inv = 𝟙 _
          exact elin.hom_inv_id
        inv_hom_id := by
          change elin.inv ≫ elin.hom = 𝟙 _
          exact elin.inv_hom_id }
  let hEq : Ebase.inverse = D.core.F (-Additive.ofMul g) := by
    have hEqE : Ebase.inverse = shiftFunctor C (-Additive.ofMul g) := by
      simp [Ebase, shiftEquiv, shiftEquiv']
    rw [hEqE, D.core.shiftFunctor_eq]
  let hEqM := Functor.isoWhiskerRight (eqToIso hEq) M.obj.obj
  let eRest :
      ((shiftFunctor (LinearModuleCategory (C := C) k)
        (Additive.ofMul g)).obj M.obj).obj ≅
        (Ebase.inverse ⋙ M.obj.obj) := elinNat ≪≫ hEqM.symm
  let eunit := Functor.isoWhiskerRight Ebase.unitIso.symm M.obj.obj
  let eassoc := Functor.associator Ebase.functor Ebase.inverse M.obj.obj
  let eAmbient : (Ebase.functor ⋙ Mshift.obj.obj) ≅ M.obj.obj :=
    Functor.isoWhiskerLeft Ebase.functor eunderNat ≪≫
      Functor.isoWhiskerLeft Ebase.functor eRest ≪≫
      eassoc.symm ≪≫ eunit
  have hR : E.functor.obj Rtar ≅ Rsrc := by
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    change (E.functor.obj Rtar).obj.obj ≅ Rsrc.obj.obj
    refine NatIso.ofComponents (fun X => ?_) ?_
    · change Mshift.obj.obj.obj (eDel.functor.obj X).obj.as ≅
        M.obj.obj.obj X.obj.as
      have hqX : (eDel.functor.obj X).obj.as = Ebase.functor.obj X.obj.as := by
        change Ebase.functor.obj X.obj.as = Ebase.functor.obj X.obj.as
        rfl
      exact (eqToIso (congrArg (fun Z : C => Mshift.obj.obj.obj Z) hqX)).symm ≪≫
        eAmbient.app X.obj.as
    · intro X Y f
      rcases X with ⟨⟨X⟩, hX⟩
      rcases Y with ⟨⟨Y⟩, hY⟩
      obtain ⟨q, hq⟩ := (rawFunctor (k := k) C S).map_surjective f.hom
      change
        ((ideal (k := k) C (equivalenceDeletedSet Ebase S)).quotientLift
            Mshift.obj.obj (module_isKilledBy_of_vanishesOnDeleted (k := k) C
              (equivalenceDeletedSet Ebase S) Mshift.obj.obj hMshiftvanish)).map
              ((eDel.functor.map f).hom) ≫ _ =
          _ ≫ ((ideal (k := k) C S).quotientLift M.obj.obj
            (module_isKilledBy_of_vanishesOnDeleted (k := k) C S
              M.obj.obj hvanish)).map f.hom
      change
        ((ideal (k := k) C (equivalenceDeletedSet Ebase S)).quotientLift
            Mshift.obj.obj (module_isKilledBy_of_vanishesOnDeleted (k := k) C
              (equivalenceDeletedSet Ebase S) Mshift.obj.obj hMshiftvanish)).map
          ((rawDeletionMapFunctor (k := k) Ebase S).map f.hom) ≫ _ = _
      rw [← hq]
      have hraw :
          (rawDeletionMapFunctor (k := k) Ebase S).map
              ((rawFunctor (k := k) C S).map q) =
            (rawFunctor (k := k) C (equivalenceDeletedSet Ebase S)).map
              (Ebase.functor.map q) := by
        rfl
      rw [hraw]
      let hkill : (ideal (k := k) C (equivalenceDeletedSet Ebase S)).IsKilledBy
          Mshift.obj.obj :=
        module_isKilledBy_of_vanishesOnDeleted (k := k) C
          (equivalenceDeletedSet Ebase S) Mshift.obj.obj hMshiftvanish
      have houter :=
        QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.quotientLift_map_functor_map
          (ideal (k := k) C (equivalenceDeletedSet Ebase S)) Mshift.obj.obj
          hkill (Ebase.functor.map q)
      change
        ((ideal (k := k) C (equivalenceDeletedSet Ebase S)).quotientLift
            Mshift.obj.obj hkill).map
          ((rawFunctor (k := k) C (equivalenceDeletedSet Ebase S)).map
            (Ebase.functor.map q)) ≫ _ = _
      rw [houter]
      have hqX : (eDel.functor.obj (⟨⟨X⟩, hX⟩)).obj.as = Ebase.functor.obj X := by
        change Ebase.functor.obj X = Ebase.functor.obj X
        rfl
      have hqY : (eDel.functor.obj (⟨⟨Y⟩, hY⟩)).obj.as = Ebase.functor.obj Y := by
        change Ebase.functor.obj Y = Ebase.functor.obj Y
        rfl
      cases hqX
      cases hqY
      change
        Mshift.obj.obj.map (Ebase.functor.map q) ≫
            (eAmbient.app Y).hom =
          (eAmbient.app X).hom ≫ M.obj.obj.map q
      simpa using eAmbient.hom.naturality q
  have hRtar : Indecomposable Rtar :=
    finiteDimensionalModuleRestrictionToDeletion_indec C
      (equivalenceDeletedSet Ebase S) Mshift hMshift hMshiftvanish
  have hRsrc : Indecomposable Rsrc :=
    finiteDimensionalModuleRestrictionToDeletion_indec C S M hM hvanish
  have htarget := finiteModuleLocalDensity_eq_of_iso
    (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
    ((MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor Rtar).2 hRtar) hRsrc hR
  have htransport := finiteModuleLocalDensity_map_equivalence
    (k := k)
    (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
    (isLocallyRepresentationFinite_deletion (k := k) C
      (equivalenceDeletedSet Ebase S) hlocal)
    E Rtar hRtar
  have hsource : finiteModuleLocalDensity
      (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
      Rsrc (finiteDimensionalModuleRestrictionToDeletion_indec C S M hM hvanish) =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM := by
    simp [Rsrc, finiteDeletionExtendedLocalDensity, hvanish]
  have htarget' : finiteDeletionExtendedLocalDensity (k := k) C hlocal
      (equivalenceDeletedSet Ebase S) Mshift hMshift =
      finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C
          (equivalenceDeletedSet Ebase S) hlocal)
        (finiteDimensionalModuleRestrictionToDeletion C
          (equivalenceDeletedSet Ebase S) Mshift hMshiftvanish)
        hRtar := by
    simp [finiteDeletionExtendedLocalDensity, hMshiftvanish]
  dsimp
  rw [htarget', htransport.symm, htarget, hsource]

/- The same transport has a zero extension when the module does not survive:
vanishing on the translated deletion set is equivalent across the shift. -/
theorem finiteDeletionExtendedLocalDensity_shift_eq_of_not_vanishes
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hC : Skeletal C)
    (hlocalEnd : ∀ X : C, IsLocalRing (End X))
    (S : Set C) (g : G)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hvanish : ¬ ModuleVanishesOnDeleted (k := k) C S M.obj.obj) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift
      (k := k) (Additive.ofMul g)
    let Ebase := shiftEquiv C (Additive.ofMul g)
    let Mshift :=
      (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
        (Additive.ofMul g)).obj M
    let hMshift :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
          (Additive.ofMul g)) M).2 hM
    ¬ ModuleVanishesOnDeleted (k := k) C
      (equivalenceDeletedSet Ebase S) Mshift.obj.obj := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI : (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
      (Additive.ofMul g)).Additive :=
    D.finiteDimensionalModuleCategoryAdditiveShift (k := k) (Additive.ofMul g)
  let Ebase := shiftEquiv C (Additive.ofMul g)
  letI : Ebase.functor.Additive := D.additiveShift (Additive.ofMul g)
  letI : Ebase.functor.Linear k := D.linearShift (k := k) (Additive.ofMul g)
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC S
  let Mshift :=
    (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
      (Additive.ofMul g)).obj M
  let hMshift :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
        (Additive.ofMul g)) M).2 hM
  dsimp
  intro htarget
  apply hvanish
  intro X hX
  let Y := Ebase.functor.obj X
  have hY : Y ∈ equivalenceDeletedSet Ebase S := by
    change Ebase.inverse.obj Y ∈ S
    have hi : Ebase.inverse.obj Y ≅ X := by
      simpa [Y] using (Ebase.unitIso.app X).symm
    exact ObjectProperty.prop_of_iso S hi.symm hX
  have hzeroShift : IsZero (Mshift.obj.obj.obj Y) := htarget Y hY
  have hzeroMoved : IsZero (M.obj.obj.obj (g • Y)) :=
    hzeroShift.of_iso (D.finiteDimensionalModuleShiftEvaluationIso k M g Y).symm
  have hGY : g • Y ≅ X := by
    have hi : Ebase.inverse.obj Y ≅ g • Y := by
      have hEq : Ebase.inverse = D.core.F (Additive.ofMul g⁻¹) := by
        simp [Ebase, shiftEquiv, shiftEquiv', D.core.shiftFunctor_eq]
      simpa [hEq] using (D.objIso g⁻¹ Y)
    exact hi.symm ≪≫ (Ebase.unitIso.app X).symm
  exact hzeroMoved.of_iso (M.obj.obj.mapIso hGY.symm)

/- A convenient total form, with the extended density convention made
explicit. -/
theorem finiteDeletionExtendedLocalDensity_shift_eq_total
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hC : Skeletal C)
    (hlocalEnd : ∀ X : C, IsLocalRing (End X))
    (S : Set C) (g : G)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift
      (k := k) (Additive.ofMul g)
    let Ebase := shiftEquiv C (Additive.ofMul g)
    let Mshift :=
      (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
        (Additive.ofMul g)).obj M
    let hMshift :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
          (Additive.ofMul g)) M).2 hM
    finiteDeletionExtendedLocalDensity (k := k) C hlocal
      (equivalenceDeletedSet Ebase S) Mshift hMshift =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM := by
  classical
  by_cases hvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj
  · exact finiteDeletionExtendedLocalDensity_shift_eq
      (k := k) D hlocal hC hlocalEnd S g M hM hvanish
  · have hnot := finiteDeletionExtendedLocalDensity_shift_eq_of_not_vanishes
      (k := k) D hlocal hC hlocalEnd S g M hM hvanish
    simp [finiteDeletionExtendedLocalDensity, hvanish, hnot]

/- The inverse image of a deletion set under the shift equivalence is the
   corresponding inverse deck translate.  This rewrites the arbitrary-set
   transport above in the pointwise action notation used by the finite
   incidence argument. -/
theorem equivalenceDeletedSet_shift_eq_inv_smul
    (hC : Skeletal C) (S : Set C) (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    equivalenceDeletedSet (shiftEquiv C (Additive.ofMul g)) S = g⁻¹ • S := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  let Ebase := shiftEquiv C (Additive.ofMul g)
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC S
  ext Y
  change Ebase.inverse.obj Y ∈ S ↔ Y ∈ g⁻¹ • S
  have hEq : Ebase.inverse = D.core.F (Additive.ofMul g⁻¹) := by
    simp [Ebase, shiftEquiv, shiftEquiv', D.core.shiftFunctor_eq]
  have hIso : Ebase.inverse.obj Y ≅ g • Y := by
    simpa [hEq] using (D.objIso g⁻¹ Y)
  have hmem : Ebase.inverse.obj Y ∈ S ↔ g • Y ∈ S :=
    ObjectProperty.prop_iff_of_iso S hIso
  rw [hmem]
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp

/- The canonical all-incoming-source support is transported exactly by a deck
  shift.  This is the naturality statement needed to reindex finite deletion
  marginals; the filtered neighborhood support is only an auxiliary finite
  envelope for the locality proof. -/
theorem canonicalIncomingSourceSupport_shift_eq_preimage
    (D : CoherentDeckShift C G)
    [hAdd : ∀ a : Additive G, (D.core.F a).Additive]
    [hLin : ∀ a : Additive G, (D.core.F a).Linear k]
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory (C := C) k) (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k:=k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k:=k)
    canonicalIncomingSourceSupport (k:=k) C hlocal
      ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k)
        (Additive.ofMul g)).obj M) =
      (g • ·) ⁻¹' canonicalIncomingSourceSupport (k:=k) C hlocal M := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k:=k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k:=k)
  let E := shiftEquiv (FiniteDimensionalModuleCategory (C:=C) k)
    (Additive.ofMul g)
  letI : E.functor.Additive :=
    D.finiteDimensionalModuleCategoryAdditiveShift (k:=k) (Additive.ofMul g)
  letI : E.functor.Linear k :=
    D.finiteDimensionalModuleCategoryLinearShift (k:=k) (Additive.ofMul g)
  letI : (shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k)
      (-Additive.ofMul g)).Additive :=
    D.finiteDimensionalModuleCategoryAdditiveShift (k:=k) (-Additive.ofMul g)
  letI : (shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k)
      (-Additive.ofMul g)).Linear k :=
    D.finiteDimensionalModuleCategoryLinearShift (k:=k) (-Additive.ofMul g)
  letI : E.inverse.Additive := by
    simpa [E, shiftEquiv, shiftEquiv']
  letI : E.inverse.Linear k := by
    simpa [E, shiftEquiv, shiftEquiv']
  let Mshift := E.functor.obj M
  have hMshift : Mshift =
      (shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k)
        (Additive.ofMul g)).obj M := rfl
  ext X
  constructor
  · intro hX
    change X ∈ moduleSupport k Mshift.obj.obj ∪ _ at hX
    rcases hX with hX | hX
    · have hs := D.finiteDimensionalModuleSupport_shift_eq_preimage (k:=k) M g
      have hsX := Set.ext_iff.mp hs X
      exact Set.mem_union_left _ (hsX.mp hX)
    · rcases hX with ⟨N, hN, f, hf, hNX⟩
      change N ⟶ Mshift at f
      let N0 := E.inverse.obj N
      have hN0 : Indecomposable N0 :=
        (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
          E.inverse N).2 hN
      let f0 : N0 ⟶ M := E.inverse.map f ≫ E.unitIso.inv.app M
      have hf0 : f0 ≠ 0 := by
        intro hz
        have hz' : E.inverse.map f = 0 := by
          apply (cancel_mono (E.unitIso.inv.app M)).1
          calc
            E.inverse.map f ≫ E.unitIso.inv.app M = f0 := by rfl
            _ = 0 := hz
            _ = 0 ≫ E.unitIso.inv.app M := by simp
        apply hf
        exact (E.inverse.map_eq_zero_iff).mp hz'
      have hNX' : X ∈ moduleSupport k (E.functor.obj N0).obj.obj := by
        exact (mem_moduleSupport_iff_of_iso (E.counitIso.app N) X).mpr hNX
      have hNX'' : X ∈ moduleSupport k
          ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k)
            (Additive.ofMul g)).obj N0).obj.obj := by
        simpa [E, shiftEquiv, shiftEquiv'] using hNX'
      have hs := D.finiteDimensionalModuleSupport_shift_eq_preimage (k:=k) N0 g
      have hsX := Set.ext_iff.mp hs X
      exact Set.mem_union_right _ ⟨N0, hN0, f0, hf0, hsX.mp hNX''⟩
  · intro hX
    change g • X ∈ moduleSupport k M.obj.obj ∪ _ at hX
    rcases hX with hX | hX
    · have hs := D.finiteDimensionalModuleSupport_shift_eq_preimage (k:=k) M g
      have hsX := Set.ext_iff.mp hs X
      exact Set.mem_union_left _ (hsX.mpr hX)
    · rcases hX with ⟨N, hN, f, hf, hNX⟩
      let Nshift := E.functor.obj N
      have hNshift : Indecomposable Nshift :=
        (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
          E.functor N).2 hN
      let fshift : Nshift ⟶ Mshift := E.functor.map f
      have hfshift : fshift ≠ 0 := by
        intro hz
        apply hf
        exact (E.functor.map_eq_zero_iff).mp hz
      have hs := D.finiteDimensionalModuleSupport_shift_eq_preimage (k:=k) N g
      have hsX := Set.ext_iff.mp hs X
      have htmp := hsX.mpr hNX
      have hNX' : X ∈ moduleSupport k Nshift.obj.obj := by
        simpa [Nshift, E, shiftEquiv, shiftEquiv'] using htmp
      exact Set.mem_union_right _ ⟨Nshift, hNshift, fshift, hfshift, hNX'⟩

/- For an action-invariant deleted set, the transported set appearing in the
   shift theorem is definitionally the same set.  This is the form consumed
   by the universal-cover incidence argument. -/
theorem finiteDeletionLocalChangeAt_shift_eq_of_actionInvariant
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hC : Skeletal C)
    (hlocalEnd : ∀ X : C, IsLocalRing (End X))
    (S : Set C) (hS : ActionInvariant (G := G) S) (g : G)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift
      (k := k) (Additive.ofMul g)
    let Ebase := shiftEquiv C (Additive.ofMul g)
    let Mshift :=
      (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
        (Additive.ofMul g)).obj M
    let hMshift :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
          (Additive.ofMul g)) M).2 hM
    finiteDeletionLocalChangeAt (k := k) C hlocal S Mshift hMshift =
      finiteDeletionLocalChangeAt (k := k) C hlocal S M hM := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift
    (k := k) (Additive.ofMul g)
  let Ebase := shiftEquiv C (Additive.ofMul g)
  letI : Ebase.functor.Additive := D.additiveShift (Additive.ofMul g)
  letI : Ebase.functor.Linear k := D.linearShift (k := k) (Additive.ofMul g)
  let Mshift :=
    (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
      (Additive.ofMul g)).obj M
  let hMshift :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
        (Additive.ofMul g)) M).2 hM
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC S
  have hset : equivalenceDeletedSet Ebase S = S := by
    ext Y
    change Ebase.inverse.obj Y ∈ S ↔ Y ∈ S
    have hEq : Ebase.inverse.obj Y ≅ g • Y := by
      have hcore : Ebase.inverse = D.core.F (Additive.ofMul g⁻¹) := by
        simp [Ebase, shiftEquiv, shiftEquiv', D.core.shiftFunctor_eq]
      simpa [hcore] using (D.objIso g⁻¹ Y)
    exact (ObjectProperty.prop_iff_of_iso S hEq).trans
      (hS g Y)
  have hdens := finiteDeletionExtendedLocalDensity_shift_eq_total
    (k := k) D hlocal hC hlocalEnd S g M hM
  have hdens' :
      finiteDeletionExtendedLocalDensity (k := k) C hlocal S Mshift hMshift =
        finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM := by
    dsimp at hdens
    rw [hset] at hdens
    simpa only [Mshift, hMshift] using hdens
  dsimp only [Mshift, hMshift]
  unfold finiteDeletionLocalChangeAt
  rw [finiteModuleLocalDensity_shift_eq (k := k) D hlocal g M hM, hdens']

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
