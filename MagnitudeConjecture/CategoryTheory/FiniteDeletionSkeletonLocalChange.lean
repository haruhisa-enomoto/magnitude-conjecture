import MagnitudeConjecture.CategoryTheory.FiniteSkeletonIntrinsicLocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalDensity

/-!
# Finite-skeleton local change under object deletion

For complete finite indecomposable skeletons before and after deletion,
extension by zero identifies the post-deletion labels with exactly the
ambient labels which vanish on the deleted objects.  Consequently the sum of
the intrinsic pointwise deletion changes is the difference of the two
Auslander--Reiten surpluses.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

namespace FiniteDeletionSkeleton

variable (D : Set C)
variable (S : FiniteDimensionalModuleIndecomposableSkeleton
  (k := k) (C := C))
variable (T : FiniteDimensionalModuleIndecomposableSkeleton
  (k := k) (C := DeletionCategory (k := k) C D))

/-- Labels of the ambient skeleton represented by modules which survive the
deletion. -/
abbrev SurvivingLabel :=
  {i : Fin S.n //
    ModuleVanishesOnDeleted (k := k) C D (S.obj i).obj.obj}

/-- The complete post-deletion skeleton obtained by keeping exactly the
ambient indecomposable representatives which vanish on the deleted objects
and restricting them to the deletion category. -/
noncomputable def restrictionSkeleton :
    FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := DeletionCategory (k := k) C D) := by
  classical
  let e : SurvivingLabel (k := k) D S ≃
      Fin (Fintype.card (SurvivingLabel (k := k) D S)) :=
    Fintype.equivFin (SurvivingLabel (k := k) D S)
  let R : Fin (Fintype.card (SurvivingLabel (k := k) D S)) →
      FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C D) k :=
    fun j ↦ finiteDimensionalModuleRestrictionToDeletion
      (k := k) C D (S.obj (e.symm j).1) (e.symm j).2
  refine
    { n := Fintype.card (SurvivingLabel (k := k) D S)
      obj := R
      indecomposable := fun j ↦
        finiteDimensionalModuleRestrictionToDeletion_indec
          (k := k) C D (S.obj (e.symm j).1)
            (S.indecomposable (e.symm j).1) (e.symm j).2
      skeletal := ?_
      complete := ?_ }
  · intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    apply S.skeletal
    let F := finiteDimensionalModuleExtensionByZero (k := k) C D
    let h := Classical.choice hij
    exact ⟨(finiteDimensionalModuleRestrictionExtensionIso
        (k := k) C D (S.obj (e.symm i).1) (e.symm i).2).symm |>.trans
      ((F.mapIso h).trans
        (finiteDimensionalModuleRestrictionExtensionIso
          (k := k) C D (S.obj (e.symm j).1) (e.symm j).2))⟩
  · intro M hM
    let F := finiteDimensionalModuleExtensionByZero (k := k) C D
    have hFM : Indecomposable (F.obj M) :=
      finiteDimensionalModuleExtensionByZero_indec
        (k := k) C D M hM
    obtain ⟨i, ⟨hFi⟩⟩ := S.complete (F.obj M) hFM
    have hi : ModuleVanishesOnDeleted (k := k) C D (S.obj i).obj.obj := by
      apply moduleVanishesOnDeleted_of_iso (k := k) C D hFi
      intro X hX
      exact moduleExtensionByZero_obj_isZero_of_mem
        (k := k) C D M.obj.obj hX
    let q : SurvivingLabel (k := k) D S := ⟨i, hi⟩
    let j := e q
    refine ⟨j, ⟨?_⟩⟩
    have heq : e.symm j = q := e.symm_apply_apply q
    let hFR : F.obj M ≅
        F.obj (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C D (S.obj i) hi) :=
      hFi.trans
        (finiteDimensionalModuleRestrictionExtensionIso
          (k := k) C D (S.obj i) hi).symm
    let hpre := F.preimageIso hFR
    simpa only [R, j, heq, q] using hpre

/-- The ambient skeleton label representing extension by zero of a
post-deletion skeleton object. -/
noncomputable def survivingRelabel (j : Fin T.n) : Fin S.n :=
  Classical.choose
    (S.complete
      ((finiteDimensionalModuleExtensionByZero (k := k) C D).obj (T.obj j))
      (finiteDimensionalModuleExtensionByZero_indec
        (k := k) C D (T.obj j) (T.indecomposable j)))

/-- The chosen isomorphism underlying the surviving relabelling. -/
noncomputable def survivingRelabelIso (j : Fin T.n) :
    (finiteDimensionalModuleExtensionByZero (k := k) C D).obj (T.obj j) ≅
      S.obj (survivingRelabel (k := k) D S T j) :=
  Classical.choice
    (Classical.choose_spec
      (S.complete
        ((finiteDimensionalModuleExtensionByZero (k := k) C D).obj (T.obj j))
        (finiteDimensionalModuleExtensionByZero_indec
          (k := k) C D (T.obj j) (T.indecomposable j))))

/-- Extension by zero lands in the vanishing part of the ambient skeleton. -/
theorem survivingRelabel_vanishes (j : Fin T.n) :
    ModuleVanishesOnDeleted (k := k) C D
      (S.obj (survivingRelabel (k := k) D S T j)).obj.obj := by
  apply moduleVanishesOnDeleted_of_iso (k := k) C D
    (survivingRelabelIso (k := k) D S T j)
  intro X hX
  exact moduleExtensionByZero_obj_isZero_of_mem
    (k := k) C D (T.obj j).obj.obj hX

/-- Surviving relabelling with its vanishing certificate. -/
noncomputable def survivingRelabelSubtype (j : Fin T.n) :
    SurvivingLabel (k := k) D S :=
  ⟨survivingRelabel (k := k) D S T j,
    survivingRelabel_vanishes (k := k) D S T j⟩

theorem survivingRelabelSubtype_injective :
    Function.Injective (survivingRelabelSubtype (k := k) D S T) := by
  intro i j hij
  apply T.skeletal
  apply Nonempty.intro
  let F := finiteDimensionalModuleExtensionByZero (k := k) C D
  apply F.preimageIso
  exact (survivingRelabelIso (k := k) D S T i).trans
    ((eqToIso (congrArg S.obj (congrArg Subtype.val hij))).trans
      (survivingRelabelIso (k := k) D S T j).symm)

theorem survivingRelabelSubtype_surjective :
    Function.Surjective (survivingRelabelSubtype (k := k) D S T) := by
  intro i
  let R := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C D (S.obj i.1) i.2
  have hR : Indecomposable R :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C D (S.obj i.1) (S.indecomposable i.1) i.2
  obtain ⟨j, ⟨eR⟩⟩ := T.complete R hR
  refine ⟨j, Subtype.ext ?_⟩
  apply S.skeletal
  apply Nonempty.intro
  let F := finiteDimensionalModuleExtensionByZero (k := k) C D
  exact (survivingRelabelIso (k := k) D S T j).symm |>.trans
    ((F.mapIso eR.symm).trans
      (finiteDimensionalModuleRestrictionExtensionIso
        (k := k) C D (S.obj i.1) i.2))

/-- Post-deletion labels are equivalent to the vanishing labels of the
ambient skeleton. -/
noncomputable def survivingRelabelEquiv :
    Fin T.n ≃ SurvivingLabel (k := k) D S :=
  Equiv.ofBijective (survivingRelabelSubtype (k := k) D S T)
    ⟨survivingRelabelSubtype_injective (k := k) D S T,
      survivingRelabelSubtype_surjective (k := k) D S T⟩

/-- At corresponding labels, deletion-extended ambient density is the
intrinsic density of the post-deletion skeleton object. -/
theorem finiteDeletionExtendedLocalDensity_survivingRelabel
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (j : Fin T.n) :
    finiteDeletionExtendedLocalDensity (k := k) C hlocal D
        (S.obj (survivingRelabel (k := k) D S T j))
        (S.indecomposable (survivingRelabel (k := k) D S T j)) =
      finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C D hlocal)
        (T.obj j) (T.indecomposable j) := by
  let i := survivingRelabel (k := k) D S T j
  let hi := survivingRelabel_vanishes (k := k) D S T j
  let R := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C D (S.obj i) hi
  have hR : Indecomposable R :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C D (S.obj i) (S.indecomposable i) hi
  let F := finiteDimensionalModuleExtensionByZero (k := k) C D
  let eR : R ≅ T.obj j := F.preimageIso
    ((finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C D (S.obj i) hi).trans
        (survivingRelabelIso (k := k) D S T j).symm)
  simpa only [finiteDeletionExtendedLocalDensity, dif_pos hi, i, R]
    using finiteModuleLocalDensity_eq_of_iso
      (isLocallyRepresentationFinite_deletion (k := k) C D hlocal)
        hR (T.indecomposable j) eR

/-- Summing the extended density over the ambient skeleton gives the total
intrinsic density of the post-deletion skeleton. -/
theorem sum_finiteDeletionExtendedLocalDensity_eq
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) :
    (∑ i : Fin S.n,
        finiteDeletionExtendedLocalDensity (k := k) C hlocal D
          (S.obj i) (S.indecomposable i)) =
      ∑ j : Fin T.n,
        finiteModuleLocalDensity
          (isLocallyRepresentationFinite_deletion (k := k) C D hlocal)
          (T.obj j) (T.indecomposable j) := by
  classical
  let p : Fin S.n → Prop := fun i ↦
    ModuleVanishesOnDeleted (k := k) C D (S.obj i).obj.obj
  let f : Fin S.n → ℤ := fun i ↦
    finiteDeletionExtendedLocalDensity (k := k) C hlocal D
      (S.obj i) (S.indecomposable i)
  have hzero : ∑ i : {i : Fin S.n // ¬ p i}, f i.1 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact finiteDeletionExtendedLocalDensity_eq_zero_of_not_vanishes
      (k := k) C hlocal D (S.obj i.1) (S.indecomposable i.1) i.2
  have hpartition := Fintype.sum_subtype_add_sum_subtype p f
  have hsurviving :
      (∑ i : {i : Fin S.n // p i}, f i.1) =
        ∑ j : Fin T.n,
          finiteModuleLocalDensity
            (isLocallyRepresentationFinite_deletion (k := k) C D hlocal)
            (T.obj j) (T.indecomposable j) := by
    symm
    exact Fintype.sum_bijective
      (survivingRelabelEquiv (k := k) D S T)
      (survivingRelabelEquiv (k := k) D S T).bijective
      (fun j : Fin T.n ↦
        finiteModuleLocalDensity
          (isLocallyRepresentationFinite_deletion (k := k) C D hlocal)
          (T.obj j) (T.indecomposable j))
      (fun i : {i : Fin S.n // p i} ↦ f i.1)
      (fun j ↦
        (finiteDeletionExtendedLocalDensity_survivingRelabel
          (k := k) D S T hlocal j).symm)
  calc
    ∑ i : Fin S.n,
        finiteDeletionExtendedLocalDensity (k := k) C hlocal D
          (S.obj i) (S.indecomposable i) =
        (∑ i : {i : Fin S.n // p i}, f i.1) +
          ∑ i : {i : Fin S.n // ¬ p i}, f i.1 := hpartition.symm
    _ = ∑ i : {i : Fin S.n // p i}, f i.1 := by rw [hzero, add_zero]
    _ = _ := hsurviving

variable [EnoughProjectives
  (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
variable [EnoughProjectives
  (FiniteDimensionalModuleCategory.{u, v, v, v}
    (C := DeletionCategory (k := k) C D) k)]

/-- The finite sum of intrinsic pointwise deletion changes is exactly the
difference of the before and after Auslander--Reiten surpluses. -/
theorem sum_finiteDeletionLocalChangeAt_eq_surplus_sub
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) :
    (∑ i : Fin S.n,
        finiteDeletionLocalChangeAt (k := k) C hlocal D
          (S.obj i) (S.indecomposable i)) =
      @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            S.toFiniteRightTauCategoryData)
          S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) -
        @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) := by
  classical
  simp only [finiteDeletionLocalChangeAt]
  rw [Finset.sum_sub_distrib,
    S.sum_finiteModuleLocalDensity_eq_surplus hlocal,
    sum_finiteDeletionExtendedLocalDensity_eq (k := k) D S T hlocal,
    T.sum_finiteModuleLocalDensity_eq_surplus
      (isLocallyRepresentationFinite_deletion (k := k) C D hlocal)]

/-- The deletion difference may be stated using the canonical restriction
skeleton obtained directly from the ambient complete skeleton. -/
theorem sum_finiteDeletionLocalChangeAt_eq_restrictionSkeleton_surplus_sub
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) :
    (∑ i : Fin S.n,
        finiteDeletionLocalChangeAt (k := k) C hlocal D
          (S.obj i) (S.indecomposable i)) =
      @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            S.toFiniteRightTauCategoryData)
          S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) -
        @MagnitudeConjecture.ARCount.surplus
          (Fin (restrictionSkeleton (k := k) D S).n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            (restrictionSkeleton (k := k) D S).toFiniteRightTauCategoryData)
          (restrictionSkeleton (k := k) D S).toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) := by
  exact sum_finiteDeletionLocalChangeAt_eq_surplus_sub
    (k := k) D S (restrictionSkeleton (k := k) D S) hlocal

end FiniteDeletionSkeleton

end MagnitudeConjecture.ObjectDeletion
