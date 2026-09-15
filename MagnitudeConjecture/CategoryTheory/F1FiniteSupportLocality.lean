import MagnitudeConjecture.CategoryTheory.IncomingHomLocalDensity
import MagnitudeConjecture.CategoryTheory.F1FiniteSupportEquivariance
import MagnitudeConjecture.CategoryTheory.ObjectDeletionComparison
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.ObjectDeletion
open MagnitudeConjecture.CoveringHom
universe u v
variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
noncomputable def finiteIncomingHomMapNeighborhood
 (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
 (M : FiniteDimensionalModuleCategory.{u,v,v,v} (C:=C) k) :
   CategoryTheory.FiniteIndecomposableSourceNeighborhood M :=
 finiteIncomingHomNeighborhood_restricted (k:=k) C hlocal M (∅ : Set C)
   (by intro X hX f hf Y hY; exact False.elim (by simpa using hY))
theorem finiteIncomingHomMapNeighborhood_exists_map
 (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
 (M : FiniteDimensionalModuleCategory.{u,v,v,v} (C:=C) k)
 (j : Fin (finiteIncomingHomMapNeighborhood (k:=k) hlocal M).n) :
 ∃ f : (finiteIncomingHomMapNeighborhood (k:=k) hlocal M).obj j ⟶ M, f ≠ 0 := by
  classical
  let N := finiteIncomingHomNeighborhood (k:=k) C hlocal M
  let I := {j : Fin N.n // ∃ f : N.obj j ⟶ M, f ≠ 0}
  letI : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  change ∃ f : N.obj (e j).1 ⟶ M, f ≠ 0
  exact (e j).2
noncomputable def finiteIncomingHomMapDependencySupport
 (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
 (M : FiniteDimensionalModuleCategory.{u,v,v,v} (C:=C) k) : Set C :=
 moduleSupport k M.obj.obj ∪
   ⋃ j : Fin (finiteIncomingHomMapNeighborhood (k:=k) hlocal M).n,
    moduleSupport k ((finiteIncomingHomMapNeighborhood (k:=k) hlocal M).obj j).obj.obj
 theorem finiteIncomingHomMapDependencySupport_finite
 (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
 (M : FiniteDimensionalModuleCategory.{u,v,v,v} (C:=C) k) :
 (finiteIncomingHomMapDependencySupport (k:=k) hlocal M).Finite := by
  classical
  exact (finite_moduleSupport k M).union (Set.finite_iUnion fun j =>
    finite_moduleSupport k ((finiteIncomingHomMapNeighborhood (k:=k) hlocal M).obj j))
 theorem finiteIncomingHomMapDependencySupport_endpoint
 (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
 (M : FiniteDimensionalModuleCategory.{u,v,v,v} (C:=C) k) :
 moduleSupport k M.obj.obj ⊆ finiteIncomingHomMapDependencySupport (k:=k) hlocal M := by
  intro X hX; exact Set.mem_union_left _ hX
 theorem finiteIncomingHomMapDependencySupport_neighbor
 (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
 (M : FiniteDimensionalModuleCategory.{u,v,v,v} (C:=C) k)
 (j : Fin (finiteIncomingHomMapNeighborhood (k:=k) hlocal M).n) :
 moduleSupport k ((finiteIncomingHomMapNeighborhood (k:=k) hlocal M).obj j).obj.obj ⊆
   finiteIncomingHomMapDependencySupport (k:=k) hlocal M := by
  intro X hX; exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j,hX⟩)

/- Every member of the filtered neighborhood carries an actual nonzero map to
  the endpoint, so the chosen finite dependency support is contained in the
  canonical all-incoming-source support. -/
theorem finiteIncomingHomMapDependencySupport_subset_canonicalIncomingSourceSupport
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u,v,v,v} (C:=C) k) :
    finiteIncomingHomMapDependencySupport (k:=k) hlocal M ⊆
      canonicalIncomingSourceSupport (k:=k) C hlocal M := by
  intro X hX
  change X ∈ moduleSupport k M.obj.obj ∪ _ at hX
  rcases hX with hX | hX
  · exact Set.mem_union_left _ hX
  · obtain ⟨j, hX⟩ := Set.mem_iUnion.mp hX
    obtain ⟨f, hf⟩ := finiteIncomingHomMapNeighborhood_exists_map
      (k:=k) hlocal M j
    exact Set.mem_union_right _ ⟨_,
      (finiteIncomingHomMapNeighborhood (k:=k) hlocal M).indecomposable j,
      f, hf, hX⟩

 theorem finiteIncomingHomMapDependencySupport_additionalDeleted_disjoint
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S U : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hS : ModuleVanishesOnDeleted (k := k) C S M.obj.obj)
    (hU : Disjoint U (finiteIncomingHomMapDependencySupport (k:=k) hlocal M)) :
    let D := DeletionCategory (k := k) C S
    let F := finiteDimensionalModuleExtensionByZero.{u,v,v,v} (k := k) C S
    let R := finiteDimensionalModuleRestrictionToDeletion (k := k) C S M hS
    let hR := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C S M hM hS
    Disjoint (AdditionalDeleted (k := k) C S U)
      (finiteIncomingHomMapDependencySupport (k := k) (isLocallyRepresentationFinite_deletion (k := k) C S hlocal) R) := by
  dsimp
  let D := DeletionCategory (k := k) C S
  let F := finiteDimensionalModuleExtensionByZero.{u,v,v,v} (k := k) C S
  let hlocalD := isLocallyRepresentationFinite_deletion (k := k) C S hlocal
  let R := finiteDimensionalModuleRestrictionToDeletion C S M hS
  let hR := finiteDimensionalModuleRestrictionToDeletion_indec C S M hM hS
  rw [Set.disjoint_left]
  intro X hX hdep
  change X.obj.as ∈ U at hX
  change X ∈ moduleSupport k (R.obj.obj) ∪
    ⋃ j : Fin (finiteIncomingHomMapNeighborhood (k:=k) hlocalD R).n,
      moduleSupport k ((finiteIncomingHomMapNeighborhood (k:=k) hlocalD R).obj j).obj.obj at hdep
  rcases hdep with hendpoint | hdep
  · have hFR : Nontrivial ((F.obj R).obj.obj.obj X.obj.as) := by
      have hi := moduleExtensionByZeroObjIsoAt (k := k) C S R.obj.obj X
      exact hi.toLinearEquiv.toEquiv.nontrivial_congr.mpr hendpoint
    have hFM : Nontrivial (M.obj.obj.obj X.obj.as) := by
      have hi := (moduleRestrictionExtensionIso (k := k) C S M.obj.obj hS).app X.obj.as
      exact hi.toLinearEquiv.toEquiv.nontrivial_congr.mp hFR
    exact hU.le_bot ⟨hX, finiteIncomingHomMapDependencySupport_endpoint (k:=k) hlocal M hFM⟩
  · obtain ⟨j, hdep⟩ := Set.mem_iUnion.mp hdep
    have hFR : Nontrivial ((F.obj ((finiteIncomingHomMapNeighborhood (k:=k) hlocalD R).obj j)).obj.obj.obj X.obj.as) := by
      have hi := moduleExtensionByZeroObjIsoAt (k := k) C S
        ((finiteIncomingHomMapNeighborhood (k:=k) hlocalD R).obj j).obj.obj X
      exact hi.toLinearEquiv.toEquiv.nontrivial_congr.mpr hdep
    obtain ⟨f, hf⟩ := finiteIncomingHomMapNeighborhood_exists_map (k:=k) hlocalD R j
    let fF := F.map f
    have hfF : fF ≠ 0 := by
      intro hz
      apply hf
      exact (F.map_eq_zero_iff).mp hz
    have hFFindec := finiteDimensionalModuleExtensionByZero_indec
      (k := k) C S ((finiteIncomingHomMapNeighborhood (k:=k) hlocalD R).obj j)
      ((finiteIncomingHomMapNeighborhood (k:=k) hlocalD R).indecomposable j)
    let eFinite := finiteDimensionalModuleRestrictionExtensionIso C S M hS
    let fM : (F.obj ((finiteIncomingHomMapNeighborhood (k:=k) hlocalD R).obj j)) ⟶ M :=
      fF ≫ eFinite.hom
    have hfM : fM ≠ 0 := by
      intro hz
      apply hfF
      rw [← cancel_mono eFinite.hom]
      simpa [fM] using hz
    let N := finiteIncomingHomMapNeighborhood (k:=k) hlocal M
    obtain ⟨j', ⟨e⟩⟩ := N.covers hFFindec fM hfM
    have hNsupport := finiteIncomingHomMapDependencySupport_neighbor (k:=k) hlocal M j'
    have hXsupport : X.obj.as ∈ moduleSupport k (N.obj j').obj.obj := by
      exact (mem_moduleSupport_iff_of_iso e X.obj.as).mpr hFR
    exact hU.le_bot ⟨hX, hNsupport hXsupport⟩
end MagnitudeConjecture.ObjectDeletion

namespace MagnitudeConjecture.ObjectDeletion
open MagnitudeConjecture.CoveringHom
universe u v
variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
 theorem finiteDeletionExtendedLocalDensity_eq_of_union_disjoint_mapDependency
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S U : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hU : Disjoint U (finiteIncomingHomMapDependencySupport (k:=k) hlocal M)) :
    finiteDeletionExtendedLocalDensity (k:=k) C hlocal S M hM =
      finiteDeletionExtendedLocalDensity (k:=k) C hlocal (S ∪ U) M hM := by
  classical
  by_cases hS : ModuleVanishesOnDeleted (k:=k) C S M.obj.obj
  · let D := DeletionCategory (k:=k) C S
    let F := finiteDimensionalModuleExtensionByZero (k:=k) C S
    let hlocalD := isLocallyRepresentationFinite_deletion (k:=k) C S hlocal
    let R := finiteDimensionalModuleRestrictionToDeletion C S M hS
    let hR := finiteDimensionalModuleRestrictionToDeletion_indec C S M hM hS
    let U' := AdditionalDeleted (k:=k) C S U
    have hUdep : Disjoint U' (finiteIncomingHomMapDependencySupport (k:=k) hlocalD R) :=
      finiteIncomingHomMapDependencySupport_additionalDeleted_disjoint (C:=C) (k:=k) hP hlocal S U M hM hS hU
    have hRvanish : ModuleVanishesOnDeleted (k:=k) D U' R.obj.obj := by
      intro X hX
      change X.obj.as ∈ U at hX
      by_contra hnon
      have hnontriv : Nontrivial (R.obj.obj.obj X) :=
        not_subsingleton_iff_nontrivial.mp (fun hsub => hnon (ModuleCat.isZero_iff_subsingleton.mpr hsub))
      have hi := moduleExtensionByZeroObjIsoAt (k:=k) C S R.obj.obj X
      have hFR : Nontrivial ((F.obj R).obj.obj.obj X.obj.as) := hi.toLinearEquiv.toEquiv.nontrivial_congr.mpr hnontriv
      have hFM : Nontrivial (M.obj.obj.obj X.obj.as) :=
        (moduleRestrictionExtensionIso (k:=k) C S M.obj.obj hS).app X.obj.as |>.toLinearEquiv.toEquiv.nontrivial_congr.mp hFR
      exact (hU.le_bot ⟨hX, finiteIncomingHomMapDependencySupport_endpoint (k:=k) hlocal M hFM⟩).elim
    let hPD : ∀ X : D, IsFiniteDimensionalModule (C:=D) k
      (linearCoyonedaLinearModule (k:=k) X) :=
      fun X => deletion_linearCoyoneda_isFiniteDimensional (k:=k) C hP S X
    have hsource : ModuleVanishesOnDeleted (k:=k) D U'
        (finiteModuleMinimalSinkData hlocalD R hR).source.obj.obj := by
      let A := finiteModuleMinimalSinkData hlocalD R hR
      apply moduleVanishesOnDeleted_of_decomposition_summands (k:=k) D U' A.source A.decomposition
      intro i
      obtain ⟨j, ⟨e⟩⟩ := (finiteIncomingHomMapNeighborhood (k:=k) hlocalD R).covers
        (A.decomposition.indecomposable i)
        (A.decomposition.inclusion i ≫ A.map)
        (A.decomposition.inclusion_comp_ne_zero_of_isRightMinimal i A.map A.rightMinimal)
      intro X hX
      by_cases hXN : X ∈ moduleSupport k ((finiteIncomingHomMapNeighborhood (k:=k) hlocalD R).obj j).obj.obj
      · exact (hUdep.le_bot ⟨hX, finiteIncomingHomMapDependencySupport_neighbor (k:=k) hlocalD R j hXN⟩).elim
      · rw [ModuleCat.isZero_iff_subsingleton]
        apply not_nontrivial_iff_subsingleton.mp
        intro hnon
        apply hXN
        exact (mem_moduleSupport_iff_of_iso e X).mpr hnon
    have hrightDensity := finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
      (k:=k) D hPD hlocalD U' R hR hRvanish
        (finiteModuleMinimalSinkData hlocalD R hR).map
        (finiteModuleMinimalSinkData hlocalD R hR).rightAlmostSplit
        (finiteModuleMinimalSinkData hlocalD R hR).rightMinimal
        (finiteModuleMinimalSinkData hlocalD R hR).decomposition hsource
    have hleftDensity : finiteModuleLocalDensity hlocalD R hR =
        finiteModuleLocalDensity hlocalD R hR := rfl
    let hUnion : ModuleVanishesOnDeleted (k:=k) C (S ∪ U) M.obj.obj := by
      intro X hX
      exact hX.elim (hS X) (fun hUX => by
        rw [ModuleCat.isZero_iff_subsingleton]
        apply not_nontrivial_iff_subsingleton.mp
        intro hnon
        apply hU.le_bot ⟨hUX, finiteIncomingHomMapDependencySupport_endpoint (k:=k) hlocal M hnon⟩)
    let hAdditional : ModuleVanishesOnDeleted (k:=k) D U' R.obj.obj := hRvanish
    let Rfull := finiteDimensionalModuleRestrictionToDeletion C (S ∪ U) M hUnion
    let hRfull := finiteDimensionalModuleRestrictionToDeletion_indec C (S ∪ U) M hM hUnion
    let Riter := finiteDimensionalModuleRestrictionToDeletion D U' R hRvanish
    let hRiter := finiteDimensionalModuleRestrictionToDeletion_indec D U' R hR hRvanish
    let a := iteratedLinearModuleRestrictionIso (k:=k) C S U M.obj hUnion hS hAdditional
    let eBase := iteratedDeletionEquivalence (k:=k) C S U
    letI : eBase.functor.Additive := iteratedDeletionEquivalence_functor_additive (k:=k) C S U
    letI : eBase.functor.Linear k := iteratedDeletionEquivalence_functor_linear (k:=k) C S U
    let eObj := iteratedDeletionObjectEquiv (k:=k) C S U
    let hobj : ∀ X, eBase.functor.obj X = eObj X := by
      intro X
      simpa [eBase, eObj] using
        (iteratedDeletionObjectEquiv_apply (k:=k) C S U X)
    let E := finiteDimensionalModuleCongrEquivalence (k:=k) eBase eObj
      hobj
    letI : E.functor.Additive :=
      finiteDimensionalModuleCongrEquivalence_functor_additive
        (k:=k) eBase eObj hobj
    letI : E.functor.Linear k :=
      finiteDimensionalModuleCongrEquivalence_functor_linear
        (k:=k) eBase eObj hobj
    let eIso : E.functor.obj Rfull ≅ Riter := by
      apply ObjectProperty.isoMk
      apply ObjectProperty.isoMk
      change ((finiteDimensionalModuleCongrEquivalence (k:=k) eBase eObj hobj).functor.obj Rfull).obj.obj ≅
        Riter.obj.obj
      rw [finiteDimensionalModuleCongrEquivalence_functor_obj_obj_obj]
      exact a
    have htransport := finiteModuleLocalDensity_map_equivalence
      (k:=k)
      (isLocallyRepresentationFinite_deletion (k:=k) D U' hlocalD)
      (isLocallyRepresentationFinite_deletion (k:=k) C (S ∪ U) hlocal)
      E Rfull hRfull
    have hisoDensity := finiteModuleLocalDensity_eq_of_iso
      (isLocallyRepresentationFinite_deletion (k:=k) D U' hlocalD)
      ((MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.functor Rfull).2 hRfull) hRiter eIso
    have hdens := hrightDensity.symm.trans (hisoDensity.symm.trans htransport)
    simpa only [finiteDeletionExtendedLocalDensity, dif_pos hS, dif_pos hUnion] using hdens
  · have hSU : ¬ ModuleVanishesOnDeleted (k:=k) C (S ∪ U) M.obj.obj := by
      intro h
      apply hS
      intro X hX
      exact h X (Set.mem_union_left _ hX)
    simp [finiteDeletionExtendedLocalDensity, hS, hSU]
end MagnitudeConjecture.ObjectDeletion

namespace MagnitudeConjecture.ObjectDeletion
open MagnitudeConjecture.CoveringHom
universe u v
variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Deletion density only sees the intersection with the finite incoming-map
dependency support of the endpoint.  This is the finite support quotient
locality statement used by the frozen manuscript. -/
theorem finiteDeletionExtendedLocalDensity_eq_of_inter_eq_mapDependency
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S T : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hST : S ∩ finiteIncomingHomMapDependencySupport (k:=k) hlocal M =
      T ∩ finiteIncomingHomMapDependencySupport (k:=k) hlocal M) :
    finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal T M hM := by
  let K := finiteIncomingHomMapDependencySupport (k:=k) hlocal M
  have hS := finiteDeletionExtendedLocalDensity_eq_of_union_disjoint_mapDependency
    (k:=k) hP hlocal (S ∩ K) (S \ K) M hM (Set.disjoint_sdiff_left)
  have hT := finiteDeletionExtendedLocalDensity_eq_of_union_disjoint_mapDependency
    (k:=k) hP hlocal (T ∩ K) (T \ K) M hM (Set.disjoint_sdiff_left)
  have hS' : finiteDeletionExtendedLocalDensity (k := k) C hlocal (S ∩ K) M hM =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM := by
    simpa only [Set.inter_union_diff] using hS
  have hT' : finiteDeletionExtendedLocalDensity (k := k) C hlocal (T ∩ K) M hM =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal T M hM := by
    simpa only [Set.inter_union_diff] using hT
  have hST' : finiteDeletionExtendedLocalDensity (k := k) C hlocal (S ∩ K) M hM =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal (T ∩ K) M hM := by
    rw [show S ∩ K = T ∩ K by simpa [K] using hST]
  exact hS'.symm.trans (hST'.trans hT')

/- The canonical source support is a slightly larger, but shift-natural,
   support envelope. Equality of intersections with it implies equality of
   intersections with the filtered support used by the deletion comparison. -/
theorem finiteDeletionExtendedLocalDensity_eq_of_inter_eq_canonicalIncomingSourceSupport
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S T : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hST : S ∩ canonicalIncomingSourceSupport (k := k) C hlocal M =
      T ∩ canonicalIncomingSourceSupport (k := k) C hlocal M) :
    finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal T M hM := by
  apply finiteDeletionExtendedLocalDensity_eq_of_inter_eq_mapDependency
    (k := k) hP hlocal S T M hM
  ext X
  constructor
  · rintro ⟨hXS, hXK⟩
    have hXcan : X ∈ canonicalIncomingSourceSupport (k := k) C hlocal M :=
      finiteIncomingHomMapDependencySupport_subset_canonicalIncomingSourceSupport
        (k := k) hlocal M hXK
    have hXTcan : X ∈ T ∩ canonicalIncomingSourceSupport
        (k := k) C hlocal M := by
      rw [← hST]
      exact ⟨hXS, hXcan⟩
    exact ⟨hXTcan.1, hXK⟩
  · rintro ⟨hXT, hXK⟩
    have hXcan : X ∈ canonicalIncomingSourceSupport (k := k) C hlocal M :=
      finiteIncomingHomMapDependencySupport_subset_canonicalIncomingSourceSupport
        (k := k) hlocal M hXK
    have hXScan : X ∈ S ∩ canonicalIncomingSourceSupport
        (k := k) C hlocal M := by
      rw [hST]
      exact ⟨hXT, hXcan⟩
    exact ⟨hXScan.1, hXK⟩

theorem finiteDeletionLocalChangeAt_eq_of_inter_eq_canonicalIncomingSourceSupport
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S T : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hST : S ∩ canonicalIncomingSourceSupport (k := k) C hlocal M =
      T ∩ canonicalIncomingSourceSupport (k := k) C hlocal M) :
    finiteDeletionLocalChangeAt (k := k) C hlocal S M hM =
      finiteDeletionLocalChangeAt (k := k) C hlocal T M hM := by
  unfold finiteDeletionLocalChangeAt
  rw [finiteDeletionExtendedLocalDensity_eq_of_inter_eq_canonicalIncomingSourceSupport
    (k := k) hP hlocal S T M hM hST]

/- The intrinsic pre-deletion density is fixed, so the same finite-support
   comparison immediately applies to the pointwise deletion change. -/
theorem finiteDeletionLocalChangeAt_eq_of_inter_eq_mapDependency
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S T : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hST : S ∩ finiteIncomingHomMapDependencySupport (k:=k) hlocal M =
      T ∩ finiteIncomingHomMapDependencySupport (k:=k) hlocal M) :
    finiteDeletionLocalChangeAt (k := k) C hlocal S M hM =
      finiteDeletionLocalChangeAt (k := k) C hlocal T M hM := by
  unfold finiteDeletionLocalChangeAt
  rw [finiteDeletionExtendedLocalDensity_eq_of_inter_eq_mapDependency
    (k:=k) hP hlocal S T M hM hST]

/- A successive deletion is the singleton deletion in the first quotient.
   This is the relative form used when the averaging argument is applied at
   an arbitrary earlier support set. -/
theorem finiteDeletionLocalChangeAt_eq_of_restriction
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C) (x : C) (hx : x ∉ S)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hS : ModuleVanishesOnDeleted (k := k) C S M.obj.obj) :
    finiteDeletionExtendedLocalDensity (k:=k) C hlocal S M hM -
      finiteDeletionExtendedLocalDensity (k:=k) C hlocal (S ∪ {x}) M hM =
    finiteDeletionLocalChangeAt (k:=k)
      (DeletionCategory (k:=k) C S)
      (isLocallyRepresentationFinite_deletion (k:=k) C S hlocal)
      ({survivingObj (k:=k) C S hx} : Set _)
      (finiteDimensionalModuleRestrictionToDeletion C S M hS)
      (finiteDimensionalModuleRestrictionToDeletion_indec C S M hM hS) := by
  classical
  let D := DeletionCategory (k:=k) C S
  let hlocalD := isLocallyRepresentationFinite_deletion (k:=k) C S hlocal
  let R := finiteDimensionalModuleRestrictionToDeletion C S M hS
  let hR := finiteDimensionalModuleRestrictionToDeletion_indec C S M hM hS
  let xS := survivingObj (k:=k) C S hx
  have hSet : ({xS} : Set D) = AdditionalDeleted (k:=k) C S ({x} : Set C) := by
    simpa [xS, D] using (Frozen.survivingSingleton_eq_additionalDeleted_f1 (k:=k) S x hx)
  have hRvanish_of_union
      (hUnion : ModuleVanishesOnDeleted (k:=k) C (S ∪ {x}) M.obj.obj) :
      ModuleVanishesOnDeleted (k:=k) D (AdditionalDeleted (k:=k) C S ({x} : Set C)) R.obj.obj := by
    intro Y hY
    have hY' : Y ∈ ({xS} : Set D) := by rw [hSet]; exact hY
    have hYeq : Y = xS := Set.mem_singleton_iff.mp hY'
    subst Y
    have hzeroM : IsZero (M.obj.obj.obj x) := hUnion x (Set.mem_union_right _ (Set.mem_singleton x))
    have hzeroExt : IsZero (((finiteDimensionalModuleExtensionByZero (k:=k) C S).obj R).obj.obj.obj x) := by
      exact ((moduleRestrictionExtensionIso (k:=k) C S M.obj.obj hS).app x).isZero_iff.mpr hzeroM
    have hzeroExt' : IsZero (((finiteDimensionalModuleExtensionByZero (k:=k) C S).obj R).obj.obj.obj xS.obj.as) := by
      have hraw : xS.obj.as = x := by rfl
      simpa only [hraw] using hzeroExt
    exact (moduleExtensionByZeroObjIsoAt (k:=k) C S R.obj.obj xS).isZero_iff.mp hzeroExt'
  by_cases hUnion : ModuleVanishesOnDeleted (k:=k) C (S ∪ {x}) M.obj.obj
  · let hRfull := finiteDimensionalModuleRestrictionToDeletion_indec C (S ∪ {x}) M hM hUnion
    let Rfull := finiteDimensionalModuleRestrictionToDeletion C (S ∪ {x}) M hUnion
    let hAdditional := hRvanish_of_union hUnion
    let Riter := finiteDimensionalModuleRestrictionToDeletion D (AdditionalDeleted (k:=k) C S ({x} : Set C)) R hAdditional
    let hRiter := finiteDimensionalModuleRestrictionToDeletion_indec D (AdditionalDeleted (k:=k) C S ({x} : Set C)) R hR hAdditional
    let hlocalIter := isLocallyRepresentationFinite_deletion (k:=k) D (AdditionalDeleted (k:=k) C S ({x} : Set C)) hlocalD
    let hUnion' : ModuleVanishesOnDeleted (k:=k) C (S ∪ ({x} : Set C)) M.obj.obj := hUnion
    let a := iteratedLinearModuleRestrictionIso (k:=k) C S ({x} : Set C) M.obj hUnion' hS hAdditional
    let eBase := iteratedDeletionEquivalence (k:=k) C S ({x} : Set C)
    letI : eBase.functor.Additive := iteratedDeletionEquivalence_functor_additive (k:=k) C S ({x} : Set C)
    letI : eBase.functor.Linear k := iteratedDeletionEquivalence_functor_linear (k:=k) C S ({x} : Set C)
    let eObj := iteratedDeletionObjectEquiv (k:=k) C S ({x} : Set C)
    let hobj : ∀ X, eBase.functor.obj X = eObj X := by
      intro X
      simpa [eBase, eObj] using (iteratedDeletionObjectEquiv_apply (k:=k) C S ({x} : Set C) X)
    let E := finiteDimensionalModuleCongrEquivalence (k:=k) eBase eObj hobj
    letI : E.functor.Additive := finiteDimensionalModuleCongrEquivalence_functor_additive (k:=k) eBase eObj hobj
    letI : E.functor.Linear k := finiteDimensionalModuleCongrEquivalence_functor_linear (k:=k) eBase eObj hobj
    let eIso : E.functor.obj Rfull ≅ Riter := by
      apply ObjectProperty.isoMk
      apply ObjectProperty.isoMk
      change ((finiteDimensionalModuleCongrEquivalence (k:=k) eBase eObj hobj).functor.obj Rfull).obj.obj ≅ Riter.obj.obj
      rw [finiteDimensionalModuleCongrEquivalence_functor_obj_obj_obj]
      exact a
    have htransport := finiteModuleLocalDensity_map_equivalence
      (k:=k) (isLocallyRepresentationFinite_deletion (k:=k) D (AdditionalDeleted (k:=k) C S ({x} : Set C)) hlocalD)
      (isLocallyRepresentationFinite_deletion (k:=k) C (S ∪ ({x} : Set C)) hlocal)
      E Rfull hRfull
    have hisoDensity := finiteModuleLocalDensity_eq_of_iso hlocalIter
      ((MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence E.functor Rfull).2 hRfull) hRiter eIso
    have hdensR : finiteModuleLocalDensity
          (isLocallyRepresentationFinite_deletion (k:=k) C (S ∪ ({x} : Set C)) hlocal) Rfull hRfull =
        finiteModuleLocalDensity hlocalIter Riter hRiter := htransport.symm.trans hisoDensity
    have hleft : finiteDeletionExtendedLocalDensity (k:=k) C hlocal (S ∪ {x}) M hM =
        finiteModuleLocalDensity (isLocallyRepresentationFinite_deletion (k:=k) C (S ∪ ({x} : Set C)) hlocal) Rfull hRfull := by
      simp only [finiteDeletionExtendedLocalDensity, dif_pos hUnion]
      rfl
    have hright : finiteDeletionExtendedLocalDensity (k:=k) D hlocalD (AdditionalDeleted (k:=k) C S ({x} : Set C)) R hR =
        finiteModuleLocalDensity hlocalIter Riter hRiter := by
      simp only [finiteDeletionExtendedLocalDensity, dif_pos hAdditional]
      exact finiteModuleLocalDensity_eq_of_iso hlocalIter hRiter hRiter (Iso.refl _)
    have hfirst : finiteDeletionExtendedLocalDensity (k:=k) C hlocal S M hM =
        finiteModuleLocalDensity hlocalD R hR := by
      simp only [finiteDeletionExtendedLocalDensity, dif_pos hS]
      rfl
    unfold finiteDeletionLocalChangeAt
    rw [hSet, hfirst, hleft, hright, hdensR]
  · have hRnot : ¬ ModuleVanishesOnDeleted (k:=k) D (AdditionalDeleted (k:=k) C S ({x} : Set C)) R.obj.obj := by
      intro hRvan
      apply hUnion
      intro Y hY
      by_cases hSY : Y ∈ S
      · exact hS Y hSY
      · rw [ModuleCat.isZero_iff_subsingleton]
        apply not_nontrivial_iff_subsingleton.mp
        intro hnon
        let YS := survivingObj (k:=k) C S hSY
        have hraw : YS.obj.as = Y := by rfl
        have hYin : YS ∈ AdditionalDeleted (k:=k) C S ({x} : Set C) := by
          change YS.obj.as ∈ ({x} : Set C)
          have hYx : Y ∈ ({x} : Set C) := hY.resolve_left hSY
          rw [hraw]
          exact hYx
        have hFM : Nontrivial (M.obj.obj.obj YS.obj.as) := by
          simpa only [hraw] using hnon
        have hFR : Nontrivial (((finiteDimensionalModuleExtensionByZero (k:=k) C S).obj R).obj.obj.obj YS.obj.as) := by
          exact ((moduleRestrictionExtensionIso (k:=k) C S M.obj.obj hS).app YS.obj.as).toLinearEquiv.toEquiv.nontrivial_congr.mpr hFM
        have hnonR : Nontrivial (R.obj.obj.obj YS) := by
          exact (moduleExtensionByZeroObjIsoAt (k:=k) C S R.obj.obj YS).toLinearEquiv.toEquiv.nontrivial_congr.mp hFR
        exact (not_nontrivial_iff_subsingleton.mpr (ModuleCat.isZero_iff_subsingleton.mp (hRvan YS hYin))) hnonR
    have hzeroR : finiteDeletionExtendedLocalDensity (k:=k) D hlocalD
        (AdditionalDeleted (k:=k) C S ({x} : Set C)) R hR = 0 := by
      rw [finiteDeletionExtendedLocalDensity, dif_neg hRnot]
    unfold finiteDeletionLocalChangeAt
    rw [hSet, hzeroR]
    simp only [finiteDeletionExtendedLocalDensity, dif_pos hS, dif_neg hUnion]
end MagnitudeConjecture.ObjectDeletion
