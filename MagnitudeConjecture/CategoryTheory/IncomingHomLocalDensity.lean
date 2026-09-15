import MagnitudeConjecture.CategoryTheory.FiniteDecompositionVanishes
import MagnitudeConjecture.CategoryTheory.LocallyFiniteModuleLocalDensity
import MagnitudeConjecture.CategoryTheory.F1LocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalDensity

/-!
# Incoming-Hom locality of object-deletion density

For an indecomposable endpoint `M`, local representation-finiteness supplies a
finite family representing every indecomposable `Z` with `Hom(Z,M) ≠ 0`.
If `M` and every member of this one-sided incoming neighborhood survive an
object deletion, the minimal sink of `M` survives with all its summands.
Consequently the intrinsic local density at `M` is unchanged.  This is the
locality mechanism used in Section 9 of the frozen manuscript; it uses no
convex window and no residual finite quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom
open MagnitudeConjecture.ObjectDeletion.Frozen

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- The finite incoming-Hom neighborhood chosen from local
representation-finiteness. -/
noncomputable def finiteIncomingHomNeighborhood
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
  finiteIndecomposableSourceNeighborhood_of_locallyRepresentationFinite
    hlocal M

/- A source neighborhood obtained by discarding the irrelevant members of the
  locally finite cover.  Every retained member comes equipped with a nonzero
  map to the endpoint; this is the finite form of the incoming-Hom set used in
  the frozen proof. -/
noncomputable def finiteIncomingHomNeighborhood_restricted
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (D : Set C)
    (hsource : ∀ {X : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := C) k}, Indecomposable X →
      ∀ f : X ⟶ M, f ≠ 0 →
        ModuleVanishesOnDeleted (k := k) C D X.obj.obj) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableSourceNeighborhood M := by
  classical
  let N := finiteIncomingHomNeighborhood (k := k) C hlocal M
  let I := {j : Fin N.n // ∃ f : N.obj j ⟶ M, f ≠ 0}
  letI : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine
    { n := Fintype.card I
      obj := fun i ↦ N.obj (e i).1
      indecomposable := fun i ↦ N.indecomposable (e i).1
      covers := ?_ }
  intro X hX f hf
  obtain ⟨j, ⟨ej⟩⟩ := N.covers hX f hf
  have hej : ej.hom ≫ f ≠ 0 := by
    intro hz
    apply hf
    calc
      f = 𝟙 X ≫ f := by simp
      _ = (ej.inv ≫ ej.hom) ≫ f := by rw [ej.inv_hom_id]
      _ = ej.inv ≫ (ej.hom ≫ f) := by rw [Category.assoc]
      _ = 0 := by rw [hz]; simp
  let q : I := ⟨j, ⟨ej.hom ≫ f, hej⟩⟩
  refine ⟨e.symm q, ?_⟩
  have heq : e (e.symm q) = q := e.apply_symm_apply q
  refine ⟨?_⟩
  simpa only [heq] using ej

theorem finiteIncomingHomNeighborhood_restricted_vanishes
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (D : Set C)
    (hsource : ∀ {X : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := C) k}, Indecomposable X →
      ∀ f : X ⟶ M, f ≠ 0 →
        ModuleVanishesOnDeleted (k := k) C D X.obj.obj) :
    ∀ j, ModuleVanishesOnDeleted (k := k) C D
      ((finiteIncomingHomNeighborhood_restricted (k := k) C hlocal M D
        hsource).obj j).obj.obj := by
  intro j
  let N := finiteIncomingHomNeighborhood (k := k) C hlocal M
  let I := {j : Fin N.n // ∃ f : N.obj j ⟶ M, f ≠ 0}
  letI : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hj : ∃ f : N.obj (e j).1 ⟶ M, f ≠ 0 := (e j).2
  obtain ⟨f, hf⟩ := hj
  exact hsource (N.indecomposable (e j).1) f hf


/-- The endpoint together with the supports of all members of its incoming-Hom
neighborhood. -/
noncomputable def finiteIncomingHomDependencySupport
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) : Set C :=
  moduleSupport k M.obj.obj ∪
    ⋃ j : Fin (finiteIncomingHomNeighborhood (k := k) C hlocal M).n,
      moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj

theorem finiteIncomingHomDependencySupport_finite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    (finiteIncomingHomDependencySupport (k := k) C hlocal M).Finite := by
  classical
  have hM : (moduleSupport k M.obj.obj).Finite := finite_moduleSupport k M
  have hN :
      (⋃ j : Fin (finiteIncomingHomNeighborhood (k := k) C hlocal M).n,
        moduleSupport k
          ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj).Finite := by
    exact Set.finite_iUnion fun j ↦
      finite_moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j)
  simpa only [finiteIncomingHomDependencySupport] using hM.union hN

/- The literal finite support used by the frozen averaging lemma.  Unlike the
  auxiliary chosen neighborhood support above, this set quantifies over all
  indecomposable sources carrying a nonzero map to the endpoint.  It is
  therefore canonical and transports exactly under deck shifts. -/
noncomputable def canonicalIncomingSourceSupport
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) : Set C :=
  moduleSupport k M.obj.obj ∪
    {X : C | ∃ (N : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := C) k) (hN : Indecomposable N),
      ∃ f : N ⟶ M, f ≠ 0 ∧ X ∈ moduleSupport k N.obj.obj}

theorem canonicalIncomingSourceSupport_finite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    (canonicalIncomingSourceSupport (k := k) C hlocal M).Finite := by
  classical
  let N := finiteIncomingHomNeighborhood (k := k) C hlocal M
  let A : Set C := moduleSupport k M.obj.obj
  let B : Set C := ⋃ j : Fin N.n, moduleSupport k (N.obj j).obj.obj
  have hA : A.Finite := finite_moduleSupport k M
  have hB : B.Finite := Set.finite_iUnion fun j => finite_moduleSupport k (N.obj j)
  have hsub : {X : C | ∃ (Q : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := C) k) (hQ : Indecomposable Q),
      ∃ f : Q ⟶ M, f ≠ 0 ∧ X ∈ moduleSupport k Q.obj.obj} ⊆ B := by
    intro X hX
    rcases hX with ⟨Q, hQ, f, hf, hX⟩
    obtain ⟨j, ⟨e⟩⟩ := N.covers hQ f hf
    exact Set.mem_iUnion.mpr ⟨j, (mem_moduleSupport_iff_of_iso e X).mpr hX⟩
  exact hA.union (hB.subset hsub)

/-- Every module in the incoming-Hom neighborhood is supported inside the
dependency support. -/
theorem finiteIncomingHomNeighborhood_support_subset_dependency
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) (j : Fin
      (finiteIncomingHomNeighborhood (k := k) C hlocal M).n) :
    moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj ⊆
      finiteIncomingHomDependencySupport (k := k) C hlocal M := by
  intro X hX
  exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, hX⟩)

/-- The endpoint is supported inside its incoming-Hom dependency support. -/
theorem finiteIncomingHom_endpoint_support_subset_dependency
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    moduleSupport k M.obj.obj ⊆
      finiteIncomingHomDependencySupport (k := k) C hlocal M := by
  intro X hX
  exact Set.mem_union_left _ hX

/-- Deleting outside the incoming-Hom dependency support leaves both the
endpoint and every incoming neighbor alive as ambient modules. -/
theorem finiteIncomingHomDependency_survivors
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    ModuleVanishesOnDeleted (k := k) C
        (finiteIncomingHomDependencySupport (k := k) C hlocal M)ᶜ M.obj.obj ∧
      (∀ j, ModuleVanishesOnDeleted (k := k) C
        (finiteIncomingHomDependencySupport (k := k) C hlocal M)ᶜ
        ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj) := by
  constructor
  · exact moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
      (k := k) C M _
      (finiteIncomingHom_endpoint_support_subset_dependency (k := k) C hlocal M)
  · intro j
    exact moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
      (k := k) C ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j) _
      (finiteIncomingHomNeighborhood_support_subset_dependency
        (k := k) C hlocal M j)

/-- Every summand of a minimal sink source is represented in the chosen
incoming-Hom neighborhood of its endpoint. -/
theorem minimalSink_summand_covered_by_finiteIncomingHomNeighborhood
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) (i : Fin (finiteModuleMinimalSinkData
      hlocal M hM).decomposition.n) :
    ∃ j, Nonempty
      ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j ≅
        (finiteModuleMinimalSinkData hlocal M hM).decomposition.summand i) := by
  let A := finiteModuleMinimalSinkData hlocal M hM
  let N := finiteIncomingHomNeighborhood (k := k) C hlocal M
  exact N.covers (A.decomposition.indecomposable i)
    (A.decomposition.inclusion i ≫ A.map)
    (A.decomposition.inclusion_comp_ne_zero_of_isRightMinimal
      i A.map A.rightMinimal)

/- The minimal-sink source is supported on the same finite dependency set.
  This is the source-side companion to the endpoint and incoming-neighborhood
  support lemmas above; it is useful when a deletion comparison is phrased in
  terms of the whole right-almost-split source. -/
theorem finiteIncomingHom_minimalSinkSource_support_subset_dependency
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) :
    moduleSupport k
        (finiteModuleMinimalSinkData hlocal M hM).source.obj.obj ⊆
      finiteIncomingHomDependencySupport (k := k) C hlocal M := by
  classical
  let A := finiteModuleMinimalSinkData hlocal M hM
  intro X hX
  by_contra hnot
  let E := finiteDimensionalModuleEvaluation (k := k) C X
  have hzeroSummand (i : Fin A.decomposition.n) :
      IsZero (E.obj (A.decomposition.summand i)) := by
    obtain ⟨j, ⟨e⟩⟩ :=
      minimalSink_summand_covered_by_finiteIncomingHomNeighborhood
        (k := k) C hlocal M hM i
    rw [ModuleCat.isZero_iff_subsingleton]
    apply not_nontrivial_iff_subsingleton.mp
    intro hnontrivial
    apply hnot
    have hdep := finiteIncomingHomNeighborhood_support_subset_dependency
      (k := k) C hlocal M j
    exact hdep ((mem_moduleSupport_iff_of_iso e X).mpr hnontrivial)
  have hzeroSum : IsZero (⨁ fun i : Fin A.decomposition.n ↦
      E.obj (A.decomposition.summand i)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro i
    exact (hzeroSummand i).eq_of_tgt _ _
  have hzeroBiproduct : IsZero (E.obj (⨁ A.decomposition.summand)) :=
    by
      letI : E.Additive := by
        dsimp only [E, finiteDimensionalModuleEvaluation]
        infer_instance
      exact hzeroSum.of_iso (E.mapBiproduct A.decomposition.summand)
  have hzeroSource : IsZero (E.obj A.source) :=
    hzeroBiproduct.of_iso (E.mapIso A.decomposition.isoBiproduct)
  have hsourceSubsingleton : Subsingleton (E.obj A.source) :=
    ModuleCat.isZero_iff_subsingleton.mp hzeroSource
  exact (not_nontrivial_iff_subsingleton.mpr hsourceSubsingleton) hX

/- A deletion-set comparison used by the frozen locality statement.  It is
  deliberately stated for an arbitrary module-valued functor: once its object
  support is known to lie in a finite set `K`, vanishing on deleted objects is
  determined by the intersection with `K`. -/
theorem moduleVanishesOnDeleted_iff_of_eq_inter_of_moduleSupport_subset
    (S T K : Set C)
    (M : C ⥤ ModuleCat.{v} k)
    (hM : moduleSupport k M ⊆ K)
    (hinter : S ∩ K = T ∩ K) :
    ModuleVanishesOnDeleted (k := k) C S M ↔
      ModuleVanishesOnDeleted (k := k) C T M := by
  constructor
  · intro hS X hXT
    by_cases hXK : X ∈ K
    · have hXS : X ∈ S ∩ K := by
        rw [hinter]
        exact ⟨hXT, hXK⟩
      exact hS X hXS.1
    · rw [ModuleCat.isZero_iff_subsingleton]
      apply not_nontrivial_iff_subsingleton.mp
      intro hnontrivial
      exact hXK (hM hnontrivial)
  · intro hT X hXS
    by_cases hXK : X ∈ K
    · have hXT : X ∈ T ∩ K := by
        rw [← hinter]
        exact ⟨hXS, hXK⟩
      exact hT X hXT.1
    · rw [ModuleCat.isZero_iff_subsingleton]
      apply not_nontrivial_iff_subsingleton.mp
      intro hnontrivial
      exact hXK (hM hnontrivial)


/-- If the chosen incoming-Hom neighborhood survives a deletion, then the
source of the chosen minimal sink survives it as well. -/
theorem minimalSink_source_vanishes_of_incomingHomNeighborhood_vanishes
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hN : ∀ j, ModuleVanishesOnDeleted (k := k) C S
      ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj) :
    ModuleVanishesOnDeleted (k := k) C S
      (finiteModuleMinimalSinkData hlocal M hM).source.obj.obj := by
  let A := finiteModuleMinimalSinkData hlocal M hM
  apply moduleVanishesOnDeleted_of_decomposition_summands
    (k := k) C S A.source A.decomposition
  intro i
  obtain ⟨j, ⟨e⟩⟩ :=
    minimalSink_summand_covered_by_finiteIncomingHomNeighborhood
      (k := k) C hlocal M hM i
  exact moduleVanishesOnDeleted_of_iso (k := k) C S e (hN j)

/- The finite dependency support gives a useful special case of the
  manuscript's locality statement: if two deletion sets avoid the whole
  dependency support, both restrictions retain the same minimal-sink data and
  hence have the same extended density.  The general dependence-on-the-
  intersection statement is the next comparison needed by the F1 average. -/
theorem finiteDeletionExtendedLocalDensity_eq_of_disjoint_dependency
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S T : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hS : Disjoint S
      (finiteIncomingHomDependencySupport (k := k) C hlocal M))
    (hT : Disjoint T
      (finiteIncomingHomDependencySupport (k := k) C hlocal M)) :
    finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal T M hM := by
  have hsurvive (D : Set C) (hD : Disjoint D
      (finiteIncomingHomDependencySupport (k := k) C hlocal M)) :
      ModuleVanishesOnDeleted (k := k) C D M.obj.obj := by
    intro X hX
    by_cases hXM : X ∈ moduleSupport k M.obj.obj
    · have hdep : X ∈ finiteIncomingHomDependencySupport
          (k := k) C hlocal M :=
        finiteIncomingHom_endpoint_support_subset_dependency
          (k := k) C hlocal M hXM
      exact (hD.le_bot ⟨hX, hdep⟩).elim
    · change ¬ Nontrivial (M.obj.obj.obj X) at hXM
      rw [ModuleCat.isZero_iff_subsingleton]
      exact not_nontrivial_iff_subsingleton.mp hXM
  have hneighbors (D : Set C) (hD : Disjoint D
      (finiteIncomingHomDependencySupport (k := k) C hlocal M)) :
      ∀ j, ModuleVanishesOnDeleted (k := k) C D
        ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj := by
    intro j X hX
    by_cases hXN : X ∈ moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj
    · have hdep : X ∈ finiteIncomingHomDependencySupport
          (k := k) C hlocal M :=
        finiteIncomingHomNeighborhood_support_subset_dependency
          (k := k) C hlocal M j hXN
      exact (hD.le_bot ⟨hX, hdep⟩).elim
    · change ¬ Nontrivial
        (((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj.obj X)
        at hXN
      rw [ModuleCat.isZero_iff_subsingleton]
      exact not_nontrivial_iff_subsingleton.mp hXN
  have hSdensity :=
    finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
      (k := k) C hP hlocal S M hM (hsurvive S hS)
      (finiteModuleMinimalSinkData hlocal M hM).map
      (finiteModuleMinimalSinkData hlocal M hM).rightAlmostSplit
      (finiteModuleMinimalSinkData hlocal M hM).rightMinimal
      (finiteModuleMinimalSinkData hlocal M hM).decomposition
      (minimalSink_source_vanishes_of_incomingHomNeighborhood_vanishes
        (k := k) C hlocal S M hM (hneighbors S hS))
  have hTdensity :=
    finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
      (k := k) C hP hlocal T M hM (hsurvive T hT)
      (finiteModuleMinimalSinkData hlocal M hM).map
      (finiteModuleMinimalSinkData hlocal M hM).rightAlmostSplit
      (finiteModuleMinimalSinkData hlocal M hM).rightMinimal
      (finiteModuleMinimalSinkData hlocal M hM).decomposition
      (minimalSink_source_vanishes_of_incomingHomNeighborhood_vanishes
        (k := k) C hlocal T M hM (hneighbors T hT))
  simp only [finiteDeletionExtendedLocalDensity, dif_pos (hsurvive S hS),
    dif_pos (hsurvive T hT)]
  exact hSdensity.trans hTdensity.symm

/-- The pointwise deletion change vanishes when the deleted set misses the
entire incoming dependency support. -/
theorem finiteDeletionLocalChangeAt_eq_zero_of_disjoint_dependency
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hS : Disjoint S
      (finiteIncomingHomDependencySupport (k := k) C hlocal M)) :
    finiteDeletionLocalChangeAt (k := k) C hlocal S M hM = 0 := by
  have hEq := finiteDeletionExtendedLocalDensity_eq_of_disjoint_dependency
    (k := k) C hP hlocal S (∅ : Set C) M hM hS (by simp)
  have hEmpty : ModuleVanishesOnDeleted (k := k) C (∅ : Set C) M.obj.obj := by
    intro X hX
    exact False.elim (by simpa using hX)
  have hDensity :=
    finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
      (k := k) C hP hlocal (∅ : Set C) M hM hEmpty
      (finiteModuleMinimalSinkData hlocal M hM).map
      (finiteModuleMinimalSinkData hlocal M hM).rightAlmostSplit
      (finiteModuleMinimalSinkData hlocal M hM).rightMinimal
      (finiteModuleMinimalSinkData hlocal M hM).decomposition (by
        intro X hX
        exact False.elim (by simpa using hX))
  rw [finiteDeletionLocalChangeAt, hEq,
    finiteDeletionExtendedLocalDensity, dif_pos hEmpty, hDensity]
  ring

/-- One-sided locality for the manuscript's intrinsic density: deletion does
not change the contribution of a surviving endpoint when every indecomposable
with a nonzero map to it also survives. -/
theorem finiteDeletionLocalChangeAt_eq_zero_of_incomingHomNeighborhood_vanishes
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hMvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj)
    (hN : ∀ j, ModuleVanishesOnDeleted (k := k) C S
      ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj) :
    localChange (k := k) C hlocal S M hM = 0 := by
  let A := finiteModuleMinimalSinkData hlocal M hM
  have hsource : ModuleVanishesOnDeleted (k := k) C S A.source.obj.obj :=
    minimalSink_source_vanishes_of_incomingHomNeighborhood_vanishes
      (k := k) C hlocal S M hM hN
  exact localChange_eq_zero_of_minimalSink_source_vanishes
    (k := k) C hP hlocal S M hM hMvanish A.map A.rightAlmostSplit
      A.rightMinimal A.decomposition hsource

theorem finiteDeletionLocalChangeAt_eq_zero_of_sourceNeighborhood_vanishes
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (N : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableSourceNeighborhood M)
    (hN : ∀ j, ModuleVanishesOnDeleted (k := k) C S
      (N.obj j).obj.obj)
    (hMvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj) :
    localChange (k := k) C hlocal S M hM = 0 := by
  let A := finiteModuleMinimalSinkData hlocal M hM
  have hsource : ModuleVanishesOnDeleted (k := k) C S A.source.obj.obj := by
    apply moduleVanishesOnDeleted_of_decomposition_summands
      (k := k) C S A.source A.decomposition
    intro i
    obtain ⟨j, ⟨e⟩⟩ := N.covers
      (A.decomposition.indecomposable i)
      (A.decomposition.inclusion i ≫ A.map)
      (A.decomposition.inclusion_comp_ne_zero_of_isRightMinimal
        i A.map A.rightMinimal)
    exact moduleVanishesOnDeleted_of_iso (k := k) C S e (hN j)
  exact localChange_eq_zero_of_minimalSink_source_vanishes
    (k := k) C hP hlocal S M hM hMvanish A.map A.rightAlmostSplit
      A.rightMinimal A.decomposition hsource

/- The filtered neighborhood gives the corresponding locality statement from
  the intrinsic condition used in the frozen proof: it is enough to know that
  every nonzero source map into the endpoint survives. -/
theorem finiteDeletionLocalChangeAt_eq_zero_of_incomingSources_vanish
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hMvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj)
    (hsource : ∀ {X : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := C) k}, Indecomposable X →
      ∀ f : X ⟶ M, f ≠ 0 →
        ModuleVanishesOnDeleted (k := k) C S X.obj.obj) :
    localChange (k := k) C hlocal S M hM = 0 := by
  exact finiteDeletionLocalChangeAt_eq_zero_of_sourceNeighborhood_vanishes
    (k := k) C hP hlocal S M hM
      (finiteIncomingHomNeighborhood_restricted (k := k) C hlocal M S hsource)
      (finiteIncomingHomNeighborhood_restricted_vanishes
        (k := k) C hlocal M S hsource) hMvanish


/-- If the distinguished object lies outside the incoming dependency support
of a surviving stage endpoint, deleting that object leaves its local density
unchanged.  The proof transports every nonzero source map through extension by
zero and applies one-sided incoming-source locality in the deletion category. -/
theorem finiteDeletionLocalChangeAt_eq_zero_of_not_mem_dependency_support
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C) (x : C) (hx : x ∉ S)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k)
    (hM : Indecomposable M)
    (hnot : x ∉ finiteIncomingHomDependencySupport (k := k) C hlocal
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj M)) :
    finiteDeletionLocalChangeAt (k := k) (DeletionCategory (k := k) C S)
      (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
      ({survivingObj (k := k) C S hx} : Set _) M hM = 0 := by
  classical
  let D := DeletionCategory (k := k) C S
  let yS := survivingObj (k := k) C S hx
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  let hlocalD := isLocallyRepresentationFinite_deletion (k := k) C S hlocal
  let hFD := ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
    (k := k) C hP S
  have hMvanish : ModuleVanishesOnDeleted (k := k) D ({yS} : Set D) M.obj.obj := by
    intro Y hY
    rw [Set.mem_singleton_iff] at hY
    subst Y
    have hzeroF : IsZero ((F.obj M).obj.obj.obj x) := by
      rw [ModuleCat.isZero_iff_subsingleton]
      apply not_nontrivial_iff_subsingleton.mp
      intro htriv
      apply hnot
      exact finiteIncomingHom_endpoint_support_subset_dependency
        (k := k) C hlocal (F.obj M) htriv
    exact (moduleExtensionByZeroObjIsoAt
      (k := k) C S M.obj.obj yS).isZero_iff.mp hzeroF
  have hsource : ∀ {X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := D) k},
      Indecomposable X → ∀ f : X ⟶ M, f ≠ 0 →
        ModuleVanishesOnDeleted (k := k) D ({yS} : Set D) X.obj.obj := by
    intro X hX f hf
    intro Y hY
    change Y ∈ ({yS} : Set D) at hY
    rw [Set.mem_singleton_iff] at hY
    subst Y
    let fF : F.obj X ⟶ F.obj M := F.map f
    have hfF : fF ≠ 0 := by
      intro hzero
      apply hf
      exact (F.map_eq_zero_iff).mp hzero
    let N := finiteIncomingHomNeighborhood (k := k) C hlocal (F.obj M)
    obtain ⟨j, ⟨e⟩⟩ := N.covers
      (finiteDimensionalModuleExtensionByZero_indec (k := k) C S X hX)
      fF hfF
    have hxN : x ∉ moduleSupport k (N.obj j).obj.obj := by
      intro hxN
      apply hnot
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, hxN⟩)
    have hzeroN : IsZero ((N.obj j).obj.obj.obj x) := by
      rw [ModuleCat.isZero_iff_subsingleton]
      exact not_nontrivial_iff_subsingleton.mp hxN
    have hzeroF : IsZero ((F.obj X).obj.obj.obj x) := by
      have hzeroIso := (mem_moduleSupport_iff_of_iso e x)
      rw [ModuleCat.isZero_iff_subsingleton]
      apply not_nontrivial_iff_subsingleton.mp
      intro htriv
      apply hxN
      exact hzeroIso.mpr htriv
    exact (moduleExtensionByZeroObjIsoAt
      (k := k) C S X.obj.obj yS).isZero_iff.mp hzeroF
  exact finiteDeletionLocalChangeAt_eq_zero_of_incomingSources_vanish
    (k := k) D hFD hlocalD ({yS} : Set D) M hM hMvanish hsource

/-- A nonzero local change witnesses a surviving obstruction in the incoming
Hom data.  The endpoint itself is included via its identity map. -/
theorem exists_nonvanishing_incomingSource_of_localChange_ne_zero
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hchange : localChange (k := k) C hlocal S M hM ≠ 0) :
    ∃ (X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
      Indecomposable X ∧ ∃ f : X ⟶ M, f ≠ 0 ∧
        ¬ ModuleVanishesOnDeleted (k := k) C S X.obj.obj := by
  by_contra hno
  have hsource : ∀ {X : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := C) k}, Indecomposable X →
      ∀ f : X ⟶ M, f ≠ 0 →
        ModuleVanishesOnDeleted (k := k) C S X.obj.obj := by
    intro X hX f hf
    by_contra hnot
    apply hno
    exact ⟨X, hX, f, hf, hnot⟩
  have hMvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj :=
    hsource hM (𝟙 M) (by
      intro hid
      exact hM.1 ((Limits.IsZero.iff_id_eq_zero M).2 hid))
  exact hchange
    (finiteDeletionLocalChangeAt_eq_zero_of_incomingSources_vanish
      (k := k) C hP hlocal S M hM hMvanish hsource)

/- The canonical support is intrinsic to the module isomorphism class.  This
   is used whenever a shifted occurrence is replaced by its chosen family
   representative. -/
theorem canonicalIncomingSourceSupport_eq_of_iso
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    {M N : FiniteDimensionalModuleCategory (C:=C) k} (e : M ≅ N) :
    canonicalIncomingSourceSupport (k:=k) C hlocal M =
      canonicalIncomingSourceSupport (k:=k) C hlocal N := by
  ext X
  constructor
  · intro hX
    change X ∈ moduleSupport k M.obj.obj ∪ _ at hX
    rcases hX with hX | hX
    · exact Set.mem_union_left _ ((mem_moduleSupport_iff_of_iso e X).mp hX)
    · rcases hX with ⟨Q, hQ, f, hf, hQX⟩
      apply Set.mem_union_right
      change ∃ (Q : FiniteDimensionalModuleCategory (C:=C) k) (hQ : Indecomposable Q),
        ∃ f : Q ⟶ N, f ≠ 0 ∧ X ∈ moduleSupport k Q.obj.obj
      refine ⟨Q, hQ, ?_⟩
      refine ⟨f ≫ e.hom, ?_, hQX⟩
      intro hz
      apply hf
      apply (cancel_mono e.hom).1
      simpa [hz]
  · intro hX
    change X ∈ moduleSupport k N.obj.obj ∪ _ at hX
    rcases hX with hX | hX
    · exact Set.mem_union_left _ ((mem_moduleSupport_iff_of_iso e X).mpr hX)
    · rcases hX with ⟨Q, hQ, f, hf, hQX⟩
      apply Set.mem_union_right
      change ∃ (Q : FiniteDimensionalModuleCategory (C:=C) k) (hQ : Indecomposable Q),
        ∃ f : Q ⟶ M, f ≠ 0 ∧ X ∈ moduleSupport k Q.obj.obj
      refine ⟨Q, hQ, ?_⟩
      refine ⟨f ≫ e.inv, ?_, hQX⟩
      intro hz
      apply hf
      apply (cancel_mono e.inv).1
      simpa [hz]

end MagnitudeConjecture.ObjectDeletion
