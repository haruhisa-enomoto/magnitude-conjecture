import MagnitudeConjecture.CategoryTheory.F1FiniteOrbitSourceRepresentatives
import MagnitudeConjecture.CategoryTheory.F1FiniteSupportShiftDeletion
import MagnitudeConjecture.CategoryTheory.F1FiniteSupportLocalChange
import MagnitudeConjecture.Combinatorics.F1FiniteDeletionAverage
import MagnitudeConjecture.CategoryTheory.F1FiniteSupportLocality
import MagnitudeConjecture.CategoryTheory.FiniteModuleControlWindowEquivariance
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageControlWindow
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped Pointwise
namespace MagnitudeConjecture.StandardCovering
open MagnitudeConjecture.CoveringHom
open MagnitudeConjecture.CoveringHom.CoherentDeckShift
open MagnitudeConjecture.ObjectDeletion
open MagnitudeConjecture.ObjectDeletion.Frozen
open MagnitudeConjecture.DeletionOrderAverage
universe u v
variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

noncomputable def isoClassFamily (W : FiniteIndecomposableModuleFamily (k:=k) (C:=C)) :
    FiniteIndecomposableModuleFamily (k:=k) (C:=C) := by
  let e : Fin (Fintype.card W.IsoClass) ≃ W.IsoClass := (Fintype.equivFin _).symm
  let n := Fintype.card (W.IsoClass)
  refine
    { n := n
      obj := fun j => W.obj (Quotient.out (e j))
      indecomposable := fun j => W.indecomposable (Quotient.out (e j)) }

 theorem isoClassFamily_mem (W : FiniteIndecomposableModuleFamily (k:=k) (C:=C))
    (i : Fin (isoClassFamily W).n) :
    (isoClassFamily W).obj i ∈ W.isoClosure := by
  refine ⟨Quotient.out ((Fintype.equivFin W.IsoClass).symm i), ?_⟩
  exact ⟨Iso.refl _⟩

 theorem isoClassFamily_pairwise (W : FiniteIndecomposableModuleFamily (k:=k) (C:=C))
    {i j : Fin (isoClassFamily W).n}
    (h : Nonempty ((isoClassFamily W).obj i ≅ (isoClassFamily W).obj j)) : i = j := by
  have hij : ((Fintype.equivFin W.IsoClass).symm i) =
      ((Fintype.equivFin W.IsoClass).symm j) := by
    rw [← Quotient.out_eq ((Fintype.equivFin W.IsoClass).symm i),
      ← Quotient.out_eq ((Fintype.equivFin W.IsoClass).symm j)]
    apply Quotient.sound
    obtain ⟨e⟩ := h
    exact ⟨e⟩
  exact (Fintype.equivFin W.IsoClass).symm.injective hij

 theorem isoClassFamily_isoClosure_eq (W : FiniteIndecomposableModuleFamily (k:=k) (C:=C)) :
    (isoClassFamily W).isoClosure = W.isoClosure := by
  apply Set.Subset.antisymm
  · intro M hM
    obtain ⟨i, ⟨e⟩⟩ := hM
    obtain ⟨j, ⟨ej⟩⟩ := isoClassFamily_mem W i
    exact ⟨j, ⟨ej.trans e⟩⟩
  · intro M hM
    obtain ⟨i, ⟨e⟩⟩ := hM
    let q : W.IsoClass := Quotient.mk W.isoSetoid i
    let j := (Fintype.equivFin W.IsoClass) q
    refine ⟨j, ?_⟩
    change Nonempty (W.obj (Quotient.out ((Fintype.equivFin W.IsoClass).symm j)) ≅ M)
    rw [show (Fintype.equivFin W.IsoClass).symm j = q by simp [j]]
    have hrel : W.obj (Quotient.out q) ≅ W.obj i :=
      Classical.choice (Quotient.exact (Quotient.out_eq q))
    exact ⟨hrel.trans e⟩


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

/- The empty deletion category is canonically equivalent to the ambient
   category.  This adapter identifies the extended density at the empty
   support with the intrinsic density, which is the first endpoint of F1's
   telescoping average. -/
theorem finiteDeletionExtendedLocalDensity_empty_eq_finiteModuleLocalDensity
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory (C := C) k)
    (hM : Indecomposable M) :
    finiteDeletionExtendedLocalDensity (k := k) C hlocal ∅ M hM =
      finiteModuleLocalDensity hlocal M hM := by
  classical
  let E0 := emptyDeletionEquivalence (k := k) C
  letI : E0.functor.Additive := by
    change (emptyDeletionFunctor (k := k) C).Additive
    infer_instance
  letI : E0.functor.Linear k := by
    change (emptyDeletionFunctor (k := k) C).Linear k
    infer_instance
  let eobj : C ≃ DeletionCategory (k := k) C ∅ := by
    apply Equiv.ofBijective E0.functor.obj
    constructor
    · intro X Y hXY
      change (emptyDeletionFunctor (k := k) C).obj X =
        (emptyDeletionFunctor (k := k) C).obj Y at hXY
      have hxy := congrArg
        (fun Z : DeletionCategory (k := k) C ∅ ↦ Z.obj.as) hXY
      exact hxy
    · intro Y
      refine ⟨Y.obj.as, ?_⟩
      apply ObjectProperty.FullSubcategory.ext
      apply CategoryTheory.Quotient.ext
      rfl
  let hobj : ∀ X, E0.functor.obj X = eobj X := by
    intro X
    rfl
  let E := finiteDimensionalModuleCongrEquivalence
    (k := k) E0 eobj hobj
  letI : E.functor.Additive := by
    dsimp [E]
    infer_instance
  letI : E.functor.Linear k := by
    dsimp [E]
    infer_instance
  have hvanish : ModuleVanishesOnDeleted (k := k) C ∅ M.obj.obj := by
    intro X hX
    exact False.elim hX
  let R := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C ∅ M hvanish
  have hR : Indecomposable R :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C ∅ M hM hvanish
  have hDensity := finiteModuleLocalDensity_map_equivalence
    (k := k) hlocal
    (isLocallyRepresentationFinite_deletion (k := k) C ∅ hlocal)
    E R hR
  have hIso : E.functor.obj R ≅ M := by
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    letI : (E.functor.obj R).obj.obj.Additive := inferInstance
    letI : M.obj.obj.Additive := inferInstance
    exact NatIso.ofComponents (fun X ↦ by
      rw [finiteDimensionalModuleCongrEquivalence_functor_obj_obj_obj]
      change (E0.functor ⋙ R.obj.obj).obj X ≅ M.obj.obj.obj X
      exact Iso.refl _) (by
      intro X Y f
      rfl)
  have hER : Indecomposable (E.functor.obj R) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso hIso).2 hM
  have hAmbient : finiteModuleLocalDensity hlocal (E.functor.obj R) hER =
      finiteModuleLocalDensity hlocal M hM :=
    finiteModuleLocalDensity_eq_of_iso hlocal hER hM hIso
  rw [finiteDeletionExtendedLocalDensity, dif_pos hvanish]
  exact hDensity.symm.trans hAmbient



set_option maxHeartbeats 4000000 in
 theorem finiteSupportOrbitAverage_nonnegative_point_frozen
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocalEnd : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hDir : HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C))
    (x : C) (S : Finset C) (hxS : x ∉ S) :
    (0 ≤ ∑ j : Fin
          (isoClassFamily ((finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 2)).n,
        ((finiteDeletionExtendedLocalDensity (k:=k) C hrep (S : Set C)
          ((isoClassFamily ((finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 2)).obj j)
          ((isoClassFamily ((finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 2)).indecomposable j) : ℚ) -
        (finiteDeletionExtendedLocalDensity (k:=k) C hrep (insert x (S : Set C))
          ((isoClassFamily ((finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 2)).obj j)
          ((isoClassFamily ((finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 2)).indecomposable j) : ℚ))) := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  let Core := (finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 2
  let V := isoClassFamily (k:=k) Core
  let Sset : Set C := (S : Set C)
  let Ddel := DeletionCategory (k:=k) C Sset
  let hlocalD := isLocallyRepresentationFinite_deletion (k:=k) C Sset hrep
  let hxD : x ∉ Sset := by simpa [Sset] using hxS
  let xD : Ddel := survivingObj (k:=k) C Sset hxD
  let pV : Fin V.n → Prop := fun j =>
    ModuleVanishesOnDeleted (k:=k) C Sset (V.obj j).obj.obj
  let efV : {j : Fin V.n // pV j} ≃ Fin (Fintype.card {j : Fin V.n // pV j}) :=
    Fintype.equivFin _
  let W : FiniteIndecomposableModuleFamily (k:=k) (C:=Ddel) :=
    { n := Fintype.card {j : Fin V.n // pV j}
      obj := fun q => finiteDimensionalModuleRestrictionToDeletion
        (k:=k) C Sset (V.obj (efV.symm q).1) (efV.symm q).2
      indecomposable := fun q => finiteDimensionalModuleRestrictionToDeletion_indec
        (k:=k) C Sset (V.obj (efV.symm q).1)
          (V.indecomposable (efV.symm q).1) (efV.symm q).2 }
  have hcoreD :
      ((finiteFiberControlSeed hlocalD xD).iterateHomNeighborhood hlocalD 2).isoClosure ⊆
        W.isoClosure := by
    intro M hM
    obtain ⟨i, ⟨eM⟩⟩ := hM
    have hMi : Indecomposable M :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eM).1
        (((finiteFiberControlSeed hlocalD xD).iterateHomNeighborhood
          hlocalD 2).indecomposable i)
    have hExtCore :=
      MagnitudeConjecture.ObjectDeletion.iterateHomNeighborhood_extensionByZero_mem
        (k:=k) C hrep x Sset hxD 2 M hMi
          (by exact ⟨i, ⟨eM⟩⟩)
    have hExtCore' : (finiteDimensionalModuleExtensionByZero
        (k:=k) C Sset).obj M ∈ Core.isoClosure := hExtCore
    have hExtCoreV : (finiteDimensionalModuleExtensionByZero
        (k:=k) C Sset).obj M ∈ V.isoClosure := by
      rw [isoClassFamily_isoClosure_eq (k:=k) Core]
      exact hExtCore'
    obtain ⟨j, ⟨eV⟩⟩ := hExtCoreV
    have hExtVan : ModuleVanishesOnDeleted (k:=k) C Sset
        ((finiteDimensionalModuleExtensionByZero (k:=k) C Sset).obj M).obj.obj := by
      intro Y hY
      exact moduleExtensionByZero_obj_isZero_of_mem (k:=k) C Sset M.obj.obj hY
    have hpj : pV j := moduleVanishesOnDeleted_of_iso
      (k:=k) C Sset eV.symm hExtVan
    let q : Fin W.n := efV ⟨j, hpj⟩
    refine ⟨q, ?_⟩
    change Nonempty (W.obj q ≅ M)
    let eExtV := finiteDimensionalModuleRestrictionExtensionIso
      (k:=k) C Sset (V.obj j) hpj
    have eExt : (finiteDimensionalModuleExtensionByZero
        (k:=k) C Sset).obj (W.obj q) ≅
        (finiteDimensionalModuleExtensionByZero (k:=k) C Sset).obj M := by
      simpa [W, q, efV] using eExtV.trans eV
    exact ⟨(finiteDimensionalModuleExtensionByZero
      (k:=k) C Sset).preimageIso eExt⟩
  have hWpair : ∀ {i j : Fin W.n},
      Nonempty (W.obj i ≅ W.obj j) → i = j := by
    intro i j hij
    let qi := efV.symm i
    let qj := efV.symm j
    let Fext := finiteDimensionalModuleExtensionByZero (k:=k) C Sset
    let ei := finiteDimensionalModuleRestrictionExtensionIso
      (k:=k) C Sset (V.obj qi.1) qi.2
    let ej := finiteDimensionalModuleRestrictionExtensionIso
      (k:=k) C Sset (V.obj qj.1) qj.2
    have eAmb : V.obj qi.1 ≅ V.obj qj.1 := by
      exact ei.symm.trans ((Fext.mapIso (Classical.choice hij)).trans ej)
    have hq : qi.1 = qj.1 := isoClassFamily_pairwise (k:=k) Core ⟨eAmb⟩
    simpa [qi, qj] using congrArg efV (Subtype.ext hq)
  let wclass : W.IsoClass → Fin W.n := Quotient.lift id (by
    intro i j hij
    obtain ⟨e⟩ := hij
    exact hWpair ⟨e⟩)
  have hwclass_bij : Function.Bijective wclass := by
    constructor
    · intro q r hqr
      induction q using Quotient.inductionOn with
      | _ i =>
        induction r using Quotient.inductionOn with
        | _ j =>
          apply Quotient.sound
          change i = j at hqr
          exact ⟨eqToIso (congrArg W.obj hqr)⟩
    · intro i
      refine ⟨Quotient.mk W.isoSetoid i, ?_⟩
      rfl
  have hsumW :
      finiteDeletionLocalChangeSum (k:=k) Ddel hlocalD ({xD} : Set Ddel) W =
        ∑ i : Fin W.n, finiteDeletionLocalChangeAt (k:=k) Ddel hlocalD
          ({xD} : Set Ddel) (W.obj i) (W.indecomposable i) := by
    unfold finiteDeletionLocalChangeSum
    apply Fintype.sum_equiv (Equiv.ofBijective wclass hwclass_bij)
      (fun q : W.IsoClass => finiteDeletionLocalChangeOnIsoClass
        (k:=k) Ddel hlocalD ({xD} : Set Ddel) W q)
      (fun i : Fin W.n => finiteDeletionLocalChangeAt (k:=k) Ddel hlocalD
        ({xD} : Set Ddel) (W.obj i) (W.indecomposable i))
    intro q
    induction q using Quotient.inductionOn with
    | _ i => rfl
  let hPdel := deletion_linearCoyoneda_isFiniteDimensional (k:=k) C hP Sset
  let hRingdel := deletion_end_isLocalRing (k:=k) C hC hlocalEnd Sset
  let hCdel := deletion_skeletal (k:=k) C hC hlocalEnd Sset
  let hDirDel := hasAcyclicFiniteModuleNonzeroNonisomorphisms_deletion
    (k:=k) (C:=C) Sset hDir
  have hnonW := MagnitudeConjecture.ObjectDeletion.Frozen.finiteFamily_localChangeSum_nonnegative_f1
    (k:=k) hPdel hlocalD hRingdel hCdel hDirDel xD W hcoreD
  have hnonW' : 0 ≤ ∑ i : Fin W.n,
      finiteDeletionLocalChangeAt (k:=k) Ddel hlocalD ({xD} : Set Ddel)
        (W.obj i) (W.indecomposable i) := by
    rw [← hsumW]
    exact hnonW
  let dV : Fin V.n → ℚ := fun j ↦
    (finiteDeletionExtendedLocalDensity (k:=k) C hrep Sset
      (V.obj j) (V.indecomposable j) : ℚ) -
    (finiteDeletionExtendedLocalDensity (k:=k) C hrep (insert x Sset)
      (V.obj j) (V.indecomposable j) : ℚ)
  let dW : Fin W.n → ℚ := fun i ↦
    (finiteDeletionLocalChangeAt (k:=k) Ddel hlocalD ({xD} : Set Ddel)
      (W.obj i) (W.indecomposable i) : ℚ)
  have hchange_q : ∀ q : {j : Fin V.n // pV j},
      dV q.1 = dW (efV q) := by
    intro q
    have h := finiteDeletionLocalChangeAt_eq_of_restriction
      (k:=k) hrep Sset x hxD (V.obj q.1) (V.indecomposable q.1) q.2
    have hSet : Sset ∪ ({x} : Set C) = insert x Sset := by
      ext Y
      simp [Set.mem_insert_iff, or_comm]
    rw [hSet] at h
    have h' := congrArg (fun z : ℤ => (z : ℚ)) h
    simpa [dV, dW, W, efV, xD] using h'
  have hzeroV : ∀ j : {j : Fin V.n // ¬ pV j}, dV j.1 = 0 := by
    intro j
    have hnotIns : ¬ ModuleVanishesOnDeleted (k:=k) C (insert x Sset)
        (V.obj j.1).obj.obj := by
      intro hIns
      apply j.2
      intro Y hY
      exact hIns Y (Set.mem_insert_iff.mpr (Or.inr hY))
    have hSzero := finiteDeletionExtendedLocalDensity_eq_zero_of_not_vanishes
      (k:=k) C hrep Sset (V.obj j.1) (V.indecomposable j.1) j.2
    have hInszero := finiteDeletionExtendedLocalDensity_eq_zero_of_not_vanishes
      (k:=k) C hrep (insert x Sset) (V.obj j.1) (V.indecomposable j.1) hnotIns
    dsimp [dV]
    rw [hSzero, hInszero]
    norm_num
  have hsumV_subtype :
      (∑ j : Fin V.n, dV j) =
        ∑ q : {j : Fin V.n // pV j}, dV q.1 := by
    have hpart := Fintype.sum_subtype_add_sum_subtype pV dV
    have hzero : ∑ j : {j : Fin V.n // ¬ pV j}, dV j.1 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact hzeroV j
    rw [← hpart, hzero, add_zero]
  have hsumV_W :
      (∑ q : {j : Fin V.n // pV j}, dV q.1) =
        ∑ i : Fin W.n, dW i := by
    exact Fintype.sum_equiv efV (fun q : {j : Fin V.n // pV j} => dV q.1) dW hchange_q
  change 0 ≤ ∑ j : Fin V.n, dV j
  rw [hsumV_subtype, hsumV_W]
  have hnonWq : (0 : ℚ) ≤ ∑ i : Fin W.n,
      (finiteDeletionLocalChangeAt (k:=k) Ddel hlocalD ({xD} : Set Ddel)
        (W.obj i) (W.indecomposable i) : ℚ) := by
    exact_mod_cast hnonW'
  simpa [dW] using hnonWq


set_option maxHeartbeats 4000000 in
 theorem finiteSupportOrbitAverage_nonnegative_frozen
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocalEnd : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hDir : HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C))
    (x : C)
    : (0 ≤
      ∑ i : Fin
          (finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).n,
        ((finiteModuleLocalDensity hrep
          ((finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).obj i)
          ((finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).indecomposable i) : ℚ) -
        (finiteDeletionExtendedLocalDensity (k:=k) C hrep (MulAction.orbit G x)
          ((finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).obj i)
          ((finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).indecomposable i) : ℚ)) ∧
      ((∑ i : Fin
          (finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).n,
        ((finiteModuleLocalDensity hrep
          ((finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).obj i)
          ((finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).indecomposable i) : ℚ) -
        (finiteDeletionExtendedLocalDensity (k:=k) C hrep (MulAction.orbit G x)
          ((finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).obj i)
          ((finiteOrbitSourceRepresentativeFamily (k:=k) D hP hI hlocalEnd hfree hrep).indecomposable i) : ℚ)) = 0 →
        finiteDeletionLocalChangeSum (k:=k) C hrep ({x} : Set C)
          ((finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 2) = 0))) := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  let F := CoherentDeckShift.finiteOrbitSourceRepresentativeFamily
    (k := k) D hP hI hlocalEnd hfree hrep
  let U := MulAction.orbit G x
  have hUG : ActionInvariant (G := G) U := by
    intro g Y
    rw [← MulAction.orbit_eq_iff, ← MulAction.orbit_eq_iff,
      MulAction.orbit_smul]
  let Kset : Fin F.n → Set C := fun i ↦
    canonicalIncomingSourceSupport (k:=k) C hrep (F.obj i) ∩ U
  have hKset : ∀ i, (Kset i).Finite := by
    intro i
    exact (canonicalIncomingSourceSupport_finite (k:=k) C hrep (F.obj i)).subset
      Set.inter_subset_left
  let K : Fin F.n → Finset C := fun i ↦ (hKset i).toFinset
  let Core := (finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 2
  let V := isoClassFamily (k:=k) Core
  let A := Σ i : {i : Fin F.n // i ∈ (Finset.univ : Finset (Fin F.n))},
    {y : C // y ∈ K i.1}
  have hOrbit (p : A) : p.2.1 ∈ U := by
    exact ((hKset p.1.1).mem_toFinset.mp p.2.2).2
  let gOf : A → G := fun p => Classical.choose (by
    change ∃ g : G, g • x = p.2.1
    exact hOrbit p)
  have hgOf (p : A) : gOf p • x = p.2.1 :=
    Classical.choose_spec (by
      change ∃ g : G, g • x = p.2.1
      exact hOrbit p)
  let Z (p : A) : FiniteDimensionalModuleCategory (C:=C) k :=
    (shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k)
      (Additive.ofMul (gOf p))).obj (F.obj p.1.1)
  have hZind (p : A) : Indecomposable (Z p) := by
    exact (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k)
        (Additive.ofMul (gOf p))) (F.obj p.1.1)).2 (F.indecomposable p.1.1)
  have hZx (p : A) : p.2.1 ∈ canonicalIncomingSourceSupport (k:=k) C hrep (F.obj p.1.1) :=
    ((hKset p.1.1).mem_toFinset.mp p.2.2).1
  have hZcanonical (p : A) : x ∈ canonicalIncomingSourceSupport (k:=k) C hrep (Z p) := by
    rw [canonicalIncomingSourceSupport_shift_eq_preimage (k:=k) D hrep
      (F.obj p.1.1) (gOf p)]
    simpa [hgOf p] using hZx p
  have hZcore (p : A) : Z p ∈ Core.isoClosure := by
    change Z p ∈
      ((finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 2).isoClosure
    have hind := hZind p
    have hcan := hZcanonical p
    change x ∈ moduleSupport k (Z p).obj.obj ∪ _ at hcan
    rcases hcan with hzx | hzx
    · have hnontriv : Nontrivial ((Z p).obj.obj.obj x) := hzx
      have hseed : Z p ∈ (finiteFiberControlSeed hrep x).isoClosure :=
        (mem_finiteFiberControlSeed_isoClosure_iff hrep x (Z p)).2 ⟨hind, hnontriv⟩
      have h1 : Z p ∈
          ((finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 1).isoClosure := by
        simpa only [FiniteIndecomposableModuleFamily.iterateHomNeighborhood] using
          (finiteFiberControlSeed hrep x).mem_iterateHomNeighborhood_succ_of_homInteraction
            (n := 0) hrep hseed hind (Or.inl rfl)
      exact (finiteFiberControlSeed hrep x).mem_iterateHomNeighborhood_succ_of_homInteraction
        (n := 1) hrep h1 hind (Or.inl rfl)
    · rcases hzx with ⟨N, hN, f, hf, hxN⟩
      have hNtriv : Nontrivial (N.obj.obj.obj x) := hxN
      have hNseed : N ∈ (finiteFiberControlSeed hrep x).isoClosure :=
        (mem_finiteFiberControlSeed_isoClosure_iff hrep x N).2 ⟨hN, hNtriv⟩
      have h1 : Z p ∈
          ((finiteFiberControlSeed hrep x).iterateHomNeighborhood hrep 1).isoClosure := by
        simpa only [FiniteIndecomposableModuleFamily.iterateHomNeighborhood] using
          (finiteFiberControlSeed hrep x).mem_iterateHomNeighborhood_succ_of_ne_zero_to
            (n := 0) hrep hNseed hind f hf
      exact (finiteFiberControlSeed hrep x).mem_iterateHomNeighborhood_succ_of_homInteraction
        (n := 1) hrep h1 hind (Or.inl rfl)
  have hZV (p : A) : Z p ∈ V.isoClosure := by
    rw [isoClassFamily_isoClosure_eq (k:=k) Core]
    exact hZcore p
  have hZcore' (p : A) : ∃ j : Fin V.n, Nonempty (V.obj j ≅ Z p) := by
    have h := hZV p
    change ∃ j : Fin V.n, Nonempty (V.obj j ≅ Z p) at h
    exact h
  let jOf : A → Fin V.n := fun p => Classical.choose (hZcore' p)
  have eOf (p : A) : V.obj (jOf p) ≅ Z p :=
    Classical.choice (Classical.choose_spec (hZcore' p))
  let B : Type := {j : Fin V.n // x ∈ canonicalIncomingSourceSupport (k:=k) C hrep (V.obj j)}
  let eAB : A → B := fun p => ⟨jOf p, by
    have hmem : x ∈ canonicalIncomingSourceSupport (k:=k) C hrep (V.obj (jOf p)) := by
      rw [canonicalIncomingSourceSupport_eq_of_iso hrep (eOf p)]
      exact hZcanonical p
    exact hmem⟩
  have eAB_surj : Function.Surjective eAB := by
    intro j
    obtain ⟨i, a, ⟨e⟩⟩ :=
      CoherentDeckShift.finiteOrbitSourceRepresentativeFamily_covers
        (k:=k) D hP hI hlocalEnd hfree hrep (V.obj j) (V.indecomposable j)
    let g : G := a.toMul
    have ha : a = Additive.ofMul g := by
      apply Additive.toMul.injective
      rfl
    have hcanShift : x ∈ canonicalIncomingSourceSupport (k:=k) C hrep
        ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) a).obj (F.obj i)) := by
      rw [← canonicalIncomingSourceSupport_eq_of_iso hrep e]
      exact j.property
    have hcanSrc : g • x ∈ canonicalIncomingSourceSupport (k:=k) C hrep (F.obj i) := by
      have hcanShift' := hcanShift
      rw [show ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) a).obj (F.obj i)) =
          ((shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) (Additive.ofMul g)).obj (F.obj i)) by rw [ha]] at hcanShift'
      rw [canonicalIncomingSourceSupport_shift_eq_preimage (k:=k) D hrep (F.obj i) g] at hcanShift'
      exact hcanShift'
    have hKg : g • x ∈ K i := (hKset i).mem_toFinset.mpr
      ⟨hcanSrc, ⟨g, rfl⟩⟩
    let p : A := ⟨⟨i, by simp⟩, ⟨g • x, hKg⟩⟩
    have hgg : gOf p = g := by
      apply IsCancelSMul.right_cancel (gOf p) g x
      simpa [p] using (hgOf p).trans rfl
    have hiso : V.obj j ≅ Z p := by
      change V.obj j ≅ Z p
      rw [show Z p = (shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k)
          (Additive.ofMul g)).obj (F.obj i) by simp [Z, p, hgg]]
      simpa [ha] using e
    have hji : Nonempty (V.obj j ≅ V.obj (jOf p)) := by
      exact ⟨hiso.trans (eOf p).symm⟩
    have hEq : j = jOf p := by
      change j = jOf p
      apply isoClassFamily_pairwise (k:=k) Core
      exact hji
    exact ⟨p, Subtype.ext hEq.symm⟩
  have eAB_inj : Function.Injective eAB := by
    intro p q hpq
    have hpq' : jOf p = jOf q := congrArg Subtype.val hpq
    have hZpq : Z p ≅ Z q := (eOf p).symm.trans
      ((eqToIso (congrArg V.obj hpq')).trans (eOf q))
    let ap : Additive G := Additive.ofMul (gOf p)
    let aq : Additive G := Additive.ofMul (gOf q)
    have hAmbient : F.obj p.1.1 ≅
        (shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) (aq + -ap)).obj
          (F.obj q.1.1) := by
      let hshift := (shiftFunctor (FiniteDimensionalModuleCategory (C:=C) k) (-ap)).mapIso hZpq
      let eleft := shiftShiftNeg (F.obj p.1.1) ap
      let eadd := (shiftFunctorAdd (FiniteDimensionalModuleCategory (C:=C) k) aq (-ap)).app
        (F.obj q.1.1)
      exact (eleft.symm.trans (by
        simpa [Z, ap, aq] using hshift)).trans eadd.symm
    have hindex :=
      CoherentDeckShift.finiteOrbitSourceRepresentativeFamily_no_shift_iso
        (k:=k) D hP hI hlocalEnd hfree hrep p.1.1 q.1.1 (aq + -ap) hAmbient
    have hpidx : p.1.1 = q.1.1 := hindex
    have hdiff : aq + -ap = 0 := by
      exact D.finiteDimensionalModule_trivialStabilizer
        (k:=k) (F.obj p.1.1) (F.indecomposable p.1.1).1 (aq + -ap)
          ⟨by simpa [hpidx] using hAmbient⟩
    have hapq : ap = aq := by
      have h := eq_neg_of_add_eq_zero_left hdiff
      have h' : aq = ap := by simpa using h
      exact h'.symm
    have hgpq : gOf p = gOf q := by
      apply Additive.toMul.injective
      exact hapq
    have hpy : p.2.1 = q.2.1 := by
      rw [← hgOf p, ← hgOf q, hgpq]
    have hpfst : p.1 = q.1 := Subtype.ext hpidx
    have hsigma : ∀ (r s : A), r.1 = s.1 →
        (r.2.1 : C) = s.2.1 → r = s := by
      intro r s hrs hys
      apply Sigma.ext hrs
      apply (Subtype.heq_iff_coe_eq (fun z => by simpa [hrs])).2
      exact hys
    exact hsigma p q hpfst hpy
  have eAB_bij : Function.Bijective eAB := ⟨eAB_inj, eAB_surj⟩
  let fF : Fin F.n → Finset C → ℚ := fun i S ↦
    (finiteDeletionExtendedLocalDensity (k:=k) C hrep (S : Set C)
      (F.obj i) (F.indecomposable i) : ℤ)
  let fV : Fin V.n → Finset C → ℚ := fun j S ↦
    (finiteDeletionExtendedLocalDensity (k:=k) C hrep (S : Set C)
      (V.obj j) (V.indecomposable j) : ℤ)
  let eg : A → Equiv.Perm C := fun p => MulAction.toPerm (gOf p)⁻¹
  let L : A → Finset C := fun p =>
    (eg p).finsetCongr ((K p.1.1).erase p.2.1)
  let Tset : Set C := ⋃ p : A, (L p : Set C)
  have hTset : Tset.Finite := by
    exact Set.finite_iUnion fun p => (L p).finite_toSet
  let T : Finset C := hTset.toFinset
  have hLsub : ∀ p : A, L p ⊆ T := by
    intro p z hz
    exact hTset.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨p, hz⟩)
  have hxT : x ∉ T := by
    intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hTset.mem_toFinset.mp hx)
    have hp' : (eg p).symm x ∈ (K p.1.1).erase p.2.1 := by
      simpa [L, Equiv.finsetCongr_apply, and_comm, Equiv.symm_apply_eq] using hp
    have hxy : p.2.1 = (gOf p) • x := (hgOf p).symm
    have := (Finset.mem_erase.mp hp').1
    apply this
    rw [hxy]
    simp [eg]
  have htarget : ∀ (p : A) (S : Finset C),
      fV (eAB p).1 S =
        fF p.1.1 ((eg p).symm.finsetCongr S) := by
    intro p S
    let g := gOf p
    let Ssrc := (eg p).symm.finsetCongr S
    have hSsrc : (Ssrc : Set C) = g • (S : Set C) := by
      ext Y
      constructor
      · intro hY
        change Y ∈ (eg p).symm.finsetCongr S at hY
        simp only [Equiv.finsetCongr_apply, Finset.mem_map] at hY
        obtain ⟨Z, hZ, rfl⟩ := hY
        simpa [Ssrc, eg, g, MulAction.toPerm_symm_apply] using hZ
      · intro hY
        obtain ⟨Z, hZ, hZY⟩ := Set.mem_smul_set.mp hY
        change Z ∈ S at hZ
        rw [← hZY]
        simpa [Ssrc, eg, g] using hZ
    have hshift := finiteDeletionExtendedLocalDensity_shift_eq_total
      (k := k) D hrep hC hlocalEnd (Ssrc : Set C) g
        (F.obj p.1.1) (F.indecomposable p.1.1)
    have hset : equivalenceDeletedSet
        (shiftEquiv C (Additive.ofMul g)) (Ssrc : Set C) = (S : Set C) := by
      rw [equivalenceDeletedSet_shift_eq_inv_smul D hC]
      rw [hSsrc]
      ext Y
      simp
    have hFpind : Indecomposable
        ((shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
          (Additive.ofMul g)).obj (F.obj p.1.1)) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
          (Additive.ofMul g)) (F.obj p.1.1)).2 (F.indecomposable p.1.1)
    have hshift' :
        finiteDeletionExtendedLocalDensity (k := k) C hrep
          (S : Set C)
          ((shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
            (Additive.ofMul g)).obj (F.obj p.1.1))
          hFpind =
        finiteDeletionExtendedLocalDensity (k := k) C hrep
          (Ssrc : Set C) (F.obj p.1.1) (F.indecomposable p.1.1) := by
      rw [← hset]
      simpa [fF, Ssrc] using congrArg (fun z : ℤ => (z : ℚ)) hshift
    have hIso : (V.obj (eAB p).1) ≅
        (shiftFunctor (FiniteDimensionalModuleCategory (C := C) k)
          (Additive.ofMul g)).obj (F.obj p.1.1) := by
      simpa [Z, g] using eOf p
    have hIsoDensity := finiteDeletionExtendedLocalDensity_eq_of_iso
      (k := k) C hrep S (V.indecomposable (eAB p).1)
        hFpind hIso
    change (finiteDeletionExtendedLocalDensity (k := k) C hrep
      (S : Set C) (V.obj (eAB p).1) (V.indecomposable (eAB p).1) : ℚ) =
      (finiteDeletionExtendedLocalDensity (k := k) C hrep
        (Ssrc : Set C) (F.obj p.1.1) (F.indecomposable p.1.1) : ℚ)
    rw [hIsoDensity, hshift']
  have hMarginal_L : ∀ (p : A),
      insertionMarginal (K p.1.1) (fF p.1.1) p.2.1 =
        ∑ S ∈ (L p).powerset, weight (L p) S *
          (fV (eAB p).1 S - fV (eAB p).1 (insert x S)) := by
    intro p
    let e := eg p
    have hIM := insertionMarginal_finsetCongr e (K p.1.1)
      (fF p.1.1) p.2.1
    have heval : e p.2.1 = x := by
      change (gOf p)⁻¹ • p.2.1 = x
      rw [← hgOf p]
      simp
    have hEK : (e.finsetCongr (K p.1.1)).erase x = L p := by
      simpa [L, e, ← heval] using
        (Finset.map_erase e.toEmbedding (K p.1.1) p.2.1).symm
    rw [← hIM]
    rw [heval]
    unfold insertionMarginal
    rw [hEK]
    apply Finset.sum_congr rfl
    intro S hS
    rw [htarget p S, htarget p (insert x S)]
  have hTU : (T : Set C) ⊆ U := by
    intro a ha
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hTset.mem_toFinset.mp ha)
    have hp' : (eg p).symm a ∈ (K p.1.1).erase p.2.1 := by
      simpa [L, Equiv.finsetCongr_apply, Equiv.symm_apply_eq, and_comm] using hp
    have hpK : (eg p).symm a ∈ K p.1.1 := (Finset.mem_erase.mp hp').2
    have hpU : (eg p).symm a ∈ U :=
      ((hKset p.1.1).mem_toFinset.mp hpK).2
    apply (hUG (gOf p) a).mp
    simpa [eg] using hpU
  have hcanonical_imp_L : ∀ (p : A) (a : C), a ∈ T →
      a ∈ canonicalIncomingSourceSupport (k:=k) C hrep (V.obj (eAB p).1) →
      a = x ∨ a ∈ L p := by
    intro p a haT haCan
    have haZ : a ∈ canonicalIncomingSourceSupport (k:=k) C hrep (Z p) := by
      rw [canonicalIncomingSourceSupport_eq_of_iso hrep (eOf p)] at haCan
      exact haCan
    have hgaCan : (gOf p) • a ∈
        canonicalIncomingSourceSupport (k:=k) C hrep (F.obj p.1.1) := by
      have hpre := haZ
      rw [canonicalIncomingSourceSupport_shift_eq_preimage (k:=k) D hrep
        (F.obj p.1.1) (gOf p)] at hpre
      change (gOf p) • a ∈
        canonicalIncomingSourceSupport (k:=k) C hrep (F.obj p.1.1) at hpre
      exact hpre
    have hgaU : (gOf p) • a ∈ U := (hUG (gOf p) a).mpr (hTU haT)
    have hgaK : (gOf p) • a ∈ K p.1.1 :=
      (hKset p.1.1).mem_toFinset.mpr ⟨hgaCan, hgaU⟩
    by_cases hax : a = x
    · exact Or.inl hax
    · right
      have hne : (gOf p) • a ≠ p.2.1 := by
        intro h
        apply hax
        apply (MulAction.injective (gOf p))
        exact h.trans (hgOf p).symm
      have hgaErase : (gOf p) • a ∈ (K p.1.1).erase p.2.1 :=
        Finset.mem_erase.mpr ⟨hne, hgaK⟩
      rw [show L p = (eg p).finsetCongr ((K p.1.1).erase p.2.1) by rfl]
      rw [Equiv.finsetCongr_apply, Finset.mem_map]
      refine ⟨(gOf p) • a, hgaErase, ?_⟩
      simp [eg]
  have hlocal_irrel : ∀ (p : A) (a : C), a ∈ T → a ∉ L p →
      ∀ S ∈ (T.erase a).powerset,
        (fV (eAB p).1 (insert a S) - fV (eAB p).1 (insert x (insert a S))) =
          (fV (eAB p).1 S - fV (eAB p).1 (insert x S)) := by
    intro p a haT haL S hS
    have hnotCan : a ∉ canonicalIncomingSourceSupport (k:=k) C hrep
        (V.obj (eAB p).1) := by
      intro hca
      rcases hcanonical_imp_L p a haT hca with hax | hal
      · exact hxT (hax ▸ haT)
      · exact haL hal
    have hdens : ∀ R : Finset C,
        fV (eAB p).1 (insert a R) = fV (eAB p).1 R := by
      intro R
      have hdensZ :=
        finiteDeletionExtendedLocalDensity_eq_of_inter_eq_canonicalIncomingSourceSupport
          (k:=k) hP hrep (insert a (R : Set C)) (R : Set C)
          (V.obj (eAB p).1) (V.indecomposable (eAB p).1) (by
            ext z
            constructor
            · rintro ⟨hz, hzC⟩
              have hz' : z = a ∨ z ∈ (R : Set C) := by simpa using hz
              rcases hz' with rfl | hzR
              · exact False.elim (hnotCan hzC)
              · exact ⟨hzR, hzC⟩
            · rintro ⟨hzR, hzC⟩
              exact ⟨by simp [hzR], hzC⟩)
      dsimp [fV]
      simpa only [Finset.coe_insert] using
        congrArg (fun z : ℤ => (z : ℚ)) hdensZ
    rw [Finset.insert_comm x a, hdens S, hdens (insert x S)]
  have hMarginal : ∀ (p : A),
      insertionMarginal (K p.1.1) (fF p.1.1) p.2.1 =
        ∑ S ∈ T.powerset, weight T S *
          (fV (eAB p).1 S - fV (eAB p).1 (insert x S)) := by
    intro p
    let gd : Finset C → ℚ := fun S ↦
      fV (eAB p).1 S - fV (eAB p).1 (insert x S)
    have hproj := weightedPowersetSum_eq_of_subset (L p) T (hLsub p) gd
      (by
        intro a haT haL S hS
        exact hlocal_irrel p a haT haL S hS)
    calc
      insertionMarginal (K p.1.1) (fF p.1.1) p.2.1 =
          ∑ S ∈ (L p).powerset, weight (L p) S *
            (fV (eAB p).1 S - fV (eAB p).1 (insert x S)) := hMarginal_L p
      _ = ∑ S ∈ T.powerset, weight T S * gd S := hproj.symm
      _ = ∑ S ∈ T.powerset, weight T S *
          (fV (eAB p).1 S - fV (eAB p).1 (insert x S)) := by rfl
  let vchange : Fin V.n → ℤ := fun j ↦
    finiteDeletionLocalChangeAt (k:=k) C hrep ({x} : Set C)
      (V.obj j) (V.indecomposable j)
  let vclass : V.IsoClass → Fin V.n := Quotient.lift id (by
    intro i j hij
    obtain ⟨e⟩ := hij
    exact isoClassFamily_pairwise (k:=k) Core ⟨e⟩)
  have hvclass_bij : Function.Bijective vclass := by
    constructor
    · intro q r hqr
      induction q using Quotient.inductionOn with
      | _ i =>
        induction r using Quotient.inductionOn with
        | _ j =>
          have hij : i = j := by simpa [vclass] using hqr
          subst j
          exact Quotient.sound ⟨Iso.refl _⟩
    · intro j
      refine ⟨Quotient.mk V.isoSetoid j, ?_⟩
      rfl
  let vEquiv : V.IsoClass ≃ Fin V.n := Equiv.ofBijective vclass hvclass_bij
  have hvsum : (∑ j : Fin V.n, vchange j) =
      finiteDeletionLocalChangeSum (k:=k) C hrep ({x} : Set C) V := by
    unfold finiteDeletionLocalChangeSum
    symm
    apply Fintype.sum_equiv vEquiv
      (fun q : V.IsoClass => finiteDeletionLocalChangeOnIsoClass
        (k:=k) C hrep ({x} : Set C) V q)
      vchange
    intro q
    induction q using Quotient.inductionOn with
    | _ j => rfl
  have hvzero : ∀ j : Fin V.n,
      x ∉ canonicalIncomingSourceSupport (k:=k) C hrep (V.obj j) →
      ∀ S : Finset C, fV j S - fV j (insert x S) = 0 := by
    intro j hj S
    have hz := finiteDeletionExtendedLocalDensity_eq_of_inter_eq_canonicalIncomingSourceSupport
      (k:=k) hP hrep (S : Set C) (insert x (S : Set C))
      (V.obj j) (V.indecomposable j) (by
        ext z
        constructor
        · rintro ⟨hzS, hzC⟩
          exact ⟨by simp [hzS], hzC⟩
        · rintro ⟨hzS, hzC⟩
          have hz' : z = x ∨ z ∈ (S : Set C) := by simpa using hzS
          rcases hz' with rfl | hzR
          · exact False.elim (hj hzC)
          · exact ⟨hzR, hzC⟩)
    have hz' := congrArg (fun z : ℤ => (z : ℚ)) hz
    dsimp [fV]
    rw [sub_eq_zero]
    exact_mod_cast hz'
  have hBpos : ∀ S ∈ T.powerset,
      0 ≤ ∑ b : B, (fV b.1 S - fV b.1 (insert x S)) := by
    intro S hS
    let P : Fin V.n → Prop := fun j ↦
      x ∈ canonicalIncomingSourceSupport (k:=k) C hrep (V.obj j)
    let d : Fin V.n → ℚ := fun j ↦
      fV j S - fV j (insert x S)
    have hout : ∑ j : {j : Fin V.n // ¬ P j}, d j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact hvzero j.1 j.2 S
    have hpart := Fintype.sum_subtype_add_sum_subtype P d
    have hsub : (∑ j : {j : Fin V.n // P j}, d j) =
        ∑ j : Fin V.n, d j := by
      rw [← hpart, hout, add_zero]
    have hxS : x ∉ S := by
      intro hx
      exact hxT ((Finset.mem_powerset.mp hS) hx)
    have hpoint := finiteSupportOrbitAverage_nonnegative_point_frozen
      (k:=k) D hC hP hI hlocalEnd hrep hfree hDir x S hxS
    have hall : 0 ≤ ∑ j : Fin V.n, d j := by
      simpa [d, V, fV] using hpoint
    change 0 ≤ ∑ j : {j : Fin V.n // P j}, d j
    rw [hsub]
    exact hall
  let eABeq : A ≃ B := Equiv.ofBijective eAB eAB_bij
  have hoccpos : ∀ S ∈ T.powerset,
      0 ≤ ∑ p : A, (fV (eAB p).1 S - fV (eAB p).1 (insert x S)) := by
    intro S hS
    have heq : (∑ p : A,
        (fV (eAB p).1 S - fV (eAB p).1 (insert x S))) =
        ∑ b : B, (fV b.1 S - fV b.1 (insert x S)) := by
      exact Fintype.sum_equiv eABeq
        (fun p : A => fV (eAB p).1 S - fV (eAB p).1 (insert x S))
        (fun b : B => fV b.1 S - fV b.1 (insert x S))
        (fun p => rfl)
    rw [heq]
    exact hBpos S hS
  have hnon := finiteSupportOrbitAverage_nonnegative_of_occurrence
    (α := C) (β := Fin F.n) (γ := B)
    (Finset.univ : Finset (Fin F.n)) K fF T x hxT
    eAB (fun b : B => fV b.1)
    (fun p => hMarginal p) hoccpos
  have hnon' : 0 ≤ ∑ b ∈ (Finset.univ : Finset (Fin F.n)),
      (fF b ∅ - fF b (K b)) := hnon
  have hKlocal : ∀ i : Fin F.n, fF i (K i) =
      (finiteDeletionExtendedLocalDensity (k:=k) C hrep U
        (F.obj i) (F.indecomposable i) : ℚ) := by
    intro i
    have hinter : Kset i ∩ canonicalIncomingSourceSupport
        (k:=k) C hrep (F.obj i) =
        U ∩ canonicalIncomingSourceSupport (k:=k) C hrep (F.obj i) := by
      ext z
      constructor
      · rintro ⟨⟨hzCan, hzU⟩, hzCan'⟩
        exact ⟨hzU, hzCan'⟩
      · rintro ⟨hzU, hzCan⟩
        exact ⟨⟨hzCan, hzU⟩, hzCan⟩
    have h := finiteDeletionExtendedLocalDensity_eq_of_inter_eq_canonicalIncomingSourceSupport
      (k:=k) hP hrep (Kset i) U (F.obj i) (F.indecomposable i) hinter
    dsimp [fF, K]
    rw [show ((hKset i).toFinset : Set C) = Kset i by
      ext z
      exact (hKset i).mem_toFinset]
    exact_mod_cast h
  have hempty : ∀ i : Fin F.n,
      fF i ∅ = (finiteModuleLocalDensity hrep (F.obj i)
        (F.indecomposable i) : ℚ) := by
    intro i
    have h := finiteDeletionExtendedLocalDensity_empty_eq_finiteModuleLocalDensity
      (k:=k) hrep (F.obj i) (F.indecomposable i)
    dsimp [fF]
    exact_mod_cast h
  have hrewrite :
      (∑ b ∈ (Finset.univ : Finset (Fin F.n)),
        (fF b ∅ - fF b (K b))) =
      ∑ b ∈ (Finset.univ : Finset (Fin F.n)),
        ((finiteModuleLocalDensity hrep (F.obj b)
          (F.indecomposable b) : ℚ) -
          (finiteDeletionExtendedLocalDensity (k:=k) C hrep U
            (F.obj b) (F.indecomposable b) : ℚ)) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [hempty b, hKlocal b]
  have hineq : 0 ≤
      ∑ i : Fin F.n,
        ((finiteModuleLocalDensity hrep (F.obj i)
          (F.indecomposable i) : ℚ) -
        (finiteDeletionExtendedLocalDensity (k:=k) C hrep U
          (F.obj i) (F.indecomposable i) : ℚ)) := by
    rw [← hrewrite]
    exact hnon'
  refine ⟨?_, ?_⟩
  · simpa [F, U] using hineq
  · intro hzeroTarget
    have hzero' :
        (∑ b ∈ (Finset.univ : Finset (Fin F.n)),
          (fF b ∅ - fF b (K b))) = 0 := by
      rw [hrewrite]
      simpa [F, U] using hzeroTarget
    let inner : Finset C → ℚ := fun S ↦
      ∑ p : A, (fV (eAB p).1 S - fV (eAB p).1 (insert x S))
    have hweighted :
        (∑ S ∈ T.powerset, weight T S * inner S) = 0 := by
      have havg := finiteSupportOrbitAverage_of_occurrence
        (α := C) (β := Fin F.n) (γ := B)
        (Finset.univ : Finset (Fin F.n)) K fF T x hxT
        eAB (fun b : B => fV b.1)
        (fun p => hMarginal p)
      rw [← havg, hzero']
    have hinner0 : inner ∅ = 0 :=
      empty_localChange_eq_zero_of_weighted_sum_eq_zero T inner
        (by simpa [inner] using hoccpos) hweighted
    have hinnerB : inner ∅ =
        ∑ b : B, (fV b.1 ∅ - fV b.1 (insert x ∅)) := by
      exact Fintype.sum_equiv eABeq
        (fun p : A => fV (eAB p).1 ∅ - fV (eAB p).1 (insert x ∅))
        (fun b : B => fV b.1 ∅ - fV b.1 (insert x ∅))
        (fun p => rfl)
    have hvdiff : ∀ j : Fin V.n,
        fV j ∅ - fV j (insert x ∅) = (vchange j : ℚ) := by
      intro j
      have h := finiteDeletionExtendedLocalDensity_empty_eq_finiteModuleLocalDensity
        (k:=k) hrep (V.obj j) (V.indecomposable j)
      have hq :
          (finiteDeletionExtendedLocalDensity (k:=k) C hrep ∅
            (V.obj j) (V.indecomposable j) : ℚ) =
            (finiteModuleLocalDensity hrep (V.obj j)
              (V.indecomposable j) : ℚ) := by
        exact_mod_cast h
      have hq' :
          (finiteDeletionExtendedLocalDensity (k:=k) C hrep
              ((∅ : Finset C) : Set C)
              (V.obj j) (V.indecomposable j) : ℚ) =
            (finiteModuleLocalDensity hrep (V.obj j)
              (V.indecomposable j) : ℚ) := by
        simpa using hq
      dsimp [fV, vchange]
      rw [finiteDeletionLocalChangeAt]
      rw [hq']
      push_cast
      rfl
    have hsumBv :
        (∑ b : B, (fV b.1 ∅ - fV b.1 (insert x ∅))) =
          ∑ j : Fin V.n, (vchange j : ℚ) := by
      let P : Fin V.n → Prop := fun j ↦
        x ∈ canonicalIncomingSourceSupport (k:=k) C hrep (V.obj j)
      have hpart := Fintype.sum_subtype_add_sum_subtype P
        (fun j : Fin V.n => (vchange j : ℚ))
      have hout : ∑ j : {j : Fin V.n // ¬ P j}, (vchange j.1 : ℚ) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hz := hvzero j.1 j.2 ∅
        have hv := hvdiff j.1
        have hz' : (vchange j.1 : ℚ) = 0 := by
          rw [← hv]
          simpa using hz
        exact hz'
      have hsub : (∑ j : {j : Fin V.n // P j}, (vchange j.1 : ℚ)) =
          ∑ j : Fin V.n, (vchange j : ℚ) := by
        rw [← hpart, hout, add_zero]
      have hleft :
          (∑ b : B, (fV b.1 ∅ - fV b.1 (insert x ∅))) =
            ∑ j : {j : Fin V.n // P j}, (vchange j.1 : ℚ) := by
        apply Fintype.sum_equiv (Equiv.refl B)
        intro b
        exact hvdiff b.1
      rw [hleft, hsub]
    have hsumVzero : ∑ j : Fin V.n, (vchange j : ℚ) = 0 := by
      rw [← hsumBv, ← hinnerB]
      exact hinner0
    have hcast :
        ((∑ j : Fin V.n, vchange j : ℤ) : ℚ) = 0 := by
      push_cast
      exact hsumVzero
    have hcorezero : finiteDeletionLocalChangeSum (k:=k) C hrep
        ({x} : Set C) Core = 0 := by
      have hCV : Core.isoClosure ⊆ V.isoClosure := by
        rw [isoClassFamily_isoClosure_eq (k:=k) Core]
      have houtCV : ∀ j : Fin V.n, V.obj j ∉ Core.isoClosure →
          finiteDeletionLocalChangeAt (k:=k) C hrep ({x} : Set C)
            (V.obj j) (V.indecomposable j) = 0 := by
        intro j hj
        exfalso
        apply hj
        rw [← isoClassFamily_isoClosure_eq (k:=k) Core]
        exact V.obj_mem_isoClosure j
      have hsumCV := finiteDeletionLocalChangeSum_eq_of_isoClosure_subset
        (k:=k) C hrep ({x} : Set C) Core V hCV houtCV
      calc
        finiteDeletionLocalChangeSum (k:=k) C hrep ({x} : Set C) Core =
            finiteDeletionLocalChangeSum (k:=k) C hrep ({x} : Set C) V := hsumCV
        _ = ∑ j : Fin V.n, vchange j := hvsum.symm
        _ = 0 := by exact_mod_cast hcast
    exact hcorezero
end MagnitudeConjecture.StandardCovering
