import MagnitudeConjecture.CategoryTheory.ObjectDeletionControlWindow

/-!
# Finitely many surviving object-deletion windows

The manuscript fixes the finite ambient family `U₃(x)` and observes that an
intermediate deletion stage can only discard some of those representatives.
Hence only finitely many surviving full subcategories occur.  This file
formalizes that finite signature and the ensuing choice-and-union argument
for upward-closed finite control data.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- The indices of a finite ambient family whose representatives survive a
given deletion, equivalently whose modules vanish on every deleted object. -/
def deletionSurvivingIndices
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (D : Set C) : Finset (Fin W.n) := by
  classical
  exact Finset.univ.filter fun i ↦
    ModuleVanishesOnDeleted (k := k) C D (W.obj i).obj.obj

@[simp]
theorem mem_deletionSurvivingIndices_iff
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (D : Set C) (i : Fin W.n) :
    i ∈ deletionSurvivingIndices (k := k) C W D ↔
      ModuleVanishesOnDeleted (k := k) C D (W.obj i).obj.obj := by
  simp [deletionSurvivingIndices]

/-- The finite subfamily of ambient representatives surviving a deletion. -/
def deletionSurvivingSubfamily
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (D : Set C) :
    FiniteIndecomposableModuleFamily (k := k) (C := C) :=
  W.subfamily (deletionSurvivingIndices (k := k) C W D)

/-- Every object of the surviving subfamily really vanishes on the deleted
set. -/
theorem deletionSurvivingSubfamily_obj_vanishes
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (D : Set C) (t : Fin (deletionSurvivingSubfamily (k := k) C W D).n) :
    ModuleVanishesOnDeleted (k := k) C D
      ((deletionSurvivingSubfamily (k := k) C W D).obj t).obj.obj := by
  let I := deletionSurvivingIndices (k := k) C W D
  let e : Fin I.card ≃ I := I.equivFin.symm
  change ModuleVanishesOnDeleted (k := k) C D (W.obj (e t).1).obj.obj
  exact (mem_deletionSurvivingIndices_iff (k := k) C W D (e t).1).1
    (e t).2

/-- Any module represented by the ambient family and surviving the deletion
is represented by the corresponding finite surviving subfamily. -/
theorem mem_deletionSurvivingSubfamily_isoClosure
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (D : Set C)
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : M ∈ W.isoClosure)
    (hvanish : ModuleVanishesOnDeleted (k := k) C D M.obj.obj) :
    M ∈ (deletionSurvivingSubfamily (k := k) C W D).isoClosure := by
  obtain ⟨i, ⟨e⟩⟩ := hM
  have hi : i ∈ deletionSurvivingIndices (k := k) C W D := by
    rw [mem_deletionSurvivingIndices_iff]
    exact moduleVanishesOnDeleted_of_iso (k := k) C D e.symm hvanish
  obtain ⟨j, ⟨ej⟩⟩ :=
    W.obj_mem_subfamily_isoClosure
      (deletionSurvivingIndices (k := k) C W D) hi
  exact ⟨j, ⟨ej ≪≫ e⟩⟩

/-- The surviving finite subfamily represents exactly the members of the
ambient family that vanish on the deleted objects.  Thus its isomorphism
closure is the manuscript's full surviving subcategory inside the fixed
finite window. -/
theorem mem_deletionSurvivingSubfamily_isoClosure_iff
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (D : Set C)
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k} :
    M ∈ (deletionSurvivingSubfamily (k := k) C W D).isoClosure ↔
      M ∈ W.isoClosure ∧
        ModuleVanishesOnDeleted (k := k) C D M.obj.obj := by
  constructor
  · rintro ⟨t, ⟨e⟩⟩
    let I := deletionSurvivingIndices (k := k) C W D
    let eI : Fin I.card ≃ I := I.equivFin.symm
    change W.obj (eI t).1 ≅ M at e
    constructor
    · exact ⟨(eI t).1, ⟨e⟩⟩
    · exact moduleVanishesOnDeleted_of_iso (k := k) C D e
        (deletionSurvivingSubfamily_obj_vanishes (k := k) C W D t)
  · rintro ⟨hM, hvanish⟩
    exact mem_deletionSurvivingSubfamily_isoClosure (k := k) C W D hM hvanish

/-- A realized survivor signature is one of the finite subsets of the fixed
ambient family actually produced by an allowed deleted set. -/
def RealizedSurvivorSignature
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (Allowed : Set C → Prop) :=
  {I : Finset (Fin W.n) //
    ∃ D : Set C, Allowed D ∧
      deletionSurvivingIndices (k := k) C W D = I}

noncomputable instance realizedSurvivorSignatureFintype
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (Allowed : Set C → Prop) :
    Fintype (RealizedSurvivorSignature (k := k) C W Allowed) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The signature associated to one allowed deletion stage. -/
def realizedSurvivorSignatureOf
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (Allowed : Set C → Prop) (D : Set C) (hD : Allowed D) :
    RealizedSurvivorSignature (k := k) C W Allowed :=
  ⟨deletionSurvivingIndices (k := k) C W D, ⟨D, hD, rfl⟩⟩

/-- Choose one deleted set realizing a given survivor signature. -/
def RealizedSurvivorSignature.representativeDeletedSet
    {W : FiniteIndecomposableModuleFamily (k := k) (C := C)}
    {Allowed : Set C → Prop}
    (q : RealizedSurvivorSignature (k := k) C W Allowed) : Set C :=
  Classical.choose q.property

theorem RealizedSurvivorSignature.representative_allowed
    {W : FiniteIndecomposableModuleFamily (k := k) (C := C)}
    {Allowed : Set C → Prop}
    (q : RealizedSurvivorSignature (k := k) C W Allowed) :
    Allowed (q.representativeDeletedSet (k := k) C) :=
  (Classical.choose_spec q.property).1

theorem RealizedSurvivorSignature.representative_indices
    {W : FiniteIndecomposableModuleFamily (k := k) (C := C)}
    {Allowed : Set C → Prop}
    (q : RealizedSurvivorSignature (k := k) C W Allowed) :
    deletionSurvivingIndices (k := k) C W
        (q.representativeDeletedSet (k := k) C) = q.1 :=
  (Classical.choose_spec q.property).2

/-- Finite survivor signatures and upward closure turn stagewise existence
of finite control families into one finite family controlling every allowed
deletion stage.  The invariance premise is the exact statement that control
depends only on the surviving full subcategory of the fixed ambient family. -/
theorem exists_uniformControlFamily_of_survivorSignatures
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (Allowed : Set C → Prop)
    (Control : Set C →
      FiniteIndecomposableModuleFamily (k := k) (C := C) → Prop)
    (exists_control : ∀ D, Allowed D → ∃ V, Control D V)
    (control_invariant :
      ∀ {D E}, Allowed D → Allowed E →
        deletionSurvivingIndices (k := k) C W D =
          deletionSurvivingIndices (k := k) C W E →
        ∀ {V}, Control D V ↔ Control E V)
    (control_upward :
      ∀ D, Allowed D → ∀ {V U}, Control D V →
        V.isoClosure ⊆ U.isoClosure → Control D U) :
    ∃ U : FiniteIndecomposableModuleFamily (k := k) (C := C),
      ∀ D, Allowed D → Control D U := by
  classical
  let Q := RealizedSurvivorSignature (k := k) C W Allowed
  let rep : Q → Set C := fun q ↦ q.representativeDeletedSet (k := k) C
  have hrep : ∀ q : Q, Allowed (rep q) := fun q ↦ q.representative_allowed
  choose V hV using fun q : Q ↦ exists_control (rep q) (hrep q)
  let U := FiniteIndecomposableModuleFamily.flatten V
  refine ⟨U, ?_⟩
  intro D hD
  let q : Q := realizedSurvivorSignatureOf (k := k) C W Allowed D hD
  have hindices : deletionSurvivingIndices (k := k) C W (rep q) =
      deletionSurvivingIndices (k := k) C W D := by
    exact q.representative_indices.trans rfl
  have hcontrolD : Control D (V q) :=
    (control_invariant (hrep q) hD hindices).1 (hV q)
  exact control_upward D hD hcontrolD
    (FiniteIndecomposableModuleFamily.isoClosure_subset_flatten V q)

/-- The uniform-choice argument specialized to the manuscript's fixed
three-step Hom window `U₃(y)`. -/
theorem exists_uniformControlFamily_for_threeStepDeletionStages
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) (y : C)
    (Allowed : Set C → Prop)
    (Control : Set C →
      FiniteIndecomposableModuleFamily (k := k) (C := C) → Prop)
    (exists_control : ∀ D, Allowed D → ∃ V, Control D V)
    (control_invariant :
      ∀ {D E}, Allowed D → Allowed E →
        deletionSurvivingIndices (k := k) C
            (finiteThreeStepControlFamily hlocal y) D =
          deletionSurvivingIndices (k := k) C
            (finiteThreeStepControlFamily hlocal y) E →
        ∀ {V}, Control D V ↔ Control E V)
    (control_upward :
      ∀ D, Allowed D → ∀ {V U}, Control D V →
        V.isoClosure ⊆ U.isoClosure → Control D U) :
    ∃ U : FiniteIndecomposableModuleFamily (k := k) (C := C),
      ∀ D, Allowed D → Control D U :=
  exists_uniformControlFamily_of_survivorSignatures (k := k) C
    (finiteThreeStepControlFamily hlocal y) Allowed Control
    exists_control control_invariant control_upward

end MagnitudeConjecture.ObjectDeletion
