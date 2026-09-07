import MagnitudeConjecture.CategoryTheory.AdmissibleModuleCategory
import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalChangeSum

/-!
# Finite convex support windows for module families

An admissible category contains the support of any finite module family,
together with one chosen base object, in a finite convex object set.  Deleting
the complementary objects gives a literal finite category.  Every module in
the family descends to that category, and restriction preserves exactly the
finite quotient of its indices by represented isomorphism classes.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- The union of the object supports of a finite indecomposable module
family. -/
def finiteModuleFamilyObjectSupport
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) : Set C :=
  ⋃ i : Fin W.n, moduleSupport k (W.obj i).obj.obj

theorem finiteModuleFamilyObjectSupport_finite
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    (finiteModuleFamilyObjectSupport (k := k) W).Finite := by
  exact Set.finite_iUnion fun i ↦ finite_moduleSupport k (W.obj i)

/-- A finite convex object window containing a base object and the supports
of every representative in a finite module family. -/
structure FiniteConvexModuleControlWindow
    (x : C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) where
  objects : Set C
  finite : objects.Finite
  base_mem : x ∈ objects
  familySupport_subset : finiteModuleFamilyObjectSupport (k := k) W ⊆ objects
  convex : IsConvexObjectSet objects

/-- Admissible finite-convex neighborhoods produce a control window for any
finite module family. -/
theorem finiteConvexModuleControlWindow_nonempty
    (H : HasFiniteConvexObjectNeighborhoods (C := C))
    (x : C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    Nonempty (FiniteConvexModuleControlWindow (k := k) x W) := by
  let T : Set C := {x} ∪ finiteModuleFamilyObjectSupport (k := k) W
  have hT : T.Finite :=
    (Set.finite_singleton x).union (finiteModuleFamilyObjectSupport_finite W)
  obtain ⟨U, hUfinite, hTU, hUconvex⟩ := H T hT
  exact ⟨
    { objects := U
      finite := hUfinite
      base_mem := hTU (by simp [T])
      familySupport_subset := fun y hy ↦ hTU (by
        exact Or.inr hy)
      convex := hUconvex }⟩

namespace FiniteConvexModuleControlWindow

variable {x : C}
variable {W : FiniteIndecomposableModuleFamily (k := k) (C := C)}

theorem obj_moduleSupport_subset
    (P : FiniteConvexModuleControlWindow (k := k) x W)
    (i : Fin W.n) :
    moduleSupport k (W.obj i).obj.obj ⊆ P.objects := by
  intro y hy
  apply P.familySupport_subset
  exact Set.mem_iUnion.mpr ⟨i, hy⟩

theorem moduleSupport_subset_of_mem_isoClosure
    (P : FiniteConvexModuleControlWindow (k := k) x W)
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : M ∈ W.isoClosure) :
    moduleSupport k M.obj.obj ⊆ P.objects := by
  obtain ⟨i, ⟨e⟩⟩ := hM
  intro y hy
  apply P.obj_moduleSupport_subset i
  let J := (IsLinearModule.{u, v, v, v} (C := C) k).ι
  let eY := (J.mapIso ((IsFiniteDimensionalModule
    (C := C) k).ι.mapIso e)).app y
  exact eY.toLinearEquiv.toEquiv.nontrivial_congr.mpr hy

/-- A three-step support window is also a support window for the preceding
two-step endpoint family, with the same finite convex object set. -/
def twoStepWindow
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C)
    (P : FiniteConvexModuleControlWindow (k := k) x
      (finiteThreeStepControlFamily hlocal x)) :
    FiniteConvexModuleControlWindow (k := k) x
      ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood hlocal 2) where
  objects := P.objects
  finite := P.finite
  base_mem := P.base_mem
  familySupport_subset := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    have hiThree :
        (((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
          hlocal 2).obj i) ∈
          (finiteThreeStepControlFamily hlocal x).isoClosure :=
      (finiteFiberControlSeed hlocal x).mem_iterateHomNeighborhood_succ_of_homInteraction
          hlocal
          (((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
            hlocal 2).obj_mem_isoClosure i)
          (((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
            hlocal 2).indecomposable i)
          (Or.inl rfl)
    exact P.moduleSupport_subset_of_mem_isoClosure hiThree hi
  convex := P.convex

end FiniteConvexModuleControlWindow

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- A module supported in `U` vanishes on the complementary deleted object
set. -/
theorem moduleVanishesOnDeleted_compl_of_moduleSupport_subset
    (U : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : moduleSupport k M.obj.obj ⊆ U) :
    ModuleVanishesOnDeleted (k := k) C Uᶜ M.obj.obj := by
  intro X hX
  rw [ModuleCat.isZero_iff_subsingleton]
  exact not_nontrivial_iff_subsingleton.mp fun hnontrivial ↦
    hX (hM hnontrivial)

/-- Deleting the complement of a finite object set has finitely many
surviving objects, even when the ambient category is infinite. -/
theorem complementDeletion_finite
    (U : Set C) (hU : U.Finite) :
    Finite (DeletionCategory (k := k) C Uᶜ) := by
  let f : DeletionCategory (k := k) C Uᶜ → U := fun X ↦
    ⟨X.obj.as, by
      have hX := X.property
      change X.obj.as ∉ Uᶜ at hX
      simpa only [Set.mem_compl_iff, not_not] using hX⟩
  letI : Finite U := hU
  exact Finite.of_injective f (by
    intro X Y hXY
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    exact congrArg Subtype.val hXY)

end MagnitudeConjecture.ObjectDeletion

namespace MagnitudeConjecture.CoveringHom.FiniteConvexModuleControlWindow

open MagnitudeConjecture.ObjectDeletion

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

variable {x : C}
variable {W : FiniteIndecomposableModuleFamily (k := k) (C := C)}

/-- Every representative in the control family vanishes outside its finite
object window. -/
theorem obj_vanishesOn_compl
    (P : FiniteConvexModuleControlWindow (k := k) x W)
    (i : Fin W.n) :
    ModuleVanishesOnDeleted (k := k) C P.objectsᶜ (W.obj i).obj.obj :=
  moduleVanishesOnDeleted_compl_of_moduleSupport_subset
    (k := k) C P.objects (W.obj i) (P.obj_moduleSupport_subset i)

/-- Restrict every representative of a finite control family to the literal
finite category obtained by deleting the complementary objects. -/
def restrictionFamily
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    FiniteIndecomposableModuleFamily
      (k := k) (C := DeletionCategory (k := k) C P.objectsᶜ) where
  n := W.n
  obj i := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C P.objectsᶜ (W.obj i) (P.obj_vanishesOn_compl C i)
  indecomposable i :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C P.objectsᶜ (W.obj i) (W.indecomposable i)
        (P.obj_vanishesOn_compl C i)

/-- An ambient isomorphism between controlled modules descends to the finite
control category. -/
noncomputable def restrictionIso
    (P : FiniteConvexModuleControlWindow (k := k) x W)
    (i j : Fin W.n) (e : W.obj i ≅ W.obj j) :
    (P.restrictionFamily C).obj i ≅ (P.restrictionFamily C).obj j := by
  let eLinear := (IsFiniteDimensionalModule (C := C) k).ι.mapIso e
  let eFunctor := (IsLinearModule.{u, v, v, v} (C := C) k).ι.mapIso eLinear
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (moduleRestrictionToDeletionIso
      (k := k) C P.objectsᶜ (W.obj i).obj.obj (W.obj j).obj.obj
        (P.obj_vanishesOn_compl C i) (P.obj_vanishesOn_compl C j) eFunctor))

/-- Restriction induces the identity-on-indices map on represented
isomorphism classes. -/
noncomputable def restrictionIsoClassMap
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    W.IsoClass → (P.restrictionFamily C).IsoClass :=
  Quotient.lift
    (fun i ↦ Quotient.mk (P.restrictionFamily C).isoSetoid i)
    (by
      intro i j hij
      apply Quotient.sound
      exact hij.map (P.restrictionIso C i j))

theorem restrictionIsoClassMap_injective
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    Function.Injective (P.restrictionIsoClassMap C) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ i =>
      induction r using Quotient.inductionOn with
      | _ j =>
          apply Quotient.sound
          obtain ⟨e⟩ := Quotient.exact hqr
          let F := finiteDimensionalModuleExtensionByZero
            (k := k) C P.objectsᶜ
          let qi := finiteDimensionalModuleRestrictionExtensionIso
            (k := k) C P.objectsᶜ (W.obj i) (P.obj_vanishesOn_compl C i)
          let qj := finiteDimensionalModuleRestrictionExtensionIso
            (k := k) C P.objectsᶜ (W.obj j) (P.obj_vanishesOn_compl C j)
          exact ⟨qi.symm ≪≫ F.mapIso e ≪≫ qj⟩

theorem restrictionIsoClassMap_surjective
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    Function.Surjective (P.restrictionIsoClassMap C) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ i => exact ⟨Quotient.mk W.isoSetoid i, rfl⟩

/-- Restriction preserves exactly the finite set of represented
indecomposable isomorphism classes. -/
noncomputable def restrictionIsoClassEquiv
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    W.IsoClass ≃ (P.restrictionFamily C).IsoClass :=
  Equiv.ofBijective (P.restrictionIsoClassMap C)
    ⟨P.restrictionIsoClassMap_injective C,
      P.restrictionIsoClassMap_surjective C⟩

/-- Reindex a sum over the restricted control family by the original
represented isomorphism classes. -/
theorem sum_isoClass_restrictionFamily
    (P : FiniteConvexModuleControlWindow (k := k) x W)
    (f : (P.restrictionFamily C).IsoClass → ℤ) :
    (∑ q, f q) = ∑ q, f (P.restrictionIsoClassMap C q) := by
  exact (Equiv.sum_comp (P.restrictionIsoClassEquiv C) f).symm

/-- If a deletion-stage module extends to an isomorphism class represented
by the controlled ambient family, then it is represented by the restricted
family itself. -/
theorem mem_restrictionFamily_isoClosure_of_extension_mem_isoClosure
    (P : FiniteConvexModuleControlWindow (k := k) x W)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C P.objectsᶜ) k)
    (hM : (finiteDimensionalModuleExtensionByZero
      (k := k) C P.objectsᶜ).obj M ∈ W.isoClosure) :
    M ∈ (P.restrictionFamily C).isoClosure := by
  obtain ⟨i, ⟨e⟩⟩ := hM
  let F := finiteDimensionalModuleExtensionByZero
    (k := k) C P.objectsᶜ
  let qi := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C P.objectsᶜ (W.obj i) (P.obj_vanishesOn_compl C i)
  exact ⟨i, ⟨F.preimageIso (qi.trans e)⟩⟩

end FiniteConvexModuleControlWindow
