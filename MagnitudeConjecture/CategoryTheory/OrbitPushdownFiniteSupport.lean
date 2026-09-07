import MagnitudeConjecture.CategoryTheory.OrbitPushdownDegree
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite support of degrees extracted from orbit push-down maps

A linear map from a finite-dimensional space into a direct sum has only
finitely many nonzero component maps.  Applied objectwise to a transformation
between Gabriel push-downs, and then combined with finite object support, this
packages all extracted degree components as a genuine shift-orbit morphism.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe uK uV uI uW

variable {k : Type uK} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {I : Type uI}
variable (W : I → Type uW)
variable [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

/-- A linear map from a finite-dimensional space into a direct sum has only
finitely many nonzero component maps. -/
theorem finite_nonzero_components_of_finiteDimensional
    [FiniteDimensional k V]
    (f : V →ₗ[k] DirectSum I W) :
    {i : I | (DirectSum.component k I W i).comp f ≠ 0}.Finite := by
  classical
  let b := Module.finBasis k V
  let S : Finset I := Finset.univ.biUnion fun j ↦ (f (b j)).support
  apply S.finite_toSet.subset
  intro i hi
  by_contra hiS
  apply hi
  apply b.ext
  intro j
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  change (f (b j)) i = 0
  have hij : i ∉ (f (b j)).support := by
    intro hij
    exact hiS (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hij⟩)
  simpa [DFinsupp.mem_support_toFun] using hij

universe u v w uM

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {A : Type w} [AddGroup A]
variable (D : ShiftMkCore C A)
variable [∀ a : A, (D.F a).Additive]
variable [∀ a : A, (D.F a).Linear k]
variable {M N : CategoryTheory.Functor C (ModuleCat.{uM} k)}
variable [M.Additive] [M.Linear k] [N.Additive] [N.Linear k]

/-- At a finite-dimensional source value, only finitely many extracted
degrees can be nonzero. -/
theorem finite_orbitPushdownNatTransDegreeAppLinear_ne
    (X : C) [FiniteDimensional k (M.obj X)] :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    ∀ (α : orbitPushdown (A := A) M ⟶ orbitPushdown (A := A) N),
      {a : A | orbitPushdownNatTransDegreeAppLinear D a X α ≠ 0}.Finite := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  classical
  intro α
  let f : M.obj X →ₗ[k] DirectSum A
      (fun b ↦ N.obj ((D.F b).obj X)) :=
    (α.app X).hom.comp
      ((orbitPushdownLof M X 0).comp
        (M.map ((shiftFunctorZero C A).inv.app X)).hom)
  have hf := finite_nonzero_components_of_finiteDimensional
    (fun b ↦ N.obj ((D.F b).obj X)) f
  have hpre := hf.preimage (neg_injective (G := A)).injOn
  simpa only [Set.preimage_setOf_eq, f,
    orbitPushdownNatTransDegreeAppLinear] using hpre

/-- For a finite-dimensional source module, only finitely many extracted raw
module transformations can be nonzero. -/
theorem finite_orbitPushdownNatTransDegreeRaw_ne
    (M₀ : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    ∀ (α : orbitPushdown (A := A) M₀.obj.obj ⟶
        orbitPushdown (A := A) N₀.obj),
      {a : A | orbitPushdownNatTransDegreeRaw D a α ≠ 0}.Finite := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  classical
  intro α
  let S := moduleSupport k M₀.obj.obj
  let T : C → Set A := fun X ↦
    {a : A | orbitPushdownNatTransDegreeAppLinear D a X α ≠ 0}
  have hT (X : C) : (T X).Finite :=
    finite_orbitPushdownNatTransDegreeAppLinear_ne D X α
  have hUnion : (⋃ X ∈ S, T X).Finite :=
    (finite_moduleSupport k M₀).biUnion fun X _ ↦ hT X
  apply hUnion.subset
  intro a ha
  have hex : ∃ X : C,
      (orbitPushdownNatTransDegreeRaw D a α).app X ≠ 0 := by
    by_contra hn
    apply ha
    apply NatTrans.ext
    funext X
    exact not_ne_iff.mp (not_exists.mp hn X)
  obtain ⟨X, hX⟩ := hex
  have hXS : X ∈ S := by
    change Nontrivial (M₀.obj.obj.obj X)
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply hX
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0]
    simp
  have hXT : a ∈ T X := by
    change orbitPushdownNatTransDegreeAppLinear D a X α ≠ 0
    intro hzero
    apply hX
    apply ModuleCat.hom_ext
    exact hzero
  exact Set.mem_iUnion_of_mem X
    (Set.mem_iUnion_of_mem hXS hXT)

/-- Only finitely many shifted module maps extracted from a push-down
transformation can be nonzero. -/
theorem finite_linearModuleOrbitPushdownDegree_ne
    (M₀ : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    ∀ (α : (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀.obj ⟶
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀),
      {a : A | linearModuleOrbitPushdownDegree D M₀.obj N₀ a α ≠ 0}.Finite := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  intro α
  apply (finite_orbitPushdownNatTransDegreeRaw_ne D M₀ N₀ α.hom).subset
  intro a ha
  by_contra hraw
  have hraw' : orbitPushdownNatTransDegreeRaw D a α.hom = 0 :=
    not_ne_iff.mp hraw
  apply ha
  apply ObjectProperty.hom_ext
  simp [linearModuleOrbitPushdownDegree, hraw']

/-- Package all degree components extracted from a push-down transformation
as a finite-support shift-orbit morphism. -/
noncomputable def linearModuleOrbitPushdownDegrees
    (M₀ : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    ((linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀.obj ⟶
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀) →
      ShiftOrbitHom A M₀.obj N₀ := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  intro α
  let h := finite_linearModuleOrbitPushdownDegree_ne D M₀ N₀ α
  exact DFinsupp.mk h.toFinset fun a ↦
    linearModuleOrbitPushdownDegree D M₀.obj N₀ a.1 α

@[simp]
theorem linearModuleOrbitPushdownDegrees_apply
    (M₀ : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    ∀ (α : (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀.obj ⟶
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀)
      (a : A),
      linearModuleOrbitPushdownDegrees D M₀ N₀ α a =
        linearModuleOrbitPushdownDegree D M₀.obj N₀ a α := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  intro α a
  unfold linearModuleOrbitPushdownDegrees
  rw [DFinsupp.mk_apply]
  split_ifs with ha
  · rfl
  · symm
    exact not_ne_iff.mp fun hne ↦ ha
      ((finite_linearModuleOrbitPushdownDegree_ne D M₀ N₀ α).mem_toFinset.mpr hne)

/-- All extracted degrees form a linear map into the finite-support direct
sum. -/
noncomputable def linearModuleOrbitPushdownDegreesLinear
    (M₀ : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N₀ : LinearModuleCategory.{u, v, uK, uM} (C := C) k) :
    letI := hasShiftMk C A D
    letI := shiftMkCoreAdditiveShift D
    letI := shiftMkCoreLinearShift (k := k) D
    letI := isLinearModule_stableUnderShift (k := k) D
    letI := linearModuleCategoryHasShift (k := k) D
    ((linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj M₀.obj ⟶
        (linearModuleOrbitPushdown (k := k) (C := C) (A := A)).obj N₀) →ₗ[k]
      ShiftOrbitHom A M₀.obj N₀ := by
  letI := hasShiftMk C A D
  letI := shiftMkCoreAdditiveShift D
  letI := shiftMkCoreLinearShift (k := k) D
  letI := isLinearModule_stableUnderShift (k := k) D
  letI := linearModuleCategoryHasShift (k := k) D
  classical
  exact
    { toFun := linearModuleOrbitPushdownDegrees D M₀ N₀
      map_add' := by
        intro α β
        apply DirectSum.ext
        intro a
        simp only [linearModuleOrbitPushdownDegrees_apply,
          DirectSum.add_apply]
        exact (linearModuleOrbitPushdownDegreeLinear D M₀.obj N₀ a).map_add α β
      map_smul' := by
        intro r α
        apply DirectSum.ext
        intro a
        rw [linearModuleOrbitPushdownDegrees_apply]
        change linearModuleOrbitPushdownDegree D M₀.obj N₀ a (r • α) =
          r • (linearModuleOrbitPushdownDegrees D M₀ N₀ α a)
        rw [linearModuleOrbitPushdownDegrees_apply]
        exact (linearModuleOrbitPushdownDegreeLinear D M₀.obj N₀ a).map_smul r α }

end MagnitudeConjecture.CoveringHom
