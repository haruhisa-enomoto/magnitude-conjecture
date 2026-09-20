import MagnitudeConjecture.CategoryTheory.GradedModuleDecomposition
import MagnitudeConjecture.Graded.ShiftRigidity

/-! # Supports of shifted graded modules and their direct summands -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- The physical degrees of a module after applying its external shift. -/
def shiftedSupport (X : ShiftedModule.{u,u} (R := R)) : Finset ℤ :=
  X.obj.grading.toVectorGrading.support.image (fun d ↦ d + X.degree)

/-- Injective homogeneous maps cannot remove a nonzero source component. -/
theorem shiftedSupport_subset_of_injective {X Y : ShiftedModule.{u,u} (R := R)}
    (f : X ⟶ Y) (hinj : Function.Injective (fun x : X.obj.module ↦ (f.val : X.obj.module →ₗ[A] Y.obj.module).toFun x)) : shiftedSupport X ⊆ shiftedSupport Y := by
  let l : X.obj.module →ₗ[A] Y.obj.module := f.val
  intro d hd
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
  have hi' := (X.obj.grading.toVectorGrading.mem_support_iff i).mp hi
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi'
  have hm := f.property i x hx
  have hn : Y.obj.grading.component (i + (X.degree - Y.degree)) ≠ ⊥ := by
    intro hz
    rw [hz] at hm
    have hfx : l x = l 0 := by simpa only [map_zero, Submodule.mem_bot] using hm
    exact hx0 (hinj hfx)
  apply Finset.mem_image.mpr
  exact ⟨i + (X.degree - Y.degree),
    (Y.obj.grading.toVectorGrading.mem_support_iff _).mpr hn, by omega⟩

/-- A graded direct summand has support contained in the ambient module. -/
theorem shiftedSupport_subset_of_splitMono {X Y : ShiftedModule.{u,u} (R := R)}
    (f : X ⟶ Y) [IsSplitMono f] : shiftedSupport X ⊆ shiftedSupport Y := by
  apply shiftedSupport_subset_of_injective f
  have he := congrArg Subtype.val (IsSplitMono.id f)
  apply Function.LeftInverse.injective (g := fun y : Y.obj.module ↦ ((retraction f).val : Y.obj.module →ₗ[A] X.obj.module).toFun y)
  intro x
  exact LinearMap.congr_fun he x

/-- Graded isomorphisms preserve the exact shifted support. -/
theorem shiftedSupport_eq_of_iso {X Y : ShiftedModule.{u,u} (R := R)} (e : X ≅ Y) :
    shiftedSupport X = shiftedSupport Y :=
  Finset.Subset.antisymm (shiftedSupport_subset_of_splitMono e.hom)
    (shiftedSupport_subset_of_splitMono e.inv)

/-- Modules whose physical support lies in the integer interval [0,m]. -/
def SupportedIn (m : ℕ) (X : ShiftedModule.{u,u} (R := R)) : Prop :=
  ∀ d ∈ shiftedSupport X, 0 ≤ d ∧ d ≤ m

theorem supportedIn_of_splitMono {m : ℕ} {X Y : ShiftedModule.{u,u} (R := R)}
    (f : X ⟶ Y) [IsSplitMono f] (hY : SupportedIn m Y) : SupportedIn m X :=
  fun d hd ↦ hY d (shiftedSupport_subset_of_splitMono f hd)

theorem supportedIn_iff_of_iso {m : ℕ} {X Y : ShiftedModule.{u,u} (R := R)} (e : X ≅ Y) :
    SupportedIn m X ↔ SupportedIn m Y := by
  unfold SupportedIn
  rw [shiftedSupport_eq_of_iso e]

end MagnitudeConjecture.Graded.FiniteGradedModule
