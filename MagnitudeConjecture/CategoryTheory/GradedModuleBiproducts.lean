import MagnitudeConjecture.CategoryTheory.GradedModuleHomCategory
import MagnitudeConjecture.Graded.ShiftedProduct
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Binary biproducts of shifted graded modules -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

abbrev ShiftedModule := GradedCategory.DegreeObject (homGrading (R := R) :
  GradedCategory.HomGrading k (FiniteGradedModule.{u,v} R))

/-- Realize both degree labels in the grading of the ordinary module product. -/
def sumObject (X Y : ShiftedModule.{u,v} (R := R)) : ShiftedModule.{u,v} (R := R) :=
  ⟨{ module := ModuleCat.of A (X.obj.module × Y.obj.module)
     finite := inferInstance
     grading := X.obj.grading.shiftedProduct Y.obj.grading X.degree Y.degree }, 0⟩

def sumBicone (X Y : ShiftedModule.{u,v} (R := R)) : BinaryBicone X Y where
  pt := sumObject X Y
  fst := ⟨LinearMap.fst A _ _, by
    intro d x hx
    change x.1 ∈ X.obj.grading.component (d + (0 - X.degree))
    change x.1 ∈ X.obj.grading.component (d - X.degree) ∧ _ at hx
    simpa [sub_eq_add_neg] using hx.1⟩
  snd := ⟨LinearMap.snd A _ _, by
    intro d x hx
    change x.2 ∈ Y.obj.grading.component (d + (0 - Y.degree))
    change _ ∧ x.2 ∈ Y.obj.grading.component (d - Y.degree) at hx
    simpa [sub_eq_add_neg] using hx.2⟩
  inl := ⟨LinearMap.inl A _ _, by
    intro d x hx
    change x ∈ X.obj.grading.component (d + (X.degree - 0) - X.degree) ∧
      (0 : Y.obj.module) ∈ Y.obj.grading.component (d + (X.degree - 0) - Y.degree)
    exact ⟨by simpa using hx, (Y.obj.grading.component _).zero_mem⟩⟩
  inr := ⟨LinearMap.inr A _ _, by
    intro d x hx
    change (0 : X.obj.module) ∈ X.obj.grading.component (d + (Y.degree - 0) - X.degree) ∧
      x ∈ Y.obj.grading.component (d + (Y.degree - 0) - Y.degree)
    exact ⟨(X.obj.grading.component _).zero_mem, by simpa using hx⟩⟩
  inl_fst := by apply Subtype.ext; rfl
  inl_snd := by apply Subtype.ext; rfl
  inr_fst := by apply Subtype.ext; rfl
  inr_snd := by apply Subtype.ext; rfl

instance : HasBinaryBiproducts (ShiftedModule.{u,v} (R := R)) where
  has_binary_biproduct X Y := hasBinaryBiproduct_of_total (sumBicone X Y) (by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (add_zero x.1) (zero_add x.2))

end MagnitudeConjecture.Graded.FiniteGradedModule
