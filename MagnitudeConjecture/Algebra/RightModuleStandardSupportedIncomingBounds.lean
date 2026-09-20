import MagnitudeConjecture.Algebra.RightModuleStandardSupportedCategory
import MagnitudeConjecture.Algebra.RightModuleStandardGradedIncomingBounds

/-! # Incoming shift and dimension bounds inside every supported interval -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance supportedIncomingQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance supportedIncomingArrowFintype (x y : Fin S.n) :
    Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- Passing to supported modules preserves the common incoming shift window. -/
theorem standardFormSupported_incoming_shift_bounds
    (h : ℕ) (hb : ∀ X Y : S.StandardFormMeshCategory, ∀ d : ℤ,
      d < 0 ∨ (h : ℤ) < d → S.standardFormIntegerHomGrading.component X Y d = ⊥)
    {m : ℕ} (a b : S.standardFormSupportedLabel m)
    (f : S.standardFormSupportedFamily m a ⟶ S.standardFormSupportedFamily m b)
    (hf : f ≠ 0) : b.2.val ≤ a.2.val ∧ a.2.val ≤ b.2.val + h := by
  apply S.standardFormGraded_incoming_shift_bounds h hb
    (MeshCategory.obj (k := k) S.standardFormRightMeshData a.1)
    (MeshCategory.obj (k := k) S.standardFormRightMeshData b.1) a.2.val b.2.val f.hom
  intro hz
  apply hf
  apply ObjectProperty.hom_ext
  exact hz

/-- The full supported subcategory retains exactly the ambient graded Hom space. -/
def standardFormSupportedHomEquiv {m : ℕ} (a b : S.standardFormSupportedLabel m) :
    (S.standardFormSupportedFamily m a ⟶ S.standardFormSupportedFamily m b) ≃ₗ[k]
      ((S.standardFormSupportedFamily m a).obj ⟶ (S.standardFormSupportedFamily m b).obj) where
  toFun f := f.hom
  invFun f := ⟨f⟩
  left_inv f := by cases f; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restricting to an interval leaves the fixed mesh Hom dimension as a
bound, even for pairs whose irreducibility changes at the boundary. -/
theorem standardFormSupported_hom_finrank_le {m : ℕ}
    (a b : S.standardFormSupportedLabel m) :
    Module.finrank k (S.standardFormSupportedFamily m a ⟶ S.standardFormSupportedFamily m b) ≤
      Module.finrank k (MeshCategory.obj (k := k) S.standardFormRightMeshData a.1 ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData b.1) := by
  rw [(S.standardFormSupportedHomEquiv a b).finrank_eq]
  exact S.standardFormGraded_hom_finrank_le _ _ a.2.val b.2.val

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
