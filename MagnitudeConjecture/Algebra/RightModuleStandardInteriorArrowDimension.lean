import MagnitudeConjecture.Algebra.RightModuleStandardInteriorIrreducibleSpace
import MagnitudeConjecture.Algebra.RightModuleStandardGradedArrowDimension

/-! # Interior supported irreducible dimensions count ordinary arrows -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance interiorArrowQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance interiorArrowFintype (x y : Fin S.n) :
    Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- At an interior target, the supported quotient retains exactly the ordinary
arrows from source labels whose shift is one higher. -/
def standardFormSupported_interior_arrowDimension
    {m : ℕ} (a b : S.standardFormSupportedLabel m)
    (ht0 : 0 ≤ b.2.val)
    (htm : b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight) :=
  (S.standardFormSupported_interior_irreducible_finrank a b ht0 htm).trans
    (S.standardFormGraded_irreducible_arrowMultiplicity
      (MeshCategory.obj (k := k) S.standardFormRightMeshData a.1)
      (MeshCategory.obj (k := k) S.standardFormRightMeshData b.1) a.2.val b.2.val)

/-- Every ordinary source label has its degree-one shift inside an interior
interval, whether or not that particular label contributes an arrow. -/
theorem standardFormSupported_interior_nextShift {m : ℕ}
    (b : S.standardFormSupportedLabel m) (ht0 : 0 ≤ b.2.val)
    (htm : b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight)
    (i : Fin S.n) :
    b.2.val + 1 ∈ GradedInterval.allowedShifts m
      (S.standardFormSupportWindow i).lower (S.standardFormSupportWindow i).upper := by
  have hpos := S.standardFormIntervalControlHeight_pos
  exact GradedInterval.incoming_shift_allowed m S.standardFormIntervalControlHeight
    _ _ (S.standardFormSupportWindow_upper_le_control i) (b.2.val + 1) b.2.val
    ht0 htm (by omega) (by omega)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
