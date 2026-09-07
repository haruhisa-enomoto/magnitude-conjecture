import MagnitudeConjecture.CategoryTheory.AdmissibleModuleCategory
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStage

/-!
# Admissibility of the finite-cover deletion stages

Every intermediate stage in the ordered deletion of a deck orbit is a
literal object-deletion quotient, hence remains admissible.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C]
variable {N : Subgroup G}

/-- Every ordered subgroup-orbit deletion stage inherits admissibility from
the ambient covering category. -/
theorem isAdmissible_stage
    (H : IsAdmissible (k := k) (C := C))
    {m : ℕ} (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :
    IsAdmissible (k := k)
      (C := StageCategory (k := k) N representative x j) :=
  isAdmissible_deletion (k := k) (C := C)
    (stageDeletedSet N representative x j) H

end MagnitudeConjecture.ObjectDeletion
