import MagnitudeConjecture.Algebra.CoordinateThinModule
import MagnitudeConjecture.Algebra.BiserialModule

/-!
# Coordinate-thin consequences for local modules

Small reusable consequences of the global all-indecomposables-coordinate-thin
hypothesis for finitely generated modules with simple top.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u w

variable {k A : Type u} {ι : Type w}
variable [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- A finitely generated module with simple top is one of the
indecomposables controlled by the all-coordinate-thin premise. -/
theorem coordinateThin_of_simpleTop
    (e : ι → A)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (W : FinitelyGeneratedCategory A)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (W ⧸ Module.jacobson Aᵐᵒᵖ W)) :
    IsCoordinateThin (k := k) e W := by
  have hindModule :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ W :=
    IsUniserialModule.isIndecomposableModule_of_simpleTop htop
  exact H W
    ((FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) W).mp hindModule)

/-- Under the global coordinate-thin premise, the simple top of a local
module is nonisomorphic to every nonzero submodule of its radical. -/
theorem nonisomorphic_top_and_nonzero_jacobson_submodule_of_simpleTop
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (W : FinitelyGeneratedCategory A)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (W ⧸ Module.jacobson Aᵐᵒᵖ W))
    (P : Submodule Aᵐᵒᵖ W) (hPne : P ≠ ⊥)
    (hPJ : P ≤ Module.jacobson Aᵐᵒᵖ W) :
    ¬ Nonempty
      ((W ⧸ Module.jacobson Aᵐᵒᵖ W) ≃ₗ[Aᵐᵒᵖ] P) := by
  rintro ⟨hTopP⟩
  exact nonisomorphic_submodule_and_top_of_coordinateThin
    (k := k) e hall W (coordinateThin_of_simpleTop e H W htop)
      P hPne hPJ ⟨hTopP.symm⟩

/-- Under a complete coordinate family, a simple-top module cannot contain
the repeated self-subquotient used by any obstruction construction. -/
theorem no_repeatedSelfSubquotient_of_simpleTop_of_all_coordinateThin
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (W : FinitelyGeneratedCategory A)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (W ⧸ Module.jacobson Aᵐᵒᵖ W)) :
    ¬ HasRepeatedSelfSubquotient W := by
  have hindModule :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ W :=
    IsUniserialModule.isIndecomposableModule_of_simpleTop htop
  have hind : Indecomposable W :=
    (FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) W).mp hindModule
  exact no_repeatedSelfSubquotient_of_all_coordinateThin
    (k := k) e hall H W hind

/-- Two disjoint simple submodules of a coordinate-thin local module are
nonisomorphic. -/
theorem nonisomorphic_disjoint_simple_submodules_of_simpleTop
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (H : AllIndecomposablesCoordinateThin (k := k) e)
    (W : FinitelyGeneratedCategory A)
    (htop : IsSimpleModule Aᵐᵒᵖ
      (W ⧸ Module.jacobson Aᵐᵒᵖ W))
    (P Q : Submodule Aᵐᵒᵖ W)
    (hP : IsSimpleModule Aᵐᵒᵖ P)
    (hinf : P ⊓ Q = ⊥) :
    ¬ Nonempty (P ≃ₗ[Aᵐᵒᵖ] Q) := by
  rintro ⟨ePQ⟩
  letI : Nontrivial P := hP.nontrivial
  apply no_repeatedSelfSubquotient_of_simpleTop_of_all_coordinateThin
    (k := k) e hall H W htop
  exact hasRepeatedSelfSubquotient_of_disjoint_isomorphic_submodules
    W P Q hinf ePQ

end MagnitudeConjecture.RightModule
