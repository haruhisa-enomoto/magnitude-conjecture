import MagnitudeConjecture.Algebra.BiserialCommonRadicalCokernel

/-!
# Common-radical extensions from uniserial branch successors

A maximal nonsimple indecomposable submodule of a branch intersection has
exactly the expected intersection in any two immediate uniserial successors.
This supplies the cross-kernel equality needed by the common-radical
diagonal-cokernel obstruction.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- If two ambient submodules meet in `E` and `E` is the intrinsic radical
of the second, then projection of the second to the quotient by the first
has precisely that radical as kernel. -/
theorem crossKernel_eq_jacobson_of_inf_eq
    (E C D : Submodule R M)
    (hinf : C ⊓ D = E)
    (hDrad : E.comap D.subtype = Module.jacobson R D) :
    (C.mkQ.comp D.subtype).ker = Module.jacobson R D := by
  have hker : (C.mkQ.comp D.subtype).ker = C.comap D.subtype := by
    ext x
    change C.mkQ x.1 = 0 ↔ x.1 ∈ C
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [hker]
  calc
    C.comap D.subtype = E.comap D.subtype := by
      ext x
      constructor
      · intro hx
        have hxinf : (x.1 : M) ∈ C ⊓ D := ⟨hx, x.2⟩
        exact hinf ▸ hxinf
      · intro hx
        have hxinf : (x.1 : M) ∈ C ⊓ D := hinf.symm ▸ hx
        exact hxinf.1
    _ = Module.jacobson R D := hDrad

end MagnitudeConjecture

namespace MagnitudeConjecture.RightModule

universe u w

variable {k A : Type u} {ι : Type w}
variable [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- If a nonsimple indecomposable intersection is the full Jacobson radical
of both local branches, gluing the branches along the radical of their
intersection gives the forbidden diagonal cokernel.  No uniseriality of the
intersection is needed in this terminal case. -/
theorem false_of_nonsimple_indecomposable_intersection_eq_both_jacobson
    [Fintype ι]
    (e : ι → A) (hall : CompleteOrthogonalIdempotents e)
    (Hthin : AllIndecomposablesCoordinateThin (k := k) e)
    (L : FinitelyGeneratedCategory A)
    (hL : IsCoordinateThin (k := k) e L)
    (P Q : Submodule Aᵐᵒᵖ L)
    (hPtop : IsSimpleModule Aᵐᵒᵖ
      (P ⧸ Module.jacobson Aᵐᵒᵖ P))
    (hQtop : IsSimpleModule Aᵐᵒᵖ
      (Q ⧸ Module.jacobson Aᵐᵒᵖ Q))
    (hPjac : (infToLeftLinearMap P Q).range =
      Module.jacobson Aᵐᵒᵖ P)
    (hQjac : (infToRightLinearMap P Q).range =
      Module.jacobson Aᵐᵒᵖ Q)
    (hIind : Foundation.IsIndecomposableModule Aᵐᵒᵖ
      (P ⊓ Q : Submodule Aᵐᵒᵖ L))
    (hInonsimple : ¬ IsSimpleModule Aᵐᵒᵖ
      (P ⊓ Q : Submodule Aᵐᵒᵖ L)) :
    False := by
  let R := Aᵐᵒᵖ
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  let I := submoduleFGObj L (P ⊓ Q)
  let K : Submodule R I := Module.jacobson R I
  let iP : I →ₗ[R] submoduleFGObj L P := infToLeftLinearMap P Q
  let iQ : I →ₗ[R] submoduleFGObj L Q := infToRightLinearMap P Q
  let sP : K →ₗ[R] submoduleFGObj L P := iP.comp K.subtype
  let sQ : K →ₗ[R] submoduleFGObj L Q := iQ.comp K.subtype
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hKbot' : Module.jacobson R
        (P ⊓ Q : Submodule R L) = ⊥ := hKbot
    letI : IsSemisimpleModule R (P ⊓ Q : Submodule R L) :=
      (IsArtinian.isSemisimpleModule_iff_jacobson R
        (P ⊓ Q : Submodule R L)).mpr hKbot'
    exact hInonsimple
      (IsUniserialModule.isSimpleModule_of_semisimple_of_isIndecomposableModule
        hIind)
  letI : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hKne
  letI : Nontrivial I := hIind.nontrivial
  letI : Nontrivial (I ⧸ K) :=
    Submodule.Quotient.nontrivial_iff.mpr
      (Module.jacobson_lt_top R I).ne
  letI : Nontrivial (submoduleFGObj I K) := by
    change Nontrivial K
    infer_instance
  have hsP : Function.Injective sP :=
    (infToLeftLinearMap_injective P Q).comp K.subtype_injective
  have hsQ : Function.Injective sQ :=
    (infToRightLinearMap_injective P Q).comp K.subtype_injective
  have hcrossP : ∀ f : submoduleFGObj L P →ₗ[R]
      quotientFGObj (submoduleFGObj L Q) sQ.range, f = 0 := by
    intro f
    exact
      linearMap_to_crossBranchQuotient_eq_zero_of_coordinateThin_of_inf_left_le_jacobson
        e hall L hL P Q hPtop K hPjac.le f
  have hcrossQ : ∀ f : submoduleFGObj L Q →ₗ[R]
      quotientFGObj (submoduleFGObj L P) sP.range, f = 0 := by
    intro f
    exact
      linearMap_to_crossBranchLeftQuotient_eq_zero_of_coordinateThin_of_inf_right_le_jacobson
        e hall L hL P Q hQtop K hQjac.le f
  let h : K →ₗ[R] (submoduleFGObj L P × submoduleFGObj L Q) :=
    sP.prod sQ
  have hindModule : Foundation.IsIndecomposableModule R
      (cokernelFGObj (submoduleFGObj I K)
        (prodFGObj (submoduleFGObj L P) (submoduleFGObj L Q)) h) :=
    isIndecomposableModule_diagonalCokernel_of_crossHom_eq_zero
      (submoduleFGObj I K) (submoduleFGObj L P) (submoduleFGObj L Q)
        sP sQ hsP hsQ
        (IsUniserialModule.isIndecomposableModule_of_simpleTop hPtop)
        (IsUniserialModule.isIndecomposableModule_of_simpleTop hQtop)
        hcrossP hcrossQ
  have hind : Indecomposable
      (cokernelFGObj (submoduleFGObj I K)
        (prodFGObj (submoduleFGObj L P) (submoduleFGObj L Q)) h) :=
    (FiniteIndecomposableSkeleton.fgModule_isIndecomposableModule_iff_indecomposable
      (k := k) (A := A) _).mp hindModule
  have hnot :=
    @not_indec_diagonalSubmoduleCokernel_of_all_coordinateThin
      k A _ _ _ _ _ ι _ e hall Hthin
      I (submoduleFGObj L P) (submoduleFGObj L Q) K
      iP iQ (infToLeftLinearMap_injective P Q)
      (infToRightLinearMap_injective P Q) (by infer_instance)
  exact hnot hind

end MagnitudeConjecture.RightModule
