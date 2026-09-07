import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotientAlgebraEquivInequality
import MagnitudeConjecture.CategoryTheory.StandardCoveringCategoryAlgebra

/-!
# Covering inequalities transported across an algebra equivalence
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.StandardCovering

open MagnitudeConjecture.CoveringHom

universe u

variable {k B : Type u} [Field k] [IsAlgClosed k]
variable [Ring B] [Algebra k B] [FiniteDimensional k B]
  [IsNoetherianRing Bᵐᵒᵖ]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C]
variable {G : Type u} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- Transport the covering-average primitive-deletion inequality from the
orbit-category algebra to any algebraically equivalent finite-dimensional
algebra. -/
theorem primitiveQuotient_ambientARSurplus_le_of_admissible_of_algEquiv
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    [Group.ResiduallyFinite G]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (S : RightModule.FiniteIndecomposableSkeleton k B)
    (f : orbitCategoryAlgebra
      (k := k) D H.locallyBounded.finiteCovariantRepresentables ≃ₐ[k] B)
    (x : C) :
    let hP := H.locallyBounded.finiteCovariantRepresentables
    let hlocal := H.locallyBounded.localEndomorphismRings
    let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hP hlocal
    let P := orbitCategoryProjectorPrimitive
      (k := k) D hP hlocal hfree x
    letI : IsNoetherianRing
        (RightModule.primitiveQuotientAlgebra
          (f (orbitCategoryProjector (k := k) D hP x)))ᵐᵒᵖ :=
      IsNoetherianRing.of_finite k _
    (S.primitiveQuotientFiniteIndecomposableSkeleton (P.mapAlgEquiv f)
      ).ambientARSurplus ≤ S.ambientARSurplus := by
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let hlocal := H.locallyBounded.localEndomorphismRings
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let e := orbitCategoryProjector (k := k) D hP x
  let P := orbitCategoryProjectorPrimitive
    (k := k) D hP hlocal hfree x
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra (f e))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Salg := S.mapAlgEquiv f.symm
  have hcover :=
    primitiveQuotient_ambientARSurplus_le_ambientARSurplus_of_admissible
      (k := k) D H Salg x
  exact S.primitiveQuotient_ambientARSurplus_le_mapAlgEquiv f e P hcover

/-- Transport the equality clause across an algebra equivalence and apply the
covering-average one-dimensional-fibre theorem. -/
theorem finrank_obj_eq_one_of_ambientARSurplus_eq_of_admissible_of_algEquiv
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    [Group.ResiduallyFinite G]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (S : RightModule.FiniteIndecomposableSkeleton k B)
    (f : orbitCategoryAlgebra
      (k := k) D H.locallyBounded.finiteCovariantRepresentables ≃ₐ[k] B)
    (x : C)
    (hEquality :
      let hP := H.locallyBounded.finiteCovariantRepresentables
      let hlocal := H.locallyBounded.localEndomorphismRings
      let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
        (k := k) hP hlocal
      let P := orbitCategoryProjectorPrimitive
        (k := k) D hP hlocal hfree x
      letI : IsNoetherianRing
          (RightModule.primitiveQuotientAlgebra
            (f (orbitCategoryProjector (k := k) D hP x)))ᵐᵒᵖ :=
        IsNoetherianRing.of_finite k _
      S.ambientARSurplus =
        (S.primitiveQuotientFiniteIndecomposableSkeleton (P.mapAlgEquiv f)
          ).ambientARSurplus)
    (M : FiniteDimensionalModuleCategory.{0, u, u, u} (C := C) k)
    (hM : Indecomposable M)
    (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
  let hP := H.locallyBounded.finiteCovariantRepresentables
  let hlocal := H.locallyBounded.localEndomorphismRings
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let e := orbitCategoryProjector (k := k) D hP x
  let P := orbitCategoryProjectorPrimitive
    (k := k) D hP hlocal hfree x
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra (f e))ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let Salg := S.mapAlgEquiv f.symm
  have hCoverEquality :=
    S.ambientARSurplus_eq_primitiveQuotient_mapAlgEquiv f e P hEquality
  exact
    finrank_obj_eq_one_of_ambientARSurplus_eq_primitiveQuotient_of_admissible
      (k := k) D H Salg x hCoverEquality M hM hMx

end MagnitudeConjecture.StandardCovering
