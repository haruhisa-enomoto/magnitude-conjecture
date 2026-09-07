import QuotientSubmoduleEquidistribution.RepresentationTheory.ContragredientDuality
import MagnitudeConjecture.CategoryTheory.OppositeLinear

/-!
# Linearity of finite-dimensional contragredient duality

The vendored contragredient equivalence is packaged additively.  Its action
on morphisms is also linear over the central coefficient field.  Recording
that fact lets a linear Morita equivalence be transported to the opposite
module categories without changing scalars.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace QuotientSubmoduleEquidistribution.Contragredient

universe u

variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable [FiniteDimensional k R]

local instance moduleCategoryOppositeLinear :
    CategoryTheory.Linear k (FGModuleCat.{u} R)ᵒᵖ :=
  MagnitudeConjecture.CoveringHom.oppositeLinear

local instance oppositeModuleCategoryOppositeLinear :
    CategoryTheory.Linear k (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ :=
  MagnitudeConjecture.CoveringHom.oppositeLinear

noncomputable instance dualFunctor_additive :
    ((dualFunctor k R :
      (FGModuleCat.{u} R)ᵒᵖ ⥤ FGModuleCat.{u} Rᵐᵒᵖ)).Additive where
  map_add := by
    intro X Y f g
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    letI : Module k Y.unop := Module.restrictScalars k R Y.unop
    letI : Module k X.unop := Module.restrictScalars k R X.unop
    let E := forwardInnerDualEquiv k R Y.unop
    apply E.injective
    apply LinearMap.coe_injective
    funext x
    change
      (forwardInnerDualEquiv k R X.unop phi)
          ((f + g).unop.hom.hom x) =
        (forwardInnerDualEquiv k R X.unop phi)
            (f.unop.hom.hom x) +
          (forwardInnerDualEquiv k R X.unop phi)
            (g.unop.hom.hom x)
    have hin :
        (f + g).unop.hom.hom x =
          f.unop.hom.hom x + g.unop.hom.hom x := rfl
    rw [hin, map_add]

noncomputable instance dualFunctor_linear :
    ((dualFunctor k R :
      (FGModuleCat.{u} R)ᵒᵖ ⥤ FGModuleCat.{u} Rᵐᵒᵖ)).Linear k where
  map_smul := by
    intro X Y f r
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    letI : Module k Y.unop := Module.restrictScalars k R Y.unop
    letI : Module k X.unop := Module.restrictScalars k R X.unop
    let E := forwardInnerDualEquiv k R Y.unop
    have hout :
        ((r • (dualFunctor k R).map f).hom.hom phi) =
          @SMul.smul k _
            (Module.restrictScalars k Rᵐᵒᵖ
              ((dualFunctor k R).obj Y)).toSMul r
                (((dualFunctor k R).map f).hom.hom phi) := rfl
    rw [hout]
    apply E.injective
    have hE :
        E (@SMul.smul k _
            (Module.restrictScalars k Rᵐᵒᵖ
              ((dualFunctor k R).obj Y)).toSMul r
                (((dualFunctor k R).map f).hom.hom phi)) =
          r • E (((dualFunctor k R).map f).hom.hom phi) :=
      E.map_smul r (((dualFunctor k R).map f).hom.hom phi)
    rw [hE]
    apply LinearMap.coe_injective
    funext x
    change
      (forwardInnerDualEquiv k R X.unop phi)
          ((r • f).unop.hom.hom x) =
        r * (forwardInnerDualEquiv k R X.unop phi)
          (f.unop.hom.hom x)
    have hin :
        (r • f).unop.hom.hom x =
          @SMul.smul k _
            (Module.restrictScalars k R X.unop).toSMul r
              (f.unop.hom.hom x) := rfl
    rw [hin]
    exact phi.map_smul r (f.unop.hom.hom x)

noncomputable instance reverseDualFunctor_additive :
    ((reverseDualFunctor k R :
      (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ⥤ FGModuleCat.{u} R)).Additive where
  map_add := by
    intro X Y f g
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    letI : Module k Y.unop := Module.restrictScalars k Rᵐᵒᵖ Y.unop
    letI : Module k X.unop := Module.restrictScalars k Rᵐᵒᵖ X.unop
    let E := reverseInnerDualEquiv k R Y.unop
    apply E.injective
    apply LinearMap.coe_injective
    funext x
    change
      (reverseInnerDualEquiv k R X.unop phi)
          ((f + g).unop.hom.hom x) =
        (reverseInnerDualEquiv k R X.unop phi)
            (f.unop.hom.hom x) +
          (reverseInnerDualEquiv k R X.unop phi)
            (g.unop.hom.hom x)
    have hin :
        (f + g).unop.hom.hom x =
          f.unop.hom.hom x + g.unop.hom.hom x := rfl
    rw [hin, map_add]

noncomputable instance reverseDualFunctor_linear :
    ((reverseDualFunctor k R :
      (FGModuleCat.{u} Rᵐᵒᵖ)ᵒᵖ ⥤ FGModuleCat.{u} R)).Linear k where
  map_smul := by
    intro X Y f r
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    letI : Module k Y.unop := Module.restrictScalars k Rᵐᵒᵖ Y.unop
    letI : Module k X.unop := Module.restrictScalars k Rᵐᵒᵖ X.unop
    let E := reverseInnerDualEquiv k R Y.unop
    have hout :
        ((r • (reverseDualFunctor k R).map f).hom.hom phi) =
          @SMul.smul k _
            (Module.restrictScalars k R
              ((reverseDualFunctor k R).obj Y)).toSMul r
                (((reverseDualFunctor k R).map f).hom.hom phi) := rfl
    rw [hout]
    apply E.injective
    have hE :
        E (@SMul.smul k _
            (Module.restrictScalars k R
              ((reverseDualFunctor k R).obj Y)).toSMul r
                (((reverseDualFunctor k R).map f).hom.hom phi)) =
          r • E (((reverseDualFunctor k R).map f).hom.hom phi) :=
      E.map_smul r (((reverseDualFunctor k R).map f).hom.hom phi)
    rw [hE]
    apply LinearMap.coe_injective
    funext x
    change
      (reverseInnerDualEquiv k R X.unop phi)
          ((r • f).unop.hom.hom x) =
        r * (reverseInnerDualEquiv k R X.unop phi)
          (f.unop.hom.hom x)
    have hin :
        (r • f).unop.hom.hom x =
          @SMul.smul k _
            (Module.restrictScalars k Rᵐᵒᵖ X.unop).toSMul r
              (f.unop.hom.hom x) := rfl
    rw [hin]
    exact phi.map_smul r (f.unop.hom.hom x)

noncomputable instance dualityEquivalence_functor_additive :
    (dualityEquivalence k R).functor.Additive := by
  change (dualFunctor k R).Additive
  infer_instance

noncomputable instance dualityEquivalence_functor_linear :
    (dualityEquivalence k R).functor.Linear k := by
  change (dualFunctor k R).Linear k
  infer_instance

noncomputable instance dualityEquivalence_inverse_additive :
    (dualityEquivalence k R).inverse.Additive := by
  change (reverseDualFunctor k R).rightOp.Additive
  infer_instance

noncomputable instance dualityEquivalence_inverse_linear :
    (dualityEquivalence k R).inverse.Linear k := by
  change (reverseDualFunctor k R).rightOp.Linear k
  infer_instance

end QuotientSubmoduleEquidistribution.Contragredient
