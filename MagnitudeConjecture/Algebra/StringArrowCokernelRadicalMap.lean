import MagnitudeConjecture.Algebra.StringArrowBranchProjection
import MagnitudeConjecture.Algebra.StringArrowBranchEvaluation

/-! # The radical map of a string-arrow cokernel -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

noncomputable local instance arrowRadicalMapAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance arrowRadicalMapAlgebraOppositeIsNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- The projective radical maps linearly onto the radical of the arrow
cokernel. -/
def arrowCokernelRadicalLinearMap
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y) →ₗ[
      P.quotientCategoryAlgebraᵐᵒᵖ]
      Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.arrowCokernelFGObj a) := by
  let J : Submodule P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) :=
    Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y)
  let JV : Submodule P.quotientCategoryAlgebraᵐᵒᵖ
      (P.arrowCokernelFGObj a) :=
    Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
      (P.arrowCokernelFGObj a)
  exact
    { toFun := fun z ↦ ⟨P.arrowCokernelProjection a z.1, by
        have hEq : JV = J.map (P.arrowCokernelProjection a) := by
          change Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
              (P.representedVertexModule y ⧸ P.arrowCokernelSubmodule a) =
            J.map (P.arrowCokernelSubmodule a).mkQ
          exact Module.jacobson_quotient_of_le
            (P.arrowCokernelSubmodule_le_jacobson a)
        change P.arrowCokernelProjection a z.1 ∈ JV
        rw [hEq]
        exact ⟨z.1, z.2, rfl⟩⟩
      map_add' := by
        intro z w
        apply Subtype.ext
        exact (P.arrowCokernelProjection a).map_add z.1 w.1
      map_smul' := by
        intro c z
        apply Subtype.ext
        exact (P.arrowCokernelProjection a).map_smul c z.1 }

/-- The projective radical map, bundled in the finite module category. -/
def arrowCokernelRadicalMap
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    P.representedVertexRadicalFGObj y ⟶
      FGModuleCat.of P.quotientCategoryAlgebraᵐᵒᵖ
        (Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
          (P.arrowCokernelFGObj a)) :=
  FGModuleCat.ofHom (P.arrowCokernelRadicalLinearMap a)

theorem arrowCokernelRadicalMap_surjective
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Function.Surjective (P.arrowCokernelRadicalLinearMap a) := by
  intro z
  let J := Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
    (P.representedVertexModule y)
  let JV := Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
    (P.arrowCokernelFGObj a)
  have hEq : JV = J.map (P.arrowCokernelProjection a) := by
    change Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y ⧸ P.arrowCokernelSubmodule a) =
      J.map (P.arrowCokernelSubmodule a).mkQ
    exact Module.jacobson_quotient_of_le
      (P.arrowCokernelSubmodule_le_jacobson a)
  have hz : z.1 ∈ J.map (P.arrowCokernelProjection a) := by
    rw [← hEq]
    exact z.2
  obtain ⟨w, hwJ, hw⟩ := hz
  exact ⟨⟨w, hwJ⟩, Subtype.ext hw⟩

theorem arrowCokernelRadicalMap_ker
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    LinearMap.ker (P.arrowCokernelRadicalLinearMap a) =
      LinearMap.range
        (P.arrowBranchRadicalInclusionLinearMap (Sigma.mk x a)) := by
  ext z
  constructor
  · intro hz
    rw [LinearMap.mem_ker] at hz
    have hzQ : P.arrowCokernelProjection a z.1 = 0 :=
      congrArg Subtype.val hz
    have hzU : z.1 ∈ P.arrowCokernelSubmodule a := by
      rw [← P.arrowCokernelProjection_ker a, LinearMap.mem_ker]
      exact hzQ
    let u : LinearMap.range (P.representedArrowLinearMap a) := ⟨z.1, hzU⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact P.arrowBranchRadicalInclusionLinearMap_apply_coe (Sigma.mk x a) u
  · rintro ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change P.arrowCokernelProjection a
      (P.arrowBranchRadicalInclusionLinearMap (Sigma.mk x a) u).1 = 0
    rw [P.arrowBranchRadicalInclusionLinearMap_apply_coe]
    change LinearMap.range (P.representedArrowLinearMap a) at u
    change (P.arrowCokernelSubmodule a).mkQ u.1 = 0
    exact (Submodule.Quotient.mk_eq_zero
      (P.arrowCokernelSubmodule a)).2 u.2

end MagnitudeConjecture.BoundQuiver.StringPresentation
