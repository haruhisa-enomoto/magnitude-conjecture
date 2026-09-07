import MagnitudeConjecture.Algebra.StringProjectiveRadicalDecompositionObjects
import MagnitudeConjecture.CategoryTheory.ModuleCatLargeBiproduct
import Mathlib.Algebra.Category.FGModuleCat.Limits

/-!
# The incoming-arrow product model of a string projective radical

We retain the incoming-arrow indexing here.  Reindexing is performed only
after passing to a categorical biproduct, avoiding a large dependent
`LinearEquiv.piCongrLeft` term.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

noncomputable local instance quotientFGHasFiniteBiproducts
    (P : StringPresentation k A Q) :
    HasFiniteBiproducts
      (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ) := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- The dependent product of the incoming-arrow ranges, retained as a
finitely generated module. -/
noncomputable def representedVertexRadicalArrowPiFGObj
    (P : StringPresentation k A Q) (y : Q) :
    FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Fintype (DisplayedIncomingArrow y) := Fintype.ofFinite _
  letI : Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) := inferInstance
  letI (a : DisplayedIncomingArrow y) :
      Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
        (LinearMap.range (P.representedArrowLinearMap a.2)) := inferInstance
  exact FGModuleCat.of P.quotientCategoryAlgebraᵐᵒᵖ
    (∀ a : DisplayedIncomingArrow y,
      LinearMap.range (P.representedArrowLinearMap a.2))

/-- The radical is isomorphic to the incoming-arrow dependent product. -/
noncomputable def representedVertexRadicalToArrowPiIso
    (P : StringPresentation k A Q) (y : Q) :
    P.representedVertexRadicalFGObj y ≅
      P.representedVertexRadicalArrowPiFGObj y := by
  classical
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Fintype (DisplayedIncomingArrow y) := Fintype.ofFinite _
  letI : Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) := inferInstance
  letI (a : DisplayedIncomingArrow y) :
      Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
        (LinearMap.range (P.representedArrowLinearMap a.2)) := inferInstance
  letI : Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
      (Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y)) := inferInstance
  exact (P.incomingArrowRangeFamilyRadicalLinearEquiv y).symm.toFGModuleCatIso

/-- The incoming-arrow dependent product is the underlying module of the
corresponding categorical biproduct. -/
noncomputable def representedVertexRadicalArrowPiModuleIso
    (P : StringPresentation k A Q) (y : Q) :
    (forget₂ (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ)
        (ModuleCat P.quotientCategoryAlgebraᵐᵒᵖ)).obj
        (P.representedVertexRadicalArrowPiFGObj y) ≅
      (forget₂ (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ)
        (ModuleCat P.quotientCategoryAlgebraᵐᵒᵖ)).obj
        (⨁ (fun a : DisplayedIncomingArrow y ↦
          P.incomingArrowRangeFGObj a)) := by
  classical
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  letI : FiniteDimensional k P.quotientCategoryAlgebra :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
  letI : IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : Fintype (DisplayedIncomingArrow y) := Fintype.ofFinite _
  letI : Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y) := inferInstance
  letI (a : DisplayedIncomingArrow y) :
      Module.Finite P.quotientCategoryAlgebraᵐᵒᵖ
        (LinearMap.range (P.representedArrowLinearMap a.2)) := inferInstance
  let U := forget₂
    (FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ)
    (ModuleCat P.quotientCategoryAlgebraᵐᵒᵖ)
  letI : PreservesBiproduct
      (fun a : DisplayedIncomingArrow y ↦ P.incomingArrowRangeFGObj a) U :=
    preservesBiproduct_of_preservesProduct U
  exact (MagnitudeConjecture.ModuleCat.biproductIsoPi
    (fun a : DisplayedIncomingArrow y ↦
      ModuleCat.of P.quotientCategoryAlgebraᵐᵒᵖ
        (LinearMap.range (P.representedArrowLinearMap a.2)))).symm |>.trans <|
      (U.mapBiproduct
        (fun a : DisplayedIncomingArrow y ↦
          P.incomingArrowRangeFGObj a)).symm

/-- The incoming-arrow dependent product, as an FG-module, is isomorphic to
the incoming-arrow categorical biproduct. -/
noncomputable def representedVertexRadicalArrowPiToBiproductIso
    (P : StringPresentation k A Q) (y : Q) :
    P.representedVertexRadicalArrowPiFGObj y ≅
      ⨁ (fun a : DisplayedIncomingArrow y ↦
        P.incomingArrowRangeFGObj a) := by
  exact ObjectProperty.isoMk _ (P.representedVertexRadicalArrowPiModuleIso y)

end MagnitudeConjecture.BoundQuiver.StringPresentation
