import MagnitudeConjecture.Algebra.RightModuleCoherentDefectComparisonIso
import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectComparisonIso

/-!
# Coherent duality on exact defects

This file packages the two pointwise Ext² calculations as functors on the
full subcategories of defects admitting exact representable presentations.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable [HasExt.{u} (FG (A := A))]
variable [HasExt.{u} (S.FiniteContravariantFunctor)]
variable [HasExt.{u} (S.FiniteCovariantFunctor)]

/-- A chosen exact presentation of a contravariant defect. -/
def contravariantDefectPresentation
    (F : S.FiniteContravariantDefectCategory) :
    ShortComplex (FG (A := A)) :=
  F.property.choose

theorem contravariantDefectPresentation_shortExact
    (F : S.FiniteContravariantDefectCategory) :
    (S.contravariantDefectPresentation F).ShortExact :=
  F.property.choose_spec.1

/-- Identification of the defect of the chosen presentation with the
given contravariant defect. -/
def contravariantDefectPresentationIso
    (F : S.FiniteContravariantDefectCategory) :
    S.finiteContravariantDefect (S.contravariantDefectPresentation F) ≅
      F.obj :=
  Classical.choice F.property.choose_spec.2

/-- A chosen exact presentation of a covariant defect. -/
def covariantDefectPresentation
    (G : S.FiniteCovariantDefectCategory) :
    ShortComplex (FG (A := A)) :=
  G.property.choose

theorem covariantDefectPresentation_shortExact
    (G : S.FiniteCovariantDefectCategory) :
    (S.covariantDefectPresentation G).ShortExact :=
  G.property.choose_spec.1

/-- Identification of the defect of the chosen presentation with the
given covariant defect. -/
def covariantDefectPresentationIso
    (G : S.FiniteCovariantDefectCategory) :
    S.finiteCovariantDefect (S.covariantDefectPresentation G) ≅ G.obj :=
  Classical.choice G.property.choose_spec.2

/-- The coherent dual of a contravariant defect is identified with the
covariant defect of its chosen exact presentation. -/
def chosenCovariantDefectCoherentDualIso
    (F : S.FiniteContravariantDefectCategory) :
    S.finiteCovariantFunctorInclusion.obj
        (S.finiteCovariantDefect (S.contravariantDefectPresentation F)) ≅
      S.coherentDualObj F.obj :=
  S.finiteCovariantDefectCoherentDualIso
      (S.contravariantDefectPresentation_shortExact F) ≪≫
    S.coherentDualRaw.mapIso
      (S.contravariantDefectPresentationIso F).op.symm

/-- The reverse coherent dual of a covariant defect is identified with the
contravariant defect of its chosen exact presentation. -/
def chosenContravariantDefectCoherentCodualIso
    (G : S.FiniteCovariantDefectCategory) :
    S.finiteContravariantFunctorInclusion.obj
        (S.finiteContravariantDefect (S.covariantDefectPresentation G)) ≅
      S.coherentCodualObj G.obj :=
  S.finiteContravariantDefectCoherentCodualIso
      (S.covariantDefectPresentation_shortExact G) ≪≫
    S.coherentCodualRaw.mapIso
      (S.covariantDefectPresentationIso G).op.symm

/-- The raw coherent dual restricted to exact contravariant defects. -/
def coherentDualOnContravariantDefectsRaw :
    S.FiniteContravariantDefectCategoryᵒᵖ ⥤
      (S.IndecCategory ⥤ ModuleCat.{u} k) :=
  (ObjectProperty.ι S.IsFiniteContravariantDefect).op ⋙
    S.coherentDualRaw

theorem coherentDualOnContravariantDefectsRaw_isLinear
    (F : S.FiniteContravariantDefectCategoryᵒᵖ) :
    CoveringHom.IsLinearModule (C := S.IndecCategory) k
      ((S.coherentDualOnContravariantDefectsRaw).obj F) := by
  let e := S.chosenCovariantDefectCoherentDualIso F.unop
  let M := S.finiteCovariantDefect
    (S.contravariantDefectPresentation F.unop)
  letI : (S.finiteCovariantFunctorInclusion.obj M).Additive := by
    change M.obj.obj.Additive
    infer_instance
  letI : (S.finiteCovariantFunctorInclusion.obj M).Linear k := by
    change M.obj.obj.Linear k
    infer_instance
  exact ⟨Functor.additive_of_iso e, Functor.linear_of_iso k e⟩

/-- The coherent dual on exact contravariant defects, valued in linear
modules. -/
def coherentDualOnContravariantDefectsLinear :
    S.FiniteContravariantDefectCategoryᵒᵖ ⥤
      CoveringHom.LinearModuleCategory (C := S.IndecCategory) k :=
  (CoveringHom.IsLinearModule (C := S.IndecCategory) k).lift
    S.coherentDualOnContravariantDefectsRaw
    S.coherentDualOnContravariantDefectsRaw_isLinear

theorem coherentDualOnContravariantDefectsLinear_isFiniteDimensional
    (F : S.FiniteContravariantDefectCategoryᵒᵖ) :
    CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategory) k
      ((S.coherentDualOnContravariantDefectsLinear).obj F) := by
  let e :
      (S.finiteCovariantDefect
          (S.contravariantDefectPresentation F.unop)).obj ≅
        (S.coherentDualOnContravariantDefectsLinear).obj F :=
    ObjectProperty.isoMk _
      (S.chosenCovariantDefectCoherentDualIso F.unop)
  exact (CoveringHom.IsFiniteDimensionalModule
      (C := S.IndecCategory) k).prop_of_iso e
    (S.finiteCovariantDefect
      (S.contravariantDefectPresentation F.unop)).property

/-- The coherent dual restricted to exact contravariant defects, valued in
finite linear functors. -/
def coherentDualOnContravariantDefectsFinite :
    S.FiniteContravariantDefectCategoryᵒᵖ ⥤
      S.FiniteCovariantFunctor :=
  (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).lift
      S.coherentDualOnContravariantDefectsLinear
      S.coherentDualOnContravariantDefectsLinear_isFiniteDimensional

theorem coherentDualOnContravariantDefectsFinite_isDefect
    (F : S.FiniteContravariantDefectCategoryᵒᵖ) :
    S.IsFiniteCovariantDefect
      ((S.coherentDualOnContravariantDefectsFinite).obj F) := by
  refine ⟨S.contravariantDefectPresentation F.unop,
    S.contravariantDefectPresentation_shortExact F.unop, ?_⟩
  exact ⟨ObjectProperty.isoMk _ <| ObjectProperty.isoMk _ <|
    S.chosenCovariantDefectCoherentDualIso F.unop⟩

/-- Auslander's coherent dual as a contravariant functor from exact
contravariant defects to exact covariant defects. -/
def coherentDualOnContravariantDefects :
    S.FiniteContravariantDefectCategoryᵒᵖ ⥤
      S.FiniteCovariantDefectCategory :=
  S.IsFiniteCovariantDefect.lift
    S.coherentDualOnContravariantDefectsFinite
    S.coherentDualOnContravariantDefectsFinite_isDefect

/-- The raw reverse coherent dual restricted to exact covariant defects. -/
def coherentCodualOnCovariantDefectsRaw :
    S.FiniteCovariantDefectCategoryᵒᵖ ⥤
      (S.IndecCategoryᵒᵖ ⥤ ModuleCat.{u} k) :=
  (ObjectProperty.ι S.IsFiniteCovariantDefect).op ⋙
    S.coherentCodualRaw

theorem coherentCodualOnCovariantDefectsRaw_isLinear
    (G : S.FiniteCovariantDefectCategoryᵒᵖ) :
    CoveringHom.IsLinearModule (C := S.IndecCategoryᵒᵖ) k
      ((S.coherentCodualOnCovariantDefectsRaw).obj G) := by
  let e := S.chosenContravariantDefectCoherentCodualIso G.unop
  let M := S.finiteContravariantDefect
    (S.covariantDefectPresentation G.unop)
  letI : (S.finiteContravariantFunctorInclusion.obj M).Additive := by
    change M.obj.obj.Additive
    infer_instance
  letI : (S.finiteContravariantFunctorInclusion.obj M).Linear k := by
    change M.obj.obj.Linear k
    infer_instance
  exact ⟨Functor.additive_of_iso e, Functor.linear_of_iso k e⟩

/-- The reverse coherent dual on exact covariant defects, valued in linear
modules. -/
def coherentCodualOnCovariantDefectsLinear :
    S.FiniteCovariantDefectCategoryᵒᵖ ⥤
      CoveringHom.LinearModuleCategory (C := S.IndecCategoryᵒᵖ) k :=
  (CoveringHom.IsLinearModule (C := S.IndecCategoryᵒᵖ) k).lift
    S.coherentCodualOnCovariantDefectsRaw
    S.coherentCodualOnCovariantDefectsRaw_isLinear

theorem coherentCodualOnCovariantDefectsLinear_isFiniteDimensional
    (G : S.FiniteCovariantDefectCategoryᵒᵖ) :
    CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategoryᵒᵖ) k
      ((S.coherentCodualOnCovariantDefectsLinear).obj G) := by
  let e :
      (S.finiteContravariantDefect
          (S.covariantDefectPresentation G.unop)).obj ≅
        (S.coherentCodualOnCovariantDefectsLinear).obj G :=
    ObjectProperty.isoMk _
      (S.chosenContravariantDefectCoherentCodualIso G.unop)
  exact (CoveringHom.IsFiniteDimensionalModule
      (C := S.IndecCategoryᵒᵖ) k).prop_of_iso e
    (S.finiteContravariantDefect
      (S.covariantDefectPresentation G.unop)).property

/-- The reverse coherent dual restricted to exact covariant defects, valued
in finite linear functors. -/
def coherentCodualOnCovariantDefectsFinite :
    S.FiniteCovariantDefectCategoryᵒᵖ ⥤
      S.FiniteContravariantFunctor :=
  (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).lift
      S.coherentCodualOnCovariantDefectsLinear
      S.coherentCodualOnCovariantDefectsLinear_isFiniteDimensional

theorem coherentCodualOnCovariantDefectsFinite_isDefect
    (G : S.FiniteCovariantDefectCategoryᵒᵖ) :
    S.IsFiniteContravariantDefect
      ((S.coherentCodualOnCovariantDefectsFinite).obj G) := by
  refine ⟨S.covariantDefectPresentation G.unop,
    S.covariantDefectPresentation_shortExact G.unop, ?_⟩
  exact ⟨ObjectProperty.isoMk _ <| ObjectProperty.isoMk _ <|
    S.chosenContravariantDefectCoherentCodualIso G.unop⟩

/-- The reverse coherent dual as a contravariant functor from exact
covariant defects to exact contravariant defects. -/
def coherentCodualOnCovariantDefects :
    S.FiniteCovariantDefectCategoryᵒᵖ ⥤
      S.FiniteContravariantDefectCategory :=
  S.IsFiniteContravariantDefect.lift
    S.coherentCodualOnCovariantDefectsFinite
    S.coherentCodualOnCovariantDefectsFinite_isDefect

/-- The coherent dual is essentially surjective on exact defects. -/
noncomputable instance coherentDualOnContravariantDefects_essSurj :
    (S.coherentDualOnContravariantDefects).EssSurj where
  mem_essImage G := by
    let K := S.covariantDefectPresentation G
    have hK : K.ShortExact := S.covariantDefectPresentation_shortExact G
    let F : S.FiniteContravariantDefectCategory :=
      ⟨S.finiteContravariantDefect K,
        ⟨K, hK, ⟨Iso.refl _⟩⟩⟩
    let eComparison :
        S.finiteCovariantDefect K ≅
          (S.coherentDualOnContravariantDefects.obj
            (Opposite.op F)).obj :=
      ObjectProperty.isoMk _ <| ObjectProperty.isoMk _ <|
        S.finiteCovariantDefectCoherentDualIso hK
    let eTarget :
        (⟨S.finiteCovariantDefect K,
          ⟨K, hK, ⟨Iso.refl _⟩⟩⟩ :
            S.FiniteCovariantDefectCategory) ≅ G :=
      ObjectProperty.isoMk _ (S.covariantDefectPresentationIso G)
    exact ⟨Opposite.op F, ⟨
      (ObjectProperty.isoMk _ eComparison).symm ≪≫ eTarget⟩⟩

/-- The reverse coherent dual is essentially surjective on exact defects. -/
noncomputable instance coherentCodualOnCovariantDefects_essSurj :
    (S.coherentCodualOnCovariantDefects).EssSurj where
  mem_essImage F := by
    let K := S.contravariantDefectPresentation F
    have hK : K.ShortExact := S.contravariantDefectPresentation_shortExact F
    let G : S.FiniteCovariantDefectCategory :=
      ⟨S.finiteCovariantDefect K,
        ⟨K, hK, ⟨Iso.refl _⟩⟩⟩
    let eComparison :
        S.finiteContravariantDefect K ≅
          (S.coherentCodualOnCovariantDefects.obj
            (Opposite.op G)).obj :=
      ObjectProperty.isoMk _ <| ObjectProperty.isoMk _ <|
        S.finiteContravariantDefectCoherentCodualIso hK
    let eTarget :
        (⟨S.finiteContravariantDefect K,
          ⟨K, hK, ⟨Iso.refl _⟩⟩⟩ :
            S.FiniteContravariantDefectCategory) ≅ F :=
      ObjectProperty.isoMk _ (S.contravariantDefectPresentationIso F)
    exact ⟨Opposite.op G, ⟨
      (ObjectProperty.isoMk _ eComparison).symm ≪≫ eTarget⟩⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
