import MagnitudeConjecture.Algebra.RightModuleCoherentDefect
import MagnitudeConjecture.Algebra.RightModuleRestrictedCoyonedaHom
import MagnitudeConjecture.CategoryTheory.EpiRightFreydKernel
import MagnitudeConjecture.CategoryTheory.RightFreydCokernel

/-!
# Freyd realizations of the two coherent-defect presentations

The restricted contravariant and covariant Yoneda embeddings are fully
faithful and have projective values.  Their right-Freyd cokernel realizations
are therefore fully faithful.  This packages the projective-resolution
lifting and homotopy-independence used in the morphism part of Auslander's
coherent duality.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Restricted contravariant Yoneda is full on all finitely generated
modules. -/
theorem finiteRestrictedContravariantRepresentableFunctor_full :
    S.finiteRestrictedContravariantRepresentableFunctor.Full := by
  let F := S.finiteRestrictedContravariantRepresentableFunctor
  change F.Full
  refine MagnitudeConjecture.CategoryTheory.functor_full_of_finite_coordinates
    (C := RightModule.FinitelyGeneratedCategory A)
    (D := CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k)
    (P := S.IndecCategory) S.fgObj F ?_ ?_
  · intro X
    letI : Module.Finite k X :=
      RightModule.finite_over_field_of_finitelyGenerated k A X
    obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
      (k := k) X
    have hdense (j : Fin d.n) :
        ∃ i : S.IndecCategory, Nonempty (d.summand j ≅ S.fgObj i) :=
      S.fgObj_complete (d.summand j) (d.indecomposable j)
    choose i e using hdense
    let eModule : X ≅ ⨁ fun j : Fin d.n ↦ S.fgObj (i j) :=
      d.isoBiproduct ≪≫ biproduct.mapIso
        (fun j ↦ Classical.choice (e j))
    exact ⟨d.n, i, ⟨eModule.symm⟩⟩
  · intro i j a
    let f : S.fgObj i ⟶ S.fgObj j := ObjectProperty.homMk (by
      change S.obj i ⟶ S.obj j
      exact a.hom.hom.app (Opposite.op i) (𝟙 (S.inclusion.obj i)))
    refine ⟨f, ?_⟩
    change S.finiteRestrictedContravariantRepresentableMap f = a
    exact S.finiteRestrictedContravariantRepresentableMap_fgObj_eq i j a

/-- Restricted contravariant Yoneda is faithful on all finitely generated
modules. -/
theorem finiteRestrictedContravariantRepresentableFunctor_faithful :
    S.finiteRestrictedContravariantRepresentableFunctor.Faithful where
  map_injective {X Y} :=
    S.finiteRestrictedContravariantRepresentableMap_injective X Y

/-- Every finite contravariant functor is an epimorphic image of a
restricted representable of a finitely generated module. -/
theorem finiteRestrictedContravariantRepresentableFunctor_epi_covers
    (Y : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k) :
    ∃ (X : RightModule.FinitelyGeneratedCategory A)
      (p : S.finiteRestrictedContravariantRepresentableFunctor.obj X ⟶ Y),
      Epi p := by
  let hP : ∀ X : S.IndecCategoryᵒᵖ,
      CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategoryᵒᵖ) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) :=
    fun X ↦ by simpa only [Opposite.op_unop] using
      S.indecOppositeRepresentableFinite X.unop
  obtain ⟨P⟩ :=
    CoveringHom.finiteRepresentablePresentation_nonempty hP Y
  let label : Fin P.n → S.IndecCategory := fun i ↦ (P.X i).unop
  let X : RightModule.FinitelyGeneratedCategory A :=
    ⨁ fun i ↦ S.fgObj (label i)
  let F := S.finiteRestrictedContravariantRepresentableFunctor
  let e : F.obj X ≅ P.source :=
    F.mapBiproduct (fun i ↦ S.fgObj (label i)) ≪≫
      biproduct.mapIso (fun i ↦ by
        change S.finiteRestrictedContravariantRepresentable
            (S.fgObj (label i)) ≅
          CoveringHom.finiteDimensionalLinearCoyoneda
            (k := k) (P.X i) (hP (P.X i))
        simpa only [label, Opposite.op_unop] using
          S.finiteRestrictedContravariantRepresentableFgObjIso
            ((P.X i).unop))
  refine ⟨X, e.hom ≫ P.f, ?_⟩
  infer_instance

/-- The right-Freyd realization of contravariant representable
presentations. -/
def contravariantDefectFreydRealization :
    CategoryTheory.Preadditive.RightFreyd
        (RightModule.FinitelyGeneratedCategory A) ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k :=
  CategoryTheory.Preadditive.RightFreyd.cokernelFunctor
    S.finiteRestrictedContravariantRepresentableFunctor

noncomputable instance contravariantDefectFreydRealization_essSurj :
    S.contravariantDefectFreydRealization.EssSurj := by
  letI : S.finiteRestrictedContravariantRepresentableFunctor.Full :=
    S.finiteRestrictedContravariantRepresentableFunctor_full
  exact
    CategoryTheory.Preadditive.RightFreyd.cokernelFunctor_essSurj_of_epi_covers
      S.finiteRestrictedContravariantRepresentableFunctor
      S.finiteRestrictedContravariantRepresentableFunctor_epi_covers

noncomputable instance contravariantDefectFreydRealization_full :
    S.contravariantDefectFreydRealization.Full := by
  letI : S.finiteRestrictedContravariantRepresentableFunctor.Full :=
    S.finiteRestrictedContravariantRepresentableFunctor_full
  letI : S.finiteRestrictedContravariantRepresentableFunctor.Faithful :=
    S.finiteRestrictedContravariantRepresentableFunctor_faithful
  exact
    CategoryTheory.Preadditive.RightFreyd.cokernelFunctor_full_of_projective_objects
        S.finiteRestrictedContravariantRepresentableFunctor
        S.finiteRestrictedContravariantRepresentable_projective

noncomputable instance contravariantDefectFreydRealization_faithful :
    S.contravariantDefectFreydRealization.Faithful := by
  letI : S.finiteRestrictedContravariantRepresentableFunctor.Full :=
    S.finiteRestrictedContravariantRepresentableFunctor_full
  letI : S.finiteRestrictedContravariantRepresentableFunctor.Faithful :=
    S.finiteRestrictedContravariantRepresentableFunctor_faithful
  exact
    CategoryTheory.Preadditive.RightFreyd.cokernelFunctor_faithful_of_projective_objects
        S.finiteRestrictedContravariantRepresentableFunctor
        S.finiteRestrictedContravariantRepresentable_projective

noncomputable instance contravariantDefectFreydRealization_isEquivalence :
    S.contravariantDefectFreydRealization.IsEquivalence := {}

/-- Every finite contravariant functor has a restricted-representable
presentation, and right homotopy is exactly equality on its cokernel. -/
def contravariantDefectFreydEquivalence :
    CategoryTheory.Preadditive.RightFreyd
        (RightModule.FinitelyGeneratedCategory A) ≌
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k :=
  S.contravariantDefectFreydRealization.asEquivalence

/-- The right-Freyd realization of covariant representable presentations.
The representing module variable is opposite because `Hom(X,−)` is
contravariant in `X`. -/
def covariantDefectFreydRealization :
    CategoryTheory.Preadditive.RightFreyd
        (RightModule.FinitelyGeneratedCategory A)ᵒᵖ ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategory) k :=
  CategoryTheory.Preadditive.RightFreyd.cokernelFunctor
    S.finiteRestrictedCovariantRepresentableFunctor

noncomputable instance covariantDefectFreydRealization_full :
    S.covariantDefectFreydRealization.Full := by
  letI : S.finiteRestrictedCovariantRepresentableFunctor.Full :=
    S.finiteRestrictedCovariantRepresentableFunctor_full
  letI : S.finiteRestrictedCovariantRepresentableFunctor.Faithful :=
    S.finiteRestrictedCovariantRepresentableFunctor_faithful
  exact
    CategoryTheory.Preadditive.RightFreyd.cokernelFunctor_full_of_projective_objects
        S.finiteRestrictedCovariantRepresentableFunctor
        (fun X ↦ S.finiteRestrictedCovariantRepresentable_projective X.unop)

noncomputable instance covariantDefectFreydRealization_faithful :
    S.covariantDefectFreydRealization.Faithful := by
  letI : S.finiteRestrictedCovariantRepresentableFunctor.Full :=
    S.finiteRestrictedCovariantRepresentableFunctor_full
  letI : S.finiteRestrictedCovariantRepresentableFunctor.Faithful :=
    S.finiteRestrictedCovariantRepresentableFunctor_faithful
  exact
    CategoryTheory.Preadditive.RightFreyd.cokernelFunctor_faithful_of_projective_objects
        S.finiteRestrictedCovariantRepresentableFunctor
        (fun X ↦ S.finiteRestrictedCovariantRepresentable_projective X.unop)

/-- Every finite covariant functor is an epimorphic image of a restricted
covariant representable of an object of the opposite module category. -/
theorem finiteRestrictedCovariantRepresentableFunctor_epi_covers
    (Y : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k) :
    ∃ (X : (RightModule.FinitelyGeneratedCategory A)ᵒᵖ)
      (p : S.finiteRestrictedCovariantRepresentableFunctor.obj X ⟶ Y),
      Epi p := by
  let hP : ∀ X : S.IndecCategory,
      CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategory) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) :=
    S.indecCovariantRepresentableFinite
  obtain ⟨P⟩ :=
    CoveringHom.finiteRepresentablePresentation_nonempty hP Y
  let X : (RightModule.FinitelyGeneratedCategory A)ᵒᵖ :=
    ⨁ fun i ↦ Opposite.op (S.fgObj (P.X i))
  let F := S.finiteRestrictedCovariantRepresentableFunctor
  let e : F.obj X ≅ P.source :=
    F.mapBiproduct (fun i ↦ Opposite.op (S.fgObj (P.X i))) ≪≫
      biproduct.mapIso (fun i ↦
        S.finiteRestrictedCovariantRepresentableFgObjIso (P.X i))
  refine ⟨X, e.hom ≫ P.f, ?_⟩
  infer_instance

noncomputable instance covariantDefectFreydRealization_essSurj :
    S.covariantDefectFreydRealization.EssSurj := by
  letI : S.finiteRestrictedCovariantRepresentableFunctor.Full :=
    S.finiteRestrictedCovariantRepresentableFunctor_full
  exact
    CategoryTheory.Preadditive.RightFreyd.cokernelFunctor_essSurj_of_epi_covers
      S.finiteRestrictedCovariantRepresentableFunctor
      S.finiteRestrictedCovariantRepresentableFunctor_epi_covers

noncomputable instance covariantDefectFreydRealization_isEquivalence :
    S.covariantDefectFreydRealization.IsEquivalence := {}

/-- Every finite covariant functor has a restricted-corepresentable
presentation, modulo right homotopy. -/
def covariantDefectFreydEquivalence :
    CategoryTheory.Preadditive.RightFreyd
        (RightModule.FinitelyGeneratedCategory A)ᵒᵖ ≌
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategory) k :=
  S.covariantDefectFreydRealization.asEquivalence

private abbrev ModuleEpiFreyd :=
  CategoryTheory.Preadditive.RightFreyd.EpiCategory
    (RightModule.FinitelyGeneratedCategory A)

private abbrev OppositeModuleEpiFreyd :=
  CategoryTheory.Preadditive.RightFreyd.EpiCategory
    (RightModule.FinitelyGeneratedCategory A)ᵒᵖ

/-- The contravariant Freyd realization restricted to epimorphic
presentations. -/
def contravariantEpiFreydRealizationRaw :
    ModuleEpiFreyd (A := A) ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k :=
  ObjectProperty.ι
      (CategoryTheory.Preadditive.RightFreyd.IsEpiArrow
        (RightModule.FinitelyGeneratedCategory A)) ⋙
    S.contravariantDefectFreydRealization

theorem contravariantEpiFreydRealizationRaw_isDefect
    (X : ModuleEpiFreyd (A := A)) :
    S.IsFiniteContravariantDefect
      ((S.contravariantEpiFreydRealizationRaw).obj X) := by
  let a := X.obj.as
  letI : Epi a.hom := X.property
  let K : ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
    ShortComplex.mk (kernel.ι a.hom) a.hom (kernel.condition a.hom)
  have hK : K.ShortExact :=
    { exact := ShortComplex.exact_kernel a.hom
      mono_f := inferInstance
      epi_g := inferInstance }
  refine ⟨K, hK, ⟨?_⟩⟩
  exact Iso.refl _

/-- Epimorphic Freyd presentations realized as exact contravariant
defects. -/
def contravariantEpiFreydRealization :
    ModuleEpiFreyd (A := A) ⥤ S.FiniteContravariantDefectCategory :=
  S.IsFiniteContravariantDefect.lift
    S.contravariantEpiFreydRealizationRaw
    S.contravariantEpiFreydRealizationRaw_isDefect

noncomputable instance contravariantEpiFreydRealization_full :
    S.contravariantEpiFreydRealization.Full where
  map_surjective {X Y} f := by
    let T := S.contravariantDefectFreydRealization
    obtain ⟨g, hg⟩ := T.map_surjective f.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg

noncomputable instance contravariantEpiFreydRealization_faithful :
    S.contravariantEpiFreydRealization.Faithful where
  map_injective {X Y} f g h := by
    let T := S.contravariantDefectFreydRealization
    apply ObjectProperty.hom_ext
    apply T.map_injective
    exact congrArg (fun z ↦ z.hom) h

noncomputable instance contravariantEpiFreydRealization_essSurj :
    S.contravariantEpiFreydRealization.EssSurj where
  mem_essImage F := by
    let K := F.property.choose
    have hK : K.ShortExact := F.property.choose_spec.1
    let a : Arrow (RightModule.FinitelyGeneratedCategory A) := Arrow.mk K.g
    let X : ModuleEpiFreyd (A := A) :=
      ⟨(CategoryTheory.Preadditive.RightFreyd.quotient _).obj a,
        hK.epi_g⟩
    refine ⟨X, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _
      (Classical.choice F.property.choose_spec.2)

noncomputable instance contravariantEpiFreydRealization_isEquivalence :
    S.contravariantEpiFreydRealization.IsEquivalence := {}

/-- Exact contravariant defects are the cokernel realizations of epimorphic
presentations. -/
def contravariantEpiFreydEquivalence :
    ModuleEpiFreyd (A := A) ≌ S.FiniteContravariantDefectCategory :=
  S.contravariantEpiFreydRealization.asEquivalence

/-- The covariant Freyd realization restricted to epimorphic presentations
in the opposite module category. -/
def covariantEpiFreydRealizationRaw :
    OppositeModuleEpiFreyd (A := A) ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategory) k :=
  ObjectProperty.ι
      (CategoryTheory.Preadditive.RightFreyd.IsEpiArrow
        (RightModule.FinitelyGeneratedCategory A)ᵒᵖ) ⋙
    S.covariantDefectFreydRealization

theorem covariantEpiFreydRealizationRaw_isDefect
    (X : OppositeModuleEpiFreyd (A := A)) :
    S.IsFiniteCovariantDefect
      ((S.covariantEpiFreydRealizationRaw).obj X) := by
  let a := X.obj.as
  letI : Epi a.hom := X.property
  let i : a.right.unop ⟶ a.left.unop := a.hom.unop
  letI : Mono i := by
    dsimp only [i]
    infer_instance
  let K : ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
    ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hK : K.ShortExact :=
    { exact := ShortComplex.exact_cokernel i
      mono_f := inferInstance
      epi_g := inferInstance }
  refine ⟨K, hK, ⟨?_⟩⟩
  exact Iso.refl _

/-- Epimorphic opposite-Freyd presentations realized as exact covariant
defects. -/
def covariantEpiFreydRealization :
    OppositeModuleEpiFreyd (A := A) ⥤ S.FiniteCovariantDefectCategory :=
  S.IsFiniteCovariantDefect.lift
    S.covariantEpiFreydRealizationRaw
    S.covariantEpiFreydRealizationRaw_isDefect

noncomputable instance covariantEpiFreydRealization_full :
    S.covariantEpiFreydRealization.Full where
  map_surjective {X Y} f := by
    let T := S.covariantDefectFreydRealization
    obtain ⟨g, hg⟩ := T.map_surjective f.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg

noncomputable instance covariantEpiFreydRealization_faithful :
    S.covariantEpiFreydRealization.Faithful where
  map_injective {X Y} f g h := by
    let T := S.covariantDefectFreydRealization
    apply ObjectProperty.hom_ext
    apply T.map_injective
    exact congrArg (fun z ↦ z.hom) h

noncomputable instance covariantEpiFreydRealization_essSurj :
    S.covariantEpiFreydRealization.EssSurj where
  mem_essImage G := by
    let K := G.property.choose
    have hK : K.ShortExact := G.property.choose_spec.1
    letI : Mono K.f := hK.mono_f
    let a : Arrow (RightModule.FinitelyGeneratedCategory A)ᵒᵖ :=
      Arrow.mk K.f.op
    let X : OppositeModuleEpiFreyd (A := A) :=
      ⟨(CategoryTheory.Preadditive.RightFreyd.quotient _).obj a, by
        change Epi K.f.op
        infer_instance⟩
    refine ⟨X, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _
      (Classical.choice G.property.choose_spec.2)

noncomputable instance covariantEpiFreydRealization_isEquivalence :
    S.covariantEpiFreydRealization.IsEquivalence := {}

/-- Exact covariant defects are the cokernel realizations of epimorphic
presentations in the opposite module category. -/
def covariantEpiFreydEquivalence :
    OppositeModuleEpiFreyd (A := A) ≌ S.FiniteCovariantDefectCategory :=
  S.covariantEpiFreydRealization.asEquivalence

/-- Auslander's anti-equivalence on the exact-defect subcategories,
realized by projective presentations and kernel reversal. -/
def coherentDefectEquivalence :
    S.FiniteContravariantDefectCategoryᵒᵖ ≌
      S.FiniteCovariantDefectCategory :=
  (S.contravariantEpiFreydEquivalence.op).symm |>.trans
    (CategoryTheory.Preadditive.RightFreyd.kernelOpEquivalence
      (C := RightModule.FinitelyGeneratedCategory A)) |>.trans
    S.covariantEpiFreydEquivalence

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
