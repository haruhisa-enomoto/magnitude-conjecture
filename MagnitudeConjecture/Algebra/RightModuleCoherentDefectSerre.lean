import MagnitudeConjecture.Algebra.RightModuleCoherentDefectEquivalence
import MagnitudeConjecture.Algebra.RightModuleCoherentDefectEvaluation
import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectEvaluation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDualUniserial
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Exact defects form Serre subcategories

The coherent-duality equivalence is defined on exact defects.  To compare
uniseriality there with uniseriality in the ambient finite-functor category,
we identify the exact defects by their vanishing on projective or injective
modules.  This file begins with the two direct vanishing implications.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra ZeroObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Finite contravariant functors vanishing on the chosen projective
indecomposables. -/
def ContravariantVanishesOnProjectives :
    ObjectProperty
      (CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
        (C := S.IndecCategoryᵒᵖ) k) :=
  fun F ↦ ∀ i : S.IndecCategory, Projective (S.fgObj i) →
    IsZero (F.obj.obj.obj (Opposite.op i))

/-- Finite covariant functors vanishing on the chosen injective
indecomposables. -/
def CovariantVanishesOnInjectives :
    ObjectProperty (FiniteCovariantFunctor S) :=
  fun F ↦ ∀ i : S.IndecCategory, Injective (S.fgObj i) →
    IsZero (F.obj.obj.obj i)

noncomputable instance contravariantVanishes_closedUnderSubobjects :
    S.ContravariantVanishesOnProjectives.IsClosedUnderSubobjects where
  prop_of_mono {X Y} f hf hY i hi := by
    letI : Mono f := hf
    let E := S.finiteContravariantFunctorEvaluation (Opposite.op i)
    letI : E.PreservesMonomorphisms :=
      NormalEpiCategory.preservesMonomorphisms_of_preservesKernels E
    exact @IsZero.of_mono _ _ _ _ _ (E.map f)
      (Functor.PreservesMonomorphisms.preserves f) (hY i hi)

noncomputable instance contravariantVanishes_closedUnderQuotients :
    S.ContravariantVanishesOnProjectives.IsClosedUnderQuotients where
  prop_of_epi {X Y} f hf hX i hi := by
    letI : Epi f := hf
    let E := S.finiteContravariantFunctorEvaluation (Opposite.op i)
    letI : E.PreservesEpimorphisms :=
      NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels E
    exact @IsZero.of_epi _ _ _ _ _ (E.map f)
      (Functor.PreservesEpimorphisms.preserves f) (hX i hi)

noncomputable instance covariantVanishes_closedUnderSubobjects :
    S.CovariantVanishesOnInjectives.IsClosedUnderSubobjects where
  prop_of_mono {X Y} f hf hY i hi := by
    letI : Mono f := hf
    let E := S.finiteCovariantFunctorEvaluation i
    letI : E.PreservesMonomorphisms :=
      NormalEpiCategory.preservesMonomorphisms_of_preservesKernels E
    exact @IsZero.of_mono _ _ _ _ _ (E.map f)
      (Functor.PreservesMonomorphisms.preserves f) (hY i hi)

noncomputable instance covariantVanishes_closedUnderQuotients :
    S.CovariantVanishesOnInjectives.IsClosedUnderQuotients where
  prop_of_epi {X Y} f hf hX i hi := by
    letI : Epi f := hf
    let E := S.finiteCovariantFunctorEvaluation i
    letI : E.PreservesEpimorphisms :=
      NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels E
    exact @IsZero.of_epi _ _ _ _ _ (E.map f)
      (Functor.PreservesEpimorphisms.preserves f) (hX i hi)

/-- A contravariant exact defect vanishes at every projective chosen
indecomposable. -/
theorem finiteContravariantDefect_isZero_at_projective
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) (i : S.IndecCategory)
    (hi : Projective (S.fgObj i)) :
    IsZero ((S.finiteContravariantDefect K).obj.obj.obj
      (Opposite.op i)) := by
  let E := S.finiteContravariantFunctorEvaluation (Opposite.op i)
  let f := S.finiteRestrictedContravariantRepresentableMap K.g
  haveI : Epi K.g := hK.epi_g
  haveI : Projective (S.fgObj i) := hi
  have hsurj : Function.Surjective (E.map f) := by
    intro q
    let qFG : S.fgObj i ⟶ K.X₃ := ObjectProperty.homMk q
    let l := Projective.factorThru qFG K.g
    refine ⟨l.hom, ?_⟩
    exact congrArg (fun z : S.fgObj i ⟶ K.X₃ ↦ z.hom)
      (Projective.factorThru_comp qFG K.g)
  letI : Epi (E.map f) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  letI : PreservesFiniteColimits E := by
    change PreservesFiniteColimits
      (S.finiteContravariantFunctorInclusion ⋙
        (evaluation S.IndecCategoryᵒᵖ (ModuleCat.{u} k)).obj
          (Opposite.op i))
    exact comp_preservesFiniteColimits
      S.finiteContravariantFunctorInclusion
      ((evaluation S.IndecCategoryᵒᵖ (ModuleCat.{u} k)).obj
        (Opposite.op i))
  let e : E.obj (cokernel f) ≅ cokernel (E.map f) :=
    PreservesCokernel.iso E f
  exact (isZero_cokernel_of_epi (E.map f)).of_iso e

/-- A covariant exact defect vanishes at every injective chosen
indecomposable. -/
theorem finiteCovariantDefect_isZero_at_injective
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) (i : S.IndecCategory)
    (hi : Injective (S.fgObj i)) :
    IsZero ((S.finiteCovariantDefect K).obj.obj.obj i) := by
  let E := S.finiteCovariantFunctorEvaluation i
  let f := S.finiteRestrictedCovariantRepresentableMap K.f
  haveI : Mono K.f := hK.mono_f
  haveI : Injective (S.fgObj i) := hi
  have hsurj : Function.Surjective (E.map f) := by
    intro q
    let qFG : K.X₁ ⟶ S.fgObj i := ObjectProperty.homMk q
    let l := Injective.factorThru qFG K.f
    refine ⟨l.hom, ?_⟩
    exact congrArg (fun z : K.X₁ ⟶ S.fgObj i ↦ z.hom)
      (Injective.comp_factorThru qFG K.f)
  letI : Epi (E.map f) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  letI : PreservesFiniteColimits E := by
    change PreservesFiniteColimits
      (S.finiteCovariantFunctorInclusion ⋙
        (evaluation S.IndecCategory (ModuleCat.{u} k)).obj i)
    exact comp_preservesFiniteColimits
      S.finiteCovariantFunctorInclusion
      ((evaluation S.IndecCategory (ModuleCat.{u} k)).obj i)
  let e : E.obj (cokernel f) ≅ cokernel (E.map f) :=
    PreservesCokernel.iso E f
  exact (isZero_cokernel_of_epi (E.map f)).of_iso e

/-- Exact contravariant defects satisfy projective vanishing. -/
theorem isFiniteContravariantDefect_le_vanishesOnProjectives :
    S.IsFiniteContravariantDefect ≤
      S.ContravariantVanishesOnProjectives := by
  intro F hF
  obtain ⟨K, hK, ⟨e⟩⟩ := hF
  apply S.ContravariantVanishesOnProjectives.prop_of_iso e
  intro i hi
  exact S.finiteContravariantDefect_isZero_at_projective K hK i hi

/-- Exact covariant defects satisfy injective vanishing. -/
theorem isFiniteCovariantDefect_le_vanishesOnInjectives :
    S.IsFiniteCovariantDefect ≤ S.CovariantVanishesOnInjectives := by
  intro F hF
  obtain ⟨K, hK, ⟨e⟩⟩ := hF
  apply S.CovariantVanishesOnInjectives.prop_of_iso e
  intro i hi
  exact S.finiteCovariantDefect_isZero_at_injective K hK i hi

/-- If the cokernel of a restricted contravariant representable map
vanishes on projective indecomposables, then the presenting module map is
an epimorphism. -/
theorem epi_of_contravariantCokernel_vanishesOnProjectives
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y)
    (hzero : S.ContravariantVanishesOnProjectives
      (cokernel (S.finiteRestrictedContravariantRepresentableMap f))) :
    Epi f := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  obtain ⟨P⟩ := EnoughProjectives.presentation Y
  letI : Module.Finite k P.p :=
    RightModule.finite_over_field_of_finitelyGenerated k A P.p
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) P.p
  let inclusion (j : Fin d.n) : d.summand j ⟶ P.p :=
    biproduct.ι d.summand j ≫ d.isoBiproduct.inv
  let projection (j : Fin d.n) : P.p ⟶ d.summand j :=
    d.isoBiproduct.hom ≫ biproduct.π d.summand j
  have hprojective (j : Fin d.n) : Projective (d.summand j) := by
    apply projective_of_retract (P := P.p) (Q := d.summand j)
      (inferInstance : Projective P.p) (inclusion j) (projection j)
    simp [inclusion, projection, Category.assoc]
  have hdense (j : Fin d.n) :
      ∃ i : S.IndecCategory, Nonempty (d.summand j ≅ S.fgObj i) :=
    S.fgObj_complete (d.summand j) (d.indecomposable j)
  choose label e using hdense
  have hlabelProjective (j : Fin d.n) : Projective (S.fgObj (label j)) :=
    Projective.of_iso (Classical.choice (e j)) (hprojective j)
  have hlift (j : Fin d.n) :
      ∃ l : S.fgObj (label j) ⟶ X,
        l ≫ f = (Classical.choice (e j)).inv ≫ inclusion j ≫ P.f := by
    let E := S.finiteContravariantFunctorEvaluation
      (Opposite.op (label j))
    let m := S.finiteRestrictedContravariantRepresentableMap f
    let ecokernel : E.obj (cokernel m) ≅ cokernel (E.map m) :=
      PreservesCokernel.iso E m
    have hz : IsZero (cokernel (E.map m)) :=
      (hzero (label j) (hlabelProjective j)).of_iso ecokernel.symm
    letI : Epi (E.map m) :=
      Preadditive.epi_of_isZero_cokernel (E.map m) hz
    let r : S.fgObj (label j) ⟶ Y :=
      (Classical.choice (e j)).inv ≫ inclusion j ≫ P.f
    obtain ⟨l, hl⟩ :=
      (ModuleCat.epi_iff_surjective (E.map m)).mp inferInstance r.hom
    refine ⟨ObjectProperty.homMk l, ?_⟩
    apply ObjectProperty.hom_ext
    exact hl
  choose l hl using hlift
  let L : P.p ⟶ X :=
    d.isoBiproduct.hom ≫
      biproduct.desc (fun j ↦ (Classical.choice (e j)).hom ≫ l j)
  have hLf : L ≫ f = P.f := by
    apply (cancel_epi d.isoBiproduct.inv).1
    apply biproduct.hom_ext'
    intro j
    simp only [L, Category.assoc, Iso.inv_hom_id_assoc,
      biproduct.ι_desc_assoc, hl]
    simp [inclusion, Category.assoc]
  exact epi_of_epi_fac hLf

/-- If the cokernel of a restricted covariant representable map vanishes on
injective indecomposables, then the presenting module map is a
monomorphism. -/
theorem mono_of_covariantCokernel_vanishesOnInjectives
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y)
    (hzero : S.CovariantVanishesOnInjectives
      (cokernel (S.finiteRestrictedCovariantRepresentableMap f))) :
    Mono f := by
  letI : EnoughInjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughInjectives k Aᵐᵒᵖ
  obtain ⟨I⟩ := EnoughInjectives.presentation X
  letI : Module.Finite k I.J :=
    RightModule.finite_over_field_of_finitelyGenerated k A I.J
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) I.J
  let inclusion (j : Fin d.n) : d.summand j ⟶ I.J :=
    biproduct.ι d.summand j ≫ d.isoBiproduct.inv
  let projection (j : Fin d.n) : I.J ⟶ d.summand j :=
    d.isoBiproduct.hom ≫ biproduct.π d.summand j
  have hinjective (j : Fin d.n) : Injective (d.summand j) := by
    exact Retract.injective
      { i := inclusion j
        r := projection j
        retract := by simp [inclusion, projection, Category.assoc] }
  have hdense (j : Fin d.n) :
      ∃ i : S.IndecCategory, Nonempty (d.summand j ≅ S.fgObj i) :=
    S.fgObj_complete (d.summand j) (d.indecomposable j)
  choose label e using hdense
  have hlabelInjective (j : Fin d.n) : Injective (S.fgObj (label j)) :=
    Injective.of_iso (Classical.choice (e j)) (hinjective j)
  have hextend (j : Fin d.n) :
      ∃ l : Y ⟶ S.fgObj (label j),
        f ≫ l = I.f ≫ projection j ≫ (Classical.choice (e j)).hom := by
    let E := S.finiteCovariantFunctorEvaluation (label j)
    let m := S.finiteRestrictedCovariantRepresentableMap f
    let ecokernel : E.obj (cokernel m) ≅ cokernel (E.map m) :=
      PreservesCokernel.iso E m
    have hz : IsZero (cokernel (E.map m)) :=
      (hzero (label j) (hlabelInjective j)).of_iso ecokernel.symm
    letI : Epi (E.map m) :=
      Preadditive.epi_of_isZero_cokernel (E.map m) hz
    let r : X ⟶ S.fgObj (label j) :=
      I.f ≫ projection j ≫ (Classical.choice (e j)).hom
    obtain ⟨l, hl⟩ :=
      (ModuleCat.epi_iff_surjective (E.map m)).mp inferInstance r.hom
    refine ⟨ObjectProperty.homMk l, ?_⟩
    apply ObjectProperty.hom_ext
    exact hl
  choose l hl using hextend
  let L : Y ⟶ I.J :=
    biproduct.lift
      (fun j ↦ l j ≫ (Classical.choice (e j)).inv) ≫
        d.isoBiproduct.inv
  have hfL : f ≫ L = I.f := by
    apply (cancel_mono d.isoBiproduct.hom).1
    apply biproduct.hom_ext
    intro j
    simp only [L, Category.assoc, Iso.inv_hom_id_assoc,
      biproduct.lift_π]
    rw [← Category.assoc, hl]
    simp [projection, Category.assoc]
  exact mono_of_mono_fac hfL

/-- Projective vanishing is sufficient for a finite contravariant functor to
admit an exact representable presentation. -/
theorem vanishesOnProjectives_le_isFiniteContravariantDefect :
    S.ContravariantVanishesOnProjectives ≤
      S.IsFiniteContravariantDefect := by
  intro F hF
  let R := S.contravariantDefectFreydRealization
  obtain ⟨X, ⟨e⟩⟩ := (inferInstance : R.EssSurj).mem_essImage F
  let a := X.as
  have haVanishes : S.ContravariantVanishesOnProjectives
      (cokernel
        (S.finiteRestrictedContravariantRepresentableMap a.hom)) := by
    exact S.ContravariantVanishesOnProjectives.prop_of_iso e.symm hF
  letI : Epi a.hom :=
    S.epi_of_contravariantCokernel_vanishesOnProjectives a.hom
      haVanishes
  let K : ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
    ShortComplex.mk (kernel.ι a.hom) a.hom (kernel.condition a.hom)
  have hK : K.ShortExact :=
    { exact := ShortComplex.exact_kernel a.hom
      mono_f := inferInstance
      epi_g := inferInstance }
  refine ⟨K, hK, ⟨?_⟩⟩
  exact e

/-- Injective vanishing is sufficient for a finite covariant functor to admit
an exact representable presentation. -/
theorem vanishesOnInjectives_le_isFiniteCovariantDefect :
    S.CovariantVanishesOnInjectives ≤
      S.IsFiniteCovariantDefect := by
  intro F hF
  let R := S.covariantDefectFreydRealization
  obtain ⟨X, ⟨e⟩⟩ := (inferInstance : R.EssSurj).mem_essImage F
  let a := X.as
  let i : a.right.unop ⟶ a.left.unop := a.hom.unop
  have hiVanishes : S.CovariantVanishesOnInjectives
      (cokernel (S.finiteRestrictedCovariantRepresentableMap i)) := by
    exact S.CovariantVanishesOnInjectives.prop_of_iso e.symm hF
  letI : Mono i :=
    S.mono_of_covariantCokernel_vanishesOnInjectives i hiVanishes
  let K : ShortComplex (RightModule.FinitelyGeneratedCategory A) :=
    ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hK : K.ShortExact :=
    { exact := ShortComplex.exact_cokernel i
      mono_f := inferInstance
      epi_g := inferInstance }
  refine ⟨K, hK, ⟨?_⟩⟩
  exact e

/-- Exact contravariant defects are precisely the finite functors vanishing
on projective indecomposables. -/
theorem isFiniteContravariantDefect_iff_vanishesOnProjectives
    (F : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k) :
    S.IsFiniteContravariantDefect F ↔
      S.ContravariantVanishesOnProjectives F :=
  ⟨S.isFiniteContravariantDefect_le_vanishesOnProjectives F,
    S.vanishesOnProjectives_le_isFiniteContravariantDefect F⟩

/-- Exact covariant defects are precisely the finite functors vanishing on
injective indecomposables. -/
theorem isFiniteCovariantDefect_iff_vanishesOnInjectives
    (F : S.FiniteCovariantFunctor) :
    S.IsFiniteCovariantDefect F ↔
      S.CovariantVanishesOnInjectives F :=
  ⟨S.isFiniteCovariantDefect_le_vanishesOnInjectives F,
    S.vanishesOnInjectives_le_isFiniteCovariantDefect F⟩

noncomputable instance contravariantVanishes_containsZero :
    S.ContravariantVanishesOnProjectives.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    intro i hi
    let E := S.finiteContravariantFunctorEvaluation (Opposite.op i)
    exact E.map_isZero (isZero_zero _)⟩

noncomputable instance covariantVanishes_containsZero :
    S.CovariantVanishesOnInjectives.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    intro i hi
    let E := S.finiteCovariantFunctorEvaluation i
    exact E.map_isZero (isZero_zero _)⟩

noncomputable instance contravariantVanishes_closedUnderExtensions :
    S.ContravariantVanishesOnProjectives.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ i hi := by
    let E := S.finiteContravariantFunctorEvaluation (Opposite.op i)
    exact (hT.map_of_exact E).exact.isZero_of_both_isZero
      (h₁ i hi) (h₃ i hi)

noncomputable instance covariantVanishes_closedUnderExtensions :
    S.CovariantVanishesOnInjectives.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ i hi := by
    let E := S.finiteCovariantFunctorEvaluation i
    exact (hT.map_of_exact E).exact.isZero_of_both_isZero
      (h₁ i hi) (h₃ i hi)

noncomputable instance contravariantVanishes_closedUnderFiniteProducts :
    S.ContravariantVanishesOnProjectives.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨p, hp⟩ i hi
    let E := S.finiteContravariantFunctorEvaluation (Opposite.op i)
    exact (isLimitOfPreserves E (limit.isLimit p)).isZero_pt
      ((p ⋙ E).isZero (fun j ↦ hp j i hi))

noncomputable instance covariantVanishes_closedUnderFiniteProducts :
    S.CovariantVanishesOnInjectives.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨p, hp⟩ i hi
    let E := S.finiteCovariantFunctorEvaluation i
    exact (isLimitOfPreserves E (limit.isLimit p)).isZero_pt
      ((p ⋙ E).isZero (fun j ↦ hp j i hi))

noncomputable instance finiteContravariantDefect_containsZero :
    S.IsFiniteContravariantDefect.ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    S.vanishesOnProjectives_le_isFiniteContravariantDefect _
      (S.ContravariantVanishesOnProjectives.prop_of_isZero
        (isZero_zero _))⟩

noncomputable instance finiteCovariantDefect_containsZero :
    S.IsFiniteCovariantDefect.ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    S.vanishesOnInjectives_le_isFiniteCovariantDefect _
      (S.CovariantVanishesOnInjectives.prop_of_isZero
        (isZero_zero _))⟩

noncomputable instance finiteContravariantDefect_closedUnderSubobjects :
    S.IsFiniteContravariantDefect.IsClosedUnderSubobjects where
  prop_of_mono {X Y} f hf hY := by
    letI : Mono f := hf
    apply S.vanishesOnProjectives_le_isFiniteContravariantDefect
    exact S.ContravariantVanishesOnProjectives.prop_of_mono f
      (S.isFiniteContravariantDefect_le_vanishesOnProjectives Y hY)

noncomputable instance finiteContravariantDefect_closedUnderQuotients :
    S.IsFiniteContravariantDefect.IsClosedUnderQuotients where
  prop_of_epi {X Y} f hf hX := by
    letI : Epi f := hf
    apply S.vanishesOnProjectives_le_isFiniteContravariantDefect
    exact S.ContravariantVanishesOnProjectives.prop_of_epi f
      (S.isFiniteContravariantDefect_le_vanishesOnProjectives X hX)

noncomputable instance finiteCovariantDefect_closedUnderSubobjects :
    S.IsFiniteCovariantDefect.IsClosedUnderSubobjects where
  prop_of_mono {X Y} f hf hY := by
    letI : Mono f := hf
    apply S.vanishesOnInjectives_le_isFiniteCovariantDefect
    exact S.CovariantVanishesOnInjectives.prop_of_mono f
      (S.isFiniteCovariantDefect_le_vanishesOnInjectives Y hY)

noncomputable instance finiteCovariantDefect_closedUnderQuotients :
    S.IsFiniteCovariantDefect.IsClosedUnderQuotients where
  prop_of_epi {X Y} f hf hX := by
    letI : Epi f := hf
    apply S.vanishesOnInjectives_le_isFiniteCovariantDefect
    exact S.CovariantVanishesOnInjectives.prop_of_epi f
      (S.isFiniteCovariantDefect_le_vanishesOnInjectives X hX)

noncomputable instance finiteContravariantDefect_closedUnderExtensions :
    S.IsFiniteContravariantDefect.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    apply S.vanishesOnProjectives_le_isFiniteContravariantDefect
    exact S.ContravariantVanishesOnProjectives.prop_X₂_of_shortExact hT
      (S.isFiniteContravariantDefect_le_vanishesOnProjectives T.X₁ h₁)
      (S.isFiniteContravariantDefect_le_vanishesOnProjectives T.X₃ h₃)

noncomputable instance finiteCovariantDefect_closedUnderExtensions :
    S.IsFiniteCovariantDefect.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    apply S.vanishesOnInjectives_le_isFiniteCovariantDefect
    exact S.CovariantVanishesOnInjectives.prop_X₂_of_shortExact hT
      (S.isFiniteCovariantDefect_le_vanishesOnInjectives T.X₁ h₁)
      (S.isFiniteCovariantDefect_le_vanishesOnInjectives T.X₃ h₃)

noncomputable instance finiteContravariantDefect_closedUnderFiniteProducts :
    S.IsFiniteContravariantDefect.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    constructor
    rintro X ⟨p⟩
    apply S.vanishesOnProjectives_le_isFiniteContravariantDefect
    exact S.ContravariantVanishesOnProjectives.prop_of_isLimit p.isLimit
      (fun j ↦ S.isFiniteContravariantDefect_le_vanishesOnProjectives _
        (p.prop_diag_obj j))

noncomputable instance finiteCovariantDefect_closedUnderFiniteProducts :
    S.IsFiniteCovariantDefect.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    constructor
    rintro X ⟨p⟩
    apply S.vanishesOnInjectives_le_isFiniteCovariantDefect
    exact S.CovariantVanishesOnInjectives.prop_of_isLimit p.isLimit
      (fun j ↦ S.isFiniteCovariantDefect_le_vanishesOnInjectives _
        (p.prop_diag_obj j))

noncomputable instance finiteContravariantDefect_isSerreClass :
    S.IsFiniteContravariantDefect.IsSerreClass := {}

noncomputable instance finiteCovariantDefect_isSerreClass :
    S.IsFiniteCovariantDefect.IsSerreClass := {}

/-- Passing to the exact contravariant-defect subcategory does not change
whether an exact defect is uniserial. -/
theorem finiteContravariantDefect_isUniserial_iff_subcategory
    (F : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k) (hF : S.IsFiniteContravariantDefect F) :
    IsUniserialObject F ↔
      IsUniserialObject
        (⟨F, hF⟩ : S.FiniteContravariantDefectCategory) := by
  let E := MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
    S.IsFiniteContravariantDefect
      (⟨F, hF⟩ : S.FiniteContravariantDefectCategory)
  exact ⟨fun h ↦ IsUniserialObject.congrOrderIso h E.symm,
    fun h ↦ IsUniserialObject.congrOrderIso h E⟩

/-- Passing to the exact covariant-defect subcategory does not change
whether an exact defect is uniserial. -/
theorem finiteCovariantDefect_isUniserial_iff_subcategory
    (F : S.FiniteCovariantFunctor) (hF : S.IsFiniteCovariantDefect F) :
    IsUniserialObject F ↔
      IsUniserialObject
        (⟨F, hF⟩ : S.FiniteCovariantDefectCategory) := by
  let E := MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
    S.IsFiniteCovariantDefect
      (⟨F, hF⟩ : S.FiniteCovariantDefectCategory)
  exact ⟨fun h ↦ IsUniserialObject.congrOrderIso h E.symm,
    fun h ↦ IsUniserialObject.congrOrderIso h E⟩

/-- Auslander's coherent anti-equivalence preserves uniseriality for the two
defects attached to the same short exact module presentation. -/
theorem finiteContravariantDefect_isUniserial_iff_finiteCovariantDefect
    (K : ShortComplex (RightModule.FinitelyGeneratedCategory A))
    (hK : K.ShortExact) :
    IsUniserialObject (S.finiteContravariantDefect K) ↔
      IsUniserialObject (S.finiteCovariantDefect K) := by
  let F := S.contravariantDefectObject K hK
  let G := S.covariantDefectObject K hK
  let E := S.coherentDefectEquivalence
  let e := S.coherentDefectEquivalenceObjIso K hK
  constructor
  · intro h
    have hF : IsUniserialObject F :=
      (S.finiteContravariantDefect_isUniserial_iff_subcategory
        (S.finiteContravariantDefect K) F.property).mp h
    have hEF : IsUniserialObject (E.functor.obj (Opposite.op F)) :=
      (IsUniserialObject.op hF).map_equivalence E
    have hG : IsUniserialObject G := hEF.congr e
    exact (S.finiteCovariantDefect_isUniserial_iff_subcategory
      (S.finiteCovariantDefect K) G.property).mpr hG
  · intro h
    have hG : IsUniserialObject G :=
      (S.finiteCovariantDefect_isUniserial_iff_subcategory
        (S.finiteCovariantDefect K) G.property).mp h
    have hEF : IsUniserialObject (E.functor.obj (Opposite.op F)) :=
      hG.congr e.symm
    have hFop : IsUniserialObject (Opposite.op F) :=
      IsUniserialObject.of_map_equivalence E hEF
    have hF : IsUniserialObject F := IsUniserialObject.unop hFop
    exact (S.finiteContravariantDefect_isUniserial_iff_subcategory
      (S.finiteContravariantDefect K) F.property).mpr hF

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
