import MagnitudeConjecture.Algebra.RightModuleFiniteType
import MagnitudeConjecture.Algebra.IndecomposableLocalEnd
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleEssentialSocle
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleRepresentableGeneration
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.LinearCoveringSummand
import MagnitudeConjecture.CategoryTheory.LocallyBoundedOpposite
import MagnitudeConjecture.CategoryTheory.RadicalSubobject
import MagnitudeConjecture.CategoryTheory.ModuleFunctorExact
import MagnitudeConjecture.CategoryTheory.OppositeLinear
import MagnitudeConjecture.CategoryTheory.ProjectiveStableHom
import MagnitudeConjecture.CategoryTheory.RestrictedYoneda
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Stable representables on a finite indecomposable skeleton

For a representation-finite module category, the projective-stable
contravariant representable `stable Hom(-, C)` may be restricted to the
finite skeleton of indecomposables.  This file bundles that restriction as a
finite-dimensional linear module.  It is the functor appearing in
Auslander--Reiten's uniserial-functor criterion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ProjectiveStable

universe uk v u

variable {k : Type uk} [Field k]
variable {D : Type u} [Category.{v} D] [Preadditive D]
variable [CategoryTheory.Linear k D] [HasZeroObject D]
variable [HasBinaryBiproducts D]

/-- Precomposition on projective-stable Hom. -/
def precomp (Y : D) {X Z : D} (g : X ⟶ Z) :
    Hom (k := k) Z Y →ₗ[k] Hom (k := k) X Y :=
  (factorSubmodule (k := k) Z Y).mapQ
    (factorSubmodule (k := k) X Y)
    (CategoryTheory.Linear.leftComp k Y g) (by
      intro f hf
      obtain ⟨hfactor⟩ := hf
      exact ⟨hfactor.precomp g⟩)

@[simp]
theorem precomp_mk (Y : D) {X Z : D} (g : X ⟶ Z) (f : Z ⟶ Y) :
    precomp (k := k) Y g (mk (k := k) f) =
      mk (k := k) (g ≫ f) :=
  rfl

/-- If `q : P ⟶ Y` is an epimorphism from a projective object, then a
morphism into `Y` factors through some projective exactly when it factors
through `q`. -/
theorem factorSubmodule_eq_range_rightComp_of_projective_epi
    {P Y : D} (q : P ⟶ Y) [Projective P] [Epi q] (X : D) :
    factorSubmodule (k := k) X Y =
      LinearMap.range (CategoryTheory.Linear.rightComp k X q) := by
  ext f
  constructor
  · rintro ⟨hf⟩
    letI : Projective hf.middle := hf.projective
    let lift : hf.middle ⟶ P := Projective.factorThru hf.right q
    refine ⟨hf.left ≫ lift, ?_⟩
    change (hf.left ≫ lift) ≫ q = f
    rw [Category.assoc, Projective.factorThru_comp, hf.fac]
  · rintro ⟨g, rfl⟩
    exact ⟨{
      middle := P
      projective := inferInstance
      left := g
      right := q
      fac := rfl }⟩

end MagnitudeConjecture.ProjectiveStable

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

noncomputable local instance indecCategoryOppositeFintype :
    Fintype S.IndecCategoryᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

private def endRingEquivOfIso
    {D : Type*} [CategoryTheory.Category D] [CategoryTheory.Preadditive D]
    {X Y : D} (e : X ≅ Y) : End X ≃+* End Y :=
  { e.conj with
    map_add' := by
      intro f g
      apply End.ext
      change e.inv ≫ (End.asHom f + End.asHom g) ≫ e.hom =
        e.inv ≫ End.asHom f ≫ e.hom +
          e.inv ≫ End.asHom g ≫ e.hom
      simp only [Preadditive.comp_add, Preadditive.add_comp] }

/-- The restriction of `stable Hom(-, C)` to the opposite finite skeleton
of indecomposable right modules. -/
def projectiveStableContravariantRepresentable
    (C : RightModule.FinitelyGeneratedCategory A) :
    S.IndecCategoryᵒᵖ ⥤ ModuleCat.{u} k where
  obj X := ModuleCat.of k
    (ProjectiveStable.Hom (k := k) (S.inclusion.obj X.unop) C.obj)
  map {X Y} f := ModuleCat.ofHom <|
    ProjectiveStable.precomp (k := k) C.obj (S.inclusion.map f.unop)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change ProjectiveStable.mk (k := k)
        ((S.inclusion.map g.unop ≫ S.inclusion.map f.unop) ≫ h) =
      ProjectiveStable.mk (k := k)
        (S.inclusion.map g.unop ≫ (S.inclusion.map f.unop ≫ h))
    rw [Category.assoc]

instance projectiveStableContravariantRepresentable_additive
    (C : RightModule.FinitelyGeneratedCategory A) :
    (S.projectiveStableContravariantRepresentable C).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change ProjectiveStable.mk (k := k)
        ((S.inclusion.map f.unop + S.inclusion.map g.unop) ≫ h) =
      ProjectiveStable.mk (k := k) (S.inclusion.map f.unop ≫ h) +
        ProjectiveStable.mk (k := k) (S.inclusion.map g.unop ≫ h)
    simp

instance projectiveStableContravariantRepresentable_linear
    (C : RightModule.FinitelyGeneratedCategory A) :
    (S.projectiveStableContravariantRepresentable C).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change ProjectiveStable.mk (k := k)
        ((r • S.inclusion.map f.unop) ≫ h) =
      r • ProjectiveStable.mk (k := k) (S.inclusion.map f.unop ≫ h)
    simp

/-- The restricted stable representable as an additive linear module. -/
def projectiveStableContravariantRepresentableLinearModule
    (C : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.LinearModuleCategory (C := S.IndecCategoryᵒᵖ) k :=
  ⟨S.projectiveStableContravariantRepresentable C,
    inferInstance, inferInstance⟩

/-- On the finite indecomposable skeleton, the stable representable is a
finite-dimensional linear module. -/
theorem projectiveStableContravariantRepresentable_isFiniteDimensional
    (C : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategoryᵒᵖ) k
      (S.projectiveStableContravariantRepresentableLinearModule C) := by
  constructor
  · intro X
    letI : Module.Finite k (S.inclusion.obj X.unop) :=
      S.indecCategory_obj_finite X.unop
    letI : Module.Finite k C.obj :=
      RightModule.finite_over_field_of_finitelyGenerated k A C
    letI : Module.Finite k (S.inclusion.obj X.unop ⟶ C.obj) :=
      moduleCat_hom_finite (k := k) (A := A)
        (S.inclusion.obj X.unop) C.obj
    change Module.Finite k
      (ProjectiveStable.Hom (k := k) (S.inclusion.obj X.unop) C.obj)
    exact Module.Finite.quotient k
      (ProjectiveStable.factorSubmodule (k := k)
        (S.inclusion.obj X.unop) C.obj)
  · exact Set.toFinite _

/-- The restricted stable representable as an object of the finite functor
category. -/
def finiteProjectiveStableContravariantRepresentable
    (C : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k :=
  ⟨S.projectiveStableContravariantRepresentableLinearModule C,
    S.projectiveStableContravariantRepresentable_isFiniteDimensional C⟩

/-- The ordinary contravariant representable restricted to the finite
indecomposable skeleton. -/
def finiteRestrictedContravariantRepresentable
    (C : RightModule.FinitelyGeneratedCategory A) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k :=
  ⟨CoveringHom.restrictedLinearYonedaLinearModule
      (k := k) S.inclusion C.obj, by
    apply CoveringHom.restrictedLinearYoneda_isFiniteDimensional
      (k := k) S.inclusion C.obj
    intro X
    letI : Module.Finite k (S.inclusion.obj X) :=
      S.indecCategory_obj_finite X
    letI : Module.Finite k C.obj :=
      RightModule.finite_over_field_of_finitelyGenerated k A C
    exact moduleCat_hom_finite (k := k) (A := A)
      (S.inclusion.obj X) C.obj⟩

/-- The representable at an object of the opposite indecomposable skeleton
is finite-dimensional. -/
def indecOppositeRepresentableFinite (i : S.IndecCategory) :
    CoveringHom.IsFiniteDimensionalModule
      (C := S.IndecCategoryᵒᵖ) k
      (CoveringHom.linearCoyonedaLinearModule
        (k := k) (Opposite.op i)) := by
  constructor
  · intro X
    letI : Module.Finite k (S.inclusion.obj X.unop) :=
      S.indecCategory_obj_finite X.unop
    letI : Module.Finite k (S.inclusion.obj i) :=
      S.indecCategory_obj_finite i
    letI : Module.Finite k
        (S.inclusion.obj X.unop ⟶ S.inclusion.obj i) :=
      moduleCat_hom_finite (k := k) (A := A)
        (S.inclusion.obj X.unop) (S.inclusion.obj i)
    let e := CoveringHom.oppositeHomLinearEquiv
      (k := k) (C := S.IndecCategory)
      (Opposite.op i) X
    exact e.symm.finiteDimensional
  · exact Set.toFinite _

/-- Ambient morphisms between chosen skeleton objects are the same as
morphisms in the induced skeleton, written in the variance appropriate for
the opposite representable. -/
def restrictedFgObjOppositeHomLinearEquiv
    (i : S.IndecCategory) (X : S.IndecCategoryᵒᵖ) :
    (S.inclusion.obj X.unop ⟶ S.inclusion.obj i) ≃ₗ[k]
      ((Opposite.op i : S.IndecCategoryᵒᵖ) ⟶ X) where
  toFun f := (InducedCategory.homMk f).op
  invFun f := f.unop.hom
  left_inv _ := rfl
  right_inv f := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restricted ambient Yoneda at a chosen indecomposable agrees naturally
with the corresponding representable of the opposite finite skeleton. -/
def restrictedContravariantRepresentableFgObjRawIso
    (i : S.IndecCategory) :
    CoveringHom.restrictedLinearYoneda
        (k := k) S.inclusion (S.fgObj i).obj ≅
      (CategoryTheory.linearCoyoneda k S.IndecCategoryᵒᵖ).obj
        (Opposite.op (Opposite.op i)) := by
  refine NatIso.ofComponents (fun X ↦
    (S.restrictedFgObjOppositeHomLinearEquiv i X).toModuleIso) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  rfl

/-- Linear-module form of the comparison with the opposite-skeleton
representable. -/
def restrictedContravariantRepresentableFgObjLinearIso
    (i : S.IndecCategory) :
    CoveringHom.restrictedLinearYonedaLinearModule
        (k := k) S.inclusion (S.fgObj i).obj ≅
      CoveringHom.linearCoyonedaLinearModule
        (k := k) (Opposite.op i) :=
  ObjectProperty.isoMk _
    (S.restrictedContravariantRepresentableFgObjRawIso i)

/-- Finite-module form of the comparison with the opposite-skeleton
representable. -/
def finiteRestrictedContravariantRepresentableFgObjIso
    (i : S.IndecCategory) :
    S.finiteRestrictedContravariantRepresentable (S.fgObj i) ≅
      CoveringHom.finiteDimensionalLinearCoyoneda
        (k := k) (Opposite.op i)
        (S.indecOppositeRepresentableFinite i) :=
  ObjectProperty.isoMk _
    (S.restrictedContravariantRepresentableFgObjLinearIso i)

/-- A nonzero finite functor on the indecomposable skeleton receives a
nonzero map from one restricted representable. -/
theorem finiteDimensionalModule_exists_nonzero_restrictedRepresentableMap
    {M : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (hM : ¬ IsZero M) :
    ∃ (i : S.IndecCategory)
      (f : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ M),
      f ≠ 0 := by
  let hP : ∀ X : S.IndecCategoryᵒᵖ,
      CoveringHom.IsFiniteDimensionalModule (C := S.IndecCategoryᵒᵖ) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) :=
    fun X ↦ by simpa only [Opposite.op_unop] using
      S.indecOppositeRepresentableFinite X.unop
  obtain ⟨X, f, hf⟩ :=
    CoveringHom.finiteDimensionalModule_exists_nonzero_representableMap hP hM
  let i := X.unop
  let e := S.finiteRestrictedContravariantRepresentableFgObjIso i
  refine ⟨i, e.hom ≫ f, ?_⟩
  intro hzero
  apply hf
  apply (cancel_epi e.hom).1
  exact hzero

/-- To prove a simple finite subfunctor essential, it suffices to factor the
composites of its nonzero restricted-representable generators through it. -/
theorem finiteDimensionalModule_isEssentialMono_of_simple_restrictedRepresentable_factors
    {L F : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    [Simple L] (l : L ⟶ F) [Mono l]
    (hfactor : ∀ {T : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k} [Simple T]
      (t : T ⟶ F) [Mono t] (i : S.IndecCategory)
      (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T),
      p ≠ 0 → ∃ a : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ L,
        a ≫ l = p ≫ t) :
    IsEssentialMono l := by
  apply CoveringHom.finiteDimensionalModule_isEssentialMono_of_simple_factors l
  intro T _ t _ ht
  have hT : ¬ IsZero T := by
    intro hzero
    exact CategoryTheory.id_nonzero T (hzero.eq_of_src (𝟙 T) 0)
  obtain ⟨i, p, hp⟩ :=
    S.finiteDimensionalModule_exists_nonzero_restrictedRepresentableMap hT
  letI : Epi p := epi_of_nonzero_to_simple hp
  obtain ⟨a, ha⟩ := hfactor t i p hp
  have htc : t ≫ cokernel.π l = 0 := by
    apply (cancel_epi p).1
    change (p ≫ t) ≫ cokernel.π l = 0
    rw [← ha, Category.assoc, cokernel.condition, comp_zero]
  exact ⟨Abelian.monoLift l t htc, Abelian.monoLift_comp l t htc⟩

/-- A chosen object has local endomorphism ring already in the induced
indecomposable skeleton. -/
theorem indecCategory_obj_end_isLocalRing (i : S.IndecCategory) :
    IsLocalRing (End i) := by
  letI : Module.Finite k Aᵐᵒᵖ := inferInstance
  letI : Module.Finite k (S.inclusion.obj i) :=
    S.indecCategory_obj_finite i
  letI : IsLocalRing (End (S.inclusion.obj i)) :=
    MagnitudeConjecture.moduleCat_end_isLocalRing
      (k := k) (A := Aᵐᵒᵖ) (S.inclusion.obj i)
      (S.indecCategory_obj_indecomposable i)
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (CategoryTheory.Functor.endRingEquivOfFullyFaithful
      S.inclusion i).symm

/-- Local endomorphism rings pass to objects of the opposite finite
indecomposable skeleton. -/
theorem indecCategoryOpposite_obj_end_isLocalRing
    (X : S.IndecCategoryᵒᵖ) : IsLocalRing (End X) := by
  letI : IsLocalRing (End X.unop) :=
    S.indecCategory_obj_end_isLocalRing X.unop
  letI : IsLocalRing (End X.unop)ᵐᵒᵖ :=
    CoveringHom.isLocalRing_mulOpposite
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (CoveringHom.oppositeEndRingEquiv X.unop)

instance finiteRestrictedContravariantRepresentableFgObj_projective
    (i : S.IndecCategory) :
    Projective
      (S.finiteRestrictedContravariantRepresentable (S.fgObj i)) :=
  Projective.of_iso
    (S.finiteRestrictedContravariantRepresentableFgObjIso i).symm
      inferInstance

/-- The ordinary restricted representable at a chosen indecomposable has
local endomorphism ring. -/
theorem finiteRestrictedContravariantRepresentableFgObj_end_isLocalRing
    (i : S.IndecCategory) :
    IsLocalRing (End
      (S.finiteRestrictedContravariantRepresentable (S.fgObj i))) := by
  let hfinite : ∀ X : S.IndecCategoryᵒᵖ,
      CoveringHom.IsFiniteDimensionalModule
        (C := S.IndecCategoryᵒᵖ) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) :=
    fun X ↦ by
      simpa only [Opposite.op_unop] using
        S.indecOppositeRepresentableFinite X.unop
  let hlocal : ∀ X : S.IndecCategoryᵒᵖ, IsLocalRing (End X) :=
    S.indecCategoryOpposite_obj_end_isLocalRing
  let R := (CoveringHom.finiteDimensionalLinearCoyonedaFunctor
    (k := k) hfinite).obj (Opposite.op (Opposite.op i))
  let e : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ≅ R :=
    ObjectProperty.isoMk _
      (S.restrictedContravariantRepresentableFgObjLinearIso i)
  letI : IsLocalRing (End R) :=
    CoveringHom.finiteDimensionalLinearCoyoneda_end_isLocalRing
      hfinite hlocal (Opposite.op i)
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (endRingEquivOfIso e).symm

/-- The categorical radical of the finite representable corresponding to a
chosen indecomposable, transported to the restricted ambient representable. -/
def finiteRestrictedContravariantRepresentableRadical
    (i : S.IndecCategory) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k :=
  CoveringHom.finiteDimensionalLinearCoyonedaRadical
    (k := k) (Opposite.op i) (S.indecOppositeRepresentableFinite i)

/-- The radical inclusion after transporting from the opposite-skeleton
representable to the restricted ambient representable. -/
def finiteRestrictedContravariantRepresentableRadicalInclusion
    (i : S.IndecCategory) :
    S.finiteRestrictedContravariantRepresentableRadical i ⟶
      S.finiteRestrictedContravariantRepresentable (S.fgObj i) :=
  CoveringHom.finiteDimensionalLinearCoyonedaRadicalInclusion
      (k := k) (Opposite.op i) (S.indecOppositeRepresentableFinite i) ≫
    (S.finiteRestrictedContravariantRepresentableFgObjIso i).inv

@[simp]
theorem finiteRestrictedContravariantRepresentableRadicalInclusion_app_apply
    (i : S.IndecCategory) (X : S.IndecCategoryᵒᵖ)
    (q : MagnitudeConjecture.CategoryTheory.radicalHomSubmodule
      k (Opposite.op i) X) :
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i).hom.hom.app X q =
      q.1.unop.hom :=
  rfl

instance finiteRestrictedContravariantRepresentableRadicalInclusion_mono
    (i : S.IndecCategory) :
    Mono (S.finiteRestrictedContravariantRepresentableRadicalInclusion i) := by
  change Mono
    (CoveringHom.finiteDimensionalLinearCoyonedaRadicalInclusion
        (k := k) (Opposite.op i) (S.indecOppositeRepresentableFinite i) ≫
      (S.finiteRestrictedContravariantRepresentableFgObjIso i).inv)
  infer_instance

/-- The transported radical inclusion is the right almost-split boundary of
the chosen restricted representable. -/
theorem finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit
    (i : S.IndecCategory) :
    IsRightAlmostSplit
      (S.finiteRestrictedContravariantRepresentableRadicalInclusion i) := by
  let hfinite : ∀ X : S.IndecCategoryᵒᵖ,
      CoveringHom.IsFiniteDimensionalModule
        (C := S.IndecCategoryᵒᵖ) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) :=
    fun X ↦ by
      simpa only [Opposite.op_unop] using
        S.indecOppositeRepresentableFinite X.unop
  let hlocal : ∀ X : S.IndecCategoryᵒᵖ, IsLocalRing (End X) :=
    S.indecCategoryOpposite_obj_end_isLocalRing
  have hr :=
    CoveringHom.finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hfinite hlocal (Opposite.op i)
  exact hr.postcomp_iso
    (S.finiteRestrictedContravariantRepresentableFgObjIso i).symm

/-- Postcomposition gives the expected map between two restricted ordinary
representables. -/
def finiteRestrictedContravariantRepresentableMap
    {C D : RightModule.FinitelyGeneratedCategory A} (f : C ⟶ D) :
    S.finiteRestrictedContravariantRepresentable C ⟶
      S.finiteRestrictedContravariantRepresentable D :=
  ObjectProperty.homMk <|
    CoveringHom.restrictedLinearYonedaLinearModuleMap
      (k := k) S.inclusion f.hom

@[simp]
theorem finiteRestrictedContravariantRepresentableMap_app_apply
    {C D : RightModule.FinitelyGeneratedCategory A} (f : C ⟶ D)
    (X : S.IndecCategoryᵒᵖ)
    (g : S.inclusion.obj X.unop ⟶ C.obj) :
    (S.finiteRestrictedContravariantRepresentableMap f).hom.hom.app X g =
      g ≫ f.hom :=
  rfl

/-- Restricted Yoneda is full on the chosen indecomposable skeleton: a map
between two represented functors is recovered by evaluating it at the
identity of its source. -/
theorem finiteRestrictedContravariantRepresentableMap_fgObj_eq
    (i j : S.IndecCategory)
    (f : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶
      S.finiteRestrictedContravariantRepresentable (S.fgObj j)) :
    let h : S.fgObj i ⟶ S.fgObj j := ObjectProperty.homMk (by
      change S.obj i ⟶ S.obj j
      exact f.hom.hom.app (Opposite.op i) (𝟙 (S.inclusion.obj i)))
    S.finiteRestrictedContravariantRepresentableMap h = f := by
  dsimp
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change q ≫ f.hom.hom.app (Opposite.op i) (𝟙 (S.inclusion.obj i)) =
    f.hom.hom.app X q
  let q' : X.unop ⟶ i := InducedCategory.homMk (by
    exact q)
  have h := ConcreteCategory.congr_hom
    (f.hom.hom.naturality q'.op)
    (𝟙 (S.inclusion.obj i))
  exact h.symm

@[simp]
theorem finiteRestrictedContravariantRepresentableMap_comp
    {B C D : RightModule.FinitelyGeneratedCategory A}
    (f : B ⟶ C) (g : C ⟶ D) :
    S.finiteRestrictedContravariantRepresentableMap (f ≫ g) =
      S.finiteRestrictedContravariantRepresentableMap f ≫
        S.finiteRestrictedContravariantRepresentableMap g := by
  apply ObjectProperty.hom_ext
  exact CoveringHom.restrictedLinearYonedaLinearModuleMap_comp
    (k := k) S.inclusion f.hom g.hom

@[simp]
theorem finiteRestrictedContravariantRepresentableMap_id
    (C : RightModule.FinitelyGeneratedCategory A) :
    S.finiteRestrictedContravariantRepresentableMap (𝟙 C) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  exact CoveringHom.restrictedLinearYonedaLinearModuleMap_id
    (k := k) S.inclusion C.obj

instance finiteRestrictedContravariantRepresentableMap_isIso
    {C D : RightModule.FinitelyGeneratedCategory A} (f : C ⟶ D)
    [IsIso f] : IsIso (S.finiteRestrictedContravariantRepresentableMap f) := by
  apply IsIso.mk
  refine ⟨S.finiteRestrictedContravariantRepresentableMap (inv f), ?_, ?_⟩
  · rw [← finiteRestrictedContravariantRepresentableMap_comp,
      IsIso.hom_inv_id, finiteRestrictedContravariantRepresentableMap_id]
  · rw [← finiteRestrictedContravariantRepresentableMap_comp,
      IsIso.inv_hom_id, finiteRestrictedContravariantRepresentableMap_id]

@[simp]
theorem finiteRestrictedContravariantRepresentableMap_add
    {C D : RightModule.FinitelyGeneratedCategory A} (f g : C ⟶ D) :
    S.finiteRestrictedContravariantRepresentableMap (f + g) =
      S.finiteRestrictedContravariantRepresentableMap f +
        S.finiteRestrictedContravariantRepresentableMap g := by
  apply ObjectProperty.hom_ext
  exact (CoveringHom.restrictedLinearYonedaFunctor
    (k := k) S.inclusion).map_add

@[simp]
theorem finiteRestrictedContravariantRepresentableMap_zero
    (C D : RightModule.FinitelyGeneratedCategory A) :
    S.finiteRestrictedContravariantRepresentableMap (0 : C ⟶ D) = 0 := by
  apply ObjectProperty.hom_ext
  exact (CoveringHom.restrictedLinearYonedaFunctor
    (k := k) S.inclusion).map_zero C.obj D.obj

@[simp]
theorem finiteRestrictedContravariantRepresentableMap_neg
    {C D : RightModule.FinitelyGeneratedCategory A} (f : C ⟶ D) :
    S.finiteRestrictedContravariantRepresentableMap (-f) =
      -S.finiteRestrictedContravariantRepresentableMap f := by
  apply ObjectProperty.hom_ext
  exact (CoveringHom.restrictedLinearYonedaFunctor
    (k := k) S.inclusion).map_neg

/-- A split summand and its chosen complement decompose the restricted
representable map induced by any morphism out of the ambient object. -/
theorem finiteRestrictedContravariantRepresentableMap_eq_splitMono_add_complement
    {X Y Z : RightModule.FinitelyGeneratedCategory A}
    (t : X ⟶ Y) [IsSplitMono t]
    (d : QuotientSubmoduleEquidistribution.SplitMonoComplement t)
    (f : Y ⟶ Z) :
    S.finiteRestrictedContravariantRepresentableMap f =
      S.finiteRestrictedContravariantRepresentableMap (retraction t) ≫
          S.finiteRestrictedContravariantRepresentableMap (t ≫ f) +
        S.finiteRestrictedContravariantRepresentableMap d.projection ≫
          S.finiteRestrictedContravariantRepresentableMap
            (d.inclusion ≫ f) := by
  rw [← finiteRestrictedContravariantRepresentableMap_comp,
    ← finiteRestrictedContravariantRepresentableMap_comp,
    ← finiteRestrictedContravariantRepresentableMap_add]
  congr 1
  calc
    f = 𝟙 Y ≫ f := (Category.id_comp f).symm
    _ = (retraction t ≫ t + d.projection ≫ d.inclusion) ≫ f := by
      rw [d.total]
    _ = retraction t ≫ t ≫ f +
        d.projection ≫ d.inclusion ≫ f := by
      rw [Preadditive.add_comp]
      simp only [Category.assoc]

/-- If one split-summand branch is killed after a further map, the whole
image is generated by the complementary branch. -/
theorem finiteRestrictedContravariantRepresentableMap_comp_eq_complement
    {X Y Z : RightModule.FinitelyGeneratedCategory A}
    (t : X ⟶ Y) [IsSplitMono t]
    (d : QuotientSubmoduleEquidistribution.SplitMonoComplement t)
    (f : Y ⟶ Z)
    {G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (p : S.finiteRestrictedContravariantRepresentable Z ⟶ G)
    (hzero :
      S.finiteRestrictedContravariantRepresentableMap (t ≫ f) ≫ p = 0) :
    S.finiteRestrictedContravariantRepresentableMap f ≫ p =
      S.finiteRestrictedContravariantRepresentableMap d.projection ≫
        (S.finiteRestrictedContravariantRepresentableMap
          (d.inclusion ≫ f) ≫ p) := by
  rw [S.finiteRestrictedContravariantRepresentableMap_eq_splitMono_add_complement
    t d f, Preadditive.add_comp, Category.assoc, hzero, comp_zero,
    zero_add, Category.assoc]

/-- A nonsplit epimorphism onto a chosen indecomposable remains nonsplit
after applying restricted Yoneda, even when its source is not itself a
chosen indecomposable. -/
theorem finiteRestrictedContravariantRepresentableMap_to_fgObj_not_isSplitEpi
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (f : C ⟶ S.fgObj i)
    (hf : ¬ IsSplitEpi f) :
    ¬ IsSplitEpi (S.finiteRestrictedContravariantRepresentableMap f) := by
  intro hsplit
  letI : IsSplitEpi
      (S.finiteRestrictedContravariantRepresentableMap f) := hsplit
  let g : S.fgObj i ⟶ C := ObjectProperty.homMk
    ((section_ (S.finiteRestrictedContravariantRepresentableMap f)).hom.hom.app
      (Opposite.op i) (𝟙 (S.inclusion.obj i)))
  apply hf
  apply IsSplitEpi.mk'
  refine { section_ := g, id := ?_ }
  apply ObjectProperty.hom_ext
  have hs := congrArg
    (fun q : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶
        S.finiteRestrictedContravariantRepresentable (S.fgObj i) ↦
      q.hom.hom.app (Opposite.op i) (𝟙 (S.inclusion.obj i)))
    (IsSplitEpi.id
      (S.finiteRestrictedContravariantRepresentableMap f))
  exact hs

/-- Restricted Yoneda sends a right almost-split map ending at a chosen
indecomposable onto the whole radical of the corresponding representable. -/
theorem imageSubobject_finiteRestrictedContravariantRepresentableMap_eq_radical
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (f : C ⟶ S.fgObj i)
    (hf : IsRightAlmostSplit f) :
    imageSubobject (S.finiteRestrictedContravariantRepresentableMap f) =
      Subobject.mk
        (S.finiteRestrictedContravariantRepresentableRadicalInclusion i) := by
  let F := S.finiteRestrictedContravariantRepresentableMap f
  let r := S.finiteRestrictedContravariantRepresentableRadicalInclusion i
  obtain ⟨l, hl⟩ :=
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit i).factors
      F
      (S.finiteRestrictedContravariantRepresentableMap_to_fgObj_not_isSplitEpi
        i f hf.not_isSplitEpi)
  let I := imageSubobject F
  let R := Subobject.mk r
  have hle : I ≤ R := imageSubobject_le_mk r F l hl
  let a : (I : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k) ⟶
      (R : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) :=
    Subobject.ofLE I R hle
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  let L := (CoveringHom.IsLinearModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  have happ (X : S.IndecCategoryᵒᵖ) : Epi
      ((L.map (J.map a)).app X) := by
    rw [ModuleCat.epi_iff_surjective]
    intro q
    let eR := Subobject.underlyingIso r
    let qR := ((L.map (J.map eR.hom)).app X) q
    let y : S.fgObj X.unop ⟶ S.fgObj i :=
      ObjectProperty.homMk qR.1.unop.hom
    have hnot : ¬ IsSplitEpi y := by
      intro hsplit
      letI : IsSplitEpi y := hsplit
      have hzero : ¬ IsZero (Opposite.op i) := by
        intro hz
        exact (S.indecCategory_obj_indecomposable i).1
          (S.inclusion.map_isZero (IsZero.unop hz))
      letI : IsLocalRing (End (Opposite.op i)) :=
        S.indecCategoryOpposite_obj_end_isLocalRing (Opposite.op i)
      have hqNot : ¬ IsSplitMono qR.1 :=
        (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
          hzero qR.1).1 qR.2
      apply hqNot
      apply IsSplitMono.mk'
      refine { retraction := (show X ⟶ Opposite.op i from
          (show i ⟶ X.unop from
            InducedCategory.homMk (section_ y).hom).op), id := ?_ }
      apply Quiver.Hom.unop_inj
      apply InducedCategory.hom_ext
      exact congrArg (fun q : S.fgObj i ⟶ S.fgObj i ↦ q.hom)
        (IsSplitEpi.id y)
    obtain ⟨t, ht⟩ := hf.factors y hnot
    let z := ((L.map (J.map (factorThruImageSubobject F))).app X) t.hom
    refine ⟨z, ?_⟩
    have hrinj : Function.Injective
        ((L.map (J.map r)).app X) := by
      intro x₁ x₂ hx
      apply Subtype.ext
      apply Quiver.Hom.unop_inj
      apply InducedCategory.hom_ext
      exact hx
    have heinj : Function.Injective
        ((L.map (J.map eR.hom)).app X) :=
      (ModuleCat.mono_iff_injective
        ((L.map (J.map eR.hom)).app X)).1 inferInstance
    have hRinj : Function.Injective
        ((L.map (J.map R.arrow)).app X) := by
      intro x₁ x₂ hx
      apply heinj
      apply hrinj
      have hRarrow : eR.hom ≫ r = R.arrow :=
        Subobject.underlyingIso_hom_comp_eq_mk r
      have hmapped := congrArg
        (fun m : (R : CoveringHom.FiniteDimensionalModuleCategory
            (C := S.IndecCategoryᵒᵖ) k) ⟶
            S.finiteRestrictedContravariantRepresentable (S.fgObj i) ↦
          (L.map (J.map m)).app X)
        hRarrow
      rw [← hRarrow, Functor.map_comp, Functor.map_comp] at hx
      simpa only [NatTrans.comp_app, ModuleCat.comp_apply] using hx
    apply hRinj
    have ha :
        (L.map (J.map a)).app X ≫
            (L.map (J.map R.arrow)).app X =
          (L.map (J.map I.arrow)).app X := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
        Subobject.ofLE_arrow]
    change
      ((L.map (J.map R.arrow)).app X)
          (((L.map (J.map a)).app X) z) =
        ((L.map (J.map R.arrow)).app X) q
    change
      ((L.map (J.map a)).app X ≫
          (L.map (J.map R.arrow)).app X) z =
        ((L.map (J.map R.arrow)).app X) q
    rw [ha]
    change
      ((L.map (J.map I.arrow)).app X) z =
        (L.map (J.map R.arrow)).app X q
    dsimp only [z]
    have hImage :
        (L.map (J.map (factorThruImageSubobject F))).app X ≫
            (L.map (J.map I.arrow)).app X =
          (L.map (J.map F)).app X := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
        imageSubobject_arrow_comp]
    change
      ((L.map (J.map (factorThruImageSubobject F))).app X ≫
          (L.map (J.map I.arrow)).app X) t.hom =
        (L.map (J.map R.arrow)).app X q
    rw [hImage]
    have hRq :
        (L.map (J.map R.arrow)).app X q =
          (L.map (J.map r)).app X qR := by
      change
        (L.map (J.map R.arrow)).app X q =
          (L.map (J.map r)).app X
            ((L.map (J.map eR.hom)).app X q)
      rw [← ModuleCat.comp_apply, ← NatTrans.comp_app,
        ← Functor.map_comp, ← Functor.map_comp,
        Subobject.underlyingIso_hom_comp_eq_mk]
    rw [hRq]
    change t.hom ≫ f.hom = qR.1.unop.hom
    exact congrArg
      (fun q : S.fgObj X.unop ⟶ S.fgObj i ↦ q.hom) ht
  have hnat : Epi (L.map (J.map a)) := NatTrans.epi_of_epi_app _
  have hlinear : Epi (J.map a) := L.epi_of_epi_map hnat
  have haEpi : Epi a := J.epi_of_epi_map hlinear
  letI : Epi a := haEpi
  letI : IsIso a := isIso_of_mono_of_epi a
  exact Subobject.eq_of_comm (asIso a) (Subobject.ofLE_arrow hle)

section

set_option synthInstance.maxHeartbeats 100000

universe v' u'

/-- In an abelian category, precomposing a morphism by an epimorphism does
not change its image subobject. -/
theorem imageSubobject_comp_eq_of_epi
    {D : Type u'} [CategoryTheory.Category.{v'} D] [Abelian D]
    {X Y Z : D} (e : X ⟶ Y) [Epi e] (q : Y ⟶ Z) :
    imageSubobject (e ≫ q) = imageSubobject q := by
  let I := imageSubobject (e ≫ q)
  let J := imageSubobject q
  have hle : I ≤ J := imageSubobject_comp_le e q
  haveI : Epi (Subobject.ofLE I J hle) :=
    imageSubobject_comp_le_epi_of_epi e q
  haveI : IsIso (Subobject.ofLE I J hle) :=
    isIso_of_mono_of_epi (Subobject.ofLE I J hle)
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE I J hle))
    (Subobject.ofLE_arrow hle)

/-- Postcomposition by a monomorphism preserves the object underlying an
image, although it changes the ambient object in which the image sits. -/
def imageSubobjectCompMonoIso
    {D : Type u'} [CategoryTheory.Category.{v'} D] [Abelian D]
    {X Y Z : D} (q : X ⟶ Y) (m : Y ⟶ Z) [Mono m] :
    (imageSubobject q : D) ≅ (imageSubobject (q ≫ m) : D) := by
  letI : StrongEpi (factorThruImageSubobject q) :=
    strongEpi_of_epi (factorThruImageSubobject q)
  exact image.isoStrongEpiMono
      (factorThruImageSubobject q) ((imageSubobject q).arrow ≫ m)
      (by rw [← Category.assoc, imageSubobject_arrow_comp]) ≪≫
    (imageSubobjectIso (q ≫ m)).symm

/-- Precomposition by the epimorphism onto an image does not change the
image after a further morphism. -/
private theorem imageSubobject_comp_eq_imageSubobject_arrow_comp
    {D : Type u'} [CategoryTheory.Category.{v'} D] [Abelian D]
    {X Y Z : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) =
      imageSubobject ((imageSubobject f).arrow ≫ g) := by
  let e := factorThruImageSubobject f
  let q := (imageSubobject f).arrow ≫ g
  have he : Epi e := inferInstance
  have hfac : e ≫ q = f ≫ g := by
    dsimp only [e, q]
    rw [← Category.assoc, imageSubobject_arrow_comp]
  rw [← hfac]
  exact imageSubobject_comp_eq_of_epi e q

end

/-- Pushing a representable radical through any further map can equivalently
be computed from any right almost-split map ending at that representable. -/
theorem imageSubobject_radicalInclusion_comp_eq_rightAlmostSplit_comp
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (f : C ⟶ S.fgObj i)
    (hf : IsRightAlmostSplit f)
    {G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G) :
    imageSubobject
        (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫ p) =
      imageSubobject
        (S.finiteRestrictedContravariantRepresentableMap f ≫ p) := by
  let r := S.finiteRestrictedContravariantRepresentableRadicalInclusion i
  let F := S.finiteRestrictedContravariantRepresentableMap f
  calc
    imageSubobject (r ≫ p) =
        imageSubobject ((imageSubobject r).arrow ≫ p) :=
      imageSubobject_comp_eq_imageSubobject_arrow_comp r p
    _ = imageSubobject ((Subobject.mk r).arrow ≫ p) := by
      rw [imageSubobject_mono r]
    _ = imageSubobject ((imageSubobject F).arrow ≫ p) := by
      rw [S.imageSubobject_finiteRestrictedContravariantRepresentableMap_eq_radical
        i f hf]
    _ = imageSubobject (F ≫ p) := by
      simpa only [F] using
        (imageSubobject_comp_eq_imageSubobject_arrow_comp
          (S.finiteRestrictedContravariantRepresentableMap f) p).symm

/-- A nonsplit epimorphism between ambient modules remains nonsplit after
applying the restricted contravariant representable construction. -/
theorem finiteRestrictedContravariantRepresentableMap_not_isSplitEpi
    {i j : S.IndecCategory} (f : S.fgObj j ⟶ S.fgObj i)
    (hf : ¬ IsSplitEpi f) :
    ¬ IsSplitEpi (S.finiteRestrictedContravariantRepresentableMap f) := by
  exact S.finiteRestrictedContravariantRepresentableMap_to_fgObj_not_isSplitEpi
    i f hf

/-- An irreducible map between chosen indecomposables factors, after
restricted Yoneda, through the transported radical of its target. -/
theorem exists_finiteRestrictedContravariantRepresentableRadicalFactor
    {i j : S.IndecCategory} (f : S.fgObj j ⟶ S.fgObj i)
    (hf : IsIrreducibleMorphism f) :
    ∃ l : S.finiteRestrictedContravariantRepresentable (S.fgObj j) ⟶
        S.finiteRestrictedContravariantRepresentableRadical i,
      l ≫ S.finiteRestrictedContravariantRepresentableRadicalInclusion i =
        S.finiteRestrictedContravariantRepresentableMap f := by
  exact
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit i).factors
      (S.finiteRestrictedContravariantRepresentableMap f)
      (S.finiteRestrictedContravariantRepresentableMap_not_isSplitEpi
        f hf.not_isSplitEpi)

/-- The objectwise stable-quotient map from the restricted ordinary
representable to the restricted projective-stable representable. -/
def projectiveStableQuotientLinearModule
    (C : RightModule.FinitelyGeneratedCategory A) :
    (S.finiteRestrictedContravariantRepresentable C).obj ⟶
      (S.finiteProjectiveStableContravariantRepresentable C).obj :=
  ObjectProperty.homMk
    { app := fun X ↦ ModuleCat.ofHom
        (ProjectiveStable.mk (k := k))
      naturality := by
        intro X Y f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro h
        rfl }

/-- The stable-quotient map in the finite-dimensional functor category. -/
def finiteProjectiveStableQuotient
    (C : RightModule.FinitelyGeneratedCategory A) :
    S.finiteRestrictedContravariantRepresentable C ⟶
      S.finiteProjectiveStableContravariantRepresentable C :=
  ObjectProperty.homMk (S.projectiveStableQuotientLinearModule C)

/-- A module morphism out of a chosen indecomposable represents a natural
map into the stable representable of its target. -/
def finiteRestrictedToProjectiveStableMap
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C) :
    S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶
      S.finiteProjectiveStableContravariantRepresentable C :=
  S.finiteRestrictedContravariantRepresentableMap h ≫
    S.finiteProjectiveStableQuotient C

@[simp]
theorem finiteRestrictedToProjectiveStableMap_app_apply
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (X : S.IndecCategoryᵒᵖ)
    (f : S.inclusion.obj X.unop ⟶ S.inclusion.obj i) :
    (S.finiteRestrictedToProjectiveStableMap i h).hom.hom.app X f =
      ProjectiveStable.mk (k := k) (f ≫ h.hom) :=
  rfl

/-- Precomposing a stable generator by an ordinary morphism agrees with
postcomposing the corresponding restricted representable map. -/
theorem finiteRestrictedContravariantRepresentableMap_comp_stableMap
    {C : RightModule.FinitelyGeneratedCategory A}
    {i j : S.IndecCategory} (f : S.fgObj j ⟶ S.fgObj i)
    (h : S.fgObj i ⟶ C) :
    S.finiteRestrictedContravariantRepresentableMap f ≫
        S.finiteRestrictedToProjectiveStableMap i h =
      S.finiteRestrictedToProjectiveStableMap j (f ≫ h) := by
  rw [finiteRestrictedToProjectiveStableMap,
    finiteRestrictedToProjectiveStableMap,
    finiteRestrictedContravariantRepresentableMap_comp]
  simp only [Category.assoc]

/-- The finite functor generated by one stable morphism. -/
def finiteProjectiveStableImage
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k :=
  (imageSubobject (S.finiteRestrictedToProjectiveStableMap i h) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k)

/-- The canonical inclusion of a cyclic stable image into the full stable
representable. -/
def finiteProjectiveStableImageInclusion
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C) :
    S.finiteProjectiveStableImage i h ⟶
      S.finiteProjectiveStableContravariantRepresentable C := by
  change
    (imageSubobject (S.finiteRestrictedToProjectiveStableMap i h) :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k) ⟶
      S.finiteProjectiveStableContravariantRepresentable C
  exact (imageSubobject
    (S.finiteRestrictedToProjectiveStableMap i h)).arrow

instance finiteProjectiveStableImageInclusion_mono
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C) :
    Mono (S.finiteProjectiveStableImageInclusion i h) := by
  change Mono (imageSubobject
    (S.finiteRestrictedToProjectiveStableMap i h)).arrow
  infer_instance

/-- The canonical epimorphism from the representing projective onto the
stable image generated by a morphism. -/
def finiteProjectiveStableImagePresentation
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C) :
    S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶
      S.finiteProjectiveStableImage i h :=
  factorThruImageSubobject
    (S.finiteRestrictedToProjectiveStableMap i h)

@[reassoc]
theorem finiteProjectiveStableImagePresentation_comp_inclusion
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C) :
    S.finiteProjectiveStableImagePresentation i h ≫
        S.finiteProjectiveStableImageInclusion i h =
      S.finiteRestrictedToProjectiveStableMap i h := by
  change factorThruImageSubobject
      (S.finiteRestrictedToProjectiveStableMap i h) ≫
      (imageSubobject
        (S.finiteRestrictedToProjectiveStableMap i h)).arrow =
    S.finiteRestrictedToProjectiveStableMap i h
  exact imageSubobject_arrow_comp _

instance finiteProjectiveStableImagePresentation_epi
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C) :
    Epi (S.finiteProjectiveStableImagePresentation i h) :=
  show Epi (factorThruImageSubobject
    (S.finiteRestrictedToProjectiveStableMap i h)) from inferInstance

theorem finiteProjectiveStableImagePresentation_ne_zero
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    S.finiteProjectiveStableImagePresentation i h ≠ 0 := by
  intro hzero
  apply hstable
  change factorThruImageSubobject
    (S.finiteRestrictedToProjectiveStableMap i h) = 0 at hzero
  rw [← imageSubobject_arrow_comp
    (S.finiteRestrictedToProjectiveStableMap i h), hzero, zero_comp]

/-- Every nonzero cyclic stable image has the expected indecomposable
representable as its minimal projective cover. -/
def finiteProjectiveStableImageMinimalProjectivePresentation
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    MinimalProjectivePresentation
      (S.finiteProjectiveStableImage i h) where
  p := S.finiteRestrictedContravariantRepresentable (S.fgObj i)
  f := S.finiteProjectiveStableImagePresentation i h
  projective := inferInstance
  epi := inferInstance
  rightMinimal := by
    letI : IsLocalRing (End
        (S.finiteRestrictedContravariantRepresentable (S.fgObj i))) :=
      S.finiteRestrictedContravariantRepresentableFgObj_end_isLocalRing i
    exact isRightMinimal_of_localEnd_of_ne_zero _
      (S.finiteProjectiveStableImagePresentation_ne_zero i h hstable)

/-- Pushing the representable radical through the minimal cover of a nonzero
cyclic stable image gives a radical subobject of that image. -/
theorem finiteProjectiveStableImageRadical_isRadicalSubobject
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C) :
    IsUniserialObject.IsRadicalSubobject
      (imageSubobject
        (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
          S.finiteProjectiveStableImagePresentation i h)) :=
  isRadicalSubobject_imageSubobject_comp_of_epi
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i)
    (S.finiteProjectiveStableImagePresentation i h)
    (isRadicalSubobject_mk_of_mono_rightAlmostSplit
      (S.finiteRestrictedContravariantRepresentableRadicalInclusion i)
      (S.finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit i))

/-- For a nonzero stable generator, its pushed-forward representable radical
is a proper subobject of the cyclic stable image. -/
theorem finiteProjectiveStableImageRadical_ne_top
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    imageSubobject
        (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
          S.finiteProjectiveStableImagePresentation i h) ≠ ⊤ := by
  have hessential : IsEssentialEpi
      (S.finiteProjectiveStableImagePresentation i h) :=
    isEssentialEpi_of_isRightMinimal _
      (S.finiteProjectiveStableImageMinimalProjectivePresentation
        i h hstable).rightMinimal
  exact imageSubobject_comp_ne_top_of_isEssentialEpi
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i)
    (S.finiteProjectiveStableImagePresentation i h) hessential
    (mk_ne_top_of_mono_rightAlmostSplit
      (S.finiteRestrictedContravariantRepresentableRadicalInclusion i)
      (S.finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit i))

/-- The top of every nonzero cyclic stable image is simple: quotienting by
the pushed-forward representable radical gives a simple object. -/
theorem finiteProjectiveStableImageRadicalCokernel_simple
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    Simple
      (cokernel
        (imageSubobject
          (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
            S.finiteProjectiveStableImagePresentation i h)).arrow) := by
  let R := imageSubobject
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
      S.finiteProjectiveStableImagePresentation i h)
  apply simple_cokernel_of_isRadicalSubobject R.arrow
  · simpa only [R, R.mk_arrow] using
      S.finiteProjectiveStableImageRadical_isRadicalSubobject i h
  · simpa only [R, R.mk_arrow] using
      S.finiteProjectiveStableImageRadical_ne_top i h hstable

/-- The radical step for cyclic stable images: uniseriality of the proper
pushed-forward radical implies uniseriality of the image itself. -/
theorem finiteProjectiveStableImage_isUniserial_of_radical
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hrad : IsUniserialObject
      ((imageSubobject
          (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
            S.finiteProjectiveStableImagePresentation i h) :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k))) :
    IsUniserialObject (S.finiteProjectiveStableImage i h) :=
  IsUniserialObject.of_radicalSubobject _
    (S.finiteProjectiveStableImageRadical_isRadicalSubobject i h) hrad

/-- Finite-length radical induction for a class of cyclic stable images.
If the class is closed under taking a nonzero radical stage, then every
image in the class is uniserial. -/
theorem finiteProjectiveStableImage_isUniserial_of_closedRadicalSuccessors
    (Good : ∀ {C : RightModule.FinitelyGeneratedCategory A}
      (i : S.IndecCategory), (S.fgObj i ⟶ C) → Prop)
    (hsuccessor :
      ∀ {C : RightModule.FinitelyGeneratedCategory A}
        (i : S.IndecCategory) (h : S.fgObj i ⟶ C),
        Good i h →
        S.finiteRestrictedToProjectiveStableMap i h ≠ 0 →
        ¬ IsZero
          ((imageSubobject
              (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
                S.finiteProjectiveStableImagePresentation i h) :
            CoveringHom.FiniteDimensionalModuleCategory
              (C := S.IndecCategoryᵒᵖ) k)) →
        ∃ (j : S.IndecCategory) (g : S.fgObj j ⟶ C),
          Good j g ∧
            S.finiteRestrictedToProjectiveStableMap j g ≠ 0 ∧
            Nonempty
              ((imageSubobject
                    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
                      S.finiteProjectiveStableImagePresentation i h) :
                  CoveringHom.FiniteDimensionalModuleCategory
                    (C := S.IndecCategoryᵒᵖ) k) ≅
                S.finiteProjectiveStableImage j g))
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hgood : Good i h)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    IsUniserialObject (S.finiteProjectiveStableImage i h) := by
  let main : ∀ n : ℕ,
      ∀ {D : RightModule.FinitelyGeneratedCategory A}
        (j : S.IndecCategory) (g : S.fgObj j ⟶ D),
        CoveringHom.moduleTotalDimension
            (S.finiteProjectiveStableImage j g) = n →
          Good j g →
          S.finiteRestrictedToProjectiveStableMap j g ≠ 0 →
          IsUniserialObject (S.finiteProjectiveStableImage j g) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro D j g hdim hgood hg
        let R := imageSubobject
          (S.finiteRestrictedContravariantRepresentableRadicalInclusion j ≫
            S.finiteProjectiveStableImagePresentation j g)
        by_cases hRzero : IsZero
            (R : CoveringHom.FiniteDimensionalModuleCategory
              (C := S.IndecCategoryᵒᵖ) k)
        · apply S.finiteProjectiveStableImage_isUniserial_of_radical j g
          exact IsUniserialObject.of_isZero hRzero
        · obtain ⟨j', g', hgood', hg', ⟨e⟩⟩ :=
            hsuccessor j g hgood hg hRzero
          have hRproper : R ≠ ⊤ :=
            S.finiteProjectiveStableImageRadical_ne_top j g hg
          have hRarrowNotIso : ¬ IsIso R.arrow := by
            intro hiso
            letI : IsIso R.arrow := hiso
            apply hRproper
            simpa using
              (Subobject.isIso_iff_mk_eq_top R.arrow).mp
                (inferInstance : IsIso R.arrow)
          have hRdim : CoveringHom.moduleTotalDimension
                (R : CoveringHom.FiniteDimensionalModuleCategory
                  (C := S.IndecCategoryᵒᵖ) k) < n := by
            rw [← hdim]
            exact CoveringHom.moduleTotalDimension_lt_of_mono_not_isIso
              (R : CoveringHom.FiniteDimensionalModuleCategory
                (C := S.IndecCategoryᵒᵖ) k)
              (S.finiteProjectiveStableImage j g) R.arrow hRarrowNotIso
          have hdimIso : CoveringHom.moduleTotalDimension
                (R : CoveringHom.FiniteDimensionalModuleCategory
                  (C := S.IndecCategoryᵒᵖ) k) =
              CoveringHom.moduleTotalDimension
                (S.finiteProjectiveStableImage j' g') := by
            unfold CoveringHom.moduleTotalDimension
            apply finsum_congr
            intro X
            exact (asIso (e.hom.hom.hom.app X)).toLinearEquiv.finrank_eq
          have hnext : IsUniserialObject
              (S.finiteProjectiveStableImage j' g') :=
            ih (CoveringHom.moduleTotalDimension
              (S.finiteProjectiveStableImage j' g'))
              (by rw [← hdimIso]; exact hRdim) j' g' rfl hgood' hg'
          have hrad : IsUniserialObject
              (R : CoveringHom.FiniteDimensionalModuleCategory
                (C := S.IndecCategoryᵒᵖ) k) :=
            hnext.congr e.symm
          exact S.finiteProjectiveStableImage_isUniserial_of_radical j g hrad
  exact main
    (CoveringHom.moduleTotalDimension
      (S.finiteProjectiveStableImage i h)) i h rfl hgood hstable

/-- The predicate-free form of finite-length radical induction. -/
theorem finiteProjectiveStableImage_isUniserial_of_radicalSuccessors
    (hsuccessor :
      ∀ {C : RightModule.FinitelyGeneratedCategory A}
        (i : S.IndecCategory) (h : S.fgObj i ⟶ C),
        S.finiteRestrictedToProjectiveStableMap i h ≠ 0 →
        ¬ IsZero
          ((imageSubobject
              (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
                S.finiteProjectiveStableImagePresentation i h) :
            CoveringHom.FiniteDimensionalModuleCategory
              (C := S.IndecCategoryᵒᵖ) k)) →
        ∃ (j : S.IndecCategory) (g : S.fgObj j ⟶ C),
          S.finiteRestrictedToProjectiveStableMap j g ≠ 0 ∧
            Nonempty
              ((imageSubobject
                    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
                      S.finiteProjectiveStableImagePresentation i h) :
                  CoveringHom.FiniteDimensionalModuleCategory
                    (C := S.IndecCategoryᵒᵖ) k) ≅
                S.finiteProjectiveStableImage j g))
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    IsUniserialObject (S.finiteProjectiveStableImage i h) := by
  apply S.finiteProjectiveStableImage_isUniserial_of_closedRadicalSuccessors
    (Good := fun _ _ ↦ True) (fun i h _ hh hR ↦ ?_) i h trivial hstable
  obtain ⟨j, g, hg, he⟩ := hsuccessor i h hh hR
  exact ⟨j, g, trivial, hg, he⟩

instance finiteProjectiveStableQuotient_epi
    (C : RightModule.FinitelyGeneratedCategory A) :
    Epi (S.finiteProjectiveStableQuotient C) := by
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  have happ (X : S.IndecCategoryᵒᵖ) : Epi
      ((I.map (J.map (S.finiteProjectiveStableQuotient C))).app X) := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (ProjectiveStable.mk (k := k) :
      (S.inclusion.obj X.unop ⟶ C.obj) →ₗ[k]
        ProjectiveStable.Hom (k := k)
          (S.inclusion.obj X.unop) C.obj)
    exact Submodule.Quotient.mk_surjective _
  have hnat : Epi (I.map (J.map
      (S.finiteProjectiveStableQuotient C))) :=
    NatTrans.epi_of_epi_app _
  have hlinear : Epi (J.map (S.finiteProjectiveStableQuotient C)) :=
    I.epi_of_epi_map hnat
  exact J.epi_of_epi_map hlinear

/-- Every map from a restricted representable to the stable representable of
a chosen indecomposable is induced by an actual module morphism. -/
theorem exists_finiteRestrictedToProjectiveStableMap_eq
    (i j : S.IndecCategory)
    (f : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶
      S.finiteProjectiveStableContravariantRepresentable (S.fgObj j)) :
    ∃ h : S.fgObj i ⟶ S.fgObj j,
      S.finiteRestrictedToProjectiveStableMap i h = f := by
  obtain ⟨a, ha⟩ := Projective.factors f
    (S.finiteProjectiveStableQuotient (S.fgObj j))
  let h : S.fgObj i ⟶ S.fgObj j := ObjectProperty.homMk (by
    change S.obj i ⟶ S.obj j
    exact a.hom.hom.app (Opposite.op i) (𝟙 (S.inclusion.obj i)))
  refine ⟨h, ?_⟩
  rw [finiteRestrictedToProjectiveStableMap]
  change S.finiteRestrictedContravariantRepresentableMap h ≫
      S.finiteProjectiveStableQuotient (S.fgObj j) = f
  rw [show S.finiteRestrictedContravariantRepresentableMap h = a by
    exact S.finiteRestrictedContravariantRepresentableMap_fgObj_eq i j a]
  exact ha

/-- For a nonprojective indecomposable, the quotient from ordinary to stable
Hom is nonzero: otherwise its identity would factor through a projective. -/
theorem finiteProjectiveStableQuotient_fgObj_ne_zero
    (i : S.IndecCategory)
    (hi : ¬ Projective (S.inclusion.obj i)) :
    S.finiteProjectiveStableQuotient (S.fgObj i) ≠ 0 := by
  intro hzero
  have happ := congrArg
    (fun f : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶
        S.finiteProjectiveStableContravariantRepresentable (S.fgObj i) ↦
      f.hom.hom.app (Opposite.op i) (𝟙 (S.inclusion.obj i)))
    hzero
  change ProjectiveStable.mk (k := k) (𝟙 (S.inclusion.obj i)) = 0 at happ
  have hidFactor :
      (𝟙 (S.inclusion.obj i)) ∈
        ProjectiveStable.factorSubmodule (k := k)
          (S.inclusion.obj i) (S.inclusion.obj i) :=
    (Submodule.Quotient.mk_eq_zero
      (ProjectiveStable.factorSubmodule (k := k)
        (S.inclusion.obj i) (S.inclusion.obj i))).1 happ
  obtain ⟨hfactor⟩ := hidFactor
  exact hi (MagnitudeConjecture.projective_of_retract
    hfactor.projective hfactor.left hfactor.right hfactor.fac)

/-- At a nonprojective indecomposable, the stable quotient is the minimal
projective cover of the restricted stable representable. -/
theorem finiteProjectiveStableQuotient_fgObj_isRightMinimal
    (i : S.IndecCategory)
    (hi : ¬ Projective (S.inclusion.obj i)) :
    IsRightMinimal
      (S.finiteProjectiveStableQuotient (S.fgObj i)) := by
  letI : IsLocalRing (End
      (S.finiteRestrictedContravariantRepresentable (S.fgObj i))) :=
    S.finiteRestrictedContravariantRepresentableFgObj_end_isLocalRing i
  exact isRightMinimal_of_localEnd_of_ne_zero
    (S.finiteProjectiveStableQuotient (S.fgObj i))
    (S.finiteProjectiveStableQuotient_fgObj_ne_zero i hi)

/-- The canonical minimal projective presentation of the stable
representable at a nonprojective indecomposable. -/
def finiteProjectiveStableMinimalProjectivePresentation
    (i : S.IndecCategory)
    (hi : ¬ Projective (S.inclusion.obj i)) :
    MinimalProjectivePresentation
      (S.finiteProjectiveStableContravariantRepresentable (S.fgObj i)) where
  p := S.finiteRestrictedContravariantRepresentable (S.fgObj i)
  f := S.finiteProjectiveStableQuotient (S.fgObj i)
  projective := inferInstance
  epi := inferInstance
  rightMinimal :=
    S.finiteProjectiveStableQuotient_fgObj_isRightMinimal i hi

/-- A projective epimorphism presents the stable representable pointwise:
the image of postcomposition with the epimorphism is exactly the kernel of
the stable quotient. -/
theorem finiteRestrictedMap_stableQuotient_app_range_eq_ker
    {P C : RightModule.FinitelyGeneratedCategory A} (q : P ⟶ C)
    [Epi q] (hP : Projective P.obj) (X : S.IndecCategoryᵒᵖ) :
    let J := (CoveringHom.IsFiniteDimensionalModule
      (C := S.IndecCategoryᵒᵖ) k).ι
    let I := (CoveringHom.IsLinearModule
      (C := S.IndecCategoryᵒᵖ) k).ι
    LinearMap.range
        ((I.map (J.map
          (S.finiteRestrictedContravariantRepresentableMap q))).app X).hom =
      LinearMap.ker
        ((I.map (J.map
          (S.finiteProjectiveStableQuotient C))).app X).hom := by
  letI : Projective P.obj := hP
  have hsurj : Function.Surjective q.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      q).1 inferInstance
  letI : Epi q.hom := (ModuleCat.epi_iff_surjective q.hom).2 hsurj
  change LinearMap.range
      (CategoryTheory.Linear.rightComp k (S.inclusion.obj X.unop) q.hom) =
    LinearMap.ker
      (ProjectiveStable.mk (k := k) :
        (S.inclusion.obj X.unop ⟶ C.obj) →ₗ[k]
          ProjectiveStable.Hom (k := k)
            (S.inclusion.obj X.unop) C.obj)
  rw [← ProjectiveStable.factorSubmodule_eq_range_rightComp_of_projective_epi
    (k := k) q.hom (S.inclusion.obj X.unop),
    Submodule.ker_mkQ]

/-- Postcomposition through a projective is killed by the stable quotient. -/
theorem finiteRestrictedMap_comp_stableQuotient_eq_zero
    {P C : RightModule.FinitelyGeneratedCategory A} (q : P ⟶ C)
    (hP : Projective P.obj) :
    S.finiteRestrictedContravariantRepresentableMap q ≫
        S.finiteProjectiveStableQuotient C = 0 := by
  letI : Projective P.obj := hP
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (S.inclusion.obj X.unop ⟶ P.obj) at f
  change ProjectiveStable.mk (k := k) (f ≫ q.hom) = 0
  apply (Submodule.Quotient.mk_eq_zero
    (ProjectiveStable.factorSubmodule (k := k)
      (S.inclusion.obj X.unop) C.obj)).2
  exact ⟨{
    middle := P.obj
    projective := inferInstance
    left := f
    right := q.hom
    fac := rfl }⟩

/-- The representables of a monomorphism and its cokernel projection form an
exact sequence.  This is the left half of the explicit projective
presentation used for a quotient by an irreducible projective submodule. -/
theorem finiteRestrictedMap_cokernelMap_exact
    {U P : RightModule.FinitelyGeneratedCategory A} (g : U ⟶ P) [Mono g] :
    (ShortComplex.mk
      (S.finiteRestrictedContravariantRepresentableMap g)
      (S.finiteRestrictedContravariantRepresentableMap (cokernel.π g))
      (by rw [← S.finiteRestrictedContravariantRepresentableMap_comp,
        cokernel.condition, S.finiteRestrictedContravariantRepresentableMap_zero])).Exact := by
  let T := ShortComplex.mk
    (S.finiteRestrictedContravariantRepresentableMap g)
    (S.finiteRestrictedContravariantRepresentableMap (cokernel.π g))
    (by rw [← S.finiteRestrictedContravariantRepresentableMap_comp,
      cokernel.condition, S.finiteRestrictedContravariantRepresentableMap_zero])
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  apply J.reflects_exact_of_faithful T
  apply I.reflects_exact_of_faithful (T.map J)
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro X
  change LinearMap.range
      ((S.finiteRestrictedContravariantRepresentableMap g).hom.hom.app X).hom =
    LinearMap.ker
      ((S.finiteRestrictedContravariantRepresentableMap (cokernel.π g)).hom.hom.app X).hom
  change LinearMap.range
      (CategoryTheory.Linear.rightComp k (S.inclusion.obj X.unop) g.hom) =
    LinearMap.ker
      (CategoryTheory.Linear.rightComp k (S.inclusion.obj X.unop) (cokernel.π g).hom)
  ext h
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    change (a ≫ g.hom) ≫ (cokernel.π g).hom = 0
    have hcond := congrArg (fun f : U ⟶ cokernel g ↦ f.hom)
      (cokernel.condition g)
    change g.hom ≫ (cokernel.π g).hom = 0 at hcond
    rw [Category.assoc, hcond, comp_zero]
  · intro hh
    rw [LinearMap.mem_ker] at hh
    change h ≫ (cokernel.π g).hom = 0 at hh
    let hfg : S.fgObj X.unop ⟶ P := ObjectProperty.homMk h
    have hfgq : hfg ≫ cokernel.π g = 0 := by
      apply ObjectProperty.hom_ext
      exact hh
    let a := Abelian.monoLift g hfg hfgq
    refine ⟨a.hom, ?_⟩
    change a.hom ≫ g.hom = h
    exact congrArg (fun f : S.fgObj X.unop ⟶ P ↦ f.hom)
      (Abelian.monoLift_comp g hfg hfgq)

/-- Hence a projective epimorphism gives an exact two-term presentation of
the restricted stable representable. -/
theorem finiteRestrictedMap_stableQuotient_exact
    {P C : RightModule.FinitelyGeneratedCategory A} (q : P ⟶ C)
    [Epi q] (hP : Projective P.obj) :
    (ShortComplex.mk
      (S.finiteRestrictedContravariantRepresentableMap q)
      (S.finiteProjectiveStableQuotient C)
      (S.finiteRestrictedMap_comp_stableQuotient_eq_zero q hP)).Exact := by
  let T := ShortComplex.mk
    (S.finiteRestrictedContravariantRepresentableMap q)
    (S.finiteProjectiveStableQuotient C)
    (S.finiteRestrictedMap_comp_stableQuotient_eq_zero q hP)
  let J := (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  let I := (CoveringHom.IsLinearModule
    (C := S.IndecCategoryᵒᵖ) k).ι
  apply J.reflects_exact_of_faithful T
  apply I.reflects_exact_of_faithful (T.map J)
  apply MagnitudeConjecture.CategoryTheory.moduleFunctor_exact_of_app_range_eq_ker
  intro X
  change LinearMap.range
      ((S.finiteRestrictedContravariantRepresentableMap q).hom.hom.app X).hom =
    LinearMap.ker
      ((S.finiteProjectiveStableQuotient C).hom.hom.app X).hom
  exact S.finiteRestrictedMap_stableQuotient_app_range_eq_ker q hP X

/-- A projective epimorphism presents the restricted stable representable as
the actual cokernel of postcomposition.  This upgrades the pointwise exact
sequence above to the projective-presentation interface used in the
Auslander--Reiten socle argument. -/
noncomputable def finiteRestrictedMap_stableQuotient_isCokernel
    {P C : RightModule.FinitelyGeneratedCategory A} (q : P ⟶ C)
    [Epi q] (hP : Projective P.obj) :
    IsColimit (CokernelCofork.ofπ
      (S.finiteProjectiveStableQuotient C)
      (S.finiteRestrictedMap_comp_stableQuotient_eq_zero q hP)) := by
  let T := ShortComplex.mk
    (S.finiteRestrictedContravariantRepresentableMap q)
    (S.finiteProjectiveStableQuotient C)
    (S.finiteRestrictedMap_comp_stableQuotient_eq_zero q hP)
  exact Classical.choice
    (T.exact_and_epi_g_iff_g_is_cokernel.1 ⟨
      S.finiteRestrictedMap_stableQuotient_exact q hP, inferInstance⟩)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
