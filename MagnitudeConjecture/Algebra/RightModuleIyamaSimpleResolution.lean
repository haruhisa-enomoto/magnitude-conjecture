import MagnitudeConjecture.Algebra.RightModuleIyamaSaturation
import MagnitudeConjecture.Algebra.RightModulePrimitiveMultiplicity
import MagnitudeConjecture.Algebra.RightModuleDirected
import MagnitudeConjecture.Algebra.IdempotentSaturationProjective
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Algebra.Algebra.Opposite

/-!
# Simple Auslander modules from strict tau meshes

For a surviving indecomposable `X`, the right tau mesh ending at `X`
becomes, under the full-generator representable functor, the beginning of a
projective resolution of the simple functor at `X`.  Strictness makes its
first map injective, while the right almost-split property identifies the
image of its second map with the categorical radical.

The evaluated-mesh calculation is the only routine adapted from the clean
equidistribution formalization.  It is stated here directly for the literal
factor category and its Auslander ring; no word-quiver or OP layer is
imported.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.Iyama
open MagnitudeConjecture.CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The categorical radical inside a full-generator representable. -/
def factorRepresentableRadical
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Submodule (S.factorAuslanderRing K)
      (S.factorAdditiveGenerator K ⟶ S.factorObject K x) where
  carrier :=
    (S.factorFiniteTauCategoryData K).radical.ideal.hom
      (S.factorAdditiveGenerator K) (S.factorObject K x)
  zero_mem' :=
    ((S.factorFiniteTauCategoryData K).radical.ideal.hom _ _).zero_mem
  add_mem' :=
    ((S.factorFiniteTauCategoryData K).radical.ideal.hom _ _).add_mem
  smul_mem' := by
    intro a f hf
    change End.asHom a.unop ≫ f ∈
      (S.factorFiniteTauCategoryData K).radical.ideal.hom _ _
    exact (S.factorFiniteTauCategoryData K).radical.ideal.precomp
      (End.asHom a.unop) hf

omit [IsAlgClosed k] in
@[simp]
theorem mem_factorRepresentableRadical_iff
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    (f : S.factorAdditiveGenerator K ⟶ S.factorObject K x) :
    f ∈ S.factorRepresentableRadical K x ↔
      CategoricalRadical.IsRadicalMorphism f :=
  (S.factorFiniteTauCategoryData K).radical.mem_ideal_iff f

/-- The simple-functor candidate at a surviving factor label. -/
abbrev factorAuslanderSimple
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :=
  (S.factorAdditiveGenerator K ⟶ S.factorObject K x) ⧸
    S.factorRepresentableRadical K x

/-- The coefficient-field structure on the radical quotient, obtained by
restriction from the factor Auslander algebra. -/
noncomputable instance factorAuslanderSimpleModule
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Module k (S.factorAuslanderSimple K x) :=
  Module.restrictScalars k (S.factorAuslanderRing K)
    (S.factorAuslanderSimple K x)

noncomputable instance factorAuslanderSimpleIsScalarTower
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    IsScalarTower k (S.factorAuslanderRing K)
      (S.factorAuslanderSimple K x) :=
  IsScalarTower.restrictScalars k (S.factorAuslanderRing K)
    (S.factorAuslanderSimple K x)

/-- The transported second map of the right mesh, with literal endpoint
`factorObject K x`. -/
def factorRepresentableMeshTargetMap
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (S.factorFiniteTauCategoryData K).thetaPlus x ⟶
      S.factorObject K x :=
  ((S.factorFiniteTauCategoryData K).rightMesh
      ((S.factorFiniteTauCategoryData K).obj x)).g ≫
    ((S.factorFiniteTauCategoryData K).rightTermIso
      (S.factorObject K x)).hom

/-- The first evaluated mesh differential. -/
def factorRepresentableMeshNu
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (S.factorAdditiveGenerator K ⟶
        ((S.factorFiniteTauCategoryData K).rightMesh
          (S.factorObject K x)).X₁) →ₗ[S.factorAuslanderRing K]
      (S.factorAdditiveGenerator K ⟶
        (S.factorFiniteTauCategoryData K).thetaPlus x) :=
  ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).map
    ((S.factorFiniteTauCategoryData K).rightMesh
      ((S.factorFiniteTauCategoryData K).obj x)).f).hom

/-- The second evaluated mesh differential. -/
def factorRepresentableMeshMu
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (S.factorAdditiveGenerator K ⟶
        (S.factorFiniteTauCategoryData K).thetaPlus x) →ₗ[
      S.factorAuslanderRing K]
      (S.factorAdditiveGenerator K ⟶ S.factorObject K x) :=
  ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).map
    (S.factorRepresentableMeshTargetMap K x)).hom

omit [IsAlgClosed k] in
/-- Exactness of the evaluated right mesh at its middle representable. -/
theorem factorRepresentableMesh_exact_middle
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Function.Exact
      (S.factorRepresentableMeshNu K x)
      (S.factorRepresentableMeshMu K x) := by
  let T := S.factorFiniteTauCategoryData K
  change Function.Exact
    (fun l : S.factorAdditiveGenerator K ⟶
        (T.rightMesh (T.obj x)).X₁ ↦
      l ≫ (T.rightMesh (T.obj x)).f)
    (fun f : S.factorAdditiveGenerator K ⟶ T.thetaPlus x ↦
      f ≫ ((T.rightMesh (T.obj x)).g ≫
        (T.rightTermIso (T.obj x)).hom))
  intro f
  constructor
  · intro hf
    change f ≫ ((T.rightMesh (T.obj x)).g ≫
      (T.rightTermIso (T.obj x)).hom) = 0 at hf
    have hfg : f ≫ (T.rightMesh (T.obj x)).g = 0 := by
      apply (cancel_mono (T.rightTermIso (T.obj x)).hom).1
      simpa only [Category.assoc, zero_comp] using hf
    exact (T.rightTau (T.obj x)).exact_postcomp
      (S.factorAdditiveGenerator K) f |>.mp hfg
  · rintro ⟨g, rfl⟩
    simp only [Category.assoc]
    rw [← Category.assoc (T.rightMesh (T.obj x)).f,
      (T.rightMesh (T.obj x)).zero, zero_comp]
    simp

omit [IsAlgClosed k] in
/-- The second evaluated mesh differential has exactly the categorical
radical as its image. -/
theorem range_factorRepresentableMeshMu
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    LinearMap.range (S.factorRepresentableMeshMu K x) =
      S.factorRepresentableRadical K x := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    rw [S.mem_factorRepresentableRadical_iff K x]
    change CategoricalRadical.IsRadicalMorphism
      (g ≫ ((S.factorFiniteTauCategoryData K).rightMesh
          (S.factorObject K x)).g ≫
        ((S.factorFiniteTauCategoryData K).rightTermIso
          (S.factorObject K x)).hom)
    simpa only [Category.assoc] using
      CategoricalRadical.isRadicalMorphism_postcomp
        ((S.factorFiniteTauCategoryData K).rightTermIso
          (S.factorObject K x)).hom
        (CategoricalRadical.isRadicalMorphism_precomp g
          ((S.factorFiniteTauCategoryData K).rightTau
            (S.factorObject K x)).g_radical)
  · intro hf
    have hfRad : CategoricalRadical.IsRadicalMorphism f :=
      (S.mem_factorRepresentableRadical_iff K x f).1 hf
    let e := (S.factorFiniteTauCategoryData K).rightTermIso
      (S.factorObject K x)
    have hf'Rad : CategoricalRadical.IsRadicalMorphism (f ≫ e.inv) :=
      CategoricalRadical.isRadicalMorphism_postcomp e.inv hfRad
    obtain ⟨g, hg⟩ :=
      ((S.factorFiniteTauCategoryData K).rightTau
        (S.factorObject K x)).factors_into_right (f ≫ e.inv) hf'Rad
    refine ⟨g, ?_⟩
    change g ≫ ((S.factorFiniteTauCategoryData K).rightMesh
      (S.factorObject K x)).g ≫ e.hom = f
    calc
      g ≫ ((S.factorFiniteTauCategoryData K).rightMesh
          (S.factorObject K x)).g ≫ e.hom =
          (f ≫ e.inv) ≫ e.hom := by
            rw [← Category.assoc, hg]
      _ = f ≫ (e.inv ≫ e.hom) := Category.assoc _ _ _
      _ = f := by rw [e.inv_hom_id, Category.comp_id]

omit [IsAlgClosed k] in
/-- Between distinct surviving indecomposables every morphism belongs to the
categorical radical. -/
theorem factorHom_mem_radical_of_ne
    (K : Set (Fin S.n)) {a x : S.SurvivingLabel K} (hax : a ≠ x)
    (f : S.factorObject K a ⟶ S.factorObject K x) :
    f ∈ (S.factorFiniteTauCategoryData K).radical.ideal.hom
      (S.factorObject K a) (S.factorObject K x) := by
  rw [(S.factorFiniteTauCategoryData K).radical.mem_ideal_iff]
  apply ((S.factorFiniteTauCategoryData K).isRadicalMorphism_iff_not_isSplitEpi_to_obj f).2
  intro hf
  let T := S.factorFiniteTauCategoryData K
  let fT : T.obj a ⟶ T.obj x := f
  letI : IsSplitEpi fT := hf
  let s : T.obj x ⟶ T.obj a := section_ fT
  have hs : IsSplitMono s := inferInstance
  letI : IsSplitMono s := hs
  haveI : IsIso s := T.isIso_of_isSplitMono_obj_obj s
  exact hax (T.obj_skeletal ⟨asIso s⟩).symm

/-- The identity-coordinate class generating the simple functor at `x`. -/
def factorAuslanderSimpleGenerator
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    S.factorAuslanderSimple K x :=
  (S.factorRepresentableRadical K x).mkQ
    (biproduct.π
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x)

omit [IsAlgClosed k] in
/-- The identity-coordinate class in the radical quotient is nonzero. -/
theorem factorAuslanderSimpleGenerator_ne_zero
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    S.factorAuslanderSimpleGenerator K x ≠ 0 := by
  intro hzero
  let p : S.factorAdditiveGenerator K ⟶ S.factorObject K x :=
    biproduct.π
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x
  have hprojection :
      p ∈ S.factorRepresentableRadical K x := by
    exact (Submodule.Quotient.mk_eq_zero _).1 hzero
  have hidmem :
      (biproduct.ι
          (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x ≫
        biproduct.π
          (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x) ∈
      (S.factorFiniteTauCategoryData K).radical.ideal.hom
        (S.factorObject K x) (S.factorObject K x) :=
    (S.factorFiniteTauCategoryData K).radical.ideal.precomp
      (biproduct.ι
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x)
      hprojection
  have hidrad : CategoricalRadical.IsRadicalMorphism
      (𝟙 (S.factorObject K x)) := by
    rw [biproduct.ι_π_self] at hidmem
    exact ((S.factorFiniteTauCategoryData K).radical.mem_ideal_iff _).1
      hidmem
  exact
    (((S.factorFiniteTauCategoryData K).isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (𝟙 (S.factorObject K x))).1 hidrad)
      (inferInstance : IsSplitEpi (𝟙 (S.factorObject K x)))

/-- The categorical radical quotient at `x` is one-dimensional over the
coefficient field. -/
theorem finrank_factorAuslanderSimple_eq_one
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Module.finrank k
      (ModuleCat.of (S.factorAuslanderRing K)
        (S.factorAuslanderSimple K x)) = 1 := by
  let T := S.factorFiniteTauCategoryData K
  apply (finrank_eq_one_iff_of_nonzero'
    (S.factorAuslanderSimpleGenerator K x)
    (S.factorAuslanderSimpleGenerator_ne_zero K x)).2
  intro q
  obtain ⟨f, rfl⟩ :=
    (S.factorRepresentableRadical K x).mkQ_surjective q
  let p : S.factorAdditiveGenerator K ⟶ S.factorObject K x :=
    biproduct.π
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x
  obtain ⟨c, hc⟩ := H.factorObject_endomorphism_eq_smul_id S K x
    (biproduct.ι
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x ≫ f)
  refine ⟨c, ?_⟩
  have hscalar :
      (algebraMap k (S.factorAuslanderRing K) c) • p = c • p := by
    change End.asHom
      ((algebraMap k (S.factorAuslanderRing K) c).unop) ≫ p = c • p
    change (c • 𝟙 (S.factorAdditiveGenerator K)) ≫
          p = c • p
    rw [CategoryTheory.Linear.smul_comp, Category.id_comp]
  apply (Submodule.Quotient.eq
    (S.factorRepresentableRadical K x)).2
  change
    (algebraMap k (S.factorAuslanderRing K) c) • p - f ∈
      T.radical.ideal.hom
        (S.factorAdditiveGenerator K) (S.factorObject K x)
  rw [hscalar]
  unfold factorAdditiveGenerator at p f ⊢
  change
    c • biproduct.π
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x - f ∈
      T.radical.ideal.hom
        (S.factorAdditiveGenerator K) (S.factorObject K x)
  apply mem_radicalIdeal_of_biproduct_source_components T.radical
  intro a
  by_cases hax : a = x
  · subst a
    rw [Preadditive.comp_sub, CategoryTheory.Linear.comp_smul,
      biproduct.ι_π_self, hc, sub_self]
    exact (T.radical.ideal.hom _ _).zero_mem
  · have hcomponent :
        biproduct.ι
            (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a ≫ f ∈
          T.radical.ideal.hom
            (S.factorObject K a) (S.factorObject K x) :=
      S.factorHom_mem_radical_of_ne K hax _
    rw [Preadditive.comp_sub, CategoryTheory.Linear.comp_smul]
    rw [biproduct.ι_π_ne _ hax, smul_zero, zero_sub]
    exact (T.radical.ideal.hom _ _).neg_mem hcomponent

/-- The mesh radical quotient is a simple module over the factor Auslander
ring. -/
theorem factorAuslanderSimple_simple
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Simple
      (ModuleCat.of (S.factorAuslanderRing K)
        (S.factorAuslanderSimple K x)) :=
  simple_of_finrank_eq_one (k := k)
    (R := S.factorAuslanderRing K)
    (S.finrank_factorAuslanderSimple_eq_one H K x)

/-- The second evaluated mesh map, corestricted to its radical image. -/
def factorRepresentableMeshMuToRadical
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (S.factorAdditiveGenerator K ⟶
        (S.factorFiniteTauCategoryData K).thetaPlus x) →ₗ[
      S.factorAuslanderRing K]
      S.factorRepresentableRadical K x :=
  (S.factorRepresentableMeshMu K x).codRestrict
    (S.factorRepresentableRadical K x) (fun y ↦ by
      rw [← S.range_factorRepresentableMeshMu K x]
      exact ⟨y, rfl⟩)

omit [IsAlgClosed k] in
/-- Corestricting the second mesh differential to the radical preserves
exactness at the middle representable. -/
theorem factorRepresentableMesh_exact_radical
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Function.Exact
      (S.factorRepresentableMeshNu K x)
      (S.factorRepresentableMeshMuToRadical K x) := by
  intro y
  constructor
  · intro hy
    apply (S.factorRepresentableMesh_exact_middle K x y).1
    exact congrArg Subtype.val hy
  · intro hy
    apply Subtype.ext
    exact (S.factorRepresentableMesh_exact_middle K x y).2 hy

omit [IsAlgClosed k] in
/-- Strictness of the right mesh makes its first evaluated differential
injective. -/
theorem factorRepresentableMeshNu_injective
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (x : S.SurvivingLabel K) :
    Function.Injective (S.factorRepresentableMeshNu K x) := by
  let T := S.factorFiniteTauCategoryData K
  letI : Mono (T.rightMesh (T.obj x)).f :=
    PrimitiveFactorInput.rightMesh_mono (S := S) D x
  intro a b hab
  apply (cancel_mono (T.rightMesh (T.obj x)).f).1
  exact hab

omit [IsAlgClosed k] in
/-- The corestricted second evaluated mesh differential is onto the
categorical radical. -/
theorem factorRepresentableMeshMuToRadical_surjective
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Function.Surjective
      (S.factorRepresentableMeshMuToRadical K x) := by
  intro z
  have hz : z.1 ∈ LinearMap.range
      (S.factorRepresentableMeshMu K x) := by
    rw [S.range_factorRepresentableMeshMu K x]
    exact z.2
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, Subtype.ext ?_⟩
  exact hy

/-- A strict right tau mesh gives a length-two projective resolution of the
simple Auslander module at its endpoint. -/
theorem factorAuslanderSimple_hasProjectiveDimensionLE_two
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (x : S.SurvivingLabel K) :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        (S.factorAuslanderSimple K x)) 2 := by
  let C₁ : ShortComplex (ModuleCat.{u} (S.factorAuslanderRing K)) :=
    ModuleCat.shortComplexOfCompEqZero
      (S.factorRepresentableMeshNu K x)
      (S.factorRepresentableMeshMuToRadical K x) (by
        apply LinearMap.ext
        intro y
        change S.factorRepresentableMeshMuToRadical K x
          (S.factorRepresentableMeshNu K x y) = 0
        exact (S.factorRepresentableMesh_exact_radical K x
          (S.factorRepresentableMeshNu K x y)).2 ⟨y, rfl⟩)
  have hC₁ : C₁.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · exact S.factorRepresentableMesh_exact_radical K x
    · exact S.factorRepresentableMeshNu_injective D x
    · exact S.factorRepresentableMeshMuToRadical_surjective K x
  have hP₂ : Projective C₁.X₁ := by
    change Projective
      ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).obj
        ((S.factorFiniteTauCategoryData K).rightMesh
          (S.factorObject K x)).X₁)
    exact (S.factorAuslanderRepresentable_finiteProjective K _).2
  have hP₁ : Projective C₁.X₂ := by
    change Projective
      ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).obj
        ((S.factorFiniteTauCategoryData K).thetaPlus x))
    exact (S.factorAuslanderRepresentable_finiteProjective K _).2
  have hradical : HasProjectiveDimensionLE C₁.X₃ 1 := by
    letI : Projective C₁.X₁ := hP₂
    letI : Projective C₁.X₂ := hP₁
    exact hC₁.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance
  let C₀ : ShortComplex (ModuleCat.{u} (S.factorAuslanderRing K)) :=
    ModuleCat.shortComplexOfCompEqZero
      (S.factorRepresentableRadical K x).subtype
      (S.factorRepresentableRadical K x).mkQ (by
        ext y
        simp)
  have hC₀ : C₀.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · exact LinearMap.exact_subtype_mkQ
        (S.factorRepresentableRadical K x)
    · exact (S.factorRepresentableRadical K x).injective_subtype
    · exact (S.factorRepresentableRadical K x).mkQ_surjective
  have hP₀ : Projective C₀.X₂ := by
    change Projective
      ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).obj
        (S.factorObject K x))
    exact (S.factorAuslanderRepresentable_finiteProjective K _).2
  letI : HasProjectiveDimensionLE C₀.X₁ 1 := by
    change HasProjectiveDimensionLE C₁.X₃ 1
    exact hradical
  letI : Projective C₀.X₂ := hP₀
  exact hC₀.hasProjectiveDimensionLT_X₃ 2 inferInstance inferInstance

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
