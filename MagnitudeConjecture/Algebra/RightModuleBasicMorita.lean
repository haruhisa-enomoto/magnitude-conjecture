import MagnitudeConjecture.Algebra.RightModuleOrdinaryQuiver
import MagnitudeConjecture.Algebra.RightModulePrimitiveDirectedDeletion
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitivePresentation
import MagnitudeConjecture.CategoryTheory.FiniteTauSurplusEquivalence
import MagnitudeConjecture.CategoryTheory.RepresentablePresentation
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Abelian.Projective.Basic

/-!
# The canonical basic Morita representative

For a finite indecomposable skeleton of finitely generated right modules, let
`G` be the biproduct of one representative of every indecomposable projective.
The represented functor `Hom(G, -)` identifies the original finitely generated
module category with the finitely generated right modules over `End(G)`.

This file packages that elementary projective-generator Morita equivalence.
It uses no structural input about special biserial or string algebras.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The biproduct of one representative of every indecomposable projective
right module. -/
abbrev basicProjectiveGenerator : RightModule.FinitelyGeneratedCategory A :=
  ⨁ fun p : S.ProjectiveLabel ↦ S.fgObj p.label

/-- The chosen projective generator is projective. -/
noncomputable instance basicProjectiveGenerator_projective :
    Projective S.basicProjectiveGenerator := by
  change Projective (⨁ fun p : S.ProjectiveLabel ↦ S.fgObj p.label)
  constructor
  intro E X f e hepi
  letI : Epi e := hepi
  choose lift hlift using fun p : S.ProjectiveLabel ↦
    p.projective.factors
      (biproduct.ι (fun q : S.ProjectiveLabel ↦ S.fgObj q.label) p ≫ f) e
  refine ⟨biproduct.desc lift, ?_⟩
  apply biproduct.hom_ext'
  intro p
  simpa only [biproduct.ι_desc_assoc] using hlift p

/-- Every finitely generated projective right module belongs to the additive
closure of the chosen projective generator. -/
theorem finiteAddClosure_basicProjectiveGenerator_of_projective
    (X : RightModule.FinitelyGeneratedCategory A) (hX : Projective X) :
    MagnitudeConjecture.CategoryTheory.finiteAddClosure
      S.basicProjectiveGenerator X := by
  change MagnitudeConjecture.CategoryTheory.finiteAddClosure
    (⨁ fun p : S.ProjectiveLabel ↦ S.fgObj p.label) X
  letI : Projective X := hX
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition (k := k) X
  let F : Fin n → RightModule.FinitelyGeneratedCategory A :=
    fun j ↦ S.fgObj (label j)
  have hprojective (j : Fin n) : Projective (F j) := by
    let R : Retract (F j) X :=
      { i := biproduct.ι F j ≫ e.inv
        r := e.hom ≫ biproduct.π F j
        retract := by simp [F, Category.assoc] }
    exact R.projective
  let projectiveLabel : Fin n → S.ProjectiveLabel :=
    fun j ↦ ⟨label j, hprojective j⟩
  let intoGenerator : ∀ j : Fin n,
      F j ⟶ ⨁ fun p : S.ProjectiveLabel ↦ S.fgObj p.label :=
    fun j ↦ biproduct.ι
      (fun p : S.ProjectiveLabel ↦ S.fgObj p.label) (projectiveLabel j)
  let outOfGenerator : ∀ j : Fin n,
      (⨁ fun p : S.ProjectiveLabel ↦ S.fgObj p.label) ⟶ F j :=
    fun j ↦ biproduct.π
      (fun p : S.ProjectiveLabel ↦ S.fgObj p.label) (projectiveLabel j)
  let iB : (⨁ F) ⟶
      ⨁ fun _ : Fin n ↦
        ⨁ fun p : S.ProjectiveLabel ↦ S.fgObj p.label :=
    biproduct.map intoGenerator
  let rB : (⨁ fun _ : Fin n ↦
      ⨁ fun p : S.ProjectiveLabel ↦ S.fgObj p.label) ⟶ ⨁ F :=
    biproduct.map outOfGenerator
  have hir : iB ≫ rB = 𝟙 (⨁ F) := by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro l
    by_cases hjl : j = l
    · subst l
      simp only [iB, rB, biproduct.ι_map, biproduct.map_π,
        intoGenerator, outOfGenerator]
      simp [projectiveLabel, F]
    · simp only [iB, rB, biproduct.ι_map, biproduct.map_π,
        intoGenerator, outOfGenerator]
      simp [projectiveLabel, F, hjl]
  exact ⟨{
    n := n
    retract :=
      { i := e.hom ≫ iB
        r := rB ≫ e.inv
        retract := by
          rw [Category.assoc, ← Category.assoc iB, hir]
          simp } }⟩

/-- The endomorphism algebra of the chosen projective generator.  This is the
canonical basic representative used below. -/
abbrev moritaBasicAlgebra := End S.basicProjectiveGenerator

noncomputable instance moritaBasicAlgebra_finiteDimensional :
    FiniteDimensional k S.moritaBasicAlgebra :=
  fgModuleCatHomFinite (k := k) (A := A)
    S.basicProjectiveGenerator S.basicProjectiveGenerator

noncomputable instance moritaBasicAlgebra_opposite_noetherian :
    IsNoetherianRing S.moritaBasicAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Maps out of the chosen projective generator detect every nonzero map. -/
theorem exists_basicProjectiveGenerator_hom_comp_ne_zero
    {X Y : RightModule.FinitelyGeneratedCategory A} (f : X ⟶ Y)
    (hf : f ≠ 0) :
    ∃ g : S.basicProjectiveGenerator ⟶ X, g ≫ f ≠ 0 := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let P := Projective.over X
  let q := Projective.π X
  have hqf : q ≫ f ≠ 0 := by
    intro hzero
    apply hf
    apply (cancel_epi q).1
    simpa using hzero
  let R :=
    (S.finiteAddClosure_basicProjectiveGenerator_of_projective P
      (inferInstance : Projective P)).some
  have hrqf : R.retract.r ≫ q ≫ f ≠ 0 := by
    intro hzero
    apply hqf
    calc
      q ≫ f = 𝟙 P ≫ q ≫ f := by simp
      _ = (R.retract.i ≫ R.retract.r) ≫ q ≫ f := by
        rw [R.retract.retract]
      _ = R.retract.i ≫ (R.retract.r ≫ q ≫ f) := by
        simp only [Category.assoc]
      _ = 0 := by rw [hzero, comp_zero]
  have hcomponent : ∃ j : Fin R.n,
      biproduct.ι
          (fun _ : Fin R.n ↦ S.basicProjectiveGenerator) j ≫
          R.retract.r ≫ q ≫ f ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hrqf
    apply biproduct.hom_ext'
    intro j
    simpa only [comp_zero] using hnone j
  obtain ⟨j, hj⟩ := hcomponent
  exact ⟨biproduct.ι
      (fun _ : Fin R.n ↦ S.basicProjectiveGenerator) j ≫
        R.retract.r ≫ q,
    by simpa only [Category.assoc] using hj⟩

/-- The represented functor of the chosen projective generator is faithful.
-/
noncomputable instance basicProjectiveGenerator_coyoneda_faithful :
    (preadditiveCoyonedaObj S.basicProjectiveGenerator).Faithful where
  map_injective {X Y} f g hfg := by
    apply sub_eq_zero.mp
    by_contra hne
    obtain ⟨q, hq⟩ :=
      S.exists_basicProjectiveGenerator_hom_comp_ne_zero (f - g) hne
    have happ := ConcreteCategory.congr_hom hfg q
    change q ≫ f = q ≫ g at happ
    apply hq
    rw [Preadditive.comp_sub, happ, sub_self]

/-- The standard kernel presentation by a projective cover, expressed in the
interface used by the generic representable-fullness theorem. -/
def basicProjectiveGeneratorPresentation
    (X : RightModule.FinitelyGeneratedCategory A) :
    MagnitudeConjecture.CategoryTheory.FiniteAddGeneratorPresentation
      S.basicProjectiveGenerator X := by
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  let P := Projective.over X
  let p := Projective.π X
  exact
    { P₁ := kernel p
      P₀ := P
      P₀_mem :=
        S.finiteAddClosure_basicProjectiveGenerator_of_projective P
          (inferInstance : Projective P)
      d := kernel.ι p
      p := p
      zero := kernel.condition p
      lifts_from_generator := fun h ↦
        S.basicProjectiveGenerator_projective.factors h p
      weakCokernel := fun q hq ↦
        ⟨Abelian.epiDesc p q hq, Abelian.comp_epiDesc p q hq⟩ }

/-- The represented functor of the chosen projective generator is full. -/
noncomputable instance basicProjectiveGenerator_coyoneda_full :
    (preadditiveCoyonedaObj S.basicProjectiveGenerator).Full :=
  MagnitudeConjecture.CategoryTheory.preadditiveCoyonedaObj_full_of_finiteAddGeneratorPresentations
    S.basicProjectiveGenerator inferInstance
      (fun X ↦ ⟨S.basicProjectiveGeneratorPresentation X⟩)

/-- `Hom(G,-)` restricted to finitely generated right modules over `End(G)`.
-/
def basicMoritaFunctor :
    CategoryTheory.Functor
      (RightModule.FinitelyGeneratedCategory A)
      (RightModule.FinitelyGeneratedCategory S.moritaBasicAlgebra) :=
  (ModuleCat.isFG.{u} S.moritaBasicAlgebraᵐᵒᵖ).lift
    (preadditiveCoyonedaObj S.basicProjectiveGenerator)
    (fun X ↦ by
      let G := S.basicProjectiveGenerator
      let F := preadditiveCoyonedaObj G
      let P := S.basicProjectiveGeneratorPresentation X
      have hadd : MagnitudeConjecture.CategoryTheory.finiteAddClosure
          (F.obj G) (F.obj P.P₀) :=
        ⟨MagnitudeConjecture.CategoryTheory.homFromGenerator_obj_finiteAddPresentation
          G ⟨P.P₀, P.P₀_mem⟩⟩
      have hfiniteSource : Module.Finite S.moritaBasicAlgebraᵐᵒᵖ
          (F.obj P.P₀) :=
        (show MagnitudeConjecture.CategoryTheory.finiteProjectiveModules
            S.moritaBasicAlgebraᵐᵒᵖ (F.obj P.P₀) by
          rw [← MagnitudeConjecture.CategoryTheory.finiteAddClosure_homSelf_eq_finiteProjective
            G]
          exact hadd).1
      letI : Module.Finite S.moritaBasicAlgebraᵐᵒᵖ
          (F.obj P.P₀) := hfiniteSource
      apply Module.Finite.of_surjective (F.map P.p).hom
      intro f
      obtain ⟨l, hl⟩ := P.lifts_from_generator f
      exact ⟨l, hl⟩)

noncomputable instance basicMoritaFunctor_additive :
    S.basicMoritaFunctor.Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    exact (preadditiveCoyonedaObj
      S.basicProjectiveGenerator).map_add

noncomputable instance basicMoritaFunctor_linear :
    S.basicMoritaFunctor.Linear k where
  map_smul := by
    intro X Y f r
    let F := S.basicMoritaFunctor
    apply ObjectProperty.hom_ext
    have htarget :
        (r • F.map f).hom = r • (F.map f).hom :=
      (InducedCategory.homLinearEquiv (R := k)).map_smul r (F.map f)
    rw [htarget]
    apply ModuleCat.hom_ext
    ext g
    have hleft :
        (F.map (r • f)).hom.hom g = g ≫ (r • f) := rfl
    have hright :
        (r • (F.map f).hom).hom g =
          r • (F.map f).hom.hom g := rfl
    have hmap : (F.map f).hom.hom g = g ≫ f := rfl
    rw [hleft, hright, hmap]
    have hscalar :
        r • (g ≫ f) =
          (algebraMap k S.moritaBasicAlgebraᵐᵒᵖ r) • (g ≫ f) := by
      change r • (g ≫ f) = (r • 𝟙 _) ≫ (g ≫ f)
      simp
    exact hscalar

noncomputable instance basicMoritaFunctor_faithful :
    S.basicMoritaFunctor.Faithful where
  map_injective := by
    intro X Y f g hfg
    apply (preadditiveCoyonedaObj
      S.basicProjectiveGenerator).map_injective
    exact congrArg (fun q ↦ q.hom) hfg

noncomputable instance basicMoritaFunctor_full :
    S.basicMoritaFunctor.Full where
  map_surjective := by
    intro X Y f
    obtain ⟨g, hg⟩ := (preadditiveCoyonedaObj
      S.basicProjectiveGenerator).map_surjective f.hom
    refine ⟨g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg

/-- A finite power of the chosen projective generator. -/
abbrev basicProjectiveGeneratorPower (n : ℕ) :
    RightModule.FinitelyGeneratedCategory A :=
  ⨁ fun _ : Fin n ↦ S.basicProjectiveGenerator

/-- The represented module of a finite generator power is finite free. -/
def basicMoritaGeneratorPowerIso (n : ℕ) :
    (preadditiveCoyonedaObj S.basicProjectiveGenerator).obj
        (S.basicProjectiveGeneratorPower n) ≅
      ModuleCat.of S.moritaBasicAlgebraᵐᵒᵖ
        (Fin n → S.moritaBasicAlgebraᵐᵒᵖ) :=
  ((preadditiveCoyonedaObj
      S.basicProjectiveGenerator).mapBiproduct
        (fun _ : Fin n ↦ S.basicProjectiveGenerator)).trans
    ((biproduct.mapIso fun _ : Fin n ↦
      (MagnitudeConjecture.CategoryTheory.regularLinearEquiv
        S.basicProjectiveGenerator).toModuleIso.symm).trans
      (ModuleCat.biproductIsoPi
        (fun _ : Fin n ↦
          ModuleCat.of S.moritaBasicAlgebraᵐᵒᵖ
            S.moritaBasicAlgebraᵐᵒᵖ)))

/-- Every finitely generated right module over `End(G)` is represented. -/
theorem basicMoritaFunctor_essSurj : S.basicMoritaFunctor.EssSurj := by
  let G := S.basicProjectiveGenerator
  let B := S.moritaBasicAlgebra
  let R := Bᵐᵒᵖ
  let F := preadditiveCoyonedaObj G
  letI : FiniteDimensional k B := S.moritaBasicAlgebra_finiteDimensional
  letI : FiniteDimensional k R := by infer_instance
  letI : IsNoetherianRing R := IsNoetherianRing.of_finite k R
  constructor
  intro N
  letI : Module.Finite R N := N.property
  letI : Module.FinitePresentation R N :=
    Module.finitePresentation_of_finite R N
  obtain ⟨n, K, eN, hK⟩ := Module.FinitePresentation.exists_fin R N
  letI : Module.Finite R K := Module.Finite.of_fg hK
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' R K
  let d : (Fin m → R) →ₗ[R] (Fin n → R) := K.subtype.comp q
  have hdRange : LinearMap.range d = K := by
    apply le_antisymm
    · rintro y ⟨z, rfl⟩
      exact (q z).property
    · intro y hy
      obtain ⟨z, hz⟩ := hq ⟨y, hy⟩
      refine ⟨z, ?_⟩
      change (q z : Fin n → R) = y
      exact congrArg Subtype.val hz
  let dModule :
      ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R) :=
    ModuleCat.ofHom d
  let φm := S.basicMoritaGeneratorPowerIso m
  let φn := S.basicMoritaGeneratorPowerIso n
  let δ : F.obj (S.basicProjectiveGeneratorPower m) ⟶
      F.obj (S.basicProjectiveGeneratorPower n) :=
    φm.hom ≫ dModule ≫ φn.inv
  let dC : S.basicProjectiveGeneratorPower m ⟶
      S.basicProjectiveGeneratorPower n := F.preimage δ
  have hdC : F.map dC = δ := F.map_preimage δ
  let mapEqIso : cokernel (F.map dC) ≅ cokernel δ :=
    cokernel.mapIso (F.map dC) δ (Iso.refl _) (Iso.refl _) (by
      simpa using hdC)
  let freeCokernelIso : cokernel δ ≅ cokernel dModule :=
    cokernel.mapIso δ dModule φm φn (by
      dsimp only [δ]
      simp)
  let rangeQuotientIso :
      cokernel dModule ≅ ModuleCat.of R ((Fin n → R) ⧸ K) :=
    (ModuleCat.cokernelIsoRangeQuotient dModule).trans
      ((Submodule.quotEquivOfEq d.range K hdRange).toModuleIso)
  let representedIso : F.obj (cokernel dC) ≅ N.obj :=
    (PreservesCokernel.iso F dC).trans <|
      mapEqIso.trans <| freeCokernelIso.trans <|
        rangeQuotientIso.trans eN.symm.toModuleIso
  exact ⟨cokernel dC, ⟨ObjectProperty.isoMk _ representedIso⟩⟩

/-- The canonical Morita equivalence from the original right-module category
to the right modules over the basic endomorphism algebra. -/
def basicMoritaEquivalence :
    RightModule.FinitelyGeneratedCategory A ≌
      RightModule.FinitelyGeneratedCategory S.moritaBasicAlgebra := by
  letI : S.basicMoritaFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk inferInstance inferInstance
      S.basicMoritaFunctor_essSurj
  exact S.basicMoritaFunctor.asEquivalence

noncomputable instance basicMoritaEquivalence_functor_additive :
    S.basicMoritaEquivalence.functor.Additive := by
  change S.basicMoritaFunctor.Additive
  infer_instance

/-- The complete indecomposable skeleton transported to the canonical basic
endomorphism algebra.  Labels are deliberately unchanged. -/
def moritaBasicSkeleton :
    RightModule.FiniteIndecomposableSkeleton k S.moritaBasicAlgebra := by
  let E := S.basicMoritaEquivalence
  letI : E.functor.Additive := inferInstance
  letI : E.inverse.Additive := inferInstance
  refine
    { n := S.n
      obj := fun i ↦ (E.functor.obj (S.fgObj i)).obj
      obj_finite := fun i ↦
        finite_over_field_of_finitelyGenerated k S.moritaBasicAlgebra
          (E.functor.obj (S.fgObj i))
      obj_indecomposable := ?_
      eq_of_iso := ?_
      complete := ?_ }
  · intro i
    apply (FiniteIndecomposableSkeleton.indecomposable_iff_obj
      (k := k) (A := S.moritaBasicAlgebra)
        (E.functor.obj (S.fgObj i))).1
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.functor (S.fgObj i)).2 (S.fgObj_indecomposable i)
  · intro i j hij
    obtain ⟨hij⟩ := hij
    apply S.fgObj_skeletal
    exact ⟨E.functor.preimageIso (ObjectProperty.isoMk _ hij)⟩
  · intro M hM
    let Mfg : RightModule.FinitelyGeneratedCategory S.moritaBasicAlgebra :=
      @finitelyGeneratedOfFiniteDimensional k _ S.moritaBasicAlgebra _ _
        M hM.1
    have hMfg : Indecomposable Mfg :=
      (FiniteIndecomposableSkeleton.indecomposable_iff_obj
        (k := k) (A := S.moritaBasicAlgebra) Mfg).2 hM.2
    have hInv : Indecomposable (E.inverse.obj Mfg) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.inverse Mfg).2 hMfg
    obtain ⟨i, ⟨hi⟩⟩ := S.fgObj_complete (E.inverse.obj Mfg) hInv
    let efg : Mfg ≅ E.functor.obj (S.fgObj i) :=
      (E.counitIso.app Mfg).symm ≪≫ E.functor.mapIso hi
    exact ⟨i, ⟨(forget₂
      (RightModule.FinitelyGeneratedCategory S.moritaBasicAlgebra)
        (Category S.moritaBasicAlgebra)).mapIso efg⟩⟩

/-- Each object of the transported skeleton is canonically the represented
module of the original object with the same label. -/
def moritaBasicSkeletonObjIso (i : Fin S.n) :
    S.basicMoritaEquivalence.functor.obj (S.fgObj i) ≅
      S.moritaBasicSkeleton.fgObj i :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- Passage to the canonical basic representative preserves the ambient
Auslander--Reiten surplus. -/
theorem ambientARSurplus_moritaBasicSkeleton :
    S.moritaBasicSkeleton.ambientARSurplus = S.ambientARSurplus := by
  let E := S.basicMoritaEquivalence
  letI : E.functor.Additive := inferInstance
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory S.moritaBasicAlgebra) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      S.moritaBasicAlgebraᵐᵒᵖ
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let U := S.moritaBasicSkeleton.finiteTauCategoryData.toFiniteRightTauCategoryData
  have h := FiniteTauMatrix.surplus_eq_of_equivalence
    T U E (Equiv.refl (Fin S.n)) S.moritaBasicSkeletonObjIso
  have hT : T.IsProjective = fun i ↦ Projective (S.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj T i
  have hU : U.IsProjective =
      fun i ↦ Projective (S.moritaBasicSkeleton.fgObj i) := by
    funext i
    apply propext
    exact FiniteTauMatrix.isProjective_iff_projective_obj U i
  rw [hT, hU] at h
  exact h.symm

/-- Any uniform beta bound for the original skeleton passes to the canonical
basic representative. -/
theorem moritaBasicSkeleton_beta_le {bound : ℕ}
    (h : MagnitudeConjecture.FiniteTauMatrix.beta
      S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ bound) :
    MagnitudeConjecture.FiniteTauMatrix.beta
      S.moritaBasicSkeleton.finiteTauCategoryData.toFiniteRightTauCategoryData
        ≤ bound := by
  let E := S.basicMoritaEquivalence
  letI : E.functor.Additive := inferInstance
  letI : EnoughProjectives (RightModule.FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory S.moritaBasicAlgebra) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      S.moritaBasicAlgebraᵐᵒᵖ
  exact FiniteTauMatrix.beta_le_of_equivalence
    S.finiteTauCategoryData.toFiniteRightTauCategoryData
    S.moritaBasicSkeleton.finiteTauCategoryData.toFiniteRightTauCategoryData
    E (Equiv.refl (Fin S.n)) S.moritaBasicSkeletonObjIso h

/-- The projector of the projective generator onto one indecomposable
projective summand. -/
def basicProjector (p : S.ProjectiveLabel) : S.moritaBasicAlgebra :=
  biproduct.π (fun q : S.ProjectiveLabel ↦ S.fgObj q.label) p ≫
    biproduct.ι (fun q : S.ProjectiveLabel ↦ S.fgObj q.label) p

/-- The summand projectors form a complete orthogonal family. -/
theorem basicProjector_complete :
    CompleteOrthogonalIdempotents S.basicProjector := by
  refine
    { idem := fun p ↦ by
        rw [IsIdempotentElem, End.mul_def]
        simp [basicProjector, Category.assoc]
      ortho := fun p q hpq ↦ by
        change S.basicProjector p * S.basicProjector q = 0
        rw [End.mul_def]
        simp only [basicProjector, Category.assoc]
        rw [← Category.assoc
          (biproduct.ι (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) q)
          (biproduct.π (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p),
          biproduct.ι_π_ne _ (Ne.symm hpq), zero_comp, comp_zero]
      complete := by
        change
          (∑ p : S.ProjectiveLabel,
            biproduct.π
                (fun q : S.ProjectiveLabel ↦ S.fgObj q.label) p ≫
              biproduct.ι
                (fun q : S.ProjectiveLabel ↦ S.fgObj q.label) p) = 𝟙 _
        exact biproduct.total }

/-- Each summand projector is primitive. -/
theorem basicProjector_primitive (p : S.ProjectiveLabel) :
    RightModule.PrimitiveIdempotentData (S.basicProjector p) := by
  letI : IsLocalRing (End (S.fgObj p.label)) :=
    S.fgObj_end_isLocalRing p.label
  have hF : ¬ IsZero (S.fgObj p.label) :=
    (S.fgObj_indecomposable p.label).1
  simpa only [basicProjector, basicProjectiveGenerator] using
    (MagnitudeConjecture.CoveringHom.biproductProjector_primitive
      (fun q : S.ProjectiveLabel ↦ S.fgObj q.label) p hF)

/-- The principal right ideal of a summand projector is the represented
module of that summand. -/
def basicProjectorRightIdealLinearEquiv (p : S.ProjectiveLabel) :
    RightModule.rightIdealFGObj (S.basicProjector p) ≃ₗ[
      S.moritaBasicAlgebraᵐᵒᵖ]
      S.basicMoritaFunctor.obj (S.fgObj p.label) where
  toFun q := q.1 ≫
    biproduct.π (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p
  invFun f := ⟨f ≫
    biproduct.ι (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p, ⟨
      f ≫ biproduct.ι
        (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p, by
        change S.basicProjectiveGenerator ⟶ S.fgObj p.label at f
        change
          (f ≫ biproduct.ι
              (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p) ≫
              (biproduct.π
                  (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p ≫
                biproduct.ι
                  (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p) =
            f ≫ biproduct.ι
              (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p
        simp [Category.assoc]⟩⟩
  map_add' q r := by
    change
      (q.1 + r.1) ≫
          biproduct.π
            (fun t : S.ProjectiveLabel ↦ S.fgObj t.label) p =
        q.1 ≫ biproduct.π
            (fun t : S.ProjectiveLabel ↦ S.fgObj t.label) p +
          r.1 ≫ biproduct.π
            (fun t : S.ProjectiveLabel ↦ S.fgObj t.label) p
    exact Preadditive.add_comp _ _ _ _ _ _
  map_smul' a q := by
    change
      a.unop ≫ q.1 ≫
          biproduct.π
            (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p =
        a.unop ≫ (q.1 ≫
          biproduct.π
            (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p)
    rfl
  left_inv q := by
    apply Subtype.ext
    change (q.1 : S.moritaBasicAlgebra) ≫ S.basicProjector p = q.1
    have hfixed := RightModule.rightIdeal_fixed
      (S.basicProjector_complete.idem p) q
    change (q.1 : S.moritaBasicAlgebra) ≫ S.basicProjector p = q.1 at hfixed
    exact hfixed
  right_inv f := by
    change S.basicProjectiveGenerator ⟶ S.fgObj p.label at f
    change
      f ≫ biproduct.ι
          (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p ≫
          biproduct.π
            (fun r : S.ProjectiveLabel ↦ S.fgObj r.label) p = f
    simp

/-- Categorical form of the principal-right-ideal identification. -/
def basicProjectorRightIdealIso (p : S.ProjectiveLabel) :
    RightModule.rightIdealFGObj (S.basicProjector p) ≅
      S.basicMoritaFunctor.obj (S.fgObj p.label) :=
  QuotientSubmoduleEquidistribution.Contragredient.fgModuleIsoOfLinearEquiv
    S.moritaBasicAlgebraᵐᵒᵖ (S.basicProjectorRightIdealLinearEquiv p)

/-- Projective labels are determined by their underlying skeleton labels. -/
theorem projectiveLabel_eq_of_label_eq {p q : S.ProjectiveLabel}
    (h : p.label = q.label) : p = q := by
  rcases p with ⟨i, hi⟩
  rcases q with ⟨j, hj⟩
  change i = j at h
  subst j
  rfl

/-- The original and transported projective labels correspond label by
label under the Morita equivalence. -/
def moritaBasicProjectiveLabelEquiv :
    S.ProjectiveLabel ≃ S.moritaBasicSkeleton.ProjectiveLabel where
  toFun p := ⟨p.label, Projective.of_iso
    (S.moritaBasicSkeletonObjIso p.label)
      ((S.basicMoritaEquivalence.map_projective_iff (S.fgObj p.label)).2
        p.projective)⟩
  invFun q := ⟨q.label,
    (S.basicMoritaEquivalence.map_projective_iff (S.fgObj q.label)).1
      (Projective.of_iso (S.moritaBasicSkeletonObjIso q.label).symm
        q.projective)⟩
  left_inv p := S.projectiveLabel_eq_of_label_eq rfl
  right_inv q := S.moritaBasicSkeleton.projectiveLabel_eq_of_label_eq rfl

/-- The summand projectors give the transported skeleton its canonical
primitive-projective presentation. -/
def moritaBasicPrimitiveProjectivePresentation :
    S.moritaBasicSkeleton.PrimitiveProjectivePresentation where
  idempotent q :=
    S.basicProjector (S.moritaBasicProjectiveLabelEquiv.symm q)
  complete :=
    (CompleteOrthogonalIdempotents.equiv
      (e := S.basicProjector) S.moritaBasicProjectiveLabelEquiv.symm).2
        S.basicProjector_complete
  primitive q :=
    S.basicProjector_primitive (S.moritaBasicProjectiveLabelEquiv.symm q)
  sourceLabel q := by
    let p := S.moritaBasicProjectiveLabelEquiv.symm q
    let D := S.basicProjector_primitive p
    apply S.moritaBasicSkeleton.projectiveLabel_eq_of_label_eq
    apply S.moritaBasicSkeleton.fgObj_skeletal
    exact ⟨
      (S.moritaBasicSkeleton.primitiveSourceIso D).symm ≪≫
        S.basicProjectorRightIdealIso p ≪≫
        S.moritaBasicSkeletonObjIso p.label ≪≫
        eqToIso (congrArg
          (fun r : S.moritaBasicSkeleton.ProjectiveLabel ↦
            S.moritaBasicSkeleton.fgObj r.label)
          (Equiv.apply_symm_apply S.moritaBasicProjectiveLabelEquiv q))⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
