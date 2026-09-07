import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleHomFinite
import MagnitudeConjecture.CategoryTheory.RepresentablePresentation
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Abelian.Projective.Basic

/-!
# The projective generator of a finite linear category

For a finite-object locally bounded linear category, the biproduct of all
covariant representables is a finite projective generator of its finite-
dimensional module category.  The represented functor to modules over its
endomorphism algebra is therefore full and faithful.  This is the first half
of the finite-category-algebra bridge used in the manuscript's local directed
deletion theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Fintype C]

/-- The biproduct of all covariant representables of a finite linear
category. -/
abbrev finiteCategoryProjectiveGenerator
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X)) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  ⨁ fun X : C ↦
    (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
      (Opposite.op X)

namespace finiteCategoryProjectiveGenerator

variable
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))

private abbrev representable (X : C) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
    (Opposite.op X)

/-- Each representable is a retract of the finite projective generator. -/
def representableRetract (X : C) :
    Retract (representable hP X) (finiteCategoryProjectiveGenerator hP) := by
  classical
  exact
    { i := biproduct.ι (representable hP) X
      r := biproduct.π (representable hP) X
      retract := by
        simp }

/-- A finite sum of representables belongs to the additive closure of the
finite projective generator. -/
def finiteRepresentableSumPresentation
    {n : ℕ} (X : Fin n → C) :
    MagnitudeConjecture.CategoryTheory.FiniteAddPresentation
      (finiteCategoryProjectiveGenerator hP)
      (⨁ fun i ↦ representable hP (X i)) where
  n := n
  retract :=
    { i := biproduct.map fun i ↦ (representableRetract hP (X i)).i
      r := biproduct.map fun i ↦ (representableRetract hP (X i)).r
      retract := by
        apply biproduct.hom_ext'
        intro i
        apply biproduct.hom_ext
        intro j
        by_cases hij : i = j
        · subst j
          simp [representableRetract]
        · simp [hij] }

/-- The finite projective generator is projective. -/
instance projective : Projective (finiteCategoryProjectiveGenerator hP) where
  factors := by
    intro E M f e hepi
    let Q := fun X : C ↦ representable hP X
    letI (X : C) : Projective (Q X) :=
      finiteDimensionalLinearCoyoneda_projective X (hP X)
    refine ⟨biproduct.desc (fun X ↦
      Projective.factorThru (biproduct.ι Q X ≫ f) e), ?_⟩
    apply biproduct.hom_ext'
    intro X
    simpa only [Q, biproduct.ι_desc_assoc] using
      (Projective.factorThru_comp (biproduct.ι Q X ≫ f) e)

/-- A two-step finite-representable presentation is also a presentation by
the single finite projective generator. -/
def toFiniteAddGeneratorPresentation
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (P : TwoStepFiniteRepresentablePresentation hP M) :
    MagnitudeConjecture.CategoryTheory.FiniteAddGeneratorPresentation
      (finiteCategoryProjectiveGenerator hP) M where
  P₁ := P.syzygyPresentation.source
  P₀ := P.augmentation.source
  P₀_mem := ⟨finiteRepresentableSumPresentation hP P.augmentation.X⟩
  d := P.differential
  p := P.augmentation.f
  zero := P.differential_comp_augmentation
  lifts_from_generator := fun f ↦
    ⟨Projective.factorThru f P.augmentation.f,
      Projective.factorThru_comp f P.augmentation.f⟩
  weakCokernel := fun q hq ↦
    haveI : Epi P.presentationComplex.g := by
      change Epi P.augmentation.f
      infer_instance
    P.presentationComplex_exact.desc' q hq

/-- Every finite-dimensional module has a two-term presentation by the
finite projective generator. -/
theorem finiteAddGeneratorPresentation_nonempty
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Nonempty
      (MagnitudeConjecture.CategoryTheory.FiniteAddGeneratorPresentation
        (finiteCategoryProjectiveGenerator hP) M) := by
  obtain ⟨P⟩ := twoStepFiniteRepresentablePresentation_nonempty hP M
  exact ⟨toFiniteAddGeneratorPresentation hP P⟩

/-- The represented functor of the finite projective generator is faithful.
-/
instance representedFaithful :
    (preadditiveCoyonedaObj (finiteCategoryProjectiveGenerator hP)).Faithful where
  map_injective := by
    classical
    intro M N f g hfg
    obtain ⟨P⟩ := finiteRepresentablePresentation_nonempty hP M
    apply (cancel_epi P.f).1
    apply biproduct.hom_ext'
    intro i
    let G := finiteCategoryProjectiveGenerator hP
    let Q := fun X : C ↦ representable hP X
    let a : G ⟶ M :=
      biproduct.π Q (P.X i) ≫
        biproduct.ι (fun j ↦ representable hP (P.X j)) i ≫ P.f
    have ha := ConcreteCategory.congr_hom hfg a
    change a ≫ f = a ≫ g at ha
    have hai := congrArg
      (fun q ↦ biproduct.ι Q (P.X i) ≫ q) ha
    simpa [a, Q, representable, Category.assoc] using hai

/-- The represented functor of the finite projective generator is full. -/
instance representedFull :
    (preadditiveCoyonedaObj (finiteCategoryProjectiveGenerator hP)).Full :=
  MagnitudeConjecture.CategoryTheory.preadditiveCoyonedaObj_full_of_finiteAddGeneratorPresentations
      (finiteCategoryProjectiveGenerator hP) inferInstance
      (finiteAddGeneratorPresentation_nonempty hP)

/-- The finite category algebra in the right-module convention. -/
abbrev algebra := End (finiteCategoryProjectiveGenerator hP)

/-- The finite category algebra is finite-dimensional over the coefficient
field. -/
theorem algebra_finiteDimensional :
    FiniteDimensional k (algebra hP) :=
  finiteDimensionalModuleHom_finiteDimensional k _ _

/-- `Hom(G,-)` restricted to finitely generated right modules over the finite
category algebra. -/
def representedFGFunctor :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k ⥤
      FGModuleCat.{max u v} (algebra hP)ᵐᵒᵖ :=
  (ModuleCat.isFG.{max u v} (algebra hP)ᵐᵒᵖ).lift
    (preadditiveCoyonedaObj (finiteCategoryProjectiveGenerator hP))
    (fun M ↦ by
      let G := finiteCategoryProjectiveGenerator hP
      let F := preadditiveCoyonedaObj G
      obtain ⟨P⟩ := finiteRepresentablePresentation_nonempty hP M
      have hsource : MagnitudeConjecture.CategoryTheory.finiteAddClosure
          G P.source :=
        ⟨finiteRepresentableSumPresentation hP P.X⟩
      let X :
          (MagnitudeConjecture.CategoryTheory.finiteAddClosure G).FullSubcategory :=
        ⟨P.source, hsource⟩
      have hadd : MagnitudeConjecture.CategoryTheory.finiteAddClosure
          (F.obj G) (F.obj P.source) :=
        ⟨MagnitudeConjecture.CategoryTheory.homFromGenerator_obj_finiteAddPresentation
          G X⟩
      have hfiniteSource : Module.Finite (algebra hP)ᵐᵒᵖ (F.obj P.source) :=
        (show MagnitudeConjecture.CategoryTheory.finiteProjectiveModules
            (algebra hP)ᵐᵒᵖ (F.obj P.source) by
          rw [← MagnitudeConjecture.CategoryTheory.finiteAddClosure_homSelf_eq_finiteProjective
            G]
          exact hadd).1
      letI : Module.Finite (algebra hP)ᵐᵒᵖ (F.obj P.source) :=
        hfiniteSource
      apply Module.Finite.of_surjective (F.map P.f).hom
      intro f
      refine ⟨Projective.factorThru f P.f, ?_⟩
      exact Projective.factorThru_comp f P.f)

/-- The target restriction of the represented functor remains additive. -/
instance representedFGFunctor_additive :
    (representedFGFunctor hP).Additive where
  map_add {X Y} f g := by
    apply ObjectProperty.hom_ext
    exact
      (preadditiveCoyonedaObj
        (finiteCategoryProjectiveGenerator hP)).map_add (f := f) (g := g)

/-- The target-restricted represented functor respects the coefficient-field
linear structures. -/
instance representedFGFunctor_linear :
    (representedFGFunctor hP).Linear k where
  map_smul {X Y} f r := by
    let F := representedFGFunctor hP
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
          (algebraMap k (algebra hP)ᵐᵒᵖ r) • (g ≫ f) := by
      change r • (g ≫ f) = (r • 𝟙 _) ≫ (g ≫ f)
      simp
    exact hscalar

/-- The target-restricted represented functor remains faithful. -/
instance representedFGFunctor_faithful :
    (representedFGFunctor hP).Faithful where
  map_injective := by
    intro M N f g hfg
    apply
      (preadditiveCoyonedaObj
        (finiteCategoryProjectiveGenerator hP)).map_injective
    exact congrArg (fun q ↦ q.hom) hfg

/-- The target-restricted represented functor remains full. -/
instance representedFGFunctor_full :
    (representedFGFunctor hP).Full where
  map_surjective := by
    intro M N f
    obtain ⟨g, hg⟩ :=
      (preadditiveCoyonedaObj
        (finiteCategoryProjectiveGenerator hP)).map_surjective f.hom
    refine ⟨g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg

/-- A finite power of the projective generator. -/
abbrev generatorPower (n : ℕ) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  ⨁ fun _ : Fin n ↦ finiteCategoryProjectiveGenerator hP

/-- The represented module of a finite generator power is the corresponding
finite free module over the opposite endomorphism algebra. -/
def representedGeneratorPowerIso (n : ℕ) :
    (preadditiveCoyonedaObj (finiteCategoryProjectiveGenerator hP)).obj
        (generatorPower hP n) ≅
      ModuleCat.of (algebra hP)ᵐᵒᵖ (Fin n → (algebra hP)ᵐᵒᵖ) :=
  ((preadditiveCoyonedaObj
      (finiteCategoryProjectiveGenerator hP)).mapBiproduct
        (fun _ : Fin n ↦ finiteCategoryProjectiveGenerator hP)).trans
    ((biproduct.mapIso fun _ : Fin n ↦
      (MagnitudeConjecture.CategoryTheory.regularLinearEquiv
        (finiteCategoryProjectiveGenerator hP)).toModuleIso.symm).trans
      (ModuleCat.biproductIsoPi
        (fun _ : Fin n ↦
          ModuleCat.of (algebra hP)ᵐᵒᵖ (algebra hP)ᵐᵒᵖ)))

/-- Every finitely generated right module over the finite category algebra is
represented. -/
theorem representedFGFunctor_essSurj :
    (representedFGFunctor hP).EssSurj := by
  let G := finiteCategoryProjectiveGenerator hP
  let R := (algebra hP)ᵐᵒᵖ
  let F := preadditiveCoyonedaObj G
  letI : FiniteDimensional k (algebra hP) := algebra_finiteDimensional hP
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
  let φm := representedGeneratorPowerIso hP m
  let φn := representedGeneratorPowerIso hP n
  let δ : F.obj (generatorPower hP m) ⟶
      F.obj (generatorPower hP n) :=
    φm.hom ≫ dModule ≫ φn.inv
  let dC : generatorPower hP m ⟶ generatorPower hP n :=
    F.preimage δ
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

/-- Finite-dimensional modules over a finite linear category are equivalent
to finitely generated right modules over its finite category algebra. -/
def moduleEquivalence :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k ≌
      FGModuleCat.{max u v} (algebra hP)ᵐᵒᵖ := by
  letI : (representedFGFunctor hP).IsEquivalence :=
    Functor.IsEquivalence.mk inferInstance inferInstance
      (representedFGFunctor_essSurj hP)
  exact (representedFGFunctor hP).asEquivalence

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
