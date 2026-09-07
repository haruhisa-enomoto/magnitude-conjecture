import MagnitudeConjecture.Algebra.RightModuleIyamaSimpleResolution
import MagnitudeConjecture.Algebra.RightModuleNakayamaHom

/-!
# Opposite Auslander simples from strict left tau meshes

For a surviving indecomposable `X`, evaluation of the strict left tau mesh
starting at `X` gives a projective resolution of the corresponding simple
module over `End(G)`, where `G` is the full factor generator.  This is the
opposite-side counterpart of `RightModuleIyamaSimpleResolution`, which uses
right meshes to resolve simples over the factor Auslander ring `End(G)ᵒᵖ`.

The projectivity input is obtained without importing a second categorical
realization: full additive Yoneda identifies `Hom(X,G)` with the regular-Hom
dual of the projective `Hom(G,X)`, and the finite-projective duality already
developed for Nakayama modules makes that dual projective over `End(G)`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

abbrev factorOppositeAuslanderRing (K : Set (Fin S.n)) :=
  End (S.factorAdditiveGenerator K)

/-- A full-generator representable, bundled over the factor Auslander ring. -/
abbrev factorAuslanderRepresentableFGObj
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    FGModuleCat.{u} (S.factorOppositeAuslanderRing K)ᵐᵒᵖ :=
  FGModuleCat.of (S.factorOppositeAuslanderRing K)ᵐᵒᵖ
    (S.factorAdditiveGenerator K ⟶ X)

def factorCorepresentableRegularHomDualLinearEquiv
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    (X ⟶ S.factorAdditiveGenerator K) ≃ₗ[
      S.factorOppositeAuslanderRing K]
      RightModule.regularHomDualCarrier
        (S.factorAuslanderRepresentableFGObj K X) := by
  let G := S.factorAdditiveGenerator K
  let P : FiniteAddPresentation G X :=
    (S.factorAdditiveGenerator_isFiniteAddGenerator K X).some
  let toLinear : (X ⟶ G) →ₗ[End G]
      RightModule.regularHomDualCarrier
        (S.factorAuslanderRepresentableFGObj K X) :=
    { toFun := fun f ↦
        { toFun := fun q ↦ q ≫ f
          map_add' := by
            intro q r
            change ((q : G ⟶ X) + (r : G ⟶ X)) ≫ f =
              (q : G ⟶ X) ≫ f + (r : G ⟶ X) ≫ f
            rw [Preadditive.add_comp]
          map_smul' := by
            intro a q
            change (End.asHom a.unop ≫ q) ≫ f =
              End.asHom a.unop ≫ (q ≫ f)
            exact Category.assoc _ _ _ }
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro q
        change q ≫ (f + g) = q ≫ f + q ≫ g
        simp only [Preadditive.comp_add]
      map_smul' := by
        intro a f
        apply LinearMap.ext
        intro q
        change q ≫ (f ≫ End.asHom a) =
          (q ≫ f) ≫ End.asHom a
        exact (Category.assoc _ _ _).symm }
  let inverse (phi : RightModule.regularHomDualCarrier
      (S.factorAuslanderRepresentableFGObj K X)) : X ⟶ G :=
    Classical.choose
      (exists_hom_of_moduleHom_of_finiteAddSource G P
        (ModuleCat.ofHom phi))
  refine
    { toLinearMap := toLinear
      invFun := inverse
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    have hspec := Classical.choose_spec
      (exists_hom_of_moduleHom_of_finiteAddSource G P
        (ModuleCat.ofHom (toLinear f)))
    change inverse (toLinear f) = f
    apply (cancel_epi P.retract.r).1
    apply biproduct.hom_ext'
    intro i
    have hi := congrArg
      (fun q ↦ q.hom
        (biproduct.ι (fun _ : Fin P.n ↦ G) i ≫ P.retract.r)) hspec
    change
      (biproduct.ι (fun _ : Fin P.n ↦ G) i ≫ P.retract.r) ≫
          inverse (toLinear f) =
        (biproduct.ι (fun _ : Fin P.n ↦ G) i ≫ P.retract.r) ≫ f at hi
    simpa only [Category.assoc] using hi
  · intro phi
    have hspec := Classical.choose_spec
      (exists_hom_of_moduleHom_of_finiteAddSource G P
        (ModuleCat.ofHom phi))
    apply LinearMap.ext
    intro q
    have hq := congrArg (fun h ↦ h.hom q) hspec
    exact hq

omit [IsAlgClosed k] in
/-- Every full-generator corepresentable is finite projective over `End(G)`. -/
theorem factorCorepresentable_finiteProjective
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    CategoryTheory.finiteProjectiveModules
      (S.factorOppositeAuslanderRing K)
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (X ⟶ S.factorAdditiveGenerator K)) := by
  let P := S.factorAuslanderRepresentableFGObj K X
  letI : Projective
      (ModuleCat.of (S.factorAuslanderRing K)
        (S.factorAdditiveGenerator K ⟶ X)) :=
    (S.factorAuslanderRepresentable_finiteProjective K X).2
  let hmodule : Module.Projective (S.factorAuslanderRing K)
      (S.factorAdditiveGenerator K ⟶ X) :=
    ModuleCat.projective_of_module_projective
      (ModuleCat.of (S.factorAuslanderRing K)
        (S.factorAdditiveGenerator K ⟶ X))
  letI : Projective P :=
    MagnitudeConjecture.fgProjective_of_moduleProjective P hmodule
  have hdual : Module.Projective (S.factorOppositeAuslanderRing K)
      (RightModule.regularHomDualCarrier P) :=
    RightModule.regularHomDual_moduleProjective P
  letI : Module.Projective (S.factorOppositeAuslanderRing K)
      (RightModule.regularHomDualCarrier P) := hdual
  have hprojective : Projective
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (RightModule.regularHomDualCarrier P)) := inferInstance
  let I := RightModule.regularHomDualFGObj (k := k) P
  have hfinite : Module.Finite (S.factorOppositeAuslanderRing K)
      (RightModule.regularHomDualCarrier P) := by
    exact I.property
  constructor
  · letI : Module.Finite (S.factorOppositeAuslanderRing K)
        (RightModule.regularHomDualCarrier P) := hfinite
    exact Module.Finite.equiv
      (S.factorCorepresentableRegularHomDualLinearEquiv K X).symm
  · exact Projective.of_iso
      (S.factorCorepresentableRegularHomDualLinearEquiv K X).symm.toModuleIso
      hprojective

def factorCorepresentableRadical
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Submodule (S.factorOppositeAuslanderRing K)
      (S.factorObject K x ⟶ S.factorAdditiveGenerator K) where
  carrier :=
    (S.factorFiniteTauCategoryData K).radical.ideal.hom
      (S.factorObject K x) (S.factorAdditiveGenerator K)
  zero_mem' :=
    ((S.factorFiniteTauCategoryData K).radical.ideal.hom _ _).zero_mem
  add_mem' :=
    ((S.factorFiniteTauCategoryData K).radical.ideal.hom _ _).add_mem
  smul_mem' := by
    intro a f hf
    change f ≫ End.asHom a ∈
      (S.factorFiniteTauCategoryData K).radical.ideal.hom _ _
    exact (S.factorFiniteTauCategoryData K).radical.ideal.postcomp
      (End.asHom a) hf

omit [IsAlgClosed k] in
@[simp]
theorem mem_factorCorepresentableRadical_iff
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    (f : S.factorObject K x ⟶ S.factorAdditiveGenerator K) :
    f ∈ S.factorCorepresentableRadical K x ↔
      QuotientSubmoduleEquidistribution.CategoricalRadical.IsRadicalMorphism f :=
  (S.factorFiniteTauCategoryData K).radical.mem_ideal_iff f

abbrev factorOppositeAuslanderSimple
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :=
  (S.factorObject K x ⟶ S.factorAdditiveGenerator K) ⧸
    S.factorCorepresentableRadical K x

noncomputable instance factorOppositeAuslanderSimpleModule
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Module k (S.factorOppositeAuslanderSimple K x) :=
  Module.restrictScalars k (S.factorOppositeAuslanderRing K)
    (S.factorOppositeAuslanderSimple K x)

noncomputable instance factorOppositeAuslanderSimpleIsScalarTower
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    IsScalarTower k (S.factorOppositeAuslanderRing K)
      (S.factorOppositeAuslanderSimple K x) :=
  IsScalarTower.restrictScalars k (S.factorOppositeAuslanderRing K)
    (S.factorOppositeAuslanderSimple K x)

def factorCorepresentableMeshSourceMap
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    S.factorObject K x ⟶
      (S.factorFiniteTauCategoryData K).thetaMinus x :=
  ((S.factorFiniteTauCategoryData K).leftTermIso
      (S.factorObject K x)).inv ≫
    ((S.factorFiniteTauCategoryData K).leftMesh
      (S.factorObject K x)).f

def factorCorepresentableMeshNu
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    (((S.factorFiniteTauCategoryData K).leftMesh
        (S.factorObject K x)).X₃ ⟶ S.factorAdditiveGenerator K) →ₗ[
      S.factorOppositeAuslanderRing K]
      ((S.factorFiniteTauCategoryData K).thetaMinus x ⟶
        S.factorAdditiveGenerator K) :=
  ((preadditiveYonedaObj (S.factorAdditiveGenerator K)).map
    ((S.factorFiniteTauCategoryData K).leftMesh
      (S.factorObject K x)).g.op).hom

def factorCorepresentableMeshMu
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ((S.factorFiniteTauCategoryData K).thetaMinus x ⟶
        S.factorAdditiveGenerator K) →ₗ[
      S.factorOppositeAuslanderRing K]
      (S.factorObject K x ⟶ S.factorAdditiveGenerator K) :=
  ((preadditiveYonedaObj (S.factorAdditiveGenerator K)).map
    (S.factorCorepresentableMeshSourceMap K x).op).hom

omit [IsAlgClosed k] in
theorem factorCorepresentableMesh_exact_middle
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Function.Exact
      (S.factorCorepresentableMeshNu K x)
      (S.factorCorepresentableMeshMu K x) := by
  let T := S.factorFiniteTauCategoryData K
  change Function.Exact
    (fun l : (T.leftMesh (T.obj x)).X₃ ⟶ S.factorAdditiveGenerator K ↦
      (T.leftMesh (T.obj x)).g ≫ l)
    (fun f : T.thetaMinus x ⟶ S.factorAdditiveGenerator K ↦
      ((T.leftTermIso (T.obj x)).inv ≫
        (T.leftMesh (T.obj x)).f) ≫ f)
  intro f
  constructor
  · intro hf
    have hff : (T.leftMesh (T.obj x)).f ≫ f = 0 := by
      apply (cancel_epi (T.leftTermIso (T.obj x)).inv).1
      simpa only [Category.assoc, comp_zero] using hf
    exact (T.leftTau (T.obj x)).exact_precomp
      (S.factorAdditiveGenerator K) f |>.mp hff
  · rintro ⟨g, rfl⟩
    change
      ((T.leftTermIso (T.obj x)).inv ≫
        (T.leftMesh (T.obj x)).f) ≫
          ((T.leftMesh (T.obj x)).g ≫ g) = 0
    rw [Category.assoc,
      ← Category.assoc (T.leftMesh (T.obj x)).f,
      (T.leftMesh (T.obj x)).zero, zero_comp, comp_zero]

omit [IsAlgClosed k] in
theorem range_factorCorepresentableMeshMu
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    LinearMap.range (S.factorCorepresentableMeshMu K x) =
      S.factorCorepresentableRadical K x := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    rw [S.mem_factorCorepresentableRadical_iff K x]
    change QuotientSubmoduleEquidistribution.CategoricalRadical.IsRadicalMorphism
      (S.factorCorepresentableMeshSourceMap K x ≫ g)
    dsimp only [factorCorepresentableMeshSourceMap]
    simpa only [Category.assoc] using
      QuotientSubmoduleEquidistribution.CategoricalRadical.isRadicalMorphism_precomp
        ((S.factorFiniteTauCategoryData K).leftTermIso
          (S.factorObject K x)).inv
        (QuotientSubmoduleEquidistribution.CategoricalRadical.isRadicalMorphism_postcomp
          g ((S.factorFiniteTauCategoryData K).leftTau
            (S.factorObject K x)).f_radical)
  · intro hf
    have hfRad :
        QuotientSubmoduleEquidistribution.CategoricalRadical.IsRadicalMorphism f :=
      (S.mem_factorCorepresentableRadical_iff K x f).1 hf
    let e := (S.factorFiniteTauCategoryData K).leftTermIso
      (S.factorObject K x)
    have hf'Rad :
        QuotientSubmoduleEquidistribution.CategoricalRadical.IsRadicalMorphism
          (e.hom ≫ f) :=
      QuotientSubmoduleEquidistribution.CategoricalRadical.isRadicalMorphism_precomp
        e.hom hfRad
    obtain ⟨g, hg⟩ :=
      ((S.factorFiniteTauCategoryData K).leftTau
        (S.factorObject K x)).factors_from_left (e.hom ≫ f) hf'Rad
    refine ⟨g, ?_⟩
    change (e.inv ≫ ((S.factorFiniteTauCategoryData K).leftMesh
      (S.factorObject K x)).f) ≫ g = f
    calc
      (e.inv ≫ ((S.factorFiniteTauCategoryData K).leftMesh
          (S.factorObject K x)).f) ≫ g =
          e.inv ≫ (e.hom ≫ f) := by
            rw [Category.assoc, hg]
      _ = (e.inv ≫ e.hom) ≫ f := (Category.assoc _ _ _).symm
      _ = f := by rw [e.inv_hom_id, Category.id_comp]

def factorOppositeAuslanderSimpleGenerator
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    S.factorOppositeAuslanderSimple K x :=
  (S.factorCorepresentableRadical K x).mkQ
    (biproduct.ι
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x)

omit [IsAlgClosed k] in
theorem factorOppositeAuslanderSimpleGenerator_ne_zero
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    S.factorOppositeAuslanderSimpleGenerator K x ≠ 0 := by
  intro hzero
  let i : S.factorObject K x ⟶ S.factorAdditiveGenerator K :=
    biproduct.ι
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x
  have hinclusion : i ∈ S.factorCorepresentableRadical K x :=
    (Submodule.Quotient.mk_eq_zero _).1 hzero
  have hidmem :
      (biproduct.ι
          (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x ≫
        biproduct.π
          (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x) ∈
      (S.factorFiniteTauCategoryData K).radical.ideal.hom
        (S.factorObject K x) (S.factorObject K x) :=
    (S.factorFiniteTauCategoryData K).radical.ideal.postcomp
      (biproduct.π
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x)
      hinclusion
  have hidrad :
      QuotientSubmoduleEquidistribution.CategoricalRadical.IsRadicalMorphism
        (𝟙 (S.factorObject K x)) := by
    rw [biproduct.ι_π_self] at hidmem
    exact ((S.factorFiniteTauCategoryData K).radical.mem_ideal_iff _).1
      hidmem
  exact
    (((S.factorFiniteTauCategoryData K).isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (𝟙 (S.factorObject K x))).1 hidrad)
      (inferInstance : IsSplitEpi (𝟙 (S.factorObject K x)))

theorem finrank_factorOppositeAuslanderSimple_eq_one
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Module.finrank k
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorOppositeAuslanderSimple K x)) = 1 := by
  let T := S.factorFiniteTauCategoryData K
  apply (finrank_eq_one_iff_of_nonzero'
    (S.factorOppositeAuslanderSimpleGenerator K x)
    (S.factorOppositeAuslanderSimpleGenerator_ne_zero K x)).2
  intro q
  obtain ⟨f, rfl⟩ :=
    (S.factorCorepresentableRadical K x).mkQ_surjective q
  let i : S.factorObject K x ⟶ S.factorAdditiveGenerator K :=
    biproduct.ι
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x
  obtain ⟨c, hc⟩ := H.factorObject_endomorphism_eq_smul_id S K x
    (f ≫ biproduct.π
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x)
  refine ⟨c, ?_⟩
  have hscalar :
      (algebraMap k (S.factorOppositeAuslanderRing K) c) • i = c • i := by
    change i ≫ (c • 𝟙 (S.factorAdditiveGenerator K)) = c • i
    rw [CategoryTheory.Linear.comp_smul, Category.comp_id]
  apply (Submodule.Quotient.eq
    (S.factorCorepresentableRadical K x)).2
  change
    (algebraMap k (S.factorOppositeAuslanderRing K) c) • i - f ∈
      T.radical.ideal.hom
        (S.factorObject K x) (S.factorAdditiveGenerator K)
  rw [hscalar]
  unfold factorAdditiveGenerator at i f ⊢
  have hcomponent : ∀ a : S.SurvivingLabel K,
      (c • i - f) ≫ biproduct.π
          (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a ∈
        T.radical.ideal.hom (S.factorObject K x) (S.factorObject K a) := by
    intro a
    by_cases hax : a = x
    · subst a
      have hzero :
          (c • i - f) ≫ biproduct.π
              (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x = 0 := by
        rw [Preadditive.sub_comp, CategoryTheory.Linear.smul_comp,
          biproduct.ι_π_self, hc]
        exact sub_self _
      rw [hzero]
      exact (T.radical.ideal.hom _ _).zero_mem
    · have hrad : f ≫ biproduct.π
          (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a ∈
          T.radical.ideal.hom (S.factorObject K x) (S.factorObject K a) :=
        S.factorHom_mem_radical_of_ne K (Ne.symm hax) _
      have heq :
          (c • i - f) ≫ biproduct.π
              (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a =
            -(f ≫ biproduct.π
              (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a) := by
        rw [Preadditive.sub_comp, CategoryTheory.Linear.smul_comp,
          biproduct.ι_π_ne _ (Ne.symm hax), smul_zero, zero_sub]
      rw [heq]
      exact (T.radical.ideal.hom _ _).neg_mem hrad
  have hsum : c • i - f = ∑ a : S.SurvivingLabel K,
      ((c • i - f) ≫ biproduct.π
          (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a) ≫
        biproduct.ι
          (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a := by
    calc
      c • i - f = (c • i - f) ≫
          𝟙 (⨁ fun a : S.SurvivingLabel K ↦ S.factorObject K a) := by
        rw [Category.comp_id]
      _ = (c • i - f) ≫
          (∑ a : S.SurvivingLabel K,
            biproduct.π
                (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a ≫
              biproduct.ι
                (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a) := by
        rw [biproduct.total]
      _ = _ := by
        rw [Preadditive.comp_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Category.assoc]
  rw [hsum]
  apply (T.radical.ideal.hom _ _).sum_mem
  intro a _
  exact T.radical.ideal.postcomp
    (biproduct.ι
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) a)
    (hcomponent a)

theorem factorOppositeAuslanderSimple_simple
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    CategoryTheory.Simple
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorOppositeAuslanderSimple K x)) :=
  simple_of_finrank_eq_one (k := k)
    (R := S.factorOppositeAuslanderRing K)
    (S.finrank_factorOppositeAuslanderSimple_eq_one H K x)

def factorCorepresentableMeshMuToRadical
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    ((S.factorFiniteTauCategoryData K).thetaMinus x ⟶
        S.factorAdditiveGenerator K) →ₗ[
      S.factorOppositeAuslanderRing K]
      S.factorCorepresentableRadical K x :=
  (S.factorCorepresentableMeshMu K x).codRestrict
    (S.factorCorepresentableRadical K x) (fun y ↦ by
      rw [← S.range_factorCorepresentableMeshMu K x]
      exact ⟨y, rfl⟩)

omit [IsAlgClosed k] in
theorem factorCorepresentableMesh_exact_radical
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Function.Exact
      (S.factorCorepresentableMeshNu K x)
      (S.factorCorepresentableMeshMuToRadical K x) := by
  intro y
  constructor
  · intro hy
    apply (S.factorCorepresentableMesh_exact_middle K x y).1
    exact congrArg Subtype.val hy
  · intro hy
    apply Subtype.ext
    exact (S.factorCorepresentableMesh_exact_middle K x y).2 hy

omit [IsAlgClosed k] in
theorem factorCorepresentableMeshNu_injective
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (x : S.SurvivingLabel K) :
    Function.Injective (S.factorCorepresentableMeshNu K x) := by
  let T := S.factorFiniteTauCategoryData K
  letI : Epi (T.leftMesh (T.obj x)).g :=
    PrimitiveFactorInput.leftMesh_epi (S := S) D x
  intro a b hab
  apply (cancel_epi (T.leftMesh (T.obj x)).g).1
  exact hab

omit [IsAlgClosed k] in
theorem factorCorepresentableMeshMuToRadical_surjective
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    Function.Surjective
      (S.factorCorepresentableMeshMuToRadical K x) := by
  intro z
  have hz : z.1 ∈ LinearMap.range
      (S.factorCorepresentableMeshMu K x) := by
    rw [S.range_factorCorepresentableMeshMu K x]
    exact z.2
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, Subtype.ext ?_⟩
  exact hy

omit [IsAlgClosed k] in
/-- A strict left tau mesh gives a length-two projective resolution of the
corresponding simple quotient over the opposite Auslander ring. -/
theorem factorOppositeAuslanderSimple_hasProjectiveDimensionLE_two
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (x : S.SurvivingLabel K) :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorOppositeAuslanderSimple K x)) 2 := by
  let C₁ : ShortComplex
      (ModuleCat.{u} (S.factorOppositeAuslanderRing K)) :=
    ModuleCat.shortComplexOfCompEqZero
      (S.factorCorepresentableMeshNu K x)
      (S.factorCorepresentableMeshMuToRadical K x) (by
        apply LinearMap.ext
        intro y
        change S.factorCorepresentableMeshMuToRadical K x
          (S.factorCorepresentableMeshNu K x y) = 0
        exact (S.factorCorepresentableMesh_exact_radical K x
          (S.factorCorepresentableMeshNu K x y)).2 ⟨y, rfl⟩)
  have hC₁ : C₁.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · exact S.factorCorepresentableMesh_exact_radical K x
    · exact S.factorCorepresentableMeshNu_injective D x
    · exact S.factorCorepresentableMeshMuToRadical_surjective K x
  have hP₂ : Projective C₁.X₁ := by
    change Projective
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (((S.factorFiniteTauCategoryData K).leftMesh
          (S.factorObject K x)).X₃ ⟶ S.factorAdditiveGenerator K))
    exact (S.factorCorepresentable_finiteProjective K _).2
  have hP₁ : Projective C₁.X₂ := by
    change Projective
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        ((S.factorFiniteTauCategoryData K).thetaMinus x ⟶
          S.factorAdditiveGenerator K))
    exact (S.factorCorepresentable_finiteProjective K _).2
  have hradical : HasProjectiveDimensionLE C₁.X₃ 1 := by
    letI : Projective C₁.X₁ := hP₂
    letI : Projective C₁.X₂ := hP₁
    exact hC₁.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance
  let C₀ : ShortComplex
      (ModuleCat.{u} (S.factorOppositeAuslanderRing K)) :=
    ModuleCat.shortComplexOfCompEqZero
      (S.factorCorepresentableRadical K x).subtype
      (S.factorCorepresentableRadical K x).mkQ (by
        ext y
        simp)
  have hC₀ : C₀.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · exact LinearMap.exact_subtype_mkQ
        (S.factorCorepresentableRadical K x)
    · exact (S.factorCorepresentableRadical K x).injective_subtype
    · exact (S.factorCorepresentableRadical K x).mkQ_surjective
  have hP₀ : Projective C₀.X₂ := by
    change Projective
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorObject K x ⟶ S.factorAdditiveGenerator K))
    exact (S.factorCorepresentable_finiteProjective K _).2
  letI : HasProjectiveDimensionLE C₀.X₁ 1 := by
    change HasProjectiveDimensionLE C₁.X₃ 1
    exact hradical
  letI : Projective C₀.X₂ := hP₀
  exact hC₀.hasProjectiveDimensionLT_X₃ 2 inferInstance inferInstance

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
