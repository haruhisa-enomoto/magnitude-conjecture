import MagnitudeConjecture.Algebra.RightModuleIyamaDualSimpleResolution
import MagnitudeConjecture.CategoryTheory.FGExtRealization
import MagnitudeConjecture.CategoryTheory.ProjectiveDimensionBiproduct
import Mathlib.CategoryTheory.Abelian.Injective.Dimension

/-!
# The tau-projective boundary Nakayama estimate

Strict left tau meshes resolve the simple modules over `End(G)`.  If `X`
is tau-projective, every map from `X` into the nonprojective third term of a
left mesh is radical, so the left tau approximation makes the relevant
degree-two Ext class vanish.  Classification of simples and finite-length
induction then give injective dimension at most one for `Hom(X,G)`.

Finite contragredient duality turns a corresponding injective copresentation
into a two-term projective presentation of the Nakayama module.  Finally,
additivity assembles the indecomposable estimates over the literal boundary
generator `U`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MagnitudeConjecture.CategoryTheory
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.Iyama

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u v w

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

noncomputable local instance fgModuleCatHasFiniteBiproducts
    {R : Type u} [Ring R] [IsNoetherianRing R] :
    HasFiniteBiproducts (FGModuleCat.{u} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

omit [IsAlgClosed k] in
theorem exists_factorCorepresentable_hom_of_moduleHom
    (K : Set (Fin S.n)) {X Y : S.FactorCategory K}
    (P : FiniteAddPresentation (S.factorAdditiveGenerator K) Y)
    (α : ModuleCat.of (S.factorOppositeAuslanderRing K)
        (Y ⟶ S.factorAdditiveGenerator K) ⟶
      ModuleCat.of (S.factorOppositeAuslanderRing K)
        (X ⟶ S.factorAdditiveGenerator K)) :
    ∃ f : X ⟶ Y,
      ((preadditiveYonedaObj (S.factorAdditiveGenerator K)).map f.op) = α := by
  let G := S.factorAdditiveGenerator K
  let q : X ⟶ (⨁ fun _ : Fin P.n ↦ G) :=
    biproduct.lift fun j ↦
      α.hom (P.retract.i ≫ biproduct.π (fun _ : Fin P.n ↦ G) j)
  let f : X ⟶ Y := q ≫ P.retract.r
  refine ⟨f, ?_⟩
  apply ModuleCat.hom_ext
  ext l
  change Y ⟶ G at l
  change f ≫ l = α.hom l
  let F : Fin P.n → S.FactorCategory K := fun _ ↦ G
  have hr : P.retract.r ≫ l = biproduct.desc (fun j : Fin P.n ↦
      biproduct.ι F j ≫ P.retract.r ≫ l) := by
    apply biproduct.hom_ext'
    intro j
    simp only [F, G, biproduct.ι_desc]
  have hl : l = ∑ j : Fin P.n,
      (P.retract.i ≫ biproduct.π F j) ≫
        (biproduct.ι F j ≫
          P.retract.r ≫ l) := by
    calc
      l = (P.retract.i ≫ P.retract.r) ≫ l := by
        rw [P.retract.retract, Category.id_comp]
      _ = P.retract.i ≫ (P.retract.r ≫ l) :=
        Category.assoc _ _ _
      _ = P.retract.i ≫ biproduct.desc (fun j : Fin P.n ↦
          biproduct.ι F j ≫ P.retract.r ≫ l) := by
        exact congrArg (fun z ↦ P.retract.i ≫ z) hr
      _ = P.retract.i ≫ ∑ j : Fin P.n,
          biproduct.π F j ≫
            (biproduct.ι F j ≫ P.retract.r ≫ l) := by
        rw [biproduct.desc_eq]
      _ = _ := by
        simp only [Preadditive.comp_sum, Category.assoc]
  calc
    f ≫ l = (biproduct.lift fun j : Fin P.n ↦
        α.hom (P.retract.i ≫ biproduct.π F j)) ≫
          (P.retract.r ≫ l) := by
      dsimp only [f, q, F]
      exact Category.assoc _ _ _
    _ = (biproduct.lift fun j : Fin P.n ↦
        α.hom (P.retract.i ≫ biproduct.π F j)) ≫
          biproduct.desc (fun j : Fin P.n ↦
            biproduct.ι F j ≫ P.retract.r ≫ l) := by
      exact congrArg (fun z ↦
        (biproduct.lift fun j : Fin P.n ↦
          α.hom (P.retract.i ≫ biproduct.π F j)) ≫ z) hr
    _ = ∑ j : Fin P.n,
        α.hom (P.retract.i ≫ biproduct.π F j) ≫
          (biproduct.ι F j ≫ P.retract.r ≫ l) := by
      rw [biproduct.lift_desc]
    _ = α.hom (∑ j : Fin P.n,
        (P.retract.i ≫ biproduct.π F j) ≫
          (biproduct.ι F j ≫ P.retract.r ≫ l)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      let e : End G := End.of
        (biproduct.ι F j ≫ P.retract.r ≫ l)
      change e • α.hom (P.retract.i ≫ biproduct.π F j) =
        α.hom (e • (P.retract.i ≫ biproduct.π F j))
      exact (α.hom.map_smul e _).symm
    _ = α.hom l := by rw [← hl]

def factorHomToGenerator (K : Set (Fin S.n)) :
    (finiteAddClosure (S.factorAdditiveGenerator K)).FullSubcategoryᵒᵖ ⥤
      ModuleCat.{u} (S.factorOppositeAuslanderRing K) :=
  (finiteAddClosure (S.factorAdditiveGenerator K)).ι.op ⋙
    preadditiveYonedaObj (S.factorAdditiveGenerator K)

omit [IsAlgClosed k] in
instance factorHomToGenerator_full (K : Set (Fin S.n)) :
    (S.factorHomToGenerator K).Full where
  map_surjective {X Y} α := by
    obtain ⟨f, hf⟩ := S.exists_factorCorepresentable_hom_of_moduleHom K
      X.unop.property.some α
    refine ⟨(ObjectProperty.homMk f).op, ?_⟩
    exact hf

omit [IsAlgClosed k] in
instance factorHomToGenerator_faithful (K : Set (Fin S.n)) :
    (S.factorHomToGenerator K).Faithful where
  map_injective {X Y} f g hfg := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    let P := X.unop.property.some
    apply (cancel_mono P.retract.i).1
    apply biproduct.hom_ext
    intro j
    have h := congrArg
      (fun a ↦ a.hom
        (P.retract.i ≫ biproduct.π
          (fun _ : Fin P.n ↦ S.factorAdditiveGenerator K) j)) hfg
    change f.unop.hom ≫
        (P.retract.i ≫ biproduct.π
          (fun _ : Fin P.n ↦ S.factorAdditiveGenerator K) j) =
      g.unop.hom ≫
        (P.retract.i ≫ biproduct.π
          (fun _ : Fin P.n ↦ S.factorAdditiveGenerator K) j) at h
    simpa only [Category.assoc] using h

def factorHomToGeneratorFullyFaithful (K : Set (Fin S.n)) :
    (S.factorHomToGenerator K).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

private def oppositeEndRingEquiv
    {C : Type v} [CategoryTheory.Category.{w} C]
    [CategoryTheory.Preadditive C] (X : C) :
    (CategoryTheory.End X)ᵐᵒᵖ ≃+*
      CategoryTheory.End (Opposite.op X) where
  toFun f := f.unop.op
  invFun f := MulOpposite.op f.unop
  left_inv := by intro f; cases f; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; apply Quiver.Hom.unop_inj; rfl
  map_mul' := by intro f g; apply Quiver.Hom.unop_inj; rfl

private theorem isLocalRing_mulOpposite {R : Type v} [Ring R] [IsLocalRing R] :
    IsLocalRing Rᵐᵒᵖ := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := R) (a := a.unop) (b := 1 - a.unop)
      (add_sub_cancel a.unop 1) with h | h
  · exact Or.inl (by simpa using h.op)
  · exact Or.inr (by simpa using h.op)

omit [IsAlgClosed k] in
theorem factorCorepresentable_end_isLocalRing
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    IsLocalRing
      (Module.End (S.factorOppositeAuslanderRing K)
        (S.factorObject K x ⟶ S.factorAdditiveGenerator K)) := by
  let G := S.factorAdditiveGenerator K
  let X : (finiteAddClosure G).FullSubcategory :=
    ⟨S.factorObject K x,
      S.factorAdditiveGenerator_isFiniteAddGenerator K
        (S.factorObject K x)⟩
  let U := (finiteAddClosure G).ι
  letI : IsLocalRing (End (U.obj X)) := by
    change IsLocalRing (End (S.factorObject K x))
    exact S.factorObject_end_isLocalRing K x
  letI : IsLocalRing (End X) :=
    RingEquiv.isLocalRing_noncomm
      (Functor.endRingEquivOfFullyFaithful U X).symm
  let Xop : (finiteAddClosure G).FullSubcategoryᵒᵖ := Opposite.op X
  letI : IsLocalRing (End Xop) :=
    letI : IsLocalRing (End X)ᵐᵒᵖ := isLocalRing_mulOpposite
    RingEquiv.isLocalRing_noncomm (oppositeEndRingEquiv X)
  let F := S.factorHomToGenerator K
  letI : F.Additive := by
    dsimp only [F, factorHomToGenerator]
    infer_instance
  letI : IsLocalRing (End (F.obj Xop)) :=
    RingEquiv.isLocalRing_noncomm
      (Functor.endRingEquivOfFullyFaithful F Xop)
  exact RingEquiv.isLocalRing_noncomm
    (ModuleCat.endRingEquiv (F.obj Xop))

theorem factorCorepresentableRadical_eq_jacobson
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K) :
    S.factorCorepresentableRadical K x =
      Module.jacobson (S.factorOppositeAuslanderRing K)
        (S.factorObject K x ⟶ S.factorAdditiveGenerator K) := by
  let R := S.factorOppositeAuslanderRing K
  let Q := S.factorObject K x ⟶ S.factorAdditiveGenerator K
  letI : Module.Finite R Q :=
    (S.factorCorepresentable_finiteProjective K
      (S.factorObject K x)).1
  letI : Module.Projective R Q := by
    apply (IsProjective.iff_projective Q).2
    exact (S.factorCorepresentable_finiteProjective K
      (S.factorObject K x)).2
  letI : Nontrivial Q := by
    refine ⟨biproduct.ι
      (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x, 0, ?_⟩
    intro hzero
    have hid : 𝟙 (S.factorObject K x) = 0 := by
      rw [← biproduct.ι_π_self
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x]
      rw [hzero]
      exact zero_comp
    exact S.factorObject_not_isZero K x
      ((IsZero.iff_id_eq_zero _).2 hid)
  letI : IsLocalRing (Module.End R Q) :=
    S.factorCorepresentable_end_isLocalRing K x
  have hjac : IsCoatom (Module.jacobson R Q) :=
    jacobson_isCoatom_of_projective_local_end
  have hrad : IsCoatom (S.factorCorepresentableRadical K x) := by
    rw [← isSimpleModule_iff_isCoatom]
    exact (simple_iff_isSimpleModule' _).1
      (S.factorOppositeAuslanderSimple_simple H K x)
  exact (hjac.le_iff_eq hrad.ne_top).mp (sInf_le hrad)

def factorCorepresentableToModule
    (K : Set (Fin S.n)) (x : S.SurvivingLabel K)
    {M : Type u} [AddCommGroup M]
    [Module (S.factorOppositeAuslanderRing K) M] (m : M) :
    (S.factorObject K x ⟶ S.factorAdditiveGenerator K) →ₗ[
      S.factorOppositeAuslanderRing K] M :=
  (LinearMap.toSpanSingleton (S.factorOppositeAuslanderRing K) M m).comp
    ((preadditiveYonedaObj (S.factorAdditiveGenerator K)).map
      (biproduct.π
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x).op).hom

omit [IsAlgClosed k] in
theorem exists_factorCorepresentableToModule_ne_zero
    (K : Set (Fin S.n))
    {M : Type u} [AddCommGroup M]
    [Module (S.factorOppositeAuslanderRing K) M]
    (m : M) (hm : m ≠ 0) :
    ∃ x : S.SurvivingLabel K,
      S.factorCorepresentableToModule K x m ≠ 0 := by
  classical
  let G := S.factorAdditiveGenerator K
  let q : (G ⟶ G) →ₗ[S.factorOppositeAuslanderRing K] M :=
    LinearMap.toSpanSingleton (S.factorOppositeAuslanderRing K) M m
  let term : S.SurvivingLabel K → (G ⟶ G) := fun x ↦
    (biproduct.π
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x :
      G ⟶ S.factorObject K x) ≫
    (biproduct.ι
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x :
      S.factorObject K x ⟶ G)
  by_contra h
  push Not at h
  have hx (x : S.SurvivingLabel K) : q (term x) = 0 := by
    have hxzero := DFunLike.congr_fun (h x)
      (biproduct.ι
        (fun a : S.SurvivingLabel K ↦ S.factorObject K a) x)
    change q (term x) = 0 at hxzero
    exact hxzero
  have hqid : q (𝟙 G) = m := by
    change (1 : S.factorOppositeAuslanderRing K) • m = m
    exact one_smul _ _
  have htotal : (∑ x : S.SurvivingLabel K, term x) = 𝟙 G := by
    exact biproduct.total
  apply hm
  rw [← hqid, ← htotal]
  rw [map_sum]
  exact Finset.sum_eq_zero fun x _ ↦ hx x

theorem exists_factorOppositeAuslanderSimple_linearEquiv
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (K : Set (Fin S.n))
    {M : Type u} [AddCommGroup M]
    [Module (S.factorOppositeAuslanderRing K) M]
    [IsSimpleModule (S.factorOppositeAuslanderRing K) M] :
    ∃ x : S.SurvivingLabel K,
      Nonempty (S.factorOppositeAuslanderSimple K x ≃ₗ[
        S.factorOppositeAuslanderRing K] M) := by
  letI : Nontrivial M :=
    (inferInstance : IsSimpleModule
      (S.factorOppositeAuslanderRing K) M).nontrivial
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨x, hx⟩ :=
    S.exists_factorCorepresentableToModule_ne_zero K m hm
  let φ := S.factorCorepresentableToModule K x m
  have hφ : Function.Surjective φ :=
    LinearMap.surjective_of_ne_zero hx
  have hker : IsCoatom (LinearMap.ker φ) := by
    rw [← isSimpleModule_iff_isCoatom]
    exact (φ.quotKerEquivOfSurjective hφ).isSimpleModule_iff.mpr
      (inferInstance : IsSimpleModule
        (S.factorOppositeAuslanderRing K) M)
  have hrad : IsCoatom (S.factorCorepresentableRadical K x) := by
    rw [← isSimpleModule_iff_isCoatom]
    exact (simple_iff_isSimpleModule' _).1
      (S.factorOppositeAuslanderSimple_simple H K x)
  have hle : S.factorCorepresentableRadical K x ≤
      LinearMap.ker φ := by
    rw [S.factorCorepresentableRadical_eq_jacobson H K x,
      Module.jacobson]
    exact sInf_le hker
  have hkerEq : LinearMap.ker φ =
      S.factorCorepresentableRadical K x :=
    (hrad.le_iff_eq hker.ne_top).mp hle
  refine ⟨x, ⟨?_⟩⟩
  let eKer := Submodule.Quotient.equiv
    (S.factorCorepresentableRadical K x) (LinearMap.ker φ)
    (LinearEquiv.refl (S.factorOppositeAuslanderRing K)
      (S.factorObject K x ⟶ S.factorAdditiveGenerator K)) (by
        simpa using hkerEq.symm)
  exact eKer.trans (φ.quotKerEquivOfSurjective hφ)

omit [IsAlgClosed k] in
theorem factorProjective_to_leftMeshThird_isRadical
    (K : Set (Fin S.n)) (x y : S.SurvivingLabel K)
    (hx : (S.factorFiniteTauCategoryData K).IsProjective x)
    (f : S.factorObject K x ⟶
      ((S.factorFiniteTauCategoryData K).leftMesh
        (S.factorObject K y)).X₃) :
    CategoricalRadical.IsRadicalMorphism f := by
  let T := S.factorFiniteTauCategoryData K
  change T.IsProjective x at hx
  change T.obj x ⟶ (T.leftMesh (T.obj y)).X₃ at f
  obtain ⟨n, label, ⟨e⟩, hlabel⟩ :=
    T.supportedOnNonprojectives_leftMesh_X₃ (T.obj y)
  have hfmem : f ∈ T.radical.ideal.hom
      (T.obj x) (T.leftMesh (T.obj y)).X₃ := by
    rw [show f = ∑ i : Fin n,
        (f ≫ e.hom ≫ biproduct.π (fun j ↦ T.obj (label j)) i) ≫
          biproduct.ι (fun j ↦ T.obj (label j)) i ≫ e.inv by
      calc
        f = f ≫ e.hom ≫ e.inv := by
          symm
          rw [e.hom_inv_id, Category.comp_id]
        _ = f ≫ e.hom ≫
            (∑ i : Fin n,
              biproduct.π (fun j ↦ T.obj (label j)) i ≫
                biproduct.ι (fun j ↦ T.obj (label j)) i) ≫ e.inv := by
          simp only [biproduct.total, Category.id_comp]
        _ = _ := by
          simp only [Preadditive.comp_sum, Preadditive.sum_comp,
            Category.assoc]]
    apply (T.radical.ideal.hom _ _).sum_mem
    intro i _
    exact T.radical.ideal.postcomp
      (biproduct.ι (fun j ↦ T.obj (label j)) i ≫ e.inv)
      (S.factorHom_mem_radical_of_ne K (a := x) (x := label i)
        (fun hxy ↦ hlabel i (hxy ▸ hx))
        (f ≫ e.hom ≫
          biproduct.π (fun j ↦ T.obj (label j)) i))
  exact (T.radical.mem_ideal_iff f).1 hfmem

omit [IsAlgClosed k] in
theorem factorCorepresentableMeshNu_hom_surjective_at_projective
    (K : Set (Fin S.n)) (x y : S.SurvivingLabel K)
    (hx : (S.factorFiniteTauCategoryData K).IsProjective x) :
    Function.Surjective (fun
      a : ModuleCat.of (S.factorOppositeAuslanderRing K)
          ((S.factorFiniteTauCategoryData K).thetaMinus y ⟶
            S.factorAdditiveGenerator K) ⟶
        ModuleCat.of (S.factorOppositeAuslanderRing K)
          (S.factorObject K x ⟶ S.factorAdditiveGenerator K) ↦
      (ModuleCat.ofHom (S.factorCorepresentableMeshNu K y)) ≫ a) := by
  intro h
  obtain ⟨f, hf⟩ := S.exists_factorCorepresentable_hom_of_moduleHom K
    (S.factorAdditiveGenerator_isFiniteAddGenerator K
      ((S.factorFiniteTauCategoryData K).leftMesh
        (S.factorObject K y)).X₃).some h
  have hrad : CategoricalRadical.IsRadicalMorphism f :=
    S.factorProjective_to_leftMeshThird_isRadical K x y hx f
  obtain ⟨b, hb⟩ :=
    ((S.factorFiniteTauCategoryData K).leftTau
      (S.factorObject K y)).factors_into_right f hrad
  let a : ModuleCat.of (S.factorOppositeAuslanderRing K)
        ((S.factorFiniteTauCategoryData K).thetaMinus y ⟶
          S.factorAdditiveGenerator K) ⟶
      ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorObject K x ⟶ S.factorAdditiveGenerator K) :=
    (preadditiveYonedaObj (S.factorAdditiveGenerator K)).map b.op
  refine ⟨a, ?_⟩
  rw [← hf]
  let F := preadditiveYonedaObj (S.factorAdditiveGenerator K)
  change F.map
      ((S.factorFiniteTauCategoryData K).leftMesh
        (S.factorObject K y)).g.op ≫ F.map b.op = F.map f.op
  rw [← F.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  change b ≫
    ((S.factorFiniteTauCategoryData K).leftMesh
      (S.factorObject K y)).g = f
  exact hb

noncomputable local instance factorOppositeAuslanderModuleHasExt
    (K : Set (Fin S.n)) :
    HasExt.{u} (ModuleCat.{u} (S.factorOppositeAuslanderRing K)) := by
  letI : EnoughProjectives
      (ModuleCat.{u} (S.factorOppositeAuslanderRing K)) :=
    ModuleCat.enoughProjectives
  exact CategoryTheory.hasExt_of_enoughProjectives _

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
omit [IsAlgClosed k] in
theorem factorOppositeAuslanderSimple_ext_two_corepresentable_eq_zero
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (x y : S.SurvivingLabel K)
    (hx : (S.factorFiniteTauCategoryData K).IsProjective x)
    (xi : Ext.{u}
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorOppositeAuslanderSimple K y))
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorObject K x ⟶ S.factorAdditiveGenerator K)) 2) :
    xi = 0 := by
  let C₁ : ShortComplex
      (ModuleCat.{u} (S.factorOppositeAuslanderRing K)) :=
    ModuleCat.shortComplexOfCompEqZero
      (S.factorCorepresentableMeshNu K y)
      (S.factorCorepresentableMeshMuToRadical K y) (by
        apply LinearMap.ext
        intro z
        change S.factorCorepresentableMeshMuToRadical K y
          (S.factorCorepresentableMeshNu K y z) = 0
        exact (S.factorCorepresentableMesh_exact_radical K y
          (S.factorCorepresentableMeshNu K y z)).2 ⟨z, rfl⟩)
  have hC₁ : C₁.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · exact S.factorCorepresentableMesh_exact_radical K y
    · exact S.factorCorepresentableMeshNu_injective D y
    · exact S.factorCorepresentableMeshMuToRadical_surjective K y
  let C₀ : ShortComplex
      (ModuleCat.{u} (S.factorOppositeAuslanderRing K)) :=
    ModuleCat.shortComplexOfCompEqZero
      (S.factorCorepresentableRadical K y).subtype
      (S.factorCorepresentableRadical K y).mkQ (by
        ext z
        simp)
  have hC₀ : C₀.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · exact LinearMap.exact_subtype_mkQ
        (S.factorCorepresentableRadical K y)
    · exact (S.factorCorepresentableRadical K y).injective_subtype
    · exact (S.factorCorepresentableRadical K y).mkQ_surjective
  let Q := ModuleCat.of (S.factorOppositeAuslanderRing K)
    (S.factorObject K x ⟶ S.factorAdditiveGenerator K)
  have hP₀ : Projective C₀.X₂ := by
    change Projective
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorObject K y ⟶ S.factorAdditiveGenerator K))
    exact (S.factorCorepresentable_finiteProjective K _).2
  have hP₁ : Projective C₁.X₂ := by
    change Projective
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        ((S.factorFiniteTauCategoryData K).thetaMinus y ⟶
          S.factorAdditiveGenerator K))
    exact (S.factorCorepresentable_finiteProjective K _).2
  have hxiZero :
      (Ext.mk₀ C₀.g).comp xi (zero_add 2) = 0 := by
    letI : Projective C₀.X₂ := hP₀
    exact Ext.eq_zero_of_projective _
  obtain ⟨eta, heta⟩ :=
    Ext.contravariant_sequence_exact₃ hC₀ Q xi hxiZero
      (rfl : 1 + 1 = 2)
  have hetaZero :
      (Ext.mk₀ C₁.g).comp eta (zero_add 1) = 0 := by
    letI : Projective C₁.X₂ := hP₁
    exact Ext.eq_zero_of_projective _
  obtain ⟨z, hz⟩ :=
    Ext.contravariant_sequence_exact₃ hC₁ Q eta hetaZero
      (rfl : 1 + 0 = 1)
  let zHom : C₁.X₁ ⟶ Q := Ext.addEquiv₀ z
  obtain ⟨a, ha⟩ :=
    S.factorCorepresentableMeshNu_hom_surjective_at_projective K x y hx zHom
  have hetaEqZero : eta = 0 := by
    rw [← hz]
    rw [← Ext.mk₀_addEquiv₀_apply z]
    change hC₁.extClass.comp (Ext.mk₀ zHom) (rfl : 1 + 0 = 1) = 0
    rw [← ha]
    rw [← Ext.mk₀_comp_mk₀]
    exact hC₁.extClass_comp_assoc (Ext.mk₀ a)
  rw [← heta, hetaEqZero]
  simp

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem simpleModule_ext_two_corepresentable_eq_zero
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.SurvivingLabel K)
    (hp : (S.factorFiniteTauCategoryData K).IsProjective p)
    {M : Type u} [AddCommGroup M]
    [Module (S.factorOppositeAuslanderRing K) M]
    [IsSimpleModule (S.factorOppositeAuslanderRing K) M]
    (xi : Ext.{u}
      (ModuleCat.of (S.factorOppositeAuslanderRing K) M)
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorObject K p ⟶ S.factorAdditiveGenerator K)) 2) :
    xi = 0 := by
  obtain ⟨x, ⟨e⟩⟩ :=
    S.exists_factorOppositeAuslanderSimple_linearEquiv H K (M := M)
  let eIso := e.toModuleIso
  let eta := (Ext.mk₀ eIso.hom).comp xi (zero_add 2)
  have heta : eta = 0 :=
    S.factorOppositeAuslanderSimple_ext_two_corepresentable_eq_zero
      D p x hp eta
  rw [← Ext.mk₀_id_comp xi, ← eIso.inv_hom_id,
    ← Ext.mk₀_comp_mk₀_assoc]
  change (Ext.mk₀ eIso.inv).comp eta (zero_add 2) = 0
  rw [heta]
  exact Ext.comp_zero _ _ _ _ _

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem finiteLengthModule_ext_two_corepresentable_eq_zero
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.SurvivingLabel K)
    (hp : (S.factorFiniteTauCategoryData K).IsProjective p)
    {M : Type u} [AddCommGroup M]
    [Module (S.factorOppositeAuslanderRing K) M]
    (hM : IsFiniteLength (S.factorOppositeAuslanderRing K) M)
    (xi : Ext.{u}
      (ModuleCat.of (S.factorOppositeAuslanderRing K) M)
      (ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorObject K p ⟶ S.factorAdditiveGenerator K)) 2) :
    xi = 0 := by
  induction hM with
  | @of_subsingleton M _ _ hsub =>
      letI : Subsingleton M := hsub
      let X := ModuleCat.of (S.factorOppositeAuslanderRing K) M
      have hzero : IsZero X :=
        ModuleCat.isZero_iff_subsingleton.mpr (by
          change Subsingleton M
          infer_instance)
      rw [← Ext.mk₀_id_comp xi]
      have hid : 𝟙 X = 0 := hzero.eq_of_src _ _
      rw [hid, Ext.mk₀_zero]
      exact Ext.zero_comp _ _ _ _ _
  | @of_simple_quotient M _ _ N _ hN ih =>
      let C : ShortComplex
          (ModuleCat.{u} (S.factorOppositeAuslanderRing K)) :=
        ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by
          ext y
          simp)
      have hC : C.ShortExact := by
        apply ModuleCat.shortComplex_shortExact
        · exact LinearMap.exact_subtype_mkQ N
        · exact N.injective_subtype
        · exact N.mkQ_surjective
      let Q := ModuleCat.of (S.factorOppositeAuslanderRing K)
        (S.factorObject K p ⟶ S.factorAdditiveGenerator K)
      have hrestrict :
          (Ext.mk₀ C.f).comp xi (zero_add 2) = 0 := by
        apply ih
      obtain ⟨eta, heta⟩ :=
        Ext.contravariant_sequence_exact₂ hC Q xi hrestrict
      have hetaZero : eta = 0 := by
        apply S.simpleModule_ext_two_corepresentable_eq_zero D H p hp
      rw [← heta, hetaZero]
      exact Ext.comp_zero _ _ _ _ _

def factorCorepresentableFGObj
    (K : Set (Fin S.n)) (X : S.FactorCategory K) :
    FGModuleCat.{u} (S.factorOppositeAuslanderRing K) := by
  letI : Module.Finite (S.factorOppositeAuslanderRing K)
      (X ⟶ S.factorAdditiveGenerator K) :=
    (S.factorCorepresentable_finiteProjective K X).1
  exact FGModuleCat.of (S.factorOppositeAuslanderRing K)
    (X ⟶ S.factorAdditiveGenerator K)

noncomputable local instance factorOppositeAuslanderFGModuleHasExt
    (K : Set (Fin S.n)) :
    HasExt.{u} (FGModuleCat.{u} (S.factorOppositeAuslanderRing K)) := by
  letI : EnoughProjectives
      (FGModuleCat.{u} (S.factorOppositeAuslanderRing K)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (S.factorOppositeAuslanderRing K)
  exact CategoryTheory.hasExt_of_enoughProjectives _

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem fgModule_ext_two_corepresentable_eq_zero
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.SurvivingLabel K)
    (hp : (S.factorFiniteTauCategoryData K).IsProjective p)
    (Y : FGModuleCat.{u} (S.factorOppositeAuslanderRing K))
    (xi : Ext.{u} Y
      (S.factorCorepresentableFGObj K (S.factorObject K p)) 2) :
    xi = 0 := by
  let R := S.factorOppositeAuslanderRing K
  letI : Module.Finite k R :=
    S.factorCategoryHomFinite K
      (S.factorAdditiveGenerator K) (S.factorAdditiveGenerator K)
  letI : IsNoetherianRing R := IsNoetherianRing.of_finite k R
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  letI : EnoughProjectives (FGModuleCat.{u} R) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives R
  let F := MagnitudeConjecture.FGExtRealization.inclusion (R := R)
  apply (F.mapExt_bijective_of_preservesProjectiveObjects Y
    (S.factorCorepresentableFGObj K (S.factorObject K p)) 2).injective
  have hfinite : IsFiniteLength R Y :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨inferInstance, inferInstance⟩
  rw [map_zero]
  apply S.finiteLengthModule_ext_two_corepresentable_eq_zero
    D H p hp hfinite

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem factorCorepresentable_hasInjectiveDimensionLE_one
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.SurvivingLabel K)
    (hp : (S.factorFiniteTauCategoryData K).IsProjective p) :
    HasInjectiveDimensionLE
      (S.factorCorepresentableFGObj K (S.factorObject K p)) 1 := by
  let R := S.factorOppositeAuslanderRing K
  letI : EnoughProjectives (FGModuleCat.{u} R) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives R
  apply hasInjectiveDimensionLT_of_enoughProjectives
    (S.factorCorepresentableFGObj K (S.factorObject K p)) 2
  intro Y
  exact ⟨fun a b ↦ by
    rw [S.fgModule_ext_two_corepresentable_eq_zero D H p hp Y a,
      S.fgModule_ext_two_corepresentable_eq_zero D H p hp Y b]⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem dualFactorCorepresentable_hasProjectiveDimensionLE_one
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.SurvivingLabel K)
    (hp : (S.factorFiniteTauCategoryData K).IsProjective p) :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        ((Contragredient.dualFunctor k
          (S.factorOppositeAuslanderRing K)).obj
            (Opposite.op
              (S.factorCorepresentableFGObj K
                (S.factorObject K p))))) 1 := by
  let R := S.factorOppositeAuslanderRing K
  letI : Module.Finite k R :=
    S.factorCategoryHomFinite K
      (S.factorAdditiveGenerator K) (S.factorAdditiveGenerator K)
  letI : Module.Finite k Rᵐᵒᵖ := inferInstance
  letI : IsNoetherianRing Rᵐᵒᵖ := IsNoetherianRing.of_finite k Rᵐᵒᵖ
  letI : EnoughProjectives (FGModuleCat.{u} R) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives R
  letI : EnoughInjectives (FGModuleCat.{u} R) :=
    MagnitudeConjecture.fgModuleCat_enoughInjectives k R
  let Q := S.factorCorepresentableFGObj K (S.factorObject K p)
  letI : HasInjectiveDimensionLT Q 2 :=
    S.factorCorepresentable_hasInjectiveDimensionLE_one D H p hp
  let P := (EnoughInjectives.presentation Q).some
  let C : ShortComplex (FGModuleCat.{u} R) :=
    ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)
  have hC : C.ShortExact :=
    { exact := ShortComplex.exact_cokernel P.f }
  have hCokerDim : HasInjectiveDimensionLT C.X₃ 1 :=
    (hC.hasInjectiveDimensionLT_X₃_iff 0 P.injective).2
      (show HasInjectiveDimensionLT C.X₁ 2 from inferInstance)
  letI : Injective C.X₃ :=
    injective_iff_hasInjectiveDimensionLT_one.mpr hCokerDim
  let E := Contragredient.dualityEquivalence k R
  let Cop := C.op
  let T := Cop.map E.functor
  have hT : T.ShortExact := by
    exact hC.op.map_of_exact E.functor
  have hCop₁ : Projective Cop.X₁ := by
    change Projective (Opposite.op C.X₃)
    exact Injective.injective_iff_projective_op.mp inferInstance
  have hCop₂ : Projective Cop.X₂ := by
    change Projective (Opposite.op C.X₂)
    exact Injective.injective_iff_projective_op.mp P.injective
  letI : Projective T.X₁ := (E.map_projective_iff Cop.X₁).2 hCop₁
  letI : Projective T.X₂ := (E.map_projective_iff Cop.X₂).2 hCop₂
  let U := MagnitudeConjecture.FGExtRealization.inclusion (R := Rᵐᵒᵖ)
  let V := T.map U
  have hV : V.ShortExact := hT.map_of_exact U
  letI : Projective V.X₁ := by
    change Projective (U.obj T.X₁)
    exact U.projective_obj_of_projective inferInstance
  letI : Projective V.X₂ := by
    change Projective (U.obj T.X₂)
    exact U.projective_obj_of_projective inferInstance
  exact hV.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem factorAuslanderRepresentableNakayama_hasProjectiveDimensionLE_one
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (p : S.SurvivingLabel K)
    (hp : (S.factorFiniteTauCategoryData K).IsProjective p) :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        (RightModule.projectiveNakayamaFGObj (k := k)
          (S.factorAuslanderRepresentableFGObj K
            (S.factorObject K p)))) 1 := by
  let R := S.factorOppositeAuslanderRing K
  letI : Module.Finite k R :=
    S.factorCategoryHomFinite K
      (S.factorAdditiveGenerator K) (S.factorAdditiveGenerator K)
  letI : Module.Finite k Rᵐᵒᵖ := inferInstance
  letI : Module.Finite R
      (S.factorObject K p ⟶ S.factorAdditiveGenerator K) :=
    (S.factorCorepresentable_finiteProjective K
      (S.factorObject K p)).1
  let Q := S.factorCorepresentableFGObj K (S.factorObject K p)
  let P := S.factorAuslanderRepresentableFGObj K (S.factorObject K p)
  let Qregular := RightModule.regularHomDualFGObj (k := k) P
  letI : Module.Finite R (RightModule.regularHomDualCarrier P) :=
    Qregular.property
  let e : Q ≅ Qregular :=
    (S.factorCorepresentableRegularHomDualLinearEquiv K
      (S.factorObject K p)).toFGModuleCatIso
  let E := Contragredient.dualityEquivalence k R
  let eDual : E.functor.obj (Opposite.op Q) ≅
      E.functor.obj (Opposite.op Qregular) :=
    E.functor.mapIso e.symm.op
  let U := MagnitudeConjecture.FGExtRealization.inclusion (R := Rᵐᵒᵖ)
  have hsource : HasProjectiveDimensionLT
      (ModuleCat.of Rᵐᵒᵖ
        (E.functor.obj (Opposite.op Q))) 2 :=
    S.dualFactorCorepresentable_hasProjectiveDimensionLE_one D H p hp
  letI : HasProjectiveDimensionLT
      (U.obj (E.functor.obj (Opposite.op Q))) 2 := hsource
  exact hasProjectiveDimensionLT_of_iso (U.mapIso eDual) 2

def factorRepresentableFGFunctor (K : Set (Fin S.n)) :
    S.FactorCategory K ⥤ FGModuleCat.{u} (S.factorAuslanderRing K) where
  obj X := S.factorAuslanderRepresentableFGObj K X
  map f := FGModuleCat.ofHom
    ((preadditiveCoyonedaObj (S.factorAdditiveGenerator K)).map f).hom
  map_id X := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change h ≫ 𝟙 X = h
    exact Category.comp_id h
  map_comp f g := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change h ≫ (f ≫ g) = (h ≫ f) ≫ g
    exact (Category.assoc _ _ _).symm

omit [IsAlgClosed k] in
instance factorRepresentableFGFunctor_additive (K : Set (Fin S.n)) :
    (S.factorRepresentableFGFunctor K).Additive where
  map_add := by
    intro X Y f g
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change h ≫ (f + g) = h ≫ f + h ≫ g
    rw [Preadditive.comp_add]

def factorProjectiveNakayamaFunctor (K : Set (Fin S.n)) :
    FGModuleCat.{u} (S.factorAuslanderRing K) ⥤
      FGModuleCat.{u} (S.factorAuslanderRing K) where
  obj P := RightModule.projectiveNakayamaFGObj (k := k) P
  map f := RightModule.projectiveNakayamaMap (k := k) f
  map_id P := RightModule.projectiveNakayamaMap_id (k := k) P
  map_comp f g := RightModule.projectiveNakayamaMap_comp (k := k) f g

instance factorProjectiveNakayamaFunctor_additive
    (K : Set (Fin S.n)) :
    (S.factorProjectiveNakayamaFunctor K).Additive where
  map_add := by
    intro P Q f g
    exact RightModule.projectiveNakayamaMap_add (k := k) f g

noncomputable local instance factorProjectiveLabelFintype
    (K : Set (Fin S.n)) : Fintype (S.FactorProjectiveLabel K) :=
  Fintype.ofFinite _

omit [IsAlgClosed k] in
def factorBoundaryRepresentableBiproductIso
    (K : Set (Fin S.n)) :
    S.factorBoundaryRepresentableFGObj K ≅
      ⨁ fun p : S.FactorProjectiveLabel K ↦
        S.factorAuslanderRepresentableFGObj K
          (S.factorObject K p.1) := by
  let F : S.FactorProjectiveLabel K → S.FactorCategory K :=
    fun p ↦ S.factorObject K p.1
  exact (S.factorRepresentableFGFunctor K).mapBiproduct F

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem factorBoundaryNakayama_hasProjectiveDimensionLE_one
    {K : Set (Fin S.n)} (D : S.PrimitiveFactorInput K)
    (H : S.HasAcyclicNonzeroNonisomorphisms) :
    HasProjectiveDimensionLE
      (ModuleCat.of (S.factorAuslanderRing K)
        (RightModule.projectiveNakayamaFGObj (k := k)
          (S.factorBoundaryRepresentableFGObj K))) 1 := by
  let R := S.factorAuslanderRing K
  let P : S.FactorProjectiveLabel K → FGModuleCat.{u} R :=
    fun p ↦ S.factorAuslanderRepresentableFGObj K
      (S.factorObject K p.1)
  let N := S.factorProjectiveNakayamaFunctor K
  let eN : N.obj (S.factorBoundaryRepresentableFGObj K) ≅
      ⨁ fun p : S.FactorProjectiveLabel K ↦ N.obj (P p) :=
    N.mapIso (S.factorBoundaryRepresentableBiproductIso K) ≪≫
      N.mapBiproduct P
  let U := MagnitudeConjecture.FGExtRealization.inclusion (R := R)
  let eAmbient :
      U.obj (N.obj (S.factorBoundaryRepresentableFGObj K)) ≅
        ⨁ fun p : S.FactorProjectiveLabel K ↦ U.obj (N.obj (P p)) :=
    U.mapIso eN ≪≫ U.mapBiproduct (fun p ↦ N.obj (P p))
  have hcomponent (p : S.FactorProjectiveLabel K) :
      HasProjectiveDimensionLT (U.obj (N.obj (P p))) 2 := by
    exact S.factorAuslanderRepresentableNakayama_hasProjectiveDimensionLE_one
      D H p.1 p.2
  letI : HasProjectiveDimensionLT
      (⨁ fun p : S.FactorProjectiveLabel K ↦ U.obj (N.obj (P p))) 2 :=
    MagnitudeConjecture.CategoryTheory.hasProjectiveDimensionLT_biproduct
      (fun p : S.FactorProjectiveLabel K ↦ U.obj (N.obj (P p))) 2
      hcomponent
  exact hasProjectiveDimensionLT_of_iso eAmbient.symm 2

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
