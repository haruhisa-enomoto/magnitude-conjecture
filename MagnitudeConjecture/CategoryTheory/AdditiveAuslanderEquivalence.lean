import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import MagnitudeConjecture.CategoryTheory.FiniteGeneratorRadicalNilpotence

/-!
# The additive-generator Auslander equivalence

For an object `G` in an idempotent-complete additive category, the
representable functor `Hom(G,-)` identifies `add(G)` with the additive retract
closure of the regular representable module `Hom(G,G)`.

This is the exact generic foundation needed for Iyama's minimal realization
in the magnitude campaign.  It is a bounded adaptation of the corresponding
core in the clean equidistribution formalization; no OP-conjecture module or
classification layer is imported.
-/

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace MagnitudeConjecture.CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- The object property `add(G)`. -/
def finiteAddClosure (G : C) : ObjectProperty C :=
  fun X ↦ Nonempty (FiniteAddPresentation G X)

/-- A finite additive generator has top additive closure. -/
theorem finiteAddClosure_eq_top
    (G : C) (hG : IsFiniteAddGenerator G) :
    finiteAddClosure G = ⊤ := by
  funext X
  apply propext
  exact ⟨fun _ ↦ trivial, fun _ ↦ hG X⟩

/-- Replace the generator in a finite additive presentation by an isomorphic
one. -/
def FiniteAddPresentation.replaceGenerator
    {G H X : C} (e : G ≅ H)
    (P : FiniteAddPresentation G X) :
    FiniteAddPresentation H X where
  n := P.n
  retract :=
    P.retract.trans
      (Retract.ofIso (biproduct.mapIso fun _ : Fin P.n ↦ e))

/-- The additive closure is invariant under isomorphic generators. -/
theorem finiteAddClosure_iff_of_iso
    {G H X : C} (e : G ≅ H) :
    finiteAddClosure G X ↔ finiteAddClosure H X :=
  ⟨fun ⟨P⟩ ↦ ⟨P.replaceGenerator e⟩,
    fun ⟨P⟩ ↦ ⟨P.replaceGenerator e.symm⟩⟩

/-- Binary biproducts of objects in `add(G)` remain in `add(G)`. -/
def FiniteAddPresentation.biprod
    [HasBinaryBiproducts C]
    {G X Y : C} (P : FiniteAddPresentation G X)
    (Q : FiniteAddPresentation G Y) :
    FiniteAddPresentation G (X ⊞ Y) := by
  classical
  let F : Fin P.n → C := fun _ ↦ G
  let H : Fin Q.n → C := fun _ ↦ G
  let K : Fin (P.n + Q.n) → C := fun _ ↦ G
  let inclusion : (X ⊞ Y) ⟶ ⨁ K :=
    biprod.desc
      (biproduct.lift (Fin.addCases
        (fun i ↦ P.retract.i ≫ biproduct.π F i)
        (fun _ ↦ 0)))
      (biproduct.lift (Fin.addCases
        (fun _ ↦ 0)
        (fun j ↦ Q.retract.i ≫ biproduct.π H j)))
  let projection : (⨁ K) ⟶ (X ⊞ Y) :=
    biprod.lift
      (biproduct.desc (Fin.addCases
        (fun i ↦ biproduct.ι F i ≫ P.retract.r)
        (fun _ ↦ 0)))
      (biproduct.desc (Fin.addCases
        (fun _ ↦ 0)
        (fun j ↦ biproduct.ι H j ≫ Q.retract.r)))
  exact
    { n := P.n + Q.n
      retract :=
        { i := inclusion
          r := projection
          retract := by
            apply biprod.hom_ext
            all_goals apply biprod.hom_ext'
            all_goals
              dsimp only [inclusion, projection]
              simp only [Category.assoc, biprod.lift_fst,
                biprod.lift_snd, biprod.inl_desc_assoc,
                biprod.inr_desc_assoc, biproduct.lift_desc,
                Fin.sum_univ_add, Fin.addCases_left,
                Fin.addCases_right, comp_zero, zero_comp,
                Finset.sum_const_zero, Category.id_comp,
                biprod.inl_fst,
                biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
                add_zero, zero_add]
            · calc
                _ = P.retract.i ≫
                    (∑ i, biproduct.π F i ≫ biproduct.ι F i) ≫
                      P.retract.r := by
                  simp only [Preadditive.comp_sum,
                    Preadditive.sum_comp, Category.assoc]
                _ = 𝟙 X := by
                  rw [biproduct.total]
                  simpa only [F, Category.comp_id, Category.id_comp]
                    using P.retract.retract
            · calc
                _ = Q.retract.i ≫
                    (∑ j, biproduct.π H j ≫ biproduct.ι H j) ≫
                      Q.retract.r := by
                  simp only [Preadditive.comp_sum,
                    Preadditive.sum_comp, Category.assoc]
                _ = 𝟙 Y := by
                  rw [biproduct.total]
                  simpa only [H, Category.comp_id, Category.id_comp]
                    using Q.retract.retract } }

/-- Object-property form of closure of `add(G)` under binary biproducts. -/
theorem finiteAddClosure_biprod
    [HasBinaryBiproducts C]
    {G X Y : C} (hX : finiteAddClosure G X)
    (hY : finiteAddClosure G Y) :
    finiteAddClosure G (X ⊞ Y) :=
  ⟨hX.some.biprod hY.some⟩

/-- The representable module functor on `add(G)`.  Mathlib uses left module
categories, so the scalar ring is `(End G)ᵐᵒᵖ`. -/
def homFromGenerator (G : C) :
    (finiteAddClosure G).FullSubcategory ⥤
      ModuleCat.{v} (End G)ᵐᵒᵖ :=
  (finiteAddClosure G).ι ⋙ preadditiveCoyonedaObj G

omit [HasFiniteBiproducts C] in
private theorem linear_map_comp
    {G X Y : C}
    (α :
      ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ X) ⟶
        ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ Y))
    (e : End G) (k : G ⟶ X) :
    α.hom (e ≫ k) = e ≫ α.hom k := by
  change α.hom (MulOpposite.op e • k) =
    MulOpposite.op e • α.hom k
  exact α.hom.map_smul (MulOpposite.op e) k

/-- A module map out of a representable object coming from `add(G)` is
represented by a categorical morphism, even when the target object need not
belong to `add(G)`. -/
theorem exists_hom_of_moduleHom_of_finiteAddSource
    (G : C) {X Y : C} (P : FiniteAddPresentation G X)
    (α :
      ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ X) ⟶
        ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ Y)) :
    ∃ f : X ⟶ Y, (preadditiveCoyonedaObj G).map f = α := by
    change
      ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ X) ⟶
        ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ Y) at α
    let q : (⨁ fun _ : Fin P.n ↦ G) ⟶ Y :=
      biproduct.desc fun j ↦
        α.hom (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫ P.retract.r)
    let f : X ⟶ Y := P.retract.i ≫ q
    refine ⟨f, ?_⟩
    apply ModuleCat.hom_ext
    ext h
    let h' : G ⟶ X := h
    change h' ≫ f = α.hom h'
    dsimp only [f, q]
    rw [← Category.assoc, biproduct.desc_eq,
      Preadditive.comp_sum]
    simp_rw [← Category.assoc]
    simp_rw [← linear_map_comp α]
    rw [← map_sum]
    congr 1
    have ht :=
      congrArg
        (fun t ↦ h' ≫ P.retract.i ≫ t ≫ P.retract.r)
        (biproduct.total (f := fun _ : Fin P.n ↦ G))
    calc
      _ = h' ≫ P.retract.i ≫
          𝟙 (⨁ fun _ : Fin P.n ↦ G) ≫ P.retract.r := by
        simpa only [Preadditive.comp_sum,
          Preadditive.sum_comp, Category.assoc]
          using ht
      _ = h' := by simp

/-- `Hom(G,-)` is full on `add(G)`. -/
instance homFromGenerator_full (G : C) :
    (homFromGenerator G).Full where
  map_surjective {X Y} α := by
    obtain ⟨f, hf⟩ :=
      exists_hom_of_moduleHom_of_finiteAddSource
        G X.property.some α
    exact ⟨ObjectProperty.homMk f, hf⟩

/-- `Hom(G,-)` is faithful on `add(G)`. -/
instance homFromGenerator_faithful (G : C) :
    (homFromGenerator G).Faithful where
  map_injective {X Y} f g hfg := by
    change
      (preadditiveCoyonedaObj G).map f.hom =
        (preadditiveCoyonedaObj G).map g.hom at hfg
    let P := X.property.some
    apply ObjectProperty.hom_ext
    apply (cancel_epi P.retract.r).1
    apply biproduct.hom_ext'
    intro j
    have h :=
      congrArg
        (fun k ↦
          k.hom
            (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫
              P.retract.r))
        hfg
    dsimp [preadditiveCoyonedaObj] at h
    convert h using 1 <;>
      exact (Category.assoc _ _ _).symm

/-- Bundled full faithfulness of the representable functor on `add(G)`. -/
def homFromGeneratorFullyFaithful (G : C) :
    (homFromGenerator G).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (homFromGenerator G)

/-- The regular left `(End G)ᵐᵒᵖ`-module is the self-representable module
`Hom(G,G)`. -/
def regularLinearEquiv (G : C) :
    (End G)ᵐᵒᵖ ≃ₗ[(End G)ᵐᵒᵖ] (G ⟶ G) where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

omit [HasFiniteBiproducts C] in
/-- The self-representable module is projective over the opposite
endomorphism ring. -/
theorem homSelf_projective (G : C) :
    Projective ((preadditiveCoyonedaObj G).obj G) := by
  let R := (End G)ᵐᵒᵖ
  have hregular : Projective (ModuleCat.of R R) :=
    ModuleCat.projective_of_free (Module.Basis.singleton Unit R)
  exact Projective.of_iso
    (regularLinearEquiv G).toModuleIso hregular

/-- Every represented object from `add(G)` lies in the additive closure of
the regular representable module. -/
def homFromGenerator_obj_finiteAddPresentation
    (G : C) (X : (finiteAddClosure G).FullSubcategory) :
    FiniteAddPresentation
      ((preadditiveCoyonedaObj G).obj G)
      ((homFromGenerator G).obj X) := by
  let P := X.property.some
  let F := preadditiveCoyonedaObj G
  exact
    { n := P.n
      retract :=
        (P.retract.map F).trans
          (Retract.ofIso
            (F.mapBiproduct (fun _ : Fin P.n ↦ G))) }

/-- `Hom(G,-)` with its target restricted to the additive closure of the
regular representable module. -/
def homFromGeneratorToAdd (G : C) :
    (finiteAddClosure G).FullSubcategory ⥤
      (finiteAddClosure
        ((preadditiveCoyonedaObj G).obj G)).FullSubcategory :=
  (finiteAddClosure
    ((preadditiveCoyonedaObj G).obj G)).lift
      (homFromGenerator G)
      (fun X ↦ ⟨homFromGenerator_obj_finiteAddPresentation G X⟩)

/-- The target-restricted representable functor is fully faithful. -/
def homFromGeneratorToAddFullyFaithful (G : C) :
    (homFromGeneratorToAdd G).FullyFaithful := by
  unfold homFromGeneratorToAdd
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- Idempotent completeness makes the target-restricted representable
functor essentially surjective. -/
theorem homFromGeneratorToAdd_essSurj
    [IsIdempotentComplete C] (G : C) :
    (homFromGeneratorToAdd G).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  let Q := Y.property.some
  let F := preadditiveCoyonedaObj G
  let A : C := ⨁ fun _ : Fin Q.n ↦ G
  let φ :
      F.obj A ≅ ⨁ fun _ : Fin Q.n ↦ F.obj G :=
    F.mapBiproduct (fun _ : Fin Q.n ↦ G)
  let r : Retract Y.obj (F.obj A) :=
    Q.retract.trans (Retract.ofIso φ.symm)
  let A' : (finiteAddClosure G).FullSubcategory :=
    ⟨A, ⟨{
      n := Q.n
      retract := Retract.refl A }⟩⟩
  let p : F.obj A ⟶ F.obj A := r.r ≫ r.i
  have hp : p ≫ p = p := by
    dsimp only [p]
    simp [Category.assoc]
  let FF := homFromGeneratorFullyFaithful G
  let p' :
      (homFromGenerator G).obj A' ⟶
        (homFromGenerator G).obj A' :=
    p
  let a : A' ⟶ A' := FF.preimage p'
  have hmapa : (homFromGenerator G).map a = p' :=
    FF.map_preimage p'
  have ha : a ≫ a = a := by
    apply (homFromGenerator G).map_injective
    rw [Functor.map_comp, hmapa]
    change p ≫ p = p
    exact hp
  have ha0 : a.hom ≫ a.hom = a.hom :=
    congrArg (fun k ↦ k.hom) ha
  rcases IsIdempotentComplete.idempotents_split A a.hom ha0 with
    ⟨Z, i, e, hie, hei⟩
  let X : (finiteAddClosure G).FullSubcategory :=
    ⟨Z, ⟨{
      n := Q.n
      retract :=
        { i := i
          r := e
          retract := hie } }⟩⟩
  have hmapa0 : F.map a.hom = p := by
    change F.map a.hom = p at hmapa
    exact hmapa
  let isoAmbient : F.obj Z ≅ Y.obj :=
    { hom := F.map i ≫ r.r
      inv := r.i ≫ F.map e
      hom_inv_id := by
        calc
          (F.map i ≫ r.r) ≫ (r.i ≫ F.map e) =
              F.map i ≫ (r.r ≫ r.i) ≫ F.map e := by
            simp only [Category.assoc]
          _ = F.map i ≫ F.map a.hom ≫ F.map e := by
            dsimp only [p] at hmapa0
            rw [hmapa0]
          _ = 𝟙 _ := by
            rw [← F.map_comp, ← F.map_comp, ← hei]
            simp [Category.assoc, hie]
      inv_hom_id := by
        calc
          (r.i ≫ F.map e) ≫ (F.map i ≫ r.r) =
              r.i ≫ F.map (e ≫ i) ≫ r.r := by
            simp only [Category.assoc, F.map_comp]
          _ = r.i ≫ F.map a.hom ≫ r.r := by rw [hei]
          _ = r.i ≫ (r.r ≫ r.i) ≫ r.r := by
            dsimp only [p] at hmapa0
            rw [hmapa0]
          _ = 𝟙 _ := by simp [Category.assoc] }
  exact ⟨X, ⟨ObjectProperty.isoMk _ isoAmbient⟩⟩

/-- The additive Auslander equivalence. -/
def additiveAuslanderEquivalence
    [IsIdempotentComplete C] (G : C) :
    (finiteAddClosure G).FullSubcategory ≌
      (finiteAddClosure
        ((preadditiveCoyonedaObj G).obj G)).FullSubcategory := by
  letI : (homFromGeneratorToAdd G).IsEquivalence :=
    Functor.IsEquivalence.mk
      (homFromGeneratorToAddFullyFaithful G).faithful
      (homFromGeneratorToAddFullyFaithful G).full
      (homFromGeneratorToAdd_essSurj G)
  exact (homFromGeneratorToAdd G).asEquivalence

/-- The object property of finitely generated projective modules. -/
def finiteProjectiveModules
    (R : Type v) [Ring R] :
    ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.Finite R M ∧ Projective M

/-- A module is a retract of a finite power of the regular module exactly
when it is finitely generated and projective. -/
theorem finiteAddClosure_regular_iff
    (R : Type v) [Ring R] (M : ModuleCat.{v} R) :
    finiteAddClosure (ModuleCat.of R R) M ↔
      finiteProjectiveModules R M := by
  constructor
  · rintro ⟨P⟩
    have hBfinite :
        Module.Finite R
          (⨁ fun _ : Fin P.n ↦ ModuleCat.of R R :
            ModuleCat.{v} R) := by
      have hPi : Module.Finite R (∀ _ : Fin P.n, R) :=
        inferInstance
      exact
        (Module.Finite.equiv_iff
          (ModuleCat.biproductIsoPi
            (fun _ : Fin P.n ↦ ModuleCat.of R R)).toLinearEquiv).mpr hPi
    have hMfinite : Module.Finite R M := by
      letI :
          Module.Finite R
            (⨁ fun _ : Fin P.n ↦ ModuleCat.of R R :
              ModuleCat.{v} R) :=
        hBfinite
      exact
        Module.Finite.of_surjective P.retract.r.hom
          (fun x ↦
            ⟨P.retract.i.hom x, by
              change (P.retract.i ≫ P.retract.r).hom x = x
              rw [P.retract.retract]
              rfl⟩)
    have hRegularProjective : Projective (ModuleCat.of R R) :=
      ModuleCat.projective_of_free (Module.Basis.singleton Unit R)
    have hBprojective :
        Projective
          (⨁ fun _ : Fin P.n ↦ ModuleCat.of R R :
            ModuleCat.{v} R) := by
      classical
      refine ⟨fun {E Y} f e _ ↦ ?_⟩
      choose lift hlift using
        fun j ↦
          hRegularProjective.factors
            (biproduct.ι
              (fun _ : Fin P.n ↦ ModuleCat.of R R) j ≫ f) e
      refine ⟨biproduct.desc lift, ?_⟩
      apply biproduct.hom_ext'
      intro j
      simpa only [biproduct.ι_desc_assoc] using hlift j
    letI :
        Projective
          (⨁ fun _ : Fin P.n ↦ ModuleCat.of R R :
            ModuleCat.{v} R) :=
      hBprojective
    exact ⟨hMfinite, P.retract.projective⟩
  · rintro ⟨hMfinite, hMprojective⟩
    letI : Module.Finite R M := hMfinite
    letI : Projective M := hMprojective
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
    let e : ModuleCat.of R (Fin n → R) ⟶ M := ModuleCat.ofHom p
    haveI : Epi e := (ModuleCat.epi_iff_surjective e).mpr hp
    obtain ⟨i, hi⟩ := Projective.factors (𝟙 M) e
    let rFree : Retract M (ModuleCat.of R (Fin n → R)) :=
      { i := i
        r := e
        retract := hi }
    let φ :
        (⨁ fun _ : Fin n ↦ ModuleCat.of R R : ModuleCat.{v} R) ≅
          ModuleCat.of R (Fin n → R) :=
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ ModuleCat.of R R)
    exact
      ⟨{
        n := n
        retract := rFree.trans (Retract.ofIso φ.symm) }⟩

/-- The additive closure of the regular module is the finitely generated
projective locus. -/
theorem finiteAddClosure_regular_eq_finiteProjective
    (R : Type v) [Ring R] :
    finiteAddClosure (ModuleCat.of R R) =
      finiteProjectiveModules R := by
  funext M
  exact propext (finiteAddClosure_regular_iff R M)

omit [HasFiniteBiproducts C] in
/-- The additive closure of `Hom(G,G)` is the finitely generated projective
module locus over `(End G)ᵐᵒᵖ`. -/
theorem finiteAddClosure_homSelf_eq_finiteProjective
    (G : C) :
    finiteAddClosure
        ((preadditiveCoyonedaObj G).obj G) =
      finiteProjectiveModules (End G)ᵐᵒᵖ := by
  funext M
  apply propext
  exact
    (finiteAddClosure_iff_of_iso
      ((regularLinearEquiv G).toModuleIso.symm :
        (preadditiveCoyonedaObj G).obj G ≅
          ModuleCat.of (End G)ᵐᵒᵖ (End G)ᵐᵒᵖ)).trans
      (finiteAddClosure_regular_iff (End G)ᵐᵒᵖ M)

/-- A finitely generated projective module over the opposite endomorphism
ring is represented by an object of `add(G)`. -/
theorem exists_obj_homSelf_iso_of_finite_projective
    [IsIdempotentComplete C] (G : C)
    (M : ModuleCat.{v} (End G)ᵐᵒᵖ)
    (hM : finiteProjectiveModules (End G)ᵐᵒᵖ M) :
    ∃ X : C, finiteAddClosure G X ∧
      Nonempty ((preadditiveCoyonedaObj G).obj X ≅ M) := by
  have hMadd :
      finiteAddClosure ((preadditiveCoyonedaObj G).obj G) M := by
    rw [finiteAddClosure_homSelf_eq_finiteProjective G]
    exact hM
  let M' :
      (finiteAddClosure
        ((preadditiveCoyonedaObj G).obj G)).FullSubcategory :=
    ⟨M, hMadd⟩
  obtain ⟨X, ⟨e⟩⟩ := (homFromGeneratorToAdd_essSurj G).mem_essImage M'
  exact
    ⟨X.obj, X.property,
      ⟨(ObjectProperty.ι
        (finiteAddClosure
          ((preadditiveCoyonedaObj G).obj G))).mapIso e⟩⟩

/-- The additive Auslander equivalence with the conventional finitely
generated projective target. -/
def auslanderEquivalence
    [IsIdempotentComplete C] (G : C) :
    (finiteAddClosure G).FullSubcategory ≌
      (finiteProjectiveModules (End G)ᵐᵒᵖ).FullSubcategory :=
  (additiveAuslanderEquivalence G).trans
    (ObjectProperty.fullSubcategoryCongr
      (finiteAddClosure_homSelf_eq_finiteProjective G))

/-- If `G` generates the whole category, the source of the additive
Auslander equivalence can be written as the ambient category. -/
def finiteAddGeneratorAuslanderEquivalence
    [IsIdempotentComplete C]
    (G : C) (hG : IsFiniteAddGenerator G) :
    C ≌
      (finiteProjectiveModules (End G)ᵐᵒᵖ).FullSubcategory :=
  (ObjectProperty.topEquivalence C).symm |>.trans
    (ObjectProperty.fullSubcategoryCongr
      (finiteAddClosure_eq_top G hG).symm) |>.trans
    (auslanderEquivalence G)

end MagnitudeConjecture.CategoryTheory
