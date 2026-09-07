import MagnitudeConjecture.CategoryTheory.AdditiveAuslanderEquivalence
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Morita.Basic

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.CategoryTheory

universe u

variable {R : Type u} [Ring R]

/-- If the regular module belongs to the finite additive closure of `G`, then
the all-module restricted Yoneda functor represented by `G` is faithful. -/
theorem preadditiveCoyonedaObj_faithful_of_regular_finiteAddClosure
    (G : ModuleCat.{u} R)
    (hregular : finiteAddClosure G (ModuleCat.of R R)) :
    (preadditiveCoyonedaObj G).Faithful := by
  constructor
  intro X Y f g hfg
  apply ModuleCat.hom_ext
  ext x
  let P := hregular.some
  let hx : ModuleCat.of R R ⟶ X :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R X x)
  have heq : hx ≫ f = hx ≫ g := by
    apply (cancel_epi P.retract.r).1
    apply biproduct.hom_ext'
    intro j
    have h := congrArg
      (fun q ↦ q.hom
        (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫ P.retract.r ≫ hx))
      hfg
    change
      (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫ P.retract.r ≫ hx) ≫ f =
        (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫ P.retract.r ≫ hx) ≫ g at h
    simpa only [Category.assoc] using h
  have h := congrArg (fun q ↦ q.hom 1) heq
  simpa [hx, LinearMap.toSpanSingleton_apply_one] using h

private theorem moduleHom_comp
    (G : ModuleCat.{u} R) {X Y : ModuleCat.{u} R}
    (α : (preadditiveCoyonedaObj G).obj X ⟶
      (preadditiveCoyonedaObj G).obj Y)
    (e : End G) (f : G ⟶ X) :
    α.hom (e ≫ f) = e ≫ α.hom f := by
  change α.hom (MulOpposite.op e • f) =
    MulOpposite.op e • α.hom f
  exact α.hom.map_smul (MulOpposite.op e) f

/-- If the regular module belongs to the finite additive closure of `G`, then
the all-module restricted Yoneda functor represented by `G` is full. -/
theorem preadditiveCoyonedaObj_full_of_regular_finiteAddClosure
    (G : ModuleCat.{u} R)
    (hregular : finiteAddClosure G (ModuleCat.of R R)) :
    (preadditiveCoyonedaObj G).Full := by
  let F := preadditiveCoyonedaObj G
  letI : F.Faithful :=
    preadditiveCoyonedaObj_faithful_of_regular_finiteAddClosure G hregular
  constructor
  intro X Y α
  let P := hregular.some
  let point (x : X) : ModuleCat.of R R ⟶ X :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R X x)
  let qExists (x : X) : ∃ q : ModuleCat.of R R ⟶ Y,
      F.map q = F.map (point x) ≫ α :=
    exists_hom_of_moduleHom_of_finiteAddSource
      G P (F.map (point x) ≫ α)
  let q (x : X) : ModuleCat.of R R ⟶ Y := (qExists x).choose
  have hq (x : X) : F.map (q x) = F.map (point x) ≫ α :=
    (qExists x).choose_spec
  have hq_add (x y : X) : q (x + y) = q x + q y := by
    apply F.map_injective
    calc
      F.map (q (x + y)) = F.map (point (x + y)) ≫ α := hq (x + y)
      _ = F.map (point x + point y) ≫ α := by
        congr 2
        apply ModuleCat.hom_ext
        exact LinearMap.toSpanSingleton_add x y
      _ = (F.map (point x) + F.map (point y)) ≫ α := by
        rw [F.map_add]
      _ = F.map (point x) ≫ α + F.map (point y) ≫ α := by
        rw [Preadditive.add_comp]
      _ = F.map (q x) + F.map (q y) := by rw [hq x, hq y]
      _ = F.map (q x + q y) := by rw [F.map_add]
  let rightMul (r : R) : ModuleCat.of R R ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom (LinearMap.mulRight R r)
  have point_smul (r : R) (x : X) :
      point (r • x) = rightMul r ≫ point x := by
    apply ModuleCat.hom_ext
    ext a
    simp [point, rightMul]
  have hq_smul (r : R) (x : X) :
      q (r • x) = rightMul r ≫ q x := by
    apply F.map_injective
    calc
      F.map (q (r • x)) = F.map (point (r • x)) ≫ α := hq (r • x)
      _ = F.map (rightMul r ≫ point x) ≫ α := by rw [point_smul]
      _ = F.map (rightMul r) ≫ (F.map (point x) ≫ α) := by
        rw [F.map_comp, Category.assoc]
      _ = F.map (rightMul r) ≫ F.map (q x) := by rw [hq x]
      _ = F.map (rightMul r ≫ q x) := by rw [F.map_comp]
  let f : X →ₗ[R] Y :=
    { toFun := fun x ↦ (q x).hom 1
      map_add' := by
        intro x y
        rw [hq_add]
        rfl
      map_smul' := by
        intro r x
        calc
          (q (r • x)).hom 1 = (rightMul r ≫ q x).hom 1 := by
            rw [hq_smul]
          _ = r • (q x).hom 1 := by
            change (q x).hom (1 * r) = r • (q x).hom 1
            simpa using (q x).hom.map_smul r (1 : R) }
  let fm : X ⟶ Y := ModuleCat.ofHom f
  refine ⟨fm, ?_⟩
  apply ModuleCat.hom_ext
  ext a
  apply ModuleCat.hom_ext
  ext g
  let am : G ⟶ X := a
  let pointG : ModuleCat.of R R ⟶ G :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R G g)
  let αa : G ⟶ Y := α.hom am
  have point_comp : point (am.hom g) = pointG ≫ am := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r • a.hom g = a.hom (r • g)
    exact (am.hom.map_smul r g).symm
  have hq_point : q (am.hom g) = pointG ≫ αa := by
    apply F.map_injective
    apply ModuleCat.hom_ext
    ext t
    let tm : G ⟶ ModuleCat.of R R := t
    change tm ≫ q (am.hom g) =
      tm ≫ pointG ≫ αa
    have hleft := congrArg (fun z ↦ z.hom tm) (hq (am.hom g))
    change tm ≫ q (am.hom g) = α.hom (tm ≫ point (am.hom g)) at hleft
    rw [hleft, point_comp]
    change α.hom (tm ≫ pointG ≫ am) = tm ≫ pointG ≫ αa
    have hlin := moduleHom_comp G α (tm ≫ pointG) am
    change α.hom ((tm ≫ pointG) ≫ am) =
      (tm ≫ pointG) ≫ αa at hlin
    simpa only [Category.assoc] using hlin
  change (q (am.hom g)).hom 1 = (α.hom am).hom g
  rw [hq_point]
  rw [ModuleCat.comp_apply]
  simp [pointG, αa]

/-- The inclusion of one summand into an arbitrary direct sum of copies of a
module, using the concrete `Finsupp` model. -/
def finsuppInclusion (G : ModuleCat.{u} R) (ι : Type u) (i : ι) :
    G ⟶ ModuleCat.of R (ι →₀ G) :=
  ModuleCat.ofHom (Finsupp.lsingle i)

private def postcompEndLinearMap (G : ModuleCat.{u} R) {X : ModuleCat.{u} R}
    (f : G ⟶ X) : (G ⟶ G) →ₗ[(End G)ᵐᵒᵖ] (G ⟶ X) where
  toFun e := e ≫ f
  map_add' := by
    intro e e'
    change (e + e') ≫ f = e ≫ f + e' ≫ f
    rw [Preadditive.add_comp]
  map_smul' := by
    intro e a
    change e.unop ≫ a ≫ f = e.unop ≫ (a ≫ f)
    rfl

/-- The canonical map from a free module over `(End G)ᵐᵒᵖ` to the
module represented by the corresponding direct sum of copies of `G`. -/
def freeModuleRepresentableLinearMap (G : ModuleCat.{u} R) (ι : Type u) :
    (ι →₀ (End G)ᵐᵒᵖ) →ₗ[(End G)ᵐᵒᵖ]
      (G ⟶ ModuleCat.of R (ι →₀ G)) :=
  Finsupp.lsum ℤ <| fun i ↦
    (postcompEndLinearMap G (finsuppInclusion G ι i)).comp
      (regularLinearEquiv G).toLinearMap

/-- The categorical form of `freeModuleRepresentableLinearMap`. -/
def freeModuleRepresentableMap (G : ModuleCat.{u} R) (ι : Type u) :
    ModuleCat.of (End G)ᵐᵒᵖ (ι →₀ (End G)ᵐᵒᵖ) ⟶
      (preadditiveCoyonedaObj G).obj (ModuleCat.of R (ι →₀ G)) :=
  ModuleCat.ofHom (freeModuleRepresentableLinearMap G ι)

private theorem freeModuleRepresentableMap_apply_single
    (G : ModuleCat.{u} R) (ι : Type u) (i : ι) (e : (End G)ᵐᵒᵖ) :
    (freeModuleRepresentableMap G ι).hom (Finsupp.single i e) =
      ((preadditiveCoyonedaObj G).map
        (finsuppInclusion G ι i)).hom e.unop := by
  change (freeModuleRepresentableLinearMap G ι) (Finsupp.single i e) = _
  simp only [freeModuleRepresentableLinearMap]
  rw [Finsupp.lsum_single]
  rfl

private theorem freeModuleRepresentableMap_apply
    (G : ModuleCat.{u} R) (ι : Type u)
    (a : ι →₀ (End G)ᵐᵒᵖ) (g : G) (i : ι) :
    ((freeModuleRepresentableMap G ι).hom a).hom g i =
      (a i).unop.hom g := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => rfl
  | add a b ha hb =>
      rw [map_add, Finsupp.add_apply, MulOpposite.unop_add]
      exact congrArg₂ (.+.) ha hb
  | single j e =>
      have hs := congrArg (fun q ↦ q.hom g i)
        (freeModuleRepresentableMap_apply_single G ι j e)
      by_cases hji : j = i
      · subst i
        change
          ((freeModuleRepresentableMap G ι).hom
              (Finsupp.single j e)).hom g j =
            (Finsupp.single j (e.unop.hom g)) j at hs
        simpa using hs
      · change
          ((freeModuleRepresentableMap G ι).hom
              (Finsupp.single j e)).hom g i =
            (Finsupp.single j (e.unop.hom g)) i at hs
        simpa [hji] using hs

private theorem freeModuleRepresentableMap_injective
    (G : ModuleCat.{u} R) (ι : Type u) :
    Function.Injective (freeModuleRepresentableMap G ι).hom := by
  intro a b hab
  ext i
  apply MulOpposite.unop_injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  have hg := congrArg (fun f ↦ f.hom g i) hab
  rw [freeModuleRepresentableMap_apply,
    freeModuleRepresentableMap_apply] at hg
  exact hg

private theorem freeModuleRepresentableMap_surjective
    (G : ModuleCat.{u} R) (ι : Type u) [Module.Finite R G] :
    Function.Surjective (freeModuleRepresentableMap G ι).hom := by
  intro f
  obtain ⟨c, hc⟩ :=
    (LinearMap.finsuppLinearMap_bijective_of_moduleFinite
      R G G ι ℤ).2 f.hom
  let a : ι →₀ (End G)ᵐᵒᵖ :=
    c.mapRange (fun q ↦ MulOpposite.op (ModuleCat.ofHom q)) (by simp)
  refine ⟨a, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  have hg := LinearMap.congr_fun hc g
  ext i
  have hgi := DFunLike.congr_fun hg i
  rw [freeModuleRepresentableMap_apply]
  simpa [a, LinearMap.finsuppLinearMap] using hgi

/-- If `G` is finitely generated, `Hom(G, ι →₀ G)` is the free
`(End G)ᵐᵒᵖ`-module on `ι`, for an arbitrary index type `ι`. -/
def freeModuleRepresentableIso (G : ModuleCat.{u} R) (ι : Type u)
    [Module.Finite R G] :
    ModuleCat.of (End G)ᵐᵒᵖ (ι →₀ (End G)ᵐᵒᵖ) ≅
      (preadditiveCoyonedaObj G).obj (ModuleCat.of R (ι →₀ G)) :=
  (LinearEquiv.ofBijective (freeModuleRepresentableMap G ι).hom
    ⟨freeModuleRepresentableMap_injective G ι,
      freeModuleRepresentableMap_surjective G ι⟩).toModuleIso

/-- A finitely generated projective generator represents every module over
its opposite endomorphism ring. -/
theorem preadditiveCoyonedaObj_essSurj_of_regular_finiteAddClosure
    (G : ModuleCat.{u} R) [Module.Finite R G] [Projective G]
    (hregular : finiteAddClosure G (ModuleCat.of R R)) :
    (preadditiveCoyonedaObj G).EssSurj := by
  let F := preadditiveCoyonedaObj G
  let B := (End G)ᵐᵒᵖ
  letI : F.Faithful :=
    preadditiveCoyonedaObj_faithful_of_regular_finiteAddClosure G hregular
  letI : F.Full :=
    preadditiveCoyonedaObj_full_of_regular_finiteAddClosure G hregular
  constructor
  intro N
  let q : (N →₀ B) →ₗ[B] N :=
    Finsupp.linearCombination B (fun x : N ↦ x)
  have hq : Function.Surjective q := by
    intro x
    refine ⟨Finsupp.single x 1, ?_⟩
    simp [q]
  let K := LinearMap.ker q
  let d : (K →₀ B) →ₗ[B] (N →₀ B) :=
    Finsupp.linearCombination B (fun x : K ↦ x.1)
  have hdRange : LinearMap.range d = K := by
    apply le_antisymm
    · rintro y ⟨z, rfl⟩
      classical
      simp only [d, Finsupp.linearCombination_apply]
      apply K.sum_mem
      intro x hx
      exact K.smul_mem (z x) x.2
    · intro y hy
      refine ⟨Finsupp.single ⟨y, hy⟩ 1, ?_⟩
      simp [d]
  let dModule : ModuleCat.of B (K →₀ B) ⟶
      ModuleCat.of B (N →₀ B) := ModuleCat.ofHom d
  let φK : F.obj (ModuleCat.of R (K →₀ G)) ≅
      ModuleCat.of B (K →₀ B) := (freeModuleRepresentableIso G K).symm
  let φN : F.obj (ModuleCat.of R (N →₀ G)) ≅
      ModuleCat.of B (N →₀ B) := (freeModuleRepresentableIso G N).symm
  let δ : F.obj (ModuleCat.of R (K →₀ G)) ⟶
      F.obj (ModuleCat.of R (N →₀ G)) :=
    φK.hom ≫ dModule ≫ φN.inv
  let dC : ModuleCat.of R (K →₀ G) ⟶
      ModuleCat.of R (N →₀ G) := F.preimage δ
  have hdC : F.map dC = δ := F.map_preimage δ
  let mapEqIso : cokernel (F.map dC) ≅ cokernel δ :=
    cokernel.mapIso (F.map dC) δ (Iso.refl _) (Iso.refl _) (by
      simpa using hdC)
  let freeCokernelIso : cokernel δ ≅ cokernel dModule :=
    cokernel.mapIso δ dModule φK φN (by
      dsimp only [δ]
      simp)
  let rangeQuotientIso : cokernel dModule ≅ N :=
    (ModuleCat.cokernelIsoRangeQuotient dModule).trans <|
      ((Submodule.quotEquivOfEq d.range K hdRange).toModuleIso).trans <|
        (q.quotKerEquivOfSurjective hq).toModuleIso
  let representedIso : F.obj (cokernel dC) ≅ N :=
    (PreservesCokernel.iso F dC).trans <|
      mapEqIso.trans <| freeCokernelIso.trans rangeQuotientIso
  exact ⟨cokernel dC, ⟨representedIso⟩⟩

/-- The all-module equivalence represented by a finitely generated projective
generator. -/
def moduleEquivalenceOfProgenerator
    (G : ModuleCat.{u} R) [Module.Finite R G] [Projective G]
    (hregular : finiteAddClosure G (ModuleCat.of R R)) :
    ModuleCat.{u} R ≌ ModuleCat.{u} (End G)ᵐᵒᵖ := by
  let F := preadditiveCoyonedaObj G
  letI : F.Faithful :=
    preadditiveCoyonedaObj_faithful_of_regular_finiteAddClosure G hregular
  letI : F.Full :=
    preadditiveCoyonedaObj_full_of_regular_finiteAddClosure G hregular
  letI : F.EssSurj :=
    preadditiveCoyonedaObj_essSurj_of_regular_finiteAddClosure G hregular
  letI : F.IsEquivalence :=
    Functor.IsEquivalence.mk inferInstance inferInstance inferInstance
  exact F.asEquivalence

universe v

variable {k : Type v} [CommSemiring k] [Algebra k R]

/-- The represented all-module functor respects the scalar action inherited
from an algebra over a commutative semiring. -/
noncomputable instance preadditiveCoyonedaObj_linear (G : ModuleCat.{u} R) :
    (preadditiveCoyonedaObj G).Linear k where
  map_smul {X Y} f r := by
    apply ModuleCat.hom_ext
    ext g
    have hleft :
        ((preadditiveCoyonedaObj G).map (r • f)).hom g =
          g ≫ (r • f) := rfl
    have hright :
        (r • ((preadditiveCoyonedaObj G).map f)).hom g =
          (algebraMap k (End G)ᵐᵒᵖ r) • (g ≫ f) := rfl
    rw [hleft, hright]
    change r • (g ≫ f) = (r • 𝟙 G) ≫ (g ≫ f)
    simp

/-- The Morita equivalence supplied by a finitely generated projective
generator, in Mathlib's all-module and linear convention. -/
def moritaEquivalenceOfProgenerator
    (G : ModuleCat.{u} R) [Module.Finite R G] [Projective G]
    (hregular : finiteAddClosure G (ModuleCat.of R R)) :
    _root_.MoritaEquivalence k R (End G)ᵐᵒᵖ where
  eqv := moduleEquivalenceOfProgenerator G hregular
  linear := preadditiveCoyonedaObj_linear G

end MagnitudeConjecture.CategoryTheory
