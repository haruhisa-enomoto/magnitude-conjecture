import MagnitudeConjecture.Algebra.RightModuleBasicMorita
import MagnitudeConjecture.Algebra.RightModuleRegularDecomposition
import MagnitudeConjecture.Algebra.BoundQuiverAdmissibleBasic
import MagnitudeConjecture.Algebra.SpecialBiserialAlgebra
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitivePresentation
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitiveQuotientSurplusReindex
import MagnitudeConjecture.CategoryTheory.FiniteMoritaEquivalence

/-!
# Uniqueness of finite-dimensional basic Morita representatives

A complete duplicate-free primitive-projective presentation identifies the
ambient algebra with the endomorphism algebra of the sum of its distinct
indecomposable projective right modules.  A linear equivalence of right-module
categories identifies those endomorphism algebras.  These are the two pieces
needed to turn Morita equivalence into algebra equivalence when both displayed
representatives are basic.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [IsNoetherianRing Aᵐᵒᵖ]

/-- Left multiplication by an algebra element as an endomorphism of the
finitely generated regular right module. -/
def rightRegularLeftMulFGHom (a : A) :
    rightRegularFGObj (B := A) ⟶ rightRegularFGObj (B := A) := by
  letI : Module.Finite Aᵐᵒᵖ A :=
    Module.Finite.equiv rightRegularLinearEquiv
  exact FGModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a)

@[simp]
theorem rightRegularLeftMulFGHom_apply (a x : A) :
    (rightRegularLeftMulFGHom a).hom.hom x = a * x :=
  rfl

/-- Left multiplication identifies an algebra with the categorical
endomorphism algebra of its regular right module. -/
def rightRegularEndAlgEquiv :
    A ≃ₐ[k] End (rightRegularFGObj (B := A)) where
  toFun a := rightRegularLeftMulFGHom a
  invFun f := f.hom.hom 1
  left_inv a := by
    change a * 1 = a
    simp
  right_inv f := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := f.hom.hom.map_smul (MulOpposite.op x) (1 : A)
    rw [rightRegularLeftMulFGHom_apply]
    simpa using hx.symm
  map_add' a b := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (a + b) * x = a * x + b * x
    exact add_mul a b x
  map_mul' a b := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (a * b) * x = a * (b * x)
    exact mul_assoc a b x
  commutes' r := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [rightRegularLeftMulFGHom_apply]
    simp only [Algebra.algebraMap_eq_smul_one]
    have hrhs :
        (r • (1 : End (rightRegularFGObj (B := A)))).hom.hom x =
          x * algebraMap k A r := rfl
    rw [hrhs]
    rw [Algebra.smul_def]
    rw [mul_one]
    exact Algebra.commutes r x

namespace FiniteIndecomposableSkeleton.PrimitiveProjectivePresentation

variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable (P : S.PrimitiveProjectivePresentation)

/-- A complete primitive family decomposes the regular module into the
chosen duplicate-free projective generator. -/
def regularIsoBasicProjectiveGenerator :
    rightRegularFGObj (B := A) ≅ S.basicProjectiveGenerator :=
  (regularDecompositionIso P.idempotent P.complete).trans <|
    biproduct.mapIso fun p ↦ P.primitiveProjectiveIso p

/-- A basic algebra supplied with its literal primitive-projective
presentation is algebra-equivalent to the canonical basic representative
formed from its right-module skeleton. -/
def ambientAlgEquivMoritaBasic : A ≃ₐ[k] S.moritaBasicAlgebra :=
  rightRegularEndAlgEquiv.trans <|
    MagnitudeConjecture.CategoryTheory.Iso.endAlgEquiv
      P.regularIsoBasicProjectiveGenerator

end FiniteIndecomposableSkeleton.PrimitiveProjectivePresentation

namespace FiniteIndecomposableSkeleton

variable {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B]
variable [IsNoetherianRing Bᵐᵒᵖ]

/-- Transport a complete duplicate-free indecomposable right-module
skeleton through an additive equivalence. -/
def mapEquivalence
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ FGModuleCat.{u} Bᵐᵒᵖ)
    [E.functor.Additive] [E.inverse.Additive] :
    RightModule.FiniteIndecomposableSkeleton k B := by
  refine
    { n := S.n
      obj := fun i ↦ (E.functor.obj (S.fgObj i)).obj
      obj_finite := fun i ↦
        finite_over_field_of_finitelyGenerated k B
          (E.functor.obj (S.fgObj i))
      obj_indecomposable := ?_
      eq_of_iso := ?_
      complete := ?_ }
  · intro i
    apply (FiniteIndecomposableSkeleton.indecomposable_iff_obj
      (k := k) (A := B) (E.functor.obj (S.fgObj i))).1
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.functor (S.fgObj i)).2 (S.fgObj_indecomposable i)
  · intro i j hij
    obtain ⟨hij⟩ := hij
    apply S.fgObj_skeletal
    exact ⟨E.functor.preimageIso (ObjectProperty.isoMk _ hij)⟩
  · intro M hM
    let Mfg : RightModule.FinitelyGeneratedCategory B :=
      @finitelyGeneratedOfFiniteDimensional k _ B _ _ M hM.1
    have hMfg : Indecomposable Mfg :=
      (FiniteIndecomposableSkeleton.indecomposable_iff_obj
        (k := k) (A := B) Mfg).2 hM.2
    have hInv : Indecomposable (E.inverse.obj Mfg) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.inverse Mfg).2 hMfg
    obtain ⟨i, ⟨hi⟩⟩ := S.fgObj_complete (E.inverse.obj Mfg) hInv
    let efg : Mfg ≅ E.functor.obj (S.fgObj i) :=
      (E.counitIso.app Mfg).symm ≪≫ E.functor.mapIso hi
    exact ⟨i, ⟨(forget₂
      (RightModule.FinitelyGeneratedCategory B) (Category B)).mapIso efg⟩⟩

/-- The transported skeleton object is the functorial image of the original
object with the same finite label. -/
def mapEquivalenceObjIso
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ FGModuleCat.{u} Bᵐᵒᵖ)
    [E.functor.Additive] [E.inverse.Additive] (i : Fin S.n) :
    E.functor.obj (S.fgObj i) ≅ (S.mapEquivalence E).fgObj i :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- Projective labels are transported without changing the underlying finite
label. -/
def mapEquivalenceProjectiveLabelEquiv
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ FGModuleCat.{u} Bᵐᵒᵖ)
    [E.functor.Additive] [E.inverse.Additive] :
    S.ProjectiveLabel ≃ (S.mapEquivalence E).ProjectiveLabel where
  toFun p := ⟨p.label, Projective.of_iso
    (S.mapEquivalenceObjIso E p.label)
      ((E.map_projective_iff (S.fgObj p.label)).2 p.projective)⟩
  invFun q := ⟨q.label,
    (E.map_projective_iff (S.fgObj q.label)).1
      (Projective.of_iso (S.mapEquivalenceObjIso E q.label).symm
        q.projective)⟩
  left_inv p := by
    rcases p with ⟨i, hi⟩
    rfl
  right_inv q := by
    rcases q with ⟨i, hi⟩
    rfl

/-- The image of the duplicate-free projective generator is the projective
generator of the transported skeleton. -/
def basicProjectiveGeneratorMapIso
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ FGModuleCat.{u} Bᵐᵒᵖ)
    [E.functor.Additive] [E.inverse.Additive] :
    E.functor.obj S.basicProjectiveGenerator ≅
      (S.mapEquivalence E).basicProjectiveGenerator :=
  (E.functor.mapBiproduct
      (fun p : S.ProjectiveLabel ↦ S.fgObj p.label)).trans <|
    biproduct.whiskerEquiv
      (S.mapEquivalenceProjectiveLabelEquiv E)
      (fun p ↦ (S.mapEquivalenceObjIso E p.label).symm)

/-- A linear equivalence of finitely generated right-module categories
identifies the canonical basic endomorphism algebras. -/
def moritaBasicAlgebraEquivOfEquivalence
    (S : RightModule.FiniteIndecomposableSkeleton k A)
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ FGModuleCat.{u} Bᵐᵒᵖ)
    [E.functor.Additive] [E.inverse.Additive] [E.functor.Linear k] :
    S.moritaBasicAlgebra ≃ₐ[k]
      (S.mapEquivalence E).moritaBasicAlgebra :=
  (MagnitudeConjecture.CategoryTheory.Functor.endAlgEquivOfFullyFaithful
      E.functor S.basicProjectiveGenerator).trans <|
    MagnitudeConjecture.CategoryTheory.Iso.endAlgEquiv
      (S.basicProjectiveGeneratorMapIso E)

end FiniteIndecomposableSkeleton

end MagnitudeConjecture.RightModule

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- For an algebra already certified as basic by a primitive-projective
presentation, the Morita-invariant special-biserial predicate can be realized
by a literal special-biserial presentation of the ambient algebra. -/
theorem ambient_admitsSpecialBiserialPresentation_of_isSpecialBiserial
    (P : S.PrimitiveProjectivePresentation)
    (hSpecial : BoundQuiver.IsSpecialBiserial k A) :
    BoundQuiver.AdmitsSpecialBiserialPresentation k A := by
  rcases hSpecial with ⟨M⟩
  rcases M.presentation with ⟨N⟩
  letI : Fintype N.Vertex := N.vertexFintype
  letI : Quiver.{u} N.Vertex := N.quiver
  letI (x y : N.Vertex) : Fintype (x ⟶ y) := N.arrowFintype x y
  let R : BoundQuiver.RelationFamily k N.Vertex :=
    N.presentation.toPresentation.relations
  let hR : BoundQuiver.IsAdmissible R :=
    N.presentation.toPresentation.admissible
  let hP := BoundQuiver.finiteRepresentablesOfAdmissible hR
  let D := CoveringHom.finiteCategoryProjectiveGenerator.algebra hP
  let hP₀ :=
    CoveringHom.finiteObjectModel_finiteCovariantRepresentables hP
  let D₀ := CoveringHom.finiteCategoryProjectiveGenerator.algebra hP₀
  let eD₀D : D₀ ≃ₐ[k] D :=
    CoveringHom.finiteCategoryAlgebraEquiv hP₀ hP
      (CoveringHom.finiteObjectModelEquivalence
        (C := BoundQuiver.Category R))
      (CoveringHom.finiteObjectEquiv
        (C := BoundQuiver.Category R)).bijective
  letI : FiniteDimensional k D₀ :=
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP₀
  letI : IsNoetherianRing D₀ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k D₀ᵐᵒᵖ
  let moritaAD₀ : _root_.MoritaEquivalence k A D₀ :=
    _root_.MoritaEquivalence.trans k M.morita
      (_root_.MoritaEquivalence.trans k
        (_root_.MoritaEquivalence.ofAlgEquiv
          N.presentation.toPresentation.algebraEquiv)
        (_root_.MoritaEquivalence.ofAlgEquiv eD₀D.symm))
  let E := MagnitudeConjecture.MoritaEquivalence.fgRightModuleEquivalence
    moritaAD₀
  let T :=
    MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton.mapEquivalence
      S E
  let PD : T.PrimitiveProjectivePresentation :=
    CoveringHom.finiteCategoryProjectiveGenerator.primitiveProjectivePresentation
      (k := k) (S := T) hP₀
        (CoveringHom.finiteObjectModel_localEndomorphismRings
          hR.quotientEnd_isLocalRing)
        (CoveringHom.finiteObjectModel_skeletal
          hR.quotientCategory_skeletal)
  let eAD₀ : A ≃ₐ[k] D₀ :=
    P.ambientAlgEquivMoritaBasic.trans <|
      (S.moritaBasicAlgebraEquivOfEquivalence E).trans <|
        PD.ambientAlgEquivMoritaBasic.symm
  let eACarrier : A ≃ₐ[k] M.Carrier :=
    eAD₀.trans <| eD₀D.trans
      N.presentation.toPresentation.algebraEquiv.symm
  exact ⟨N.mapAlgEquiv eACarrier⟩

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
