import MagnitudeConjecture.Algebra.RightModulePrimitiveDeletion
import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# A label-aligned indecomposable skeleton of the primitive quotient

The indecomposable right modules over `A / AeA` are indexed literally by the
ambient skeleton labels annihilated by `AeA`.  This file realizes those labels
inside the quotient module category and supplies the complete donor skeleton
needed to form intrinsic irreducible-Hom spaces.  No quotient-only relabeling
is introduced.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {e : A} (D : PrimitiveIdempotentData e)

variable [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ]

/-- A surviving ambient label, realized as a finitely generated module over
the literal primitive quotient. -/
def primitiveQuotientFGObj (x : S.PrimitiveQuotientLabel D) :
    RightModule.FinitelyGeneratedCategory
      (RightModule.primitiveQuotientAlgebra e) :=
  (RightModule.primitiveQuotientEquivalence (k := k) e).functor.obj
    (S.primitiveQuotientLabelObj D x)

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
/-- Indecomposability in the annihilated full subcategory is exactly
indecomposability in the ambient finitely generated module category. -/
theorem primitiveQuotientSubcategory_indecomposable_iff_ambient
    [HasBinaryBiproducts
      (RightModule.PrimitiveQuotientSubcategory e)]
    (M : RightModule.PrimitiveQuotientSubcategory e) :
    Indecomposable M ↔ Indecomposable M.obj := by
  let U := (RightModule.PrimitiveQuotientProperty e).ι
  constructor
  · intro hM
    refine ⟨?_, ?_⟩
    · intro hzero
      exact hM.1 (IsZero.of_full_of_faithful_of_isZero U M hzero)
    · intro Y Z hYZ
      let rY : Retract Y M.obj :=
        (BinaryBiproduct.bicone Y Z).retract_left |>.trans
          (Retract.ofIso hYZ.symm)
      let rZ : Retract Z M.obj :=
        (BinaryBiproduct.bicone Y Z).retract_right |>.trans
          (Retract.ofIso hYZ.symm)
      let Yq : RightModule.PrimitiveQuotientSubcategory e :=
        ⟨Y, (RightModule.PrimitiveQuotientProperty e).prop_of_retract
          rY M.property⟩
      let Zq : RightModule.PrimitiveQuotientSubcategory e :=
        ⟨Z, (RightModule.PrimitiveQuotientProperty e).prop_of_retract
          rZ M.property⟩
      letI : PreservesBinaryBiproduct Yq Zq U :=
        preservesBinaryBiproduct_of_preservesBinaryProduct U
      let hq : M ≅ Yq ⊞ Zq :=
        ObjectProperty.isoMk _
          (hYZ.trans (U.mapBiprod Yq Zq).symm)
      rcases hM.2 Yq Zq hq with hY | hZ
      · have hYu := U.map_isZero hY
        change IsZero Y at hYu
        exact Or.inl hYu
      · have hZu := U.map_isZero hZ
        change IsZero Z at hZu
        exact Or.inr hZu
  · intro hM
    exact
      MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
        U M hM

/-- Every literal quotient representative is indecomposable in the
module-theoretic sense used by the almost-split API. -/
theorem primitiveQuotientFGObj_indecomposable
    (x : S.PrimitiveQuotientLabel D) :
    Foundation.IsIndecomposableModule
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ
      (S.primitiveQuotientFGObj D x) := by
  let E := RightModule.primitiveQuotientEquivalence (k := k) e
  letI : E.functor.Additive := inferInstance
  let C := RightModule.PrimitiveQuotientSubcategory e
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      E.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence E.functor
  let U := (RightModule.PrimitiveQuotientProperty e).ι
  have hambient : Indecomposable
      (U.obj (S.primitiveQuotientLabelObj D x)) := by
    change Indecomposable (S.fgObj x.1)
    exact S.fgObj_indecomposable x.1
  have hsub : Indecomposable (S.primitiveQuotientLabelObj D x) :=
    MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
      U _ hambient
  have hquot : Indecomposable (S.primitiveQuotientFGObj D x) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor (S.primitiveQuotientLabelObj D x)).2 hsub
  exact (fgModule_isIndecomposableModule_iff_indecomposable
    (k := k) (A := RightModule.primitiveQuotientAlgebra e)
      (S.primitiveQuotientFGObj D x)).2 hquot

omit [IsNoetherianRing
  (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ] in
/-- The literal quotient representatives contain no isomorphic duplicates. -/
theorem primitiveQuotientFGObj_skeletal
    {x y : S.PrimitiveQuotientLabel D}
    (h : Nonempty (S.primitiveQuotientFGObj D x ≅
      S.primitiveQuotientFGObj D y)) :
    x = y := by
  let E := RightModule.primitiveQuotientEquivalence (k := k) e
  let U := (RightModule.PrimitiveQuotientProperty e).ι
  obtain ⟨h⟩ := h
  apply Subtype.ext
  apply S.fgObj_skeletal
  exact ⟨U.mapIso (E.functor.preimageIso h)⟩

/-- Every indecomposable quotient module is represented by a unique surviving
ambient label. -/
theorem primitiveQuotientFGObj_complete
    (X : RightModule.FinitelyGeneratedCategory
      (RightModule.primitiveQuotientAlgebra e))
    (hX : Indecomposable X) :
    ∃ x : S.PrimitiveQuotientLabel D,
      Nonempty (X ≅ S.primitiveQuotientFGObj D x) := by
  let E := RightModule.primitiveQuotientEquivalence (k := k) e
  letI : E.inverse.Additive := inferInstance
  let C := RightModule.PrimitiveQuotientSubcategory e
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      E.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence E.functor
  let U := (RightModule.PrimitiveQuotientProperty e).ι
  have hpre : Indecomposable (E.inverse.obj X) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse X).2 hX
  have hambient : Indecomposable (U.obj (E.inverse.obj X)) := by
    exact (primitiveQuotientSubcategory_indecomposable_iff_ambient
      (e := e) (E.inverse.obj X)).1 hpre
  obtain ⟨i, ⟨hi⟩⟩ := S.fgObj_complete
    (U.obj (E.inverse.obj X)) hambient
  have hproperty : RightModule.PrimitiveQuotientProperty e (S.fgObj i) :=
    (RightModule.PrimitiveQuotientProperty e).prop_of_iso hi
      (E.inverse.obj X).property
  let x : S.PrimitiveQuotientLabel D :=
    ⟨i, (S.mem_primitiveKilledLabels_iff_isAnnihilatedBy D i).2 hproperty⟩
  let hsub : E.inverse.obj X ≅ S.primitiveQuotientLabelObj D x :=
    U.preimageIso hi
  exact ⟨x, ⟨(E.counitIso.app X).symm.trans
    (E.functor.mapIso hsub)⟩⟩

/-- Every quotient module decomposes over the literal surviving label
family. -/
theorem primitiveQuotientFGObj_decomposition
    (X : RightModule.FinitelyGeneratedCategory
      (RightModule.primitiveQuotientAlgebra e)) :
    ∃ n : ℕ, ∃ label : Fin n → S.PrimitiveQuotientLabel D,
      Nonempty (X ≅ ⨁ fun i ↦ S.primitiveQuotientFGObj D (label i)) := by
  letI : Module k X := Module.restrictScalars k
    (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ X
  letI : IsScalarTower k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ X :=
    IsScalarTower.restrictScalars k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ X
  letI : Module.Finite k
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ := inferInstance
  letI : Module.Finite k X :=
    RightModule.finite_over_field_of_finitelyGenerated k
      (RightModule.primitiveQuotientAlgebra e) X
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_module_exists
    (k := k) X.obj
  let summandFG (j : Fin d.n) :
      RightModule.FinitelyGeneratedCategory
        (RightModule.primitiveQuotientAlgebra e) :=
    letI : Module.Finite k (d.summand j) :=
      d.summand_finite (k := k) inferInstance j
    ⟨d.summand j,
      Module.Finite.of_restrictScalars_finite k
        (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ (d.summand j)⟩
  have hsummand (j : Fin d.n) : Indecomposable (summandFG j) :=
    (indecomposable_iff_obj (k := k)
      (A := RightModule.primitiveQuotientAlgebra e) (summandFG j)).2
      (d.indecomposable j)
  have hcomplete (j : Fin d.n) :
      ∃ x : S.PrimitiveQuotientLabel D,
        Nonempty (summandFG j ≅ S.primitiveQuotientFGObj D x) :=
    S.primitiveQuotientFGObj_complete D (summandFG j) (hsummand j)
  choose label hlabel using hcomplete
  let U := forget₂
    (RightModule.FinitelyGeneratedCategory
      (RightModule.primitiveQuotientAlgebra e))
    (RightModule.Category (RightModule.primitiveQuotientAlgebra e))
  letI : PreservesBiproduct
      (fun i ↦ S.primitiveQuotientFGObj D (label i)) U :=
    preservesBiproduct_of_preservesProduct U
  let eUnderlying : X.obj ≅
      U.obj (⨁ fun i ↦ S.primitiveQuotientFGObj D (label i)) :=
    d.isoBiproduct.trans
      ((biproduct.mapIso fun j ↦
          U.mapIso (Classical.choice (hlabel j))).trans
        (U.mapBiproduct
          (fun i ↦ S.primitiveQuotientFGObj D (label i))).symm)
  exact ⟨d.n, label, ⟨ObjectProperty.isoMk _ eUnderlying⟩⟩

/-- The indecomposable skeleton of the primitive quotient whose labels are
literally the surviving labels of the ambient skeleton. -/
def primitiveQuotientAlmostSplitSkeleton :
    IndecomposableSkeleton
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ
      (S.PrimitiveQuotientLabel D) where
  obj := S.primitiveQuotientFGObj D
  indecomposable := S.primitiveQuotientFGObj_indecomposable D
  finiteLength := fun x ↦
    fgModule_isFiniteLength (k := k)
      (A := RightModule.primitiveQuotientAlgebra e)
      (S.primitiveQuotientFGObj D x)
  eq_of_iso := S.primitiveQuotientFGObj_skeletal D
  complete := by
    intro X hX
    exact S.primitiveQuotientFGObj_complete D X
      ((fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := RightModule.primitiveQuotientAlgebra e) X).1 hX)
  decomposes := S.primitiveQuotientFGObj_decomposition D

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
