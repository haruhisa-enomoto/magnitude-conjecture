import MagnitudeConjecture.Algebra.RightModuleAlmostSplit
import MagnitudeConjecture.Algebra.RightModuleIdealQuotientCategory
import MagnitudeConjecture.CategoryTheory.SubobjectEquivalence
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Simple

/-!
# Indecomposable skeletons of arbitrary ideal quotients

For a two-sided ideal `I`, the indecomposable right modules over the literal
quotient `A/I` are indexed by the ambient finite-skeleton labels annihilated
by `I`.  This is the ideal-independent skeleton layer used by socle
rejection.
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
variable (I : TwoSidedIdeal A)

/-- Ambient indecomposable labels annihilated by `I`. -/
abbrev IdealQuotientLabel :=
  {i : Fin S.n // RightModule.IsAnnihilatedBy I (S.fgObj i)}

noncomputable instance idealQuotientLabelFintype :
    Fintype (S.IdealQuotientLabel I) :=
  Fintype.ofFinite _

/-- A surviving ambient label as an object of the annihilated full
subcategory. -/
def idealQuotientLabelObj (x : S.IdealQuotientLabel I) :
    RightModule.IdealQuotientSubcategory I :=
  ⟨S.fgObj x.1, x.2⟩

variable [IsNoetherianRing (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ]

/-- A surviving ambient label, realized as a finitely generated module over
the literal quotient `A/I`. -/
def idealQuotientFGObj (x : S.IdealQuotientLabel I) :
    RightModule.FinitelyGeneratedCategory
      (RightModule.idealQuotientAlgebra I) :=
  (RightModule.idealQuotientEquivalence (k := k) I).functor.obj
    (S.idealQuotientLabelObj I x)

omit [IsNoetherianRing
  (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ] in
/-- Indecomposability in the annihilated full subcategory is exactly ambient
indecomposability. -/
theorem idealQuotientSubcategory_indecomposable_iff_ambient
    [HasBinaryBiproducts (RightModule.IdealQuotientSubcategory I)]
    (M : RightModule.IdealQuotientSubcategory I) :
    Indecomposable M ↔ Indecomposable M.obj := by
  let U := (RightModule.IdealQuotientProperty I).ι
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
      let Yq : RightModule.IdealQuotientSubcategory I :=
        ⟨Y, (RightModule.IdealQuotientProperty I).prop_of_retract
          rY M.property⟩
      let Zq : RightModule.IdealQuotientSubcategory I :=
        ⟨Z, (RightModule.IdealQuotientProperty I).prop_of_retract
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

omit [IsNoetherianRing
  (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ] in
/-- For an annihilated module, simplicity in the full quotient subcategory
is exactly simplicity in the ambient module category. -/
theorem idealQuotientSubcategory_simple_iff_ambient
    (M : RightModule.IdealQuotientSubcategory I) :
    Simple M ↔ Simple M.obj := by
  let Q := RightModule.IdealQuotientProperty I
  letI : Q.Nonempty := ObjectProperty.nonempty_of_prop M.property
  letI : Q.ContainsZero := inferInstance
  rw [simple_iff_subobject_isSimpleOrder,
    simple_iff_subobject_isSimpleOrder]
  exact OrderIso.isSimpleOrder_iff
    (MagnitudeConjecture.CategoryTheory.fullSubcategorySubobjectOrderIso
      (RightModule.IdealQuotientProperty I) M)

omit [IsNoetherianRing
  (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ] in
/-- Simplicity of a literal quotient module is exactly ambient simplicity
of its inflated annihilated module. -/
theorem idealQuotientFGObj_simple_iff_ambient
    (M : RightModule.IdealQuotientSubcategory I) :
    Simple ((RightModule.idealQuotientEquivalence
      (k := k) I).functor.obj M) ↔ Simple M.obj :=
  (CategoryTheory.simple_obj_iff
    (RightModule.idealQuotientEquivalence (k := k) I).functor M).trans
      (idealQuotientSubcategory_simple_iff_ambient (I := I) M)

/-- Every displayed quotient representative is indecomposable. -/
theorem idealQuotientFGObj_indecomposable
    (x : S.IdealQuotientLabel I) :
    Foundation.IsIndecomposableModule
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ
      (S.idealQuotientFGObj I x) := by
  let E := RightModule.idealQuotientEquivalence (k := k) I
  letI : E.functor.Additive := inferInstance
  let C := RightModule.IdealQuotientSubcategory I
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      E.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence E.functor
  let U := (RightModule.IdealQuotientProperty I).ι
  have hambient : Indecomposable
      (U.obj (S.idealQuotientLabelObj I x)) := by
    change Indecomposable (S.fgObj x.1)
    exact S.fgObj_indecomposable x.1
  have hsub : Indecomposable (S.idealQuotientLabelObj I x) :=
    MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
      U _ hambient
  have hquot : Indecomposable (S.idealQuotientFGObj I x) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor (S.idealQuotientLabelObj I x)).2 hsub
  exact (fgModule_isIndecomposableModule_iff_indecomposable
    (k := k) (A := RightModule.idealQuotientAlgebra I)
      (S.idealQuotientFGObj I x)).2 hquot

omit [IsNoetherianRing
  (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ] in
/-- The displayed quotient representatives have no isomorphic duplicates. -/
theorem idealQuotientFGObj_skeletal
    {x y : S.IdealQuotientLabel I}
    (h : Nonempty (S.idealQuotientFGObj I x ≅
      S.idealQuotientFGObj I y)) :
    x = y := by
  let E := RightModule.idealQuotientEquivalence (k := k) I
  let U := (RightModule.IdealQuotientProperty I).ι
  obtain ⟨h⟩ := h
  apply Subtype.ext
  apply S.fgObj_skeletal
  exact ⟨U.mapIso (E.functor.preimageIso h)⟩

/-- Every indecomposable quotient module is represented by a unique
annihilated ambient label. -/
theorem idealQuotientFGObj_complete
    (X : RightModule.FinitelyGeneratedCategory
      (RightModule.idealQuotientAlgebra I))
    (hX : Indecomposable X) :
    ∃ x : S.IdealQuotientLabel I,
      Nonempty (X ≅ S.idealQuotientFGObj I x) := by
  let E := RightModule.idealQuotientEquivalence (k := k) I
  letI : E.inverse.Additive := inferInstance
  let C := RightModule.IdealQuotientSubcategory I
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      E.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence E.functor
  let U := (RightModule.IdealQuotientProperty I).ι
  have hpre : Indecomposable (E.inverse.obj X) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.inverse X).2 hX
  have hambient : Indecomposable (U.obj (E.inverse.obj X)) := by
    exact (idealQuotientSubcategory_indecomposable_iff_ambient
      (I := I) (E.inverse.obj X)).1 hpre
  obtain ⟨i, ⟨hi⟩⟩ := S.fgObj_complete
    (U.obj (E.inverse.obj X)) hambient
  have hproperty : RightModule.IdealQuotientProperty I (S.fgObj i) :=
    (RightModule.IdealQuotientProperty I).prop_of_iso hi
      (E.inverse.obj X).property
  let x : S.IdealQuotientLabel I := ⟨i, hproperty⟩
  let hsub : E.inverse.obj X ≅ S.idealQuotientLabelObj I x :=
    U.preimageIso hi
  exact ⟨x, ⟨(E.counitIso.app X).symm.trans
    (E.functor.mapIso hsub)⟩⟩

/-- Every quotient module decomposes over the displayed surviving label
family. -/
theorem idealQuotientFGObj_decomposition
    (X : RightModule.FinitelyGeneratedCategory
      (RightModule.idealQuotientAlgebra I)) :
    ∃ n : ℕ, ∃ label : Fin n → S.IdealQuotientLabel I,
      Nonempty (X ≅ ⨁ fun i ↦ S.idealQuotientFGObj I (label i)) := by
  letI : Module k X := Module.restrictScalars k
    (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ X
  letI : IsScalarTower k
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ X :=
    IsScalarTower.restrictScalars k
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ X
  letI : Module.Finite k
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ := inferInstance
  letI : Module.Finite k X :=
    RightModule.finite_over_field_of_finitelyGenerated k
      (RightModule.idealQuotientAlgebra I) X
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_module_exists
    (k := k) X.obj
  let summandFG (j : Fin d.n) :
      RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra I) :=
    letI : Module.Finite k (d.summand j) :=
      d.summand_finite (k := k) inferInstance j
    ⟨d.summand j,
      Module.Finite.of_restrictScalars_finite k
        (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ (d.summand j)⟩
  have hsummand (j : Fin d.n) : Indecomposable (summandFG j) :=
    (indecomposable_iff_obj (k := k)
      (A := RightModule.idealQuotientAlgebra I) (summandFG j)).2
      (d.indecomposable j)
  have hcomplete (j : Fin d.n) :
      ∃ x : S.IdealQuotientLabel I,
        Nonempty (summandFG j ≅ S.idealQuotientFGObj I x) :=
    S.idealQuotientFGObj_complete I (summandFG j) (hsummand j)
  choose label hlabel using hcomplete
  let U := forget₂
    (RightModule.FinitelyGeneratedCategory
      (RightModule.idealQuotientAlgebra I))
    (RightModule.Category (RightModule.idealQuotientAlgebra I))
  letI : PreservesBiproduct
      (fun i ↦ S.idealQuotientFGObj I (label i)) U :=
    preservesBiproduct_of_preservesProduct U
  let eUnderlying : X.obj ≅
      U.obj (⨁ fun i ↦ S.idealQuotientFGObj I (label i)) :=
    d.isoBiproduct.trans
      ((biproduct.mapIso fun j ↦
          U.mapIso (Classical.choice (hlabel j))).trans
        (U.mapBiproduct
          (fun i ↦ S.idealQuotientFGObj I (label i))).symm)
  exact ⟨d.n, label, ⟨ObjectProperty.isoMk _ eUnderlying⟩⟩

/-- The indecomposable skeleton of the literal quotient `A/I`, with labels
identified with the annihilated ambient labels. -/
def idealQuotientAlmostSplitSkeleton :
    IndecomposableSkeleton
      (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ
      (S.IdealQuotientLabel I) where
  obj := S.idealQuotientFGObj I
  indecomposable := S.idealQuotientFGObj_indecomposable I
  finiteLength := fun x ↦
    fgModule_isFiniteLength (k := k)
      (A := RightModule.idealQuotientAlgebra I)
      (S.idealQuotientFGObj I x)
  eq_of_iso := S.idealQuotientFGObj_skeletal I
  complete := by
    intro X hX
    exact S.idealQuotientFGObj_complete I X
      ((fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := RightModule.idealQuotientAlgebra I) X).1 hX)
  decomposes := S.idealQuotientFGObj_decomposition I

/-- The single reindexing from the intrinsic surviving-label type to the
finite-ordinal shape used by `FiniteIndecomposableSkeleton`. -/
def idealQuotientFiniteLabelEquiv :
    Fin (Nat.card (S.IdealQuotientLabel I)) ≃ S.IdealQuotientLabel I :=
  (Finite.equivFin (S.IdealQuotientLabel I)).symm

/-- The complete duplicate-free finite skeleton of the literal ideal
quotient, retaining the intrinsic surviving labels through
`idealQuotientFiniteLabelEquiv`. -/
def idealQuotientFiniteIndecomposableSkeleton :
    RightModule.FiniteIndecomposableSkeleton k
      (RightModule.idealQuotientAlgebra I) := by
  let sigma := S.idealQuotientAlmostSplitSkeleton I
  let q := S.idealQuotientFiniteLabelEquiv I
  refine
    { n := Nat.card (S.IdealQuotientLabel I)
      obj := fun i ↦ (sigma.obj (q i)).obj
      obj_finite := ?_
      obj_indecomposable := ?_
      eq_of_iso := ?_
      complete := ?_ }
  · intro i
    exact RightModule.finite_over_field_of_finitelyGenerated k
      (RightModule.idealQuotientAlgebra I) (sigma.obj (q i))
  · intro i
    exact (RightModule.FiniteIndecomposableSkeleton.indecomposable_iff_obj
      (k := k) (A := RightModule.idealQuotientAlgebra I)
        (sigma.obj (q i))).1
      ((fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := RightModule.idealQuotientAlgebra I)
          (sigma.obj (q i))).1 (sigma.indecomposable (q i)))
  · intro i j hij
    apply q.injective
    apply sigma.eq_of_iso
    exact hij.map fun h ↦ ObjectProperty.isoMk _ h
  · intro M hM
    let Mfg : RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra I) :=
      @RightModule.finitelyGeneratedOfFiniteDimensional k _
        (RightModule.idealQuotientAlgebra I) _ _ M hM.1
    have hMfg : Indecomposable Mfg :=
      (RightModule.FiniteIndecomposableSkeleton.indecomposable_iff_obj
        (k := k) (A := RightModule.idealQuotientAlgebra I) Mfg).2 hM.2
    have hMmodule : Foundation.IsIndecomposableModule
        (RightModule.idealQuotientAlgebra I)ᵐᵒᵖ Mfg :=
      (fgModule_isIndecomposableModule_iff_indecomposable
        (k := k) (A := RightModule.idealQuotientAlgebra I) Mfg).2 hMfg
    obtain ⟨x, ⟨hx⟩⟩ := sigma.complete Mfg hMmodule
    refine ⟨q.symm x, ?_⟩
    rw [q.apply_symm_apply]
    exact ⟨(forget₂
      (RightModule.FinitelyGeneratedCategory
        (RightModule.idealQuotientAlgebra I))
      (RightModule.Category
        (RightModule.idealQuotientAlgebra I))).mapIso hx⟩

/-- The finite-ordinal quotient representative is canonically the intrinsic
surviving-label representative from which it was constructed. -/
def idealQuotientFiniteFGObjIso
    (j : Fin (S.idealQuotientFiniteIndecomposableSkeleton I).n) :
    (S.idealQuotientFiniteIndecomposableSkeleton I).fgObj j ≅
      S.idealQuotientFGObj I (S.idealQuotientFiniteLabelEquiv I j) :=
  Iso.refl _

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
