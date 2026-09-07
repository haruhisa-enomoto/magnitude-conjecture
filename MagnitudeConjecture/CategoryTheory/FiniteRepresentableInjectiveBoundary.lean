import MagnitudeConjecture.CategoryTheory.AlmostSplitEquivalence
import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDuality
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableProjectiveBoundary
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaInjective
import MagnitudeConjecture.CategoryTheory.OrbitPushdownCorepresentable
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The injective boundary of the finite functor category

For an object with local endomorphism ring, restriction to the categorical
radical gives the canonical quotient
`D Hom(-,X) ⟶ D rad(-,X)`.  Finite coefficient duality identifies its
opposite with the projective radical inclusion over `Cᵒᵖ`, so this quotient
is left almost split.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical
open MagnitudeConjecture.CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- Precomposition acts contravariantly on the radical Hom subspaces. -/
def radicalHomPrecomp {Y Z X : C} (f : Y ⟶ Z) :
    radicalHomSubmodule k Z X →ₗ[k] radicalHomSubmodule k Y X where
  toFun q := ⟨f ≫ q.1, isRadicalMorphism_precomp f q.2⟩
  map_add' q r := by apply Subtype.ext; simp
  map_smul' a q := by apply Subtype.ext; simp

/-- The coefficient dual of the contravariant radical representable
`rad(-,X)`. -/
noncomputable def dualRadicalLinearYoneda (X : C) : C ⥤ ModuleCat.{v} k where
  obj Y := ModuleCat.of k (Module.Dual k (radicalHomSubmodule k Y X))
  map f := ModuleCat.ofHom (radicalHomPrecomp (k := k) f).dualMap
  map_id Y := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual k (radicalHomSubmodule k Y X) at phi
    apply LinearMap.ext
    intro q
    simp [radicalHomPrecomp]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro q
    simp [radicalHomPrecomp, Category.assoc]

instance dualRadicalLinearYoneda_additive (X : C) :
    (dualRadicalLinearYoneda (k := k) X).Additive where
  map_add := by
    intro Y Z f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual k (radicalHomSubmodule k Y X) at phi
    apply LinearMap.ext
    intro q
    change phi ⟨(f + g) ≫ q.1, _⟩ =
      phi ⟨f ≫ q.1, _⟩ + phi ⟨g ≫ q.1, _⟩
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp

instance dualRadicalLinearYoneda_linear (X : C) :
    (dualRadicalLinearYoneda (k := k) X).Linear k where
  map_smul := by
    intro Y Z f a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual k (radicalHomSubmodule k Y X) at phi
    apply LinearMap.ext
    intro q
    change phi ⟨(a • f) ≫ q.1, _⟩ = a • phi ⟨f ≫ q.1, _⟩
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    simp

/-- The dual radical representable as an additive linear module. -/
noncomputable def dualRadicalLinearYonedaLinearModule (X : C) :
    LinearModuleCategory (C := C) k :=
  ⟨dualRadicalLinearYoneda (k := k) X, inferInstance, inferInstance⟩

/-- Restriction of functionals along `rad(-,X) ⊆ Hom(-,X)`. -/
noncomputable def dualLinearYonedaRadicalProjectionNatTrans (X : C) :
    dualLinearYoneda (k := k) X ⟶
      dualRadicalLinearYoneda (k := k) X where
  app Y := ModuleCat.ofHom
    (radicalHomSubmodule k Y X).subtype.dualMap
  naturality := by
    intro Y Z f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro q
    rfl

/-- Bundled linear-module form of radical restriction. -/
noncomputable def dualLinearYonedaRadicalProjection (X : C) :
    dualLinearYonedaLinearModule (k := k) X ⟶
      dualRadicalLinearYonedaLinearModule (k := k) X :=
  ObjectProperty.homMk
    (dualLinearYonedaRadicalProjectionNatTrans (k := k) X)

instance dualLinearYonedaRadicalProjection_epi (X : C) :
    Epi (dualLinearYonedaRadicalProjection (k := k) X) := by
  let J := (IsLinearModule (C := C) k).ι
  haveI hEpiApp (Y : C) : Epi
      ((J.map (dualLinearYonedaRadicalProjection (k := k) X)).app Y) := by
    rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.dualMap_surjective_of_injective
      (radicalHomSubmodule k Y X).subtype_injective
  haveI : Epi (J.map (dualLinearYonedaRadicalProjection (k := k) X)) :=
    NatTrans.epi_of_epi_app _
  exact J.epi_of_epi_map
    (show Epi (J.map (dualLinearYonedaRadicalProjection (k := k) X)) from
      inferInstance)

/-- The dual radical quotient is finite whenever the ambient dual
corepresentable is finite. -/
theorem dualRadicalLinearYoneda_isFiniteDimensionalModule
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    IsFiniteDimensionalModule (C := C) k
      (dualRadicalLinearYonedaLinearModule (k := k) X) := by
  constructor
  · intro Y
    letI : FiniteDimensional k (Module.Dual k (Y ⟶ X)) := hX.1 Y
    exact FiniteDimensional.of_surjective
      (radicalHomSubmodule k Y X).subtype.dualMap
      (LinearMap.dualMap_surjective_of_injective
        (radicalHomSubmodule k Y X).subtype_injective)
  · apply hX.2.subset
    intro Y hY
    letI : Nontrivial (Module.Dual k (radicalHomSubmodule k Y X)) := hY
    have hsurj : Function.Surjective
        (radicalHomSubmodule k Y X).subtype.dualMap :=
      LinearMap.dualMap_surjective_of_injective
        (radicalHomSubmodule k Y X).subtype_injective
    exact hsurj.nontrivial

/-- The finite dual radical quotient. -/
noncomputable def finiteDimensionalDualRadicalLinearYoneda
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  ⟨dualRadicalLinearYonedaLinearModule (k := k) X,
    dualRadicalLinearYoneda_isFiniteDimensionalModule X hX⟩

/-- Radical restriction in the finite module category. -/
noncomputable def finiteDimensionalDualLinearYonedaRadicalProjection
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    finiteDimensionalDualLinearYoneda (k := k) X hX ⟶
      finiteDimensionalDualRadicalLinearYoneda (k := k) X hX :=
  ObjectProperty.homMk (dualLinearYonedaRadicalProjection (k := k) X)

instance finiteDimensionalDualLinearYonedaRadicalProjection_epi
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    Epi (finiteDimensionalDualLinearYonedaRadicalProjection
      (k := k) X hX) := by
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  haveI : Epi (J.map
      (finiteDimensionalDualLinearYonedaRadicalProjection
        (k := k) X hX)) := by
    change Epi (dualLinearYonedaRadicalProjection (k := k) X)
    infer_instance
  exact J.epi_of_epi_map
    (show Epi (J.map
      (finiteDimensionalDualLinearYonedaRadicalProjection
        (k := k) X hX)) from inferInstance)

/-! ## Identification after coefficient duality -/

/-- The categorical radical is invariant under passage to the opposite
category. -/
theorem isRadicalMorphism_op_iff {X Y : C} (f : X ⟶ Y) :
    IsRadicalMorphism f.op ↔ IsRadicalMorphism f := by
  constructor
  · intro hf g
    haveI hop : IsIso ((𝟙 Y - g ≫ f).op) := by
      change IsIso (𝟙 (Opposite.op Y) - f.op ≫ g.op)
      exact hf g.op
    haveI : IsIso (𝟙 Y - g ≫ f) :=
      (isIso_op_iff (𝟙 Y - g ≫ f)).1 hop
    exact isIso_one_sub_comp g f
  · intro hf g
    haveI : IsIso (𝟙 X - f ≫ g.unop) := hf g.unop
    haveI : IsIso (𝟙 Y - g.unop ≫ f) :=
      isIso_one_sub_comp f g.unop
    haveI : IsIso ((𝟙 Y - g.unop ≫ f).op) :=
      (isIso_op_iff (𝟙 Y - g.unop ≫ f)).2 inferInstance
    simpa only [op_sub, op_id, op_comp, Quiver.Hom.op_unop]
      using (inferInstance : IsIso ((𝟙 Y - g.unop ≫ f).op))

/-- Opposite passage as a linear equivalence on a Hom space. -/
def homOpLinearEquiv (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] (Opposite.op Y ⟶ Opposite.op X) where
  toFun := Quiver.Hom.op
  invFun := Quiver.Hom.unop
  left_inv := Quiver.Hom.unop_op
  right_inv := Quiver.Hom.op_unop
  map_add' f g := by apply Quiver.Hom.unop_inj; rfl
  map_smul' r f := opposite_op_smul (k := k) r f

/-- Opposite passage as a linear equivalence on radical Hom spaces. -/
def radicalHomOpLinearEquiv (X Y : C) :
    radicalHomSubmodule k X Y ≃ₗ[k]
      radicalHomSubmodule k (Opposite.op Y) (Opposite.op X) where
  toFun f := ⟨f.1.op, (isRadicalMorphism_op_iff f.1).2 f.2⟩
  invFun f := ⟨f.1.unop, by
    apply (isRadicalMorphism_op_iff f.1.unop).1
    simpa only [Quiver.Hom.op_unop] using
      (show IsRadicalMorphism f.1 from f.2)⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply Subtype.ext; rfl
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' r f := by apply Subtype.ext; exact opposite_op_smul (k := k) r f.1

/-- After coefficient duality, a finite dual corepresentable becomes the
corresponding representable over the opposite category. -/
noncomputable def coefficientDualDualLinearYonedaIso
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    coefficientDualModule (k := k)
        (dualLinearYonedaLinearModule (k := k) X) ≅
      linearCoyonedaLinearModule (k := k) (C := Cᵒᵖ) (Opposite.op X) := by
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun Y ↦ ?_) ?_
  · letI : FiniteDimensional k (Y.unop ⟶ X) :=
      (Module.finite_dual_iff k).mp (hX.1 Y.unop)
    exact ((Module.evalEquiv k (Y.unop ⟶ X)).symm.trans
      (homOpLinearEquiv (k := k) Y.unop X)).toModuleIso
  · intro Y Z f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ell
    change Module.Dual k (Module.Dual k (Y.unop ⟶ X)) at ell
    letI : FiniteDimensional k (Y.unop ⟶ X) :=
      (Module.finite_dual_iff k).mp (hX.1 Y.unop)
    letI : FiniteDimensional k (Z.unop ⟶ X) :=
      (Module.finite_dual_iff k).mp (hX.1 Z.unop)
    apply Quiver.Hom.unop_inj
    change
      (Module.evalEquiv k (Z.unop ⟶ X)).symm
          ((CategoryTheory.Linear.leftComp k X f.unop).dualMap.dualMap ell) =
        f.unop ≫ (Module.evalEquiv k (Y.unop ⟶ X)).symm ell
    apply Module.eval_apply_injective k
    apply LinearMap.ext
    intro phi
    calc
      phi ((Module.evalEquiv k (Z.unop ⟶ X)).symm
          ((CategoryTheory.Linear.leftComp k X f.unop).dualMap.dualMap ell)) =
        ((CategoryTheory.Linear.leftComp k X f.unop).dualMap.dualMap ell)
          phi := Module.apply_evalEquiv_symm_apply k (Z.unop ⟶ X) phi _
      _ = ell ((CategoryTheory.Linear.leftComp k X f.unop).dualMap phi) := rfl
      _ = ((CategoryTheory.Linear.leftComp k X f.unop).dualMap phi)
          ((Module.evalEquiv k (Y.unop ⟶ X)).symm ell) :=
        (Module.apply_evalEquiv_symm_apply k (Y.unop ⟶ X)
          ((CategoryTheory.Linear.leftComp k X f.unop).dualMap phi) ell).symm
      _ = phi (f.unop ≫
          (Module.evalEquiv k (Y.unop ⟶ X)).symm ell) := rfl

/-- After coefficient duality, the finite dual radical quotient becomes
the radical subrepresentable over the opposite category. -/
noncomputable def coefficientDualDualRadicalLinearYonedaIso
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    coefficientDualModule (k := k)
        (dualRadicalLinearYonedaLinearModule (k := k) X) ≅
      radicalLinearCoyonedaLinearModule
        (k := k) (C := Cᵒᵖ) (Opposite.op X) := by
  let hR := dualRadicalLinearYoneda_isFiniteDimensionalModule X hX
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun Y ↦ ?_) ?_
  · letI : FiniteDimensional k (radicalHomSubmodule k Y.unop X) :=
      (Module.finite_dual_iff k).mp (hR.1 Y.unop)
    exact ((Module.evalEquiv k
        (radicalHomSubmodule k Y.unop X)).symm.trans
      (radicalHomOpLinearEquiv (k := k) Y.unop X)).toModuleIso
  · intro Y Z f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ell
    change Module.Dual k
      (Module.Dual k (radicalHomSubmodule k Y.unop X)) at ell
    letI : FiniteDimensional k (radicalHomSubmodule k Y.unop X) :=
      (Module.finite_dual_iff k).mp (hR.1 Y.unop)
    letI : FiniteDimensional k (radicalHomSubmodule k Z.unop X) :=
      (Module.finite_dual_iff k).mp (hR.1 Z.unop)
    apply Subtype.ext
    apply Quiver.Hom.unop_inj
    change
      ((Module.evalEquiv k (radicalHomSubmodule k Z.unop X)).symm
        ((radicalHomPrecomp (k := k) f.unop).dualMap.dualMap ell)).1 =
      (f.unop ≫
        ((Module.evalEquiv k (radicalHomSubmodule k Y.unop X)).symm ell).1)
    have hsub :
        (Module.evalEquiv k (radicalHomSubmodule k Z.unop X)).symm
            ((radicalHomPrecomp (k := k) f.unop).dualMap.dualMap ell) =
          ⟨f.unop ≫
            ((Module.evalEquiv k
              (radicalHomSubmodule k Y.unop X)).symm ell).1,
            isRadicalMorphism_precomp f.unop
              ((Module.evalEquiv k
                (radicalHomSubmodule k Y.unop X)).symm ell).2⟩ := by
      apply Module.eval_apply_injective k
      apply LinearMap.ext
      intro phi
      calc
        phi ((Module.evalEquiv k (radicalHomSubmodule k Z.unop X)).symm
            ((radicalHomPrecomp (k := k) f.unop).dualMap.dualMap ell)) =
          ((radicalHomPrecomp (k := k) f.unop).dualMap.dualMap ell) phi :=
            Module.apply_evalEquiv_symm_apply k
              (radicalHomSubmodule k Z.unop X) phi _
        _ = ell ((radicalHomPrecomp (k := k) f.unop).dualMap phi) := rfl
        _ = ((radicalHomPrecomp (k := k) f.unop).dualMap phi)
            ((Module.evalEquiv k
              (radicalHomSubmodule k Y.unop X)).symm ell) :=
          (Module.apply_evalEquiv_symm_apply k
            (radicalHomSubmodule k Y.unop X)
            ((radicalHomPrecomp (k := k) f.unop).dualMap phi) ell).symm
        _ = phi ⟨f.unop ≫
            ((Module.evalEquiv k
              (radicalHomSubmodule k Y.unop X)).symm ell).1,
            isRadicalMorphism_precomp f.unop
              ((Module.evalEquiv k
                (radicalHomSubmodule k Y.unop X)).symm ell).2⟩ := rfl
    exact congrArg Subtype.val hsub

/-- Finiteness of a dual corepresentable over `C` implies finiteness of the
corresponding representable over `Cᵒᵖ`. -/
theorem oppositeLinearCoyoneda_isFiniteDimensionalModule
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    IsFiniteDimensionalModule (C := Cᵒᵖ) k
      (linearCoyonedaLinearModule (k := k) (Opposite.op X)) := by
  let I := finiteDimensionalDualLinearYoneda (k := k) X hX
  let DI := (finiteCoefficientDualFunctor (k := k) (C := C)).obj
    (Opposite.op I)
  exact (IsFiniteDimensionalModule (C := Cᵒᵖ) k).prop_of_iso
    (coefficientDualDualLinearYonedaIso (k := k) X hX) DI.property

/-- Finite-module form of the coefficient-dual identification of a dual
corepresentable with the opposite representable. -/
noncomputable def finiteCoefficientDualDualLinearYonedaIso
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    (finiteCoefficientDualFunctor (k := k) (C := C)).obj
        (Opposite.op (finiteDimensionalDualLinearYoneda (k := k) X hX)) ≅
      finiteDimensionalLinearCoyoneda (k := k) (Opposite.op X)
        (oppositeLinearCoyoneda_isFiniteDimensionalModule X hX) :=
  ObjectProperty.isoMk _
    (coefficientDualDualLinearYonedaIso (k := k) X hX)

/-- Finite-module form of the coefficient-dual identification of the dual
radical quotient with the opposite radical representable. -/
noncomputable def finiteCoefficientDualDualRadicalLinearYonedaIso
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    (finiteCoefficientDualFunctor (k := k) (C := C)).obj
        (Opposite.op
          (finiteDimensionalDualRadicalLinearYoneda (k := k) X hX)) ≅
      finiteDimensionalLinearCoyonedaRadical (k := k) (Opposite.op X)
        (oppositeLinearCoyoneda_isFiniteDimensionalModule X hX) :=
  ObjectProperty.isoMk _
    (coefficientDualDualRadicalLinearYonedaIso (k := k) X hX)

/-- Under the two coefficient-dual identifications, dualized radical
restriction is exactly the inclusion of the radical representable. -/
theorem finiteCoefficientDualDualLinearYoneda_radical_compatibility
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    (finiteCoefficientDualFunctor (k := k) (C := C)).map
          (finiteDimensionalDualLinearYonedaRadicalProjection
            (k := k) X hX).op ≫
        (finiteCoefficientDualDualLinearYonedaIso (k := k) X hX).hom =
      (finiteCoefficientDualDualRadicalLinearYonedaIso
          (k := k) X hX).hom ≫
        finiteDimensionalLinearCoyonedaRadicalInclusion
          (k := k) (Opposite.op X)
          (oppositeLinearCoyoneda_isFiniteDimensionalModule X hX) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Y
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  change Module.Dual k
    (Module.Dual k (radicalHomSubmodule k Y.unop X)) at ell
  let hR := dualRadicalLinearYoneda_isFiniteDimensionalModule X hX
  letI : FiniteDimensional k (Y.unop ⟶ X) :=
    (Module.finite_dual_iff k).mp (hX.1 Y.unop)
  letI : FiniteDimensional k (radicalHomSubmodule k Y.unop X) :=
    (Module.finite_dual_iff k).mp (hR.1 Y.unop)
  apply Quiver.Hom.unop_inj
  change
    (Module.evalEquiv k (Y.unop ⟶ X)).symm
        ((radicalHomSubmodule k Y.unop X).subtype.dualMap.dualMap ell) =
      ((Module.evalEquiv k
        (radicalHomSubmodule k Y.unop X)).symm ell).1
  apply Module.eval_apply_injective k
  apply LinearMap.ext
  intro phi
  calc
    phi ((Module.evalEquiv k (Y.unop ⟶ X)).symm
        ((radicalHomSubmodule k Y.unop X).subtype.dualMap.dualMap ell)) =
      ((radicalHomSubmodule k Y.unop X).subtype.dualMap.dualMap ell) phi :=
        Module.apply_evalEquiv_symm_apply k (Y.unop ⟶ X) phi _
    _ = ell ((radicalHomSubmodule k Y.unop X).subtype.dualMap phi) := rfl
    _ = ((radicalHomSubmodule k Y.unop X).subtype.dualMap phi)
        ((Module.evalEquiv k
          (radicalHomSubmodule k Y.unop X)).symm ell) :=
      (Module.apply_evalEquiv_symm_apply k
        (radicalHomSubmodule k Y.unop X)
        ((radicalHomSubmodule k Y.unop X).subtype.dualMap phi) ell).symm
    _ = phi ((Module.evalEquiv k
        (radicalHomSubmodule k Y.unop X)).symm ell).1 := rfl

/-! ## The canonical left almost-split quotient -/

/-- Endomorphisms of an opposite object are the multiplicative opposite of
the original endomorphism ring. -/
def endMulOppositeEquiv (X : C) :
    (End X)ᵐᵒᵖ ≃+* End (Opposite.op X) where
  toFun f := f.unop.op
  invFun f := MulOpposite.op f.unop
  left_inv := by intro f; cases f; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; apply Quiver.Hom.unop_inj; rfl
  map_mul' := by intro f g; apply Quiver.Hom.unop_inj; rfl

/-- The multiplicative opposite of a local ring is local. -/
theorem mulOpposite_isLocalRing
    {R : Type v} [Ring R] [IsLocalRing R] :
    IsLocalRing Rᵐᵒᵖ := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := R) (a := a.unop) (b := 1 - a.unop)
      (add_sub_cancel a.unop 1) with h | h
  · exact Or.inl (by simpa using h.op)
  · exact Or.inr (by simpa using h.op)

/-- Local endomorphism rings pass from a category to its opposite. -/
theorem opposite_end_isLocalRing
    (hlocal : ∀ X : C, IsLocalRing (End X)) (Y : Cᵒᵖ) :
    IsLocalRing (End Y) := by
  letI : IsLocalRing (End Y.unop) := hlocal Y.unop
  letI : IsLocalRing (End Y.unop)ᵐᵒᵖ := mulOpposite_isLocalRing
  simpa only [Opposite.op_unop] using
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (endMulOppositeEquiv Y.unop)

omit [Preadditive C] in
/-- If the opposite of a morphism is right almost split, the original
morphism is left almost split. -/
theorem leftAlmostSplit_of_op_isRightAlmostSplit
    {Z E : C} {f : Z ⟶ E} (hf : IsRightAlmostSplit f.op) :
    IsLeftAlmostSplit f := by
  constructor
  · intro hs
    apply hf.not_isSplitEpi
    obtain ⟨s⟩ := hs.exists_splitMono
    exact IsSplitEpi.mk'
      { section_ := s.retraction.op
        id := by
          apply Quiver.Hom.unop_inj
          simpa only [unop_comp, Quiver.Hom.unop_op, unop_id] using s.id }
  · intro W g hg
    have hgop : ¬ IsSplitEpi g.op := by
      intro hs
      apply hg
      obtain ⟨s⟩ := hs.exists_splitEpi
      exact IsSplitMono.mk'
        { retraction := s.section_.unop
          id := by
            apply Quiver.Hom.op_inj
            simpa only [op_comp, Quiver.Hom.op_unop, op_id] using s.id }
    obtain ⟨h, hh⟩ := hf.factors g.op hgop
    exact ⟨h.unop, by
      apply Quiver.Hom.op_inj
      simpa only [op_comp, Quiver.Hom.op_unop] using hh⟩

/-- Radical restriction from a finite dual corepresentable is the canonical
left almost-split morphism starting at that indecomposable injective. -/
theorem finiteDimensionalDualLinearYonedaRadicalProjection_isLeftAlmostSplit
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X)) (X : C) :
    IsLeftAlmostSplit
      (finiteDimensionalDualLinearYonedaRadicalProjection
        (k := k) X (hI X)) := by
  let hP : ∀ Y : Cᵒᵖ, IsFiniteDimensionalModule (C := Cᵒᵖ) k
      (linearCoyonedaLinearModule (k := k) Y) := fun Y ↦ by
    simpa only [Opposite.op_unop] using
      oppositeLinearCoyoneda_isFiniteDimensionalModule
        (k := k) Y.unop (hI Y.unop)
  let hlocalOp : ∀ Y : Cᵒᵖ, IsLocalRing (End Y) :=
    opposite_end_isLocalRing hlocal
  let p := finiteDimensionalDualLinearYonedaRadicalProjection
    (k := k) X (hI X)
  let eR := finiteCoefficientDualDualRadicalLinearYonedaIso
    (k := k) X (hI X)
  let eP := finiteCoefficientDualDualLinearYonedaIso
    (k := k) X (hI X)
  have hrad : IsRightAlmostSplit
      (finiteDimensionalLinearCoyonedaRadicalInclusion
        (k := k) (Opposite.op X) (hP (Opposite.op X))) :=
    finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
      hP hlocalOp (Opposite.op X)
  have hsource : IsRightAlmostSplit
      (eR.hom ≫ finiteDimensionalLinearCoyonedaRadicalInclusion
        (k := k) (Opposite.op X) (hP (Opposite.op X))) :=
    MagnitudeConjecture.CategoryTheory.rightAlmostSplit_precomp_iso eR hrad
  have hpost : IsRightAlmostSplit
      ((finiteCoefficientDualFunctor (k := k) (C := C)).map p.op ≫
        eP.hom) := by
    rw [finiteCoefficientDualDualLinearYoneda_radical_compatibility]
    exact hsource
  have hmap : IsRightAlmostSplit
      ((finiteCoefficientDualFunctor (k := k) (C := C)).map p.op) := by
    have h := hpost.postcomp_iso eP.symm
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  exact leftAlmostSplit_of_op_isRightAlmostSplit
    (IsRightAlmostSplit.of_map_equivalence
      (finiteCoefficientDualityEquivalence (k := k) (C := C)) hmap)

/-! ## The canonical simple socle -/

/-- The simple socle coordinate of a finite dual corepresentable, realized
as the kernel of its canonical left almost-split radical quotient. -/
noncomputable abbrev finiteDimensionalDualLinearYonedaSocle
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :=
  kernel (finiteDimensionalDualLinearYonedaRadicalProjection
    (k := k) X hX)

/-- The canonical socle inclusion into a finite dual corepresentable. -/
noncomputable abbrev finiteDimensionalDualLinearYonedaSocleInclusion
    (X : C)
    (hX : IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X)) :
    finiteDimensionalDualLinearYonedaSocle (k := k) X hX ⟶
      finiteDimensionalDualLinearYoneda (k := k) X hX :=
  kernel.ι (finiteDimensionalDualLinearYonedaRadicalProjection
    (k := k) X hX)

theorem finiteDimensionalDualLinearYonedaSocle_simple
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X)) (X : C) :
    Simple (finiteDimensionalDualLinearYonedaSocle (k := k) X (hI X)) := by
  let p := finiteDimensionalDualLinearYonedaRadicalProjection
    (k := k) X (hI X)
  haveI : Injective
      (finiteDimensionalDualLinearYoneda (k := k) X (hI X)) :=
    finiteDimensionalDualLinearYoneda_injective X (hI X)
  exact simple_kernel_of_epi_leftAlmostSplit_injective p
    (finiteDimensionalDualLinearYonedaRadicalProjection_isLeftAlmostSplit
      hI hlocal X)

/-- The canonical simple socle inclusion of a finite dual
corepresentable is nonzero. -/
theorem finiteDimensionalDualLinearYonedaSocleInclusion_ne_zero
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X)) (X : C) :
    finiteDimensionalDualLinearYonedaSocleInclusion
      (k := k) X (hI X) ≠ 0 := by
  letI : Simple
      (finiteDimensionalDualLinearYonedaSocle (k := k) X (hI X)) :=
    finiteDimensionalDualLinearYonedaSocle_simple hI hlocal X
  intro hzero
  apply CategoryTheory.id_nonzero
    (finiteDimensionalDualLinearYonedaSocle (k := k) X (hI X))
  apply (cancel_mono
    (finiteDimensionalDualLinearYonedaSocleInclusion
      (k := k) X (hI X))).1
  rw [Category.id_comp, zero_comp, hzero]

end MagnitudeConjecture.CoveringHom
