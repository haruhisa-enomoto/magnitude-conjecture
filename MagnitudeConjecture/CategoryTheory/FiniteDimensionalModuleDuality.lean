import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleThin
import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd
import MagnitudeConjecture.CategoryTheory.OppositeLinear
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coefficient duality for finite modules over a linear category

Pointwise coefficient duality turns a finite covariant module over `C` into
a finite covariant module over `Cᵒᵖ`.  Finite-dimensional biduality upgrades
this construction to an anti-equivalence of finite module categories.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- Pointwise coefficient dual of a covariant module, regarded as a module
over the opposite category. -/
noncomputable def coefficientDualModule
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k) :
    LinearModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k := by
  let F : Cᵒᵖ ⥤ ModuleCat.{v} k :=
    { obj := fun X ↦ ModuleCat.of k (Module.Dual k (M.obj.obj X.unop))
      map := fun f ↦ ModuleCat.ofHom (M.obj.map f.unop).hom.dualMap
      map_id := by
        intro X
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro phi
        apply LinearMap.ext
        intro x
        simp
      map_comp := by
        intro X Y Z f g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro phi
        apply LinearMap.ext
        intro x
        simp }
  have hAdd : F.Additive := by
    constructor
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro x
    simp [F]
  have hLinear : F.Linear k := by
    constructor
    intro X Y f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro x
    simp [F]
  exact ⟨F, hAdd, hLinear⟩

/-- A module morphism induces the reversed morphism between pointwise
coefficient duals. -/
noncomputable def coefficientDualMap
    {M N : LinearModuleCategory.{u, v, v, v} (C := C) k} (f : M ⟶ N) :
    coefficientDualModule (k := k) N ⟶
      coefficientDualModule (k := k) M :=
  ObjectProperty.homMk
    { app := fun X ↦ ModuleCat.ofHom (f.hom.app X.unop).hom.dualMap
      naturality := by
        intro X Y q
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro phi
        change Module.Dual k (N.obj.obj X.unop) at phi
        apply LinearMap.ext
        intro x
        have h := ConcreteCategory.congr_hom (f.hom.naturality q.unop) x
        change phi (N.obj.map q.unop (f.hom.app Y.unop x)) =
          phi (f.hom.app X.unop (M.obj.map q.unop x))
        exact congrArg phi h.symm }

@[simp]
theorem coefficientDualMap_id
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k) :
    coefficientDualMap (k := k) (M := M) (N := M) (𝟙 M) =
      𝟙 (coefficientDualModule (k := k) M) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro x
  rfl

@[simp]
theorem coefficientDualMap_comp
    {L M N : LinearModuleCategory.{u, v, v, v} (C := C) k}
    (f : L ⟶ M) (g : M ⟶ N) :
    coefficientDualMap (k := k) (f ≫ g) =
      coefficientDualMap (k := k) g ≫ coefficientDualMap (k := k) f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro x
  rfl

/-- Pointwise coefficient dual preserves the finite-module condition. -/
theorem coefficientDualModule_isFiniteDimensionalModule
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    IsFiniteDimensionalModule (C := Cᵒᵖ) k
      (coefficientDualModule (k := k) M.obj) := by
  constructor
  · intro X
    change FiniteDimensional k (Module.Dual k (M.obj.obj.obj X.unop))
    infer_instance
  · have hsupp :
        moduleSupport k (coefficientDualModule (k := k) M.obj).obj =
          Opposite.unop ⁻¹' moduleSupport k M.obj.obj := by
      ext X
      change Nontrivial (Module.Dual k (M.obj.obj.obj X.unop)) ↔
        Nontrivial (M.obj.obj.obj X.unop)
      exact Module.nontrivial_dual_iff k
    rw [hsupp]
    exact M.property.2.preimage
      (Set.injOn_of_injective Opposite.unop_injective)

/-- The coefficient dual as a contravariant functor between finite module
categories. -/
noncomputable def finiteCoefficientDualFunctor :
    (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)ᵒᵖ ⥤
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k where
  obj M := ⟨coefficientDualModule (k := k) M.unop.obj,
    coefficientDualModule_isFiniteDimensionalModule (k := k) M.unop⟩
  map f := ObjectProperty.homMk
    (coefficientDualMap (k := k) f.unop.hom)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact coefficientDualMap_id (k := k) M.unop.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact coefficientDualMap_comp (k := k) g.unop.hom f.unop.hom

noncomputable instance finiteCoefficientDualFunctor_additive :
    (finiteCoefficientDualFunctor (k := k) (C := C)).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual k (M.unop.obj.obj.obj X.unop) at phi
    apply LinearMap.ext
    intro x
    change phi (f.unop.hom.hom.app X.unop x +
        g.unop.hom.hom.app X.unop x) =
      phi (f.unop.hom.hom.app X.unop x) +
        phi (g.unop.hom.hom.app X.unop x)
    exact map_add phi _ _

/-- Pointwise coefficient duality preserves and reflects pointwise
thinness. -/
theorem coefficientDualModule_isPointwiseThin_iff
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    IsPointwiseThin (coefficientDualModule (k := k) M.obj).obj ↔
      IsPointwiseThin M.obj.obj := by
  constructor
  · intro hM X
    rw [← Subspace.dual_finrank_eq]
    exact hM (Opposite.op X)
  · intro hM X
    change Module.finrank k (Module.Dual k (M.obj.obj.obj X.unop)) ≤ 1
    rw [Subspace.dual_finrank_eq]
    exact hM X.unop

/-- Pointwise coefficient dual in the reverse direction, with the double
opposite removed. -/
noncomputable def reverseCoefficientDualModule
    (M : LinearModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k) :
    LinearModuleCategory.{u, v, v, v} (C := C) k := by
  let F : C ⥤ ModuleCat.{v} k :=
    { obj := fun X ↦ ModuleCat.of k
          (Module.Dual k (M.obj.obj (Opposite.op X)))
      map := fun f ↦ ModuleCat.ofHom (M.obj.map f.op).hom.dualMap
      map_id := by
        intro X
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro phi
        apply LinearMap.ext
        intro x
        simp
      map_comp := by
        intro X Y Z f g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro phi
        apply LinearMap.ext
        intro x
        simp }
  have hAdd : F.Additive := by
    constructor
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro x
    simp [F]
  have hLinear : F.Linear k := by
    constructor
    intro X Y f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    apply LinearMap.ext
    intro x
    simp [F]
  exact ⟨F, hAdd, hLinear⟩

/-- Reverse pointwise coefficient dual preserves finite modules. -/
theorem reverseCoefficientDualModule_isFiniteDimensionalModule
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k) :
    IsFiniteDimensionalModule (C := C) k
      (reverseCoefficientDualModule (k := k) M.obj) := by
  constructor
  · intro X
    change FiniteDimensional k
      (Module.Dual k (M.obj.obj.obj (Opposite.op X)))
    infer_instance
  · have hsupp :
        moduleSupport k (reverseCoefficientDualModule (k := k) M.obj).obj =
          Opposite.op ⁻¹' moduleSupport k M.obj.obj := by
      ext X
      change Nontrivial
          (Module.Dual k (M.obj.obj.obj (Opposite.op X))) ↔
        Nontrivial (M.obj.obj.obj (Opposite.op X))
      exact Module.nontrivial_dual_iff k
    rw [hsupp]
    exact M.property.2.preimage
      (Set.injOn_of_injective Opposite.op_injective)

/-- The same bidual evaluation in the forward order over `Cᵒᵖ`. -/
noncomputable def coefficientReverseDoubleDualLinearIso
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k) :
    coefficientDualModule (k := k)
        (reverseCoefficientDualModule (k := k) M.obj) ≅ M.obj := by
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun X ↦
    (Module.evalEquiv k (M.obj.obj.obj X)).symm.toModuleIso) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ell
  apply Module.eval_apply_injective k
  apply LinearMap.ext
  intro phi
  change
    phi ((Module.evalEquiv k (M.obj.obj.obj Y)).symm
      ((M.obj.obj.map f).hom.dualMap.dualMap ell)) =
      phi (M.obj.obj.map f
        ((Module.evalEquiv k (M.obj.obj.obj X)).symm ell))
  simp only [Module.apply_evalEquiv_symm_apply, LinearMap.dualMap_apply]
  exact (Module.apply_evalEquiv_symm_apply k
    (M.obj.obj.obj X) ((M.obj.obj.map f).hom.dualMap phi) ell).symm

/-- Forward-order bidual evaluation inside the finite module category. -/
noncomputable def coefficientReverseDoubleDualIso
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k) :
    ⟨coefficientDualModule (k := k)
        (reverseCoefficientDualModule (k := k) M.obj),
      coefficientDualModule_isFiniteDimensionalModule (k := k)
        ⟨reverseCoefficientDualModule (k := k) M.obj,
          reverseCoefficientDualModule_isFiniteDimensionalModule
            (k := k) M⟩⟩ ≅ M :=
  ObjectProperty.isoMk _
    (coefficientReverseDoubleDualLinearIso (k := k) M)

/-- The morphism recovered from a morphism between coefficient duals by
finite-dimensional biduality. -/
noncomputable def coefficientDualPreimageLinearMap
    {M N : (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)ᵒᵖ}
    (a : (finiteCoefficientDualFunctor (k := k) (C := C)).obj M ⟶
      (finiteCoefficientDualFunctor (k := k) (C := C)).obj N) :
    N.unop.obj ⟶ M.unop.obj :=
  ObjectProperty.homMk
    { app := fun X ↦ ModuleCat.ofHom
        ((Module.evalEquiv k (M.unop.obj.obj.obj X)).symm.toLinearMap.comp
          ((a.hom.hom.app (Opposite.op X)).hom.dualMap.comp
            (Module.evalEquiv k
              (N.unop.obj.obj.obj X)).toLinearMap))
      naturality := by
        intro X Y f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        apply Module.eval_apply_injective k
        apply LinearMap.ext
        intro phi
        change
          phi ((Module.evalEquiv k (M.unop.obj.obj.obj Y)).symm
            ((a.hom.hom.app (Opposite.op Y)).hom.dualMap
              (Module.evalEquiv k (N.unop.obj.obj.obj Y)
                (N.unop.obj.obj.map f y)))) =
          phi (M.unop.obj.obj.map f
            ((Module.evalEquiv k (M.unop.obj.obj.obj X)).symm
              ((a.hom.hom.app (Opposite.op X)).hom.dualMap
                (Module.evalEquiv k (N.unop.obj.obj.obj X) y))))
        have h := ConcreteCategory.congr_hom
          (a.hom.hom.naturality f.op) phi
        change
          a.hom.hom.app (Opposite.op X)
              ((M.unop.obj.obj.map f).hom.dualMap phi) =
            (N.unop.obj.obj.map f).hom.dualMap
              (a.hom.hom.app (Opposite.op Y) phi) at h
        have hy := congrArg
          (fun ell : Module.Dual k (N.unop.obj.obj.obj X) ↦ ell y)
          h.symm
        calc
          phi ((Module.evalEquiv k (M.unop.obj.obj.obj Y)).symm
              ((a.hom.hom.app (Opposite.op Y)).hom.dualMap
                (Module.evalEquiv k (N.unop.obj.obj.obj Y)
                  (N.unop.obj.obj.map f y)))) =
            (Module.evalEquiv k (N.unop.obj.obj.obj Y)
              (N.unop.obj.obj.map f y))
                (a.hom.hom.app (Opposite.op Y) phi) :=
              Module.apply_evalEquiv_symm_apply k
                (M.unop.obj.obj.obj Y) phi _
          _ = (show Module.Dual k (N.unop.obj.obj.obj Y) from
                a.hom.hom.app (Opposite.op Y) phi)
              (N.unop.obj.obj.map f y) := rfl
          _ = (show Module.Dual k (N.unop.obj.obj.obj X) from
                a.hom.hom.app (Opposite.op X)
                  ((M.unop.obj.obj.map f).hom.dualMap phi)) y := hy
          _ = ((a.hom.hom.app (Opposite.op X)).hom.dualMap
                (Module.evalEquiv k (N.unop.obj.obj.obj X) y))
              ((M.unop.obj.obj.map f).hom.dualMap phi) := rfl
          _ = ((M.unop.obj.obj.map f).hom.dualMap phi)
              ((Module.evalEquiv k (M.unop.obj.obj.obj X)).symm
                ((a.hom.hom.app (Opposite.op X)).hom.dualMap
                  (Module.evalEquiv k (N.unop.obj.obj.obj X) y))) :=
              (Module.apply_evalEquiv_symm_apply k
                (M.unop.obj.obj.obj X)
                ((M.unop.obj.obj.map f).hom.dualMap phi) _).symm
          _ = phi (M.unop.obj.obj.map f
              ((Module.evalEquiv k (M.unop.obj.obj.obj X)).symm
                ((a.hom.hom.app (Opposite.op X)).hom.dualMap
                  (Module.evalEquiv k (N.unop.obj.obj.obj X) y)))) := rfl }

/-- The recovered morphism, with both full-subcategory layers and the
opposite orientation restored. -/
noncomputable def coefficientDualPreimage
    {M N : (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)ᵒᵖ}
    (a : (finiteCoefficientDualFunctor (k := k) (C := C)).obj M ⟶
      (finiteCoefficientDualFunctor (k := k) (C := C)).obj N) :
    M ⟶ N :=
  (ObjectProperty.homMk (coefficientDualPreimageLinearMap (k := k) a)).op

/-- Dualizing the recovered morphism returns the original morphism. -/
theorem finiteCoefficientDualFunctor_map_coefficientDualPreimage
    {M N : (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)ᵒᵖ}
    (a : (finiteCoefficientDualFunctor (k := k) (C := C)).obj M ⟶
      (finiteCoefficientDualFunctor (k := k) (C := C)).obj N) :
    (finiteCoefficientDualFunctor (k := k) (C := C)).map
        (coefficientDualPreimage (k := k) a) = a := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change Module.Dual k (M.unop.obj.obj.obj X.unop) at phi
  apply LinearMap.ext
  intro x
  change
    phi ((Module.evalEquiv k (M.unop.obj.obj.obj X.unop)).symm
      ((a.hom.hom.app X).hom.dualMap
        (Module.evalEquiv k (N.unop.obj.obj.obj X.unop) x))) =
      (show Module.Dual k (N.unop.obj.obj.obj X.unop) from
        a.hom.hom.app X phi) x
  calc
    phi ((Module.evalEquiv k (M.unop.obj.obj.obj X.unop)).symm
        ((a.hom.hom.app X).hom.dualMap
          (Module.evalEquiv k (N.unop.obj.obj.obj X.unop) x))) =
      ((a.hom.hom.app X).hom.dualMap
        (Module.evalEquiv k (N.unop.obj.obj.obj X.unop) x)) phi :=
        Module.apply_evalEquiv_symm_apply k
          (M.unop.obj.obj.obj X.unop) phi _
    _ = (Module.evalEquiv k (N.unop.obj.obj.obj X.unop) x)
        (a.hom.hom.app X phi) := rfl
    _ = (show Module.Dual k (N.unop.obj.obj.obj X.unop) from
        a.hom.hom.app X phi) x := rfl

/-- Pointwise coefficient duality is full on finite modules. -/
instance finiteCoefficientDualFunctor_full :
    (finiteCoefficientDualFunctor (k := k) (C := C)).Full where
  map_surjective a :=
    ⟨coefficientDualPreimage (k := k) a,
      finiteCoefficientDualFunctor_map_coefficientDualPreimage
        (k := k) a⟩

/-- Recovering a dualized morphism returns the original morphism. -/
theorem coefficientDualPreimage_finiteCoefficientDualFunctor_map
    {M N : (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)ᵒᵖ}
    (f : M ⟶ N) :
    coefficientDualPreimage (k := k)
        ((finiteCoefficientDualFunctor (k := k) (C := C)).map f) = f := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Module.eval_apply_injective k
  apply LinearMap.ext
  intro phi
  change
    phi ((Module.evalEquiv k (M.unop.obj.obj.obj X)).symm
      ((f.unop.hom.hom.app X).hom.dualMap.dualMap
        (Module.evalEquiv k (N.unop.obj.obj.obj X) x))) =
      phi (f.unop.hom.hom.app X x)
  calc
    phi ((Module.evalEquiv k (M.unop.obj.obj.obj X)).symm
        ((f.unop.hom.hom.app X).hom.dualMap.dualMap
          (Module.evalEquiv k (N.unop.obj.obj.obj X) x))) =
      ((f.unop.hom.hom.app X).hom.dualMap.dualMap
        (Module.evalEquiv k (N.unop.obj.obj.obj X) x)) phi :=
        Module.apply_evalEquiv_symm_apply k
          (M.unop.obj.obj.obj X) phi _
    _ = (Module.evalEquiv k (N.unop.obj.obj.obj X) x)
        ((f.unop.hom.hom.app X).hom.dualMap phi) := rfl
    _ = phi (f.unop.hom.hom.app X x) := rfl

/-- Pointwise coefficient duality is faithful on finite modules. -/
instance finiteCoefficientDualFunctor_faithful :
    (finiteCoefficientDualFunctor (k := k) (C := C)).Faithful where
  map_injective {M N} f g h := by
    calc
      f = coefficientDualPreimage (k := k)
          ((finiteCoefficientDualFunctor (k := k) (C := C)).map f) :=
        (coefficientDualPreimage_finiteCoefficientDualFunctor_map
          (k := k) f).symm
      _ = coefficientDualPreimage (k := k)
          ((finiteCoefficientDualFunctor (k := k) (C := C)).map g) := by
        rw [h]
      _ = g :=
        coefficientDualPreimage_finiteCoefficientDualFunctor_map
          (k := k) g

/-- Every finite module over the opposite category is the coefficient dual
of its reverse coefficient dual. -/
instance finiteCoefficientDualFunctor_essSurj :
    (finiteCoefficientDualFunctor (k := k) (C := C)).EssSurj := by
  constructor
  intro M
  let N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
    ⟨reverseCoefficientDualModule (k := k) M.obj,
      reverseCoefficientDualModule_isFiniteDimensionalModule (k := k) M⟩
  exact ⟨Opposite.op N,
    ⟨coefficientReverseDoubleDualIso (k := k) M⟩⟩

/-- Pointwise coefficient duality is an anti-equivalence of finite module
categories. -/
instance finiteCoefficientDualFunctor_isEquivalence :
    (finiteCoefficientDualFunctor (k := k) (C := C)).IsEquivalence where

/-- The finite-module coefficient-duality anti-equivalence. -/
noncomputable def finiteCoefficientDualityEquivalence :
    (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)ᵒᵖ ≌
      FiniteDimensionalModuleCategory.{u, v, v, v} (C := Cᵒᵖ) k :=
  (finiteCoefficientDualFunctor (k := k) (C := C)).asEquivalence

/-- The coefficient-duality anti-equivalence preserves and reflects
categorical indecomposability. -/
theorem finiteCoefficientDualFunctor_indec_iff
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Indecomposable
        ((finiteCoefficientDualFunctor (k := k) (C := C)).obj
          (Opposite.op M)) ↔
      Indecomposable M := by
  rw [MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence,
    MagnitudeConjecture.CategoryTheory.indecomposable_op_iff]

end MagnitudeConjecture.CoveringHom
