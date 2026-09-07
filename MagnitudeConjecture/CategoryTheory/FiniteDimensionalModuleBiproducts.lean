import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite biproducts of finite-dimensional modules

Finite products of additive linear functors are again additive and linear.
For a finite family of finite-dimensional modules, the pointwise product is
finite-dimensional and its object support is contained in the finite union of
the supports of the factors.  Consequently both the linear-module category
and its finite-dimensional full subcategory have finite biproducts.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [CategoryTheory.Linear k C]

set_option backward.isDefEq.respectTransparency false in
/-- A finite product of additive linear module-valued functors is additive
and linear. -/
theorem isLinearModule_limit
    {J : Type} [Finite J]
    (F : Discrete J ⥤ C ⥤ ModuleCat.{uM} k) [HasLimit F]
    (hF : ∀ j, IsLinearModule (C := C) k (F.obj j)) :
    IsLinearModule (C := C) k (limit F) := by
  letI (j : Discrete J) : (F.obj j).Additive := (hF j).1
  letI (j : Discrete J) : (F.obj j).Linear k := (hF j).2
  constructor
  · constructor
    intro X Y f g
    let eY := limitObjIsoLimitCompEvaluation F Y
    apply (cancel_mono eY.hom).1
    apply (limit.isLimit (F ⋙ (evaluation C (ModuleCat.{uM} k)).obj Y)).hom_ext
    intro j
    let pY := limit.π (F ⋙
      (evaluation C (ModuleCat.{uM} k)).obj Y) j
    calc
      ((limit F).map (f + g) ≫ eY.hom) ≫ pY =
          (limit F).map (f + g) ≫ (limit.π F j).app Y := by
            rw [Category.assoc,
              limitObjIsoLimitCompEvaluation_hom_π]
      _ =
          (limit.π F j).app X ≫ (F.obj j).map (f + g) := by
            exact (limit.π F j).naturality (f + g)
      _ = (limit.π F j).app X ≫
          ((F.obj j).map f + (F.obj j).map g) := by
            rw [(F.obj j).map_add]
      _ = (limit.π F j).app X ≫ (F.obj j).map f +
          (limit.π F j).app X ≫ (F.obj j).map g := by
            rw [Preadditive.comp_add]
      _ = (limit F).map f ≫ (limit.π F j).app Y +
          (limit F).map g ≫ (limit.π F j).app Y := by
            rw [(limit.π F j).naturality, (limit.π F j).naturality]
      _ = ((limit F).map f + (limit F).map g) ≫
          (limit.π F j).app Y := by
            rw [Preadditive.add_comp]
      _ = (((limit F).map f + (limit F).map g) ≫ eY.hom) ≫ pY := by
            rw [Category.assoc,
              limitObjIsoLimitCompEvaluation_hom_π]
  · constructor
    intro X Y f r
    let eY := limitObjIsoLimitCompEvaluation F Y
    apply (cancel_mono eY.hom).1
    apply (limit.isLimit (F ⋙ (evaluation C (ModuleCat.{uM} k)).obj Y)).hom_ext
    intro j
    let pY := limit.π (F ⋙
      (evaluation C (ModuleCat.{uM} k)).obj Y) j
    calc
      ((limit F).map (r • f) ≫ eY.hom) ≫ pY =
          (limit F).map (r • f) ≫ (limit.π F j).app Y := by
            rw [Category.assoc,
              limitObjIsoLimitCompEvaluation_hom_π]
      _ =
          (limit.π F j).app X ≫ (F.obj j).map (r • f) := by
            exact (limit.π F j).naturality (r • f)
      _ = (limit.π F j).app X ≫ (r • (F.obj j).map f) := by
            rw [(F.obj j).map_smul]
      _ = r • ((limit.π F j).app X ≫ (F.obj j).map f) := by
            rw [CategoryTheory.Linear.comp_smul]
      _ = r • ((limit F).map f ≫ (limit.π F j).app Y) := by
            rw [(limit.π F j).naturality]
      _ = (r • (limit F).map f) ≫ (limit.π F j).app Y := by
            rw [CategoryTheory.Linear.smul_comp]
      _ = ((r • (limit F).map f) ≫ eY.hom) ≫ pY := by
            rw [Category.assoc,
              limitObjIsoLimitCompEvaluation_hom_π]

instance isLinearModule_closedUnderFiniteProducts :
    (IsLinearModule (C := C) k).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    constructor
    rintro X ⟨p⟩
    exact (IsLinearModule (C := C) k).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (limit.isLimit p.diag) p.isLimit)
      (isLinearModule_limit p.diag p.prop_diag_obj)

instance linearModuleCategory_hasFiniteBiproducts :
    HasFiniteBiproducts
      (LinearModuleCategory.{u, v, uK, uM} (C := C) k) := by
  constructor
  intro n
  constructor
  intro f
  letI : HasLimit
      (Discrete.functor f ⋙ (IsLinearModule (C := C) k).ι) := inferInstance
  letI : HasLimit (Discrete.functor f) :=
    hasLimit_of_closedUnderLimits
      (Discrete (Fin n)) (IsLinearModule (C := C) k) (Discrete.functor f)
  exact HasBiproduct.of_hasProduct f

instance linearModuleCategory_hasBinaryBiproducts :
    HasBinaryBiproducts
      (LinearModuleCategory.{u, v, uK, uM} (C := C) k) :=
  hasBinaryBiproducts_of_finite_biproducts _

instance isFiniteDimensionalModule_closedUnderFiniteProducts :
    (IsFiniteDimensionalModule.{u, v, uK, uM}
      (C := C) k).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    constructor
    rintro M ⟨p⟩
    constructor
    · intro X
      let I : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
          (C ⥤ ModuleCat.{uM} k) := (IsLinearModule (C := C) k).ι
      let E := (evaluation C (ModuleCat.{uM} k)).obj X
      let q := p.toLimitPresentation.map I
      have qX_isLimit : IsLimit (E.mapCone q.cone) :=
        isLimitOfPreserves E q.isLimit
      let fX : J → ModuleCat.{uM} k := fun j ↦
        E.obj (q.diag.obj ⟨j⟩)
      let α : q.diag ⋙ E ≅ Discrete.functor fX :=
        Discrete.natIsoFunctor
      have qX'_isLimit : IsLimit
          ((Cone.postcompose α.hom).obj (E.mapCone q.cone)) :=
        (IsLimit.postcomposeHomEquiv α (E.mapCone q.cone)).symm qX_isLimit
      let e : M.obj.obj X ≅ ModuleCat.of k (∀ j, fX j) :=
        qX'_isLimit.conePointUniqueUpToIso
          (ModuleCat.HasLimit.productLimitCone fX).isLimit
      letI (j : J) : FiniteDimensional k (fX j) :=
        (p.prop_diag_obj ⟨j⟩).1 X
      exact e.symm.toLinearEquiv.finiteDimensional
    · let S : Set C := ⋃ j : J,
          moduleSupport k (p.diag.obj ⟨j⟩).obj
      refine (Set.finite_iUnion fun j ↦ (p.prop_diag_obj ⟨j⟩).2).subset ?_
      intro X hX
      change X ∈ S
      let I : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
          (C ⥤ ModuleCat.{uM} k) := (IsLinearModule (C := C) k).ι
      let E := (evaluation C (ModuleCat.{uM} k)).obj X
      let q := p.toLimitPresentation.map I
      have qX_isLimit : IsLimit (E.mapCone q.cone) :=
        isLimitOfPreserves E q.isLimit
      let fX : J → ModuleCat.{uM} k := fun j ↦
        E.obj (q.diag.obj ⟨j⟩)
      let α : q.diag ⋙ E ≅ Discrete.functor fX :=
        Discrete.natIsoFunctor
      have qX'_isLimit : IsLimit
          ((Cone.postcompose α.hom).obj (E.mapCone q.cone)) :=
        (IsLimit.postcomposeHomEquiv α (E.mapCone q.cone)).symm qX_isLimit
      let e : M.obj.obj X ≅ ModuleCat.of k (∀ j, fX j) :=
        qX'_isLimit.conePointUniqueUpToIso
          (ModuleCat.HasLimit.productLimitCone fX).isLimit
      have hPi : Nontrivial (∀ j, fX j) :=
        e.toLinearEquiv.toEquiv.nontrivial_congr.mp hX
      obtain ⟨a, b, hab⟩ := exists_pair_ne (∀ j, fX j)
      have hj : ∃ j, a j ≠ b j := by
        by_contra h
        push Not at h
        exact hab (funext h)
      obtain ⟨j, hj⟩ := hj
      haveI : Nontrivial (fX j) := ⟨⟨a j, b j, hj⟩⟩
      apply Set.mem_iUnion_of_mem j
      change Nontrivial (fX j)
      exact inferInstance

instance finiteDimensionalModuleCategory_hasFiniteBiproducts :
    HasFiniteBiproducts
      (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) := by
  constructor
  intro n
  constructor
  intro f
  let P := IsFiniteDimensionalModule.{u, v, uK, uM} (C := C) k
  letI : HasLimit (Discrete.functor (fun j ↦ P.ι.obj (f j))) := inferInstance
  letI : HasLimit (Discrete.functor f ⋙ P.ι) :=
    hasLimit_of_iso (Discrete.compNatIsoDiscrete f P.ι).symm
  letI : HasLimit (Discrete.functor f) :=
    hasLimit_of_closedUnderLimits (Discrete (Fin n)) P (Discrete.functor f)
  exact HasBiproduct.of_hasProduct f

instance finiteDimensionalModuleCategory_hasBinaryBiproducts :
    HasBinaryBiproducts
      (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :=
  hasBinaryBiproducts_of_finite_biproducts _

end MagnitudeConjecture.CoveringHom
