import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleBiproducts
import MagnitudeConjecture.CategoryTheory.IdempotentCompleteFullSubcategory
import MagnitudeConjecture.CategoryTheory.IndecomposableFiniteEnd
import Mathlib.CategoryTheory.Idempotents.FunctorCategories

/-!
# Local endomorphism rings of finite-dimensional linear modules

The category of finite-support pointwise finite-dimensional linear functors
is closed under retracts inside the ambient functor category.  It is therefore
idempotent-complete.  Evaluation on the finite support embeds each
endomorphism space into a finite product of finite-dimensional pointwise
endomorphism spaces.  Hence an indecomposable object has local endomorphism
ring by the generic finite-dimensional Fitting criterion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v uK uM

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (k : Type uK) [Field k] [CategoryTheory.Linear k C]

/-- Additivity and linearity of a module-valued functor are preserved by
retracts. -/
instance isLinearModule_stableUnderRetracts :
    (IsLinearModule.{u, v, uK, uM} (C := C) k).IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    letI : Y.Additive := hY.1
    letI : Y.Linear k := hY.2
    constructor
    · constructor
      intro A B f g
      apply (cancel_mono (h.i.app B)).1
      simp only [h.i.naturality, Y.map_add,
        Preadditive.comp_add, Preadditive.add_comp]
    · constructor
      intro A B f r
      apply (cancel_mono (h.i.app B)).1
      simp only [h.i.naturality, Y.map_smul,
        CategoryTheory.Linear.comp_smul, CategoryTheory.Linear.smul_comp]

/-- The category of linear module-valued functors is idempotent-complete. -/
instance linearModuleCategory_isIdempotentComplete :
    IsIdempotentComplete
      (LinearModuleCategory.{u, v, uK, uM} (C := C) k) :=
  isIdempotentComplete_fullSubcategory_of_stableUnderRetracts
    (IsLinearModule.{u, v, uK, uM} (C := C) k)

/-- Pointwise finite-dimensionality and finite object support are preserved
by retracts of linear modules. -/
instance isFiniteDimensionalModule_stableUnderRetracts :
    (IsFiniteDimensionalModule.{u, v, uK, uM}
      (C := C) k).IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    let Q := IsLinearModule.{u, v, uK, uM} (C := C) k
    constructor
    · intro Z
      let E : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
          ModuleCat.{uM} k :=
        Q.ι ⋙ (evaluation C (ModuleCat.{uM} k)).obj Z
      let hZ := h.map E
      have hinj : Function.Injective hZ.i.hom :=
        (ModuleCat.mono_iff_injective hZ.i).mp inferInstance
      letI : FiniteDimensional k (E.obj Y) := hY.1 Z
      exact FiniteDimensional.of_injective hZ.i.hom hinj
    · refine hY.2.subset ?_
      intro Z hZ
      let E : LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
          ModuleCat.{uM} k :=
        Q.ι ⋙ (evaluation C (ModuleCat.{uM} k)).obj Z
      let hZr := h.map E
      have hinj : Function.Injective hZr.i.hom :=
        (ModuleCat.mono_iff_injective hZr.i).mp inferInstance
      letI : Nontrivial (E.obj X) := hZ
      exact hinj.nontrivial

/-- The category of finite-support pointwise finite-dimensional linear
modules is idempotent-complete. -/
instance finiteDimensionalModuleCategory_isIdempotentComplete :
    IsIdempotentComplete
      (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :=
  isIdempotentComplete_fullSubcategory_of_stableUnderRetracts
    (IsFiniteDimensionalModule.{u, v, uK, uM} (C := C) k)

/-- Evaluation on the finite support of a module gives a linear map from its
endomorphism space into the product of its pointwise endomorphism spaces. -/
noncomputable def finiteDimensionalModuleEndEvaluation
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    End M →ₗ[k]
      ((X : moduleSupport k M.obj.obj) → End (M.obj.obj.obj X.1)) where
  toFun f X := f.hom.hom.app X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation on the support detects a natural endomorphism. -/
theorem finiteDimensionalModuleEndEvaluation_injective
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    Function.Injective (finiteDimensionalModuleEndEvaluation k M) := by
  intro f g hfg
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext Z
  by_cases hZ : Nontrivial (M.obj.obj.obj Z)
  · exact congrFun hfg ⟨Z, hZ⟩
  · haveI : Subsingleton (M.obj.obj.obj Z) :=
      not_nontrivial_iff_subsingleton.mp hZ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _

/-- Endomorphism spaces of finite-support pointwise finite-dimensional
modules are finite-dimensional. -/
noncomputable instance finiteDimensionalModuleEnd_finiteDimensional
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    FiniteDimensional k (End M) := by
  letI : Fintype (moduleSupport k M.obj.obj) := M.property.2.fintype
  letI (X : moduleSupport k M.obj.obj) :
      FiniteDimensional k (End (M.obj.obj.obj X.1)) :=
    Module.Finite.equiv
      (ModuleCat.homLinearEquiv (R := k)).symm
  exact FiniteDimensional.of_injective
    (finiteDimensionalModuleEndEvaluation k M)
    (finiteDimensionalModuleEndEvaluation_injective k M)

/-- An indecomposable finite-support pointwise finite-dimensional linear
module has local endomorphism ring. -/
theorem finiteDimensionalModule_end_isLocalRing
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hM : Indecomposable M) : IsLocalRing (End M) :=
  MagnitudeConjecture.CategoryTheory.end_isLocalRing_of_finiteDimensional_indecomposable
    (k := k) M hM

/-- The finite-dimensional full-subcategory inclusion identifies the two
`k`-algebra structures on endomorphism rings. -/
noncomputable def finiteDimensionalModuleEndLinearModuleAlgEquiv
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    End M ≃ₐ[k] End M.obj := by
  let J := (IsFiniteDimensionalModule (C := C) k).ι
  exact
    { toFun := J.map
      invFun := J.preimage
      left_inv := J.preimage_map
      right_inv := J.map_preimage
      map_add' := by
        intro f g
        exact J.map_add
      map_mul' := fun f g ↦ J.map_comp g f
      commutes' := by
        intro c
        change J.map (c • 𝟙 M) = c • 𝟙 (J.obj M)
        rw [J.map_smul, J.map_id] }

/-- Endomorphisms of the underlying linear module of a finite-dimensional
module form a finite-dimensional vector space. -/
noncomputable instance finiteDimensionalModuleLinearModuleEnd_finiteDimensional
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k) :
    FiniteDimensional k (End M.obj) :=
  (finiteDimensionalModuleEndLinearModuleAlgEquiv k M).toLinearEquiv.finiteDimensional

/-- Localness of a finite-dimensional module's endomorphism ring passes to
its underlying linear module. -/
theorem finiteDimensionalModule_linearModule_end_isLocalRing
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (hM : Indecomposable M) : IsLocalRing (End M.obj) := by
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hM
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
    (finiteDimensionalModuleEndLinearModuleAlgEquiv k M).toRingEquiv

end MagnitudeConjecture.CoveringHom
