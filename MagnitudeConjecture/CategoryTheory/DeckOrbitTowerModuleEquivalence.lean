import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDeckShift
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Module equivalences over strict orbit towers

A linear equivalence of base categories acts on covariant linear modules by
precomposition.  If its object map is a literal bijection, this equivalence
restricts further to modules with finite object support.  Applied to strict
orbit-tower flattening, this identifies the linear and finite-dimensional
module categories over the two-stage and direct orbit skeletons.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u₁ v₁ u₂ v₂ uK uM

section Linear

variable {R : Type uK} [CommRing R]
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]

/-- Precomposition with the forward functor of a linear equivalence induces
an equivalence from linear modules on the target to linear modules on the
source. -/
noncomputable def linearModuleCongrEquivalence
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] :
    LinearModuleCategory.{u₂, v₂, uK, uM} (C := D) R ≌
      LinearModuleCategory.{u₁, v₁, uK, uM} (C := C) R := by
  let ef : (D ⥤ ModuleCat.{uM} R) ≌ (C ⥤ ModuleCat.{uM} R) :=
    e.symm.congrLeft
  apply ef.congrFullSubcategory
  ext M
  change ((e.functor ⋙ M).Additive ∧ (e.functor ⋙ M).Linear R) ↔
    (M.Additive ∧ M.Linear R)
  constructor
  · intro h
    letI : (e.functor ⋙ M).Additive := h.1
    letI : (e.functor ⋙ M).Linear R := h.2
    exact ⟨Functor.additive_of_full_essSurj_comp e.functor M,
      Functor.linear_of_full_essSurj_comp e.functor M⟩
  · intro h
    letI : M.Additive := h.1
    letI : M.Linear R := h.2
    exact ⟨inferInstance, inferInstance⟩

@[simp]
theorem linearModuleCongrEquivalence_functor_obj_obj
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R]
    (M : LinearModuleCategory.{u₂, v₂, uK, uM} (C := D) R) :
    ((linearModuleCongrEquivalence (R := R) e).functor.obj M).obj =
      e.functor ⋙ M.obj := rfl

instance linearModuleCongrEquivalence_functor_additive
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] :
    (linearModuleCongrEquivalence (R := R) e).functor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    rfl

instance linearModuleCongrEquivalence_functor_linear
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] :
    (linearModuleCongrEquivalence (R := R) e).functor.Linear R where
  map_smul α r := by
    apply ObjectProperty.hom_ext
    rfl

end Linear

section Finite

variable {k : Type uK} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]

/-- If the forward functor of a linear equivalence has a specified bijective
object map, precomposition restricts to an equivalence of finite-dimensional
modules with finite literal object support. -/
noncomputable def finiteDimensionalModuleCongrEquivalence
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (eobj : C ≃ D) (hobj : ∀ X, e.functor.obj X = eobj X) :
    FiniteDimensionalModuleCategory.{u₂, v₂, uK, uM} (C := D) k ≌
      FiniteDimensionalModuleCategory.{u₁, v₁, uK, uM} (C := C) k := by
  let elin :
      LinearModuleCategory.{u₂, v₂, uK, uM} (C := D) k ≌
        LinearModuleCategory.{u₁, v₁, uK, uM} (C := C) k :=
    linearModuleCongrEquivalence (R := k) e
  apply elin.congrFullSubcategory
  ext M
  change
    ((∀ X : C, FiniteDimensional k (M.obj.obj (e.functor.obj X))) ∧
      (moduleSupport k (e.functor ⋙ M.obj)).Finite) ↔
    ((∀ Y : D, FiniteDimensional k (M.obj.obj Y)) ∧
      (moduleSupport k M.obj).Finite)
  have hsupp : moduleSupport k (e.functor ⋙ M.obj) =
      eobj ⁻¹' moduleSupport k M.obj := by
    ext X
    change Nontrivial (M.obj.obj (e.functor.obj X)) ↔
      Nontrivial (M.obj.obj (eobj X))
    rw [hobj X]
  constructor
  · rintro ⟨hpoint, hsupport⟩
    constructor
    · intro Y
      let X := eobj.symm Y
      have hXY : e.functor.obj X = Y := by
        rw [hobj]
        exact eobj.apply_symm_apply Y
      rw [← hXY]
      exact hpoint X
    · have himage : eobj '' moduleSupport k (e.functor ⋙ M.obj) =
          moduleSupport k M.obj := by
        ext Y
        constructor
        · rintro ⟨X, hX, rfl⟩
          rw [hsupp] at hX
          exact hX
        · intro hY
          refine ⟨eobj.symm Y, ?_, eobj.apply_symm_apply Y⟩
          rw [hsupp]
          simpa using hY
      rw [← himage]
      exact hsupport.image eobj
  · rintro ⟨hpoint, hsupport⟩
    constructor
    · intro X
      rw [hobj X]
      exact hpoint (eobj X)
    · rw [hsupp]
      exact hsupport.preimage eobj.injective.injOn

/-- Over finite object types, every literal object support is finite, so an
arbitrary linear equivalence of base categories induces an equivalence of
finite-dimensional module categories without choosing a bijection of object
types. -/
noncomputable def finiteDimensionalModuleCongrEquivalenceOfFinite
    [Finite C] [Finite D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k] :
    FiniteDimensionalModuleCategory.{u₂, v₂, uK, uM} (C := D) k ≌
      FiniteDimensionalModuleCategory.{u₁, v₁, uK, uM} (C := C) k := by
  let elin :
      LinearModuleCategory.{u₂, v₂, uK, uM} (C := D) k ≌
        LinearModuleCategory.{u₁, v₁, uK, uM} (C := C) k :=
    linearModuleCongrEquivalence (R := k) e
  apply elin.congrFullSubcategory
  ext M
  change
    ((∀ X : C, FiniteDimensional k (M.obj.obj (e.functor.obj X))) ∧
      (moduleSupport k (e.functor ⋙ M.obj)).Finite) ↔
    ((∀ Y : D, FiniteDimensional k (M.obj.obj Y)) ∧
      (moduleSupport k M.obj).Finite)
  constructor
  · rintro ⟨hpoint, _⟩
    constructor
    · intro Y
      letI : FiniteDimensional k
          (M.obj.obj ((e.inverse ⋙ e.functor).obj Y)) :=
        hpoint (e.inverse.obj Y)
      exact (M.obj.mapIso (e.counitIso.app Y)).toLinearEquiv.finiteDimensional
    · exact Set.toFinite _
  · rintro ⟨hpoint, _⟩
    exact ⟨fun X ↦ hpoint (e.functor.obj X), Set.toFinite _⟩

@[simp]
theorem finiteDimensionalModuleCongrEquivalence_functor_obj_obj_obj
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (eobj : C ≃ D) (hobj : ∀ X, e.functor.obj X = eobj X)
    (M : FiniteDimensionalModuleCategory.{u₂, v₂, uK, uM} (C := D) k) :
    ((finiteDimensionalModuleCongrEquivalence
      (k := k) e eobj hobj).functor.obj M).obj.obj =
        e.functor ⋙ M.obj.obj := rfl

instance finiteDimensionalModuleCongrEquivalence_functor_additive
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (eobj : C ≃ D) (hobj : ∀ X, e.functor.obj X = eobj X) :
    (finiteDimensionalModuleCongrEquivalence
      (k := k) e eobj hobj).functor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (linearModuleCongrEquivalence (R := k) e).functor.map_add

instance finiteDimensionalModuleCongrEquivalence_functor_linear
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k]
    (eobj : C ≃ D) (hobj : ∀ X, e.functor.obj X = eobj X) :
    (finiteDimensionalModuleCongrEquivalence
      (k := k) e eobj hobj).functor.Linear k where
  map_smul α r := by
    apply ObjectProperty.hom_ext
    exact (linearModuleCongrEquivalence (R := k) e).functor.map_smul r α.hom

instance finiteDimensionalModuleCongrEquivalenceOfFinite_functor_additive
    [Finite C] [Finite D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k] :
    (finiteDimensionalModuleCongrEquivalenceOfFinite
      (k := k) e).functor.Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (linearModuleCongrEquivalence (R := k) e).functor.map_add

instance finiteDimensionalModuleCongrEquivalenceOfFinite_functor_linear
    [Finite C] [Finite D]
    (e : C ≌ D) [e.functor.Additive] [e.functor.Linear k] :
    (finiteDimensionalModuleCongrEquivalenceOfFinite
      (k := k) e).functor.Linear k where
  map_smul α r := by
    apply ObjectProperty.hom_ext
    exact (linearModuleCongrEquivalence (R := k) e).functor.map_smul r α.hom

end Finite

end MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)

section Linear

variable {R : Type uK} [CommRing R]
variable [CategoryTheory.Linear R C]
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear R]

/-- Linear modules over the direct strict orbit skeleton are equivalent to
linear modules over the two-stage strict orbit skeleton. -/
noncomputable def deckOrbitTowerLinearModuleEquivalence
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := R)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := R)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := R) N
    LinearModuleCategory.{u, max v w, uK, uM}
        (C := DeckOrbitSkeleton C G) R ≌
      LinearModuleCategory.{u, max v w, uK, uM}
        (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N)) R := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := R)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := R)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := R) N
  let e := D.deckOrbitTowerEquivalence (k := R) N
  letI : e.functor.Additive := by
    change (D.deckOrbitTowerFlattenFunctor (k := R) N).Additive
    infer_instance
  letI : e.functor.Linear R := by
    change (D.deckOrbitTowerFlattenFunctor (k := R) N).Linear R
    infer_instance
  exact linearModuleCongrEquivalence (R := R) e

end Linear

section Finite

variable {k : Type uK} [Field k]
variable [CategoryTheory.Linear k C]
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Finite-dimensional modules over the direct strict orbit skeleton are
equivalent to finite-dimensional modules over the two-stage strict orbit
skeleton. -/
noncomputable def deckOrbitTowerFiniteDimensionalModuleEquivalence
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    FiniteDimensionalModuleCategory.{u, max v w, uK, uM}
        (C := DeckOrbitSkeleton C G) k ≌
      FiniteDimensionalModuleCategory.{u, max v w, uK, uM}
        (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N)) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  let e := D.deckOrbitTowerEquivalence (k := k) N
  letI : e.functor.Additive := by
    change (D.deckOrbitTowerFlattenFunctor (k := k) N).Additive
    infer_instance
  letI : e.functor.Linear k := by
    change (D.deckOrbitTowerFlattenFunctor (k := k) N).Linear k
    infer_instance
  exact finiteDimensionalModuleCongrEquivalence (k := k) e
    (MagnitudeConjecture.CoveringAction.orbitTowerEquiv N)
    (D.deckOrbitTowerFlattenFunctor_obj (k := k) N)

end Finite

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
