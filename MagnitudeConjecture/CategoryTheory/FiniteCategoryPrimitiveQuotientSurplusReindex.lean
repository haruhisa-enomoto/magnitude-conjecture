import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerFiniteSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitiveQuotientSurplus

/-!
# Universe-independent finite category deletion

The category algebra used by the primitive-deletion theorem is formed after
reindexing a finite object type by `Fin n`.  This keeps its objects small
without changing any Hom space.  The induced base equivalence transports
finite-dimensional module skeletons and their Auslander--Reiten surplus, so
the checked finite deletion theorem applies to a finite category in an
arbitrary object universe.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Fintype C]

/-- A finite category reindexed by a small `Fin` object type. -/
abbrev FiniteObjectModel : Type :=
  InducedCategory C (Fintype.equivFin C).symm

noncomputable instance finiteObjectModel_fintype :
    Fintype (FiniteObjectModel (C := C)) := by
  change Fintype (Fin (Fintype.card C))
  infer_instance

/-- The literal object equivalence from the small model to the original
finite category. -/
noncomputable def finiteObjectEquiv : FiniteObjectModel (C := C) ≃ C :=
  (Fintype.equivFin C).symm

/-- Reindexing by `Fin` is a linear equivalence of base categories. -/
noncomputable def finiteObjectModelEquivalence :
    FiniteObjectModel (C := C) ≌ C :=
  CategoryTheory.Equivalence.induced (finiteObjectEquiv (C := C))

noncomputable instance finiteObjectModelEquivalence_functor_additive :
    (finiteObjectModelEquivalence (C := C)).functor.Additive := by
  change (inducedFunctor (finiteObjectEquiv (C := C))).Additive
  infer_instance

noncomputable instance finiteObjectModelEquivalence_functor_linear :
    (finiteObjectModelEquivalence (C := C)).functor.Linear k := by
  change (inducedFunctor (finiteObjectEquiv (C := C))).Linear k
  infer_instance

@[simp]
theorem finiteObjectModelEquivalence_obj
    (X : FiniteObjectModel (C := C)) :
    (finiteObjectModelEquivalence (C := C)).functor.obj X =
      finiteObjectEquiv (C := C) X :=
  rfl

/-- The induced equivalence gives the corresponding equivalence of
finite-dimensional module categories. -/
noncomputable def finiteObjectModelModuleEquivalence :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k ≌
      FiniteDimensionalModuleCategory.{0, v, v, v}
        (C := FiniteObjectModel (C := C)) k :=
  finiteDimensionalModuleCongrEquivalence
    (k := k) (finiteObjectModelEquivalence (C := C))
      (finiteObjectEquiv (C := C))
      (finiteObjectModelEquivalence_obj (C := C))

noncomputable instance finiteObjectModelModuleEquivalence_functor_additive :
    (finiteObjectModelModuleEquivalence (k := k) (C := C)).functor.Additive := by
  change (finiteDimensionalModuleCongrEquivalence
    (k := k) (finiteObjectModelEquivalence (C := C))
      (finiteObjectEquiv (C := C))
      (finiteObjectModelEquivalence_obj (C := C))).functor.Additive
  infer_instance

/-- A deletion category of a finite object type again has finitely many
objects. -/
noncomputable instance ObjectDeletion.deletionCategory_finite
    [Finite C] (S : Set C) :
    Finite (ObjectDeletion.DeletionCategory (k := k) C S) := by
  let f : ObjectDeletion.DeletionCategory (k := k) C S → C :=
    fun X ↦ X.obj.as
  exact Finite.of_injective f (by
    intro X Y hXY
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    exact hXY)

/-- Reindexing preserves finite-dimensional covariant representables. -/
theorem finiteObjectModel_finiteCovariantRepresentables
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (X : FiniteObjectModel (C := C)) :
    IsFiniteDimensionalModule (C := FiniteObjectModel (C := C)) k
      (linearCoyonedaLinearModule (k := k) X) := by
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    letI : FiniteDimensional k
        ((Fintype.equivFin C).symm X ⟶
          (Fintype.equivFin C).symm Y) := by
      change FiniteDimensional k
        (finiteObjectEquiv (C := C) X ⟶
          finiteObjectEquiv (C := C) Y)
      exact (hP (finiteObjectEquiv (C := C) X)).1
        (finiteObjectEquiv (C := C) Y)
    exact FiniteDimensional.of_injective
      (InducedCategory.homLinearEquiv (R := k)).toLinearMap
      (InducedCategory.homLinearEquiv (R := k)).injective
  · exact Set.toFinite _

/-- Endomorphism rings are unchanged by the induced finite reindexing. -/
def finiteObjectModelEndRingEquiv
    (X : FiniteObjectModel (C := C)) :
    End X ≃+* End (finiteObjectEquiv (C := C) X) where
  toAddEquiv := InducedCategory.homAddEquiv
  map_mul' _ _ := rfl

/-- Local vertex endomorphism rings pass to the finite object model. -/
theorem finiteObjectModel_localEndomorphismRings
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (X : FiniteObjectModel (C := C)) : IsLocalRing (End X) := by
  letI : IsLocalRing (End (finiteObjectEquiv (C := C) X)) :=
    hlocal (finiteObjectEquiv (C := C) X)
  let e := finiteObjectModelEndRingEquiv (C := C) X
  exact
    { toNontrivial := e.toEquiv.nontrivial
      isUnit_or_isUnit_of_add_one := by
        intro a b hab
        have hab' : e a + e b = 1 := by
          rw [← e.map_add, hab, e.map_one]
        exact (IsLocalRing.isUnit_or_isUnit_of_add_one hab').imp
          (fun ha ↦ (MulEquiv.isUnit_map e).mp ha)
          (fun hb ↦ (MulEquiv.isUnit_map e).mp hb) }

/-- Skeletality passes to the finite object model. -/
theorem finiteObjectModel_skeletal (hC : Skeletal C) :
    Skeletal (FiniteObjectModel (C := C)) := by
  intro X Y hXY
  apply (finiteObjectEquiv (C := C)).injective
  exact hC (hXY.map
    (finiteObjectModelEquivalence (C := C)).functor.mapIso)

/-- A complete finite skeleton supplies the pointwise form of local
representation-finiteness. -/
theorem isLocallyRepresentationFinite_of_finiteSkeleton
    (S : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := C)) :
    IsLocallyRepresentationFinite (k := k) (C := C) := by
  intro X
  refine ⟨
    { n := S.n
      obj := S.obj
      indecomposable := S.indecomposable
      covers := ?_ }⟩
  intro Y hY _
  obtain ⟨i, ⟨e⟩⟩ := S.complete Y hY
  exact ⟨i, ⟨e.symm⟩⟩

/-- Local representation-finiteness passes to the finite object model. -/
theorem finiteObjectModel_isLocallyRepresentationFinite
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    IsLocallyRepresentationFinite
      (k := k) (C := FiniteObjectModel (C := C)) := by
  let E := finiteObjectModelModuleEquivalence (k := k) (C := C)
  let S := (finiteCategoryModuleIndecomposableSkeleton hrep).mapEquivalence E
  exact isLocallyRepresentationFinite_of_finiteSkeleton S

/-- Directedness of the finite module category passes to the finite object
model. -/
theorem finiteObjectModel_hasAcyclicFiniteModuleNonzeroNonisomorphisms
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C)) :
    HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := FiniteObjectModel (C := C)) := by
  let E := finiteObjectModelModuleEquivalence (k := k) (C := C)
  letI : E.inverse.Additive := inferInstance
  exact hasAcyclicFiniteModuleNonzeroNonisomorphisms_of_equivalence
    E.inverse H

namespace finiteCategoryProjectiveGenerator

variable [IsAlgClosed k]

/-- Literal singleton deletion cannot increase surplus for a finite
representation-directed category in an arbitrary object universe. -/
theorem singletonDeletion_surplus_le_of_fintype
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hskel : Skeletal C)
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C))
    (X : C)
    (T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
    (Tdeleted : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C))) :
    letI := enoughProjectives_of_finiteRepresentables hP
    letI := enoughProjectives_of_finiteRepresentables
      (fun Y ↦ ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
        (k := k) C hP ({X} : Set C) Y)
    @ARCount.surplus (Fin Tdeleted.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity
          Tdeleted.toFiniteRightTauCategoryData)
        Tdeleted.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) ≤
      @ARCount.surplus (Fin T.n) inferInstance
        (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) := by
  let C₀ := FiniteObjectModel (C := C)
  let e₀ := finiteObjectEquiv (C := C)
  let E₀ := finiteObjectModelEquivalence (C := C)
  let x₀ : C₀ := e₀.symm X
  let hP₀ := finiteObjectModel_finiteCovariantRepresentables
    (k := k) (C := C) hP
  let hlocal₀ := finiteObjectModel_localEndomorphismRings
    (C := C) hlocal
  let hskel₀ := finiteObjectModel_skeletal (C := C) hskel
  let hrep₀ := finiteObjectModel_isLocallyRepresentationFinite
    (k := k) (C := C) hrep
  let H₀ := finiteObjectModel_hasAcyclicFiniteModuleNonzeroNonisomorphisms
    (k := k) (C := C) H
  let E := finiteObjectModelModuleEquivalence (k := k) (C := C)
  letI : E.functor.Additive := by
    change (finiteObjectModelModuleEquivalence
      (k := k) (C := C)).functor.Additive
    infer_instance
  let T₀ := T.mapEquivalence E
  have hobj₀ : Function.Bijective E₀.functor.obj := by
    change Function.Bijective e₀
    exact e₀.bijective
  have hx₀ : E₀.functor.obj x₀ = X := by
    change e₀ (e₀.symm X) = X
    exact e₀.apply_symm_apply X
  let e₁ := ObjectDeletion.singletonDeletionEquivalence
    (k := k) (C := C₀) E₀ hobj₀ x₀
  letI : e₁.functor.Additive := inferInstance
  letI : e₁.functor.Linear k := inferInstance
  have hset : ({E₀.functor.obj x₀} : Set C) = {X} := by
    rw [hx₀]
  let e₂ := ObjectDeletion.deletionEquivalenceOfEq (k := k) C hset
  letI : e₂.functor.Additive := inferInstance
  letI : e₂.functor.Linear k := inferInstance
  let EdelBase := e₁.trans e₂
  letI : EdelBase.functor.Additive := by
    change (e₁.functor ⋙ e₂.functor).Additive
    infer_instance
  letI : EdelBase.functor.Linear k := by
    change (e₁.functor ⋙ e₂.functor).Linear k
    infer_instance
  let Edel := finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) EdelBase
  letI : Edel.functor.Additive := by
    change (finiteDimensionalModuleCongrEquivalenceOfFinite
      (k := k) EdelBase).functor.Additive
    infer_instance
  let Tdeleted₀ := Tdeleted.mapEquivalence Edel
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  let hPdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP ({X} : Set C) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, v, v, v} (C := C₀) k) :=
    enoughProjectives_of_finiteRepresentables hP₀
  let hPdeleted₀ := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C₀ hP₀ ({x₀} : Set C₀) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, v, v, v}
        (C := ObjectDeletion.DeletionCategory
          (k := k) C₀ ({x₀} : Set C₀)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted₀
  have hsmall := singletonDeletion_surplus_le hP₀ hlocal₀ hskel₀
    hrep₀ H₀ x₀ T₀ Tdeleted₀
  rw [T.surplus_mapEquivalence E,
    Tdeleted.surplus_mapEquivalence Edel] at hsmall
  exact hsmall

/-- Equality in literal singleton deletion forces one-dimensional fiber at
the deleted object for a finite representation-directed category in an
arbitrary object universe. -/
theorem finrank_obj_eq_one_of_singletonDeletion_surplus_eq_of_fintype
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hskel : Skeletal C)
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms (k := k) (C := C))
    (X : C)
    (T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))
    (Tdeleted : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)))
    (hEquality :
      letI := enoughProjectives_of_finiteRepresentables hP
      letI := enoughProjectives_of_finiteRepresentables
        (fun Y ↦ ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
          (k := k) C hP ({X} : Set C) Y)
      @ARCount.surplus (Fin Tdeleted.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity
            Tdeleted.toFiniteRightTauCategoryData)
          Tdeleted.toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) =
        @ARCount.surplus (Fin T.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hMX : ¬ IsZero (M.obj.obj.obj X)) :
    Module.finrank k (M.obj.obj.obj X) = 1 := by
  let C₀ := FiniteObjectModel (C := C)
  let e₀ := finiteObjectEquiv (C := C)
  let E₀ := finiteObjectModelEquivalence (C := C)
  let x₀ : C₀ := e₀.symm X
  let hP₀ := finiteObjectModel_finiteCovariantRepresentables
    (k := k) (C := C) hP
  let hlocal₀ := finiteObjectModel_localEndomorphismRings
    (C := C) hlocal
  let hskel₀ := finiteObjectModel_skeletal (C := C) hskel
  let hrep₀ := finiteObjectModel_isLocallyRepresentationFinite
    (k := k) (C := C) hrep
  let H₀ := finiteObjectModel_hasAcyclicFiniteModuleNonzeroNonisomorphisms
    (k := k) (C := C) H
  let E := finiteObjectModelModuleEquivalence (k := k) (C := C)
  letI : E.functor.Additive := by
    change (finiteObjectModelModuleEquivalence
      (k := k) (C := C)).functor.Additive
    infer_instance
  let T₀ := T.mapEquivalence E
  have hobj₀ : Function.Bijective E₀.functor.obj := by
    change Function.Bijective e₀
    exact e₀.bijective
  have hx₀ : E₀.functor.obj x₀ = X := by
    change e₀ (e₀.symm X) = X
    exact e₀.apply_symm_apply X
  let e₁ := ObjectDeletion.singletonDeletionEquivalence
    (k := k) (C := C₀) E₀ hobj₀ x₀
  letI : e₁.functor.Additive := inferInstance
  letI : e₁.functor.Linear k := inferInstance
  have hset : ({E₀.functor.obj x₀} : Set C) = {X} := by
    rw [hx₀]
  let e₂ := ObjectDeletion.deletionEquivalenceOfEq (k := k) C hset
  letI : e₂.functor.Additive := inferInstance
  letI : e₂.functor.Linear k := inferInstance
  let EdelBase := e₁.trans e₂
  letI : EdelBase.functor.Additive := by
    change (e₁.functor ⋙ e₂.functor).Additive
    infer_instance
  letI : EdelBase.functor.Linear k := by
    change (e₁.functor ⋙ e₂.functor).Linear k
    infer_instance
  let Edel := finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) EdelBase
  letI : Edel.functor.Additive := by
    change (finiteDimensionalModuleCongrEquivalenceOfFinite
      (k := k) EdelBase).functor.Additive
    infer_instance
  let Tdeleted₀ := Tdeleted.mapEquivalence Edel
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  let hPdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP ({X} : Set C) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := ObjectDeletion.DeletionCategory (k := k) C ({X} : Set C)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, v, v, v} (C := C₀) k) :=
    enoughProjectives_of_finiteRepresentables hP₀
  let hPdeleted₀ := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C₀ hP₀ ({x₀} : Set C₀) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{0, v, v, v}
        (C := ObjectDeletion.DeletionCategory
          (k := k) C₀ ({x₀} : Set C₀)) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted₀
  have hEquality₀ :
      @ARCount.surplus (Fin Tdeleted₀.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity
            Tdeleted₀.toFiniteRightTauCategoryData)
          Tdeleted₀.toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) =
        @ARCount.surplus (Fin T₀.n) inferInstance
          (FiniteTauMatrix.arrowMultiplicity T₀.toFiniteRightTauCategoryData)
          T₀.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) := by
    rw [T.surplus_mapEquivalence E,
      Tdeleted.surplus_mapEquivalence Edel]
    exact hEquality
  have hM₀ : Indecomposable (E.functor.obj M) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor M).2 hM
  have hMX₀ : ¬ IsZero ((E.functor.obj M).obj.obj.obj x₀) := by
    change ¬ IsZero (M.obj.obj.obj (E₀.functor.obj x₀))
    rw [hx₀]
    exact hMX
  have hsmall :=
    finrank_obj_eq_one_of_singletonDeletion_surplus_eq
      hP₀ hlocal₀ hskel₀ hrep₀ H₀ x₀ T₀ Tdeleted₀ hEquality₀
        (E.functor.obj M) hM₀ hMX₀
  change Module.finrank k
      (M.obj.obj.obj (E₀.functor.obj x₀)) = 1 at hsmall
  rw [hx₀] at hsmall
  exact hsmall

end finiteCategoryProjectiveGenerator

end MagnitudeConjecture.CoveringHom
