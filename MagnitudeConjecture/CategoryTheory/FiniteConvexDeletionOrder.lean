import MagnitudeConjecture.CategoryTheory.FiniteConvexModuleLocalDensity
import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitiveQuotientSurplusReindex

/-!
# Commuting a finite convex restriction with singleton deletion

Deleting the complement of a finite control window and then its base object
is linearly equivalent to deleting the base object first and the surviving
complement second.  Both sides are literal iterated object-deletion
categories; the comparison passes through deletion by the corresponding
union of ambient object sets.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- If `U` is finite, deleting the surviving complement of `U` after any
first deletion has finitely many objects. -/
theorem iteratedComplementDeletion_finite
    (S U : Set C) (hU : U.Finite) :
    Finite (IteratedDeletionCategory (k := k) C S Uᶜ) := by
  let f : IteratedDeletionCategory (k := k) C S Uᶜ → U := fun X ↦
    ⟨X.obj.as.obj.as, by
      have hX := X.property
      change X.obj.as.obj.as ∉ Uᶜ at hX
      simpa only [Set.mem_compl_iff, not_not] using hX⟩
  letI : Finite U := hU
  exact Finite.of_injective f (by
    intro X Y hXY
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    exact congrArg Subtype.val hXY)

end MagnitudeConjecture.ObjectDeletion

namespace MagnitudeConjecture.CoveringHom.FiniteConvexModuleControlWindow

open MagnitudeConjecture.ObjectDeletion

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable {x : C}
variable {W : FiniteIndecomposableModuleFamily (k := k) (C := C)}

/-- The base object as a surviving object of the finite control category. -/
def baseObject
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    DeletionCategory (k := k) C P.objectsᶜ :=
  survivingObj (k := k) C P.objectsᶜ (by
    simpa only [Set.mem_compl_iff, not_not] using P.base_mem)

/-- In the finite control category, the singleton base object is exactly the
surviving part of the corresponding ambient singleton. -/
theorem singleton_baseObject_eq_additionalDeleted
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    ({P.baseObject C} : Set
      (DeletionCategory (k := k) C P.objectsᶜ)) =
      AdditionalDeleted (k := k) C P.objectsᶜ ({x} : Set C) := by
  ext Y
  constructor
  · intro hY
    rw [Set.mem_singleton_iff] at hY
    subst Y
    change x ∈ ({x} : Set C)
    simp
  · intro hY
    rw [Set.mem_singleton_iff]
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    change Y.obj.as = x
    change Y.obj.as ∈ ({x} : Set C) at hY
    simpa only [Set.mem_singleton_iff] using hY

/-- Deleting the finite-window complement and then the base object is
linearly equivalent to deleting the base object and then the surviving
window complement. -/
noncomputable def singletonSwapEquivalence
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    DeletionCategory (k := k)
        (DeletionCategory (k := k) C P.objectsᶜ)
        ({P.baseObject C} : Set _) ≌
      IteratedDeletionCategory (k := k) C ({x} : Set C) P.objectsᶜ := by
  let e₀ := deletionEquivalenceOfEq
    (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
      (P.singleton_baseObject_eq_additionalDeleted C)
  let e₁ := iteratedDeletionEquivalence
    (k := k) C P.objectsᶜ ({x} : Set C)
  let e₂ := deletionEquivalenceOfEq
    (k := k) C (Set.union_comm P.objectsᶜ ({x} : Set C))
  let e₃ := (iteratedDeletionEquivalence
    (k := k) C ({x} : Set C) P.objectsᶜ).symm
  exact e₀.trans (e₁.trans (e₂.trans e₃))

noncomputable instance singletonSwapEquivalence_functor_additive
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    (P.singletonSwapEquivalence C).functor.Additive := by
  let e₀ := deletionEquivalenceOfEq
    (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
      (P.singleton_baseObject_eq_additionalDeleted C)
  let e₁ := iteratedDeletionEquivalence
    (k := k) C P.objectsᶜ ({x} : Set C)
  let e₂ := deletionEquivalenceOfEq
    (k := k) C (Set.union_comm P.objectsᶜ ({x} : Set C))
  let e₃base := iteratedDeletionEquivalence
    (k := k) C ({x} : Set C) P.objectsᶜ
  letI : e₃base.functor.Additive := inferInstance
  let e₃ := e₃base.symm
  letI : e₀.functor.Additive := inferInstance
  letI : e₁.functor.Additive := inferInstance
  letI : e₂.functor.Additive := inferInstance
  letI : e₃.functor.Additive := by
    change e₃base.inverse.Additive
    infer_instance
  change (e₀.functor ⋙
    (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor))).Additive
  infer_instance

noncomputable instance singletonSwapEquivalence_functor_linear
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    (P.singletonSwapEquivalence C).functor.Linear k := by
  let e₀ := deletionEquivalenceOfEq
    (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
      (P.singleton_baseObject_eq_additionalDeleted C)
  let e₁ := iteratedDeletionEquivalence
    (k := k) C P.objectsᶜ ({x} : Set C)
  let e₂ := deletionEquivalenceOfEq
    (k := k) C (Set.union_comm P.objectsᶜ ({x} : Set C))
  let e₃base := iteratedDeletionEquivalence
    (k := k) C ({x} : Set C) P.objectsᶜ
  letI : e₃base.functor.Linear k := inferInstance
  let e₃ := e₃base.symm
  letI : e₀.functor.Linear k := inferInstance
  letI : e₁.functor.Linear k := inferInstance
  letI : e₂.functor.Linear k := inferInstance
  letI : e₃.functor.Linear k := by
    change e₃base.inverse.Linear k
    infer_instance
  change (e₀.functor ⋙
    (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor))).Linear k
  infer_instance

/-- The module equivalence induced by commuting finite-window restriction
with singleton deletion. -/
noncomputable def singletonSwapModuleEquivalence
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := IteratedDeletionCategory
          (k := k) C ({x} : Set C) P.objectsᶜ) k ≌
      FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k)
          (DeletionCategory (k := k) C P.objectsᶜ)
          ({P.baseObject C} : Set _)) k := by
  letI : Finite (DeletionCategory (k := k) C P.objectsᶜ) :=
    complementDeletion_finite (k := k) C P.objects P.finite
  letI : Finite (IteratedDeletionCategory
      (k := k) C ({x} : Set C) P.objectsᶜ) :=
    iteratedComplementDeletion_finite
      (k := k) C ({x} : Set C) P.objects P.finite
  exact finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) (P.singletonSwapEquivalence C)

noncomputable instance singletonSwapModuleEquivalence_functor_additive
    (P : FiniteConvexModuleControlWindow (k := k) x W) :
    (P.singletonSwapModuleEquivalence C).functor.Additive := by
  letI : Finite (DeletionCategory (k := k) C P.objectsᶜ) :=
    complementDeletion_finite (k := k) C P.objects P.finite
  letI : Finite (IteratedDeletionCategory
      (k := k) C ({x} : Set C) P.objectsᶜ) :=
    iteratedComplementDeletion_finite
      (k := k) C ({x} : Set C) P.objects P.finite
  change (finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) (P.singletonSwapEquivalence C)).functor.Additive
  infer_instance

/-- Successive restriction of a controlled ambient module is unchanged when
the finite-window complement and the base singleton are deleted in the
opposite order, after transport through `singletonSwapModuleEquivalence`. -/
noncomputable def singletonSwap_restrictionIso
    (P : FiniteConvexModuleControlWindow (k := k) x W)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hWindow : ModuleVanishesOnDeleted
      (k := k) C P.objectsᶜ M.obj.obj)
    (hBase : ModuleVanishesOnDeleted
      (k := k) C ({x} : Set C) M.obj.obj)
    (hBaseAfterWindow : ModuleVanishesOnDeleted
      (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
      ({P.baseObject C} : Set _)
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k) C P.objectsᶜ M hWindow).obj.obj)
    (hWindowAfterBase : ModuleVanishesOnDeleted
      (k := k) (DeletionCategory (k := k) C ({x} : Set C))
      (AdditionalDeleted (k := k) C ({x} : Set C) P.objectsᶜ)
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k) C ({x} : Set C) M hBase).obj.obj) :
    (P.singletonSwapModuleEquivalence C).functor.obj
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) (DeletionCategory (k := k) C ({x} : Set C))
          (AdditionalDeleted (k := k) C ({x} : Set C) P.objectsᶜ)
          (finiteDimensionalModuleRestrictionToDeletion
            (k := k) C ({x} : Set C) M hBase) hWindowAfterBase) ≅
      finiteDimensionalModuleRestrictionToDeletion
        (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
        ({P.baseObject C} : Set _)
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C P.objectsᶜ M hWindow) hBaseAfterWindow := by
  let S := P.objectsᶜ
  let T := ({x} : Set C)
  let hST : S ∪ T = T ∪ S := Set.union_comm S T
  have hUnionST : ModuleVanishesOnDeleted
      (k := k) C (S ∪ T) M.obj.obj := by
    intro X hX
    exact hX.elim (hWindow X) (hBase X)
  have hUnionTS : ModuleVanishesOnDeleted
      (k := k) C (T ∪ S) M.obj.obj := by
    intro X hX
    exact hX.elim (hBase X) (hWindow X)
  have hAdditionalAfterWindow : ModuleVanishesOnDeleted
      (k := k) (DeletionCategory (k := k) C S)
      (AdditionalDeleted (k := k) C S T)
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k) C S M hWindow).obj.obj := by
    intro X hX
    have hxX : X.obj.as = x := by
      change X.obj.as ∈ T at hX
      simpa only [T, Set.mem_singleton_iff] using hX
    exact hBaseAfterWindow X (by
      rw [Set.mem_singleton_iff]
      apply ObjectProperty.FullSubcategory.ext
      apply CategoryTheory.Quotient.ext
      exact hxX)
  let e₀ := deletionEquivalenceOfEq
    (k := k) (DeletionCategory (k := k) C S)
      (P.singleton_baseObject_eq_additionalDeleted C)
  let e₁ := iteratedDeletionEquivalence (k := k) C S T
  let e₂ := deletionEquivalenceOfEq (k := k) C hST
  let e₃base := iteratedDeletionEquivalence (k := k) C T S
  let e₃ := e₃base.symm
  let RST := linearModuleRestrictionToDeletion
    (k := k) C (S ∪ T) M.obj hUnionST
  let RTS := linearModuleRestrictionToDeletion
    (k := k) C (T ∪ S) M.obj hUnionTS
  let a₀ := deletionEquivalenceOfEq_linearModuleRestrictionIso
    (k := k) (DeletionCategory (k := k) C S)
      ({P.baseObject C} : Set _)
      (P.singleton_baseObject_eq_additionalDeleted C)
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k) C S M hWindow).obj hBaseAfterWindow
          hAdditionalAfterWindow
  let a₁ := iteratedLinearModuleRestrictionIso
    (k := k) C S T M.obj hUnionST hWindow hAdditionalAfterWindow
  let a₂ := deletionEquivalenceOfEq_linearModuleRestrictionIso
    (k := k) C (S ∪ T) hST M.obj hUnionST hUnionTS
  let a₃ := iteratedLinearModuleRestrictionIso
    (k := k) C T S M.obj hUnionTS hBase hWindowAfterBase
  let c₃ := Functor.isoWhiskerRight e₃base.counitIso RTS.obj
  let b₃ := c₃.symm.trans (Functor.isoWhiskerLeft e₃.functor a₃)
  let n :
      (e₀.functor ⋙ (e₁.functor ⋙
        (e₂.functor ⋙ e₃.functor))) ⋙
          (finiteDimensionalModuleRestrictionToDeletion
            (k := k) (DeletionCategory (k := k) C T)
            (AdditionalDeleted (k := k) C T S)
            (finiteDimensionalModuleRestrictionToDeletion
              (k := k) C T M hBase) hWindowAfterBase).obj.obj ≅
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) (DeletionCategory (k := k) C S)
          ({P.baseObject C} : Set _)
          (finiteDimensionalModuleRestrictionToDeletion
            (k := k) C S M hWindow) hBaseAfterWindow).obj.obj :=
    Functor.isoWhiskerLeft e₀.functor
        (Functor.isoWhiskerLeft e₁.functor
          (Functor.isoWhiskerLeft e₂.functor b₃.symm)) ≪≫
      Functor.isoWhiskerLeft e₀.functor
        (Functor.isoWhiskerLeft e₁.functor a₂) ≪≫
      Functor.isoWhiskerLeft e₀.functor a₁ ≪≫ a₀
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ n)

end MagnitudeConjecture.CoveringHom.FiniteConvexModuleControlWindow
