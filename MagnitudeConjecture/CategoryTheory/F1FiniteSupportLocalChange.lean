import MagnitudeConjecture.CategoryTheory.F1LocalDensity
import MagnitudeConjecture.CategoryTheory.F1FiniteSupportQuotient
import MagnitudeConjecture.CategoryTheory.FiniteModuleLocalDensityEquivalence
import MagnitudeConjecture.CategoryTheory.ObjectDeletionComparison
import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleInheritance
import MagnitudeConjecture.CategoryTheory.FiniteDecompositionVanishes
import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalDensity
import MagnitudeConjecture.CategoryTheory.IncomingHomLocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalChangeSum
import MagnitudeConjecture.CategoryTheory.F1FiniteDeletionSupport
import MagnitudeConjecture.CategoryTheory.FiniteDeletionSupportLocalChangeSum

/-!
# Local change through a finite support quotient

This is the support-quotient comparison used by the frozen deletion route.
The only finiteness input is a finite set of surviving objects; no convex
window or residual finite subgroup is involved.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion.Frozen

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Extension by zero of a module supported in `K` vanishes on the surviving
objects represented by `Kᶜ`. -/
theorem moduleVanishesOnAdditionalDeleted_of_extension_support_subset_f1
    (S K : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := ObjectDeletion.DeletionCategory (k := k) C S) k)
    (hM : moduleSupport k
      ((finiteDimensionalModuleExtensionByZero
        (k := k) C S).obj M).obj.obj ⊆ K) :
    ModuleVanishesOnDeleted
      (k := k) (ObjectDeletion.DeletionCategory (k := k) C S)
      (AdditionalDeleted (k := k) C S Kᶜ) M.obj.obj := by
  intro X hX
  have hXK : X.obj.as ∉ K := hX
  have hzero : IsZero
      (((finiteDimensionalModuleExtensionByZero
        (k := k) C S).obj M).obj.obj.obj X.obj.as) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact not_nontrivial_iff_subsingleton.mp (fun hnontrivial ↦ hXK (hM hnontrivial))
  exact (moduleExtensionByZeroObjIsoAt
    (k := k) C S M.obj.obj X).isZero_iff.mp hzero

/-- The singleton in a deletion category is the surviving representative of
the corresponding ambient singleton. -/
theorem survivingSingleton_eq_additionalDeleted_f1
    (S : Set C) (x : C) (hx : x ∉ S) :
    ({survivingObj (k := k) C S hx} : Set
      (ObjectDeletion.DeletionCategory (k := k) C S)) =
      AdditionalDeleted (k := k) C S ({x} : Set C) := by
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

/- The two possible orders of deleting `S` and `{x}` are canonically
equivalent. -/
noncomputable def singletonSwapEquivalence_f1
    (S : Set C) (x : C) (hx : x ∉ S) :
    ObjectDeletion.DeletionCategory (k := k)
        (ObjectDeletion.DeletionCategory (k := k) C S)
        ({survivingObj (k := k) C S hx} : Set _) ≌
      ObjectDeletion.IteratedDeletionCategory (k := k) C ({x} : Set C) S := by
  let e₀ := deletionEquivalenceOfEq
    (k := k) (ObjectDeletion.DeletionCategory (k := k) C S)
      (survivingSingleton_eq_additionalDeleted_f1 (k := k) S x hx)
  let e₁ := iteratedDeletionEquivalence (k := k) C S ({x} : Set C)
  let e₂ := deletionEquivalenceOfEq (k := k) C (Set.union_comm S ({x} : Set C))
  let e₃ := (iteratedDeletionEquivalence (k := k) C ({x} : Set C) S).symm
  exact e₀.trans (e₁.trans (e₂.trans e₃))

noncomputable instance singletonSwapEquivalence_f1_functor_additive
    (S : Set C) (x : C) (hx : x ∉ S) :
    (singletonSwapEquivalence_f1 (k := k) S x hx).functor.Additive := by
  let e₀ := deletionEquivalenceOfEq
    (k := k) (ObjectDeletion.DeletionCategory (k := k) C S)
      (survivingSingleton_eq_additionalDeleted_f1 (k := k) S x hx)
  let e₁ := iteratedDeletionEquivalence (k := k) C S ({x} : Set C)
  let e₂ := deletionEquivalenceOfEq (k := k) C (Set.union_comm S ({x} : Set C))
  let e₃base := iteratedDeletionEquivalence (k := k) C ({x} : Set C) S
  let e₃ := e₃base.symm
  letI : e₀.functor.Additive := inferInstance
  letI : e₁.functor.Additive := inferInstance
  letI : e₂.functor.Additive := inferInstance
  letI : e₃.functor.Additive := by
    change e₃base.inverse.Additive
    infer_instance
  change (e₀.functor ⋙ (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor))).Additive
  infer_instance

noncomputable instance singletonSwapEquivalence_f1_functor_linear
    (S : Set C) (x : C) (hx : x ∉ S) :
    (singletonSwapEquivalence_f1 (k := k) S x hx).functor.Linear k := by
  let e₀ := deletionEquivalenceOfEq
    (k := k) (ObjectDeletion.DeletionCategory (k := k) C S)
      (survivingSingleton_eq_additionalDeleted_f1 (k := k) S x hx)
  let e₁ := iteratedDeletionEquivalence (k := k) C S ({x} : Set C)
  let e₂ := deletionEquivalenceOfEq (k := k) C (Set.union_comm S ({x} : Set C))
  let e₃base := iteratedDeletionEquivalence (k := k) C ({x} : Set C) S
  let e₃ := e₃base.symm
  letI : e₀.functor.Linear k := inferInstance
  letI : e₁.functor.Linear k := inferInstance
  letI : e₂.functor.Linear k := inferInstance
  letI : e₃.functor.Linear k := by
    change e₃base.inverse.Linear k
    infer_instance
  change (e₀.functor ⋙ (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor))).Linear k
  infer_instance

/-- The iterated deletion retaining a finite support set has finitely many
objects. -/
theorem iteratedComplementDeletion_finite_f1
    (K : Set C) (x : C) (hK : K.Finite) :
    Finite (ObjectDeletion.IteratedDeletionCategory (k := k) C
      ({x} : Set C) Kᶜ) := by
  let f : ObjectDeletion.IteratedDeletionCategory (k := k) C
      ({x} : Set C) Kᶜ → K := fun X ↦
    ⟨X.obj.as.obj.as, by
      have hX := X.property
      change X.obj.as.obj.as ∉ Kᶜ at hX
      simpa only [Set.mem_compl_iff, not_not] using hX⟩
  letI : Fintype K := hK.fintype
  exact Finite.of_injective f (by
    intro X Y hXY
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    exact congrArg Subtype.val hXY)

noncomputable def singletonSwapModuleEquivalence_f1
    (K : Set C) (x : C) (hx : x ∈ K) (hK : K.Finite) :
    FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := ObjectDeletion.IteratedDeletionCategory
          (k := k) C ({x} : Set C) Kᶜ) k ≌
      FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := ObjectDeletion.DeletionCategory (k := k)
          (ObjectDeletion.DeletionCategory (k := k) C Kᶜ)
          ({survivingObj (k := k) C Kᶜ (by
            simpa only [Set.mem_compl_iff, not_not] using hx)} : Set _)) k := by
  letI : Finite (ObjectDeletion.DeletionCategory (k := k) C Kᶜ) :=
    finiteSupportCategory_finite (k := k) (C := C) K hK
  letI : Finite (ObjectDeletion.IteratedDeletionCategory (k := k) C
      ({x} : Set C) Kᶜ) := iteratedComplementDeletion_finite_f1 K x hK
  let hx' : x ∉ Kᶜ := by simpa only [Set.mem_compl_iff, not_not] using hx
  exact finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) (singletonSwapEquivalence_f1 (k := k) Kᶜ x hx')

noncomputable instance singletonSwapModuleEquivalence_f1_functor_additive
    (K : Set C) (x : C) (hx : x ∈ K) (hK : K.Finite) :
    (singletonSwapModuleEquivalence_f1 (k := k) K x hx hK).functor.Additive := by
  letI : Finite (ObjectDeletion.DeletionCategory (k := k) C Kᶜ) :=
    finiteSupportCategory_finite (k := k) (C := C) K hK
  letI : Finite (ObjectDeletion.IteratedDeletionCategory (k := k) C
      ({x} : Set C) Kᶜ) := iteratedComplementDeletion_finite_f1 K x hK
  let hx' : x ∉ Kᶜ := by simpa only [Set.mem_compl_iff, not_not] using hx
  change (finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) (singletonSwapEquivalence_f1 (k := k) Kᶜ x hx')).functor.Additive
  infer_instance

noncomputable instance singletonSwapModuleEquivalence_f1_functor_linear
    (K : Set C) (x : C) (hx : x ∈ K) (hK : K.Finite) :
    (singletonSwapModuleEquivalence_f1 (k := k) K x hx hK).functor.Linear k := by
  letI : Finite (ObjectDeletion.DeletionCategory (k := k) C Kᶜ) :=
    finiteSupportCategory_finite (k := k) (C := C) K hK
  letI : Finite (ObjectDeletion.IteratedDeletionCategory (k := k) C
      ({x} : Set C) Kᶜ) := iteratedComplementDeletion_finite_f1 K x hK
  let hx' : x ∉ Kᶜ := by simpa only [Set.mem_compl_iff, not_not] using hx
  change (finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) (singletonSwapEquivalence_f1 (k := k) Kᶜ x hx')).functor.Linear k
  infer_instance

/-- Successive restriction of a module supported on `K` is independent of the
order of deleting `Kᶜ` and `{x}`. -/
noncomputable def singletonSwap_restrictionIso_f1
    (K : Set C) (x : C) (hx : x ∈ K) (hK : K.Finite)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hWindow : ModuleVanishesOnDeleted (k := k) C Kᶜ M.obj.obj)
    (hBase : ModuleVanishesOnDeleted (k := k) C ({x} : Set C) M.obj.obj)
    (hBaseAfterWindow : ModuleVanishesOnDeleted (k := k)
      (ObjectDeletion.DeletionCategory (k := k) C Kᶜ)
      ({survivingObj (k := k) C Kᶜ (by
        simpa only [Set.mem_compl_iff, not_not] using hx)} : Set _)
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k) C Kᶜ M hWindow).obj.obj)
    (hWindowAfterBase : ModuleVanishesOnDeleted (k := k)
      (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
      (AdditionalDeleted (k := k) C ({x} : Set C) Kᶜ)
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k) C ({x} : Set C) M hBase).obj.obj) :
    (singletonSwapModuleEquivalence_f1 (k := k) K x hx hK).functor.obj
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
          (AdditionalDeleted (k := k) C ({x} : Set C) Kᶜ)
          (finiteDimensionalModuleRestrictionToDeletion
            (k := k) C ({x} : Set C) M hBase) hWindowAfterBase) ≅
      finiteDimensionalModuleRestrictionToDeletion
        (k := k) (ObjectDeletion.DeletionCategory (k := k) C Kᶜ)
        ({survivingObj (k := k) C Kᶜ (by
          simpa only [Set.mem_compl_iff, not_not] using hx)} : Set _)
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C Kᶜ M hWindow) hBaseAfterWindow := by
  let S := Kᶜ
  let T := ({x} : Set C)
  let hx' : x ∉ S := by simpa only [S, Set.mem_compl_iff, not_not] using hx
  let yS := survivingObj (k := k) C S hx'
  let hUnionST : ModuleVanishesOnDeleted (k := k) C (S ∪ T) M.obj.obj := by
    intro Y hY
    exact hY.elim (hWindow Y) (hBase Y)
  let hUnionTS : ModuleVanishesOnDeleted (k := k) C (T ∪ S) M.obj.obj := by
    intro Y hY
    exact hY.elim (hBase Y) (hWindow Y)
  let hAdditionalAfterWindow : ModuleVanishesOnDeleted (k := k)
      (ObjectDeletion.DeletionCategory (k := k) C S)
      (AdditionalDeleted (k := k) C S T)
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k) C S M hWindow).obj.obj := by
    intro Y hY
    have hxy : Y.obj.as = x := by
      change Y.obj.as ∈ T at hY
      simpa only [T, Set.mem_singleton_iff] using hY
    exact hBaseAfterWindow Y (by
      rw [Set.mem_singleton_iff]
      apply ObjectProperty.FullSubcategory.ext
      apply CategoryTheory.Quotient.ext
      exact hxy)
  let e₀ := deletionEquivalenceOfEq
    (k := k) (ObjectDeletion.DeletionCategory (k := k) C S)
      (survivingSingleton_eq_additionalDeleted_f1 (k := k) S x hx')
  let e₁ := iteratedDeletionEquivalence (k := k) C S T
  let e₂ := deletionEquivalenceOfEq (k := k) C (Set.union_comm S T)
  let e₃base := iteratedDeletionEquivalence (k := k) C T S
  let e₃ := e₃base.symm
  let RST := linearModuleRestrictionToDeletion
    (k := k) C (S ∪ T) M.obj hUnionST
  let RTS := linearModuleRestrictionToDeletion
    (k := k) C (T ∪ S) M.obj hUnionTS
  let a₀ := deletionEquivalenceOfEq_linearModuleRestrictionIso
    (k := k) (ObjectDeletion.DeletionCategory (k := k) C S)
      ({yS} : Set _)
      (survivingSingleton_eq_additionalDeleted_f1 (k := k) S x hx')
      (linearModuleRestrictionToDeletion (k := k) C S M.obj hWindow)
      hBaseAfterWindow hAdditionalAfterWindow
  let a₁ := iteratedLinearModuleRestrictionIso
    (k := k) C S T M.obj hUnionST hWindow hAdditionalAfterWindow
  let a₂ := deletionEquivalenceOfEq_linearModuleRestrictionIso
    (k := k) C (S ∪ T) (Set.union_comm S T) M.obj hUnionST hUnionTS
  let a₃ := iteratedLinearModuleRestrictionIso
    (k := k) C T S M.obj hUnionTS hBase hWindowAfterBase
  let c₃ := Functor.isoWhiskerRight e₃base.counitIso RTS.obj
  let b₃ := c₃.symm.trans (Functor.isoWhiskerLeft e₃.functor a₃)
  let n :
      (e₀.functor ⋙ (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor))) ⋙
          (linearModuleRestrictionToDeletion (k := k)
            (ObjectDeletion.DeletionCategory (k := k) C T)
            (AdditionalDeleted (k := k) C T S)
            (linearModuleRestrictionToDeletion (k := k) C T M.obj hBase)
            hWindowAfterBase).obj ≅
        (linearModuleRestrictionToDeletion (k := k)
          (ObjectDeletion.DeletionCategory (k := k) C S) ({yS} : Set _)
          (linearModuleRestrictionToDeletion (k := k) C S M.obj hWindow)
          hBaseAfterWindow).obj :=
    Functor.isoWhiskerLeft e₀.functor
        (Functor.isoWhiskerLeft e₁.functor
          (Functor.isoWhiskerLeft e₂.functor b₃.symm)) ≪≫
      Functor.isoWhiskerLeft e₀.functor
        (Functor.isoWhiskerLeft e₁.functor a₂) ≪≫
      Functor.isoWhiskerLeft e₀.functor a₁ ≪≫ a₀
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ n)

/-- A finite support certificate preserves the singleton deletion local change
of an indecomposable endpoint. -/
theorem finiteSupport_restriction_localChangeAt_eq_f1
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (K : Set C) (hK : K.Finite) (x : C) (hx : x ∈ K)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hMsupport : moduleSupport k M.obj.obj ⊆ K)
    (hNsupport : ∀ j, moduleSupport k
      ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j).obj.obj ⊆ K) :
    let S := Kᶜ
    let hx' : x ∉ S := by simpa only [S, Set.mem_compl_iff, not_not] using hx
    let D := ObjectDeletion.DeletionCategory (k := k) C S
    let yS := survivingObj (k := k) C S hx'
    let hWindow := moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
      (k := k) C M K hMsupport
    let RM := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C S M hWindow
    let hRM := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C S M hM hWindow
    finiteDeletionLocalChangeAt (k := k) D
        (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
        ({yS} : Set _) RM hRM =
      finiteDeletionLocalChangeAt (k := k) C hlocal ({x} : Set C) M hM := by
  classical
  let S := Kᶜ
  let hx' : x ∉ S := by simpa only [S, Set.mem_compl_iff, not_not] using hx
  let D := ObjectDeletion.DeletionCategory (k := k) C S
  let yS := survivingObj (k := k) C S hx'
  let hWindow := moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
    (k := k) C M K hMsupport
  let RM := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C S M hWindow
  let hRM := finiteDimensionalModuleRestrictionToDeletion_indec
    (k := k) C S M hM hWindow
  let hlocalD := isLocallyRepresentationFinite_deletion (k := k) C S hlocal
  let A := finiteModuleMinimalSinkData hlocal M hM
  have hsourceSummand (i : Fin A.decomposition.n) :
      ModuleVanishesOnDeleted (k := k) C S
        (A.decomposition.summand i).obj.obj := by
    obtain ⟨j, ⟨e⟩⟩ :=
      minimalSink_summand_covered_by_finiteIncomingHomNeighborhood
        (k := k) C hlocal M hM i
    apply moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
      (k := k) C (A.decomposition.summand i) K
    intro X hX
    exact hNsupport j ((mem_moduleSupport_iff_of_iso e X).mpr hX)
  have hsource : ModuleVanishesOnDeleted (k := k) C S A.source.obj.obj :=
    moduleVanishesOnDeleted_of_decomposition_summands
      (k := k) C S A.source A.decomposition hsourceSummand
  have hPre := restriction_localDensity_eq_of_minimalSink_source_vanishes
    (k := k) C hP hlocal S M hM hWindow A.map A.rightAlmostSplit
      A.rightMinimal A.decomposition hsource
  let eM := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C S M hWindow
  by_cases hBase : ModuleVanishesOnDeleted (k := k) C ({x} : Set C) M.obj.obj
  · let RX := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C ({x} : Set C) M hBase
    let hRX := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C ({x} : Set C) M hM hBase
    let hWindowAfterBase : ModuleVanishesOnDeleted (k := k)
        (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
        (AdditionalDeleted (k := k) C ({x} : Set C) S) RX.obj.obj := by
      exact moduleVanishesOnAdditionalDeleted_of_extension_support_subset_f1
        (k := k) ({x} : Set C) K RX (by
          intro Y hY
          have hMY : Y ∈ moduleSupport k M.obj.obj :=
            (mem_moduleSupport_iff_of_iso
              (finiteDimensionalModuleRestrictionExtensionIso
                (k := k) C ({x} : Set C) M hBase) Y).mp hY
          exact hMsupport hMY)
    let hBaseAfterWindow : ModuleVanishesOnDeleted (k := k) D ({yS} : Set D)
        RM.obj.obj := by
      let F := finiteDimensionalModuleExtensionByZero (k := k) C S
      have hBaseF : ModuleVanishesOnDeleted (k := k) C ({x} : Set C)
          (F.obj RM).obj.obj :=
        moduleVanishesOnDeleted_of_iso (k := k) C ({x} : Set C) eM.symm hBase
      intro Y hY
      rw [Set.mem_singleton_iff] at hY
      subst Y
      have hzero := hBaseF x (by simp)
      exact (moduleExtensionByZeroObjIsoAt
        (k := k) C S RM.obj.obj yS).isZero_iff.mp hzero
    let hAdditionalAfterWindow : ModuleVanishesOnDeleted (k := k) D
        (AdditionalDeleted (k := k) C S ({x} : Set C)) RM.obj.obj := by
      intro Y hY
      have hxy : Y.obj.as = x := by
        change Y.obj.as ∈ ({x} : Set C) at hY
        simpa only [Set.mem_singleton_iff] using hY
      exact hBaseAfterWindow Y (by
        rw [Set.mem_singleton_iff]
        apply ObjectProperty.FullSubcategory.ext
        apply CategoryTheory.Quotient.ext
        exact hxy)
    let RMBase := finiteDimensionalModuleRestrictionToDeletion
      (k := k) D ({yS} : Set D) RM hBaseAfterWindow
    let hRMBase := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) D ({yS} : Set D) RM hRM hBaseAfterWindow
    let AX := finiteModuleMinimalSinkData
      (isLocallyRepresentationFinite_deletion
        (k := k) C ({x} : Set C) hlocal) RX hRX
    have hsourceX (i : Fin AX.decomposition.n) :
        ModuleVanishesOnDeleted (k := k)
          (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
          (AdditionalDeleted (k := k) C ({x} : Set C) S)
          (AX.decomposition.summand i).obj.obj := by
      let F := finiteDimensionalModuleExtensionByZero
        (k := k) C ({x} : Set C)
      have hcomp : AX.decomposition.inclusion i ≫ AX.map ≠ 0 :=
        AX.decomposition.inclusion_comp_ne_zero_of_isRightMinimal
          i AX.map AX.rightMinimal
      have hFcomp : F.map (AX.decomposition.inclusion i ≫ AX.map) ≠ 0 := by
        intro hzero
        exact hcomp ((F.map_eq_zero_iff).mp hzero)
      have hFind : Indecomposable (F.obj (AX.decomposition.summand i)) :=
        finiteDimensionalModuleExtensionByZero_indec
          (k := k) C ({x} : Set C) (AX.decomposition.summand i)
            (AX.decomposition.indecomposable i)
      let eRX := finiteDimensionalModuleRestrictionExtensionIso
        (k := k) C ({x} : Set C) M hBase
      let hmap : F.obj (AX.decomposition.summand i) ⟶ M :=
        F.map (AX.decomposition.inclusion i ≫ AX.map) ≫ eRX.hom
      have hmap_ne : hmap ≠ 0 := by
        intro hz
        apply hFcomp
        apply (cancel_mono eRX.hom).1
        simpa [hmap, Category.assoc] using hz
      obtain ⟨j, ⟨e⟩⟩ :=
        (finiteIncomingHomNeighborhood (k := k) C hlocal M).covers
          hFind hmap hmap_ne
      apply moduleVanishesOnAdditionalDeleted_of_extension_support_subset_f1
        (k := k) ({x} : Set C) K (AX.decomposition.summand i)
      intro X hX
      exact hNsupport j ((mem_moduleSupport_iff_of_iso e X).mpr hX)
    have hsourceX' : ModuleVanishesOnDeleted
        (k := k) (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
        (AdditionalDeleted (k := k) C ({x} : Set C) S) AX.source.obj.obj :=
      moduleVanishesOnDeleted_of_decomposition_summands
        (k := k) (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
        (AdditionalDeleted (k := k) C ({x} : Set C) S)
        AX.source AX.decomposition hsourceX
    have hPostRestriction := restriction_localDensity_eq_of_minimalSink_source_vanishes
      (k := k) (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
      (ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
        (k := k) C hP ({x} : Set C))
      (isLocallyRepresentationFinite_deletion
        (k := k) C ({x} : Set C) hlocal)
      (AdditionalDeleted (k := k) C ({x} : Set C) S) RX hRX hWindowAfterBase
      AX.map AX.rightAlmostSplit AX.rightMinimal AX.decomposition hsourceX'
    let RXWindow := finiteDimensionalModuleRestrictionToDeletion
      (k := k) (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
      (AdditionalDeleted (k := k) C ({x} : Set C) S) RX hWindowAfterBase
    let hRXWindow := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
      (AdditionalDeleted (k := k) C ({x} : Set C) S) RX hRX hWindowAfterBase
    let eSwap := singletonSwapModuleEquivalence_f1 (k := k) K x hx hK
    let eSwapIso := singletonSwap_restrictionIso_f1
      (k := k) K x hx hK M hWindow hBase hBaseAfterWindow hWindowAfterBase
    have hMap := finiteModuleLocalDensity_map_equivalence
      (isLocallyRepresentationFinite_deletion (k := k) D ({yS} : Set D) hlocalD)
      (isLocallyRepresentationFinite_deletion
        (k := k) (ObjectDeletion.DeletionCategory (k := k) C ({x} : Set C))
        (AdditionalDeleted (k := k) C ({x} : Set C) S)
        (isLocallyRepresentationFinite_deletion
          (k := k) C ({x} : Set C) hlocal))
      eSwap RXWindow hRXWindow
    have hMapIso := finiteModuleLocalDensity_eq_of_iso
      (isLocallyRepresentationFinite_deletion (k := k) D ({yS} : Set D) hlocalD)
      ((MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        eSwap.functor RXWindow).2 hRXWindow) hRMBase eSwapIso
    have hPost : finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) D ({yS} : Set D) hlocalD)
        RMBase hRMBase =
      finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C ({x} : Set C) hlocal)
        RX hRX := by
      exact hMapIso.symm.trans (hMap.trans (by
        simpa only [RXWindow] using hPostRestriction))
    have hBA : ModuleVanishesOnDeleted (k := k)
        (ObjectDeletion.DeletionCategory (k := k) C Kᶜ)
        ({survivingObj (k := k) C Kᶜ (by
          simpa only [Set.mem_compl_iff, not_not] using hx)} : Set _)
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C Kᶜ M
          (moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
            (k := k) C M K hMsupport)).obj.obj := by
      simpa only [D, yS, RM, hWindow] using hBaseAfterWindow
    have hPost' : finiteModuleLocalDensity
          (isLocallyRepresentationFinite_deletion (k := k) D ({yS} : Set D) hlocalD)
          (finiteDimensionalModuleRestrictionToDeletion
            (k := k) D ({yS} : Set D) RM hBaseAfterWindow)
          (finiteDimensionalModuleRestrictionToDeletion_indec
            (k := k) D ({yS} : Set D) RM hRM hBaseAfterWindow) =
        finiteModuleLocalDensity
          (isLocallyRepresentationFinite_deletion (k := k) C ({x} : Set C) hlocal)
          (finiteDimensionalModuleRestrictionToDeletion
            (k := k) C ({x} : Set C) M hBase) hRX := by
      simpa only [RMBase, RXWindow] using hPost
    simpa [finiteDeletionLocalChangeAt, finiteDeletionExtendedLocalDensity, hBA,
      hBase] using
      congrArg₂ (fun a b : ℤ ↦ a - b) hPre hPost'
  · have hBaseAfterWindow : ¬ ModuleVanishesOnDeleted (k := k) D ({yS} : Set D)
        RM.obj.obj := by
      intro hRMBase
      apply hBase
      let F := finiteDimensionalModuleExtensionByZero (k := k) C S
      have hFbase : ModuleVanishesOnDeleted (k := k) C ({x} : Set C)
          (F.obj RM).obj.obj := by
        intro Y hY
        rw [Set.mem_singleton_iff] at hY
        subst Y
        have hzero := hRMBase yS (by simp)
        have hzero' := (moduleExtensionByZeroObjIsoAt
          (k := k) C S RM.obj.obj yS).isZero_iff.mpr hzero
        exact hzero'
      have hMbase := moduleVanishesOnDeleted_of_iso
        (k := k) C ({x} : Set C) eM hFbase
      exact fun Y hY ↦ hMbase Y hY
    have hBA : ¬ ModuleVanishesOnDeleted (k := k)
        (ObjectDeletion.DeletionCategory (k := k) C Kᶜ)
        ({survivingObj (k := k) C Kᶜ (by
          simpa only [Set.mem_compl_iff, not_not] using hx)} : Set _)
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C Kᶜ M
          (moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
            (k := k) C M K hMsupport)).obj.obj := by
      simpa only [D, yS, RM, hWindow] using hBaseAfterWindow
    simpa [finiteDeletionLocalChangeAt, finiteDeletionExtendedLocalDensity, hBA,
      hBase] using
      congrArg₂ (fun a b : ℤ ↦ a - b) hPre (Eq.refl (0 : ℤ))

/-! The following definitions package the finite quotient of a finite control
family.  They are deliberately independent of convex windows. -/

theorem finiteIncomingHomDependencySupport_finite_f1
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory (C := C) k) :
    (finiteIncomingHomDependencySupport (k := k) C hlocal M).Finite := by
  unfold finiteIncomingHomDependencySupport
  exact (finite_moduleSupport k M).union (Set.finite_iUnion fun j ↦
    finite_moduleSupport k
      ((finiteIncomingHomNeighborhood (k := k) C hlocal M).obj j))

noncomputable def finiteSupportRestrictionFamily_f1
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (K : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hsupport : ∀ i : Fin W.n,
      moduleSupport k (W.obj i).obj.obj ⊆ K) :
    FiniteIndecomposableModuleFamily (k := k)
      (C := finiteSupportCategory (k := k) (C := C) K) where
  n := W.n
  obj i := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C Kᶜ (W.obj i)
      (moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
        (k := k) C (W.obj i) K (hsupport i))
  indecomposable i := finiteDimensionalModuleRestrictionToDeletion_indec
    (k := k) C Kᶜ (W.obj i) (W.indecomposable i)
      (moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
        (k := k) C (W.obj i) K (hsupport i))

noncomputable def finiteSupportRestrictionIso_f1
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (K : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hsupport : ∀ i : Fin W.n,
      moduleSupport k (W.obj i).obj.obj ⊆ K)
    (i j : Fin W.n) (e : W.obj i ≅ W.obj j) :
    (finiteSupportRestrictionFamily_f1 (k := k) hlocal K W hsupport).obj i ≅
      (finiteSupportRestrictionFamily_f1 (k := k) hlocal K W hsupport).obj j := by
  let hi := moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
    (k := k) C (W.obj i) K (hsupport i)
  let hj := moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
    (k := k) C (W.obj j) K (hsupport j)
  let F := finiteDimensionalModuleExtensionByZero (k := k) C Kᶜ
  let qi := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C Kᶜ (W.obj i) hi
  let qj := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C Kᶜ (W.obj j) hj
  exact F.preimageIso (qi.trans (e.trans qj.symm))

noncomputable def finiteSupportRestrictionIsoClassMap_f1
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (K : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hsupport : ∀ i : Fin W.n,
      moduleSupport k (W.obj i).obj.obj ⊆ K) :
    W.IsoClass →
      (finiteSupportRestrictionFamily_f1 (k := k) hlocal K W hsupport).IsoClass :=
  Quotient.lift
    (fun i ↦ Quotient.mk _ i)
    (by
      intro i j hij
      apply Quotient.sound
      exact hij.map (fun e ↦ finiteSupportRestrictionIso_f1
        (k := k) hlocal K W hsupport i j e))

theorem finiteSupportRestrictionIsoClassMap_f1_bijective
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (K : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hsupport : ∀ i : Fin W.n,
      moduleSupport k (W.obj i).obj.obj ⊆ K) :
    Function.Bijective
      (finiteSupportRestrictionIsoClassMap_f1 (k := k) hlocal K W hsupport) := by
  constructor
  · intro q r hqr
    induction q using Quotient.inductionOn with
    | _ i =>
      induction r using Quotient.inductionOn with
      | _ j =>
        apply Quotient.sound
        obtain ⟨e⟩ := Quotient.exact hqr
        let F := finiteDimensionalModuleExtensionByZero (k := k) C Kᶜ
        let hi := moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
          (k := k) C (W.obj i) K (hsupport i)
        let hj := moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
          (k := k) C (W.obj j) K (hsupport j)
        let qi := finiteDimensionalModuleRestrictionExtensionIso
          (k := k) C Kᶜ (W.obj i) hi
        let qj := finiteDimensionalModuleRestrictionExtensionIso
          (k := k) C Kᶜ (W.obj j) hj
        exact ⟨qi.symm ≪≫ F.mapIso e ≪≫ qj⟩
  · intro q
    induction q using Quotient.inductionOn with
    | _ i => exact ⟨Quotient.mk W.isoSetoid i, rfl⟩

theorem finiteSupport_localChangeSum_eq_f1
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (K : Set C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hsupport : ∀ i : Fin W.n,
      moduleSupport k (W.obj i).obj.obj ⊆ K)
    (hNsupport : ∀ i : Fin W.n, ∀ j,
      moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j).obj.obj ⊆ K)
    (hK : K.Finite) (x : C) (hx : x ∈ K) :
    finiteDeletionLocalChangeSum (k := k) C hlocal ({x} : Set C) W =
      finiteDeletionLocalChangeSum
        (k := k) (finiteSupportCategory (k := k) (C := C) K)
        (finiteSupportCategory_isLocallyRepresentationFinite
          (k := k) (C := C) hlocal K)
        ({survivingObj (k := k) C Kᶜ (by
          simpa only [Set.mem_compl_iff, not_not] using hx)} : Set _)
    (finiteSupportRestrictionFamily_f1 (k := k) hlocal K W hsupport) := by
  classical
  let W' := finiteSupportRestrictionFamily_f1 (k := k) hlocal K W hsupport
  let φ := finiteSupportRestrictionIsoClassMap_f1
    (k := k) hlocal K W hsupport
  have hφ : Function.Bijective φ :=
    finiteSupportRestrictionIsoClassMap_f1_bijective
      (k := k) hlocal K W hsupport
  unfold finiteDeletionLocalChangeSum
  apply Fintype.sum_bijective φ hφ
    (finiteDeletionLocalChangeOnIsoClass (k := k) C hlocal ({x} : Set C) W)
    (fun q ↦ finiteDeletionLocalChangeOnIsoClass
      (k := k) (finiteSupportCategory (k := k) (C := C) K)
      (finiteSupportCategory_isLocallyRepresentationFinite
        (k := k) (C := C) hlocal K)
      ({survivingObj (k := k) C Kᶜ (by
        simpa only [Set.mem_compl_iff, not_not] using hx)} : Set _)
      W' q)
    (by
      intro q
      induction q using Quotient.inductionOn with
      | _ i =>
        let hi := moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
          (k := k) C (W.obj i) K (hsupport i)
        let hri := finiteDimensionalModuleRestrictionToDeletion_indec
          (k := k) C Kᶜ (W.obj i) (W.indecomposable i) hi
        have hpoint := finiteSupport_restriction_localChangeAt_eq_f1
          (k := k) hP hlocal K hK
          x hx (W.obj i) (W.indecomposable i) (hsupport i)
            (hNsupport i)
        change finiteDeletionLocalChangeAt (k := k) C hlocal ({x} : Set C)
            (W.obj i) (W.indecomposable i) =
          finiteDeletionLocalChangeAt
            (k := k) (finiteSupportCategory (k := k) (C := C) K)
            (finiteSupportCategory_isLocallyRepresentationFinite
              (k := k) (C := C) hlocal K)
            ({survivingObj (k := k) C Kᶜ (by
              simpa only [Set.mem_compl_iff, not_not] using hx)} : Set _)
            ((finiteSupportRestrictionFamily_f1 (k := k) hlocal K W hsupport).obj i)
            _
        simpa only [W', finiteSupportRestrictionFamily_f1, hi, hri,
          finiteDeletionLocalChangeOnIsoClass, φ,
          finiteSupportRestrictionIsoClassMap_f1] using hpoint.symm)

theorem finiteSupport_localChangeSum_nonnegative_f1
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (hC : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (K : Set C) (hK : K.Finite) (x : C) (hx : x ∈ K)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hsupport : ∀ i : Fin W.n,
      moduleSupport k (W.obj i).obj.obj ⊆ K)
    (hNsupport : ∀ i : Fin W.n, ∀ j,
      moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j).obj.obj ⊆ K)
    (hcore : ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
      hlocal 2).isoClosure ⊆ W.isoClosure) :
    0 ≤ finiteDeletionLocalChangeSum (k := k) C hlocal ({x} : Set C) W := by
  classical
  let E := finiteSupportCategory (k := k) (C := C) K
  let hlocalE := finiteSupportCategory_isLocallyRepresentationFinite
    (k := k) (C := C) hlocal K
  let hPE := fun Y : E ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP Kᶜ Y
  let hRE := finiteSupportCategory_localEndomorphismRings
    (k := k) (C := C) hC hlocalRing K
  let hCE := finiteSupportCategory_skeletal
    (k := k) (C := C) hC hlocalRing K
  let HE := finiteSupportCategory_directed
    (k := k) (C := C) H K
  letI : Finite E := finiteSupportCategory_finite (k := k) (C := C) K hK
  letI : Fintype E := Fintype.ofFinite _
  let hx' : x ∉ Kᶜ := by
    simpa only [Set.mem_compl_iff, not_not] using hx
  let xE : E := survivingObj (k := k) C Kᶜ hx'
  let W' := finiteSupportRestrictionFamily_f1 (k := k) hlocal K W hsupport
  let S := finiteSupportCategory_skeleton (k := k) (C := C) hP hlocal K hK
  let T := finiteSupportCategory_singleton_skeleton
    (k := k) (C := C) hP hlocal K hK xE
  let p : Fin S.n → Prop := fun i ↦ S.obj i ∈ W'.isoClosure
  letI : DecidablePred p := Classical.decPred _
  have houtside : ∀ i : Fin S.n, ¬ p i →
      localChange (k := k) E hlocalE ({xE} : Set E)
        (S.obj i) (S.indecomposable i) = 0 := by
    intro i hi
    apply finiteDeletionLocalChangeAt_eq_zero_of_not_mem_twoStep
      (k := k) E hPE hlocalE xE (S.obj i) (S.indecomposable i)
    intro hiCore
    apply hi
    obtain ⟨j, ⟨e⟩⟩ :=
      iterateHomNeighborhood_extensionByZero_mem
        (k := k) C hlocal x Kᶜ hx' 2 (S.obj i)
          (S.indecomposable i) hiCore
    have hExt :
        (finiteDimensionalModuleExtensionByZero (k := k) C Kᶜ).obj
            (S.obj i) ∈
          ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
            hlocal 2).isoClosure := ⟨j, ⟨e⟩⟩
    obtain ⟨t, ⟨et⟩⟩ := hcore hExt
    let ht := moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
      (k := k) C (W.obj t) K (hsupport t)
    let F := finiteDimensionalModuleExtensionByZero (k := k) C Kᶜ
    let qt := finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C Kᶜ (W.obj t) ht
    refine ⟨t, ⟨F.preimageIso (qt.trans et)⟩⟩
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := E) k) :=
    enoughProjectives_of_finiteRepresentables hPE
  let hPEdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) E hPE ({xE} : Set E) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := ObjectDeletion.DeletionCategory (k := k) E ({xE} : Set E)) k) :=
    enoughProjectives_of_finiteRepresentables hPEdeleted
  have hmono :=
    finiteCategoryProjectiveGenerator.singletonDeletion_surplus_le_of_fintype
      (k := k) hPE hRE hCE hlocalE HE xE S T
  have hsumAll : 0 ≤ ∑ i : Fin S.n,
      localChange (k := k) E hlocalE ({xE} : Set E)
        (S.obj i) (S.indecomposable i) := by
    rw [FiniteDeletionSkeleton.sum_localChange_eq_surplus_sub
      (k := k) ({xE} : Set E) S T hlocalE]
    exact sub_nonneg.mpr hmono
  let f : Fin S.n → ℤ := fun i ↦
    localChange (k := k) E hlocalE ({xE} : Set E)
      (S.obj i) (S.indecomposable i)
  have hzero : ∑ i : {i : Fin S.n // ¬ p i}, f i.1 = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact houtside i.1 i.2
  have hpartition := Fintype.sum_subtype_add_sum_subtype p f
  have hsumE : 0 ≤ ∑ i : {i : Fin S.n // p i},
      localChange (k := k) E hlocalE ({xE} : Set E)
        (S.obj i.1) (S.indecomposable i.1) := by
    calc
      0 ≤ ∑ i : Fin S.n, f i := hsumAll
      _ = (∑ i : {i : Fin S.n // p i}, f i.1) +
          ∑ i : {i : Fin S.n // ¬ p i}, f i.1 := hpartition.symm
      _ = ∑ i : {i : Fin S.n // p i}, f i.1 := by rw [hzero, add_zero]
  have hsum := finiteSupport_localChangeSum_eq_f1
    (k := k) hP hlocal K W hsupport hNsupport hK x hx
  have hchangeE :
      finiteDeletionLocalChangeSum (k := k) E hlocalE ({xE} : Set E) W' =
        ∑ i : {i : Fin S.n // p i},
          localChange (k := k) E hlocalE ({xE} : Set E)
            (S.obj i.1) (S.indecomposable i.1) := by
    have hall := finiteDeletionLocalChangeSum_eq_skeletonSum
      (k := k) E hlocalE ({xE} : Set E) W' S (by
        intro i hi
        exact houtside i hi)
    calc
      finiteDeletionLocalChangeSum (k := k) E hlocalE ({xE} : Set E) W' =
          ∑ i : Fin S.n, localChange (k := k) E hlocalE ({xE} : Set E)
            (S.obj i) (S.indecomposable i) := hall
      _ = (∑ i : {i : Fin S.n // p i}, f i.1) +
          ∑ i : {i : Fin S.n // ¬ p i}, f i.1 := hpartition.symm
      _ = ∑ i : {i : Fin S.n // p i}, f i.1 := by rw [hzero, add_zero]
  rw [hsum]
  rw [hchangeE]
  exact hsumE

theorem finiteSupport_localChangeSum_rigidity_f1
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (hC : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (K : Set C) (hK : K.Finite) (x : C) (hx : x ∈ K)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hsupport : ∀ i : Fin W.n,
      moduleSupport k (W.obj i).obj.obj ⊆ K)
    (hNsupport : ∀ i : Fin W.n, ∀ j,
      moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j).obj.obj ⊆ K)
    (hcore : ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
      hlocal 2).isoClosure ⊆ W.isoClosure)
    (hzero : finiteDeletionLocalChangeSum (k := k) C hlocal ({x} : Set C) W = 0)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hMsupport : moduleSupport k M.obj.obj ⊆ K)
    (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
  classical
  let E := finiteSupportCategory (k := k) (C := C) K
  let hlocalE := finiteSupportCategory_isLocallyRepresentationFinite
    (k := k) (C := C) hlocal K
  let hPE := fun Y : E ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) C hP Kᶜ Y
  let hRE := finiteSupportCategory_localEndomorphismRings
    (k := k) (C := C) hC hlocalRing K
  let hCE := finiteSupportCategory_skeletal
    (k := k) (C := C) hC hlocalRing K
  let HE := finiteSupportCategory_directed
    (k := k) (C := C) H K
  letI : Finite E := finiteSupportCategory_finite (k := k) (C := C) K hK
  letI : Fintype E := Fintype.ofFinite _
  let hx' : x ∉ Kᶜ := by
    simpa only [Set.mem_compl_iff, not_not] using hx
  let xE : E := survivingObj (k := k) C Kᶜ hx'
  let W' := finiteSupportRestrictionFamily_f1 (k := k) hlocal K W hsupport
  let S := finiteSupportCategory_skeleton (k := k) (C := C) hP hlocal K hK
  let T := finiteSupportCategory_singleton_skeleton
    (k := k) (C := C) hP hlocal K hK xE
  let p : Fin S.n → Prop := fun i ↦ S.obj i ∈ W'.isoClosure
  letI : DecidablePred p := Classical.decPred _
  have houtside : ∀ i : Fin S.n, ¬ p i →
      localChange (k := k) E hlocalE ({xE} : Set E)
        (S.obj i) (S.indecomposable i) = 0 := by
    intro i hi
    apply finiteDeletionLocalChangeAt_eq_zero_of_not_mem_twoStep
      (k := k) E hPE hlocalE xE (S.obj i) (S.indecomposable i)
    intro hiCore
    apply hi
    obtain ⟨j, ⟨e⟩⟩ :=
      iterateHomNeighborhood_extensionByZero_mem
        (k := k) C hlocal x Kᶜ hx' 2 (S.obj i)
          (S.indecomposable i) hiCore
    have hExt :
        (finiteDimensionalModuleExtensionByZero (k := k) C Kᶜ).obj
            (S.obj i) ∈
          ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
            hlocal 2).isoClosure := ⟨j, ⟨e⟩⟩
    obtain ⟨t, ⟨et⟩⟩ := hcore hExt
    let ht := moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
      (k := k) C (W.obj t) K (hsupport t)
    let F := finiteDimensionalModuleExtensionByZero (k := k) C Kᶜ
    let qt := finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C Kᶜ (W.obj t) ht
    refine ⟨t, ⟨F.preimageIso (qt.trans et)⟩⟩
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := E) k) :=
    enoughProjectives_of_finiteRepresentables hPE
  let hPEdeleted := fun Y ↦
    ObjectDeletion.deletion_linearCoyoneda_isFiniteDimensional
      (k := k) E hPE ({xE} : Set E) Y
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := ObjectDeletion.DeletionCategory (k := k) E ({xE} : Set E)) k) :=
    enoughProjectives_of_finiteRepresentables hPEdeleted
  have hsurplus := finiteDeletionLocalChangeSum_eq_surplus_sub
    (k := k) E hlocalE ({xE} : Set E) W' S T (by
      intro i hi
      exact houtside i hi)
  have hsum := finiteSupport_localChangeSum_eq_f1
    (k := k) hP hlocal K W hsupport hNsupport hK x hx
  have hzeroQ : finiteDeletionLocalChangeSum (k := k) E hlocalE
      ({xE} : Set E) W' = 0 := by
    rw [← hsum]
    exact hzero
  have hdiff :
      @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            S.toFiniteRightTauCategoryData)
          S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) -
        @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) = 0 :=
    hsurplus.symm.trans hzeroQ
  have hEq := (sub_eq_zero.mp hdiff).symm
  let hMvanish :=
    moduleVanishesOnDeleted_compl_of_moduleSupport_subset_frozen
      (k := k) C M K hMsupport
  let RM := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C Kᶜ M hMvanish
  let hRM := finiteDimensionalModuleRestrictionToDeletion_indec
    (k := k) C Kᶜ M hM hMvanish
  let xE' : E := survivingObj (k := k) C Kᶜ (by
    simpa only [Set.mem_compl_iff, not_not] using hx)
  have hRMx : ¬ IsZero (RM.obj.obj.obj xE') := by
    intro hzeroM
    apply hMx
    let eM := finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C Kᶜ M hMvanish
    let J := (IsFiniteDimensionalModule.{u, v, v, v} (C := C) k).ι
    let Kfun := (IsLinearModule.{u, v, v, v} (C := C) k).ι
    let eX :
        (((finiteDimensionalModuleExtensionByZero (k := k) C Kᶜ).obj RM).obj.obj.obj x) ≅
          M.obj.obj.obj x :=
      (Kfun.mapIso (J.mapIso eM)).app x
    have hraw : ((rawFunctor (k := k) C Kᶜ).obj x).as = x := by rfl
    have hzeroF := (moduleExtensionByZeroObjIsoAt
      (k := k) C Kᶜ RM.obj.obj xE').isZero_iff.mpr hzeroM
    have hzeroFx : IsZero
        (((finiteDimensionalModuleExtensionByZero (k := k) C Kᶜ).obj RM).obj.obj.obj x) := by
      change IsZero (moduleExtensionByZeroObj (k := k) C Kᶜ RM.obj.obj x)
      simpa only [xE', survivingObj, hraw] using hzeroF
    exact eX.isZero_iff.mp hzeroFx
  have hdim :=
    finiteCategoryProjectiveGenerator.finrank_obj_eq_one_of_singletonDeletion_surplus_eq_of_fintype
      (k := k) hPE hRE hCE hlocalE HE xE S T hEq RM hRM hRMx
  let eM := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C Kᶜ M hMvanish
  let J := (IsFiniteDimensionalModule.{u, v, v, v} (C := C) k).ι
  let Kfun := (IsLinearModule.{u, v, v, v} (C := C) k).ι
  let eX :
      (((finiteDimensionalModuleExtensionByZero (k := k) C Kᶜ).obj RM).obj.obj.obj x) ≅
        M.obj.obj.obj x :=
    (Kfun.mapIso (J.mapIso eM)).app x
  have hfinExt : Module.finrank k (RM.obj.obj.obj xE') =
      Module.finrank k (((finiteDimensionalModuleExtensionByZero
        (k := k) C Kᶜ).obj RM).obj.obj.obj x) := by
    exact (moduleExtensionByZeroObjIsoAt
      (k := k) C Kᶜ RM.obj.obj xE').toLinearEquiv.finrank_eq.symm
  have hfinM : Module.finrank k (((finiteDimensionalModuleExtensionByZero
        (k := k) C Kᶜ).obj RM).obj.obj.obj x) =
      Module.finrank k (M.obj.obj.obj x) :=
    eX.toLinearEquiv.finrank_eq
  calc
    Module.finrank k (M.obj.obj.obj x) =
        Module.finrank k (((finiteDimensionalModuleExtensionByZero
          (k := k) C Kᶜ).obj RM).obj.obj.obj x) := hfinM.symm
    _ = Module.finrank k (RM.obj.obj.obj xE') := hfinExt.symm
    _ = 1 := by simpa only [RM, xE', hdim]

/-! A small automation boundary for the frozen route.  The two-step family
already contains the control core by definition; taking the union of its
supports and of the supports of all incoming neighbours supplies the finite
quotient required by the local theorem.  This is useful when the family is
reused for several earlier deletion sets. -/

noncomputable def finiteFiberControlDependencySupport_f1
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C) : Set C :=
  let W := (finiteFiberControlSeed hlocal x).iterateHomNeighborhood hlocal 2
  ({x} : Set C) ∪
    (⋃ i : Fin W.n, moduleSupport k (W.obj i).obj.obj) ∪
    (⋃ i : Fin W.n, ⋃ j : Fin
      (finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).n,
      moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j).obj.obj)

theorem finiteFiberControlDependencySupport_f1_finite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C) :
    (finiteFiberControlDependencySupport_f1 (k := k) hlocal x).Finite := by
  classical
  let W := (finiteFiberControlSeed hlocal x).iterateHomNeighborhood hlocal 2
  have hW : (⋃ i : Fin W.n, moduleSupport k (W.obj i).obj.obj).Finite := by
    exact Set.finite_iUnion fun i ↦ finite_moduleSupport k (W.obj i)
  have hN : (⋃ i : Fin W.n, ⋃ j : Fin
      ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).n),
      moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j).obj.obj).Finite := by
    exact Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦
      finite_moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j)
  simpa only [finiteFiberControlDependencySupport_f1, W, Set.union_assoc] using
    (Set.toFinite {x}).union (hW.union hN)

/- A reusable finite dependency set for an arbitrary finite family.  The
  distinguished object and every incoming-neighborhood support are included
  so that the support-quotient comparison can be applied without rebuilding
  this bookkeeping at each later deletion stage. -/
noncomputable def finiteFamilyDependencySupport_f1
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) : Set C :=
  ({x} : Set C) ∪
    (⋃ i : Fin W.n, moduleSupport k (W.obj i).obj.obj) ∪
    (⋃ i : Fin W.n, ⋃ j : Fin
      (finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).n,
      moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j).obj.obj)

theorem finiteFamilyDependencySupport_f1_finite
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) :
    (finiteFamilyDependencySupport_f1 (k := k) hlocal x W).Finite := by
  classical
  have hW : (⋃ i : Fin W.n, moduleSupport k (W.obj i).obj.obj).Finite := by
    exact Set.finite_iUnion fun i ↦ finite_moduleSupport k (W.obj i)
  have hN : (⋃ i : Fin W.n, ⋃ j : Fin
      ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).n),
      moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j).obj.obj).Finite := by
    exact Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦
      finite_moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j)
  simpa only [finiteFamilyDependencySupport_f1, Set.union_assoc] using
    (Set.toFinite {x}).union (hW.union hN)

/- The finite-support positivity theorem for any finite family containing the
  two-step control core.  The fixed control-family theorem below is a small
  specialization retained for the existing public names. -/
theorem finiteFamily_localChangeSum_nonnegative_f1
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (hC : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (x : C)
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hcore : ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
      hlocal 2).isoClosure ⊆ W.isoClosure) :
    0 ≤ finiteDeletionLocalChangeSum (k := k) C hlocal ({x} : Set C) W := by
  let K := finiteFamilyDependencySupport_f1 (k := k) hlocal x W
  have hK : K.Finite := finiteFamilyDependencySupport_f1_finite
    (k := k) hlocal x W
  have hx : x ∈ K := by
    change x ∈ ({x} : Set C) ∪ _ ∪ _
    exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_singleton x))
  have hsupport : ∀ i : Fin W.n,
      moduleSupport k (W.obj i).obj.obj ⊆ K := by
    intro i Y hY
    dsimp [K, finiteFamilyDependencySupport_f1]
    exact Set.mem_union_left _ (Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨i, hY⟩))
  have hNsupport : ∀ i : Fin W.n, ∀ j,
      moduleSupport k
        ((finiteIncomingHomNeighborhood (k := k) C hlocal (W.obj i)).obj j).obj.obj ⊆ K := by
    intro i j Y hY
    dsimp [K, finiteFamilyDependencySupport_f1]
    exact Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hY⟩⟩)
  exact finiteSupport_localChangeSum_nonnegative_f1
    (k := k) hP hlocal hlocalRing hC H K hK x hx W hsupport hNsupport hcore

theorem finiteFiberControl_localChangeSum_nonnegative_f1
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (hlocalRing : ∀ X : C, IsLocalRing (End X))
    (hC : Skeletal C)
    (H : HasAcyclicFiniteModuleNonzeroNonisomorphisms
      (k := k) (C := C))
    (x : C) :
    0 ≤ finiteDeletionLocalChangeSum (k := k) C hlocal ({x} : Set C)
      ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood hlocal 2) := by
  let W := (finiteFiberControlSeed hlocal x).iterateHomNeighborhood hlocal 2
  exact finiteFamily_localChangeSum_nonnegative_f1
    (k := k) hP hlocal hlocalRing hC H x W (by exact Set.Subset.rfl)

end MagnitudeConjecture.ObjectDeletion.Frozen
