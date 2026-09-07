import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleRightTau
import MagnitudeConjecture.CategoryTheory.FiniteTauOccurrences
import MagnitudeConjecture.CategoryTheory.AlmostSplitEquivalence
import MagnitudeConjecture.Combinatorics.OrbitQuotientAction
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton

universe u v uK w

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type w} [Group G]

private abbrev ModuleCategory
    (C : Type u) [Category.{v} C] [Preadditive C]
    (k : Type uK) [Field k] [CategoryTheory.Linear k C] :=
  FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k

variable [HasShift (ModuleCategory C k) (Additive G)]
variable [∀ a : Additive G,
  (shiftFunctor (ModuleCategory C k) a).Additive]

variable (S : FiniteDimensionalModuleIndecomposableSkeleton
  (k := k) (C := C))

private theorem shift_obj_indecomposable (g : G) (i : Fin S.n) :
    Indecomposable
      ((shiftFunctor (ModuleCategory C k) (Additive.ofMul g⁻¹)).obj (S.obj i)) :=
  by
    let F := shiftFunctor (ModuleCategory C k) (Additive.ofMul g⁻¹)
    letI : F.Additive := inferInstance
    letI : F.IsEquivalence := inferInstance
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        F (S.obj i)).2 (S.indecomposable i)

/-- The skeleton label representing the inverse shift of a chosen
indecomposable.  The inverse makes this a left group action on labels. -/
noncomputable def shiftLabel (g : G) (i : Fin S.n) : Fin S.n :=
  Classical.choose
    (S.complete
      ((shiftFunctor (ModuleCategory C k) (Additive.ofMul g⁻¹)).obj (S.obj i))
      (S.shift_obj_indecomposable g i))

/-- Chosen identification of a shifted indecomposable with its strict
skeleton representative. -/
noncomputable def shiftLabelIso (g : G) (i : Fin S.n) :
    (shiftFunctor (ModuleCategory C k) (Additive.ofMul g⁻¹)).obj (S.obj i) ≅
      S.obj (S.shiftLabel g i) :=
  Classical.choice
    (Classical.choose_spec
      (S.complete
        ((shiftFunctor (ModuleCategory C k) (Additive.ofMul g⁻¹)).obj (S.obj i))
        (S.shift_obj_indecomposable g i)))

@[simp]
theorem shiftLabel_one (i : Fin S.n) : S.shiftLabel (1 : G) i = i := by
  apply S.skeletal
  refine ⟨(S.shiftLabelIso (1 : G) i).symm ≪≫ ?_⟩
  simpa using (shiftFunctorZero (ModuleCategory C k) (Additive G)).app (S.obj i)

theorem shiftLabel_mul (g h : G) (i : Fin S.n) :
    S.shiftLabel (g * h) i = S.shiftLabel g (S.shiftLabel h i) := by
  apply S.skeletal
  let a : Additive G := Additive.ofMul h⁻¹
  let b : Additive G := Additive.ofMul g⁻¹
  let eAdd :
      (shiftFunctor (ModuleCategory C k) (Additive.ofMul (g * h)⁻¹)).obj (S.obj i) ≅
        (shiftFunctor (ModuleCategory C k) b).obj
          ((shiftFunctor (ModuleCategory C k) a).obj (S.obj i)) := by
    rw [show Additive.ofMul (g * h)⁻¹ = a + b by simp [a, b]]
    exact (shiftFunctorAdd (ModuleCategory C k) a b).app (S.obj i)
  let eMap := (shiftFunctor (ModuleCategory C k) b).mapIso (S.shiftLabelIso h i)
  exact ⟨(S.shiftLabelIso (g * h) i).symm ≪≫ eAdd ≪≫ eMap ≪≫
    S.shiftLabelIso g (S.shiftLabel h i)⟩

/-- A coherent shift becomes a strict action on the labels of a duplicate-free
indecomposable skeleton. -/
@[implicit_reducible]
noncomputable def labelMulAction : MulAction G (Fin S.n) where
  smul := S.shiftLabel
  one_smul := S.shiftLabel_one
  mul_smul := S.shiftLabel_mul

/-- The finite orbit quotient of the strict skeleton-label action. -/
@[implicit_reducible]
noncomputable def labelOrbitFintype :
    letI := S.labelMulAction (G := G)
    Fintype (MulAction.orbitRel.Quotient G (Fin S.n)) := by
  letI := S.labelMulAction (G := G)
  exact Fintype.ofFinite _

/-- Freeness of the coherent shift on the represented isomorphism classes. -/
def IsShiftFreeOnLabels : Prop :=
  ∀ (g : G) (i : Fin S.n),
    Nonempty
      ((shiftFunctor (ModuleCategory C k) (Additive.ofMul g⁻¹)).obj (S.obj i) ≅
        S.obj i) →
      g = 1

omit [∀ a : Additive G,
  (shiftFunctor (ModuleCategory C k) a).Additive] in
/-- Freeness on the labels of a complete skeleton gives a trivial shift
stabilizer for every indecomposable object in the ambient module category. -/
theorem indecomposable_trivialStabilizer_of_isShiftFreeOnLabels
    (hfree : S.IsShiftFreeOnLabels (G := G))
    (X : ModuleCategory C k) (hX : Indecomposable X) :
    ∀ a : Additive G, Nonempty (X ≅ X⟦a⟧) → a = 0 := by
  intro a ha
  obtain ⟨i, ⟨e⟩⟩ := S.complete X hX
  let g : G := a.toMul⁻¹
  have hga : Additive.ofMul g⁻¹ = a := by
    apply Additive.toMul.injective
    simp [g]
  obtain ⟨h⟩ := ha
  let eShift := (shiftFunctor (ModuleCategory C k) a).mapIso e
  have hg : g = 1 := by
    apply hfree g i
    rw [hga]
    exact ⟨eShift.symm ≪≫ h.symm ≪≫ e⟩
  apply Additive.toMul.injective
  exact inv_eq_one.mp (by simpa [g] using hg)

/-- A shift free on represented isomorphism classes induces a free strict
action on skeleton labels. -/
theorem labelMulAction_isCancelSMul
    (hfree : S.IsShiftFreeOnLabels (G := G)) :
    letI := S.labelMulAction (G := G)
    IsCancelSMul G (Fin S.n) := by
  letI := S.labelMulAction (G := G)
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g i hgi
  apply hfree g i
  have e := S.shiftLabelIso g i
  change S.shiftLabel g i = i at hgi
  rw [hgi] at e
  exact ⟨e⟩

section RightTau

variable [EnoughProjectives (ModuleCategory C k)]

private abbrev rightTauData := S.toFiniteRightTauCategoryData

/-- Local density of a strict indecomposable skeleton label. -/
noncomputable def rightTauLocalDensity (i : Fin S.n) : ℤ :=
  CoveringAction.occurrenceLocalDensity
    (MagnitudeConjecture.FiniteTauMatrix.rightArrowTarget S.rightTauData)
    S.rightTauData.IsProjective i

/-- The total right-tau local density of a finite indecomposable skeleton is
its Auslander--Reiten surplus. -/
theorem sum_rightTauLocalDensity_eq_surplus :
    (∑ i : Fin S.n, S.rightTauLocalDensity i) =
      @ARCount.surplus (Fin S.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity S.rightTauData)
        S.rightTauData.IsProjective (Classical.decPred _) := by
  classical
  letI : DecidablePred S.rightTauData.IsProjective := Classical.decPred _
  calc
    (∑ i : Fin S.n, S.rightTauLocalDensity i) =
        ∑ i : Fin S.n,
          ARCount.localDensity
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              S.rightTauData)
            S.rightTauData.IsProjective i := by
      apply Finset.sum_congr rfl
      intro i _
      exact
        (MagnitudeConjecture.FiniteTauMatrix.localDensity_eq_occurrenceLocalDensity
          S.rightTauData i).symm
    _ = ARCount.surplus
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity S.rightTauData)
        S.rightTauData.IsProjective :=
      ARCount.sum_localDensity_eq_surplus _ _

/-- Incoming right-mesh arity is invariant under the strict skeleton-label
action induced by shifts. -/
theorem rightMiddleArity_shiftLabel (g : G) (i : Fin S.n) :
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity S.rightTauData
        (S.shiftLabel g i) =
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity S.rightTauData i := by
  let T := S.rightTauData
  let a : Additive G := Additive.ofMul g⁻¹
  let E := shiftEquiv (ModuleCategory C k) a
  let F := shiftFunctor (ModuleCategory C k) a
  letI : F.Additive := inferInstance
  letI : F.IsEquivalence := inferInstance
  let d := MagnitudeConjecture.FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition
    T i
  let dMap := d.mapOfIndecomposable F fun j ↦
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      F (d.summand j)).2 (d.indecomposable j)
  let m := (T.rightMesh (T.obj i)).g ≫ (T.rightTermIso (T.obj i)).hom
  let e : F.obj (T.obj i) ≅ T.obj (S.shiftLabel g i) :=
    S.shiftLabelIso g i
  have hmAS : IsRightAlmostSplit m :=
    MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit T i
  have hmMin : IsRightMinimal m :=
    MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightMinimal T i
  have hmapAS : IsRightAlmostSplit (E.functor.map m ≫ e.hom) :=
    (hmAS.map_equivalence E).postcomp_iso e
  have hmapMin : IsRightMinimal (E.functor.map m ≫ e.hom) :=
    (hmMin.map_equivalence E).postcomp_iso e
  exact MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
    T (S.shiftLabel g i) dMap hmapAS hmapMin

/-- The finite-right-tau projectivity predicate is invariant under the
strict skeleton-label action induced by shifts. -/
theorem isProjective_shiftLabel_iff (g : G) (i : Fin S.n) :
    S.rightTauData.IsProjective (S.shiftLabel g i) ↔
      S.rightTauData.IsProjective i := by
  let T := S.rightTauData
  let a : Additive G := Additive.ofMul g⁻¹
  let E := shiftEquiv (ModuleCategory C k) a
  let e : E.functor.obj (T.obj i) ≅ T.obj (S.shiftLabel g i) :=
    S.shiftLabelIso g i
  rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj,
    MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
  constructor
  · intro h
    have hshift : Projective (E.functor.obj (T.obj i)) :=
      Projective.of_iso e.symm h
    exact (E.map_projective_iff (T.obj i)).1 hshift
  · intro h
    have hshift : Projective (E.functor.obj (T.obj i)) :=
      (E.map_projective_iff (T.obj i)).2 h
    exact Projective.of_iso e hshift

/-- The canonical finite-right-tau local density is invariant under the
strict skeleton-label action induced by shifts. -/
theorem occurrenceLocalDensity_shiftLabel (g : G) (i : Fin S.n) :
    CoveringAction.occurrenceLocalDensity
        (MagnitudeConjecture.FiniteTauMatrix.rightArrowTarget S.rightTauData)
        S.rightTauData.IsProjective (S.shiftLabel g i) =
      CoveringAction.occurrenceLocalDensity
        (MagnitudeConjecture.FiniteTauMatrix.rightArrowTarget S.rightTauData)
        S.rightTauData.IsProjective i := by
  classical
  rw [MagnitudeConjecture.FiniteTauMatrix.occurrenceLocalDensity_rightArrowTarget_eq,
    MagnitudeConjecture.FiniteTauMatrix.occurrenceLocalDensity_rightArrowTarget_eq,
    ARCount.localDensityOfIncomingArity,
    ARCount.localDensityOfIncomingArity]
  rw [S.rightMiddleArity_shiftLabel g i]
  by_cases h : S.rightTauData.IsProjective i <;>
    simp [h, S.isProjective_shiftLabel_iff g i]

theorem rightTauLocalDensity_shiftLabel (g : G) (i : Fin S.n) :
    S.rightTauLocalDensity (S.shiftLabel g i) =
      S.rightTauLocalDensity i :=
  S.occurrenceLocalDensity_shiftLabel g i

/-- Action-form version of local-density invariance. -/
theorem rightTauLocalDensity_smul :
    letI := S.labelMulAction (G := G)
    ∀ (g : G) (i : Fin S.n),
      S.rightTauLocalDensity (g • i) = S.rightTauLocalDensity i := by
  letI := S.labelMulAction (G := G)
  intro g i
  exact S.rightTauLocalDensity_shiftLabel g i

/-- Total finite-right-tau local density scales over the free quotient of
the strict skeleton-label action. -/
theorem sum_occurrenceLocalDensity_eq_card_mul_orbitSum
    [Fintype G]
    (hfree : S.IsShiftFreeOnLabels (G := G)) :
    letI := S.labelMulAction (G := G)
    letI := S.labelOrbitFintype (G := G)
    (∑ i : Fin S.n, S.rightTauLocalDensity i) =
      (Fintype.card G : ℤ) *
        ∑ q : MulAction.orbitRel.Quotient G (Fin S.n),
          CoveringAction.orbitInvariantDescend
            S.rightTauLocalDensity S.rightTauLocalDensity_smul q := by
  classical
  letI := S.labelMulAction (G := G)
  letI := S.labelOrbitFintype (G := G)
  letI : IsCancelSMul G (Fin S.n) := S.labelMulAction_isCancelSMul hfree
  exact CoveringAction.sum_eq_card_mul_sum_orbitInvariantDescend
    S.rightTauLocalDensity S.rightTauLocalDensity_smul

end RightTau

end MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton
