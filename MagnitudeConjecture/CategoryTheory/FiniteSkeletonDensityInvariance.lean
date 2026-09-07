import MagnitudeConjecture.CategoryTheory.FiniteSkeletonShiftAction

/-!
# Local-density invariance between finite indecomposable skeletons

Two complete duplicate-free skeletons of the same finite-dimensional module
category have equivalent label types.  Isomorphic represented modules have
the same projective status and the same number of indecomposable occurrences
in a minimal right almost-split source, so their right-tau local densities
agree.  Consequently the total local density is independent of the chosen
skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

variable (S T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C))

/-- The label of `T` representing the object at a label of `S`. -/
noncomputable def relabel (i : Fin S.n) : Fin T.n :=
  Classical.choose (T.complete (S.obj i) (S.indecomposable i))

/-- The chosen object isomorphism underlying relabelling between complete
duplicate-free indecomposable skeletons. -/
noncomputable def relabelIso (i : Fin S.n) :
    S.obj i ≅ T.obj (S.relabel T i) :=
  Classical.choice
    (Classical.choose_spec (T.complete (S.obj i) (S.indecomposable i)))

theorem relabel_injective : Function.Injective (S.relabel T) := by
  intro i j hij
  apply S.skeletal
  exact ⟨S.relabelIso T i ≪≫
    eqToIso (congrArg T.obj hij) ≪≫ (S.relabelIso T j).symm⟩

theorem relabel_surjective : Function.Surjective (S.relabel T) := by
  intro j
  obtain ⟨i, ⟨e⟩⟩ := S.complete (T.obj j) (T.indecomposable j)
  refine ⟨i, ?_⟩
  apply T.skeletal
  exact ⟨(S.relabelIso T i).symm ≪≫ e.symm⟩

/-- Any two complete duplicate-free indecomposable skeletons of the same
finite-dimensional module category have canonically chosen equivalent label
types. -/
noncomputable def relabelEquiv : Fin S.n ≃ Fin T.n :=
  Equiv.ofBijective (S.relabel T)
    ⟨S.relabel_injective T, S.relabel_surjective T⟩

@[simp]
theorem relabelEquiv_apply (i : Fin S.n) :
    S.relabelEquiv T i = S.relabel T i := rfl

variable [EnoughProjectives
  (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)]

/-- Isomorphic represented indecomposables have the same incoming
right-mesh arity in any two complete skeletons. -/
theorem rightMiddleArity_eq_of_obj_iso
    (i : Fin S.n) (j : Fin T.n) (e : S.obj i ≅ T.obj j) :
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        S.toFiniteRightTauCategoryData i =
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        T.toFiniteRightTauCategoryData j := by
  let TS := S.toFiniteRightTauCategoryData
  let TT := T.toFiniteRightTauCategoryData
  let d :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition
      TS i
  let m := (TS.rightMesh (TS.obj i)).g ≫ (TS.rightTermIso (TS.obj i)).hom
  have hmAS : IsRightAlmostSplit m :=
    MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit TS i
  have hmMin : IsRightMinimal m :=
    MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightMinimal TS i
  have hmAS' : IsRightAlmostSplit (m ≫ e.hom) := hmAS.postcomp_iso e
  have hmMin' : IsRightMinimal (m ≫ e.hom) := hmMin.postcomp_iso e
  exact
    (MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      TT j d hmAS' hmMin').symm

/-- Isomorphic represented indecomposables have matching projectivity
predicates in any two complete skeletons. -/
theorem isProjective_iff_of_obj_iso
    (i : Fin S.n) (j : Fin T.n) (e : S.obj i ≅ T.obj j) :
    S.toFiniteRightTauCategoryData.IsProjective i ↔
      T.toFiniteRightTauCategoryData.IsProjective j := by
  rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj,
    MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
  exact ⟨fun h ↦ Projective.of_iso e h,
    fun h ↦ Projective.of_iso e.symm h⟩

/-- Isomorphic represented indecomposables have the same right-tau local
density in any two complete skeletons. -/
theorem rightTauLocalDensity_eq_of_obj_iso
    (i : Fin S.n) (j : Fin T.n) (e : S.obj i ≅ T.obj j) :
    S.rightTauLocalDensity i = T.rightTauLocalDensity j := by
  classical
  rw [rightTauLocalDensity, rightTauLocalDensity,
    MagnitudeConjecture.FiniteTauMatrix.occurrenceLocalDensity_rightArrowTarget_eq,
    MagnitudeConjecture.FiniteTauMatrix.occurrenceLocalDensity_rightArrowTarget_eq,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    S.rightMiddleArity_eq_of_obj_iso T i j e]
  by_cases h : S.toFiniteRightTauCategoryData.IsProjective i
  · have h' : T.toFiniteRightTauCategoryData.IsProjective j :=
      (S.isProjective_iff_of_obj_iso T i j e).1 h
    simp [h, h']
  · have h' : ¬ T.toFiniteRightTauCategoryData.IsProjective j := by
      intro hT
      exact h ((S.isProjective_iff_of_obj_iso T i j e).2 hT)
    simp [h, h']

/-- The total right-tau local density is independent of the chosen complete
duplicate-free indecomposable skeleton. -/
theorem sum_rightTauLocalDensity_eq :
    (∑ i : Fin S.n, S.rightTauLocalDensity i) =
      ∑ j : Fin T.n, T.rightTauLocalDensity j := by
  classical
  exact Fintype.sum_bijective (S.relabelEquiv T)
    (S.relabelEquiv T).bijective S.rightTauLocalDensity T.rightTauLocalDensity
    fun i ↦ S.rightTauLocalDensity_eq_of_obj_iso T i (S.relabel T i)
      (S.relabelIso T i)

end MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton
