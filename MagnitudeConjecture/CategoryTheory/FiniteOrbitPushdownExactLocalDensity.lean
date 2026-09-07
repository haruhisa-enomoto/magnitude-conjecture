import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownAuslanderReiten
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownProjective
import MagnitudeConjecture.CategoryTheory.FiniteOrbitRadicalComponents
import MagnitudeConjecture.CategoryTheory.FiniteSkeletonDensityInvariance
import MagnitudeConjecture.CategoryTheory.LocallyFiniteModuleLocalDensity

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G]
variable [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

set_option linter.unusedVariables false in
theorem finiteDimensionalModuleOrbitSkeletonPushdown_rightMiddleArity_eq_of_indec_trivialStabilizers
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (htrivial :
      letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := isLinearModule_stableUnderShift (k := k) D.core
      letI := linearModuleCategoryHasShift (k := k) D.core
      letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
      letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
      ∀ (X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
        Indecomposable X →
          ∀ a : Additive G, Nonempty (X ≅ X⟦a⟧) → a = 0)
    (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ∀ (T : FiniteDimensionalModuleIndecomposableSkeleton
        (k := k) (C := DeckOrbitSkeleton C G))
      [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
      [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)]
      (i : Fin S.n) (j : Fin T.n)
      (e : (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
          (S.obj i) ≅ T.obj j),
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
          S.toFiniteRightTauCategoryData i =
        MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
          T.toFiniteRightTauCategoryData j := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro T _ _ i j e
  letI : HasExt.{max u v}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  letI : HasExt.{max u v}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let TS := S.toFiniteRightTauCategoryData
  let TT := T.toFiniteRightTauCategoryData
  by_cases hM : Projective (S.obj i)
  · letI : Projective (S.obj i) := hM
    obtain ⟨X, ⟨eX⟩⟩ :=
      indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
        hP hlocal (S.obj i) (S.indecomposable i)
    let Q := finiteDimensionalLinearCoyoneda (k := k) X (hP X)
    let R := finiteDimensionalLinearCoyonedaRadical (k := k) X (hP X)
    let r : R ⟶ Q :=
      finiteDimensionalLinearCoyonedaRadicalInclusion (k := k) X (hP X)
    let d := Classical.choice
      (finiteDimensionalModule_finiteIndecomposableDecomposition R)
    let dMap := d.mapOfIndecomposable P fun t ↦
      D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
        (k := k) (d.summand t) (d.indecomposable t)
          (htrivial (d.summand t) (d.indecomposable t))
    have hrAS : IsRightAlmostSplit r :=
      finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
        hP hlocal X
    have hrMin : IsRightMinimal r := by
      intro a ha
      have haid : a = 𝟙 R := by
        apply (cancel_mono r).1
        simpa using ha
      rw [haid]
      infer_instance
    have hUpAS : IsRightAlmostSplit (r ≫ eX.hom) :=
      hrAS.postcomp_iso eX
    have hUpMin : IsRightMinimal (r ≫ eX.hom) :=
      hrMin.postcomp_iso eX
    have hUpArity :
        MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TS i = d.n :=
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
        TS i d hUpAS hUpMin
    let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
    let Qdown : DeckOrbitSkeleton C G :=
      (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
    let rDown := finiteDimensionalLinearCoyonedaRadicalInclusion (k := k)
      (C := DeckOrbitSkeleton C G) Qdown (hPdown Qdown)
    let eR := D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k) hP hlocal hfree X
    let eQ := D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) X (hP X)
    have hrDownAS : IsRightAlmostSplit rDown :=
      finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
        hPdown (D.orbitSkeleton_end_isLocalRing (k := k) hP hlocal hfree) Qdown
    have hleft : IsRightAlmostSplit (eR.hom ≫ rDown) :=
      MagnitudeConjecture.CategoryTheory.rightAlmostSplit_precomp_iso eR hrDownAS
    have hsquare : eR.hom ≫ rDown = P.map r ≫ eQ.hom :=
      D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalInclusion
        (k' := k) hP hlocal hfree X
    have hPrAS : IsRightAlmostSplit (P.map r) := by
      have hcomp : IsRightAlmostSplit (P.map r ≫ eQ.hom) := by
        rw [← hsquare]
        exact hleft
      have hback := hcomp.postcomp_iso eQ.symm
      simpa [Category.assoc] using hback
    have hPrMin : IsRightMinimal (P.map r) := by
      intro a ha
      have haid : a = 𝟙 (P.obj R) := by
        apply (cancel_mono (P.map r)).1
        simpa using ha
      rw [haid]
      infer_instance
    let eTarget : P.obj Q ≅ T.obj j := P.mapIso eX ≪≫ e
    have hDownAS : IsRightAlmostSplit (P.map r ≫ eTarget.hom) :=
      hPrAS.postcomp_iso eTarget
    have hDownMin : IsRightMinimal (P.map r ≫ eTarget.hom) :=
      hPrMin.postcomp_iso eTarget
    have hDownArity :
        MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TT j = dMap.n :=
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
        TT j dMap hDownAS hDownMin
    change MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TT j = d.n at hDownArity
    exact hUpArity.trans hDownArity.symm
  · let d :=
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition
        TS i
    let m := (TS.rightMesh (TS.obj i)).g ≫ (TS.rightTermIso (TS.obj i)).hom
    have hmAS : IsRightAlmostSplit m :=
      MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit TS i
    have hmMin : IsRightMinimal m :=
      MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightMinimal TS i
    obtain ⟨Q⟩ := twoStepMinimalFiniteRepresentablePresentation_nonempty
      hP hlocal (S.obj i)
    have hPmAS : IsRightAlmostSplit (P.map m) :=
      D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightAlmostSplit_of_indec_trivialStabilizers
        (k := k) hP hI hlocal hfree Q hM (S.indecomposable i)
          m hmAS hmMin htrivial
    have hPmMin : IsRightMinimal (P.map m) :=
      D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightMinimal_of_indec_trivialStabilizers
        (k := k) hP hI Q hM (S.indecomposable i)
          m hmAS hmMin htrivial
    let dMap := d.mapOfIndecomposable P fun t ↦
      D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
        (k := k) (d.summand t) (d.indecomposable t)
          (htrivial (d.summand t) (d.indecomposable t))
    have hDownAS : IsRightAlmostSplit (P.map m ≫ e.hom) :=
      hPmAS.postcomp_iso e
    have hDownMin : IsRightMinimal (P.map m ≫ e.hom) :=
      hPmMin.postcomp_iso e
    have hDownArity :
        MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TT j = dMap.n :=
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
        TT j dMap hDownAS hDownMin
    change MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TT j = d.n at hDownArity
    exact (show MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity TS i = d.n from rfl).trans
      hDownArity.symm

set_option linter.unusedVariables false in
theorem finiteDimensionalModuleOrbitSkeletonPushdown_rightTauLocalDensity_eq_of_indec_trivialStabilizers
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (htrivial :
      letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := isLinearModule_stableUnderShift (k := k) D.core
      letI := linearModuleCategoryHasShift (k := k) D.core
      letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
      letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
      ∀ (X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
        Indecomposable X →
          ∀ a : Additive G, Nonempty (X ≅ X⟦a⟧) → a = 0)
    (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ∀ (T : FiniteDimensionalModuleIndecomposableSkeleton
        (k := k) (C := DeckOrbitSkeleton C G))
      [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
      [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)]
      (i : Fin S.n) (j : Fin T.n)
      (e : (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
          (S.obj i) ≅ T.obj j),
      S.rightTauLocalDensity i = T.rightTauLocalDensity j := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro T _ _ i j e
  let TS := S.toFiniteRightTauCategoryData
  let TT := T.toFiniteRightTauCategoryData
  have hArity := D.finiteDimensionalModuleOrbitSkeletonPushdown_rightMiddleArity_eq_of_indec_trivialStabilizers hP hI hlocal hfree htrivial S T i j e
  have hProjective : TS.IsProjective i ↔ TT.IsProjective j := by
    rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj,
      MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
    constructor
    · intro h
      exact Projective.of_iso e
        (D.finiteDimensionalModuleOrbitSkeletonPushdown_projective
          (k := k) hP hlocal (S.obj i) h)
    · intro h
      apply D.projective_of_finiteDimensionalModuleOrbitSkeletonPushdown_projective
        (k := k) (S.obj i)
      exact Projective.of_iso e.symm h
  rw [FiniteDimensionalModuleIndecomposableSkeleton.rightTauLocalDensity,
    FiniteDimensionalModuleIndecomposableSkeleton.rightTauLocalDensity,
    MagnitudeConjecture.FiniteTauMatrix.occurrenceLocalDensity_rightArrowTarget_eq,
    MagnitudeConjecture.FiniteTauMatrix.occurrenceLocalDensity_rightArrowTarget_eq,
    ARCount.localDensityOfIncomingArity,
    ARCount.localDensityOfIncomingArity,
    hArity]
  by_cases h : S.toFiniteRightTauCategoryData.IsProjective i
  · have h' : T.toFiniteRightTauCategoryData.IsProjective j := hProjective.1 h
    simp [h, h']
  · have h' : ¬ T.toFiniteRightTauCategoryData.IsProjective j :=
      fun hT ↦ h (hProjective.2 hT)
    simp [h, h']

set_option linter.unusedVariables false in
/-- Exact local-density preservation viewed through a shift instance explicitly
identified with the coherent deck shift.  This is the non-normalizing transport
boundary used by residual orbit towers. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_rightTauLocalDensity_eq_of_indec_trivialStabilizers
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Additive)
    (hlinear : letI := H
      ∀ a : Additive G, (shiftFunctor C a).Linear k)
    (hH : H = D.hasShift)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (htrivial :
      letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := isLinearModule_stableUnderShift (k := k) D.core
      letI := linearModuleCategoryHasShift (k := k) D.core
      letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
      letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
      ∀ (X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
        Indecomposable X →
          ∀ a : Additive G, Nonempty (X ≅ X⟦a⟧) → a = 0)
    (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C)) :
    letI := H
    letI := hadd
    letI := hlinear
    ∀ (T : FiniteDimensionalModuleIndecomposableSkeleton
        (k := k) (C := DeckOrbitSkeleton C G))
      [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
      [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)]
      (i : Fin S.n) (j : Fin T.n)
      (e : (D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
          (k := k) H hadd hlinear hH).obj (S.obj i) ≅ T.obj j),
      S.rightTauLocalDensity i = T.rightTauLocalDensity j := by
  cases hH
  letI := D.hasShift
  letI := hadd
  letI := hlinear
  intro T _ _ i j e
  exact
    D.finiteDimensionalModuleOrbitSkeletonPushdown_rightTauLocalDensity_eq_of_indec_trivialStabilizers
      hP hI hlocal hfree htrivial S T i j e

set_option linter.unusedVariables false in
/-- Finite skeletal Gabriel push-down preserves the intrinsic local density
of an indecomposable finite-dimensional module.  Unlike the finite-skeleton
coordinate theorem above, this form only asks for local representation
finiteness on the two module categories. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_localDensity_eq
    [IsMulTorsionFree G]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hUp : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
    ∀ (hDown : IsLocallyRepresentationFinite
        (k := k) (C := DeckOrbitSkeleton C G))
      (hPM : Indecomposable (P.obj M)),
      finiteModuleLocalDensity hDown (P.obj M) hPM =
        finiteModuleLocalDensity hUp M hM := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  change ∀ (hDown : IsLocallyRepresentationFinite
      (k := k) (C := DeckOrbitSkeleton C G))
    (hPM : Indecomposable (P.obj M)),
    finiteModuleLocalDensity hDown (P.obj M) hPM =
      finiteModuleLocalDensity hUp M hM
  intro hDown hPM
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  letI : HasExt.{max u v}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  letI : HasExt.{max u v}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  by_cases hProjective : Projective M
  · letI : Projective M := hProjective
    obtain ⟨X, ⟨eX⟩⟩ :=
      indecomposable_projective_iso_finiteDimensionalLinearCoyoneda
        hP hlocal M hM
    let Q := finiteDimensionalLinearCoyoneda (k := k) X (hP X)
    let R := finiteDimensionalLinearCoyonedaRadical (k := k) X (hP X)
    let r : R ⟶ Q :=
      finiteDimensionalLinearCoyonedaRadicalInclusion (k := k) X (hP X)
    let d := Classical.choice
      (finiteDimensionalModule_finiteIndecomposableDecomposition R)
    let dMap := d.mapOfIndecomposable P fun t ↦
      D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
        (k := k) (d.summand t) (d.indecomposable t)
          (D.finiteDimensionalModule_trivialStabilizer
            (k := k) (d.summand t) (d.indecomposable t).1)
    have hrAS : IsRightAlmostSplit r :=
      finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
        hP hlocal X
    have hrMin : IsRightMinimal r := by
      intro a ha
      have haid : a = 𝟙 R := by
        apply (cancel_mono r).1
        simpa using ha
      rw [haid]
      infer_instance
    have hUpAS : IsRightAlmostSplit (r ≫ eX.hom) :=
      hrAS.postcomp_iso eX
    have hUpMin : IsRightMinimal (r ≫ eX.hom) :=
      hrMin.postcomp_iso eX
    let Qdown : DeckOrbitSkeleton C G :=
      (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
    let rDown := finiteDimensionalLinearCoyonedaRadicalInclusion (k := k)
      (C := DeckOrbitSkeleton C G) Qdown (hPdown Qdown)
    let eR := D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalLinearCoyonedaIso
      (k' := k) hP hlocal hfree X
    let eQ := D.finiteDimensionalModuleOrbitSkeletonPushdownLinearCoyonedaIso
      (k := k) X (hP X)
    have hrDownAS : IsRightAlmostSplit rDown :=
      finiteDimensionalLinearCoyonedaRadicalInclusion_isRightAlmostSplit
        hPdown (D.orbitSkeleton_end_isLocalRing (k := k) hP hlocal hfree) Qdown
    have hleft : IsRightAlmostSplit (eR.hom ≫ rDown) :=
      MagnitudeConjecture.CategoryTheory.rightAlmostSplit_precomp_iso eR hrDownAS
    have hsquare : eR.hom ≫ rDown = P.map r ≫ eQ.hom :=
      D.finiteDimensionalModuleOrbitSkeletonPushdownRadicalInclusion
        (k' := k) hP hlocal hfree X
    have hPrAS : IsRightAlmostSplit (P.map r) := by
      have hcomp : IsRightAlmostSplit (P.map r ≫ eQ.hom) := by
        rw [← hsquare]
        exact hleft
      have hback := hcomp.postcomp_iso eQ.symm
      simpa [Category.assoc] using hback
    have hPrMin : IsRightMinimal (P.map r) := by
      intro a ha
      have haid : a = 𝟙 (P.obj R) := by
        apply (cancel_mono (P.map r)).1
        simpa using ha
      rw [haid]
      infer_instance
    let eTarget : P.obj Q ≅ P.obj M := P.mapIso eX
    have hDownAS : IsRightAlmostSplit (P.map r ≫ eTarget.hom) :=
      hPrAS.postcomp_iso eTarget
    have hDownMin : IsRightMinimal (P.map r ≫ eTarget.hom) :=
      hPrMin.postcomp_iso eTarget
    have hUpDensity :=
      finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
        hUp M hM d hUpAS hUpMin
    have hDownDensity :=
      finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
        hDown (P.obj M) hPM dMap hDownAS hDownMin
    have hPProjective : Projective (P.obj M) :=
      D.finiteDimensionalModuleOrbitSkeletonPushdown_projective
        (k := k) hP hlocal M hProjective
    rw [hDownDensity, hUpDensity]
    change MagnitudeConjecture.ARCount.localDensityOfIncomingArity d.n
        (Projective (P.obj M)) =
      MagnitudeConjecture.ARCount.localDensityOfIncomingArity d.n
        (Projective M)
    simp [hProjective, hPProjective]
  · let A := finiteModuleMinimalSinkData hUp M hM
    let dMap := A.decomposition.mapOfIndecomposable P fun t ↦
      D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
        (k := k) (A.decomposition.summand t)
          (A.decomposition.indecomposable t)
          (D.finiteDimensionalModule_trivialStabilizer
            (k := k) (A.decomposition.summand t)
              (A.decomposition.indecomposable t).1)
    obtain ⟨Q⟩ := twoStepMinimalFiniteRepresentablePresentation_nonempty
      hP hlocal M
    have hDownAS : IsRightAlmostSplit (P.map A.map) :=
      D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightAlmostSplit
        (k := k) hP hI hlocal hfree Q hProjective hM
          A.map A.rightAlmostSplit A.rightMinimal
    have hDownMin : IsRightMinimal (P.map A.map) :=
      D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightMinimal_of_indec_trivialStabilizers
        (k := k) hP hI Q hProjective hM
          A.map A.rightAlmostSplit A.rightMinimal
          (fun X hX ↦ D.finiteDimensionalModule_trivialStabilizer
            (k := k) X hX.1)
    have hPNotProjective : ¬ Projective (P.obj M) := by
      intro h
      exact hProjective
        (D.projective_of_finiteDimensionalModuleOrbitSkeletonPushdown_projective
          (k := k) M h)
    have hUpDensity :=
      finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
        hUp M hM A.decomposition A.rightAlmostSplit A.rightMinimal
    have hDownDensity :=
      finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
        hDown (P.obj M) hPM dMap hDownAS hDownMin
    rw [hDownDensity, hUpDensity]
    change MagnitudeConjecture.ARCount.localDensityOfIncomingArity
        A.decomposition.n (Projective (P.obj M)) =
      MagnitudeConjecture.ARCount.localDensityOfIncomingArity
        A.decomposition.n (Projective M)
    simp [hProjective, hPNotProjective]

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
