import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownWindow
import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamPresentation
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAlmostSplitMinimal
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleTrivialStabilizer
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaKernelIndecomposable
import MagnitudeConjecture.CategoryTheory.OrbitPushdownNakayama
import MagnitudeConjecture.CategoryTheory.AlmostSplitShortExact

/-!
# Auslander--Reiten kernels under finite orbit push-down

For a minimal finite-representable presentation of a nonprojective
indecomposable module, the finite Nakayama kernel is the kernel of any chosen minimal right
almost-split map.  Exact orbit push-down transports that kernel, while the
finite-matrix Nakayama comparison identifies its image with the kernel of the
literal pushed Nakayama matrix.  This gives the presentation-dependent
`DTr`/almost-split identification used in the magnitude argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

set_option linter.unusedVariables false in
/-- The kernel of the literal pushed Nakayama matrix is the kernel of any
chosen minimal right almost-split map to the pushed module.  This is the
downstairs half of the comparison used to prove that an upstairs
almost-split sequence remains almost split after orbit push-down. -/
noncomputable def orbitSkeletonNakayamaKernelIso_downstreamKernel
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ∀ [hExt : HasExt.{w}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)]
      (hM : ¬ Projective
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M))
      (hMind : Indecomposable
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M))
      {N : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k}
      (m : N ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M)
      (hmAS : IsRightAlmostSplit m) (hmMin : IsRightMinimal m),
    kernel ((D.orbitSkeletonFiniteNakayamaRepresentableSumFunctor
      (k := k) hI).map Q.representingDifferential) ≅ kernel m := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  intro _ hM hMind N m hmAS hmMin
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hI' := D.orbitSkeletonDualLinearYonedaFinite (k := k) hI
  let R := D.orbitSkeletonTwoStepMinimalFiniteRepresentablePresentation
    (k := k) hP hlocal hfree Q
  let e := Classical.choice
    (R.nonempty_nakayamaKernelIso_kernel hI' hM hMind m hmAS hmMin)
  change kernel ((finiteNakayamaRepresentableSumFunctor
    (k := k) hI').map
      (D.orbitSkeletonTwoStepMinimalFiniteRepresentablePresentation
        (k := k) hP hlocal hfree Q).toTwoStepFiniteRepresentablePresentation.matrixDifferential) ≅
          kernel m at e
  rw [D.orbitSkeletonTwoStepMinimalFiniteRepresentablePresentation_representingDifferential
    (k := k) hP hlocal hfree Q] at e
  exact e

/-- The kernel of the literal pushed Nakayama matrix is the kernel of the
pushed chosen minimal right almost-split map. -/
noncomputable def orbitSkeletonNakayamaKernelIso_pushedKernel
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M)
    {N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (m : N ⟶ M) (hmAS : IsRightAlmostSplit m)
    (hmMin : IsRightMinimal m) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    kernel ((D.orbitSkeletonFiniteNakayamaRepresentableSumFunctor
      (k := k) hI).map Q.representingDifferential) ≅
      kernel ((D.finiteDimensionalModuleOrbitSkeletonPushdown
        (k := k)).map m) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let eAR := Classical.choice (Q.nonempty_nakayamaKernelIso_kernel
    hI hM hMind m hmAS hmMin)
  exact
    (D.finiteNakayamaKernelOrbitSkeletonPushdownIso
      (k := k) hI Q.representingDifferential).symm ≪≫
      P.mapIso eAR ≪≫
      PreservesKernel.iso P m

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Gabriel 3.6(a), in the finite skeletal orbit model, under its exact
module-theoretic stabilizer hypothesis: a minimal right-almost-split map
remains right almost split after push-down. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightAlmostSplit_of_indec_trivialStabilizers
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M)
    {N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (m : N ⟶ M) (hmAS : IsRightAlmostSplit m)
    (hmMin : IsRightMinimal m) :
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
    (∀ (X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
      Indecomposable X →
        ∀ a : Additive G, Nonempty (X ≅ X⟦a⟧) → a = 0) →
    ∀ [hExtDown : HasExt.{w}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)],
      IsRightAlmostSplit
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map m) := by
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
  intro htrivial hExtDown
  letI : HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) := hExtDown
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  have hQNotSplit : ¬ IsSplitEpi Q.augmentation.f := by
    intro hsplit
    apply hM
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    exact projective_of_retract
      (inferInstance : Projective Q.augmentation.source)
      s.section_ Q.augmentation.f s.id
  letI : Epi m := hmAS.epi_of_nonsplit_epi
    Q.augmentation.f hQNotSplit
  let S : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    ShortComplex.mk (kernel.ι m) m (kernel.condition m)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel m }
  have hleft : IsLeftAlmostSplit (kernel.ι m) :=
    hmAS.kernel_ι_isLeftAlmostSplit m hmMin
  let eUp := Classical.choice
    (Q.nonempty_nakayamaKernelIso_kernel hI hM hMind m hmAS hmMin)
  have hK : Indecomposable (kernel m) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eUp).mp
      (Q.nakayamaKernel_indecomposable hI hM hMind)
  have hMtrivial : ∀ a : Additive G,
      Nonempty (M ≅ M⟦a⟧) → a = 0 :=
    htrivial M hMind
  have hKtrivial : ∀ a : Additive G,
      Nonempty (kernel m ≅ (kernel m)⟦a⟧) → a = 0 :=
    htrivial (kernel m) hK
  let PS := S.map P
  have hPS : PS.ShortExact :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_map_shortExact S hS
  have hPmnonsplit : ¬ IsSplitEpi (P.map m) := by
    change ¬ IsSplitEpi PS.g
    exact
      D.finiteDimensionalModuleOrbitSkeletonPushdown_map_g_not_isSplitEpi
        S hS hleft
  letI : Epi (P.map m) := hPS.epi_g
  have hPMind : Indecomposable (P.obj M) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) M hMind hMtrivial
  have hPM : ¬ Projective (P.obj M) := by
    intro hprojective
    letI : Projective (P.obj M) := hprojective
    obtain ⟨s, hs⟩ := Projective.factors (𝟙 (P.obj M)) (P.map m)
    apply hPmnonsplit
    exact IsSplitEpi.mk'
      { section_ := s
        id := by simpa only using hs }
  let hP' := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hI' := D.orbitSkeletonDualLinearYonedaFinite (k := k) hI
  let R := D.orbitSkeletonTwoStepMinimalFiniteRepresentablePresentation
    (k := k) hP hlocal hfree Q
  obtain ⟨E₀, i₀, q₀, zero₀, hT₀, _, hq₀AS⟩ :=
    R.exists_stableSocleClass_realization_rightAlmostSplit
      hI' hPM hPMind
  obtain ⟨N', n, hnAS, hnMin⟩ :=
    finiteDimensionalModule_exists_rightMinimal_rightAlmostSplit q₀ hq₀AS
  letI : Epi n := hnAS.epi_of_nonsplit_epi (P.map m) hPmnonsplit
  let T : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    ShortComplex.mk (kernel.ι n) n (kernel.condition n)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_kernel n }
  let eDown := D.orbitSkeletonNakayamaKernelIso_downstreamKernel
    (k := k) (hExt := hExtDown) hP hI hlocal hfree Q
      hPM hPMind n hnAS hnMin
  let ePush := D.orbitSkeletonNakayamaKernelIso_pushedKernel
    (k := k) hP hI Q hM hMind m hmAS hmMin
  let e₁ : T.X₁ ≅ PS.X₁ :=
    eDown.symm ≪≫ ePush ≪≫ (PreservesKernel.iso P m).symm
  have hfac : ∀ q : PS.X₁ ⟶ PS.X₁, ¬ IsIso q →
      ∃ c : PS.X₂ ⟶ PS.X₁, PS.f ≫ c = q := by
    intro q hq
    change ∃ c : P.obj N ⟶ P.obj (kernel m),
      P.map (kernel.ι m) ≫ c = q
    exact
      D.finiteDimensionalModuleOrbitSkeletonPushdown_leftEndomorphism_factor_of_trivial_stabilizer
        (k := k) (kernel m) N hK (kernel.ι m) hleft hKtrivial q hq
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightAlmostSplit_of_leftEndomorphismFactorization
      hPS hT hnAS hPmnonsplit e₁ (Iso.refl _) hfac

set_option linter.unusedVariables false in
/-- The same exact stabilizer hypothesis makes the pushed right-almost-split
map right minimal.  The pushed kernel remains indecomposable, so the nonsplit
pushed kernel inclusion is radical; short exactness then forces minimality of
the terminal map. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightMinimal_of_indec_trivialStabilizers
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M)
    {N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (m : N ⟶ M) (hmAS : IsRightAlmostSplit m)
    (hmMin : IsRightMinimal m) :
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
    (∀ (X : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
      Indecomposable X →
        ∀ a : Additive G, Nonempty (X ≅ X⟦a⟧) → a = 0) →
    IsRightMinimal
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map m) := by
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
  intro htrivial
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  have hQNotSplit : ¬ IsSplitEpi Q.augmentation.f := by
    intro hsplit
    apply hM
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    exact projective_of_retract
      (inferInstance : Projective Q.augmentation.source)
      s.section_ Q.augmentation.f s.id
  letI : Epi m := hmAS.epi_of_nonsplit_epi
    Q.augmentation.f hQNotSplit
  let S : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    ShortComplex.mk (kernel.ι m) m (kernel.condition m)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel m }
  have hleft : IsLeftAlmostSplit (kernel.ι m) :=
    hmAS.kernel_ι_isLeftAlmostSplit m hmMin
  let eUp := Classical.choice
    (Q.nonempty_nakayamaKernelIso_kernel hI hM hMind m hmAS hmMin)
  have hK : Indecomposable (kernel m) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eUp).mp
      (Q.nakayamaKernel_indecomposable hI hM hMind)
  have hKtrivial : ∀ a : Additive G,
      Nonempty (kernel m ≅ (kernel m)⟦a⟧) → a = 0 :=
    htrivial (kernel m) hK
  let PS := S.map P
  have hPS : PS.ShortExact :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_map_shortExact S hS
  have hPKind : Indecomposable (P.obj (kernel m)) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) (kernel m) hK hKtrivial
  have hPfnonsplit : ¬ IsSplitMono (P.map (kernel.ι m)) := by
    intro hsplit
    exact hleft.not_isSplitMono
      (D.finiteDimensionalModuleOrbitSkeletonPushdown_reflects_splitMono
        (k := k) (kernel m) N (kernel.ι m) hsplit)
  have hPfRadical : IsRadicalMorphism (P.map (kernel.ι m)) := by
    letI : IsLocalRing (End (P.obj (kernel m))) :=
      finiteDimensionalModule_end_isLocalRing k (P.obj (kernel m)) hPKind
    exact
      (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
        hPKind.1 (P.map (kernel.ι m))).2 hPfnonsplit
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_isRadicalMorphism_f
      hPS hPfRadical

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Gabriel 3.6(a), specialized to a torsion-free deck group acting freely on
objects.  Finite support supplies the indecomposable-module stabilizer
hypothesis of the exact theorem above. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightAlmostSplit
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    [IsMulTorsionFree G]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M)
    {N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (m : N ⟶ M) (hmAS : IsRightAlmostSplit m)
    (hmMin : IsRightMinimal m) :
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
    ∀ [hExtDown : HasExt.{w}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)],
      IsRightAlmostSplit
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map m) := by
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
  intro hExtDown
  exact D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightAlmostSplit_of_indec_trivialStabilizers
    (k := k) hP hI hlocal hfree Q hM hMind m hmAS hmMin
      (fun X hX ↦ D.finiteDimensionalModule_trivialStabilizer
        (k := k) X hX.1)

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Density-free left-handed form of Gabriel 3.6(a): the push-down of a
left almost-split monomorphism with indecomposable source is left almost
split.  The proof rotates the morphism to its right-almost-split cokernel,
uses the right-handed push-down theorem, and rotates the mapped short exact
sequence back. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_map_isLeftAlmostSplit
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    [IsMulTorsionFree G]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {L E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : L ⟶ E) [Mono f]
    (hf : IsLeftAlmostSplit f) (hmin : IsLeftMinimal f)
    (hL : Indecomposable L) :
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
    ∀ [hExtDown : HasExt.{w}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)],
      IsLeftAlmostSplit
        ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map f) := by
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
  intro hExtDown
  letI : HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) := hExtDown
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let q : E ⟶ cokernel f := cokernel.π f
  let S : ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    ShortComplex.mk f q (cokernel.condition f)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_cokernel f }
  have hqAS : IsRightAlmostSplit q :=
    MagnitudeConjecture.CategoryTheory.leftAlmostSplit_cokernel_π_isRightAlmostSplit
      f hf hmin
  have hfRadical : IsRadicalMorphism f := by
    letI : IsLocalRing (End L) :=
      finiteDimensionalModule_end_isLocalRing k L hL
    exact
      (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
        hL.1 f).2 hf.not_isSplitMono
  have hqMin : IsRightMinimal q :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_isRadicalMorphism_f
      hS hfRadical
  have hQind : Indecomposable (cokernel f) :=
    MagnitudeConjecture.CategoryTheory.IsRightAlmostSplit.target_indecomposable
      q hqAS
  have hQNotProjective : ¬ Projective (cokernel f) := by
    intro hprojective
    letI : Projective (cokernel f) := hprojective
    obtain ⟨s, hs⟩ := Projective.factors (𝟙 (cokernel f)) q
    apply hqAS.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := s
        id := by simpa only using hs }
  obtain ⟨Q⟩ :=
    twoStepMinimalFiniteRepresentablePresentation_nonempty
      hP hlocal (cokernel f)
  have hPqAS : IsRightAlmostSplit (P.map q) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightAlmostSplit
      (k := k) hP hI hlocal hfree Q hQNotProjective hQind
        q hqAS hqMin
  let PS := S.map P
  have hPS : PS.ShortExact :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_map_shortExact S hS
  have hPLind : Indecomposable (P.obj L) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) L hL
        (D.finiteDimensionalModule_trivialStabilizer (k := k) L hL.1)
  have hPfnonsplit : ¬ IsSplitMono (P.map f) := by
    intro hsplit
    exact hf.not_isSplitMono
      (D.finiteDimensionalModuleOrbitSkeletonPushdown_reflects_splitMono
        (k := k) L E f hsplit)
  have hPfRadical : IsRadicalMorphism (P.map f) := by
    letI : IsLocalRing (End (P.obj L)) :=
      finiteDimensionalModule_end_isLocalRing k (P.obj L) hPLind
    exact
      (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
        hPLind.1 (P.map f)).2 hPfnonsplit
  have hPqMin : IsRightMinimal (P.map q) :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_isRadicalMorphism_f
      hPS hPfRadical
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isLeftAlmostSplit_f_of_rightAlmostSplit_g
      hPS hPqAS hPqMin

set_option linter.unusedVariables false in
/-- On any full module window, the pushed minimal right almost-split map is
right almost split downstairs, and its kernel is the kernel of the literal
pushed Nakayama matrix.  This is the window-shaped form of the density-free
finite-skeletal Gabriel 3.6(a) theorem. -/
theorem orbitSkeletonNakayamaKernel_identifies_pushedRightAlmostSplit
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    [IsMulTorsionFree G]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (W : Set
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
    {X Y : CoveringSeparation.WindowCategory W} (m : X ⟶ Y)
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP Y.1)
    (hM : ¬ Projective Y.1) (hMind : Indecomposable Y.1)
    (hmAS : IsRightAlmostSplit m.hom)
    (hmMin : IsRightMinimal m.hom) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ∀ [hExtDown : HasExt.{w}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)],
      IsRightAlmostSplit
          ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
            (k := k) W).map m) ∧
        Nonempty
          (kernel ((D.orbitSkeletonFiniteNakayamaRepresentableSumFunctor
            (k := k) hI).map Q.representingDifferential) ≅
          kernel ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
            (k := k) W).map m)) := by
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
  intro hExtDown
  letI : HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) := hExtDown
  constructor
  · exact D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightAlmostSplit
      (k := k) hP hI hlocal hfree Q hM hMind m.hom hmAS hmMin
  · exact ⟨D.orbitSkeletonNakayamaKernelIso_pushedKernel
      (k := k) hP hI Q hM hMind m.hom hmAS hmMin⟩

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
