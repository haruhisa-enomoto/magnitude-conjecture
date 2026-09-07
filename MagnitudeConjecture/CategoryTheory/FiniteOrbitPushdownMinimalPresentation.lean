import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownAlmostSplit
import MagnitudeConjecture.CategoryTheory.OrbitPushdownNakayama
import MagnitudeConjecture.CategoryTheory.RadicalMinimality
import MagnitudeConjecture.CategoryTheory.RepresentableDeckShift

/-!
# Minimal projective presentations under finite orbit push-down

Finite skeletal orbit push-down preserves radical maps from indecomposable
modules with trivial deck stabilizer.  Applying this entrywise to a minimal
finite-representable presentation proves that its pushed augmentation remains
right minimal.  The only presentation-specific input is trivial stabilizer
for the representing summands.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe uC vC uG uK

variable {k : Type uK} [Field k]
variable {C : Type uC} [Category.{vC} C]
variable {G : Type uG} [Group G] [MulAction G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]
variable [IsCancelSMul G C]

set_option backward.isDefEq.respectTransparency false in
/-- The finite sums of representables on the orbit skeleton are projective. -/
theorem orbitSkeletonFiniteProjectiveRepresentableSum_projective
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (Q : Mat_ (Cᵒᵖ)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Projective
      ((D.orbitSkeletonFiniteProjectiveRepresentableSumFunctor
        (k := k) hP).obj Q) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let R := fun i : Q.ι ↦
    (D.orbitSkeletonFiniteDimensionalLinearCoyonedaFunctor
      (k := k) hP).obj (Q.X i)
  change Projective (⨁ R)
  letI (i : Q.ι) : Projective (R i) := by
    apply finiteDimensionalLinearCoyoneda_projective
      (k := k)
      (X := D.orbitSkeletonFunctor.obj (Q.X i).unop)
      ((D.orbitSkeletonFiniteDimensionalLinearCoyonedaFunctor
        (k := k) hP).obj (Q.X i)).property
  constructor
  intro E X f e hepi
  refine ⟨biproduct.desc (fun i ↦
    Projective.factorThru (biproduct.ι R i ≫ f) e), ?_⟩
  apply biproduct.hom_ext'
  intro i
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Orbit push-down of a finite sum of projective representables is
projective, via the literal downstairs representable comparison. -/
theorem finiteProjectiveRepresentableSumOrbitSkeletonPushdown_projective
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (Q : Mat_ (Cᵒᵖ)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Projective
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj Q)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let e :=
    (D.finiteProjectiveRepresentableSumOrbitSkeletonPushdownIso
      (k := k) hP).app Q
  exact Projective.of_iso e.symm
    (D.orbitSkeletonFiniteProjectiveRepresentableSum_projective
      (k := k) hP Q)

set_option backward.isDefEq.respectTransparency false in
/-- Finite skeletal orbit push-down preserves radical morphisms whose source
is indecomposable and has trivial deck stabilizer. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_map_isRadicalMorphism
    (M N : FiniteDimensionalModuleCategory.{uC, vC, uK, uG} (C := C) k)
    (f : M ⟶ N) (hM : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    (∀ a : Additive G, Nonempty (M ≅ M⟦a⟧) → a = 0) →
      IsRadicalMorphism f →
        IsRadicalMorphism
          ((D.finiteDimensionalModuleOrbitSkeletonPushdown
            (k := k)).map f) := by
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
    (LinearModuleCategory.{uC, max vC uG, uK, uG}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro htrivial hf
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  have hPM : Indecomposable (P.obj M) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) M hM htrivial
  letI : IsLocalRing (End (P.obj M)) :=
    finiteDimensionalModule_end_isLocalRing k (P.obj M) hPM
  apply (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
    hPM.1 (P.map f)).2
  intro hsplit
  have hsplitUp : IsSplitMono f :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_reflects_splitMono
      (k := k) M N f hsplit
  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hM
  exact
    ((MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      hM.1 f).1 hf) hsplitUp

set_option backward.isDefEq.respectTransparency false in
/-- Finite skeletal orbit push-down preserves a radical map between finite
biproducts when each source summand is indecomposable with trivial deck
stabilizer. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_map_finBiproduct_isRadicalMorphism
    {I J : Type} [Fintype I] [Fintype J]
    (M : I → FiniteDimensionalModuleCategory.{uC, vC, uK, uG} (C := C) k)
    (N : J → FiniteDimensionalModuleCategory.{uC, vC, uK, uG} (C := C) k)
    (f : (⨁ M) ⟶ (⨁ N)) (hM : ∀ i, Indecomposable (M i)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    (∀ i (a : Additive G),
      Nonempty (M i ≅ (M i)⟦a⟧) → a = 0) →
      IsRadicalMorphism f →
        IsRadicalMorphism
          ((D.finiteDimensionalModuleOrbitSkeletonPushdown
            (k := k)).map f) := by
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
    (LinearModuleCategory.{uC, max vC uG, uK, uG}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  classical
  intro htrivial hf
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  letI : P.Additive := by
    dsimp only [P]
    infer_instance
  apply MagnitudeConjecture.CategoryTheory.map_finBiproduct_isRadicalMorphism
    P M N f
  intro i j
  have hcomponent : IsRadicalMorphism
      (biproduct.ι M i ≫ f ≫ biproduct.π N j) :=
    MagnitudeConjecture.CategoryTheory.isRadicalMorphism_finBiproduct_component
      M N f hf i j
  exact
    D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isRadicalMorphism
      (k := k) (M i) (N j)
      (biproduct.ι M i ≫ f ≫ biproduct.π N j)
      (hM i) (htrivial i) hcomponent

end MagnitudeConjecture.CoveringHom.CoherentDeckShift

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]
variable [IsCancelSMul G C]

set_option backward.isDefEq.respectTransparency false in
/-- The pushed augmentation of a literal two-step minimal representable
presentation is right minimal when the deck action on upstairs vertices is
free on isomorphism classes. -/
private theorem finiteDimensionalModuleOrbitSkeletonPushdown_twoStep_augmentation_rightMinimal
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    IsFreeOnIsomorphismClasses (C := C) (G := G) →
      IsRightMinimal
        ((Q.toTwoStepFiniteRepresentablePresentation.presentationComplex.map
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))).g) := by
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
    (LinearModuleCategory.{u, v, uK, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  classical
  intro hfree
  let T := Q.toTwoStepFiniteRepresentablePresentation
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  have hkernel : IsRadicalMorphism
      (kernel.ι Q.augmentation.f) :=
    MagnitudeConjecture.CategoryTheory.isRadicalMorphism_kernel_ι_of_isRightMinimal
      Q.augmentation.f Q.augmentation.rightMinimal
  have hdifferential : IsRadicalMorphism T.differential := by
    apply isRadicalMorphism_precomp Q.syzygyPresentation.f hkernel
  have hpushDifferential : IsRadicalMorphism (P.map T.differential) := by
    apply
      D.finiteDimensionalModuleOrbitSkeletonPushdown_map_finBiproduct_isRadicalMorphism
        (k := k)
        (fun i ↦
          (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
            (Opposite.op (Q.syzygyPresentation.X i)))
        (fun j ↦
          (finiteDimensionalLinearCoyonedaFunctor (k := k) hP).obj
            (Opposite.op (Q.augmentation.X j)))
        T.differential
        (fun i ↦ finiteDimensionalLinearCoyoneda_indecomposable
          hP hlocal (Q.syzygyPresentation.X i))
        (fun i a ↦
          D.finiteDimensionalLinearCoyoneda_trivialStabilizer
            (k := k) hP hfree (Q.syzygyPresentation.X i) a)
        hdifferential
  have hExact : (T.presentationComplex.map P).Exact :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_map_exact
      (k := k) T.presentationComplex Q.presentationComplex_exact
  letI : Projective ((T.presentationComplex.map P).X₂) := by
    change Projective
      (P.obj
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj
          Q.augmentation.matrixObject))
    exact
      D.finiteProjectiveRepresentableSumOrbitSkeletonPushdown_projective
        (k := k) hP Q.augmentation.matrixObject
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.Exact.isRightMinimal_g_of_isRadicalMorphism_f
      hExact hpushDifferential

set_option backward.isDefEq.respectTransparency false in
/-- Orbit push-down preserves any minimal finite-representable projective
cover under freeness on isomorphism classes.  A fresh two-step presentation
supplies the radical differential; uniqueness of projective covers transports
the result to the specified cover. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_minimalFiniteRepresentablePresentation_rightMinimal
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (Q : MinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    IsRightMinimal
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map Q.f) := by
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
    (LinearModuleCategory.{u, v, uK, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  classical
  obtain ⟨R⟩ := twoStepMinimalFiniteRepresentablePresentation_nonempty
    hP hlocal M
  have hR :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_twoStep_augmentation_rightMinimal
      (k := k) hP hlocal R hfree
  let e := R.augmentation.toMinimalProjectivePresentation.objectIso
    Q.toMinimalProjectivePresentation
  have he : e.hom ≫ Q.f = R.augmentation.f :=
    R.augmentation.toMinimalProjectivePresentation.objectIso_hom_comp
      Q.toMinimalProjectivePresentation
  have hcomp : IsRightMinimal
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map e.inv ≫
        (R.toTwoStepFiniteRepresentablePresentation.presentationComplex.map
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))).g) :=
    hR.precomp_splitMono
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map e.inv)
  have hmap :
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map e.inv ≫
          (R.toTwoStepFiniteRepresentablePresentation.presentationComplex.map
            (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k))).g =
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map Q.f := by
    change
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map e.inv ≫
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map
            R.augmentation.f =
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map Q.f
    rw [← Functor.map_comp, ← he]
    exact congrArg
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map
      (e.inv_hom_id_assoc Q.f)
  rw [hmap] at hcomp
  exact hcomp

/-- The pushed form of a minimal finite-representable projective cover. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdown_minimalProjectivePresentation
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (Q : MinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    MinimalProjectivePresentation
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  letI : Projective (P.obj Q.source) := by
    change Projective
      (P.obj
        ((finiteProjectiveRepresentableSumFunctor (k := k) hP).obj
          Q.toFiniteRepresentablePresentation.matrixObject))
    exact
      D.finiteProjectiveRepresentableSumOrbitSkeletonPushdown_projective
        (k := k) hP Q.toFiniteRepresentablePresentation.matrixObject
  exact
    { p := P.obj Q.source
      f := P.map Q.f
      rightMinimal :=
        D.finiteDimensionalModuleOrbitSkeletonPushdown_minimalFiniteRepresentablePresentation_rightMinimal
          (k := k) hP hlocal hfree Q }

/-- Orbit push-down of a literal two-step minimal presentation, with the
preserved-kernel isomorphism built into its first cover target. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdown_twoStepMinimalProjectivePresentation
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    TwoStepMinimalProjectivePresentation
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  exact
    { augmentation :=
        D.finiteDimensionalModuleOrbitSkeletonPushdown_minimalProjectivePresentation
          (k := k) hP hlocal hfree Q.augmentation
      syzygyPresentation :=
        (D.finiteDimensionalModuleOrbitSkeletonPushdown_minimalProjectivePresentation
          (k := k) hP hlocal hfree Q.syzygyPresentation).postIso
            (PreservesKernel.iso P Q.augmentation.f) }

set_option backward.isDefEq.respectTransparency false in
/-- The first differential in the pushed two-step minimal presentation is
literally the image of the upstairs differential. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_twoStepMinimalProjectivePresentation_differential
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown_twoStepMinimalProjectivePresentation
      (k := k) hP hlocal hfree Q).differential =
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).map
        Q.toTwoStepFiniteRepresentablePresentation.differential := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  change
    (P.map Q.syzygyPresentation.f ≫
        (PreservesKernel.iso P Q.augmentation.f).hom) ≫
      kernel.ι (P.map Q.augmentation.f) =
        P.map (Q.syzygyPresentation.f ≫ kernel.ι Q.augmentation.f)
  rw [Category.assoc]
  simp only [PreservesKernel.iso_hom]
  rw [kernelComparison_comp_ι]
  exact (P.map_comp _ _).symm

/-- Recoordinate the pushed two-step presentation by the canonical
isomorphisms with literal finite sums of representables on the orbit
skeleton. -/
noncomputable def orbitSkeletonTwoStepMinimalProjectivePresentation
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    TwoStepMinimalProjectivePresentation
      ((D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let S :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_twoStepMinimalProjectivePresentation
      (k := k) hP hlocal hfree Q
  let e := D.finiteProjectiveRepresentableSumOrbitSkeletonPushdownIso
    (k := k) hP
  exact S.recoordinate
    (e.app Q.augmentation.toFiniteRepresentablePresentation.matrixObject).symm
    (e.app Q.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject).symm

set_option backward.isDefEq.respectTransparency false in
/-- The literal orbit-skeleton presentation has the pushed representing
matrix as its first differential. -/
theorem orbitSkeletonTwoStepMinimalProjectivePresentation_differential
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k}
    (Q : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.orbitSkeletonTwoStepMinimalProjectivePresentation
      (k := k) hP hlocal hfree Q).differential =
      (D.orbitSkeletonFiniteProjectiveRepresentableSumFunctor
        (k := k) hP).map
          Q.toTwoStepFiniteRepresentablePresentation.matrixDifferential := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let T := Q.toTwoStepFiniteRepresentablePresentation
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let F := finiteProjectiveRepresentableSumFunctor (k := k) hP
  let F' := D.orbitSkeletonFiniteProjectiveRepresentableSumFunctor
    (k := k) hP
  let e := D.finiteProjectiveRepresentableSumOrbitSkeletonPushdownIso
    (k := k) hP
  dsimp only [orbitSkeletonTwoStepMinimalProjectivePresentation]
  rw [TwoStepMinimalProjectivePresentation.recoordinate_differential]
  rw [D.finiteDimensionalModuleOrbitSkeletonPushdown_twoStepMinimalProjectivePresentation_differential
    (k := k) hP hlocal hfree Q]
  rw [← T.map_matrixDifferential]
  change
    (e.app T.syzygyPresentation.matrixObject).inv ≫
        P.map (F.map T.matrixDifferential) ≫
          (e.app T.augmentation.matrixObject).hom =
      F'.map T.matrixDifferential
  have hn := e.hom.naturality T.matrixDifferential
  change
    P.map (F.map T.matrixDifferential) ≫
        (e.app T.augmentation.matrixObject).hom =
      (e.app T.syzygyPresentation.matrixObject).hom ≫
        F'.map T.matrixDifferential at hn
  calc
    (e.app T.syzygyPresentation.matrixObject).inv ≫
          P.map (F.map T.matrixDifferential) ≫
            (e.app T.augmentation.matrixObject).hom =
        (e.app T.syzygyPresentation.matrixObject).inv ≫
          (P.map (F.map T.matrixDifferential) ≫
            (e.app T.augmentation.matrixObject).hom) := by simp
    _ = (e.app T.syzygyPresentation.matrixObject).inv ≫
          ((e.app T.syzygyPresentation.matrixObject).hom ≫
            F'.map T.matrixDifferential) := by rw [hn]
    _ = F'.map T.matrixDifferential := by simp

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
