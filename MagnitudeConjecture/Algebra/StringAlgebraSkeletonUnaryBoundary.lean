import MagnitudeConjecture.Algebra.StringAlgebraSkeletonArity
import MagnitudeConjecture.Algebra.StringFiniteUnaryBoundary
import MagnitudeConjecture.CategoryTheory.FiniteTauOneMiddle

/-!
# One-middle algebra meshes as literal unary boundaries

Coefficient duality turns the selected right almost-split map at an algebra
skeleton object into a left almost-split monomorphism.  Rotating across its
cokernel produces a literal right almost-split problem.  When the original
mesh has one middle occurrence, literal boundary classification gives a
unary boundary, while uniqueness of kernels identifies its kernel word with
the coefficient dual of the original endpoint.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical
open MagnitudeConjecture.CoveringHom

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance algebraSkeletonUnaryFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance algebraSkeletonUnaryNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Literal data extracted from a one-middle mesh of the quotient-category
algebra skeleton.  Its kernel word represents the coefficient dual of the
original algebra endpoint. -/
structure AlgebraOneMiddleLiteralBoundary
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra)
    (i : Fin T.n) where
  word : StringWord.Word P.toPresentation.relations
  boundary : StringWord.Word.FiniteUnaryBoundary P word
  dualEndpointIso :
    (P.finiteCategoryDualModuleIndecomposableSkeleton T).obj i ≅
      boundary.kernelWord.finiteRightModule P.monomial

/-- Every one-middle mesh on the algebra skeleton rotates to a literal unary
Butler--Ringel boundary. -/
theorem nonempty_algebraOneMiddleLiteralBoundary
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra)
    (Y : FiniteTauMatrix.OneMiddleMesh T.finiteTauCategoryData) :
    Nonempty (P.AlgebraOneMiddleLiteralBoundary S T Y.1) := by
  let C := Category P.toPresentation.relations
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  let E := finiteCategoryProjectiveGenerator.moduleEquivalence hP
  let U := P.finiteCategoryModuleIndecomposableSkeleton T
  let V := P.finiteCategoryDualModuleIndecomposableSkeleton T
  letI : E.functor.Additive :=
    finiteCategoryProjectiveGenerator.representedFGFunctor_additive hP
  letI : E.inverse.Additive := inferInstance
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, u, u, u} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        P.quotientCategoryAlgebra) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      P.quotientCategoryAlgebraᵐᵒᵖ
  let TU := U.toFiniteRightTauCategoryData
  let TT := T.finiteTauCategoryData.toFiniteRightTauCategoryData
  let labelEquiv : Fin T.n ≃ Fin T.n := Equiv.refl _
  let objIso (j : Fin T.n) :
      E.functor.obj (U.obj j) ≅ T.fgObj j := by
    simpa [E, hP, U] using
      P.finiteCategoryModuleIndecomposableSkeletonObjIso T j
  have hprojective :=
    FiniteTauMatrix.isProjective_equivalence_iff
      TU TT E labelEquiv objIso Y.1
  have hlabel : labelEquiv Y.1 = Y.1 := rfl
  have hiU : ¬ TU.IsProjective Y.1 := by
    intro hi
    apply Y.2.1
    exact hlabel ▸ hprojective.mp hi
  have hiUobj : ¬ Projective (TU.obj Y.1) := by
    rwa [FiniteTauMatrix.isProjective_iff_projective_obj] at hiU
  have harity :
      FiniteTauMatrix.rightMiddleArity TU Y.1 =
        FiniteTauMatrix.rightMiddleArity TT Y.1 := by
    calc
      FiniteTauMatrix.rightMiddleArity TU Y.1 =
          FiniteTauMatrix.rightMiddleArity TT (labelEquiv Y.1) :=
        FiniteTauMatrix.rightMiddleArity_eq_of_equivalence
          TU TT E labelEquiv objIso Y.1
      _ = FiniteTauMatrix.rightMiddleArity TT Y.1 :=
        congrArg (FiniteTauMatrix.rightMiddleArity TT) hlabel
  have hTUarity : FiniteTauMatrix.rightMiddleArity TU Y.1 = 1 :=
    harity.trans Y.2.2
  let d := FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition
    TU Y.1
  let m := (TU.rightMesh (TU.obj Y.1)).g ≫
    (TU.rightTermIso (TU.obj Y.1)).hom
  have hmAS : IsRightAlmostSplit m :=
    FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit TU Y.1
  have hmMin : IsRightMinimal m :=
    FiniteTauMatrix.rightMesh_terminal_isRightMinimal TU Y.1
  letI : Epi m :=
    MagnitudeConjecture.CategoryTheory.IsRightAlmostSplit.epi_of_not_projective
      m hmAS hiUobj
  let D := finiteCoefficientDualityEquivalence (k := k) (C := C)
  letI : D.functor.Additive := finiteCoefficientDualFunctor_additive
  let g : D.functor.obj (Opposite.op (TU.obj Y.1)) ⟶
      D.functor.obj
        (Opposite.op (TU.rightMesh (TU.obj Y.1)).X₂) :=
    D.functor.map m.op
  letI : Mono g := by
    dsimp only [g]
    infer_instance
  have hgAS : IsLeftAlmostSplit g := hmAS.map_op_equivalence D
  have hgMin : IsLeftMinimal g := hmMin.map_op_equivalence D
  let q : D.functor.obj
      (Opposite.op (TU.rightMesh (TU.obj Y.1)).X₂) ⟶
      cokernel g := cokernel.π g
  have hqAS : IsRightAlmostSplit q :=
    MagnitudeConjecture.CategoryTheory.leftAlmostSplit_cokernel_π_isRightAlmostSplit
      g hgAS hgMin
  let rotated : ShortComplex
      (FiniteDimensionalModuleCategory.{u, u, u, u} (C := Cᵒᵖ) k) :=
    ShortComplex.mk g q (cokernel.condition g)
  have hrotated : rotated.ShortExact :=
    { exact := ShortComplex.exact_cokernel g }
  have hYindec :
      Indecomposable (D.functor.obj (Opposite.op (TU.obj Y.1))) := by
    apply
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        D.functor (Opposite.op (TU.obj Y.1))).2
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_op_iff
        (TU.obj Y.1)).2 (TU.obj_indec Y.1)
  letI : IsLocalRing
      (End (D.functor.obj (Opposite.op (TU.obj Y.1)))) :=
    finiteDimensionalModule_end_isLocalRing k _ hYindec
  have hgRadical : IsRadicalMorphism g :=
    (MagnitudeConjecture.CategoryTheory.isRadicalMorphism_iff_not_isSplitMono_of_local_end
      hYindec.1 g).2 hgAS.not_isSplitMono
  have hqMin : IsRightMinimal q :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_isRadicalMorphism_f
      hrotated hgRadical
  have hQindec : Indecomposable (cokernel g) :=
    MagnitudeConjecture.CategoryTheory.IsRightAlmostSplit.target_indecomposable
      q hqAS
  have hQnonprojective : ¬ Projective (cokernel g) := by
    intro hQ
    letI : Projective (cokernel g) := hQ
    obtain ⟨s, hs⟩ := Projective.factors (𝟙 (cokernel g)) q
    apply hqAS.not_isSplitEpi
    exact IsSplitEpi.mk' { section_ := s, id := hs }
  obtain ⟨j, ⟨eQ⟩⟩ := V.complete (cokernel g) hQindec
  let W :=
    (StringWord.DetectorIndex.detectorIndexOfFiniteSkeletonLabel
      (S := S) V j).endpointWord.word
  let eW : W.finiteRightModule P.monomial ≅ cokernel g :=
    StringWord.DetectorIndex.finiteSkeletonStringIso
        (S := S) V j ≪≫ eQ.symm
  have hWnonprojective :
      ¬ Projective (W.finiteRightModule P.monomial) := by
    intro hW
    exact hQnonprojective (Projective.of_iso eW hW)
  have hIndec (a : Fin d.n) :
      Indecomposable
        (D.functor.obj (Opposite.op (d.summand a))) := by
    apply
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        D.functor (Opposite.op (d.summand a))).2
    exact
      (MagnitudeConjecture.CategoryTheory.indecomposable_op_iff
        (d.summand a)).2 (d.indecomposable a)
  let dMap := d.mapOpOfIndecomposable D.functor hIndec
  have hlocal (a : Fin dMap.n) :
      IsLocalRing (End (dMap.summand a)) :=
    finiteDimensionalModule_end_isLocalRing k _ (dMap.indecomposable a)
  have hdMap : dMap.n = 1 := by
    exact hTUarity
  have hqWAS : IsRightAlmostSplit (q ≫ eW.inv) :=
    hqAS.postcomp_iso eW.symm
  have hqWMin : IsRightMinimal (q ≫ eW.inv) :=
    IsRightMinimal.postcomp_iso eW.symm hqMin
  obtain ⟨B⟩ :=
    StringWord.Word.nonempty_finiteUnaryBoundary_of_decomposition_n_eq_one
      P S V W hWnonprojective (q ≫ eW.inv) dMap hlocal
        hqWAS hqWMin hdMap
  let e₃ : rotated.X₃ ≅ B.rawShortComplex.X₃ :=
    eW.symm ≪≫ B.endpointIso.symm
  obtain ⟨eLeft⟩ :=
    MagnitudeConjecture.CategoryTheory.nonempty_leftTermIso_of_shortExact_minimalRightAlmostSplit
      hrotated B.rawShortComplex_shortExact hqAS hqMin
      (B.rawShortComplex_isRightAlmostSplit P S V)
      (B.rawShortComplex_isRightMinimal P S V) e₃
  let eKernel : B.rawShortComplex.X₁ ≅
      B.kernelWord.finiteRightModule P.monomial :=
    eqToIso B.rawShortComplex_X₁
  let eDual : V.obj Y.1 ≅
      B.kernelWord.finiteRightModule P.monomial := by
    exact eLeft ≪≫ eKernel
  exact ⟨{
    word := W
    boundary := B
    dualEndpointIso := by simpa [V] using eDual }⟩

/-- A chosen literal unary boundary representing a one-middle algebra mesh. -/
noncomputable def oneMiddleLiteralBoundary
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra)
    (Y : FiniteTauMatrix.OneMiddleMesh T.finiteTauCategoryData) :
    P.AlgebraOneMiddleLiteralBoundary S T Y.1 :=
  Classical.choice (P.nonempty_algebraOneMiddleLiteralBoundary S T Y)

/-- Send a one-middle algebra mesh to the central displayed arrow of its
chosen literal unary boundary. -/
noncomputable def oneMiddleMeshDisplayedArrow
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    FiniteTauMatrix.OneMiddleMesh T.finiteTauCategoryData →
      (Σ y : Q, Σ x : Q, x ⟶ y) :=
  fun Y ↦ (P.oneMiddleLiteralBoundary S T Y).boundary.displayedArrow

/-- Distinct one-middle meshes have distinct chosen central arrows.  Equality
of arrows gives equality of their canonical kernel words, hence an
isomorphism between the corresponding objects of the coefficient-dual
skeleton. -/
theorem oneMiddleMeshDisplayedArrow_injective
    (P : StringPresentation k A Q)
    (S : P.toSpecialBiserialPresentation.ArrowPolarization)
    (T : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    Function.Injective (P.oneMiddleMeshDisplayedArrow S T) := by
  intro Y Z hYZ
  let BY := P.oneMiddleLiteralBoundary S T Y
  let BZ := P.oneMiddleLiteralBoundary S T Z
  let V := P.finiteCategoryDualModuleIndecomposableSkeleton T
  have hword : BY.boundary.kernelWord = BZ.boundary.kernelWord := by
    rw [BY.boundary.kernelWord_eq_canonicalKernelWord P,
      BZ.boundary.kernelWord_eq_canonicalKernelWord P]
    exact congrArg
      (StringWord.Word.HookExtension.canonicalKernelWord
        P.toSpecialBiserialPresentation) hYZ
  let eWord : BY.boundary.kernelWord.finiteRightModule P.monomial ≅
      BZ.boundary.kernelWord.finiteRightModule P.monomial :=
    eqToIso (congrArg
      (fun W : StringWord.Word P.toPresentation.relations ↦
        W.finiteRightModule P.monomial) hword)
  let e : V.obj Y.1 ≅ V.obj Z.1 :=
    BY.dualEndpointIso ≪≫ eWord ≪≫ BZ.dualEndpointIso.symm
  apply Subtype.ext
  exact V.skeletal ⟨e⟩

end StringPresentation
end MagnitudeConjecture.BoundQuiver
